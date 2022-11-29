use proc_macro2::{Punct, Spacing, TokenStream};
use proc_macro_error::{abort, proc_macro_error};
use quote::{quote};
use syn::parse::{Parse, ParseStream};
use syn::{parenthesized, parse_macro_input, Ident, LitInt, Result, Token};

macro_rules! unwrap_enum {
    ($target: expr, $pat: path) => {{
        if let $pat(a) = $target {
            a
        } else {
            panic!("mismatch variant when cast to {}", stringify!($pat));
        }
    }};
}

#[derive(Debug)]
enum Statement {
    Block(Block),
    Instruction(Instruction),
}

#[derive(Debug)]
struct Block {
    name: Ident,
    label: Option<Ident>,
    statements: Vec<Statement>,
}

#[derive(Debug)]
struct Instruction {
    name: Ident,
    op: Option<Operand>,
}

#[derive(Debug)]
enum Operand {
    Int(i32),
    Ident(Ident),
}

#[derive(Default, Debug)]
struct Program {
    statements: Vec<Statement>,
}

impl Parse for Statement {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(syn::token::Paren) {
            let block: Block = input.parse()?;
            Ok(Statement::Block(block))
        } else {
            let ins: Instruction = input.parse()?;
            Ok(Statement::Instruction(ins))
        }
    }
}

fn parse_statements(input: ParseStream) -> Result<Vec<Statement>> {
    let mut statements = vec![];

    while !input.is_empty() {
        let ins: Statement = input.parse()?;
        statements.push(ins);
    }

    Ok(statements)
}

impl Parse for Block {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        let _paren_token = parenthesized!(content in input);

        let name: Ident = content.parse()?;
        let label = if name == "_loop" {
            let _dollar: Token![$] = content.parse()?;
            Some(content.parse()?)
        } else {
            None
        };
        let statements = parse_statements(&content)?;

        Ok(Block {
            name,
            label,
            statements,
        })
    }
}

impl Parse for Instruction {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;
        let lookahead = input.lookahead1();

        let op = if lookahead.peek(LitInt) {
            let int: LitInt = input.parse()?;
            Some(Operand::Int(
                int.to_string()
                    .parse()
                    .expect("Only i32 accepted as instruction operand"),
            ))
        } else if lookahead.peek(Token![$]) {
            let _dollar: Token![$] = input.parse()?;
            let op: Ident = input.parse()?;
            Some(Operand::Ident(op))
        } else {
            None
        };

        Ok(Instruction { name, op })
    }
}

impl Parse for Program {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.is_empty() {
            return Ok(Program::default());
        }

        let statements = parse_statements(input)?;
        Ok(Program { statements })
    }
}

fn generate_code(program: Program) -> TokenStream {
    let mut statement_code = quote! {};

    for st in program.statements {
        statement_code.extend(gen_code_for_statement(&st));
    }

    let result_code = quote! {
        {
            let mut _stack = std::vec::Vec::<i32>::new();
            #statement_code
        }
    };

    result_code
}

fn gen_code_for_statement(st: &Statement) -> TokenStream {
    match st {
        Statement::Instruction(ins) => gen_code_for_instruction(ins),
        Statement::Block(blk) => gen_code_for_block(blk),
    }
}

fn gen_code_for_block(block: &Block) -> TokenStream {
    let blk_name = block.name.to_string();
    match blk_name.as_str() {
        "_loop" => block_loop(&block),

        _ => abort!(block.name.span(), format!("unknown block: {blk_name}")),
    }
}

fn gen_code_for_instruction(ins: &Instruction) -> TokenStream {
    let ins_name = ins.name.to_string();
    match ins_name.as_str() {
        "_const" => instruction_const(&ins),
        "add" => instruction_add(&ins),
        "sub" => instruction_sub(&ins),
        "local" => instruction_local(&ins),
        "local_get" => instruction_local_get(&ins),
        "local_set" => instruction_local_set(&ins),
        "br" => instruction_br(&ins),
        "br_if" => instruction_br_if(&ins),
        "eq" => instruction_eq(&ins),
        "eqz" => instruction_eqz(&ins),
        "print_stack" => instruction_print_stack(&ins),
        "print_local" => instruction_print_local(&ins),

        _ => abort!(ins.name.span(), format!("unknown instruction: {ins_name}")),
    }
}

macro_rules! apostrophe {
    () => {
        Punct::new('\'', Spacing::Joint)
    };
}

fn block_loop(block: &Block) -> TokenStream {
    let label = block.label.as_ref().unwrap_or_else(|| {
        abort!(
            block.name.span(),
            "block loop requires id: (_loop $my_loop ...)"
        )
    });

    let mut statement_code = quote! {};
    for st in &block.statements {
        statement_code.extend(gen_code_for_statement(&st));
    }

    // need this to make 'a: loop {}
    let apostrophe = apostrophe!();

    quote! {
        #apostrophe #label: loop {
            #statement_code
        };
    }
}

fn instruction_const(ins: &Instruction) -> TokenStream {
    let int = ins.op.as_ref().unwrap_or_else(|| {
        abort!(
            ins.name.span(),
            "_const instruction requires one i32 operand"
        )
    });
    let int = unwrap_enum!(int, Operand::Int);
    quote! {_stack.push(#int);}
}

fn instruction_print_local(ins: &Instruction) -> TokenStream {
    let id = ins.op.as_ref().unwrap_or_else(|| {
        abort!(
            ins.name.span(),
            "instruction print_local requires variable identifer as operand: print_local $id"
        )
    });
    let var_name = unwrap_enum!(id, Operand::Ident);
    quote! {println!("{:#?}", #var_name);}
}

fn instruction_print_stack(_ins: &Instruction) -> TokenStream {
    quote! {println!("{:#?}", _stack);}
}

fn instruction_add(_ins: &Instruction) -> TokenStream {
    quote! {
        assert!(_stack.len() >= 2, "instruction add requires 2 values on the stack");
        {let (a, b) = (_stack.pop().unwrap(), _stack.pop().unwrap()); _stack.push(a + b);}
    }
}

fn instruction_sub(_ins: &Instruction) -> TokenStream {
    quote! {
        assert!(_stack.len() >= 2, "instruction add requires 2 values on the stack");
        {let (a, b) = (_stack.pop().unwrap(), _stack.pop().unwrap()); _stack.push(b - a);}
    }
}

fn instruction_local(ins: &Instruction) -> TokenStream {
    let int = ins.op.as_ref().unwrap_or_else(|| {
        abort!(
            ins.name.span(),
            "instruction local requires variable identifer as operand: local $id"
        )
    });
    let var_name = unwrap_enum!(int, Operand::Ident);
    quote! {let mut #var_name = 0;}
}

fn instruction_local_get(ins: &Instruction) -> TokenStream {
    let id = ins.op.as_ref().unwrap_or_else(|| {
        abort!(
            ins.name.span(),
            "instruction local_get requires variable identifer as operand: local_get $id"
        )
    });
    let var_name = unwrap_enum!(id, Operand::Ident);
    quote! {_stack.push(#var_name);}
}

fn instruction_local_set(ins: &Instruction) -> TokenStream {
    let id = ins.op.as_ref().unwrap_or_else(|| {
        abort!(
            ins.name.span(),
            "instruction local_set requires variable identifer as operand: local_set $id"
        )
    });
    let var_name = unwrap_enum!(id, Operand::Ident);
    quote! {
        assert!(_stack.len() != 0, "instruction local_set requires one value on the stack");
        #var_name = _stack.pop().unwrap();
    }
}

fn instruction_br(ins: &Instruction) -> TokenStream {
    let id = ins.op.as_ref().unwrap_or_else(|| {
        abort!(
            ins.name.span(),
            "instruction br requires loop label as operand: br $label"
        )
    });
    let label = unwrap_enum!(id, Operand::Ident);
    let apostrophe = apostrophe!();
    quote! {break #apostrophe #label;}
}

fn instruction_br_if(ins: &Instruction) -> TokenStream {
    let id = ins.op.as_ref().unwrap_or_else(|| {
        abort!(
            ins.name.span(),
            "instruction br requires loop label as operand: br $label"
        )
    });

    let label = unwrap_enum!(id, Operand::Ident);
    let apostrophe = apostrophe!();
    quote! {
        assert!(_stack.len() > 0, "instruction br_if requires one value on the stack");
        if(_stack.pop().unwrap() != 0) { break #apostrophe #label; }
    }
}

fn instruction_eq(_ins: &Instruction) -> TokenStream {
    quote! {
        assert!(_stack.len() >= 2, "instruction eq requires 2 values on the stack");
        {
            let (a, b) = (_stack.pop().unwrap(), _stack.pop().unwrap());
            if a == b {_stack.push(1);} else {_stack.push(0);}
        } 
    }
}

fn instruction_eqz(_ins: &Instruction) -> TokenStream {
    quote! {
        assert!(_stack.len() > 0, "instruction eq requires 1 value on the stack");
        {
            let a = _stack.pop().unwrap();
            if a == 0 {_stack.push(1);} else {_stack.push(0);}
        } 
    }
}

#[proc_macro]
#[proc_macro_error]
pub fn wasm_like(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // eprintln!("{:#?}", input);
    let ast = parse_macro_input!(input as Program);
    // eprintln!("{:#?}", ast);
    let code = generate_code(ast);
    // eprintln!("{:#?}", code);
    // eprintln!("{}", code);
    code.into()
}
