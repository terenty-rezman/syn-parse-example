use proc_macro2::TokenStream;
use proc_macro_error::{abort, abort_call_site, proc_macro_error};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{parse_macro_input, Ident, LitInt, Result, Token};

macro_rules! unwrap_enum {
    ($target: expr, $pat: path) => {{
        if let $pat(a) = $target {
            // #1
            a
        } else {
            panic!("mismatch variant when cast to {}", stringify!($pat)); // #2
        }
    }};
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
struct InstructionSet {
    instructions: Vec<Instruction>,
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

impl Parse for InstructionSet {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.is_empty() {
            return Ok(InstructionSet::default());
        }

        let mut instructions = Vec::new();

        while !input.is_empty() {
            let ins: Instruction = input.parse()?;
            instructions.push(ins);
        }

        Ok(InstructionSet { instructions })
    }
}

fn generate_code(ins_set: InstructionSet) -> TokenStream {
    let mut result_ins_ast = quote! {};

    for ins in ins_set.instructions {
        let ins_name = ins.name.to_string();

        match ins_name.as_str() {
            "_const" => result_ins_ast.extend(instruction_const(&ins)),
            "add" => result_ins_ast.extend(instruction_add(&ins)),
            "local" => result_ins_ast.extend(instruction_local(&ins)),
            "local_get" => result_ins_ast.extend(instruction_local_get(&ins)),
            "local_set" => result_ins_ast.extend(instruction_local_set(&ins)),
            "print_stack" => result_ins_ast.extend(instruction_print_stack(&ins)),
            "print_local" => result_ins_ast.extend(instruction_print_local(&ins)),

            _ => abort!(ins.name.span(), format!("unknown instruction: {ins_name}")),
        }
    }

    let result_code = quote! {
        {
            let mut _stack = std::vec::Vec::new();
            #result_ins_ast
        }
    };

    result_code
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

#[proc_macro]
#[proc_macro_error]
pub fn wasm_like(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // eprintln!("{:#?}", input);
    let instructions_ast = parse_macro_input!(input as InstructionSet);
    // eprintln!("{:#?}", instructions_ast);
    let result_ast = generate_code(instructions_ast);
    result_ast.into()
}
