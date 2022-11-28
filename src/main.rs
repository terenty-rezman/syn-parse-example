use cmd_lib::run_cmd;
use my_macro::wasm_like;

fn main() {
    wasm_like!{
        local $a 
        local $b
        local $c

        (_loop $my_loop
            _const 3 
            local_set $a

            _const 4
            local_set $b

            local_get $a
            local_get $b
            add

            local_set $c
            print_local $c
        )
    };

    // run_cmd!(ls 1);
}
