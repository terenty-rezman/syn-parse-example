use my_macro::wasm_like;

fn main() {
    wasm_like!{
        local $i

        _const 10
        local_set $i

        (_loop $my_loop
            print_local $i

            local_get $i
            eqz  
            br_if $my_loop

            local_get $i
            _const 1
            sub
            local_set $i
        )
    };
}
