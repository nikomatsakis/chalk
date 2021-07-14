#[test]
fn test_trait_impl_assoc_const() {
    reparse_test!(
        program {
            struct Foo { }
            trait Bar {
                const C: u32;
            }
            impl Bar for Foo {
                const C: u32 = 3;
            }
        }
    );
}
