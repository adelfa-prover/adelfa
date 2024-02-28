open OUnit
open Test_helper
module Sub = Subordination

let simpl =
  "Simple Subordination Tests"
  >::: [ ("Reflexivity"
          >:: fun () ->
          Signature.get_type_decls unique_sig
          |> List.map (fun x -> x.Signature.ty_name)
          |> List.iter (fun ty ->
            assert_bool
              (Printf.sprintf "%s should subordinate itself" ty)
              (Sub.subordinates unique_sub_rel ty ty)))
       ; ("Term </= Type"
          >:: fun () ->
          assert_bool
            "Term should not subordinate type"
            (not (Sub.subordinates unique_sub_rel tm_decl.ty_name ty_decl.ty_name)))
       ; ("Type <= Term"
          >:: fun () ->
          assert_bool
            "Type should subordinate term"
            (Sub.subordinates unique_sub_rel ty_decl.ty_name tm_decl.ty_name))
       ; ("Type <= typeof"
          >:: fun () ->
          assert_bool
            "Type should subordinate typeof"
            (Sub.subordinates unique_sub_rel ty_decl.ty_name typeof_decl.ty_name))
       ; ("Term <= typeof"
          >:: fun () ->
          assert_bool
            "Term should subordinate typeof"
            (Sub.subordinates unique_sub_rel tm_decl.ty_name typeof_decl.ty_name))
       ; ("Term <= eval"
          >:: fun () ->
          assert_bool
            "Term should subordinate eval"
            (Sub.subordinates unique_sub_rel tm_decl.ty_name eval_decl.ty_name))
       ; ("Type <= eval"
          >:: fun () ->
          assert_bool
            "Type should subordinate eval"
            (Sub.subordinates unique_sub_rel ty_decl.ty_name eval_decl.ty_name))
       ]
;;

let ctx =
  "Context minimization"
  >::: [ ("All subordinate types should be preserved"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let ctx_expr =
            Context.Ctx
              ( Context.Ctx (Context.Nil, (Term.term_to_var n, tm))
              , (Term.term_to_var n1, tm) )
          in
          let filtered =
            Context.subordination_min unique_sub_rel tm_decl.ty_name ctx_expr
          in
          assert_context_equal ctx_expr filtered)
       ; ("Context variables preserved"
          >:: fun () ->
          let gamma = Context.ctx_var "Gamma" in
          let ctx_expr = Context.Var gamma in
          let filtered =
            Context.subordination_min unique_sub_rel tm_decl.ty_name ctx_expr
          in
          assert_context_equal ctx_expr filtered)
       ; ("Non-subordinate types should be removed"
          >:: fun () ->
          let n = Term.nominal_var "n" ity in
          let n1 = Term.nominal_var "n1" ity in
          let ctx_expr =
            Context.Ctx
              ( Context.Ctx (Context.Nil, (Term.term_to_var n, tm))
              , (Term.term_to_var n1, tm) )
          in
          let expected = Context.Nil in
          let filtered =
            Context.subordination_min unique_sub_rel ty_decl.ty_name ctx_expr
          in
          assert_context_equal expected filtered)
       ]
;;

let tests = "Subordination" >::: [ simpl; ctx ]
