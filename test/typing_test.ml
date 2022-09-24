open OUnit
open Test_helper
open Term
open Typing

let of_schema_tests =
  "Of Schema"
  >::: [ ("Legitimate schema"
         >:: fun () ->
         let gamma = Context.ctx_var "Gamma" in
         let x = var Constant "X" 0 ity in
         let y = var Constant "Y" 0 ity in
         let t = var Logic "T" 0 ity in
         let t1 = var Eigen "T1" 0 ity in
         let n = nominal_var "n" ity in
         let n1 = nominal_var "n1" ity in
         let nvars = [ term_to_name n, n; term_to_name n1, n1 ] in
         (* < Gamma, n: tm, n1: of n T > *)
         let ctx =
           Context.Ctx
             ( Context.Ctx (Context.Var gamma, (term_to_var n, tm))
             , (term_to_var n1, Term.app typeof [ n; t1 ]) )
         in
         let ctx_vars = [ gamma, Context.CtxTy ("c", []) ] in
         (* Schema c := {T}(x:tm, y:of x T) *)
         let blocks =
           [ Context.B
               ( [ "T", ity ]
               , [ term_to_var x, tm; term_to_var y, Term.app typeof [ x; t ] ] )
           ]
         in
         of_schema nvars ctx_vars ctx ("c", blocks)
         |> assert_bool "Should match instance of schema")
       ; ("Nothing matches empty schema"
         >:: fun () ->
         let gamma = Context.ctx_var "Gamma" in
         let t = var Eigen "T" 0 ity in
         let n = nominal_var "n" ity in
         let n1 = nominal_var "n1" ity in
         let nvars = [ term_to_name n, n; term_to_name n1, n1 ] in
         let ctx =
           Context.Ctx
             ( Context.Ctx (Context.Var gamma, (term_to_var n, tm))
             , (term_to_var n1, Term.app typeof [ n; t ]) )
         in
         let ctx_vars = [ "Gamma", Context.CtxTy ("c", []) ] in
         let schemas = [ Context.B ([], []) ] in
         of_schema nvars ctx_vars ctx ("c", schemas)
         |> not
         |> assert_bool "Should not match instance of empty")
       ; ("Doesn't match mismatched schema"
         >:: fun () ->
         let gamma = Context.ctx_var "Gamma" in
         let t = var Eigen "T" 0 ity in
         let x = var Constant "X" 0 ity in
         let n = nominal_var "n" ity in
         let n1 = nominal_var "n1" ity in
         let nvars = [ term_to_name n, n; term_to_name n1, n1 ] in
         (* < Gamma, n: tm, n1: of n T > *)
         let ctx =
           Context.Ctx
             ( Context.Ctx (Context.Var gamma, (term_to_var n, tm))
             , (term_to_var n1, Term.app typeof [ n; t ]) )
         in
         let ctx_vars = [ "Gamma", Context.CtxTy ("c", []) ] in
         (* Schema c := (x:tm) *)
         let schemas = [ Context.B ([], [ term_to_var x, tm ]) ] in
         of_schema nvars ctx_vars ctx ("c", schemas)
         |> not
         |> assert_bool "Doesn't match schema")
       ; ("Matches multiple repetitions of the schema"
         >:: fun () ->
         let gamma = Context.ctx_var "Gamma" in
         let x = var Constant "X" 0 ity in
         let y = var Constant "Y" 0 ity in
         let t = var Logic "T" 0 ity in
         let t1 = var Eigen "T1" 0 ity in
         let t2 = var Eigen "T2" 0 ity in
         let n = nominal_var "n" ity in
         let n1 = nominal_var "n1" ity in
         let n2 = nominal_var "n2" ity in
         let n3 = nominal_var "n3" ity in
         let nvars =
           [ term_to_name n, n
           ; term_to_name n1, n1
           ; term_to_name n2, n2
           ; term_to_name n3, n3
           ]
         in
         (* < Gamma, n: tm, n1: of n T, n2: tm, n3: of n2 T1 > *)
         let ctx =
           Context.Ctx
             ( Context.Ctx
                 ( Context.Ctx
                     ( Context.Ctx (Context.Var gamma, (term_to_var n, tm))
                     , (term_to_var n1, Term.app typeof [ n; t1 ]) )
                 , (term_to_var n2, tm) )
             , (term_to_var n3, Term.app typeof [ n2; t2 ]) )
         in
         let ctx_vars = [ "Gamma", Context.CtxTy ("c", []) ] in
         (* Schema c := {T}(x:tm, y:of x T) *)
         let schemas =
           [ Context.B
               ( [ "T", ity ]
               , [ term_to_var x, tm; term_to_var y, Term.app typeof [ x; t ] ] )
           ]
         in
         of_schema nvars ctx_vars ctx ("c", schemas)
         |> assert_bool "Should match multiple instances of a schema")
       ; ("Matches schema with only schematic variables"
         >:: fun () ->
         let gamma = Context.ctx_var "Gamma" in
         let x = var Constant "X" 0 ity in
         let n = nominal_var "n" ity in
         let nvars = [ term_to_name n, n ] in
         (* < Gamma, n: tm, n1: of n T > *)
         let ctx = Context.Ctx (Context.Var gamma, (term_to_var n, tm)) in
         let ctx_vars = [ "Gamma", Context.CtxTy ("c", []) ] in
         (* Schema c := {T}(x:tm, y:of x T) *)
         let schemas = [ Context.B ([], [ term_to_var x, tm ]) ] in
         of_schema nvars ctx_vars ctx ("c", schemas)
         |> assert_bool "Should match instance of schema")
       ; ("Matches schema with repetitions of only schematic variables"
         >:: fun () ->
         let gamma = Context.ctx_var "Gamma" in
         let x = var Constant "X" 0 ity in
         let n = nominal_var "n" ity in
         let n1 = nominal_var "n1" ity in
         let nvars = [ term_to_name n, n; term_to_name n1, n1 ] in
         (* < Gamma, n: tm, n1: of n T > *)
         let ctx =
           Context.Ctx
             (Context.Ctx (Context.Var gamma, (term_to_var n, tm)), (term_to_var n1, tm))
         in
         let ctx_vars = [ "Gamma", Context.CtxTy ("c", []) ] in
         (* Schema c := {T}(x:tm, y:of x T) *)
         let schemas = [ Context.B ([], [ term_to_var x, tm ]) ] in
         of_schema nvars ctx_vars ctx ("c", schemas)
         |> assert_bool "Should match repetitions of of schema")
       ; ("Matches schema with an application"
         >:: fun () ->
         let gamma = Context.ctx_var "Gamma" in
         let x = var Constant "X" 0 ity in
         let t = var Constant "T" 0 ity in
         let y = var Constant "Y" 0 ity in
         let n = nominal_var "n" ity in
         let n1 = nominal_var "n1" ity in
         let n2 = nominal_var "n2" ity in
         let nvars = [ term_to_name n, n; term_to_name n1, n1; term_to_name n2, n2 ] in
         (* < Gamma, n: tm, n1: of n T > *)
         let ctx =
           Context.Ctx
             ( Context.Ctx
                 ( Context.Ctx (Context.Var gamma, (term_to_var n, tm))
                 , (term_to_var n1, ty) )
             , (term_to_var n2, Term.app typeof [ n; n1 ]) )
         in
         let ctx_vars = [ "Gamma", Context.CtxTy ("c", []) ] in
         (* Schema c := {T}(x:tm, y:of x T) *)
         let schemas =
           [ Context.B
               ( []
               , [ term_to_var x, tm
                 ; term_to_var t, ty
                 ; term_to_var y, Term.app typeof [ x; t ]
                 ] )
           ]
         in
         of_schema nvars ctx_vars ctx ("c", schemas) |> assert_bool "Should match schema"
         )
       ]
;;

let tests = "Typing" >::: [ of_schema_tests ]
