(* module for definitions *)

type def = Term.tyctx * Term.tyctx * Formula.formula * Formula.formula
type dfn = Type.ty * def list
