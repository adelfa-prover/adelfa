(* module for definitions *)

type def = Term.tyctx * Term.tyctx * Formula.formula * Formula.formula
type dfn = Term.id * (Type.ty * def list)
