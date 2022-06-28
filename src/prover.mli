exception ProofCompleted

type prover_settings = { mutable search_depth : int }

type prover_state =
  { sequent : Sequent.sequent
  ; subgoals : (unit -> unit) list
  ; bind_state : Term.bind_state
  ; term_var_count : int
  ; ctx_var_count : int
  ; settings : prover_settings
  }

val change_settings : Uterms.setting list -> unit
val lf_sig : Signature.signature ref
val set_sig : Signature.signature -> unit
val clear_sig : unit -> unit
val schemas : (string * Context.ctx_schema) list ref
val add_schema : string -> Context.ctx_schema -> unit
val clear_schemas : unit -> unit
val lookup_schema : string -> Context.ctx_schema
val add_lemma : string -> Formula.formula -> unit
val clear_lemmas : unit -> unit
val lookup_lemma : string -> Formula.formula
val add_definition : Definition.dfn -> unit
val clear_definitions : unit -> unit
val lookup_definition : string -> Definition.def list
val get_propty_lst : unit -> (string * Type.ty) list
val set_sequent : Sequent.sequent -> unit
val get_sequent : unit -> Sequent.sequent
val display_state : unit -> unit
val reset_prover : unit -> unit
val induction : int -> unit
val intros : unit -> unit
val case : bool -> string -> unit
val skip : unit -> unit
val exists : Term.term -> unit
val undo : unit -> unit
val search : Uterms.depth -> unit -> unit
val apply : string -> string list -> Uterms.uwith list -> unit
val assert_thm : Formula.formula -> unit
val split : unit -> unit
val left : unit -> unit
val right : unit -> unit
val weaken : Uterms.depth -> bool -> string -> Term.term -> unit
val permute_ctx : bool -> string -> Context.ctx_expr -> unit
val strengthen : bool -> string -> unit
val inst : Uterms.depth -> bool -> string -> Uterms.uwith list -> unit
val prune : string -> unit
val unfold : string option -> Uterms.uwith list -> unit
val applydfn : string -> string option -> Uterms.uwith list -> unit
