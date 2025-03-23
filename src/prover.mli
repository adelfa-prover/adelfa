exception ProofCompleted

(** [prover_settings] stores modifiable preferences the user has. *)
type prover_settings = { mutable search_depth : int; mutable schema_sub : bool }

(** [change_settings sets] will modify the [prover_settings] based on [sets]
    values. The application of settings is done in left-to-right order *)
val change_settings : Uterms.setting list -> unit

(** [lf_sig] the specification file provided to the prover *)
val lf_sig : Signature.signature ref

(** [set_sig s] replaces the current [lf_sig] with [s] *)
val set_sig : Signature.signature -> unit

(** [clear_sig] removes any specification provided to the prover *)
val clear_sig : unit -> unit

(** [has_sig] checks if a specification file has already been provided to the
    prover. *)
val has_sig : unit -> bool

(** [schemas] a [Hashtbl.t] which stores all the context schemas defined at the
    top level. *)
val schemas : (string, Context.ctx_schema) Hashtbl.t

(** [add_schma id s] creates an entry in [schemas] for a new context schema.
    Will output a warning message if a context schema with the same idenfier as
    [id] already exists. *)
val add_schema : string -> Context.ctx_schema -> unit

(** [lookup_schema id] will return the context schema for [id] within [schemas].
    Raises [Not_found] exception if there is no entry for [id]. *)
val lookup_schema : string -> Context.ctx_schema

(** [add_lemma id f] will add a formula [f] to be used in other proofs as a
    lemma with the name [id]. *)
val add_lemma : string -> Formula.formula -> unit

(** [lookup_lemma id] returns the formula for lemma with name [id].
    Raises [Not_found] exception if there is no entry for [id]. *)
val lookup_lemma : string -> Formula.formula

(** [add_definition (id, dfn) ] adds a definition with identifier [id] to the
    prover's state. *)
val add_definition : string * Definition.dfn -> unit

(** [lookup_definition id] Returns the definition corresponding to [id].
    Raises [Not_found] exception if there is no entry for [id]. *)
val lookup_definition : string -> Definition.def list

val get_propty_lst : unit -> (string * Type.ty) list

(** [get_ind_count] returns the current depth of induction and increments the
    counter. *)
val get_ind_count : unit -> int

(** [set_sequent other] will replace the current sequent with the values
    from [other]. *)
val set_sequent : Sequent.sequent -> unit

(** [get_sequent] gives the current sequent in the prover's state. *)
val get_sequent : unit -> Sequent.sequent

(** [display_state] prints a formatted output of the sequent's state. *)
val display_state : unit -> unit

(** [reset_prover] resets all proof state to fresh values in order to prepare
    for another proof. *)
val reset_prover : unit -> unit

val induction : int -> unit
val intros : unit -> unit
val case : bool -> string -> unit
val skip : unit -> unit
val exists : Term.term -> unit
val search : Uterms.depth -> unit -> unit
val apply : string -> string list -> Uterms.uwith list -> unit
val assert_thm : Uterms.depth -> Formula.formula -> unit
val split : unit -> unit
val left : unit -> unit
val right : unit -> unit
val weaken : Uterms.depth -> bool -> string -> Term.term -> unit
val permute_ctx : bool -> string -> Context.ctx_expr -> unit

(** [permute remove hyp_name perm] attempts to permute the nominal constants
    in [hyp_name] and adds it to the assumption set if it's possible, removing
    [hyp_name] if [remove] was specified.

    The permutation must be valid with respect to the formula equivalence rules
    for the proof system and the permutation provided must be a complete
    permutation. If these conditions are not met, a failure is raised. *)
val permute : bool -> string -> (Term.id * Term.id) list -> unit

val strengthen : bool -> string -> unit
val inst : Uterms.depth -> bool -> string -> Uterms.uwith list -> unit
val prune : string -> unit
val unfold : string option -> Uterms.uwith list -> unit
val applydfn : string -> string option -> Uterms.uwith list -> unit
