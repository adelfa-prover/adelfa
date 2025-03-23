exception Reported_parse_error

type id = string
type pos = Lexing.position * Lexing.position

type uterm =
  | UConst of pos * id
  | ULam of pos * (pos * id * Type.ty option) * uterm
  | UPi of pos * (pos * id) * uterm * uterm
  | UApp of pos * uterm * uterm
  | UType of pos

val get_const_id : uterm -> id
val get_pos : uterm -> pos
val change_pos : pos -> uterm -> uterm
val get_hid_and_args : uterm -> id * uterm list

type uctx =
  | UNil of pos
  | UVar of pos * id
  | UCtxTm of pos * uctx * (id * uterm)

type aid = id * Type.ty option

type uformula =
  | UTop
  | UBottom
  | UImp of uformula * uformula
  | UOr of uformula * uformula
  | UAnd of uformula * uformula
  | UAll of (pos * aid) list * uformula
  | UExists of (pos * aid) list * uformula
  | UCtx of (pos * id * id) list * uformula
  | UAtm of uctx * uterm * uterm * Formula.annotation
  | UProp of uterm

type uschema = ((pos * id) list * (pos * id * uterm) list) list
type udef = uformula * uformula

type clearable =
  | Keep of id
  | Remove of id

type uwith =
  | Cws of id * uctx
  | Vws of id * uterm

type depth =
  | DefaultDepth
  | WithDepth of int

type setting = SearchDepth of int

val is_cws : uwith -> bool
val unwrap_cws : uwith -> id * uctx
val is_vws : uwith -> bool
val unwrap_vws : uwith -> id * uterm

type common_command =
  | Undo
  | Set of setting list

type command =
  | Skip
  | Search of depth
  | Ind of int
  | Apply of clearable * clearable list * uwith list
  | Case of clearable
  | Exists of uterm
  | Split
  | Left
  | Right
  | Intros
  | Assert of uformula * depth
  | Abort
  | Weaken of clearable * uterm * depth
  | PermuteCtx of clearable * uctx
  | Permute of clearable * (id * id) list
  | Strengthen of clearable
  | Inst of clearable * uwith list * depth
  | Prune of id
  | Unfold of id option * uwith list
  | AppDfn of id * id option * uwith list
  | Common of common_command

type top_command =
  | Theorem of id * uformula
  | Schema of id * uschema
  | Specification of string
  | Quit
  | Define of aid * udef list
  | TopCommon of common_command

type sig_decl =
  | Const of id * uterm
  (* | Define of id * uterm option * uterm *)
  (* | Abbrev of id * uterm option * uterm *)
  | Fixity of id * Signature.fixity
(* | Name of id * id * id option *)
(* | Query of int * int * id option * uterm *)
(* | Clause of id * uterm option * uterm *)
(* | Solve of (id * id * uterm option) list * id option * uterm *)
(* | Tabled of id *)
(* | QueryTabled of int * int * id option * uterm *)
(* | Deterministic of id *)
(* | Mode of (mode * id * uterm option) list * uterm *)
(* | Terminates of order * callpat list *)
(* | Reduces of placeholder *)
(* | Block of id * (id * uterm option) list * (id * uterm option) *)
(* | Worlds of id list * callpat list *)
(* | Total of order * callpat list *)
(* | Freeze of id list *)
(* | Theorem of id * mform *)
(* | Prove of int * order * callpat list *)
(* | Establish of int * order * callpat list *)
(* | Assert of callpat list *)
(* | Use of id *)

val extract_unbound_uform : id list -> uformula -> id list

module Print : sig
  val pr_str : Format.formatter -> string -> unit
  val pr_uterm : Format.formatter -> uterm -> unit
  val pr_uctxtm : Format.formatter -> uctx -> unit
  val pr_uctx : Format.formatter -> uctx -> unit
  val pr_uform : Format.formatter -> uformula -> unit
  val pr_locctxs : Format.formatter -> (pos * id * id) list -> unit
  val pr_locidtys : Format.formatter -> (pos * aid) list -> unit
  val pr_common : Format.formatter -> common_command -> unit
  val pr_setting : Format.formatter -> setting -> unit
  val pr_settings : Format.formatter -> setting list -> unit
  val pr_perm : Format.formatter -> (string * string) list -> unit
  val pr_command : Format.formatter -> command -> unit
  val pr_clearable : Format.formatter -> clearable -> unit
  val pr_clearablelist : Format.formatter -> clearable list -> unit
  val pr_args : Format.formatter -> clearable list -> unit
  val pr_with : Format.formatter -> uwith -> unit
  val pr_withs : Format.formatter -> uwith list -> unit
  val pr_aid : Format.formatter -> string * Type.ty option -> unit
  val pr_udef : Format.formatter -> uformula * uformula -> unit
  val pr_udefs : Format.formatter -> (uformula * uformula) list -> unit

  val pr_uschema
    :  Format.formatter
    -> (('a * string) list * ('b * string * uterm) list) list
    -> unit

  val pr_ublockschema
    :  Format.formatter
    -> ('a * string) list * ('b * string * uterm) list
    -> unit

  val pr_locentries : Format.formatter -> ('a * string * uterm) list -> unit
  val pr_locids : Format.formatter -> ('a * string) list -> unit
  val pr_topcommand : Format.formatter -> top_command -> unit
  val pr_subst : Format.formatter -> (string * Term.term) list -> unit
  val string_of_uterm : uterm -> string
  val string_of_command : command -> string
  val string_of_topcommand : top_command -> string
end
