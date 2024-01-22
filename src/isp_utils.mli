(** Contains general functions for extractin, converting, and other simmilar tasks on data types. *)

val extract_lvals_from_exp :
  Visitor.frama_c_visitor -> Cil_types.exp -> Cil_types.lval list
(** Extracts the [Cil_types.lval]s form an expression. *)

val create_string_of_lval_name : Cil_types.lval -> string
(** Creates a string representation of a variable from varinfo and offset.
Example: [varinfo = "x"] and [offset = 2] : will return ["x[2]"] *)

val lval_to_address_term : Cil_types.lval -> Cil_types.term
(** Will create a term that represents the address of the given lval.
    Todo: this will not work for arrays. The offset is ignored here. 
    Todo: commented code.*)

val lval_to_term : Cil_types.lval -> Cil_types.term
(** Converts a [Cil_types.lval] to [Cil_types.term]. *)

val abstract_int_to_term_int : Integer.t -> Cil_types.term
(** Converts an [Integer.t] to a [Cil_types.term]. *)

val abstract_float_to_term_float : Fval.F.t -> Cil_types.term
(** Converts an [Fval.F.t] to a [Cil_types.term]. *)

val get_eva_analysis_for_lval : Db.Value.state -> Cil_types.lval -> Db.Value.t
(** Gets the eva analysis result for the given lval. *)

val create_subset_ip :
  Cil_types.term -> Integer.t list -> Cil_types.identified_predicate
(** Creates an identified predicate that corrisponds to the ACSL annotation
    t \in s. *)

val is_array_with_lval_index : Cil_types.lval -> bool
(** Checks whether the lval is an array with a lval index. *)

val get_lvals_with_const_index :
  Cil_types.lval -> Db.Value.state -> (string * Cil_types.lval) list
(** Converts a lval of an array with a lval index to a list of [(name, lval)]
    with a constant index *)
