(*
 * Copyright 2024 Scania CV AB
 * Copyright 2024 KTH
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 *
 *  SPDX-License-Identifier: GPL-2.0+
 *)

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

val abstract_float_to_term_float : Fval.F.t -> Cil_types.term
(** Converts an [Fval.F.t] to a [Cil_types.term]. *)

val get_eva_analysis_for_lval : Eva.Results.request -> Cil_types.lval -> Ival.t Eva.Results.result
(** Gets the eva analysis result for the given lval. *)

val create_subset_ip :
  Cil_types.term -> Integer.t list -> Cil_types.identified_predicate
(** Creates an identified predicate that corrisponds to the ACSL annotation
    t \in s. *)

val is_array_with_lval_index : Cil_types.lval -> bool
(** Checks whether the lval is an array with a lval index. *)

val get_lvals_with_const_index :
  Cil_types.lval -> Eva.Results.request -> (string * Cil_types.lval) list
(** Converts a lval of an array with a lval index to a list of [(name, lval)]
    with a constant index *)
