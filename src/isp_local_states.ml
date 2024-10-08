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

(** A state local to the ISP plugin. This state is not visible for external plugins. *)

open Cil_types
open Cil

let p_debug = Isp_options.Self.debug
let p_result = Isp_options.Self.result
let p_warning = Isp_options.Self.warning

(** Used to store the current [kinstr] and [kernel_function]. 
    Todo: move the match process to here for get functions.*)
module type Visitor_State = sig
  val get_ki : unit -> Cil_types.kinstr
  val update_ki : Cil_types.kinstr -> unit
  val frama_c_plain_copy_is_none : unit -> bool
  val get_frama_c_plain_copy : unit -> Visitor.frama_c_visitor
  val update_frama_c_plain_copy : Visitor.frama_c_visitor -> unit
  val fn_entry_request_is_none : unit -> bool
  val get_fn_entry_request : unit -> Eva.Results.request
  val update_fn_entry_request : Eva.Results.request -> unit
  val clear_fn_entry_request : unit -> unit
end

module Visitor_State : Visitor_State = struct
  let ki = ref (Cil_datatype.Kinstr.kinstr_of_opt_stmt None)
  let kf = ref None
  let frama_c_plain_copy = ref None
  let fn_entry_request = ref None
  let get_ki () = !ki

  let frama_c_plain_copy_is_none () =
    match !frama_c_plain_copy with
    | Some _ -> false
    | None -> true

  let get_frama_c_plain_copy () =
    match !frama_c_plain_copy with
    | Some pc -> pc
    | None ->
        failwith
          "Isp: there must be a frama_c_plain_copy in the state at this point!"

  let update_ki new_ki = ki := new_ki
  let update_frama_c_plain_copy new_v = frama_c_plain_copy := Some new_v

  let fn_entry_request_is_none () =
    match !fn_entry_request with
    | Some _ -> false
    | None -> true

  let get_fn_entry_request () =
    match !fn_entry_request with
    | Some er -> er
    | None ->
        failwith "Isp: there must be an entry_request in the state at this point!"

  let update_fn_entry_request req = fn_entry_request := Some req
  let clear_fn_entry_request () = fn_entry_request := None
end

module type Global_Vars = sig
  val add : int -> unit
  val contains : int -> bool

  module type Global_Vars_Hashtbl_Sig = sig
    val contains : string -> bool
    val is_empty : unit -> bool
    val add : lval -> unit
    val iter : (string -> lval -> unit) -> unit
    val clear : unit -> unit
  end

  module Accessed_Global_Vars : Global_Vars_Hashtbl_Sig
  module Mutated_Global_Vars : Global_Vars_Hashtbl_Sig

  val clear : unit -> unit
end

(** A set containing the global variables declared in the given C module.
    Todo: Tested on single file C module. Need to test on multi-file C modules. *)
module Global_Vars : Global_Vars = struct
  module IntSet = Set.Make (Int)

  let ids = ref IntSet.empty
  let contains id = IntSet.exists (fun x -> x = id) !ids

  let add id =
    ids := IntSet.add id !ids;
    p_debug "·· Added global variable has id: %d." id

  module type Global_Vars_Hashtbl_Sig = sig
    val contains : string -> bool
    val is_empty : unit -> bool
    val add : lval -> unit
    val iter : (string -> lval -> unit) -> unit
    val clear : unit -> unit
  end

  (** A hash table containing [key : string representation of name] [value : Cil_types.lval] of 
    the global variables that has been read or mutated during the execution of the currently visited 
    function.
    Todo: Convert this into a set of lvals instead of a hashmap (*Requires significant rewrite to be worth it*)
    *)
  module Global_Hashtbl = struct
    let contains name hashtable =
      match Hashtbl.find_opt hashtable name with
      | None -> false
      | Some _ -> true

    let is_empty hashtable = Hashtbl.length hashtable = 0

    let add lv ?tblname:(tbl="hashtable") hashtable =
      if Isp_utils.is_array_with_lval_index lv then
        Visitor_State.get_ki ()
        |> Eva.Results.before_kinstr
        |> Isp_utils.get_lvals_with_const_index lv
        |> List.iter (fun (name, lv) ->
               Hashtbl.replace hashtable name lv;
               p_debug "· %s is added to %s." name tbl)
      else
        let name = Isp_utils.create_string_of_lval_name lv in
        Hashtbl.replace hashtable name lv;
        p_debug "· %s is added to %s." name tbl

    let iter fn hashtable = Hashtbl.iter fn hashtable

    let clear hashtable = Hashtbl.reset hashtable
  end

  (** A hash table containing [key : string representation of name] [value : Cil_types.lval] of 
    the global variables that has been read during the execution of the currently visited 
    function.
    *)
  module Accessed_Global_Vars = struct
    let (accessed : (string, lval) Hashtbl.t) = Hashtbl.create 200
    let contains name = Global_Hashtbl.contains name accessed
    let is_empty () = Global_Hashtbl.is_empty accessed
    let add lv = Global_Hashtbl.add lv accessed ~tblname:"Accessed_Global_Vars"
    let iter fn = Global_Hashtbl.iter fn accessed
    let clear () = Global_Hashtbl.clear accessed; p_debug "· Cleared Accessed_Global_Vars."
  end

  (** A hash table containing [key : string representation of name] [value : Cil_types.lval] of 
    the global variables that has been mutated during the execution of the currently visited 
    function.
    *)
  module Mutated_Global_Vars = struct
    let (mutated : (string, lval) Hashtbl.t) = Hashtbl.create 200
    let contains name = Global_Hashtbl.contains name mutated
    let is_empty () = Global_Hashtbl.is_empty mutated
    let add lv = Global_Hashtbl.add lv mutated ~tblname:"Mutated_Global_Vars"
    let iter fn = Global_Hashtbl.iter fn mutated
    let clear () = Global_Hashtbl.clear mutated; p_debug "· Cleared Mutated_Global_Vars."
  end

  (** Will clear the global variables set and the Accessed and Mutated hashtables. *)
  let clear () =
    Accessed_Global_Vars.clear ();
    Mutated_Global_Vars.clear ();
    ids := IntSet.empty;
    p_debug "· Cleared Global_Vars."
end

type global_variables_in_fun = {
  mutable read_g : lval list;
  mutable assigned_g : lval list;
}
(** Contains lists of the global variables that have been mutated or accessed. *)

(** Contains a hashtable with [kernel_function]s as key, and [global_variables_in_fun] 
    as value. *)
module type Fun_Access_Mutate = sig
  val get_opt : kernel_function -> global_variables_in_fun option

  val add : kernel_function -> unit
  (** Adds a function and the global variables it uses. *)

  val clear : unit -> unit
end

(** Contains lists of the mutated and accessed global variables of each function. *)
module Fun_Access_Mutate : Fun_Access_Mutate = struct
  let hashtable : (kernel_function, global_variables_in_fun) Hashtbl.t =
    Hashtbl.create 200

  let get_opt kf = Hashtbl.find_opt hashtable kf

  let add kf =
    let gvf : global_variables_in_fun = { read_g = []; assigned_g = [] } in
    Global_Vars.Accessed_Global_Vars.iter (fun _name lv ->
        gvf.read_g <- lv :: gvf.read_g);
    Global_Vars.Mutated_Global_Vars.iter (fun _name lv ->
        gvf.assigned_g <- lv :: gvf.assigned_g);
    Hashtbl.replace hashtable kf gvf

  let clear () =
    Hashtbl.reset hashtable;
    p_debug "· Cleared Fun_Access_Mutate."
end

(** Contains a set with the Ids of the function arguments, and a list of the argumetns 
    that needs spec emission. *)
module type Visited_function_arguments = sig
  val non_ptr_arg_ids_contain : int -> bool
  (** A set with the Ids of the function arguments that are not a pointer. *)

  val non_ptr_arg_ids_length : unit -> int
  (** Returns the length of the non_ptr_args set *)

  val add_non_ptr_arg : int -> unit
  (** Adds a new Id to the set of none pointer arguments. *)

  val ptr_arg_ids_contain : int -> bool
  (** A set with the Ids of the function arguments that are not a pointer. *)

  val ptr_arg_ids_length : unit -> int
  (** Returns the length of the ptr_args set *)

  val add_ptr_arg : int -> unit
  (** Adds a new Id to the set of none pointer arguments. *)

  val add_non_ptr_arg_to_emit : lval -> unit
  (** Adds a new argument to the list of arguments that needs spec emission. *)

  val get_non_ptr_args_to_emit : unit -> lval list
  (** Gets the list of arguments that needs spec emission. *)

  val non_ptr_args_to_emit_contains : Cil_types.lval -> bool
  (** Checks if the list of arguments to emit contains the given lval. *)

  val add_mut_ptr_arg_to_emit : lval -> unit
  (** Adds a mutated pointer argument to the list of arguments that needs spec emission. *)

  val mut_ptr_args_to_emit_is_empty : unit -> bool
  (** Checks if there are mutated pointer arguments. *)

  val get_mut_ptr_arg_to_emit : unit -> lval list
  (** Gets the list of mutated pointer arguments that needs spec emission. *)

  val mut_ptr_args_to_emit_contains : lval -> bool
  (** Checks if the list contains the given lval. *)

  val add_acc_ptr_arg_to_emit : lval -> unit
  (** Adds a accessed pointer argument to the list of arguments that needs spec emission. *)

  val get_acc_ptr_arg_to_emit : unit -> lval list
  (** Gets the list of accessed pointer arguments that needs spec emission. *)

  val acc_ptr_args_to_emit_contains : lval -> bool
  (** Checks if the list contains the given lval. *)

  val reset : unit -> unit
  (** Restes the set to an empty set. *)
end

module Visited_function_arguments : Visited_function_arguments = struct
  module IntSet = Set.Make (Int)

  let non_ptr_arg_ids = ref IntSet.empty

  let non_ptr_arg_ids_contain id =
    IntSet.exists (fun x -> x = id) !non_ptr_arg_ids

  let non_ptr_arg_ids_length () = IntSet.cardinal !non_ptr_arg_ids
  let add_non_ptr_arg id = non_ptr_arg_ids := IntSet.add id !non_ptr_arg_ids
  let ptr_arg_ids = ref IntSet.empty
  let ptr_arg_ids_contain id = IntSet.exists (fun x -> x = id) !ptr_arg_ids
  let ptr_arg_ids_length () = IntSet.cardinal !ptr_arg_ids
  let add_ptr_arg id = ptr_arg_ids := IntSet.add id !ptr_arg_ids
  let non_ptr_args_to_emit = ref []
  let mut_ptr_args_to_emit = ref []
  let acc_ptr_args_to_emit = ref []

  let add_non_ptr_arg_to_emit lv =
    non_ptr_args_to_emit := lv :: !non_ptr_args_to_emit;
    p_debug "·· The lval %a is added to non_ptr_args_to_emit." Printer.pp_lval
      lv

  let get_non_ptr_args_to_emit () = !non_ptr_args_to_emit

  let non_ptr_args_to_emit_contains lv =
    List.exists (fun l -> l == lv) !non_ptr_args_to_emit

  let add_mut_ptr_arg_to_emit lv =
    mut_ptr_args_to_emit := lv :: !mut_ptr_args_to_emit;
    p_debug "·· The lval %a is added to mut_ptr_args_to_emit." Printer.pp_lval
      lv

  let mut_ptr_args_to_emit_is_empty () = List.length !mut_ptr_args_to_emit = 0
  let get_mut_ptr_arg_to_emit () = !mut_ptr_args_to_emit

  let mut_ptr_args_to_emit_contains lv =
    List.exists (fun l -> l = lv) !mut_ptr_args_to_emit

  let add_acc_ptr_arg_to_emit lv =
    acc_ptr_args_to_emit := lv :: !acc_ptr_args_to_emit;
    p_debug "·· The lval %a is added to acc_ptr_args_to_emit." Printer.pp_lval
      lv

  let get_acc_ptr_arg_to_emit () = !acc_ptr_args_to_emit

  let acc_ptr_args_to_emit_contains lv =
    List.exists (fun l -> l = lv) !acc_ptr_args_to_emit

  let reset () =
    non_ptr_arg_ids := IntSet.empty;
    non_ptr_args_to_emit := [];
    mut_ptr_args_to_emit := [];
    acc_ptr_args_to_emit := [];
    ptr_arg_ids := IntSet.empty;
    p_debug "· Reseted Visited_function_arguments."
end

(** Contains functions that modify the states in [Isp_local_states]. *)
module Utils = struct
  (** Will store the lvals of global variables of an expression in [Accessed_Global_Vars]. *)
  let process_global_access_and_mutations e =
    p_debug "· Finding accesses and mutations in the expression: %a"
      Printer.pp_exp e;
    let lvals =
      Isp_utils.extract_lvals_from_exp
        (Visitor_State.get_frama_c_plain_copy ())
        e
    in
    List.iter
      (fun lv ->
        match lv with
        | Var vi, _ ->
            if Global_Vars.contains vi.vid then
              let name = Isp_utils.create_string_of_lval_name lv in
              if not (Global_Vars.Accessed_Global_Vars.contains name) then
                Global_Vars.Accessed_Global_Vars.add lv
              else ()
        | Mem e, _ ->
            let vi =
              match e.enode with
              | Lval (Var vi, _) -> vi
              | _ ->
                  failwith
                    "Isp: The pointer can only contain an expression of type \
                     lval at this point."
            in
            if
              Visited_function_arguments.ptr_arg_ids_contain vi.vid
              && not
                   (Visited_function_arguments.acc_ptr_args_to_emit_contains lv)
            then Visited_function_arguments.add_acc_ptr_arg_to_emit lv)
      lvals

  (** Will store the accessed and mutated global variable by the given function
      in [Accessed_Global_Vars] and [Mutated_Global_Vars]
      todo: refactor this.*)
  let add_function_access_and_mutations kf =
    (match Fun_Access_Mutate.get_opt kf with
    | None ->
        (* TODO: This warning seems to be incorrect. The function is not unknown,
           it just happens to NOT access or mutate any global variables. *)
        p_warning "A function call to an unknown function: %s"
          (Kernel_function.get_name kf)
    | Some access_and_mutations ->
        List.iter
          (fun lv -> Global_Vars.Accessed_Global_Vars.add lv)
          access_and_mutations.read_g;

        List.iter
          (fun lv -> Global_Vars.Mutated_Global_Vars.add lv)
          access_and_mutations.assigned_g);
    p_debug
      "· Completed adding the accessed and mutated global vars of function %s."
      (Kernel_function.get_name kf)

  (** Will process the accesses and mutations of global variables, and the accesses of function arguments.  *)
  let process_expression e =
    p_debug "· Processing expression %a" Printer.pp_exp e;
    let lvals =
      Isp_utils.extract_lvals_from_exp
        (Visitor_State.get_frama_c_plain_copy ())
        e
    in
    List.iter
      (fun lv ->
        match lv with
        | Var vi, _ ->
            if Global_Vars.contains vi.vid then (
              let name = Isp_utils.create_string_of_lval_name lv in
              if not (Global_Vars.Accessed_Global_Vars.contains name) then
                Global_Vars.Accessed_Global_Vars.add lv)
            else if
              Visited_function_arguments.non_ptr_arg_ids_contain vi.vid
              && not
                   (Visited_function_arguments.non_ptr_args_to_emit_contains lv)
            then Visited_function_arguments.add_non_ptr_arg_to_emit lv
        | Mem e, _ ->
            (* Todo: this is a repeated code. Refactor this. *)
            let vi =
              match e.enode with
              | Lval (Var vi, _) -> vi
              | _ ->
                  failwith
                    "Isp: The pointer can only contain an expression of type \
                     lval at this point."
            in
            if
              Visited_function_arguments.ptr_arg_ids_contain vi.vid
              && not
                   (Visited_function_arguments.acc_ptr_args_to_emit_contains lv)
            then Visited_function_arguments.add_acc_ptr_arg_to_emit lv)
      lvals
end
