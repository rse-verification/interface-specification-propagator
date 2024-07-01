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

open Cil_types
open Cil

let p_debug = Isp_options.Self.debug
let p_result = Isp_options.Self.result
let p_warning = Isp_options.Self.warning

type spec_type = Requires | Ensures | Assigns | Assumes

module type Behavior = sig
  val reset_current_behavior : unit -> unit
  val get_current_behavior : unit -> Cil_types.behavior
end

module Behavior = struct
  let current_behavior = ref (Cil.mk_behavior ())

  let reset_current_behavior () =
    current_behavior := Cil.mk_behavior ();
    p_debug "· Reseted current_behavior."

  let get_current_behavior () = !current_behavior
end

module type Auxiliary = sig
  val emit :
    exp option ->
    Eva.Results.request ->
    kernel_function ->
    (unit -> unit) Queue.t ->
    unit
end

module Auxiliary = struct
  let emitter =
    Emitter.create "Auxiliary Specification Emitter" [ Emitter.Funspec ]
      ~correctness:[] ~tuning:[]


  (** Adds required [\valid_read] of the accessed global variables which have
      not been mutated to the infered behavior contract of the given function. *)
  let emit_req_valid_read new_kf filling_actions =
    Isp_local_states.Global_Vars.Accessed_Global_Vars.iter (fun name lv ->
        if not (Isp_local_states.Global_Vars.Mutated_Global_Vars.contains name)
        then (
          let term = Isp_utils.lval_to_address_term lv in
          let ip : identified_predicate =
            Logic_const.new_predicate
              (Logic_const.pvalid_read (BuiltinLabel Here, term))
          in

          Queue.add
            (fun () ->
              Annotations.add_requires emitter new_kf
                [ ip ])
            filling_actions;

          p_debug "·· Emitted: require \\valid_read %a"
            Printer.pp_identified_predicate ip ~level:2));
    List.iter
      (fun lv ->
        if
          not
            (Isp_local_states.Visited_function_arguments
             .mut_ptr_args_to_emit_contains lv)
        then
          match lv with
          | Mem { enode = Lval lv }, _ ->
              let t = Isp_utils.lval_to_term lv in
              let ip : identified_predicate =
                Logic_const.new_predicate
                  (Logic_const.pvalid_read (BuiltinLabel Here, t))
              in

              Queue.add
                (fun () ->
                  Annotations.add_requires emitter new_kf [ ip ])
                filling_actions;

              p_debug "·· Emitted: require \\valid_read %a"
                Printer.pp_identified_predicate ip ~level:2
          | _ -> ())
      (Isp_local_states.Visited_function_arguments.get_acc_ptr_arg_to_emit ());
    List.iter
      (fun lv ->
        match lv with
        | Mem { enode = Lval lv }, _ ->
            let t = Isp_utils.lval_to_term lv in

            let ipv =
              Logic_const.new_predicate
                (Logic_const.pvalid (Logic_const.here_label, t))
            in
            let ipvr =
              Logic_const.new_predicate
                (Logic_const.pvalid_read (Logic_const.here_label, t))
            in
            let ip_list = [ ipvr; ipv ] in
            Queue.add
              (fun () ->
                Annotations.add_requires emitter new_kf
                   ip_list)
              filling_actions;
            p_debug "·· Emitted: require %a" Printer.pp_identified_predicate
              ipvr ~level:2;
            p_debug "·· Emitted: require %a" Printer.pp_identified_predicate ipv
              ~level:2
        | _ -> ())
      (Isp_local_states.Visited_function_arguments.get_mut_ptr_arg_to_emit ())

  (** Add required [\valid_read] and [\valid] for global variables that have 
      been mutated to the infered behavior contract of the given function.
      Todo: The name is missleading because this function add [\valid_read] as well.
      Todo: Rework program to not emit both [\valid] and [\valid_read] for the same variable since [\valid] implies [\valid_read].*)
  let emit_req_valid new_kf filling_actions =
    Isp_local_states.Global_Vars.Mutated_Global_Vars.iter (fun _name lv ->
        let t : term = Isp_utils.lval_to_address_term lv in
        let ipv =
          Logic_const.new_predicate
            (Logic_const.pvalid (Logic_const.here_label, t))
        in
        let ipvr =
          Logic_const.new_predicate
            (Logic_const.pvalid_read (Logic_const.here_label, t))
        in
        let ip_list = [ ipvr; ipv ] in
        Queue.add
          (fun () ->
            Annotations.add_requires emitter new_kf
              ip_list)
          filling_actions;
        p_debug "·· Emitted: require %a" Printer.pp_identified_predicate ipvr
          ~level:2;
        p_debug "·· Emitted: require %a" Printer.pp_identified_predicate ipv
          ~level:2)

  (** Add assigns for global variables that have been mutated to the infered
      behavior contract of the given function.
      Todo: Refactor the conversion.*)
  let emit_assigns new_kf filling_actions =
    if
      Isp_local_states.Global_Vars.Mutated_Global_Vars.is_empty ()
      && Isp_local_states.Visited_function_arguments
         .mut_ptr_args_to_emit_is_empty ()
    then (
      Queue.add
        (fun () ->
          Annotations.add_assigns ~keep_empty:false emitter new_kf
             (Writes []))
        filling_actions;
      p_debug "·· Emitted: assignes \\nothing" ~level:2)
    else
      let em lv =
        let t : term = Isp_utils.lval_to_term lv in
        let it : identified_term = Logic_const.new_identified_term t in
        Queue.add
          (fun () ->
            Annotations.add_assigns ~keep_empty:false emitter new_kf
              (Writes [ (it, FromAny) ]))
          filling_actions;
        p_debug "·· Emitted: assignes %a" Printer.pp_identified_term it ~level:2
      in
      Isp_local_states.Global_Vars.Mutated_Global_Vars.iter (fun _ lv -> em lv);
      List.iter
        (fun lv -> em lv)
        (Isp_local_states.Visited_function_arguments.get_mut_ptr_arg_to_emit ())

  (** Add ensures for the given term with the eva analysis results to the
      infered behavior contract of the given function. *)
  let emit_eva_result_of_term spec_type term eva_result new_kf filling_actions =
    (* This checks that eva_result is a properly generated ivalue and not an error which it will be if the term is a pointer. *)
    if Result.is_ok eva_result then
      let i : Ival.t = Result.get_ok eva_result in
      let ip_list =
        if Ival.is_int i then (
          p_debug "··· The range is of type int." ~level:3;
          if Ival.is_singleton_int i then (
            p_debug "··· The range contains a single value." ~level:3;
            let iv = Ival.project_int i in
            let it = Logic_const.tint iv in
            let ip =
              Logic_const.prel (Req, term, it) |> Logic_const.new_predicate
            in
            [ ip ])
          else if Ival.is_small_set i then (
            p_debug "··· The range contains a small set of values." ~level:3;
            let ivs = Option.get (Ival.project_small_set i) in
            let ip = Isp_utils.create_subset_ip term ivs in
            [ ip ])
          else (
            p_debug "··· The range contains is an interval of values." ~level:3;
            let lower_bound = Option.get (Ival.min_int i) in
            let upper_bound = Option.get (Ival.max_int i) in
            let lower_term = Logic_const.tint lower_bound in
            let pl : predicate = Logic_const.prel (Rge, term, lower_term) in
            let ipl : identified_predicate = Logic_const.new_predicate pl in
            let upper_term = Logic_const.tint upper_bound in
            let pu : predicate = Logic_const.prel (Rle, term, upper_term) in
            let ipu : identified_predicate = Logic_const.new_predicate pu in
            [ ipl; ipu ]))
        else if Ival.is_float i then (
          p_debug "··· The range is of type floating-point." ~level:3;
          match Ival.min_and_max_float i with
          | Some (l, u), nan ->
              let ip =
                if l = u then
                  let v = Isp_utils.abstract_float_to_term_float l in
                  let p = Logic_const.prel (Req, term, v) in
                  Logic_const.new_predicate p
                else
                  let l = Isp_utils.abstract_float_to_term_float l in
                  let u = Isp_utils.abstract_float_to_term_float u in
                  let pl = Logic_const.prel (Rge, term, l) in
                  let pu = Logic_const.prel (Rle, term, u) in
                  let p = Logic_const.pand (pl, pu) in
                  if nan then
                    p_warning "The range of values for %a contain a NaN!"
                      Printer.pp_term term;
                  Logic_const.new_predicate p
              in
              [ ip ]
          | _ ->
              p_warning "The values of %a is NaN!" Printer.pp_term term;
              [])
        else (
          p_warning "Unknown type for the range!";
          [])
      in
      if List.length ip_list = 0 then
        p_warning "Analysis for term %a is not implemented!" Printer.pp_term term
      else
        match spec_type with
        | Ensures ->
            let tk_ip_list = List.map (fun ip -> (Normal, ip)) ip_list in
            Queue.add
              (fun () ->
                Annotations.add_ensures emitter new_kf
                  tk_ip_list)
              filling_actions;
            p_debug "·· Emitted: ensures for %a." Printer.pp_term term ~level:2
        | Requires ->
            Queue.add
              (fun () ->
                Annotations.add_requires emitter new_kf
                   ip_list)
              filling_actions
        | _ ->
            failwith "Isp: Only Ensures and Requires are currently implemented!"
    else
      p_warning
        "The term %a is a pointer! Eva can't evaluate this, and thus no \
         annotations are created for this term."
        Printer.pp_term term

  (** Add 'spec_type' annotations for the given lval to the infered behavior
      contract of the given function. 'to_term' is a function that converts
      an lval into a term. *)
  let emit_lval_spec spec_type lvalue to_term req new_kf filling_actions =
    let rec find_field_offsets typ =
      match Cil.unrollType typ with
      | TNamed _ -> 
        (* TODO: May be the case with TPtr TArray etc. Check Cil.unrollTypeDeep. *)
        failwith "Trying to emit annotations for non-unrolled type."
      | TComp (compinfo, _) ->
          List.flatten 
            (List.map
              (fun fieldinfo ->
                let o = find_field_offsets fieldinfo.ftype in
                List.map (fun f -> Field (fieldinfo, f)) o)
              (Option.value compinfo.cfields ~default:[]))
      | _ -> [NoOffset]
    in
    match Cil.unrollType (Cil.typeOfLval lvalue) with
    | TNamed _ -> 
      (* TODO: May be the case with TPtr TArray etc. Check Cil.unrollTypeDeep. *)
      failwith "Trying to emit annotations for non-unrolled type."
    | TComp _ as styp->
        let (lhost, _) = lvalue in
        let offsets = find_field_offsets styp in
        p_debug "···· number of found offsets %i" (List.length offsets) ~level:4;
        List.iter 
          (fun o ->
            let term = to_term (lhost, o) in
            let eva_result = Isp_utils.get_eva_analysis_for_lval req (lhost, o) in
            emit_eva_result_of_term spec_type term eva_result new_kf filling_actions)
          offsets
    | _ ->
      p_debug "···· non TComp type" ~level:4;
      let term = to_term lvalue in
      let eva_result = Isp_utils.get_eva_analysis_for_lval req lvalue in
      emit_eva_result_of_term spec_type term eva_result new_kf filling_actions

  (** Add ensures for the mutated global variables to the infered behavior contract
      of the given function. *)
  let emit_ensures_for_m_g_v req new_kf filling_actions =
    Isp_local_states.Global_Vars.Mutated_Global_Vars.iter (fun name lv ->
        p_debug "··· Emitting ensures for global variable %s" name ~level:3;
        emit_lval_spec Ensures lv Isp_utils.lval_to_term req new_kf filling_actions)

  let emit_ensures_for_ptr_func_args req new_kf filling_actions =
    List.iter
      (fun lv ->
        p_debug "··· Emitting ensures for pointer argument %a." Printer.pp_lval
          lv ~level:3;
        emit_lval_spec Ensures lv Isp_utils.lval_to_term req new_kf filling_actions)
      (Isp_local_states.Visited_function_arguments.get_mut_ptr_arg_to_emit ())

  (** Add ensures for the result (when exist) to the infered behavior contract
      of the given function. *)
  let emit_ensures_for_results exp_opt req new_kf filling_actions =
    let emit_ensure_for_non_lval_result_expression e req new_kf filling_actions =
      let term = Cil.typeOf e |> Logic_const.tresult in
      let eva_result = Eva.Results.eval_exp e req in
      emit_eva_result_of_term Ensures term (Eva.Results.as_ival eva_result) new_kf filling_actions
    in
    let to_term lvalue =
      let typ = Cil.typeOfLval lvalue in
      let (_, offset) = lvalue in
       p_debug "··· Emitting ensures for result expression %a." Printer.pp_lval lvalue ~level:3;
      Logic_const.term (TLval(TResult typ, Logic_utils.offset_to_term_offset offset)) (Ctype typ)
    in
    match exp_opt with
    | None -> ()
    | Some ({enode = Lval lvalue; _}) -> emit_lval_spec Ensures lvalue to_term req new_kf filling_actions
    | Some e -> emit_ensure_for_non_lval_result_expression e req new_kf filling_actions

  let emit_req_for_function_parameters new_kf filling_actions =
    let req = Isp_local_states.Visitor_State.get_fn_entry_request () in
    let em lv =
      emit_lval_spec Requires lv Isp_utils.lval_to_term req new_kf filling_actions
    in
    List.iter
      (fun lv ->
        p_debug "··· Emitting requires for non-pointer function argument %a."
          Printer.pp_lval lv ~level:3;
        em lv)
      (Isp_local_states.Visited_function_arguments.get_non_ptr_args_to_emit ());
    List.iter
      (fun lv ->
        p_debug "··· Emitting requires for pointer function argument %a."
          Printer.pp_lval lv ~level:3;
        em lv)
      (Isp_local_states.Visited_function_arguments.get_acc_ptr_arg_to_emit ())

  let emit_req_for_global_variables new_kf filling_actions =
    let req = Isp_local_states.Visitor_State.get_fn_entry_request () in
    Isp_local_states.Global_Vars.Accessed_Global_Vars.iter (fun name lv ->
        p_debug "··· Emitting requires for accessed global variable %s." name ~level:3;
        emit_lval_spec Requires lv Isp_utils.lval_to_term req new_kf filling_actions)

  let emit_function_contract new_kf filling_actions =
    Queue.add
      (fun () ->
        Annotations.add_behaviors emitter new_kf
          [ Behavior.get_current_behavior () ])
      filling_actions

  let emit exp_opt req new_kf filling_actions =
    p_debug "· Start emission process for functions %s"
      (Kernel_function.get_name new_kf);
    emit_req_valid_read new_kf filling_actions;
    emit_req_valid new_kf filling_actions;
    emit_req_for_function_parameters new_kf filling_actions;
    emit_req_for_global_variables new_kf filling_actions;
    emit_assigns new_kf filling_actions;
    emit_ensures_for_m_g_v req new_kf filling_actions;
    emit_ensures_for_ptr_func_args req new_kf filling_actions;
    emit_ensures_for_results exp_opt req new_kf filling_actions;
    emit_function_contract new_kf filling_actions;
    p_debug "· Emission process for functions %s is completed."
      (Kernel_function.get_name new_kf)
end
