open Cil_types

let p_result = Isp_options.Self.result
let p_debug = Isp_options.Self.debug
let p_warning = Isp_options.Self.warning

let ( -- ) i j =
  let rec aux n acc =
    if Integer.lt n i then acc else aux (Integer.sub n Integer.one) (n :: acc)
  in
  aux j []

module LvalSet = Set.Make (Cil_datatype.Lval)

let rec extract_lvals_from_exp frama_c_visitor e result =
  match e.enode with
  | Const _ ->
      p_debug "·· Const is found in the expression. (do nothing)" ~level:2;
      result
  | Lval (Var vi, o) ->
      p_debug "·· Lval of Var is found in the expression." ~level:2;
      let new_lv = Visitor.visitFramacLval frama_c_visitor (Var vi, o) in
      new_lv :: result
  | Lval (Mem e, o) ->
      p_debug "·· Lval of Mem is found in the expression: %a." Printer.pp_lval
        (Mem e, o) ~level:2;
      let new_lv = Visitor.visitFramacLval frama_c_visitor (Mem e, o) in
      new_lv :: result
  | BinOp (_, e1, e2, _) ->
      p_debug "·· BinOp is found in the expression." ~level:2;
      extract_lvals_from_exp frama_c_visitor e2 result
      |> extract_lvals_from_exp frama_c_visitor e1
  | CastE (_, ec) ->
      p_debug "·· CastE is found in the expression." ~level:2;
      extract_lvals_from_exp frama_c_visitor ec result
  | _ ->
      p_warning "Expression %a is not supported!" Printer.pp_exp e;
      result

let extract_lvals_from_exp frama_c_visitor e =
  extract_lvals_from_exp frama_c_visitor e []

let get_enum_value ei =
  match ei.eival.enode with
  | Const c -> (
      p_debug "··· The type of the Enum is Const." ~level:3;
      match c with
      | CInt64 (i, _, _) ->
          p_debug "··· The Const is of type Int64." ~level:3;
          Format.sprintf "%d" (Integer.to_int_exn i)
      | _ -> failwith "Isp: Enum Const value not covered.")
  | _ -> failwith "Isp: Enum not covered."

let rec get_index_as_string e =
  match e.enode with
  | Const c -> (
      p_debug "·· The index is of type Const." ~level:2;
      match c with
      | CInt64 (i, _, _) ->
          p_debug "·· The type of the Const is Int64." ~level:2;
          Format.sprintf "%d" (Integer.to_int_exn i)
      | CEnum ei ->
          p_debug "·· The type of the Const is Enum." ~level:2;
          get_enum_value ei
      | _ ->
          failwith
            "Isp: Indexes of arrays can only be integers.Other expressions are \
             not supported")
  | CastE (_, exp) ->
      p_debug "·· The index is of type CastE." ~level:2;
      get_index_as_string exp
  | Lval (lh, _) -> (
      match lh with
      | Var vi -> vi.vname
      | Mem _ -> failwith "Isp: Mem is not supported.")
  | _ ->
      p_warning "Expression %a is not supported!" Printer.pp_exp e;
      failwith "Isp: Should not end up here!"

let create_string_of_lval_name (lh, o) =
  let vi =
    match lh with
    | Var v -> v
    | Mem _ -> failwith "Isp: Mem is not implemented!"
  in
  let offset_string =
    match o with
    | NoOffset -> ""
    | Index (e, _) ->
        let e_str = get_index_as_string e in
        String.concat "" [ "["; e_str; "]" ]
    | Field (_, _) -> Format.asprintf "%a" Printer.pp_offset o
  in
  String.concat "" [ vi.vname; offset_string ]

let lval_to_address_term lv =
  let tl = Logic_utils.lval_to_term_lval lv in
  Logic_utils.mk_logic_AddrOf tl (Cil.typeOfTermLval tl)

let lval_to_term lv =
  let e = Cil.new_exp ~loc:Cil_datatype.Location.unknown (Lval lv) in
  Logic_utils.expr_to_term e

(* Todo: remove this function, (became too simple after the bug fix). *)
let abstract_int_to_term_int i = Logic_const.tint i
let abstract_float_to_term_float f = Fval.F.to_float f |> Logic_const.treal

let get_eva_analysis_for_lval req lv =
  let eva_result = Eva.Results.as_ival(Eva.Results.eval_lval lv req) (*!Db.Value.eval_lval None state lv*) in  (*Change pending*)
  eva_result

let create_subset_ip t ivs =
  let its = List.map (fun iv -> abstract_int_to_term_int iv) ivs in
  let li = Cil_const.make_logic_info "\\subset" in
  li.l_tparams <- [ "a" ];
  let s1 = Cil_const.make_logic_var_formal "s1" Linteger in
  let s2 = Cil_const.make_logic_var_formal "s2" Linteger in
  li.l_profile <- [ s1; s2 ];
  let tn1 = Tunion [ t ] in
  let t1 = Logic_const.term tn1 Linteger in
  let tn2 = Tunion its in
  let t2 = Logic_const.term tn2 Linteger in
  let p = Logic_const.papp (li, [], [ t1; t2 ]) in
  Logic_const.new_predicate p

let is_array_with_lval_index (lh, o) =
  match lh with
  | Var _ -> (
      match o with
      | Index ({ enode = Lval _; _ }, _) ->
          p_debug "·· The lval is an array with a lval index." ~level:2;
          true
      | _ -> false)
  | _ -> false

let get_lvals_with_const_index (lh, o) req =
  match lh with
  | Var vi -> (
      match o with
      | Index ({ enode = Lval lv_idx; _ }, _) ->
          let res = Eva.Results.as_ival(Eva.Results.eval_lval lv_idx req)(*!Db.Value.eval_lval None state lv_idx*) in   (*Change pending*)
          let i : Ival.t = Eva.Results.default Ival.zero res in     (*Don't know if zero is a good default, but it should not default (I think)*)
          let values =
            if Ival.is_singleton_int i then (
              p_debug "··· The lval index evaluates to a single value." ~level:3;
              let iv = Ival.project_int i in
              [ iv ])
            else if Ival.is_small_set i then (
              p_debug "··· The lval index evaluates to a small set of values."
                ~level:3;
              Option.get (Ival.project_small_set i))
            else (
              p_debug "··· The lval index evaluates to an interval of values."
                ~level:3;
              let liv = Option.get (Ival.min_int i) in
              let uiv = Option.get (Ival.max_int i) in
              liv -- uiv)
          in
          List.fold_left
            (fun list value ->
              let idx = Format.sprintf "%d" (Integer.to_int_exn value) in
              let name = String.concat "" [ vi.vname; "["; idx; "]" ] in
              let dummy_e =
                Cil.dummy_exp (Const (CInt64 (value, IInt, None)))
              in
              let new_o = Index (dummy_e, NoOffset) in
              (name, (lh, new_o)) :: list)
            [] values
      | _ -> failwith "Isp: should not reach here! (get_lvals)")
  | _ -> failwith "Isp: should not reach here! (get_lvals)"
