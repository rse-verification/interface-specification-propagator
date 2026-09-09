(*
 * Copyright 2026 Scania CV AB
 * Copyright 2026 KTH
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

let p_result = Isp_options.Self.result

let function_name kf =
  let vi = Kernel_function.get_vi kf in
  if vi.vorig_name = "" then vi.vname else vi.vorig_name

let function_location kf =
  let start_pos, _ = Kernel_function.get_location kf in
  let file =
    Filename.basename (Filepath.to_string (Filepos.path start_pos))
  in
  let line = Filepos.line start_pos in
  (file, line)

let function_has_contract kf =
  Annotations.has_funspec kf
  && not (Cil.is_empty_funspec (Annotations.funspec kf))

let append_unique_kf item items =
  if List.exists (Kernel_function.equal item) !items then ()
  else items := item :: !items

let json_escape text =
  let buffer = Buffer.create (String.length text) in
  String.iter
    (function
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\t' -> Buffer.add_string buffer "\\t"
      | c -> Buffer.add_char buffer c)
    text;
  Buffer.contents buffer

let json_string text = Printf.sprintf "\"%s\"" (json_escape text)

let collect_defined_functions () =
  let definitions = Hashtbl.create 17 in
  let add_global = function
    | GFun (fd, _) ->
        let kf = Globals.Functions.get fd.svar in
        Hashtbl.replace definitions kf fd
    | _ -> ()
  in
  List.iter add_global (Ast.get ()).globals;
  definitions

let collect_direct_calls fd =
  let calls = ref [] in
  let add_varinfo vi =
    if Globals.Functions.mem vi then
      let kf = Globals.Functions.get vi in
      append_unique_kf kf calls
  in
  let visitor =
    object
      inherit Visitor.frama_c_inplace

      method! vstmt_aux stmt =
        (match stmt.skind with
        | Instr (Call (_, Var vi, _, _)) ->
            add_varinfo vi
        | Instr (Local_init (_, ConsInit (vi, _, _), _)) -> add_varinfo vi
        | _ -> ());
        Cil.DoChildren
    end
  in
  ignore (Visitor.visitFramacFunction (visitor :> Visitor.frama_c_visitor) fd);
  List.rev !calls

let build_call_graph definitions =
  let direct_calls = Hashtbl.create 17 in
  let callers = Hashtbl.create 17 in
  let add_edge caller callee =
    if Hashtbl.mem definitions callee then (
      let calls = Option.value (Hashtbl.find_opt direct_calls caller) ~default:[] in
      if not (List.exists (Kernel_function.equal callee) calls) then
        Hashtbl.replace direct_calls caller (callee :: calls);
      let current_callers =
        Option.value (Hashtbl.find_opt callers callee) ~default:[]
      in
      if not (List.exists (Kernel_function.equal caller) current_callers) then
        Hashtbl.replace callers callee (caller :: current_callers))
  in
  Hashtbl.iter
    (fun caller fd -> List.iter (add_edge caller) (collect_direct_calls fd))
    definitions;
  (direct_calls, callers)

let reachable_from_contracted definitions direct_calls =
  let reachable = Hashtbl.create 17 in
  let worklist = Queue.create () in
  Hashtbl.iter
    (fun kf _ -> if function_has_contract kf then Queue.add kf worklist)
    definitions;
  while not (Queue.is_empty worklist) do
    let caller = Queue.take worklist in
    let calls = Option.value (Hashtbl.find_opt direct_calls caller) ~default:[] in
    List.iter
      (fun callee ->
        if not (Hashtbl.mem reachable callee) then (
          Hashtbl.add reachable callee ();
          Queue.add callee worklist))
      calls
  done;
  reachable

let missing_helper_contracts definitions reachable =
  let result = ref [] in
  Hashtbl.iter
    (fun kf _ ->
      if Hashtbl.mem reachable kf && not (function_has_contract kf) then
        result := kf :: !result)
    definitions;
  List.sort
    (fun left right ->
      let left_file, left_line = function_location left in
      let right_file, right_line = function_location right in
      let file_cmp = String.compare left_file right_file in
      if file_cmp <> 0 then file_cmp
      else
        let line_cmp = Int.compare left_line right_line in
        if line_cmp <> 0 then line_cmp
        else String.compare (function_name left) (function_name right))
    !result

let format_callers callers kf =
  Option.value (Hashtbl.find_opt callers kf) ~default:[]
  |> List.sort (fun left right ->
         String.compare (function_name left) (function_name right))

let emit_text_report missing callers =
  if missing = [] then p_result "No missing helper contracts found."
  else (
    p_result "Missing helper contracts:";
    List.iter
      (fun kf ->
        let file, line = function_location kf in
        let caller_names =
          format_callers callers kf |> List.map function_name
          |> String.concat ", "
        in
        let caller_text = if caller_names = "" then "unknown" else caller_names in
        p_result "  %s at %s:%d (called by %s)" (function_name kf) file line
          caller_text)
      missing)

let caller_to_json caller =
  let file, line = function_location caller in
  Printf.sprintf "{\"function\":%s,\"file\":%s,\"line\":%d}"
    (json_string (function_name caller)) (json_string file) line

let missing_to_json callers kf =
  let file, line = function_location kf in
  let caller_json =
    format_callers callers kf |> List.map caller_to_json |> String.concat ","
  in
  Printf.sprintf
    "{\"function\":%s,\"file\":%s,\"line\":%d,\"called_by\":[%s]}"
    (json_string (function_name kf)) (json_string file) line caller_json

let write_json_report path missing callers =
  let items =
    missing |> List.map (missing_to_json callers) |> String.concat ",\n    "
  in
  let json =
    Printf.sprintf "{\n  \"missing_helper_contracts\": [\n    %s\n  ]\n}\n" items
  in
  let oc = open_out path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc json)

let report () =
  let definitions = collect_defined_functions () in
  let direct_calls, callers = build_call_graph definitions in
  let reachable = reachable_from_contracted definitions direct_calls in
  let missing = missing_helper_contracts definitions reachable in
  emit_text_report missing callers;
  match Isp_options.MissingHelperContractsJson.get () with
  | "" -> ()
  | path -> write_json_report path missing callers
