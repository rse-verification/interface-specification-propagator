open Cil_types
open Cil

let p_debug = Isp_options.Self.debug
let p_result = Isp_options.Self.result
let p_warning = Isp_options.Self.warning

class interface_specifications_propagator _ep prj =
  object (self)
    inherit Visitor.generic_frama_c_visitor (Visitor_behavior.copy prj)

    method! vglob_aux g =
      if Isp_local_states.Visitor_State.frama_c_plain_copy_is_none () then
        Isp_local_states.Visitor_State.update_frama_c_plain_copy
          self#frama_c_plain_copy;
      match g with
      | GType (ti, _) ->
          p_debug "GType is found: %s." ti.tname;
          JustCopy
      | GCompTag (ci, _) ->
          p_debug "GCompTag is found: %s." ci.cname;
          JustCopy
      | GCompTagDecl (_, _) ->
          p_warning "GCompTagDecl is not covered!";
          JustCopy
      | GEnumTag (ei, _) ->
          p_debug "GEnumTag is Found: %s." ei.ename;
          JustCopy
      | GEnumTagDecl (_, _) ->
          p_warning "GEnumTagDecl is not covered!";
          JustCopy
      | GVarDecl (_, _) ->
          p_warning "GVarDecl is not covered!";
          JustCopy
      | GAsm (_, _) ->
          p_warning "GAsm is not covered!";
          JustCopy
      | GPragma (_, _) ->
          p_warning "GPragma is not covered!";
          JustCopy
      | GText _ ->
          p_warning "GText is not covered!";
          JustCopy
      | GAnnot (_, _) ->
          p_warning "GAnnot is not covered!";
          JustCopy
      | GVar (vi, _, _) ->
          p_debug "Processing global variable: %a." Printer.pp_varinfo vi;
          p_debug "· Adding global variable %a to Global_Vars."
            Printer.pp_varinfo vi;
          Isp_local_states.Global_Vars.add vi.vid;
          JustCopy
      | GFunDecl (_, vi, _) ->
          p_debug "Skipping global function declaration: %a." Printer.pp_varinfo
            vi;
          JustCopy
      | GFun (fd, _) ->
          p_debug "Processing global function: %s" fd.svar.vname;
          let kf = Option.get self#current_kf in
          if not (Eva.Results.is_called kf) then (
            p_warning "Unreachable function: %s" fd.svar.vname;
            JustCopy)
          (* else if fd.svar.vname = ep then 
            (
              p_debug "Glob.";
              JustCopy) *)
          else (
            Isp_local_states.Global_Vars.Accessed_Global_Vars.clear ();
            Isp_local_states.Global_Vars.Mutated_Global_Vars.clear ();
            Isp_local_states.Visited_function_arguments.reset ();
            Isp_emitters.Behavior.reset_current_behavior ();
            Isp_local_states.Visitor_State.clear_fn_entry_request ();
            p_debug "· Adding arguments to Visited_function_arguments.";
            List.iter
              (fun vi ->
                match unrollType vi.vtype with
                | TPtr _ ->
                    Isp_local_states.Visited_function_arguments.add_ptr_arg
                      vi.vid;
                    p_debug
                      "·· Id (%d) of pointer argument %a added to \
                       Visited_function_arguments."
                      vi.vid Printer.pp_varinfo vi ~level:2
                | TInt _ | TFloat _ | TComp _ ->
                    Isp_local_states.Visited_function_arguments.add_non_ptr_arg
                      vi.vid;
                    p_debug
                      "·· Id (%d) of int/float argument %a added to \
                       Visited_function_arguments."
                      vi.vid Printer.pp_varinfo vi ~level:2                  
                | TEnum _ ->
                    p_warning "Arguments of Enum type (%a) are not implemented!"
                      Printer.pp_typ vi.vtype
                | _ ->
                    p_warning "Arguments with type %a are not implemented!"
                      Printer.pp_typ vi.vtype)
              fd.sformals;
            DoChildren)

    method! vstmt_aux s =
      p_debug "· Processing statement: %a" Printer.pp_stmt s;
      Isp_local_states.Visitor_State.update_ki self#current_kinstr;
      if Isp_local_states.Visitor_State.fn_entry_request_is_none () then
        Eva.Results.before_kinstr self#current_kinstr
        |> Isp_local_states.Visitor_State.update_fn_entry_request;
      if not (Eva.Results.is_reachable s) then (
        p_warning "Unreachable statement: %a" Printer.pp_stmt s;
        JustCopy)
      else
        match s.skind with
        | Instr i ->
            p_debug "· The statement is an instruction.";
            (match i with
            | Set (lv, e, _) ->
                p_debug "· The instruction is of type Set.";
                (match lv with
                | Var vi, _ ->
                    p_debug "· The left side of the Set is of type Var.";
                    (* Store assigned variable if global. *)
                    if Isp_local_states.Global_Vars.contains vi.vid then (
                      p_debug "· The Var is a global variable.";
                      Visitor.visitFramacLval self#frama_c_plain_copy lv
                      |> Isp_local_states.Global_Vars.Mutated_Global_Vars.add)
                    else if
                      Isp_local_states.Visited_function_arguments
                      .ptr_arg_ids_contain vi.vid
                    then (
                      p_debug
                        "· The Var is one of the pointer arguments of the \
                         current function.";
                      p_warning "External pointer mutation is not emplemented!")
                | Mem e_inner, _ -> (
                    p_debug
                      "· The left side of the Set is of type Mem (pointer \
                       dereference): %a."
                      Printer.pp_lval lv;
                    match e_inner.enode with
                    | Lval lv_inner -> (
                        match lv_inner with
                        | Var vi, _ ->
                            if
                              Isp_local_states.Visited_function_arguments
                              .ptr_arg_ids_contain vi.vid
                              && not
                                   (Isp_local_states.Visited_function_arguments
                                    .mut_ptr_args_to_emit_contains lv)
                            then (
                              p_debug
                                "· The Var is one of the pointer arguments of \
                                 the current function.";
                              Isp_local_states.Visited_function_arguments
                              .add_mut_ptr_arg_to_emit lv)
                        | Mem _, _ ->
                            p_warning "Nested pointers are not implemented!")
                    | _ ->
                        p_warning
                          "Dereferencing expression %a is not implemented!"
                          Printer.pp_exp e_inner));
                (* Store read global variables*)
                Visitor.visitFramacExpr self#frama_c_plain_copy e
                |> Isp_local_states.Utils.process_expression
            | Call (lv_o, e, _, _) -> (
                p_debug "· The instruction is of type Call.";
                (match lv_o with
                | None -> ()
                | Some (Var vi, o) ->
                    p_debug "· The lval of the Call is of type Var.";
                    if Isp_local_states.Global_Vars.contains vi.vid then(
                      Visitor.visitFramacLval self#frama_c_plain_copy (Var vi, o)
                      |> Isp_local_states.Global_Vars.Mutated_Global_Vars.add)
                | Some (Mem _, _) ->
                    p_warning
                      "The lval of the Call is of type Mem. Not implemented \
                       yet!");

                match e.enode with
                | Lval lv -> (
                    p_debug "· The right side expression is of type Lval.";
                    match lv with
                    | Var vi, _o -> (
                        p_debug "· The Lval is of type Var.";
                        match vi.vtype with
                        | TFun (_, _, _, _) ->
                            p_debug "· The Var is a function.";
                            let kf = Globals.Functions.find_by_name vi.vname in
                            Isp_local_states.Utils
                            .add_function_access_and_mutations kf
                        | _ -> p_warning "Unknown type of Var")
                    | Mem _, _ ->
                        p_warning "The Lval is of type Mem. (not implemented).")
                | _ ->
                    p_warning "The expression: %a is not implemented yet!"
                      Printer.pp_exp e)
            | Local_init (_, li, _) -> (
                p_debug "· The instruction is of type Local_init.";
                match li with
                | AssignInit (ini : init) -> (
                    (* The right side is an expression, a structure, a union or an array *)
                    match ini with
                    | SingleInit e ->
                        p_debug
                          "· The right side of the Local_init is an expression.";
                        Isp_local_states.Utils.process_expression e
                    | CompoundInit _ ->
                        (* if the right side is a structure, a union or an array *)
                        p_warning
                          "The right side of the Local_init is CompoundInit. \
                           (Not implemented)")
                | ConsInit (vi, e_l, _) ->
                    p_debug
                      "· The right side of the Local_init is a function call.";

                    List.iter
                      (fun e ->
                        Visitor.visitFramacExpr self#frama_c_plain_copy e
                        |> Isp_local_states.Utils.process_expression)
                      e_l;

                    let kf = Globals.Functions.find_by_name vi.vname in
                    Isp_local_states.Utils.add_function_access_and_mutations kf)
            | Asm (_, _, _, _) ->
                p_warning "The Asm instruction is not implemented!"
            | Skip _ -> ()
            | Code_annot (_, _) ->
                p_warning "The Code_annot instruction is not implemented!");
            JustCopy
        | Return (exp_opt, _) ->
            (* TODO: Implement a solution for multiple return instructions in a function. *)
            p_debug "· The statemen is a return.";
            (match exp_opt with
            | None -> p_debug "· Processing return void"
            | Some e ->
                (* Todo: this might be wrong what if the expression contains a function
                          call that mutates some global variables? *)
                Visitor.visitFramacExpr self#frama_c_plain_copy e
                |> Isp_local_states.Utils.process_expression);
            let req = Eva.Results.before_kinstr self#current_kinstr in
            let kf = Option.get self#current_kf in
            let new_kf =
              Visitor_behavior.Get.kernel_function self#behavior kf
            in
            let filling_actions = self#get_filling_actions in
            Isp_emitters.Auxiliary.emit exp_opt req new_kf filling_actions;
            Isp_local_states.Fun_Access_Mutate.add kf;
            JustCopy
        | Goto ({ contents = _ }, (_, _)) ->
            p_debug "· Goto is found.";
            JustCopy
        | Break (_, _) ->
            p_debug "· The statemen is a Break.";
            JustCopy
        | Continue (_, _) ->
            p_warning "Continue is not covered!";
            JustCopy
        | If (e, _, _, _) ->
            p_debug "· The statemen is an if-statement.";
            Visitor.visitFramacExpr self#frama_c_plain_copy e
            |> Isp_local_states.Utils.process_expression;
            DoChildren
        | Switch (e, _, _, _) ->
            p_debug "· The statemen is a switch-statement.";
            Visitor.visitFramacExpr self#frama_c_plain_copy e
            |> Isp_local_states.Utils.process_expression;
            DoChildren
        | Loop (_, _, (_, _), _, _) ->
            p_warning "Loop is not covered!";
            JustCopy
        | Block _ ->
            p_debug "· Block is found.";
            DoChildren
        | UnspecifiedSequence _ ->
            p_warning "UnspecifiedSequence is not covered!";
            JustCopy
        | Throw (_, (_, _)) ->
            p_warning "Throw is not covered!";
            JustCopy
        | TryCatch (_, _, (_, _)) ->
            p_warning "TryCatch is not covered!";
            JustCopy
        | TryFinally (_, _, (_, _)) ->
            p_warning "TryFinally is not covered!";
            JustCopy
        | TryExcept (_, (_, { eloc = _, _; _ }), _, (_, _)) ->
            p_warning "TryExcept is not covered!";
            JustCopy
  end

let execute_isp () =
  (* Reset All States *)
  Isp_local_states.Global_Vars.clear ();
  Isp_local_states.Fun_Access_Mutate.clear ();
  let ep =
    if Isp_options.EntryPoint.get () = "" then (
      p_result
        "No entry point was specified! The default entry point \"main\" will \
         be used.";
      "main")
    else Isp_options.EntryPoint.get ()
  in
  p_result "Execute Eva with entry point \"%s\"" ep;
  Globals.set_entry_point ep true;  
  Eva.Analysis.compute ();
  p_result "Eva analysis is completed.";
  let propagated_acsl =
    File.create_project_from_visitor "Propagated_ACSL"
      (new interface_specifications_propagator ep)
  in
  if Isp_options.Print.get () then (
    p_result "The transformed source code:";
    File.pretty_ast ~prj:propagated_acsl ())
