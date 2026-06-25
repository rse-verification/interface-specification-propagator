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

let same lval1 lval2 =
  Cil_datatype.Lval.equal lval1 lval2
  || Format.asprintf "%a" Printer.pp_lval lval1
     = Format.asprintf "%a" Printer.pp_lval lval2

let unique lvals =
  List.fold_left
    (fun acc lval ->
      if List.exists (same lval) acc then acc else lval :: acc)
    [] lvals
  |> List.rev

let pointer_base_lval = function
  | Mem { enode = Lval lv }, _ -> Some lv
  | _ -> None

let rec exp_is_lval lv e =
  match e.enode with
  | Lval rhs_lv -> same rhs_lv lv
  | CastE (_, e) -> exp_is_lval lv e
  | _ -> false
