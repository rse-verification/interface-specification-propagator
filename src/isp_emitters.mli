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

(** This module contains the behaviour the is currently being generated for the currently visited function. *)
module type Behavior = sig
  val reset_current_behavior : unit -> unit
  (** Rests the current behaviour to an empty behaviour. *)

  val get_current_behavior : unit -> Cil_types.behavior
  (** Gets the behaviour for the currently visited function. *)
end

module Behavior : Behavior

(** The emitters related to auxiliary specifications.
    Todo: This needs to be refactored. Auxiliary specifications are not part
    of Interface specifications. It's the other way around *)
module type Auxiliary = sig
  val emit :
    Cil_types.exp option ->
    Eva.Results.request ->
    Cil_types.kernel_function ->
    (unit -> unit) Queue.t ->
    unit
  (** Emit the the behavior contract of the given function. 
      Todo: Consider renameing this function.*)
end

module Auxiliary : Auxiliary
