(*
 * Copyright 2026 Scania CV AB
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 *  SPDX-License-Identifier: GPL-2.0+
 *)

(** Stable diagnostic formatting for the ISP plugin.

    Warnings are deliberately non-fatal: ISP can still emit a partial
    specification. Fatal paths keep Frama-C's normal failure behaviour while
    adding an identifier that can be searched in logs and test output. *)

let warning code message = Isp_options.Self.warning "[%s] %s" code message

let failure code message =
  failwith (Printf.sprintf "[%s] %s" code message)
