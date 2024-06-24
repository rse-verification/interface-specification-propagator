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

let help_msg = "Propagates interface specifications semanticaly"

module Self = Plugin.Register (struct
  let name = "isp"
  let shortname = "isp"
  let help = help_msg
end)

module Enabled = Self.False (struct
  let option_name = "-isp"

  let help =
    "When on (off by default), the interface specifications that are anotated \
     at the entry point will be propagated."
end)

module EntryPoint = Self.String (struct
  let option_name = "-isp-entry-point"
  let default = ""
  let arg_name = "function-name"
  let help = "the entry-point function name of the module (default: main)"
end)

module Print = Self.False (struct
  let option_name = "-isp-print"

  let help =
    "When on (off by default), the transformed source code will be printed."
end)
