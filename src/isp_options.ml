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
