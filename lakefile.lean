import Lake
open Lake DSL

-- We depend on Batteries for MLList
require batteries from git
  "https://github.com/leanprover-community/batteries.git" @ "main"

package «simple-prolog» where
  -- add package configuration options here

lean_lib «SimpleProlog» where
  -- add library configuration options here

@[default_target]
lean_exe «simple-prolog» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
