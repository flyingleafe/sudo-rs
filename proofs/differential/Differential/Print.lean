import Differential.Sanitize
import SudoersSpec.Grammar.PermissionRender

/-! Render alias declarations using the core renderer also used for permission lines. -/

namespace Differential.Print

open SudoersSpec SudoersSpec.Grammar.PermissionPrint

def def_ (kind : String) (f : α → String) (d : Def α) : String :=
  s!"{kind} {d.name} = {specList f d.items}"

/-- One alias definition line. -/
def anyDef : Differential.AnyDef → String
  | .user d => def_ "User_Alias" user d
  | .runas d => def_ "Runas_Alias" user d
  | .host d => def_ "Host_Alias" id d
  | .cmnd d => def_ "Cmnd_Alias" command d

end Differential.Print
