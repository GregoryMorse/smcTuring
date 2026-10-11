module
public meta import SmcTuring.Native.TerminalMarker
public meta import Lean
open Lean SmcTuring.Native
public meta def exportTerminal (mode : Mode) (input : Json) : Except String Json := do
  let pc <- input.getObjValAs? Nat "pc"
  let variant <- input.getObjValAs? Nat "mode"
  let target := pc + (if variant == 1 then 6 else 0)
  let form := DwordStore.emit mode pc target 0
  pure (Json.mkObj [("pc",toJson pc),("target",toJson target),("mode",toJson variant),
    ("bytes",toJson ((DwordStore.encode form).map BitVec.toNat)),("length",toJson 10),
    ("operand_offset",toJson 6),("next_pc",toJson (pc+10))])
public meta def main : IO Unit := do
  let some path <- IO.getEnv "SMCTURING_TERMINAL_SITES" | throw (IO.userError "missing sites")
  let some architecture <- IO.getEnv "SMCTURING_TERMINAL_ARCH" | throw (IO.userError "missing architecture")
  let text <- IO.FS.readFile path
  let output : Except String Json := do
    let input <- Json.parse text
    let rows <- input.getArr?
    let result <- rows.toList.mapM (exportTerminal (if architecture == "x86" then .x86 else .x64))
    pure (toJson result)
  match output with
  | .ok value => IO.println value.compress
  | .error message => throw (IO.userError message)
