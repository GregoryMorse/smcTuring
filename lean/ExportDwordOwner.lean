module
public meta import SmcTuring.Native.DwordOwner
public meta import Lean
open Lean SmcTuring.Native
public meta def ownerPacket (mode : Mode) (pc : Nat) (value : Nat) : Json :=
 Json.mkObj [("value",toJson value),("bytes",toJson ((DwordOwner.bytes mode pc (BitVec.ofNat 32 value)).map BitVec.toNat))]
public meta def main : IO Unit := do
 let some path <- IO.getEnv "SMCTURING_OWNER_SITES" | throw (IO.userError "missing sites")
 let some architecture <- IO.getEnv "SMCTURING_OWNER_ARCH" | throw (IO.userError "missing mode")
 let source <- IO.FS.readFile path
 let result : Except String Json := do
  let input <- Json.parse source
  let pc <- input.getObjValAs? Nat "pc"
  let live <- input.getObjVal? "live"
  let rows <- live.getArr?
  let values <- rows.toList.mapM (fun row => row.getObjValAs? Nat "value")
  let mode := if architecture == "x86" then Mode.x86 else .x64
  pure (Json.mkObj [("pc",toJson pc),("endpoint",toJson (pc+10)),("field",toJson (pc+6)),("width",toJson 4),
    ("initial",ownerPacket mode pc 0),("live",toJson (values.map (ownerPacket mode pc))),
    ("relocation",toJson (if mode = .x86 then 6 else 8))])
 match result with
 | .ok value => IO.println value.compress
 | .error message => throw (IO.userError message)
