module
public meta import SmcTuring.Appendix.InputDword
public meta import SmcTuring.Native.DwordStore
public meta import Lean
open Lean SmcTuring.Native SmcTuring.Native.LittleEndian SmcTuring.Appendix
public meta def inputPayload (offset target kind : Nat) : Json :=
 Json.mkObj [("offset",toJson offset),("width",toJson 4),("target",toJson target),("relocation",toJson kind)]
public meta def inputPacket (name : String) (pc : Nat) (bytes : List Byte) (payloads : List Json) : Json :=
 Json.mkObj [("name",toJson name),("pc",toJson pc),("bytes",toJson (bytes.map BitVec.toNat)),("payloads",toJson payloads)]
public meta def inputExport (mode : Mode) (input : Json) : Except String Json := do
 let sites <- input.getObjVal? "sites"
 let start <- sites.getObjValAs? Nat "start"
 let source <- sites.getObjValAs? Nat "source"
 let target <- sites.getObjValAs? Nat "target"
 let compare <- sites.getObjValAs? Nat "compare"
 let corrected <- input.getObjValAs? Bool "corrected"
 let sourceField := source+(if corrected then 6 else 0)
 let targetField := target+3
 let layout : DwordLayout.Layout := { start := start, source := sourceField, destination := targetField }
 let second := DwordLayout.secondPC mode layout
 let third := DwordLayout.thirdPC mode layout
 let endpoint := DwordLayout.endPC mode layout
 let kind := if mode = .x86 then 6 else 4
 let packets := [inputPacket "first" start (DwordCode.encode mode (DwordLayout.first mode layout)) [inputPayload 2 sourceField kind],
   inputPacket "second" second (DwordCode.encode mode (DwordLayout.second mode layout)) [inputPayload (if mode = .x86 then 1 else 2) targetField kind],
   inputPacket "third" third (DwordCode.encode mode (DwordLayout.third mode layout)) [inputPayload 2 sourceField kind],
   inputPacket "source" source (InputOperand.sourceBytes (Relocation.memoryDisp mode (source+10) (compare+6)) 0x80000000)
      [inputPayload 2 (compare+6) (if mode = .x86 then 6 else 8)],
   inputPacket "target" target (InputOperand.targetBytes 0x80000000) [],
   inputPacket "compare" compare (DwordStore.encode (DwordStore.emit mode compare (compare+6) 0))
      [inputPayload 2 (compare+6) (if mode = .x86 then 6 else 8)]]
 pure (Json.mkObj [("sites",sites),("corrected",toJson corrected),("source_field",toJson sourceField),("target_field",toJson targetField),
   ("end",toJson endpoint),("admissible",toJson (DwordLayout.checks mode layout)),("packets",toJson packets)])
public meta def main : IO Unit := do
 let some path <- IO.getEnv "SMCTURING_INPUT_SITES" | throw (IO.userError "missing sites")
 let some architecture <- IO.getEnv "SMCTURING_INPUT_ARCH" | throw (IO.userError "missing mode")
 let text <- IO.FS.readFile path
 let result : Except String Json := do
  let rows <- ( <- Json.parse text).getArr?
  let output <- rows.toList.mapM (inputExport (if architecture == "x86" then .x86 else .x64))
  pure (toJson output)
 match result with
 | .ok value => IO.println value.compress
 | .error message => throw (IO.userError message)
