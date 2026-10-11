module
public meta import SmcTuring.Native.AccumulatorFinalization
public meta import Lean
open Lean SmcTuring.Native SmcTuring.Native.AccumulatorLayout

public meta def payload (offset width target relocation : Nat) : Json :=
 Json.mkObj [("offset",toJson offset),("width",toJson width),("target",toJson target),("relocation",toJson relocation)]
public meta def nativePacket (mode : Mode) (name : String) (pc target : Nat) (form : Form mode) : Json :=
 let offset := match form with | .moffs _ => moffsOperandOffset mode | _ => (wordPrefix mode).length+2
 Json.mkObj [("name",toJson name),("pc",toJson pc),("bytes",toJson ((encode mode form).map BitVec.toNat)),
   ("payloads",toJson [payload offset 4 target (if mode == .x86 then 6 else 4)])]
public meta def ownerPacket (mode : Mode) (name : String) (field : Nat) (value : Word mode) (relocated : Bool) (target : Nat) : Json :=
 let pc := field-moffsOperandOffset mode
 Json.mkObj [("name",toJson name),("pc",toJson pc),("bytes",toJson ((encode mode (.moffs value)).map BitVec.toNat)),
   ("payloads",toJson (if relocated then [payload (moffsOperandOffset mode) mode.wordBytes target (if mode == .x86 then 6 else 1)] else []))]
public meta def exportLayout (mode : Mode) (input : Json) : Except String Json := do
 let sites <- input.getObjVal? "sites"
 let prologue <- sites.getObjValAs? Nat "prologue"
 let epilogue <- sites.getObjValAs? Nat "epilogue"
 let save <- sites.getObjValAs? Nat "save"
 let pointer <- sites.getObjValAs? Nat "pointer"
 let layout : Layout := Layout.mk prologue epilogue save pointer
 let bodyFirst <- sites.getObjValAs? Nat "body_first"
 let bodySecond <- sites.getObjValAs? Nat "body_second"
 let bodyStore <- sites.getObjValAs? Nat "body_store"
 let body <- sites.getObjValAs? Nat "body"
 let output <- sites.getObjValAs? Nat "output"
 let marker := endPC mode layout
 let terminal := Json.mkObj [("name",toJson "terminal"),("pc",toJson marker),
   ("bytes",toJson ((TerminalMarker.bytes mode marker).map BitVec.toNat)),
   ("payloads",toJson [payload 2 4 (marker+6) (if mode == .x86 then 6 else 8)])]
 let bodyExchange : Form mode := .memory .exchangeAcc (Relocation.instructionDisp mode .exchangeAcc bodyFirst body)
 let bodyRestore := Reader.storeForm mode (Arithmetic.encodeNat mode body) (Relocation.memoryDisp mode bodyStore body)
 let bodyOutput := Reader.storeForm mode (Arithmetic.encodeNat mode output) (Relocation.memoryDisp mode layout.epilogue output)
 let packets := [nativePacket mode "save" layout.prologue layout.save (saveForm mode layout),
   nativePacket mode "bodyFirst" bodyFirst body bodyExchange,nativePacket mode "bodySecond" bodySecond body bodyRestore,
   nativePacket mode "bodyStore" bodyStore output bodyOutput,nativePacket mode "first" layout.epilogue layout.pointer (first mode layout),
   nativePacket mode "second" (secondPC mode layout) layout.pointer (second mode layout),
   nativePacket mode "third" (thirdPC mode layout) layout.save (third mode layout),terminal,
   ownerPacket mode "saveOwner" layout.save 0 false 0,
   ownerPacket mode "pointerOwner" layout.pointer (Arithmetic.encodeNat mode layout.save) true layout.save,
   ownerPacket mode "bodyOwner" body 0 false 0,ownerPacket mode "outputOwner" output 0 false 0]
 let limit := 2^(8*mode.wordBytes)
 let range := fun next target => if mode == .x86 then true else
   let delta := (target : Int)-(next : Int)
   decide (And (-2147483648 <= delta) (delta < 2147483648))
 let checks := [decide (savedPC mode layout < limit),decide (endPC mode layout < limit),
   decide (layout.save+mode.wordBytes <= limit),decide (layout.pointer+mode.wordBytes <= limit),
   decide (Or (layout.save+mode.wordBytes <= layout.pointer) (layout.pointer+mode.wordBytes <= layout.save)),
   range (savedPC mode layout) layout.save,range (secondPC mode layout) layout.pointer,
   range (thirdPC mode layout) layout.pointer,range (endPC mode layout) layout.save]
 pure (Json.mkObj [("sites",sites),("packets",toJson packets),("checks",toJson checks),("marker",toJson marker),
   ("end",toJson (marker+10)),("save_marker_apart",toJson (decide (Or (layout.save+mode.wordBytes <= marker) (marker+10 <= layout.save))))])
public meta def main : IO Unit := do
 let some path <- IO.getEnv "SMCTURING_ACCUMULATOR_SITES" | throw (IO.userError "missing sites")
 let some architecture <- IO.getEnv "SMCTURING_ACCUMULATOR_ARCH" | throw (IO.userError "missing mode")
 let text <- IO.FS.readFile path
 let result : Except String Json := do
   let rows <- ( <- Json.parse text).getArr?
   let output <- rows.toList.mapM (exportLayout (if architecture == "x86" then .x86 else .x64))
   pure (toJson output)
 match result with
 | .ok value => IO.println value.compress
 | .error message => throw (IO.userError message)
