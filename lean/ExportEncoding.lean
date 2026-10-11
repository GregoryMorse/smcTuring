module
public meta import SmcTuring.Native.Encoding
public meta import Lean

open Lean SmcTuring.Native

meta def shape (mode : Mode) (name : String) (form : Form mode) (offset width : Nat) : Json :=
  Json.mkObj [
    ("architecture", toJson (if mode = .x64 then "x64" else "x86")),
    ("name", toJson name),
    ("bytes", toJson ((encode mode form).map BitVec.toNat)),
    ("length", toJson (instructionLength mode form)),
    ("payload_offset", toJson offset), ("payload_width", toJson width)]

meta def memoryShapes (mode : Mode) : List Json :=
  [("exchangeAcc", MemoryOp.exchangeAcc), ("storeAcc", .storeAcc), ("add", .add),
   ("subtract", .subtract), ("bitXor", .bitXor), ("bitAnd", .bitAnd),
   ("exchangeStack", .exchangeStack), ("storeStack", .storeStack),
   ("subtractBorrowZero", .subtractBorrowZero), ("callIndirect", .callIndirect)].map fun (name, operation) =>
    shape mode name (.memory operation 0) ((operation.prefix mode).length + 2) 4

meta def modeShapes (mode : Mode) : List Json :=
  [shape mode "moffs" (.moffs (BitVec.ofNat (8 * mode.wordBytes) 0)) (moffsOperandOffset mode) mode.wordBytes,
   shape mode "exchangeIndirect" .exchangeIndirect 0 0,
   shape mode "callRelative" (.callRelative 0) 1 4] ++ memoryShapes mode

#eval IO.println (toJson (modeShapes .x86 ++ modeShapes .x64)).compress
