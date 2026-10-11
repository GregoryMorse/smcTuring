module
public meta import SmcTuring.Appendix.ByteCode
public meta import Lean

open Lean SmcTuring.Appendix.ByteCode

/-- Finite native-fixture comparator; evaluated output is not a kernel theorem. -/
meta def branchShape (name : String) (form : Form) (addressOffset : Nat)
    (immediateOffset : Nat) : Json :=
  Json.mkObj [("name", toJson name), ("bytes", toJson ((encode form).map BitVec.toNat)),
    ("length", toJson (instructionLength form)), ("address_offset", toJson addressOffset),
    ("immediate_offset", toJson immediateOffset)]

meta def branchShapes : List Json :=
  [branchShape "store" (.immediate .store 0 0) 2 6,
   branchShape "xorImmediate" (.immediate .bitXor 0 0) 2 6,
   branchShape "andImmediate" (.immediate .bitAnd 0 0) 2 6,
   branchShape "exchangeAcc" (.memory .exchangeAcc 0) 2 0,
   branchShape "exchangeStack" (.memory .exchangeStack 0) 2 0,
   branchShape "subtractAcc" (.memory .subtractAcc 0) 2 0,
   branchShape "addAcc" (.memory .addAcc 0) 2 0,
   branchShape "negate" (.memory .negate 0) 2 0,
   branchShape "complement" (.memory .complement 0) 2 0,
   branchShape "sbbZero" (.memory .sbbZero 0) 2 0,
   branchShape "addFour" (.memory .addFour 0) 2 0,
   branchShape "storeAcc" (.storeAcc 0) 1 0,
   branchShape "callRelative" (.callRelative 0) 1 0]

#eval IO.println (toJson branchShapes).compress
