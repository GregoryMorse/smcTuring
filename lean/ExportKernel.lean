module
public meta import SmcTuring.Dolan.FourRegisters

open SmcTuring.Dolan

meta def registerIndex (r : Mov.Register) : Nat := (Four.slot r).val

meta def instructionLine (i : Mov.Instruction) : String :=
  match i with
  | .immediate r (.address n) => s!"imm {registerIndex r} address {n}"
  | .immediate r (.offset b) => s!"imm {registerIndex r} offset {if b then 1 else 0}"
  | .load r b o => s!"load {registerIndex r} {registerIndex b} {registerIndex o}"
  | .store b o r => s!"store {registerIndex b} {registerIndex o} {registerIndex r}"

#eval for instruction in Mov.kernelProgram do IO.println (instructionLine instruction)
