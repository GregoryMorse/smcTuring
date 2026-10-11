module
public meta import SmcTuring.Native.TemplateCopy
public meta import Lean
open Lean SmcTuring.Native TemplateRelocation

public meta def fixtureSpecs (mode : Mode) (externalPC externalField : Nat) : List Spec :=
  [.moffs (.internal (moffsOperandOffset mode)),.moffs (.external externalField),
   .memory .exchangeAcc (.internal (moffsOperandOffset mode)),.memory .storeAcc (.external externalField),
   .memory .add (.internal (moffsOperandOffset mode)),.memory .subtract (.external externalField),
   .memory .bitXor (.internal (moffsOperandOffset mode)),.memory .bitAnd (.external externalField),
   .memory .exchangeStack (.internal (moffsOperandOffset mode)),.memory .storeStack (.external externalField),
   .memory .subtractBorrowZero (.internal (moffsOperandOffset mode)),.memory .callIndirect (.external externalField),
   .call (.internal 0),.call (.external externalPC),.exchangeIndirect]

public meta def signed (next target : Nat) : Bool :=
  decide (-(2^31 : Int) <= Relocation.delta next target) && decide (Relocation.delta next target < (2^31 : Int))

public meta def packet (mode : Mode) (base : Nat) (entry : Nat × Spec) : Json :=
  let pc := entry.1
  let spec := entry.2
  let form := TemplateRelocation.bind mode base pc spec
  let bytes := encode mode form
  let actual := Fetch.fetch mode (fun position => bytes[position]?.getD 0) 0
  let target := match spec with
    | .moffs ref | .memory _ ref | .call ref => some (resolve base ref)
    | _ => none
  let resolved := match form with
    | .moffs address => some address.toNat
    | .memory _ displacement => some (Execution.memoryAddress mode (Arithmetic.encodeNat mode (pc+length mode spec)) displacement).toNat
    | .callRelative displacement => some (Arithmetic.encodeNat mode (pc+5)+Execution.displacementWord mode displacement).toNat
    | _ => none
  Json.mkObj [("pc",toJson pc),("length",toJson (length mode spec)),("bytes",toJson (bytes.map BitVec.toNat)),
    ("target",toJson target),("resolved",toJson resolved),("fetched",toJson (actual==some form)),
    ("reachable",toJson (match spec with
      | .memory op ref => if mode == Mode.x86 then true else signed (pc+length mode (.memory op ref)) (resolve base ref)
      | .call ref => signed (pc+5) (resolve base ref)
      | _ => true))]

public meta def rows (mode : Mode) : List String -> List Json
  | start::source::destination::size::externalPC::externalField::rest =>
    let pc := start.toNat!
    let dest := destination.toNat!
    let count := size.toNat!
    let specs := fixtureSpecs mode externalPC.toNat! externalField.toNat!
    let p : StringMacroLayout.Params := ⟨pc,source.toNat!,dest,count⟩
    Json.mkObj [("start",toJson pc),("source",toJson p.source),("destination",toJson dest),("size",toJson (span mode specs)),
      ("blueprint",toJson ((TemplateCopy.compiledBytes mode p specs).map BitVec.toNat)),
      ("packets",toJson ((places mode dest specs).map (packet mode dest))),
      ("macroBytes",toJson ((StringMacroLayout.bytes mode p).map BitVec.toNat)),
      ("sourceField",toJson (StringCodec.sourceField mode pc)),("destinationField",toJson (StringCodec.destinationField mode pc)),
      ("body",toJson (StringCodec.bodyStart mode pc)),("bodyEnd",toJson (StringCodec.bodyEnd mode pc count)),
      ("end",toJson (StringCodec.endpoint mode pc count))]::rows mode rest
  | _ => []

public meta def main (args : List String) : IO Unit := do
  let mode := if args[0]! == "x64" then Mode.x64 else Mode.x86
  IO.println (toJson (rows mode args.tail)).compress
