module
public meta import SmcTuring.Appendix.SpacedWhole
public meta import Lean

open Lean SmcTuring.Appendix

/-- Finite comparison at supplied COFF coordinates. This evaluator is not a
kernel proof or a theorem about the loader or physical CPU instruction fetch. -/
meta def spacedRole (sites : SpacedLayout.Sites) (fields : Branching.Fields) (position : Nat) : String :=
  if position == sites.stack + 6 then "pointer"
  else if position == sites.stack + 2 then "address"
  else if position == fields.x then "x"
  else if position == fields.y then "y"
  else if position == fields.mask then "mask"
  else if position == fields.delta then "delta"
  else if position == fields.displacement then "displacement"
  else "invalid"

meta def spacedPacket (sites : SpacedLayout.Sites) (fields : Branching.Fields) (entry : ByteImage.Entry) : Json :=
  let form := entry.packet.initial
  let offsets : List Nat := match entry.packet, form with
    | .both _ _ _, _ => [2, 6]
    | _, .immediate _ _ _ | _, .memory _ _ => [2]
    | _, .storeAcc _ => [1]
    | _, .callRelative _ => []
  let destination := match form with
    | .immediate _ address _ | .memory _ address | .storeAcc address => spacedRole sites fields address.toNat
    | .callRelative _ => "address"
  Json.mkObj [("pc", toJson entry.pc), ("bytes", toJson ((ByteCode.encode form).map BitVec.toNat)),
    ("absolute_offsets", toJson offsets), ("destination", toJson destination), ("owned", toJson entry.fields)]

meta def spacedExport (input : Json) : Except String Json := do
  let signed ← input.getObjValAs? Bool "signed"
  let name ← input.getObjValAs? String "relation"
  let relation ← match name with
    | "lt" => pure BranchAlgebra.Relation.lt
    | "le" => pure .le
    | "eq" => pure .eq
    | "ne" => pure .ne
    | "gt" => pure .gt
    | "ge" => pure .ge
    | _ => throw "unknown relation"
  let sites : SpacedLayout.Sites := ⟨← input.getObjValAs? Nat "stack", ← input.getObjValAs? Nat "start",
    ← input.getObjValAs? Nat "taken", ← input.getObjValAs? Nat "data"⟩
  let fields := SpacedLayout.fields sites signed relation
  let fall := SpacedLayout.fallPC sites signed relation
  let ordered := decide (sites.stack + 10 ≤ sites.start ∧ fall + 30 ≤ sites.taken ∧
    sites.taken + 30 ≤ sites.data ∧ SpacedLayout.endPC sites ≤ 2 ^ 32)
  let checks := SpacedLayout.admissibleChecks sites signed relation
  let valid := checks.all id
  let extents : List (Nat × Nat) := [(sites.stack, sites.stack + 10), (sites.start, fall + 30),
    (sites.taken, sites.taken + 30), (sites.data, sites.data + 20)]
  let sorted := extents.mergeSort (fun first second => decide (first.1 ≤ second.1))
  let gaps := (sorted.zip sorted.tail).map (fun pair => pair.2.1 - pair.1.2)
  pure (Json.mkObj [("signed", toJson signed), ("relation", toJson name), ("valid", toJson valid),
    ("admissible_checks", toJson checks), ("ordered", toJson ordered),
    ("backward", toJson (decide (sites.taken < fall))), ("regions", toJson extents),
    ("sites", input), ("fall", toJson fall), ("fall_end", toJson (fall + 30)),
    ("taken_end", toJson (sites.taken + 30)), ("image_end", toJson (SpacedLayout.endPC sites)),
    ("delta", toJson (SpacedLayout.delta sites signed relation).toNat),
    ("gaps", toJson gaps),
    ("fields", Json.mkObj [("x", toJson fields.x), ("y", toJson fields.y), ("mask", toJson fields.mask),
      ("delta", toJson fields.delta), ("displacement", toJson fields.displacement),
      ("pointer", toJson (sites.stack + 6)), ("address", toJson (sites.stack + 2))]),
    ("packets", toJson ((SpacedLayout.entries sites signed relation 0 0).map (spacedPacket sites fields)))])

#eval (do
  let some path ← IO.getEnv "SMCTURING_BRANCH_SITES" | throw (IO.userError "missing placement file")
  let text ← IO.FS.readFile path
  let output : Except String Json := do
    let input ← Json.parse text
    let rows ← input.getArr?
    let result ← rows.toList.mapM spacedExport
    pure (toJson result)
  match output with
  | .ok json => IO.println json.compress
  | .error message => throw (IO.userError message)
  : IO Unit)
