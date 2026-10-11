module
public meta import SmcTuring.Appendix.DivisionBlocks
public meta import Lean
open Lean SmcTuring.Appendix

/-- A finite independent PC/length comparator. JSON evaluation is not a proof
of complete native packets or physical CPU semantics. -/
public meta def main (args : List String) : IO Unit := do
  if args.length != 4 then throw (IO.userError "Expected four unsigned/signed mode origins")
  let rows := args.zipIdx |>.map fun (origin, mode) =>
    let layout : DivisionBlocks.Layout :=
      {origin := BitVec.ofNat 32 origin.toNat!, fields := fun _ => 0,
       mod := decide (mode % 2 = 1), signed := decide (2 ≤ mode),
       pointer := 0, address := 0, entryDisplacement := 0, backDisplacement := 0}
    let lengths := [DivisionBlocks.Block.initial, .guard, .body, .finish].map fun block =>
      (DivisionBlocks.words layout block).map DivisionControl.dataLength
    Json.mkObj [
      ("mode", toJson mode), ("origin", toJson layout.origin.toNat),
      ("data_lengths", toJson lengths),
      ("initial_span", toJson (DivisionBlocks.initialSpan layout)),
      ("finish_span", toJson (DivisionBlocks.finishSpan layout)),
      ("guard_continuation", toJson (DivisionBlocks.guardContinuation layout).toNat),
      ("guard", toJson (DivisionBlocks.guardPC layout).toNat),
      ("body_continuation", toJson (DivisionBlocks.bodyContinuation layout).toNat),
      ("body", toJson (DivisionBlocks.bodyPC layout).toNat),
      ("exit_continuation", toJson (DivisionBlocks.exitContinuation layout).toNat),
      ("exit", toJson (DivisionBlocks.exitPC layout).toNat),
      ("end", toJson (DivisionBlocks.endPC layout).toNat),
      ("delta", toJson (DivisionBlocks.delta layout).toNat),
      ("back_delta", toJson (DivisionBlocks.backDelta layout).toNat)]
  IO.println (toJson rows).compress
