module
public import SmcTuring.Appendix.Listing8SetupWrites
public import SmcTuring.Appendix.Listing8MacroWriteBounds
public import SmcTuring.Native.StringMoveWrites
public import SmcTuring.Native.StringRestoreWrites

public section
namespace SmcTuring.Appendix.Listing8MacroWrites
open Native StringMacroLayout StringMacroEffects
abbrev Placement:=Listing8MacroWriteBounds.Placement

theorem setup (mode : Mode) (codeStart codeEnd : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode codeStart codeEnd p) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringSetup.forms mode p.start p.source p.destination).map (StringWrites.liftString mode)) state := by
  have fields:=Listing8MacroWriteBounds.fields mode codeStart codeEnd p state ready placed
  have buffers:=Listing8MacroWriteBounds.buffers mode codeStart codeEnd p state ready placed
  have packets:=StringMacroImage.initializer_windows mode p state ready
  exact Listing8SetupWrites.owned mode codeStart codeEnd p.start p.source p.destination state ready.entry
    (prefix_capacity mode p state ready) packets.1 packets.2 fields.1 fields.2 buffers.1 buffers.2

theorem moves (mode : Mode) (codeStart codeEnd : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode codeStart codeEnd p) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringMoves.forms mode (StringPlan.widths mode p.size)).map (StringWrites.liftString mode))
      (StringMacroEffects.setup mode p state) := by
  have total:=StringPlan.total mode p.size
  change (StringPlan.widths mode p.size).sum=p.size at total
  have destination:=destination_capacity mode p state ready
  have forward : (StringMacroEffects.setup mode p state).backwards=false := by rw [setup_effect mode p state ready];exact ready.forward
  have fits : (StringMacroEffects.setup mode p state).destinationIndex.toNat+(StringPlan.widths mode p.size).sum<2^(8*mode.wordBytes) := by
    rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ destination.2.2,total]
    exact destination.1
  exact StringMoveWrites.owned mode codeStart codeEnd _ _ (StringPlan.positive mode p.size) forward fits
    (Listing8MacroWriteBounds.copied_bounds mode codeStart codeEnd p state ready placed)

theorem destination_endpoint (mode : Mode) (p : Params) :
    StringRestore.endpoint mode (destinationTail mode p) p.size=endpoint mode p := by
  simp only [destinationTail,StringRestore.endpoint,sourceTail,endpoint,StringCodec.endpoint]
  omega

theorem restores (mode : Mode) (codeStart codeEnd : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode codeStart codeEnd p) :
    StringWrites.OwnedRun mode codeStart codeEnd
      ((StringRestore.forms mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size).map (StringWrites.liftString mode)) (copied mode p state) ∧
    StringWrites.OwnedRun mode codeStart codeEnd
      ((StringRestore.forms mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size).map (StringWrites.liftString mode)) (sourceRestored mode p state) := by
  have fields:=Listing8MacroWriteBounds.fields mode codeStart codeEnd p state ready placed
  have ranges:=tail_ranges mode p ready.sizeFits
  have firstPC : (copied mode p state).principal.pc=Arithmetic.encodeNat mode (sourceTail mode p) := by rw [copied_effect mode p state ready]
  have secondPC : (sourceRestored mode p state).principal.pc=Arithmetic.encodeNat mode (destinationTail mode p) := by rw [source_effect mode p state ready]
  exact ⟨StringRestoreWrites.owned mode false codeStart codeEnd _ _ p.size _ firstPC (fun _ => ranges.1) (fun _ => ranges.2.1) fields.1,
    StringRestoreWrites.owned mode true codeStart codeEnd _ _ p.size _ secondPC (fun _ => ranges.2.2.1)
      (fun _ => by rw [destination_endpoint];exact ranges.2.2.2) fields.2⟩

/-- Every instruction in the actual TRANSFERDATA template has a nonempty
write wholly in code: both readers/exchanges, every forward MOVS element,
and both restoring XCHG/SUB pairs. Future ownership is not a premise. -/
theorem owned (mode : Mode) (codeStart codeEnd : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode codeStart codeEnd p) :
    StringWrites.OwnedRun mode codeStart codeEnd ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state := by
  have a:=setup mode codeStart codeEnd p state ready placed
  have b:=moves mode codeStart codeEnd p state ready placed
  have c:=restores mode codeStart codeEnd p state ready placed
  simp only [StringProgram.forms,List.map_append,StringWrites.owned_run_append,StringWrites.run_append,StringWrites.run_lift_string]
  exact ⟨⟨⟨a,b⟩,c.1⟩,c.2⟩

end SmcTuring.Appendix.Listing8MacroWrites
