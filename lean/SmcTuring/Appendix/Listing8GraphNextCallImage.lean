module
public import SmcTuring.Appendix.Listing8GraphNextFailureFrames

public section
namespace SmcTuring.Appendix.Listing8GraphNextCallImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem first_nonfailure (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8GraphBackedge.failed mode origin l t g node rule memory seed=false := by
  apply Listing8GraphBackedge.nonfailure mode origin l t g node rule ctx memory seed
  intro halted
  have absent:=(Listing8GraphStep.halted_iff g node rule).mpr halted
  rw [selected] at absent
  cases absent

theorem after_backedge (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphBackedge.finish mode origin l t g node rule memory seed).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) 5=
        Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))) := by
  have packet:=Listing8FailureGlobalValues.call_packet mode l t (values mode origin g node rule) _ _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)
  have previous:=first_nonfailure mode origin l t g node rule target ctx selected memory seed
  change Listing8FailureGlobalValues.failed mode l t (values mode origin g node rule) _ _
    (extra mode origin l g memory) (Listing8GlobalBoot.bodySeed mode origin seed)=false at previous
  rw [previous] at packet
  rw [Listing8GraphBackedge.effect mode origin l t g node rule ctx memory seed]
  exact packet

theorem entry_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) 5=
        Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))) := by
  have coords:=Listing8FailureLayout.positions mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))
  rw [Listing8GraphNextFailureImage.window mode origin l t g node rule target ctx selected memory seed _ _
    (by cases mode <;> simp [Listing8FailureLayout.callPC,Listing8FailureLayout.stackSpan] at coords ⊢ <;> omega) (Nat.le_refl _)]
  exact after_backedge mode origin l t g node rule target ctx selected memory seed

theorem entry_operand (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8GraphNextState.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+1)=
        Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)) := by
  let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  let state:=Listing8GraphNextState.finish mode origin l t g node rule target memory seed
  have current:=entry_packet mode origin l t g node rule target ctx selected memory seed
  have packet:=ByteWindow.packet state.principal.memory (Listing8FailureLayout.callPC mode region) [0xe8]
    (LittleEndian.wordEncode 4 (Listing8FailureLayout.original mode region)) []
    (by simpa only [region,state,Native.encode,List.append_nil,List.length_append,List.length_cons,List.length_nil,LittleEndian.word_encode_length] using current)
  change ByteMemory.bytesAt state.principal.memory (Listing8FailureLayout.callPC mode region+1) 4=LittleEndian.wordEncode 4 _ at packet
  have decoded : ByteMemory.readWord .x86 state.principal.memory (Listing8FailureLayout.callPC mode region+1)=some (Listing8FailureLayout.original mode region) := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt _ _ 4)=some _
    rw [packet,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact Option.some.inj decoded

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) 5=
        Native.encode mode (.callRelative (if Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed then 0 else
          Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))) := by
  let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  rw [Listing8GraphNextFailure.memory_effect mode origin l t g node rule target ctx selected memory seed,
    entry_operand mode origin l t g node rule target ctx selected memory seed,Listing8CallSelection.toggle_selection]
  apply Listing8CallSelection.operand_current
  have maskBefore : Listing8FailureLayout.mask mode region+4≤Listing8FailureLayout.callPC mode region := by
    cases mode <;> simp [Listing8FailureLayout.mask,Listing8FailureLayout.callPC,Listing8FailureLayout.endPC,Listing8FailureLayout.stackSpan] <;> omega
  have andBefore : Listing8FailureLayout.andPC mode region+10≤Listing8FailureLayout.callPC mode region := by
    simp only [Listing8FailureLayout.mask,Listing8FailureLayout.xorPC] at maskBefore
    omega
  rw [DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl maskBefore),
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inl (by simpa only [Nat.add_assoc] using andBefore))]
  exact entry_packet mode origin l t g node rule target ctx selected memory seed

theorem call_fetch (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringControl.fetch mode (Listing8GraphNextFailure.finish mode origin l t g node rule target memory seed).principal.memory
      (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))=
        some (.previous (StringDwordCopy.native mode (.callRelative (if Listing8GraphNextFailure.failed mode origin l t g node rule target memory seed then 0 else
          Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))))) :=
  StringControl.previous_fetch mode _ _ _ (StringDwordCopy.native_encoding mode _ _ _
    (call_packet mode origin l t g node rule target ctx selected memory seed))

end SmcTuring.Appendix.Listing8GraphNextCallImage
