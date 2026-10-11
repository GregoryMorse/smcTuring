module
public import SmcTuring.Appendix.Listing9TailTemplateInitial

public section
namespace SmcTuring.Appendix.Listing9TailTemplateEpilogue
open Native Listing9PackedLayout

theorem packets (mode : Mode) (start transitions nodes : Nat) (memory : ByteMemory.Memory)
    (intact : Listing9TailTemplates.Property mode start transitions nodes memory) :
    Listing8AccumulatorExit.Current mode (layout mode start transitions nodes) memory := by
  constructor
  · exact intact.1 _ (List.Mem.tail _ (List.Mem.head _))
  · exact intact.1 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · exact intact.1 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- The actual epilogue reconstructs both later initializer packets from their
retained opcode bytes and positively restored full-width self-pointer words. -/
theorem storage_current (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (epilogue mode start transitions nodes))
    (intact : Listing9TailTemplates.Property mode start transitions nodes state.principal.memory)
    (pointer : Execution.load mode state.principal.memory (Arithmetic.encodeNat mode (layout mode start transitions nodes).pointer)=
      Arithmetic.encodeNat mode (layout mode start transitions nodes).save) :
    Listing9Storage.Current mode start transitions nodes (Listing8AccumulatorExit.finish mode (layout mode start transitions nodes) state).principal.memory := by
  have valid:=admissible mode start transitions nodes bounds
  have coords:=positions mode start transitions nodes
  have ordered:=bounds_order mode start transitions nodes
  have trace:=Listing8AccumulatorExit.trace mode _ valid (by rw [coords.2.2.1];omega) state entry (packets mode start transitions nodes _ intact)
  have states:=Listing9TailTemplates.all_states mode start transitions nodes _ state intact
    (Listing9TailTemplateRegions.epilogue mode start transitions nodes bounds state entry)
  have finalProperty:=StringTemplateStates.at_prefix mode (fun reached => Listing9TailTemplates.Property mode start transitions nodes reached.principal.memory)
    (Listing8AccumulatorExit.program mode (layout mode start transitions nodes)) [] state (by simpa only [List.append_nil] using states)
  rw [StringWrites.trace_run_eq mode trace] at finalProperty
  have effect : (Listing8AccumulatorExit.finish mode (layout mode start transitions nodes) state).principal.memory=
      ByteMemory.putWord mode state.principal.memory (layout mode start transitions nodes).save
        (Arithmetic.encodeNat mode (layout mode start transitions nodes).save) := by
    change (AccumulatorEffects.finish mode _ state.principal).memory=_
    rw [AccumulatorEffects.effect mode _ valid state.principal entry,pointer]
  have saveWord : Protected.wordAt mode (Listing8AccumulatorExit.finish mode (layout mode start transitions nodes) state).principal.memory
      (layout mode start transitions nodes).save=Arithmetic.encodeNat mode (layout mode start transitions nodes).save := by
    change MixedMemory.getWord mode _ _=_
    rw [effect,MixedMemory.get_put]
  have pointerFits : (layout mode start transitions nodes).pointer<2^(8*mode.wordBytes) := by
    have positive : 0<mode.wordBytes := by cases mode <;> decide
    have fits:=valid.pointerFits
    omega
  have pointerWord : Protected.wordAt mode (Listing8AccumulatorExit.finish mode (layout mode start transitions nodes) state).principal.memory
      (layout mode start transitions nodes).pointer=Arithmetic.encodeNat mode (layout mode start transitions nodes).save := by
    change MixedMemory.getWord mode _ _=_
    rw [effect,MixedFrames.word_after_word mode _ _ _ _ valid.separate]
    rw [←MixedMemory.load_nat mode _ _ pointerFits]
    exact pointer
  have saveNat : (Arithmetic.encodeNat mode (layout mode start transitions nodes).save).toNat=(layout mode start transitions nodes).save :=
    AccumulatorLayout.save_toNat mode _ valid
  constructor
  · have current:=StringInitTemplates.current mode (saveOwner mode start transitions nodes) _ finalProperty.2.1
    change ByteMemory.bytesAt _ _ _=StringInit.bytes mode _ (Protected.wordAt mode _ (layout mode start transitions nodes).save).toNat at current
    rw [saveWord,saveNat] at current
    exact current
  · have current:=StringInitTemplates.current mode (pointerOwner mode start transitions nodes) _ finalProperty.2.2
    change ByteMemory.bytesAt _ _ _=StringInit.bytes mode _ (Protected.wordAt mode _ (layout mode start transitions nodes).pointer).toNat at current
    rw [pointerWord,saveNat] at current
    exact current

end SmcTuring.Appendix.Listing9TailTemplateEpilogue
