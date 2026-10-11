module
public import SmcTuring.Appendix.Listing8OwnerImage

public section
namespace SmcTuring.Appendix.Listing8LiveRetarget
open Native Listing8CopyImage Listing8Prototypes
@[expose] def patched (mode : Mode) (l : Layout) (state : StringExecution.State mode) :=
  StringRetarget.finish mode (Listing8ModeOffsets.sites mode (patchLayout mode l)) state
@[expose] def finish (mode : Mode) (l : Layout) (v : Values mode) (state : StringExecution.State mode) :=
  StringDword.execute mode (Listing8Initializer.tapeForm mode l v) (patched mode l state)
@[expose] def program (mode : Mode) (l : Layout) (v : Values mode) :=
  StringRetarget.program mode (Listing8ModeOffsets.sites mode (patchLayout mode l))++[Listing8Initializer.tapeForm mode l v]
@[expose] def Current (mode : Mode) (l : Layout) (v : Values mode) (memory : ByteMemory.Memory) :=
  ByteMemory.bytesAt memory (patchStart mode l)
    (Listing8ModeOffsets.bytes mode (patchLayout mode l) l.sourceNode l.sourceTransition
      v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState).length=
    Listing8ModeOffsets.bytes mode (patchLayout mode l) l.sourceNode l.sourceTransition
      v.tape v.rule v.fresh v.direction v.back v.forward v.next v.newState

theorem patch_trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Current mode l v state.principal.memory) :
    StringDword.Trace mode state (StringRetarget.program mode (Listing8ModeOffsets.sites mode (patchLayout mode l)))
      (patched mode l state) :=
  StringRetarget.trace mode _ (patchStart mode l) (Listing8ModeOffsets.chain mode (patchLayout mode l))
    (Listing8ModeOffsets.valid mode _ (block_capacity mode l r) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)))
    (Listing8ModeOffsets.outside mode (patchLayout mode l)) _ entry
    (Listing8ModeOffsets.initial_patches mode _ l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction
      v.back v.forward v.next v.newState _ current)
theorem patched_tape (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Current mode l v state.principal.memory) :
    ByteMemory.bytesAt (patched mode l state).principal.memory (nodeParams mode l).destination 10=
      DwordArithmetic.encode (DwordRetarget.ownerForm mode (nodeParams mode l).destination (Listing8LiteralInput.sourceField mode l.input) v.tape) :=
  (Listing8ModeOffsets.retargeted_owners mode _ l.sourceNode l.sourceTransition v.tape v.rule v.fresh v.direction
    v.back v.forward v.next v.newState (block_capacity mode l r) (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l))
    _ entry current).1
theorem patched_pc (mode : Mode) (l : Layout) (r : Resources mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l)) :
    (patched mode l state).principal.pc=Arithmetic.encodeNat mode (nodeParams mode l).destination :=
  congrArg Execution.State.pc (Listing8ModeOffsets.effect mode (patchLayout mode l) (block_capacity mode l r)
    (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) _ entry)
theorem last_trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Current mode l v state.principal.memory) :
    StringDword.Trace mode (patched mode l state) [Listing8Initializer.tapeForm mode l v] (finish mode l v state) := by
  have fits : (nodeParams mode l).destination<2^(8*mode.wordBytes) := by
    have cap:=block_capacity mode l r
    have d:=destinations mode l
    omega
  refine .step ?_ (.nil _)
  rw [patched_pc mode l r state entry,Arithmetic.encode_nat_toNat mode _ fits]
  exact StringDword.store_encoding mode _ _ _ _ (patched_tape mode l v r state entry current)
theorem trace (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l))
    (current : Current mode l v state.principal.memory) :
    StringDword.Trace mode state (program mode l v) (finish mode l v state) :=
  StringDword.trace_append mode (patch_trace mode l v r state entry current) (last_trace mode l v r state entry current)
theorem principal_effect (mode : Mode) (l : Layout) (v : Values mode) (state : StringExecution.State mode) :
    (finish mode l v state).principal=Listing8ModeOffsets.tapeState mode (patchLayout mode l) v.tape state.principal := by
  rw [finish,Listing8Initializer.tapeForm,StringDword.store_execute]
  rfl
theorem effect (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l)) :
    finish mode l v state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (backEntry mode (nodeParams mode l).destination)
      memory:=DwordCode.put (DwordRetargetSequence.writes mode (Listing8ModeOffsets.sites mode (patchLayout mode l)) state.principal.memory)
        (Listing8LiteralInput.sourceField mode l.input) v.tape}} := by
  have principal:=Listing8ModeOffsets.tape_owner_effect mode (patchLayout mode l) v.tape (block_capacity mode l r)
    (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) reach (Listing8OwnerImage.source_field_fits mode l r) _ entry
  rw [←principal_effect] at principal
  cases state with
  | mk principalState sourceIndex destinationIndex backwards =>
    simpa only [finish,Listing8Initializer.tapeForm,StringDword.store_execute,patched,StringRetarget.finish,nodeParams,patchLayout,Listing8ModeOffsets.nodeEntry] using
      congrArg (fun body : Execution.State mode =>
        StringExecution.State.mk body sourceIndex destinationIndex backwards) principal
theorem frame (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (reach : mode=.x64 → Relocation.SignedDelta ((nodeParams mode l).destination+10) (Listing8LiteralInput.sourceField mode l.input))
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (patchStart mode l)) (observed count : Nat)
    (patches : ∀ site∈Listing8ModeOffsets.sites mode (patchLayout mode l),site.owner+6≤observed ∨ observed+count≤site.owner+2)
    (tape : Listing8LiteralInput.sourceField mode l.input+4≤observed ∨ observed+count≤Listing8LiteralInput.sourceField mode l.input) :
    ByteMemory.bytesAt (finish mode l v state).principal.memory observed count=ByteMemory.bytesAt state.principal.memory observed count := by
  rw [effect mode l v r reach state entry,DwordMixedImage.bytes_frame _ _ _ _ _ tape,
    DwordRetargetSequence.writes_window mode _ _ observed count patches]
theorem instruction_count (mode : Mode) (l : Layout) (v : Values mode) : (program mode l v).length=5 := by
  simp only [program,List.length_append,StringRetarget.program,List.length_map,Listing8ModeOffsets.sites_length,List.length_cons,List.length_nil]

end SmcTuring.Appendix.Listing8LiveRetarget
