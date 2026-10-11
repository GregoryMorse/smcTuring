module
public import SmcTuring.Appendix.Listing8GraphBackedgeInput
public import SmcTuring.Appendix.Listing8GraphNextInputBounds

public section
namespace SmcTuring.Appendix.Listing8GraphNextInputImage
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8GraphInputContext Listing8GraphMacroImages Listing8GraphNextRetarget
abbrev Targets:=Listing8PointerCopies.Targets

theorem after_copies (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let v:=values mode origin g node rule
    Listing8InputMask.Intact mode l.input (-(v.rule-v.tape)) v.tape (Listing8GraphBackedgeInput.pending mode origin g node rule)
      v.fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
      (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed).principal.memory := by
  rw [Listing8InputMask.Intact,Listing8GraphNextCopyFrames.window mode origin l t g node rule target ctx selected memory seed
    l.input.start _ ctx.resources.inputAfter]
  exact Listing8GraphBackedgeInput.current mode origin l t g node rule ctx memory seed

theorem after_retargets (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let old:=values mode origin g node rule
    let v:=liveValues mode origin g node rule target
    Listing8InputMask.Intact mode l.input (-(old.rule-old.tape)) v.tape (Listing8GraphBackedgeInput.pending mode origin g node rule)
      old.fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
      (Listing8GraphNextRetarget.finish mode origin l t g node rule target memory seed).principal.memory := by
  have current:=after_copies mode origin l t g node rule target ctx selected memory seed
  have kept : Listing8InputMask.Intact mode l.input
      (-((values mode origin g node rule).rule-(values mode origin g node rule).tape)) (values mode origin g node rule).tape
      (Listing8GraphBackedgeInput.pending mode origin g node rule) (values mode origin g node rule).fresh
      (Listing8GraphBackedgeInput.mask mode origin g node rule)
      (DwordRetargetSequence.writes mode (Listing8ModeOffsets.sites mode (patchLayout mode (nextLayout mode origin l g node rule target)))
        (Listing8GraphNextCopies.finish mode origin l t g node rule target memory seed).principal.memory) := by
    rw [Listing8InputMask.Intact,DwordRetargetSequence.writes_window]
    · exact current
    · intro site member
      left
      have bounds:=(Listing8ModeOffsets.owners_after_patches mode (patchLayout mode (nextLayout mode origin l g node rule target)) site member).2.1
      change site.owner+10≤codeEnd mode l at bounds
      have after:=ctx.resources.inputAfter
      omega
  rw [Listing8GraphNextRetarget.effect mode origin l t g node rule target ctx selected memory seed]
  exact Listing8InputFields.tape_patch mode l.input _ _ (liveValues mode origin g node rule target).tape _ _ _ _ kept

theorem after_owners (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let v:=liveValues mode origin g node rule target
    Listing8InputMask.Intact mode l.input v.rule v.tape (Listing8GraphBackedgeInput.pending mode origin g node rule)
      v.fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
      (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed).principal.memory := by
  have old:=after_retargets mode origin l t g node rule target ctx selected memory seed
  have rulePatch:=Listing8OwnerInput.rule_patch mode l.input _ (liveValues mode origin g node rule target).rule _ _ _ _ _ old
  have freshPatch:=Listing8OwnerInput.fresh_patch mode l.input _ _ _ _ (liveValues mode origin g node rule target).fresh _ _ rulePatch
  rw [Listing8InputMask.Intact,(Listing8GraphNextOwners.result mode origin l t g node rule target ctx selected memory seed).2.1,
    DwordMixedImage.bytes_frame _ _ _ _ _ (Or.inr (by
      have size:=Listing8InputMask.bytes_length mode l.input (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
        (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
      have after:=ctx.fields.directionAfter;omega))]
  exact freshPatch

/-- The current second input image is obtained from the previous executed
image and the actual next owner/pointer writes, without reinitialization. -/
theorem current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule target : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (selected : Listing8GraphStep.nextRule g node rule=some target) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    let v:=liveValues mode origin g node rule target
    Listing8InputMask.Intact mode (nextLayout mode origin l g node rule target).input v.rule v.tape (Listing8GraphBackedgeInput.pending mode origin g node rule)
      v.fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
      (Listing8GraphNextPointers.finish mode origin l t g node rule target memory seed).principal.memory := by
  have current:=after_owners mode origin l t g node rule target ctx selected memory seed
  have bytesSame : Listing8InputMask.bytes mode (nextLayout mode origin l g node rule target).input
      (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape (Listing8GraphBackedgeInput.pending mode origin g node rule)
      (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)=
      Listing8InputMask.bytes mode l.input (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
        (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule) :=
    Listing8InputReuseFields.head_bytes mode l.input _ _ _ _ _ _
  rw [Listing8InputMask.Intact,bytesSame]
  change ByteMemory.bytesAt (Listing8PointerCopies.finish mode l t (Listing8GraphNextOwners.finish mode origin l t g node rule target memory seed)).principal.memory l.input.start _= _
  rw [Listing8PointerCopies.window_frame mode l t ctx.copies _
    (Listing8GraphNextOwners.registers mode origin l t g node rule target ctx selected memory seed).1]
  · exact current
  · left
    have prior:=Listing8PointerCopies.cursor_before mode l
    have after:=ctx.resources.inputAfter;omega
  · intro lay member
    have after:=ctx.body.state.head.input.targetsAfter
    have a:=after t.state (by simp)
    have b:=after t.back (by simp)
    have c:=after t.forward (by simp)
    have size:=Listing8InputMask.bytes_length mode l.input (liveValues mode origin g node rule target).rule (liveValues mode origin g node rule target).tape
      (Listing8GraphBackedgeInput.pending mode origin g node rule) (liveValues mode origin g node rule target).fresh (Listing8GraphBackedgeInput.mask mode origin g node rule)
    right
    cases mode
    all_goals simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.split,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
    all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only
    all_goals omega

end SmcTuring.Appendix.Listing8GraphNextInputImage
