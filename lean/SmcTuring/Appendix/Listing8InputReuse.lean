module
public import SmcTuring.Appendix.Listing8InputReuseFields
public import SmcTuring.Appendix.Listing8InputMaskEffects

public section
namespace SmcTuring.Appendix.Listing8InputReuse
open Native Listing8LiteralInput Listing8InputReuseFields
abbrev Dword:=BitVec 32

/-- The complete input image after the actual input execution is derived,
including the comparison scratch, pending delta and previous live mask. -/
theorem completed_image (mode : Mode) (l : Layout) (rule tape pending fresh oldMask : Dword)
    (capacity : endPC mode l<2^(8*mode.wordBytes)) (masks : Listing8LiteralMaskTrace.Valid mode l)
    (update : InputUpdate.Valid mode (updateLayout mode l)) (outside : Listing8LiteralComposition.DataOutside mode l)
    (state : Execution.State mode) (entry : state.pc=Arithmetic.encodeNat mode l.start)
    (current : Listing8InputMask.Intact mode l rule tape pending fresh oldMask state.memory)
    (cursor : MixedMemory.getWord mode state.memory l.cursor=Arithmetic.encodeNat mode l.head)
    (symbol : DwordCode.get state.memory (l.head+6)=tape) :
    Listing8InputMask.Intact mode l (-(rule-tape)) tape (CursorEffects.delta tape fresh (chosen rule tape)) fresh
      (InputUpdate.mask (chosen rule tape)) (Listing8LiteralComposition.finish mode l rule tape fresh state).memory := by
  let normalized:=Listing8InputMask.normalized mode l state
  have zero:=Listing8InputMask.zero_intact mode l rule tape pending fresh oldMask state.memory current
  have cursorNorm:=(Listing8InputMaskEffects.cursor mode l outside state).trans cursor
  have symbolNorm:=(Listing8InputMaskEffects.symbol mode l outside state).trans symbol
  have normCurrent:=mask_patch mode l rule tape pending fresh oldMask 0 state.memory current
  have reset:=mask_patch mode l rule tape pending fresh 0 0 normalized.memory normCurrent
  have copied:=pending_patch mode l rule tape pending tape fresh 0 _ reset
  have compared:=Listing8OwnerInput.rule_patch mode l rule (-(rule-tape)) tape tape fresh 0 _ copied
  have masked:=mask_patch mode l (-(rule-tape)) tape tape fresh 0 (InputUpdate.mask (chosen rule tape)) _ compared
  have prefixCurrent : Listing8InputMask.Intact mode l (-(rule-tape)) tape tape fresh (InputUpdate.mask (chosen rule tape))
      (prefixState mode l rule tape normalized).memory := by
    rw [prefix_effect mode l rule tape pending fresh capacity normalized entry zero]
    exact masked
  have distributedCurrent : Listing8InputMask.Intact mode l (-(rule-tape)) tape tape fresh (InputUpdate.mask (chosen rule tape))
      (Listing8LiteralComposition.distributedState mode l rule tape normalized).memory := by
    rw [Listing8InputMask.Intact,Listing8LiteralComposition.distribution_memory mode l rule tape pending fresh capacity masks normalized entry zero,
      DwordMixedSequence.putFields_window]
    · exact prefixCurrent
    · intro helper member
      have bound:=Listing8InputMask.bytes_length mode l (-(rule-tape)) tape tape fresh (InputUpdate.mask (chosen rule tape))
      rcases masks.outsideInput helper member with early | late
      · left;omega
      · right;omega
  have updated:=pending_patch mode l (-(rule-tape)) tape tape (CursorEffects.delta tape fresh (chosen rule tape)) fresh
    (InputUpdate.mask (chosen rule tape)) _ distributedCurrent
  rw [Listing8InputMask.Intact,Listing8InputMask.finish_same mode l rule tape fresh capacity state entry,
    Listing8SourceEffects.effect mode l rule tape pending fresh capacity masks update outside normalized entry zero cursorNorm symbolNorm,
    DwordMixedImage.bytes_frame _ _ _ _ _]
  · exact updated
  · have bound:=Listing8InputMask.bytes_length mode l (-(rule-tape)) tape (CursorEffects.delta tape fresh (chosen rule tape)) fresh (InputUpdate.mask (chosen rule tape))
    rcases outside.tape with early | late
    · left;omega
    · right;omega

end SmcTuring.Appendix.Listing8InputReuse
