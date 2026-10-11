module
public import SmcTuring.SMC.ExecutionComposition
public import SmcTuring.SMC.VirtualInstructions

public section

namespace SmcTuring.SMC

/-- Actual current-image execution changes code at some instruction. A mere
write of the old value does not meet this predicate. -/
@[expose] def ChangesInSteps (wordBytes : Int) (image : Image) : Nat → State → Prop
  | 0, _ => False
  | count + 1, s =>
    ∃ instruction next, fetch image s = some (instruction, next) ∧
      (ChangesCode image.codeField wordBytes instruction next s ∨
       ChangesInSteps wordBytes image count (execute wordBytes instruction next s))

theorem image_boundary_change_has_instruction_change (wordBytes : Int) (image : Image)
    (count : Nat) (s finish : State) (field : Int)
    (completed : runImage wordBytes image count s = some finish)
    (code : image.codeField field) (different : finish.memory field ≠ s.memory field) :
    ChangesInSteps wordBytes image count s := by
  induction count generalizing s with
  | zero =>
    have equal : s = finish := by simpa only [runImage, Option.some.injEq] using completed
    subst s
    exact False.elim (different rfl)
  | succ count ih =>
    cases fetched : fetch image s with
    | none => simp [runImage, step, fetched] at completed
    | some entry =>
      rcases entry with ⟨instruction, next⟩
      have tail : runImage wordBytes image count (execute wordBytes instruction next s) = some finish := by
        simpa [runImage, step, fetched] using completed
      refine ⟨instruction, next, fetched, ?_⟩
      by_cases unchanged : (execute wordBytes instruction next s).memory field = s.memory field
      · exact Or.inr (ih _ tail (by simpa only [unchanged] using different))
      · exact Or.inl ⟨field, code, unchanged⟩

namespace Virtual

theorem represented_register_change (layout : Layout) (wordBytes : Int) (image : Image)
    (count : Nat) (source next : Dolan.Mov.State) (target finish : State) (r : Dolan.Mov.Register)
    (start : Rep layout source target) (ended : Rep layout next finish)
    (completed : runImage wordBytes image count target = some finish)
    (code : image.codeField (registerField layout r)) (changed : next.registers r ≠ source.registers r) :
    ChangesInSteps wordBytes image count target := by
  apply image_boundary_change_has_instruction_change wordBytes image count target finish (registerField layout r)
    completed code
  rw [ended.1 r, start.1 r]
  exact fun equal => changed (encode_word_injective layout.data equal)

end Virtual
end SmcTuring.SMC
