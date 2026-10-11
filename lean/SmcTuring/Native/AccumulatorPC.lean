module
public import SmcTuring.Native.AccumulatorReadClasses
public import SmcTuring.Native.StringPCWindows

public section
namespace SmcTuring.Native.AccumulatorPC
open AccumulatorLayout

theorem prologue_size (mode : Mode) (a : Layout) :
    StringPCSteps.size mode (StringStack.native mode (saveForm mode a))=storeSize mode := by
  cases mode <;> rfl

theorem prologue_windows (mode : Mode) (a : Layout) (valid : Admissible mode a) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode a.prologue) :
    StringPCWindows.Run mode ⟨a.prologue,savedPC mode a⟩ [StringStack.native mode (saveForm mode a)] state := by
  apply StringPCWindows.sequential mode _ _ state a.prologue ?_ entry ?_ (Nat.le_refl _) ?_ valid.prologueFits
  · intro form member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    subst form
    cases mode <;> trivial
  · apply StringPCWindows.guard_last mode []
    rw [prologue_size]
    cases mode
    · change 3≤5;decide
    · change 3≤7;decide
  · simp only [StringPCSteps.total,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,prologue_size]
    exact Nat.le_refl _

theorem epilogue_sequential (mode : Mode) (a : Layout) :
    ∀ form∈Appendix.Listing8AccumulatorExit.program mode a,StringPCSteps.Sequential mode form := by
  cases mode <;> simp [Appendix.Listing8AccumulatorExit.program,program,first,second,third,Reader.storeForm,
    StringStack.native,StringDwordCopy.native,StringPCSteps.Sequential,StringPCSteps.ControlSequential,
    StringPCSteps.DwordSequential,StringPCSteps.StringSequential,StringPCSteps.NativeSequential]

theorem epilogue_total (mode : Mode) (a : Layout) :
    a.epilogue+StringPCSteps.total mode (Appendix.Listing8AccumulatorExit.program mode a)=endPC mode a := by
  cases mode <;> rfl

theorem epilogue_guard (mode : Mode) (a : Layout) :
    StringPCWindows.Guard mode (Appendix.Listing8AccumulatorExit.program mode a) := by
  change StringPCWindows.Guard mode
    ([StringStack.native mode (first mode a),StringStack.native mode (second mode a)]++[StringStack.native mode (third mode a)])
  apply StringPCWindows.guard_last
  cases mode
  · change 3≤6;decide
  · change 3≤7;decide

theorem epilogue_windows (mode : Mode) (a : Layout) (valid : Admissible mode a) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode a.epilogue) :
    StringPCWindows.Run mode ⟨a.epilogue,endPC mode a⟩ (Appendix.Listing8AccumulatorExit.program mode a) state :=
  StringPCWindows.sequential mode _ _ state a.epilogue (epilogue_sequential mode a) entry (epilogue_guard mode a)
    (Nat.le_refl _) (Nat.le_of_eq (epilogue_total mode a)) valid.epilogueFits

end SmcTuring.Native.AccumulatorPC
