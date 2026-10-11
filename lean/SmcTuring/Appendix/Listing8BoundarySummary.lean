module
public import SmcTuring.Appendix.Listing8OriginalResetBinding
public import SmcTuring.Appendix.Listing8NativeHeadBoundary

public section
namespace SmcTuring.Appendix.Listing8BoundarySummary
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
open Listing8JointAccumulatorCatalog
abbrev Targets:=Listing8PointerCopies.Targets
abbrev old:=Listing8OriginalControlImage.old
set_option maxHeartbeats 2000000
attribute [local irreducible] StringTemplateStates.Run
local instance (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) : Decidable (Listing8GraphRun.Halted g node rule) := by
  unfold Listing8GraphRun.Halted;infer_instance

/-- Exhaustive structural prefix decomposition; no assumed native future. -/
theorem cut_append {α : Type} (first second before after : List α)
    (cut : first++second=before++after) :
    (∃ rest,first=before++rest) ∨ ∃ pre rest,second=pre++rest ∧ before=first++pre := by
  induction first generalizing before with
  | nil => exact Or.inr ⟨before,after,cut,by simp⟩
  | cons item rest ih =>
    cases before with
    | nil => exact Or.inl ⟨item::rest,rfl⟩
    | cons next leading =>
      have equal := List.cons.inj cut
      have heads := equal.1
      subst next
      rcases ih leading equal.2 with ⟨later,short⟩ | ⟨pre,later,short,location⟩
      · exact Or.inl ⟨later,by simp only [List.cons_append];rw [short]⟩
      · exact Or.inr ⟨pre,later,short,by simp only [List.cons_append];rw [location]⟩

@[expose] def Covered {α : Type} (save boot main tail before : List α) :=
  (∃ rest,save=before++rest) ∨
  (∃ pre rest,boot=pre++rest ∧ before=save++pre) ∨
  (∃ pre rest,main=pre++rest ∧ before=(save++boot)++pre) ∨
  (∃ pre rest,tail=pre++rest ∧ before=((save++boot)++main)++pre)

theorem coverage {α : Type} (save boot main tail before after : List α)
    (cut : ((save++boot)++main)++tail=before++after) : Covered save boot main tail before := by
  rw [List.append_assoc,List.append_assoc] at cut
  rcases cut_append save (boot++(main++tail)) before after cut with first | ⟨pre,rest,later,location⟩
  · exact Or.inl first
  · rcases cut_append boot (main++tail) pre rest later with second | ⟨part,last,later,within⟩
    · obtain ⟨last,split⟩ := second
      exact Or.inr (Or.inl ⟨pre,last,split,location⟩)
    · rw [within] at location
      rcases cut_append main tail part last later with third | ⟨final,remaining,split,within⟩
      · obtain ⟨remaining,split⟩ := third
        exact Or.inr (Or.inr (Or.inl ⟨part,remaining,split,by simpa only [List.append_assoc] using location⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨final,remaining,split,by rw [within] at location;simpa only [List.append_assoc] using location⟩))

@[expose] def savedMemory (mode : Mode) (a : AccumulatorLayout.Layout) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  ByteMemory.putWord mode memory a.save seed.principal.accumulator
@[expose] def entry (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8AccumulatorEntry.initial mode origin l t g node rule a memory seed
@[expose] def mainState (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8GraphCopyWrites.afterBoot mode origin l t g node rule (savedMemory mode a memory seed) seed
@[expose] def saveForms (mode : Mode) (a : AccumulatorLayout.Layout) := [StringStack.native mode (AccumulatorLayout.saveForm mode a)]
@[expose] def mainForms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8LoopControl.program mode origin l t g node rule (mainState mode origin l t g node rule a memory seed)
/-- The same finite logical halt predicate selects the established native
terminal continuation;nonhalting entry exits at the actual reentry boundary. -/
@[expose] def continuation (mode : Mode) (origin : Nat) (l : Layout) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout) : List (StringStack.Form mode) := by
  exact if Listing8GraphRun.Halted g node rule then tailForms mode origin l g node rule a else []
@[expose] def forms (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  ((saveForms mode a++Listing4EntryLayout.forms mode origin)++mainForms mode origin l t g node rule a memory seed)++continuation mode origin l g node rule a
@[expose] def BootstrapProperty (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8GlobalControlTemplates.Decodes mode origin memory ∧
  Listing8JointLocalCatalog.Decodes mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) memory ∧
  StringEncodedTemplates.Decodes mode (nodeParams mode l) memory ∧
  StringEncodedTemplates.Decodes mode (transitionParams mode l) memory ∧
  (∀ template∈Listing8CopyOwnerLifetimeRun.patches mode l,DwordTemplateCollection.Decodes mode template memory) ∧
  Listing8OwnerTemplateCollection.All mode (Listing8OriginalGraphCatalog.catalog mode origin g) memory

/-- Every actual main exit retains the strong endpoint catalogs,whether
its logical branch halts or returns. The common active owner packet is empty. -/
theorem returned (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (oldInput : Listing8MainInput.OldInput) (state : StringExecution.State mode)
    (image : Listing8LoopControlImage.Current mode origin l t g node rule oldInput state) :
    TerminalProperty mode origin l g node rule (Listing8LoopControl.finish mode origin l t g node rule state).principal.memory := by
  have seed := Listing8JointDeclarationCatalog.endpoint_seed mode origin l t g node rule ctx oldInput state image
  have shared := Listing8JointLocalMain.at_prefix mode origin l t g node rule ctx oldInput state image
    (Listing8LoopControl.program mode origin l t g node rule state) [] (by rw [List.append_nil])
  have actual := StringWrites.trace_run_eq mode (Listing8LoopControl.trace mode origin l t g node rule ctx oldInput state image)
  rw [actual] at shared
  refine ⟨shared.1.1.1,seed.1,Listing8JointLocalCatalog.decodes mode l _ _ _ seed.1.1,
    (fun template member => DwordTemplateCollection.decodes mode template _ (seed.1.2.1 template member)),
    StringEncodedTemplates.macro_decodes mode (nodeParams mode l) _
      (by change Listing8Prototypes.nodeSpan mode<2^31;cases mode <;> decide) seed.1.2.2.1,
    StringEncodedTemplates.macro_decodes mode (transitionParams mode l) _
      (by change Listing8Prototypes.transitionSpan mode<2^31;cases mode <;> decide) seed.1.2.2.2,?_⟩
  obtain ⟨packet,allowed,headers⟩ := Listing8JointResetObserverRun.empty mode origin l _ g _ seed.2
  exact ⟨packet,Or.inr allowed,headers⟩

/-- ONE covered prefix predicate extends the accepted round2 main predicate
through its actual original/accumulator/bootstrap/terminal boundaries. Each
phase retains its exact inventory,word exceptions and stronger restorations. -/
structure PrefixInvariant (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (before : List (StringStack.Form mode)) (reached : StringExecution.State mode) : Prop where
  phaseCoverage : Covered (saveForms mode a) (Listing4EntryLayout.forms mode origin)
    (mainForms mode origin l t g node rule a memory seed) (continuation mode origin l g node rule a) before
  prologue : ∀ rest,saveForms mode a=before++rest → BeforeProperty mode origin l g reached.principal.memory
  bootstrap : ∀ pre rest,Listing4EntryLayout.forms mode origin=pre++rest → before=saveForms mode a++pre →
    BootstrapProperty mode origin l g reached.principal.memory
  main : ∀ pre rest,mainForms mode origin l t g node rule a memory seed=pre++rest →
    before=(saveForms mode a++Listing4EntryLayout.forms mode origin)++pre →
    Listing8JointCopyOwnerLifetimes.PrefixInvariant mode origin l t g node rule
      (mainState mode origin l t g node rule a memory seed) pre reached
  terminal : ∀ pre rest,continuation mode origin l g node rule a=pre++rest →
    before=((saveForms mode a++Listing4EntryLayout.forms mode origin)++mainForms mode origin l t g node rule a memory seed)++pre →
    TerminalProperty mode origin l g node rule reached.principal.memory

/-- Complete round3 original boundary coverage at EVERY native prefix.
Both entry seeds and every appended endpoint are derived;the only packet
observation is at the original prologue entry. No future image is assumed. -/
theorem complete (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : AccumulatorLayout.savedPC mode a=origin) (epilogue : a.epilogue=graphEnd mode origin g)
    (saveAfter : graphEnd mode origin g≤a.save) (pointerAfter : graphEnd mode origin g≤a.pointer)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (present : ByteMemory.bytesAt (entry mode origin l t g node rule a memory seed).principal.memory a.prologue
      (Native.encode mode (AccumulatorLayout.saveForm mode a)).length=Native.encode mode (AccumulatorLayout.saveForm mode a))
    (before after : List (StringStack.Form mode))
    (cut : forms mode origin l t g node rule a memory seed=before++after) :
    PrefixInvariant mode origin l t g node rule a memory seed before
      (StringWrites.run mode before (entry mode origin l t g node rule a memory seed)) := by
  have image := Listing8OriginalResetBinding.current mode origin l t g node rule ctx (savedMemory mode a memory seed) seed
  have savedRun : StringWrites.run mode (saveForms mode a) (entry mode origin l t g node rule a memory seed)=
      Listing8GraphBackedge.initial mode origin l t g node rule (savedMemory mode a memory seed) seed := by
    rw [saveForms,entry,StringWrites.trace_run_eq mode (Listing8AccumulatorEntry.trace mode origin l t g node rule a valid memory seed present),
      Listing8AccumulatorEntry.saved_eq mode origin l t g node rule ctx a valid located saveAfter memory seed]
    rfl
  have bootRun : StringWrites.run mode (saveForms mode a++Listing4EntryLayout.forms mode origin)
      (entry mode origin l t g node rule a memory seed)=mainState mode origin l t g node rule a memory seed := by
    rw [StringWrites.run_append,savedRun,Listing8GraphEntryWrites.boot_run mode origin l t g node rule ctx _ seed]
    rfl
  have mainRun : StringWrites.run mode (mainForms mode origin l t g node rule a memory seed)
      (mainState mode origin l t g node rule a memory seed)=
      Listing8LoopControl.finish mode origin l t g node rule (mainState mode origin l t g node rule a memory seed) :=
    StringWrites.trace_run_eq mode (Listing8LoopControl.trace mode origin l t g node rule ctx old _ image.control)
  have throughMain : StringWrites.run mode ((saveForms mode a++Listing4EntryLayout.forms mode origin)++mainForms mode origin l t g node rule a memory seed)
      (entry mode origin l t g node rule a memory seed)=
      Listing8LoopControl.finish mode origin l t g node rule (mainState mode origin l t g node rule a memory seed) := by
    rw [StringWrites.run_append,bootRun,mainRun]
  have tail : StringTemplateStates.Run mode (fun reached => TerminalProperty mode origin l g node rule reached.principal.memory)
      (continuation mode origin l g node rule a)
      (Listing8LoopControl.finish mode origin l t g node rule (mainState mode origin l t g node rule a memory seed)) := by
    classical
    by_cases halted : Listing8GraphRun.Halted g node rule
    · simpa only [continuation,ite_eq_left halted,mainState] using
        Listing8JointAccumulatorCatalog.terminal_tail mode origin l t g node rule ctx old _ image halted a valid epilogue saveAfter pointerAfter
    · simp only [continuation,ite_eq_right halted]
      rw [StringTemplateStates.Run]
      simpa only [mainState] using returned mode origin l t g node rule ctx old _ image.control
  refine ⟨coverage _ _ _ _ before after cut,?_,?_,?_,?_⟩
  · intro rest split
    exact StringTemplateStates.at_prefix mode _ before rest _
      (by rw [←split];exact Listing8JointAccumulatorCatalog.prologue mode origin l t g node rule ctx a valid saveAfter memory seed)
  · intro pre rest split location
    rw [location,StringWrites.run_append,savedRun]
    exact StringTemplateStates.at_prefix mode _ pre rest _
      (by rw [←split];exact Listing8OriginalControlImage.bootstrap mode origin l t g node rule ctx (savedMemory mode a memory seed) seed)
  · intro pre rest split location
    rw [location,StringWrites.run_append,bootRun]
    exact Listing8JointCopyOwnerLifetimes.complete mode origin l t g node rule ctx old _ image.control pre rest split
  · intro pre rest split location
    rw [location,StringWrites.run_append,throughMain]
    exact StringTemplateStates.at_prefix mode _ pre rest _
      (by rw [←split];exact tail)

/-- Existing native pre-cleanup head decoding and terminal output are retained
at the SAME positively initialized main state used by the prefix summary. -/
theorem observations (mode : Mode) (origin : Nat) (lower : Int) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (halted : Listing8GraphRun.Halted g node rule)
    (a : AccumulatorLayout.Layout) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8NativeHeadBoundary.observe mode origin lower g.transitions l.input.cursor
      (Listing8LoopControl.failureEnd mode origin l t g node rule (mainState mode origin l t g node rule a memory seed)).principal.memory=
        lower+((Listing8GraphStep.nextNode g node rule).val : Int) ∧
    List.ofFn (fun index : Fin g.nodes => DwordCode.get
      (Listing8LoopTerminal.finish mode origin l t g node rule (mainState mode origin l t g node rule a memory seed)).principal.memory
      (nodePC mode origin g index+6))=
        List.ofFn (fun index : Fin g.nodes => ((Listing8GraphStep.updated g node rule).tape index).symbol) := by
  have image := Listing8OriginalResetBinding.current mode origin l t g node rule ctx (savedMemory mode a memory seed) seed
  exact ⟨Listing8NativeHeadBoundary.after_failure mode origin lower l t g node rule ctx old _ image.control,
    Listing8LoopTerminal.all_symbols mode origin l t g node rule ctx old _ image halted⟩


/-- The formal native endpoint follows the same finite logical branch. -/
@[expose] def finish (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  if Listing8GraphRun.Halted g node rule then
    Listing8AccumulatorExit.finish mode a (Listing8LoopTerminal.finish mode origin l t g node rule (mainState mode origin l t g node rule a memory seed))
  else Listing8LoopControl.finish mode origin l t g node rule (mainState mode origin l t g node rule a memory seed)

theorem terminal_shape (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout) (state : StringExecution.State mode) :
    Listing8LoopControl.program mode origin l t g node rule state++tailForms mode origin l g node rule a=
      Listing8LoopTerminal.program mode origin l t g node rule state++Listing8AccumulatorExit.program mode a := by
  simp only [Listing8LoopTerminal.program,Listing8LoopReset.program,Listing8LoopTable.program,tailForms,
    Listing8GlobalLoopMainRegions.lift_dword,List.append_assoc]

/-- Future epilogue packet observations are derived from initial bytes and
whole-memory/terminal frames,not supplied as a future-state hypothesis. -/
theorem epilogue_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (halted : Listing8GraphRun.Halted g node rule)
    (a : AccumulatorLayout.Layout) (located : a.epilogue=graphEnd mode origin g)
    (saveAfter : AccumulatorLayout.endPC mode a≤a.save)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (present : Listing8AccumulatorExit.Current mode a memory) :
    Listing8AccumulatorExit.Current mode a
      (Listing8LoopTerminal.finish mode origin l t g node rule (mainState mode origin l t g node rule a memory seed)).principal.memory := by
  have image := Listing8OriginalResetBinding.current mode origin l t g node rule ctx (savedMemory mode a memory seed) seed
  have frames : ∀ observed count,graphEnd mode origin g≤observed →
      ByteMemory.bytesAt (Listing8LoopTerminal.finish mode origin l t g node rule (mainState mode origin l t g node rule a memory seed)).principal.memory observed count=
        ByteMemory.bytesAt (savedMemory mode a memory seed) observed count := by
    intro observed count after
    rw [mainState,Listing8LoopTailFrames.terminal mode origin l t g node rule ctx old _ image halted observed count after,
      Listing8OriginalControlImage.memory mode origin l t g node rule ctx _ seed,
      Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx _ seed]
    exact Listing8LoopOriginalTailFrames.initial_window mode origin l t g node rule ctx _ seed observed count after
  constructor
  · rw [frames a.epilogue (Native.encode mode (AccumulatorLayout.first mode a)).length (by rw [located]),
      savedMemory,StackWindows.word_window _ _ _ _ _ _ (Or.inr (by
        rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.1]
        unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC AccumulatorLayout.secondPC at saveAfter
        omega))]
    exact present.first
  · rw [frames (AccumulatorLayout.secondPC mode a) (Native.encode mode (AccumulatorLayout.second mode a)).length (by
      rw [←located];unfold AccumulatorLayout.secondPC;omega),
      savedMemory,StackWindows.word_window _ _ _ _ _ _ (Or.inr (by
        rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.1]
        unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC at saveAfter;omega))]
    exact present.second
  · rw [frames (AccumulatorLayout.thirdPC mode a) (Native.encode mode (AccumulatorLayout.third mode a)).length (by
      rw [←located];unfold AccumulatorLayout.thirdPC AccumulatorLayout.secondPC;omega),
      savedMemory,StackWindows.word_window _ _ _ _ _ _ (Or.inr (by
        rw [Native.instruction_length,(AccumulatorLayout.lengths mode a).2.2.2]
        exact saveAfter))]
    exact present.third

/-- One complete fetched native trace covers the same prologue/bootstrap/main
and selected terminal/epilogue forms. Only initial packet observations and
static placement/resources are inputs. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : AccumulatorLayout.savedPC mode a=origin) (epilogue : a.epilogue=graphEnd mode origin g)
    (saveAfter : AccumulatorLayout.endPC mode a≤a.save) (pointerAfter : AccumulatorLayout.endPC mode a≤a.pointer)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (prologue : ByteMemory.bytesAt (entry mode origin l t g node rule a memory seed).principal.memory a.prologue
      (Native.encode mode (AccumulatorLayout.saveForm mode a)).length=Native.encode mode (AccumulatorLayout.saveForm mode a))
    (initialExit : Listing8AccumulatorExit.Current mode a memory) :
    StringStack.Trace mode (entry mode origin l t g node rule a memory seed)
      (forms mode origin l t g node rule a memory seed) (finish mode origin l t g node rule a memory seed) := by
  have epiBefore : a.epilogue≤AccumulatorLayout.endPC mode a := by
    unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC AccumulatorLayout.secondPC;omega
  have graphSave : graphEnd mode origin g≤a.save := by rw [←epilogue];omega
  have image := Listing8OriginalResetBinding.current mode origin l t g node rule ctx (savedMemory mode a memory seed) seed
  have start := Listing8AccumulatorEntry.trace mode origin l t g node rule a valid memory seed prologue
  rw [Listing8AccumulatorEntry.saved_eq mode origin l t g node rule ctx a valid located graphSave memory seed] at start
  have boot : StringStack.Trace mode (Listing8GraphBackedge.initial mode origin l t g node rule (savedMemory mode a memory seed) seed)
      (Listing4EntryLayout.forms mode origin) (mainState mode origin l t g node rule a memory seed) :=
    Listing4Entry.trace mode origin (Listing8GraphCopyWrites.bootSeed mode origin l t g node rule (savedMemory mode a memory seed) seed)
      (Listing8GlobalBoot.entry_capacity mode origin l t _ ctx.boot ctx.body)
  have entered := StringStack.trace_append mode start boot
  by_cases halted : Listing8GraphRun.Halted g node rule
  · have body := Listing8LoopTerminal.trace mode origin l t g node rule ctx old _ image halted
    have last := Listing8AccumulatorExit.trace mode a valid pointerAfter _
      (by rw [epilogue];exact (Listing8LoopTerminal.result mode origin l t g node rule ctx old _ image halted).1)
      (epilogue_current mode origin l t g node rule ctx halted a epilogue saveAfter memory seed initialExit)
    rw [forms,List.append_assoc,mainForms,continuation,ite_eq_left halted,terminal_shape,finish,ite_eq_left halted]
    exact StringStack.trace_append mode entered (StringStack.trace_append mode body last)
  · rw [forms,continuation,ite_eq_right halted,List.append_nil,finish,ite_eq_right halted]
    exact StringStack.trace_append mode entered (Listing8LoopControl.trace mode origin l t g node rule ctx old _ image.control)

/-- Round3's single covered boundary-prefix summary:one actual fetched trace
and the accepted round2 invariant at EVERY prefix of that very same trace.
Both native branches and all partial-copy lifetimes are covered. -/
theorem complete_trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : AccumulatorLayout.savedPC mode a=origin) (epilogue : a.epilogue=graphEnd mode origin g)
    (saveAfter : AccumulatorLayout.endPC mode a≤a.save) (pointerAfter : AccumulatorLayout.endPC mode a≤a.pointer)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (prologue : ByteMemory.bytesAt (entry mode origin l t g node rule a memory seed).principal.memory a.prologue
      (Native.encode mode (AccumulatorLayout.saveForm mode a)).length=Native.encode mode (AccumulatorLayout.saveForm mode a))
    (initialExit : Listing8AccumulatorExit.Current mode a memory) :
    StringStack.Trace mode (entry mode origin l t g node rule a memory seed)
      (forms mode origin l t g node rule a memory seed) (finish mode origin l t g node rule a memory seed) ∧
    ∀ before after,forms mode origin l t g node rule a memory seed=before++after →
      PrefixInvariant mode origin l t g node rule a memory seed before
        (StringWrites.run mode before (entry mode origin l t g node rule a memory seed)) := by
  have epiBefore : a.epilogue≤AccumulatorLayout.endPC mode a := by
    unfold AccumulatorLayout.endPC AccumulatorLayout.thirdPC AccumulatorLayout.secondPC;omega
  have graphSave : graphEnd mode origin g≤a.save := by rw [←epilogue];omega
  have graphPointer : graphEnd mode origin g≤a.pointer := by rw [←epilogue];omega
  exact ⟨trace mode origin l t g node rule ctx a valid located epilogue saveAfter pointerAfter memory seed prologue initialExit,
    complete mode origin l t g node rule ctx a valid located epilogue graphSave graphPointer memory seed prologue⟩

end SmcTuring.Appendix.Listing8BoundarySummary
