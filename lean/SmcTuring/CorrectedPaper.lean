module
public import SmcTuring.Appendix.Listing9JointFullExecution
public import SmcTuring.SMC.ComputableFiniteTM0
public import SmcTuring.SMC.ComputableActiveFields
public import SmcTuring.Dolan.FourStopping

public section
namespace SmcTuring.CorrectedPaper
open SMC SMC.Effective Turing Appendix
set_option maxHeartbeats 2000000

/-- Unbounded integer-address semantics for the paper's mathematical claim.
The fixed pure image simulates every finite source TM,including divergence
and infinitely many changes caused by fetched instructions. The additional
distinct-field witness fetches each changed field's owning store immediately
after changing that field. Its literal identity-memory initializer and
primitive-recursiveness are part of the statement, excluding oracle memory. -/
@[expose] def Unbounded : Prop :=
  (∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet)),
    (Concrete.ReachesTerminal (Concrete.initialTMState machine input) ↔ TM.Halts machine (TM.initialConfiguration machine input)) ∧
    (Concrete.RunsForever (Concrete.initialTMState machine input) ↔ TM.Diverges machine (TM.initialConfiguration machine input)) ∧
    Concrete.PureComputation (Concrete.initialTMState machine input) ∧
    (TM.Diverges machine (TM.initialConfiguration machine input) → Concrete.InfinitelyChanges (Concrete.initialTMState machine input))) ∧
  Primrec Concrete.activeInitial.memory ∧ Concrete.RunsForever Concrete.activeInitial ∧
    Concrete.PureComputation Concrete.activeInitial ∧
    Concrete.InfinitelyChanges Concrete.activeInitial ∧ Concrete.UnboundedChangedFields Concrete.activeInitial

/-- Dolan foundation: four registers, three MOV forms, a fixed body and one
unconditional backedge. Invalid dereferences stop execution. Each simulated
halt has a certificate reaching the deliberate zero-address load, as in
Section 5 of Dolan's paper; invalid loads do not return zero. -/
@[expose] def FourMov : Prop :=
  ∃ program : List Dolan.Four.Instruction,
    program.length = 2252 ∧
    ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet)),
      let configuration := TM.initialConfiguration machine input
      let initial := Dolan.Four.initialState (Dolan.Mov.initialKernelState machine configuration)
      (Dolan.Four.LoopHalts program initial ↔ TM.Halts machine configuration) ∧
      (Dolan.Four.ZeroTrapHalts program initial ↔ TM.Halts machine configuration) ∧
      (Dolan.Four.LoopDiverges program initial ↔ TM.Diverges machine configuration)

/-- An effective finite-alphabet interpreter receives the encoded finite
machine/input only. Each terminal journal is on a halted configuration actually
reached by this numbered interpreter on the same encoded input. -/
@[expose] def EffectiveInterpreter : Prop := ∀ (alphabet states : Nat),

    ∃ (alphabetCount labelCount : Nat) (symbols : InterpreterAlphabet ≃ Fin alphabetCount)
      (start : Fin labelCount),
      letI : Inhabited (Fin alphabetCount) := ⟨symbols default⟩
      letI : Inhabited (Fin labelCount) := ⟨start⟩
      ∃ numbered : TM0.Machine (Fin alphabetCount) (Fin labelCount),
        ∀ input : SearchInput alphabet states,
          (Concrete.ReachesTerminal (numberedInitial numbered symbols input) ↔
            TM.Halts (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2)) ∧
          (Concrete.RunsForever (numberedInitial numbered symbols input) ↔
            TM.Diverges (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2)) ∧
          Concrete.PureComputation (numberedInitial numbered symbols input) ∧
          (TM.Diverges (TM.thaw input.1) (TM.initialConfiguration (TM.thaw input.1) input.2) ->
            Concrete.InfinitelyChanges (numberedInitial numbered symbols input)) ∧
          ∀ (count : Nat) (finish : State),
            runImage 1 Concrete.image count (numberedInitial numbered symbols input) = some finish ->
            finish.pc = Concrete.terminalPC ->
            ∃ (journal : StateCode) (library : TM0.Cfg (Fin alphabetCount) (Fin labelCount))
              (source : TM.Configuration alphabetCount (2 * labelCount)),
              journal ∈ terminalSearch input.1 input.2 ∧
              StateTransition.Reaches (TM0.step numbered)
                (TM0.init ((searchTape input).map symbols)) library ∧
              TM0.step numbered library = none ∧
              JournalOutput symbols rfl journal library.Tape.right₀ ∧
              MathlibTM0.Rep library source ∧ Concrete.TapeWords source finish

/-- Every finite source configuration is observed on the SAME pure trace:
full tape at all integer positions and the logical head link. -/
@[expose] def Observations : Prop :=
  ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (input : List (Fin alphabet))
    (steps : Nat) (configuration : TM.Configuration alphabet states),
    TM.run machine steps (TM.initialConfiguration machine input)=some configuration →
    ∃ (passes : Nat) (source : Dolan.Mov.State) (finish : SMC.State),
      Concrete.TMTraceSpec machine configuration source (Concrete.initialTMState machine input) finish steps passes ∧
      finish.memory (Virtual.registerField Concrete.dataLayout .current)=
        encodeWord Concrete.dataLayout.data (.address ((Dolan.Table.tapeLayout alphabet states).cell configuration.head)) ∧
      ∀ position : Int,finish.memory (heapField Concrete.dataLayout.data ((Dolan.Table.tapeLayout alphabet states).cell position,false))=
        encodeWord Concrete.dataLayout.data (.address ((Dolan.Table.tapeLayout alphabet states).symbol (configuration.tape position)))

theorem observations : Observations := by
  intro alphabet states machine input steps configuration actual
  obtain ⟨passes,source,finish,traced⟩ := Concrete.tm_run_correct machine input steps configuration actual
  exact ⟨passes,source,finish,traced,Concrete.configuration_head_word machine configuration source finish traced.scanned traced.represented,
    Concrete.configuration_tape_words machine configuration source finish traced.scanned traced.represented⟩

/-- Bounded printed Listing9/Listing8 realization. Static byte capacity and
relative reach are explicit;no finite processor is called unbounded. All
native traces,phase images and SAME-prefix catalog/owner certificates are derived. -/
theorem bounded_appendix {alphabet states : Nat} (machine : TM.Machine alphabet states) (capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (halted : TM.step machine finish=none)
    (mode : Native.Mode) (start : Nat)
    (capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      Listing8TMRun.width (count+input.length)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (reach : mode=.x64 → 1474+(states*(alphabet+1))*84+Listing8TMRun.width (count+input.length)*64≤2^31)
    (memory : Native.ByteMemory.Memory) (seed : Native.StringExecution.State mode) :
    ∃ lastNode : Fin (Listing8TMRun.width (count+input.length)),
      Listing8TMWindow.position (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) lastNode=finish.head ∧
      Listing9JointFullExecution.Certificate mode start
        (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
        (Listing9TMStaticExecution.bodyTargets mode start)
        (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
        (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state)
        (Listing8TMWindow.graph machine (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length))
          (Listing8TMRun.width (count+input.length)) (Listing8TMRun.positive (count+input.length)) finish)
        lastNode (Listing8TMRules.index finish.state (Listing8TMRules.endSlot alphabet)) memory seed := by
  exact Listing9JointFullExecution.complete_input machine capacity input finish count actual halted mode start capacityBytes reach memory seed

/-- Native quantitative conditions are part of the bounded appendix clause,
not assumptions of the unbounded universality/purity clauses. -/
@[expose] def BoundedAppendix : Prop :=
  ∀ (alphabet states : Nat) (machine : TM.Machine alphabet states) (_capacity : alphabet<2^32)
    (input : List (Fin alphabet)) (finish : TM.Configuration alphabet states) (count : Nat)
    (_actual : TM.run machine count (TM.initialConfiguration machine input)=some finish) (_halted : TM.step machine finish=none)
    (mode : Native.Mode) (start : Nat)
    (_capacityBytes : start+(if mode=.x86 then 943 else 1481)+(states*(alphabet+1))*(if mode=.x86 then 66 else 84)+
      Listing8TMRun.width (count+input.length)*(if mode=.x86 then 46 else 64)<2^(8*mode.wordBytes))
    (_reach : mode=.x64 → 1474+(states*(alphabet+1))*84+Listing8TMRun.width (count+input.length)*64≤2^31)
    (memory : Native.ByteMemory.Memory) (seed : Native.StringExecution.State mode),
    ∃ lastNode : Fin (Listing8TMRun.width (count+input.length)),
      Listing8TMWindow.position (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length)) lastNode=finish.head ∧
      Listing9JointFullExecution.Certificate mode start
        (Listing9TMStaticExecution.bodyLayout mode start machine (TM.initialConfiguration machine input) (count+input.length))
        (Listing9TMStaticExecution.bodyTargets mode start)
        (Listing8TMRun.initialGraph machine (TM.initialConfiguration machine input) (count+input.length))
        (Listing8TMRun.firstNode (count+input.length)) (Listing8TMRules.entry (TM.initialConfiguration machine input).state)
        (Listing8TMWindow.graph machine (Listing8TMRun.lower (TM.initialConfiguration machine input) (count+input.length))
          (Listing8TMRun.width (count+input.length)) (Listing8TMRun.positive (count+input.length)) finish)
        lastNode (Listing8TMRules.index finish.state (Listing8TMRules.endSlot alphabet)) memory seed

/-- Mathematical corrected-paper umbrella. Physical ISA/fetch/segmentation,
CET,mapping,ABI and stop/observation refinements remain explicit handoff gates;
this theorem does not assert hardware RET/OS execution or CI acceptance. -/
@[expose] def Statement : Prop := Unbounded ∧ FourMov ∧ EffectiveInterpreter ∧ Observations ∧ BoundedAppendix

theorem full_paper : Statement := by
  refine ⟨⟨Concrete.pure_infinitely_smc_universality,?_⟩,Dolan.Four.four_register_mov_certified_simulation,
    Effective.terminal_search_pure_smc,observations,?_⟩
  · exact Concrete.computably_initialized_unbounded_smc_witness
  · intro alphabet states machine capacity input finish count actual halted mode start capacityBytes reach memory seed
    exact bounded_appendix machine capacity input finish count actual halted mode start capacityBytes reach memory seed

end SmcTuring.CorrectedPaper
