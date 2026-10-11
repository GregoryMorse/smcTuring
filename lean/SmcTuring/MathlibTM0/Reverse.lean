module
public import SmcTuring.MathlibTM0.Simulation
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option

public section

namespace SmcTuring.MathlibTM0.Reverse

section Normalized

variable {alphabet states : Nat} [Inhabited (Fin alphabet)] [Inhabited (Fin states)]

/-- Original labels and a pending left/right move. There are three finite phases
per source label; the pending phase stores no unbounded internal data. -/
abbrev Labels (states : Nat) := Fin states × Option Bool

@[expose, instance_reducible] def labelInhabited : Inhabited (Labels states) := ⟨(default, none)⟩
attribute [local instance] labelInhabited

omit [Inhabited (Fin alphabet)] [Inhabited (Fin states)] in
theorem labels_finite (states : Nat) : Finite (Labels states) := by infer_instance

omit [Inhabited (Fin alphabet)] [Inhabited (Fin states)] in
theorem labels_card (states : Nat) : Fintype.card (Labels states) = 3 * states := by
  simp [Labels, Fintype.card_prod, Fintype.card_option, Fintype.card_bool, Nat.mul_comm]

@[expose] def moveDirection (right : Bool) : Turing.Dir := if right then .right else .left

@[expose] def compile (machine : TM.Machine alphabet states) : Turing.TM0.Machine (Fin alphabet) (Labels states) :=
  fun label symbol => match label.2 with
    | none => (machine.transition label.1 symbol).map fun result => ((result.2.2, some result.2.1), .write result.1)
    | some right => some ((label.1, none), .move (moveDirection right))

@[expose] def Rep (source : TM.Configuration alphabet states)
    (library : Turing.TM0.Cfg (Fin alphabet) (Labels states)) : Prop :=
  library.q = (source.state, none) ∧ ∀ position : Int, library.Tape.nth position = source.tape (source.head + position)

@[expose] def sourceResult (source : TM.Configuration alphabet states) (symbol : Fin alphabet)
    (right : Bool) (next : Fin states) : TM.Configuration alphabet states :=
  { state := next, head := if right then source.head + 1 else source.head - 1,
    tape := write source.tape source.head symbol }

@[expose] def libraryMiddle (library : Turing.TM0.Cfg (Fin alphabet) (Labels states)) (symbol : Fin alphabet)
    (right : Bool) (next : Fin states) : Turing.TM0.Cfg (Fin alphabet) (Labels states) :=
  ⟨(next, some right), library.Tape.write symbol⟩

@[expose] def libraryResult (library : Turing.TM0.Cfg (Fin alphabet) (Labels states)) (symbol : Fin alphabet)
    (right : Bool) (next : Fin states) : Turing.TM0.Cfg (Fin alphabet) (Labels states) :=
  ⟨(next, none), (library.Tape.write symbol).move (moveDirection right)⟩

omit [Inhabited (Fin states)] in
theorem represented_head (source : TM.Configuration alphabet states)
    (library : Turing.TM0.Cfg (Fin alphabet) (Labels states)) (rep : Rep source library) :
    library.Tape.head = source.tape source.head := by simpa using rep.2 0

theorem initial_rep (machine : TM.Machine alphabet states) (input : List (Fin alphabet))
    (blank : machine.blank = default) (start : machine.start = default) :
    Rep (TM.initialConfiguration machine input) (Turing.TM0.init input) := by
  constructor
  · change (default, none) = (machine.start, none)
    rw [start]
  · intro position
    simpa [Turing.TM0.init, TM.initialConfiguration, blank] using MathlibTM0.initialized_tape_nth input position

theorem write_step (machine : TM.Machine alphabet states) (source : TM.Configuration alphabet states)
    (library : Turing.TM0.Cfg (Fin alphabet) (Labels states)) (symbol : Fin alphabet) (right : Bool) (next : Fin states)
    (rep : Rep source library) (chosen : machine.transition source.state (source.tape source.head) = some (symbol, right, next)) :
    Turing.TM0.step (compile machine) library = some (libraryMiddle library symbol right next) := by
  simp [Turing.TM0.step, compile, rep.1, represented_head source library rep, chosen, libraryMiddle]

theorem move_step (machine : TM.Machine alphabet states)
    (library : Turing.TM0.Cfg (Fin alphabet) (Labels states)) (symbol : Fin alphabet) (right : Bool) (next : Fin states) :
    Turing.TM0.step (compile machine) (libraryMiddle library symbol right next) =
      some (libraryResult library symbol right next) := by
  rfl

theorem two_steps (machine : TM.Machine alphabet states) (source : TM.Configuration alphabet states)
    (library : Turing.TM0.Cfg (Fin alphabet) (Labels states)) (symbol : Fin alphabet) (right : Bool) (next : Fin states)
    (rep : Rep source library) (chosen : machine.transition source.state (source.tape source.head) = some (symbol, right, next)) :
    (Turing.TM0.step (compile machine) library).bind (Turing.TM0.step (compile machine)) =
      some (libraryResult library symbol right next) := by
  rw [write_step machine source library symbol right next rep chosen]
  exact move_step machine library symbol right next

omit [Inhabited (Fin states)] in
theorem result_rep (source : TM.Configuration alphabet states)
    (library : Turing.TM0.Cfg (Fin alphabet) (Labels states)) (symbol : Fin alphabet) (right : Bool) (next : Fin states)
    (rep : Rep source library) : Rep (sourceResult source symbol right next) (libraryResult library symbol right next) := by
  refine ⟨rfl, ?_⟩
  intro position
  cases right with
  | false =>
    change ((library.Tape.write symbol).move .left).nth position =
      write source.tape source.head symbol (source.head - 1 + position)
    rw [Turing.Tape.move_left_nth, Turing.Tape.write_nth]
    by_cases zero : position - 1 = 0
    · have atHead : source.head - 1 + position = source.head := by omega
      simp [zero, atHead]
    · have separate : source.head - 1 + position ≠ source.head := by omega
      simp only [zero, ite_false, write, separate]
      rw [rep.2 (position - 1)]
      congr 1; omega
  | true =>
    change ((library.Tape.write symbol).move .right).nth position =
      write source.tape source.head symbol (source.head + 1 + position)
    rw [Turing.Tape.move_right_nth, Turing.Tape.write_nth]
    by_cases zero : position + 1 = 0
    · have atHead : source.head + 1 + position = source.head := by omega
      simp [zero, atHead]
    · have separate : source.head + 1 + position ≠ source.head := by omega
      simp only [zero, ite_false, write, separate]
      rw [rep.2 (position + 1)]
      congr 1; omega

theorem missing_step_iff (machine : TM.Machine alphabet states) (source : TM.Configuration alphabet states)
    (library : Turing.TM0.Cfg (Fin alphabet) (Labels states)) (rep : Rep source library) :
    TM.step machine source = none ↔ Turing.TM0.step (compile machine) library = none := by
  simp only [TM.step, Turing.TM0.step, compile, rep.1, represented_head source library rep]
  cases chosen : machine.transition source.state (source.tape source.head) with
  | none => simp
  | some result => rcases result with ⟨symbol, right, next⟩; simp

theorem compiler_respects (machine : TM.Machine alphabet states) :
    StateTransition.Respects (TM.step machine) (Turing.TM0.step (compile machine)) Rep := by
  intro source library rep
  cases chosen : machine.transition source.state (source.tape source.head) with
  | none =>
    have halted : TM.step machine source = none := by simp [TM.step, chosen]
    rw [halted]
    exact (missing_step_iff machine source library rep).mp halted
  | some result =>
    rcases result with ⟨symbol, right, next⟩
    have effect := TM.transition_correct machine source symbol right next chosen
    change TM.step machine source = some (sourceResult source symbol right next) at effect
    rw [effect]
    have before : StateTransition.Reaches₁ (Turing.TM0.step (compile machine)) library
        (libraryMiddle library symbol right next) := Relation.TransGen.single (write_step machine source library symbol right next rep chosen)
    exact ⟨libraryResult library symbol right next, result_rep source library symbol right next rep,
      before.trans (Relation.TransGen.single (move_step machine library symbol right next))⟩

theorem normalized_halts_iff (machine : TM.Machine alphabet states) (input : List (Fin alphabet))
    (blank : machine.blank = default) (start : machine.start = default) :
    TM.Halts machine (TM.initialConfiguration machine input) ↔ (Turing.TM0.eval (compile machine) input).Dom := by
  rw [MathlibTM0.source_halts_eval]
  exact (StateTransition.tr_eval_dom (compiler_respects machine) (initial_rep machine input blank start)).symm

theorem normalized_terminal_output (machine : TM.Machine alphabet states) (input : List (Fin alphabet))
    (blank : machine.blank = default) (start : machine.start = default) (count : Nat)
    (finish : TM.Configuration alphabet states)
    (completed : TM.run machine count (TM.initialConfiguration machine input) = some finish)
    (halted : TM.step machine finish = none) :
    ∃ library : Turing.TM0.Cfg (Fin alphabet) (Labels states),
      library.Tape.right₀ ∈ Turing.TM0.eval (compile machine) input ∧ Rep finish library := by
  have result : finish ∈ StateTransition.eval (TM.step machine) (TM.initialConfiguration machine input) :=
    StateTransition.mem_eval.mpr ⟨MathlibTM0.source_run_reaches machine count _ finish completed, halted⟩
  rcases StateTransition.tr_eval (compiler_respects machine) (initial_rep machine input blank start) result with
    ⟨library, rep, evaluated⟩
  exact ⟨library, (Part.mem_map_iff _).mpr ⟨library, evaluated, rfl⟩, rep⟩

end Normalized

/-- Defaults are selected from the supplied machine, so the adapter covers
arbitrary source blank symbols and start labels, not just numeral zero. -/
theorem halts_iff {alphabet states : Nat} (machine : TM.Machine alphabet states) (input : List (Fin alphabet)) :
    letI : Inhabited (Fin alphabet) := ⟨machine.blank⟩
    letI : Inhabited (Fin states) := ⟨machine.start⟩
    letI : Inhabited (Labels states) := ⟨(machine.start, none)⟩
    TM.Halts machine (TM.initialConfiguration machine input) ↔ (Turing.TM0.eval (compile machine) input).Dom := by
  let : Inhabited (Fin alphabet) := ⟨machine.blank⟩
  let : Inhabited (Fin states) := ⟨machine.start⟩
  let : Inhabited (Labels states) := ⟨(machine.start, none)⟩
  exact normalized_halts_iff machine input rfl rfl

theorem terminal_output {alphabet states : Nat} (machine : TM.Machine alphabet states) (input : List (Fin alphabet))
    (count : Nat) (finish : TM.Configuration alphabet states)
    (completed : TM.run machine count (TM.initialConfiguration machine input) = some finish)
    (halted : TM.step machine finish = none) :
    letI : Inhabited (Fin alphabet) := ⟨machine.blank⟩
    letI : Inhabited (Fin states) := ⟨machine.start⟩
    letI : Inhabited (Labels states) := ⟨(machine.start, none)⟩
    ∃ library : Turing.TM0.Cfg (Fin alphabet) (Labels states),
      library.Tape.right₀ ∈ Turing.TM0.eval (compile machine) input ∧ Rep finish library := by
  let : Inhabited (Fin alphabet) := ⟨machine.blank⟩
  let : Inhabited (Fin states) := ⟨machine.start⟩
  let : Inhabited (Labels states) := ⟨(machine.start, none)⟩
  exact normalized_terminal_output machine input rfl rfl count finish completed halted

end SmcTuring.MathlibTM0.Reverse
