module
public import SmcTuring.SMC.ComputableInitialization

public section

namespace SmcTuring.SMC.Effective

open Dolan.Encoding

variable {alphabet states : Nat}

theorem address_code_arg (address : Address) : (addressCode address).2 = zigzag (addressArg address) := by
  cases address <;> rfl

theorem header_code_arg (header : Header) : (headerCode header).2.2 = zigzag (headerArg header) := by
  cases header <;> exact address_code_arg _

abbrev StepInput (alphabet states : Nat) := Prod (TM.FrozenMachine alphabet states) (Prod (List (Fin alphabet)) StateCode)
abbrev FetchedInput (alphabet states : Nat) := Prod (StepInput alphabet states) (Prod HeaderCode Nat)
abbrev DecodedInput (alphabet states : Nat) := Prod (FetchedInput alphabet states) InstructionCode

/-- A complete coded instruction step. Both reads use the certified fixed
initializer; all later changes are supplied by the finite journal. -/
@[expose] def stepCode (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (s : StateCode) : Option StateCode :=
  (fixedHeadersCode s.2.2.1).bind fun entry =>
    (decodeHeaderCode (initialWordCode machine input entry.1.2.2) entry.1 s).bind fun instruction =>
      executeInstructionCode 2 entry.2 (initialWordCode machine input instruction.2) instruction s

/-- Primitive recursion certifies fetch, operand resolution, both fallback
reads, all ten instruction effects and missing-header failure together. -/
theorem step_code_primrec : Primrec (fun input : StepInput alphabet states => stepCode input.1 input.2.1 input.2.2) := by
  have state : Primrec (fun input : StepInput alphabet states => input.2.2) := Primrec.snd.comp Primrec.snd
  have pc := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp state))
  have fetched := fixed_headers_code_primrec.comp pc
  have machine : Primrec (fun input : FetchedInput alphabet states => input.1.1) := Primrec.fst.comp Primrec.fst
  have symbols : Primrec (fun input : FetchedInput alphabet states => input.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have state : Primrec (fun input : FetchedInput alphabet states => input.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have header : Primrec (fun input : FetchedInput alphabet states => input.2.1) := Primrec.fst.comp Primrec.snd
  have argument := Primrec.snd.comp (Primrec.snd.comp header)
  have fallback := initial_word_code_primrec.comp (Primrec.pair machine (Primrec.pair symbols argument))
  have decoded := decode_header_code_primrec.comp (Primrec.pair fallback (Primrec.pair header state))
  have machine : Primrec (fun input : DecodedInput alphabet states => input.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have symbols : Primrec (fun input : DecodedInput alphabet states => input.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have state : Primrec (fun input : DecodedInput alphabet states => input.1.1.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have next : Primrec (fun input : DecodedInput alphabet states => input.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have instruction : Primrec (fun input : DecodedInput alphabet states => input.2) := Primrec.snd
  have fallback := initial_word_code_primrec.comp (Primrec.pair machine (Primrec.pair symbols (Primrec.snd.comp instruction)))
  have execute := execute_instruction_code_primrec.comp
    (Primrec.pair (Primrec.const 2) (Primrec.pair next (Primrec.pair fallback (Primrec.pair instruction state))))
  exact (Primrec.option_bind fetched (Primrec.option_bind decoded execute.to₂).to₂).of_eq fun input => by rfl

/-- The coded step is exactly the existing journal interpreter, including
faults, rather than a new execution semantics. -/
theorem step_code_correct (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (s : Finite.State) :
    stepCode machine input (stateCode s) =
      (Finite.step 1 Concrete.headers (Concrete.initialWords machine input) s).map stateCode := by
  unfold stepCode
  have pc : (stateCode s).2.2.1 = zigzag s.pc := by rfl
  rw [pc, fixed_headers_code_correct]
  cases fetched : Concrete.headers s.pc with
  | none => simp [Finite.step, fetched]
  | some entry =>
    rcases entry with ⟨header, next⟩
    simp only [Option.map_some, Option.bind_some]
    rw [header_code_arg, initial_word_code_correct, unzigzag_zigzag, decode_header_code_correct]
    simp only [Option.bind_some]
    rw [instruction_code_arg, initial_word_code_correct, unzigzag_zigzag]
    simpa only [Finite.step, fetched, Option.map_some, show zigzag (1 : Int) = 2 by rfl] using
      execute_instruction_code_correct 1 next (Concrete.initialWords machine input)
        (Finite.decode (Concrete.initialWords machine input) header s) s

/-- Bounded execution uses primitive recursion on the requested prefix length. -/
@[expose] def runCode (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) : Nat -> StateCode -> Option StateCode
  | 0, s => some s
  | count + 1, s => (stepCode machine input s).bind (runCode machine input count)

/-- Iteration on the optional journal state propagates failure exactly. -/
theorem run_code_iterate_option (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (count : Nat) (start : Option StateCode) :
    start.bind (runCode machine input count) =
      (fun state : Option StateCode => state.bind (stepCode machine input))^[count] start := by
  induction count generalizing start with
  | zero => cases start <;> rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply, ←ih]
    simp only [runCode, Option.bind_assoc]

theorem run_code_iterate (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (count : Nat) (start : StateCode) :
    runCode machine input count start =
      (fun state : Option StateCode => state.bind (stepCode machine input))^[count] (some start) := by
  simpa only [Option.bind_some] using run_code_iterate_option machine input count (some start)

abbrev RunInput (alphabet states : Nat) := Prod (TM.FrozenMachine alphabet states) (Prod (List (Fin alphabet)) (Prod Nat StateCode))

theorem run_code_primrec : Primrec (fun input : RunInput alphabet states => runCode input.1 input.2.1 input.2.2.1 input.2.2.2) := by
  have count : Primrec (fun input : RunInput alphabet states => input.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have initial : Primrec (fun input : RunInput alphabet states => some input.2.2.2) := Primrec.option_some.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have machine : Primrec (fun input : Prod (Prod (RunInput alphabet states) (Option StateCode)) StateCode => input.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have symbols : Primrec (fun input : Prod (Prod (RunInput alphabet states) (Option StateCode)) StateCode => input.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have one := step_code_primrec.comp (Primrec.pair machine (Primrec.pair symbols Primrec.snd))
  have advance : Primrec₂ (fun input : RunInput alphabet states => fun state : Option StateCode => state.bind (stepCode input.1 input.2.1)) :=
    (Primrec.option_bind Primrec.snd one.to₂).of_eq fun input => by rfl
  exact (Primrec.nat_iterate count initial advance).of_eq fun input => (run_code_iterate _ _ _ _).symm

/-- All bounded prefixes, including failures, are the original finite evaluator. -/
theorem run_code_correct (machine : TM.FrozenMachine alphabet states) (input : List (Fin alphabet)) (count : Nat) (start : Finite.State) :
    runCode machine input count (stateCode start) =
      (Finite.run 1 Concrete.headers (Concrete.initialWords machine input) count start).map stateCode := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [runCode, step_code_correct]
    cases stepped : Finite.step 1 Concrete.headers (Concrete.initialWords machine input) start with
    | none => simp [Finite.run, stepped]
    | some next => simpa only [Finite.run, stepped, Option.map_some, Option.bind_some] using ih next

/-- The actual frozen-machine execution function has a uniform primitive
recursion certificate for its complete natural state code. -/
theorem concrete_finite_run_primrec : Primrec (fun input : Prod (TM.FrozenMachine alphabet states) (Prod (List (Fin alphabet)) Nat) =>
    (Concrete.finiteRun input.1 input.2.1 input.2.2).map stateCode) := by
  exact (run_code_primrec.comp
    (Primrec.pair Primrec.fst (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.const (stateCode Concrete.initialDescription)))))).of_eq
      fun input => run_code_correct input.1 input.2.1 input.2.2 Concrete.initialDescription

end SmcTuring.SMC.Effective
