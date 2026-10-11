module
public import SmcTuring.Native.DwordDecodeImage
public import SmcTuring.Native.StringDwordArithmetic

public section
namespace SmcTuring.Native.StringMixed

/-- A successful mixed fetch supplies its complete current packet. -/
theorem packet (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : MixedDword.Form mode)
    (fetched : MixedDword.fetch mode memory pc = some form) :
    ByteMemory.bytesAt memory pc (MixedDword.encode mode form).length = MixedDword.encode mode form := by
  unfold MixedDword.fetch at fetched
  cases header : DwordArithmetic.packetSize (ByteMemory.bytesAt memory pc 2) with
  | some count =>
    simp only [header] at fetched
    rcases Option.map_eq_some_iff.mp fetched with ⟨arith,current,same⟩
    cases same
    exact DwordDecodeImage.arithmetic_fetch memory pc arith current
  | none =>
    simp only [header] at fetched
    cases mode with
    | x86 =>
      simp only at fetched
      rcases Option.map_eq_some_iff.mp fetched with ⟨copy,current,same⟩
      cases same
      exact DwordDecodeImage.copy_fetch .x86 memory pc copy current
    | x64 =>
      simp only at fetched
      split at fetched
      · rcases Option.bind_eq_some_iff.mp fetched with ⟨native,current,decoded⟩
        cases native with
        | memory operation displacement =>
          cases operation <;> simp only at decoded <;> cases decoded
          exact DecodeImage.native_fetch .x64 memory pc (.memory .exchangeAcc displacement) current
        | moffs address => cases decoded
        | exchangeIndirect => cases decoded
        | callRelative displacement => cases decoded
      · rcases Option.map_eq_some_iff.mp fetched with ⟨copy,current,same⟩
        cases same
        exact DwordDecodeImage.copy_fetch .x64 memory pc copy current

@[expose] def canonical (mode : Mode) : MixedDword.Form mode → StringDword.Form mode
  | .arithmetic form => StringDwordArithmetic.canonical mode form
  | .copy form => StringDwordCopy.copy mode form
  | .wideExchange d => StringDwordCopy.native .x64 (.memory .exchangeAcc d)

theorem fetched (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : MixedDword.Form mode)
    (current : MixedDword.fetch mode memory pc = some form) :
    StringDword.fetch mode memory pc = some (canonical mode form) := by
  have image := packet mode memory pc form current
  cases form with
  | arithmetic form => exact StringDwordArithmetic.encoding mode form memory pc image
  | copy form => exact StringDwordCopy.copy_encoding mode form memory pc image
  | wideExchange d => exact StringDwordCopy.native_encoding .x64 (.memory .exchangeAcc d) memory pc image

theorem execute (mode : Mode) (form : MixedDword.Form mode) (state : StringExecution.State mode) :
    StringDword.execute mode (canonical mode form) state =
      {state with principal := MixedDword.execute mode form state.principal} := by
  cases form with
  | arithmetic form => exact StringDwordArithmetic.execute mode form state
  | copy form => exact StringDwordCopy.copy_execute mode form state
  | wideExchange d => exact StringDwordCopy.native_execute .x64 (.memory .exchangeAcc d) state

/-- The lifted trace follows actual current-byte fetches, including mutable
operands. Only the canonical names of overlapping forms change. -/
theorem trace (mode : Mode) (state : StringExecution.State mode) (forms : List (MixedDword.Form mode))
    (final : Execution.State mode) (actual : MixedDword.Trace mode state.principal forms final) :
    StringDword.Trace mode state (forms.map (canonical mode)) {state with principal := final} := by
  cases state with
  | mk principal si di df =>
    change MixedDword.Trace mode principal forms final at actual
    induction actual with
    | nil => exact .nil _
    | step current rest ih =>
      refine .step (fetched mode _ _ _ current) ?_
      rw [execute]
      exact ih

end SmcTuring.Native.StringMixed
