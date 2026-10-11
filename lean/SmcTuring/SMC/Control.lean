module
public import SmcTuring.SMC.Macros

public section

namespace SmcTuring.SMC

theorem indirect_write_frame (memory : Int → Int) (field value label : Int)
    (labelSeparate : label ≠ field) (targetSeparate : memory label ≠ field) :
    write memory field value (write memory field value label) = memory (memory label) := by
  simp [write, labelSeparate, targetSeparate]

@[expose] def StableRead (s : State) (label field : Int) : Prop :=
  label ≠ field ∧ s.memory label ≠ field

theorem stable_read_write (s : State) (label field value : Int) (stable : StableRead s label field) :
    StableRead { s with memory := write s.memory field value } label field := by
  simpa [StableRead, write, stable.1] using stable

@[expose] def compareProgram (candidateLabel boundaryLabel scratch : Int) : List Header :=
  copyProgram candidateLabel scratch ++ readProgram boundaryLabel ++ [.subtract scratch]

theorem compare_program_correct (wordBytes candidateLabel boundaryLabel scratch : Int) (s : State)
    (boundaryStable : StableRead s boundaryLabel scratch) :
    run wordBytes (compareProgram candidateLabel boundaryLabel scratch) s =
      { s with
        acc := s.memory (s.memory boundaryLabel)
        memory := write s.memory scratch
          (s.memory (s.memory candidateLabel) - s.memory (s.memory boundaryLabel))
        carry := decide (s.memory (s.memory candidateLabel) < s.memory (s.memory boundaryLabel))
        pc := s.pc + 10 } := by
  simp only [compareProgram, run_append, copy_correct, read_correct]
  simp [run, decode, execute, write, boundaryStable.1, boundaryStable.2, Int.add_assoc]

theorem compare_program_pure (codeField : Int → Prop)
    (wordBytes candidateLabel boundaryLabel scratch : Int) (s : State)
    (boundaryStable : StableRead s boundaryLabel scratch)
    (cl : codeField candidateLabel) (cv : codeField (s.memory candidateLabel))
    (bl : codeField boundaryLabel) (bv : codeField (s.memory boundaryLabel))
    (scratchCode : codeField scratch) :
    PureRun codeField wordBytes (compareProgram candidateLabel boundaryLabel scratch) s := by
  simp only [compareProgram, pure_append, run_append, copy_correct, read_correct]
  refine ⟨⟨copy_pure codeField wordBytes candidateLabel scratch s cl cv scratchCode, ?_⟩, ?_⟩
  · apply read_pure
    · exact bl
    · simpa [write, boundaryStable.1] using bv
  · simp [PureRun, WritesCode, footprint, decode, scratchCode]

/-- Select a continuation or terminal PC using only code-writing reads, MOV,
XOR and AND. The mask is a code word containing zero or negative one. -/
@[expose] def selectionProgram (continuationLabel terminalLabel maskLabel destination : Int) : List Header :=
  copyProgram continuationLabel destination ++ xorProgram terminalLabel destination ++
    andProgram maskLabel destination ++ xorProgram continuationLabel destination

theorem selection_program_correct (wordBytes continuationLabel terminalLabel maskLabel destination : Int)
    (s : State) (halted : Bool)
    (continuationStable : StableRead s continuationLabel destination)
    (terminalStable : StableRead s terminalLabel destination)
    (maskStable : StableRead s maskLabel destination)
    (mask : s.memory (s.memory maskLabel) = if halted then -1 else 0) :
    run wordBytes (selectionProgram continuationLabel terminalLabel maskLabel destination) s =
      { s with
        acc := s.memory (s.memory continuationLabel)
        memory := write s.memory destination
          (if halted then s.memory (s.memory terminalLabel) else s.memory (s.memory continuationLabel))
        carry := false
        pc := s.pc + 20 } := by
  rcases continuationStable with ⟨cl, cv⟩
  rcases terminalStable with ⟨tl, tv⟩
  rcases maskStable with ⟨ml, mv⟩
  simp only [selectionProgram, run_append, copy_correct, xor_program_correct, and_program_correct]
  simp [write, cl, cv, tl, tv, ml, mv, mask, select_word, Int.add_assoc]

theorem selection_program_pure (codeField : Int → Prop)
    (wordBytes continuationLabel terminalLabel maskLabel destination : Int) (s : State)
    (continuationStable : StableRead s continuationLabel destination)
    (terminalStable : StableRead s terminalLabel destination)
    (maskStable : StableRead s maskLabel destination)
    (cl : codeField continuationLabel) (cv : codeField (s.memory continuationLabel))
    (tl : codeField terminalLabel) (tv : codeField (s.memory terminalLabel))
    (ml : codeField maskLabel) (mv : codeField (s.memory maskLabel))
    (destinationCode : codeField destination) :
    PureRun codeField wordBytes
      (selectionProgram continuationLabel terminalLabel maskLabel destination) s := by
  simp only [selectionProgram, pure_append, run_append, copy_correct, xor_program_correct, and_program_correct]
  refine ⟨⟨⟨copy_pure codeField wordBytes continuationLabel destination s cl cv destinationCode, ?_⟩, ?_⟩, ?_⟩
  · apply xor_program_pure <;> try assumption
    simpa [write, terminalStable.1] using tv
  · apply and_program_pure <;> try assumption
    simpa [write, maskStable.1] using mv
  · apply xor_program_pure <;> try assumption
    simpa [write, continuationStable.1] using cv

end SmcTuring.SMC
