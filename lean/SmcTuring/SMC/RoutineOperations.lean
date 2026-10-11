module
public import SmcTuring.SMC.RoutineFrames

public section

namespace SmcTuring.SMC

/-- One shared read invocation followed by an actual fetched instruction.
The invocation's return address is the following instruction's PC. -/
theorem read_then_instruction (wordBytes : Int) (image : Image)
    (label routine constant returnField : Int) (s : State)
    (placed : ReadRoutinePlacement image label routine constant returnField)
    (entryReset : LinearAt image s.pc (stackResetProgram constant))
    (entryCall : image.headers (s.pc + 2) = some (.call (.fixed routine), s.pc + 3))
    (top : s.memory constant = returnField + wordBytes)
    (constantSeparate : constant ≠ returnField) (labelSeparate : label ≠ returnField)
    (targetSeparate : s.memory label ≠ returnField)
    (constantCode : image.codeField constant) (returnCode : image.codeField returnField)
    (labelCode : image.codeField label) (targetCode : image.codeField (s.memory label))
    (header : Header) (next : Int)
    (following : image.headers (s.pc + 3) = some (header, next))
    (writes : WritesCode image.codeField wordBytes
      (decode header (readInvocationResult label routine returnField s))
      (readInvocationResult label routine returnField s)) :
    runImage wordBytes image 11 s = some
      (execute wordBytes (decode header (readInvocationResult label routine returnField s))
        next (readInvocationResult label routine returnField s)) ∧
      PureSteps wordBytes image 11 s := by
  have first := read_routine_correct wordBytes image label routine constant returnField s placed
    entryReset entryCall top constantSeparate labelSeparate targetSeparate constantCode returnCode labelCode targetCode
  have last := image_single wordBytes image header next (readInvocationResult label routine returnField s)
    (by simpa only [readInvocationResult] using following)
  constructor
  · rw [show (11 : Nat) = 10 + 1 by rfl, run_image_add, first.1, Option.bind_some]
    exact last.1
  · rw [show (11 : Nat) = 10 + 1 by rfl,
      pure_steps_composition wordBytes image 10 1 s _ first.1]
    exact ⟨first.2, last.2.mpr writes⟩

@[expose] def readCopyResult (label routine returnField destination : Int) (s : State) : State :=
  { readInvocationResult label routine returnField s with
    memory := write (write s.memory destination (s.memory (s.memory label))) returnField (routine + 7)
    pc := s.pc + 4 }

theorem read_copy_correct (wordBytes : Int) (image : Image)
    (label routine constant returnField destination : Int) (s : State)
    (placed : ReadRoutinePlacement image label routine constant returnField)
    (entryReset : LinearAt image s.pc (stackResetProgram constant))
    (entryCall : image.headers (s.pc + 2) = some (.call (.fixed routine), s.pc + 3))
    (top : s.memory constant = returnField + wordBytes)
    (constantSeparate : constant ≠ returnField) (labelSeparate : label ≠ returnField)
    (targetSeparate : s.memory label ≠ returnField) (destinationSeparate : destination ≠ returnField)
    (constantCode : image.codeField constant) (returnCode : image.codeField returnField)
    (labelCode : image.codeField label) (targetCode : image.codeField (s.memory label))
    (destinationCode : image.codeField destination)
    (following : image.headers (s.pc + 3) = some (.store (.fixed destination), s.pc + 4)) :
    runImage wordBytes image 11 s = some (readCopyResult label routine returnField destination s) ∧
      PureSteps wordBytes image 11 s := by
  have executed := read_then_instruction wordBytes image label routine constant returnField s placed
    entryReset entryCall top constantSeparate labelSeparate targetSeparate constantCode returnCode labelCode targetCode
    (.store (.fixed destination)) (s.pc + 4) following
    (by simp [WritesCode, footprint, decode, Address.eval, destinationCode])
  have effect : execute wordBytes (decode (.store (.fixed destination))
      (readInvocationResult label routine returnField s)) (s.pc + 4)
      (readInvocationResult label routine returnField s) = readCopyResult label routine returnField destination s := by
    simp only [decode, Address.eval, execute, readInvocationResult, readCopyResult]
    rw [writes_commute _ returnField destination _ _ (Ne.symm destinationSeparate)]
  exact ⟨by simpa only [effect] using executed.1, executed.2⟩

theorem read_copy_frame (label routine returnField destination field : Int) (s : State)
    (returnSeparate : field ≠ returnField) (destinationSeparate : field ≠ destination) :
    (readCopyResult label routine returnField destination s).memory field = s.memory field := by
  simp [readCopyResult, write, returnSeparate, destinationSeparate]

namespace Virtual

theorem read_copy_register_rep (layout : Layout) (source : Dolan.Mov.State) (target : State)
    (label routine returnField : Int) (r : Dolan.Mov.Register) (value : Dolan.Mov.Word)
    (rep : Rep layout source target)
    (loaded : target.memory (target.memory label) = encodeWord layout.data value)
    (outside : ¬ codeField layout.data returnField) :
    Rep layout { source with registers := write source.registers r value }
      (readCopyResult label routine returnField (registerField layout r) target) := by
  have stored := register_write_rep layout source target r value rep
  have restored := metadata_write_frame layout { source with registers := write source.registers r value }
    { target with memory := write target.memory (registerField layout r) (encodeWord layout.data value) }
    returnField (routine + 7) stored
    (fun q => data_field_separate layout.data _ _ outside (register_is_code layout q))
    (fun p => data_field_separate layout.data _ _ outside (heap_is_code layout.data p))
  simpa only [readCopyResult, readInvocationResult, loaded, Rep] using restored

end Virtual
end SmcTuring.SMC
