module
public import SmcTuring.SMC.StoreRoutines
public import SmcTuring.SMC.VirtualInitialization

public section

namespace SmcTuring.SMC.Virtual

open Dolan

theorem read_invocation_rep (layout : Layout) (source : Mov.State) (target : State)
    (label routine returnField : Int) (rep : Rep layout source target)
    (outside : ¬ codeField layout.data returnField) :
    Rep layout source (readInvocationResult label routine returnField target) := by
  have frame := metadata_write_frame layout source target returnField (routine + 7) rep
    (fun r => data_field_separate layout.data _ _ outside (register_is_code layout r))
    (fun p => data_field_separate layout.data _ _ outside (heap_is_code layout.data p))
  simpa only [readInvocationResult, Rep] using frame

theorem store_invocation_rep (layout : Layout) (source : Mov.State) (target : State)
    (label routine returnField : Int) (p : Nat × Bool) (value : Mov.Word)
    (rep : Rep layout source target) (address : target.memory label = heapField layout.data p)
    (accumulator : target.acc = encodeWord layout.data value)
    (outside : ¬ codeField layout.data returnField) :
    Rep layout { source with memory := write source.memory p value }
      (storeInvocationResult label routine returnField target) := by
  have updated := heap_write_rep layout source target p value rep
  have frame := metadata_write_frame layout { source with memory := write source.memory p value }
    { target with memory := write target.memory (heapField layout.data p) (encodeWord layout.data value) }
    returnField (routine + 7) updated
    (fun r => data_field_separate layout.data _ _ outside (register_is_code layout r))
    (fun q => data_field_separate layout.data _ _ outside (heap_is_code layout.data q))
  simpa only [storeInvocationResult, address, accumulator, Rep] using frame

theorem read_register_routine (layout : Layout) (wordBytes : Int) (image : Image)
    (source : Mov.State) (target : State) (r : Mov.Register)
    (label routine constant returnField : Int) (rep : Rep layout source target)
    (labelValue : target.memory label = registerField layout r)
    (placed : ReadRoutinePlacement image label routine constant returnField)
    (entryReset : LinearAt image target.pc (stackResetProgram constant))
    (entryCall : image.headers (target.pc + 2) = some (.call (.fixed routine), target.pc + 3))
    (top : target.memory constant = returnField + wordBytes)
    (constantSeparate : constant ≠ returnField) (labelSeparate : label ≠ returnField)
    (outside : ¬ codeField layout.data returnField)
    (constantCode : image.codeField constant) (returnCode : image.codeField returnField)
    (labelCode : image.codeField label)
    (storage : ∀ field, codeField layout.data field → image.codeField field) :
    ∃ result, runImage wordBytes image 10 target = some result ∧ Rep layout source result ∧
      result.acc = encodeWord layout.data (source.registers r) ∧ PureSteps wordBytes image 10 target := by
  have targetSeparate : target.memory label ≠ returnField := by
    rw [labelValue]
    exact data_field_separate layout.data _ _ outside (register_is_code layout r)
  have targetCode : image.codeField (target.memory label) := by
    rw [labelValue]
    exact storage _ (register_is_code layout r)
  have executed := read_routine_correct wordBytes image label routine constant returnField target placed
    entryReset entryCall top constantSeparate labelSeparate targetSeparate constantCode returnCode labelCode targetCode
  refine ⟨_, executed.1, read_invocation_rep layout source target label routine returnField rep outside, ?_, executed.2⟩
  simpa only [readInvocationResult, labelValue] using rep.1 r

end SmcTuring.SMC.Virtual
