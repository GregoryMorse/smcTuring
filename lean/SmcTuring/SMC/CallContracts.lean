module
public import SmcTuring.SMC.RoutineOperations

public section

namespace SmcTuring.SMC

/-- Structural placement and local separation assumptions for an actual CALL
to a shared reader. These are obligations for the eventual image constructor,
not an assumed machine simulation or an assumed purity theorem. -/
structure ReadCallReady (wordBytes : Int) (image : Image)
    (label routine constant returnField : Int) (s : State) : Prop where
  placed : ReadRoutinePlacement image label routine constant returnField
  entryReset : LinearAt image s.pc (stackResetProgram constant)
  entryCall : image.headers (s.pc + 2) = some (.call (.fixed routine), s.pc + 3)
  top : s.memory constant = returnField + wordBytes
  constantSeparate : constant ≠ returnField
  labelSeparate : label ≠ returnField
  targetSeparate : s.memory label ≠ returnField
  constantCode : image.codeField constant
  returnCode : image.codeField returnField
  labelCode : image.codeField label
  targetCode : image.codeField (s.memory label)

theorem ReadCallReady.correct (wordBytes : Int) (image : Image)
    (label routine constant returnField : Int) (s : State)
    (ready : ReadCallReady wordBytes image label routine constant returnField s) :
    runImage wordBytes image 10 s = some (readInvocationResult label routine returnField s) ∧
      PureSteps wordBytes image 10 s :=
  read_routine_correct wordBytes image label routine constant returnField s ready.placed ready.entryReset ready.entryCall
    ready.top ready.constantSeparate ready.labelSeparate ready.targetSeparate
    ready.constantCode ready.returnCode ready.labelCode ready.targetCode

theorem ReadCallReady.copy (wordBytes : Int) (image : Image)
    (label routine constant returnField destination : Int) (s : State)
    (ready : ReadCallReady wordBytes image label routine constant returnField s)
    (destinationSeparate : destination ≠ returnField) (destinationCode : image.codeField destination)
    (following : image.headers (s.pc + 3) = some (.store (.fixed destination), s.pc + 4)) :
    runImage wordBytes image 11 s = some (readCopyResult label routine returnField destination s) ∧
      PureSteps wordBytes image 11 s :=
  read_copy_correct wordBytes image label routine constant returnField destination s ready.placed ready.entryReset
    ready.entryCall ready.top ready.constantSeparate ready.labelSeparate ready.targetSeparate destinationSeparate
    ready.constantCode ready.returnCode ready.labelCode ready.targetCode destinationCode following

end SmcTuring.SMC
