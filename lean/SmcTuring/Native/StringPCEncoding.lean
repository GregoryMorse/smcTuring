module
public import SmcTuring.Native.StringPCSteps
public import SmcTuring.Native.StringProgram

public section
namespace SmcTuring.Native.StringPCEncoding

theorem string_size (mode : Mode) (form : StringForm.Form mode) :
    StringPCSteps.size mode (StringWrites.liftString mode form)=(StringForm.encode mode form).length := by
  cases form with
  | native form => exact (Native.instruction_length mode form).symm
  | initialize32 => rfl
  | exchangeIndex => rfl
  | subtractSmall => rfl
  | subtractFull => rfl
  | move => rfl

theorem string_total (mode : Mode) (forms : List (StringForm.Form mode)) :
    StringPCSteps.total mode (forms.map (StringWrites.liftString mode))=((forms.map (StringForm.encode mode)).flatten).length := by
  induction forms with
  | nil => rfl
  | cons form rest ih =>
    simp only [List.map_cons,List.flatten_cons,List.length_append,StringPCSteps.total,List.sum_cons]
    rw [string_size mode form]
    exact congrArg (fun count => (StringForm.encode mode form).length+count) ih

theorem program_total (mode : Mode) (start source destination size : Nat) (fits : size<2^31) :
    StringPCSteps.total mode ((StringProgram.forms mode start source destination size).map (StringWrites.liftString mode))=
      StringCodec.endpoint mode start size-start := by
  rw [string_total,StringProgram.encoding mode start source destination size fits,StringCodec.whole_length]

end SmcTuring.Native.StringPCEncoding
