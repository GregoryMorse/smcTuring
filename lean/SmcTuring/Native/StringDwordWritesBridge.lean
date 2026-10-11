module
public import SmcTuring.Native.StringStoreWrites

public section
namespace SmcTuring.Native.StringDwordWritesBridge

theorem trace (mode : Mode) {state final : StringExecution.State mode} {forms : List (StringDword.Form mode)}
    (actual : StringDword.Trace mode state forms final) :
    StringStack.Trace mode state (forms.map (StringStoreWrites.liftDword mode)) final := by
  have lifted:=StringStack.previous_trace mode (StringControl.previous_trace mode actual)
  change StringStack.Trace mode state (forms.map (fun form => StringStack.Form.previous (StringControl.Form.previous form))) final
  simpa only [List.map_map,Function.comp_def] using lifted

end SmcTuring.Native.StringDwordWritesBridge
