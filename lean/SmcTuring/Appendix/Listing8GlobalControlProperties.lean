module
public import SmcTuring.Appendix.Listing8GlobalControlTemplates

public section
namespace SmcTuring.Appendix.Listing8GlobalControlProperties
open Native

/-- Transfer the preserved catalog to the actual endpoint of an abstract
trace. Concrete wrappers derive both its initial catalog and exact stores. -/
theorem after_trace (mode : Mode) (origin : Nat) (forms : List (StringStack.Form mode))
    (state finish : StringExecution.State mode)
    (initial : Listing8GlobalControlTemplates.Property mode origin state.principal.memory)
    (regions : StringStoreRegions.Run mode (Listing8GlobalControlLayout.Allowed mode origin) forms state)
    (actual : StringStack.Trace mode state forms finish) :
    Listing8GlobalControlTemplates.Property mode origin finish.principal.memory := by
  have kept:=Listing8GlobalControlTemplates.all_states mode origin forms state initial regions
  have ending:=StringTemplateStates.at_prefix mode
    (fun reached => Listing8GlobalControlTemplates.Property mode origin reached.principal.memory) forms [] state
    (by simpa only [List.append_nil] using kept)
  rw [StringWrites.trace_run_eq mode actual] at ending
  exact ending

end SmcTuring.Appendix.Listing8GlobalControlProperties
