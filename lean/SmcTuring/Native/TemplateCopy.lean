module
public import SmcTuring.Native.TemplateRelocation

public section
namespace SmcTuring.Native.TemplateCopy
open ByteMemory StringExecution StringMacroLayout StringMacroEffects TemplateRelocation

@[expose] def compiledBytes (mode : Mode) (p : Params) (specs : List Spec) : List LittleEndian.Byte :=
  TemplateRelocation.bytes mode p.destination p.destination specs

theorem complete_image (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs)
    (blueprint : bytesAt state.principal.memory p.source (compiledBytes mode p specs).length=compiledBytes mode p specs) :
    bytesAt (finish mode p state).principal.memory p.destination (compiledBytes mode p specs).length=compiledBytes mode p specs := by
  have count : (compiledBytes mode p specs).length=p.size := by rw [compiledBytes,bytes_length,size]
  rw [finish_effect mode p state ready]
  change bytesAt (putBytes state.principal.memory p.destination (bytesAt state.principal.memory p.source p.size))
    p.destination (compiledBytes mode p specs).length=compiledBytes mode p specs
  rw [count]
  have written := bytes_at_put state.principal.memory p.destination (bytesAt state.principal.memory p.source p.size)
  rw [bytes_at_length] at written
  rw [written]
  simpa only [count] using blueprint

theorem packet (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs)
    (blueprint : bytesAt state.principal.memory p.source (compiledBytes mode p specs).length=compiledBytes mode p specs)
    (pc : Nat) (spec : Spec) (member : (pc,spec) ∈ places mode p.destination specs) :
    bytesAt (finish mode p state).principal.memory pc (length mode spec)=encode mode (bind mode p.destination pc spec) :=
  whole_packet mode p.destination p.destination specs _ (complete_image mode p specs state ready size blueprint) pc spec member

theorem fetch (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs)
    (blueprint : bytesAt state.principal.memory p.source (compiledBytes mode p specs).length=compiledBytes mode p specs)
    (pc : Nat) (spec : Spec) (member : (pc,spec) ∈ places mode p.destination specs) :
    Fetch.fetch mode (finish mode p state).principal.memory pc=some (bind mode p.destination pc spec) :=
  whole_fetch mode p.destination p.destination specs _ (complete_image mode p specs state ready size blueprint) pc spec member

theorem packet_capacity (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs)
    (pc : Nat) (spec : Spec) (member : (pc,spec) ∈ places mode p.destination specs) :
    pc+length mode spec<2^(8*mode.wordBytes) := by
  have bound := places_upper mode p.destination specs pc spec member
  have fits := (destination_capacity mode p state ready).1
  rw [size] at fits
  omega

theorem moffs_payload (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs)
    (blueprint : bytesAt state.principal.memory p.source (compiledBytes mode p specs).length=compiledBytes mode p specs)
    (pc : Nat) (reference : Reference) (member : (pc,Spec.moffs reference) ∈ places mode p.destination specs) :
    Protected.wordAt mode (finish mode p state).principal.memory (pc+moffsOperandOffset mode) =
      Arithmetic.encodeNat mode (resolve p.destination reference) := by
  have current := packet mode p specs state ready size blueprint pc (.moffs reference) member
  rw [<-encoded_length mode p.destination pc (.moffs reference)] at current
  have payload := StringWindow.packet_window (finish mode p state).principal.memory pc (wordPrefix mode++[0xA3])
    (LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode (resolve p.destination reference))) []
    (by simpa only [TemplateRelocation.bind,encode,List.append_nil] using current)
  simp only [List.length_append,List.length_singleton,LittleEndian.word_encode_length] at payload
  change bytesAt _ (pc+moffsOperandOffset mode) mode.wordBytes = _ at payload
  unfold Protected.wordAt
  rw [payload]
  have decoded := LittleEndian.word_decode_encode mode.wordBytes (Arithmetic.encodeNat mode (resolve p.destination reference))
  simp only [LittleEndian.wordDecode,LittleEndian.word_encode_length,ite_true,Option.some.injEq] at decoded
  exact decoded

theorem memory_target (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs)
    (blueprint : bytesAt state.principal.memory p.source (compiledBytes mode p specs).length=compiledBytes mode p specs)
    (pc : Nat) (op : MemoryOp) (reference : Reference) (member : (pc,Spec.memory op reference) ∈ places mode p.destination specs)
    (reachable : Reachable mode p.destination pc (.memory op reference)) :
    Fetch.fetch mode (finish mode p state).principal.memory pc=some (bind mode p.destination pc (.memory op reference)) ∧
    Execution.memoryAddress mode (Arithmetic.encodeNat mode (pc+length mode (.memory op reference)))
      (Relocation.instructionDisp mode op pc (resolve p.destination reference)) =
        Arithmetic.encodeNat mode (resolve p.destination reference) := by
  constructor
  · exact fetch mode p specs state ready size blueprint pc _ member
  · exact Relocation.memory_hits mode _ _ reachable

theorem call_target (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs)
    (blueprint : bytesAt state.principal.memory p.source (compiledBytes mode p specs).length=compiledBytes mode p specs)
    (pc : Nat) (reference : Reference) (member : (pc,Spec.call reference) ∈ places mode p.destination specs)
    (reachable : Reachable mode p.destination pc (.call reference)) (native : Execution.State mode)
    (location : native.pc=Arithmetic.encodeNat mode pc) :
    Fetch.fetch mode (finish mode p state).principal.memory pc=some (bind mode p.destination pc (.call reference)) ∧
    (Execution.execute mode (bind mode p.destination pc (.call reference)) native).pc=
      Arithmetic.encodeNat mode (resolve p.destination reference) :=
  ⟨fetch mode p specs state ready size blueprint pc _ member,TemplateRelocation.call_target mode p.destination pc reference native location reachable⟩

/-- Whole finite compiled template: one actual TRANSFERDATA trace copies every
instruction and every initialized operand. Each complete destination packet
is live-fetched with the destination's internal/external address bindings. -/
theorem correct (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs)
    (blueprint : bytesAt state.principal.memory p.source (compiledBytes mode p specs).length=compiledBytes mode p specs) :
    Trace mode state (StringProgram.forms mode p.start p.source p.destination p.size) (finish mode p state) ∧
    bytesAt (finish mode p state).principal.memory p.destination (compiledBytes mode p specs).length=compiledBytes mode p specs ∧
    ∀ pc spec, (pc,spec) ∈ places mode p.destination specs ->
      Fetch.fetch mode (finish mode p state).principal.memory pc=some (bind mode p.destination pc spec) :=
  ⟨StringMacroTrace.trace mode p state ready,complete_image mode p specs state ready size blueprint,
    fun pc spec member => fetch mode p specs state ready size blueprint pc spec member⟩

/-- This is compile-time initialization, before any template packet is run.
The blueprint is bound for its future destination, then both original images
are installed in the single byte memory used by the copying trace. -/
@[expose] def compiledImage (mode : Mode) (p : Params) (specs : List Spec) (backing : Memory) : Memory :=
  putBytes (putBytes backing p.start (StringMacroLayout.bytes mode p)) p.source (compiledBytes mode p specs)

theorem initialized_blueprint (mode : Mode) (p : Params) (specs : List Spec) (backing : Memory) :
    bytesAt (compiledImage mode p specs backing) p.source (compiledBytes mode p specs).length=compiledBytes mode p specs :=
  bytes_at_put _ _ _

theorem initialized_macro (mode : Mode) (p : Params) (specs : List Spec) (backing : Memory)
    (size : p.size=span mode specs) (outside : Outside mode p p.source) :
    bytesAt (compiledImage mode p specs backing) p.start (StringMacroLayout.bytes mode p).length=StringMacroLayout.bytes mode p := by
  unfold compiledImage
  rw [bytes_at_frame _ _ _ _ _]
  · exact bytes_at_put _ _ _
  · intro index
    have small := index.isLt
    have total := StringCodec.whole_length mode p.start p.source p.destination p.size
    change (StringMacroLayout.bytes mode p).length=endpoint mode p-p.start at total
    have positions := field_coordinates mode p
    simp only [compiledBytes,bytes_length,<-size,Inside]
    unfold Outside at outside
    rcases outside with before | after <;> omega

theorem ready_initialized (mode : Mode) (p : Params) (specs : List Spec) (backing : Memory) (state : State mode)
    (size : p.size=span mode specs) (entry : state.principal.pc=Arithmetic.encodeNat mode p.start) (forward : state.backwards=false)
    (sizeFits : p.size<2^31) (codeFits : endpoint mode p<2^(8*mode.wordBytes))
    (sourceFits : p.source+max p.size mode.wordBytes<2^(8*mode.wordBytes))
    (destinationFits : p.destination+max p.size mode.wordBytes<2^(8*mode.wordBytes))
    (separate : StringCopy.Apart p.source p.destination p.size)
    (sourceOutside : Outside mode p p.source) (destinationOutside : Outside mode p p.destination) :
    Ready mode p {state with principal := {state.principal with memory := compiledImage mode p specs backing}} :=
  ⟨entry,forward,sizeFits,codeFits,sourceFits,destinationFits,separate,sourceOutside,destinationOutside,
    initialized_macro mode p specs backing size sourceOutside⟩


/-- Static conditions for the two compiled images and complete pointed words.
No initialized image, later readiness or executed trace is a field here. -/
structure Resources (mode : Mode) (p : Params) : Prop where
  sizeFits : p.size<2^31
  codeFits : endpoint mode p<2^(8*mode.wordBytes)
  sourceFits : p.source+max p.size mode.wordBytes<2^(8*mode.wordBytes)
  destinationFits : p.destination+max p.size mode.wordBytes<2^(8*mode.wordBytes)
  buffers : StringCopy.Apart p.source p.destination p.size
  sourceOutside : Outside mode p p.source
  destinationOutside : Outside mode p p.destination

@[expose] def initialState (mode : Mode) (p : Params) (specs : List Spec) (backing : Memory) (state : State mode) : State mode :=
  {state with
    principal := {state.principal with pc := Arithmetic.encodeNat mode p.start, memory := compiledImage mode p specs backing}
    backwards := false}

theorem ready_initial (mode : Mode) (p : Params) (specs : List Spec) (backing : Memory) (state : State mode)
    (size : p.size=span mode specs) (resources : Resources mode p) :
    Ready mode p (initialState mode p specs backing state) :=
  ⟨rfl,rfl,resources.sizeFits,resources.codeFits,resources.sourceFits,resources.destinationFits,resources.buffers,
    resources.sourceOutside,resources.destinationOutside,initialized_macro mode p specs backing size resources.sourceOutside⟩

/-- Constructed compile-time binding and whole-template copy from arbitrary
backing bytes/register seeds. Both initial images and every destination fetch
are conclusions derived from compilation and static resources alone. -/
theorem original_image_correct (mode : Mode) (p : Params) (specs : List Spec) (backing : Memory) (state : State mode)
    (size : p.size=span mode specs) (resources : Resources mode p) :
    let initial := initialState mode p specs backing state
    Trace mode initial (StringProgram.forms mode p.start p.source p.destination p.size) (finish mode p initial) ∧
    bytesAt (finish mode p initial).principal.memory p.destination (compiledBytes mode p specs).length=compiledBytes mode p specs ∧
    ∀ pc spec, (pc,spec) ∈ places mode p.destination specs ->
      Fetch.fetch mode (finish mode p initial).principal.memory pc=some (bind mode p.destination pc spec) :=
  correct mode p specs _ (ready_initial mode p specs backing state size resources) size (initialized_blueprint mode p specs backing)


theorem internal_target_capacity (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs) (offset : Nat) (within : offset<=span mode specs) :
    resolve p.destination (.internal offset)<2^(8*mode.wordBytes) := by
  have fits := (destination_capacity mode p state ready).1
  simp only [resolve]
  rw [size] at fits
  omega

theorem moffs_position (mode : Mode) (p : Params) (specs : List Spec) (state : State mode)
    (ready : Ready mode p state) (size : p.size=span mode specs)
    (blueprint : bytesAt state.principal.memory p.source (compiledBytes mode p specs).length=compiledBytes mode p specs)
    (pc : Nat) (reference : Reference) (member : (pc,Spec.moffs reference) ∈ places mode p.destination specs)
    (fits : resolve p.destination reference<2^(8*mode.wordBytes)) :
    (Protected.wordAt mode (finish mode p state).principal.memory (pc+moffsOperandOffset mode)).toNat=resolve p.destination reference := by
  rw [moffs_payload mode p specs state ready size blueprint pc reference member,Arithmetic.encode_nat_toNat mode _ fits]


/-- Per-packet static signed relocation reach and full natural target capacity.
These are properties of the compiled reference/layout, not future address hits. -/
@[expose] def ReferencesValid (mode : Mode) (p : Params) (specs : List Spec) : Prop :=
  ∀ pc spec, (pc,spec) ∈ places mode p.destination specs ->
    Reachable mode p.destination pc spec ∧ TargetFits mode p.destination spec

/-- Complete constructed copy certificate, including the natural target of
every fetched address-bearing packet under static reference bounds. -/
theorem original_addresses_correct (mode : Mode) (p : Params) (specs : List Spec) (backing : Memory) (state : State mode)
    (size : p.size=span mode specs) (resources : Resources mode p) (references : ReferencesValid mode p specs) :
    let initial := initialState mode p specs backing state
    Trace mode initial (StringProgram.forms mode p.start p.source p.destination p.size) (finish mode p initial) ∧
    ∀ pc spec, (pc,spec) ∈ places mode p.destination specs ->
      Fetch.fetch mode (finish mode p initial).principal.memory pc=some (bind mode p.destination pc spec) ∧
      observed mode p.destination pc spec=target p.destination spec := by
  have copying := original_image_correct mode p specs backing state size resources
  refine ⟨copying.1,fun pc spec member => ⟨copying.2.2 pc spec member,?_ ⟩⟩
  exact observed_target mode p.destination pc spec (references pc spec member).1 (references pc spec member).2

end SmcTuring.Native.TemplateCopy
