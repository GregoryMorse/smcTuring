module
public import SmcTuring.Native.StringMacroImage

public section
namespace SmcTuring.Native.StringMacroEffects
open StringExecution StringMacroLayout ByteMemory

@[expose] def setup (mode : Mode) (p : Params) (state : State mode) : State mode :=
  run mode (StringSetup.forms mode p.start p.source p.destination) state
@[expose] def copied (mode : Mode) (p : Params) (state : State mode) : State mode :=
  run mode (StringMoves.forms mode (StringPlan.widths mode p.size)) (setup mode p state)
@[expose] def sourceRestored (mode : Mode) (p : Params) (state : State mode) : State mode :=
  run mode (StringRestore.forms mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size) (copied mode p state)
@[expose] def finish (mode : Mode) (p : Params) (state : State mode) : State mode :=
  run mode (StringRestore.forms mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size) (sourceRestored mode p state)

theorem state_eq (mode : Mode) (a b : State mode)
    (pc : a.principal.pc=b.principal.pc) (ax : a.principal.accumulator=b.principal.accumulator)
    (sp : a.principal.stack=b.principal.stack) (cf : a.principal.carry=b.principal.carry)
    (mem : a.principal.memory=b.principal.memory) (si : a.sourceIndex=b.sourceIndex)
    (di : a.destinationIndex=b.destinationIndex) (df : a.backwards=b.backwards) : a=b := by
  cases a with | mk ap asi adi adf =>
    cases b with | mk bp bsi bdi bdf =>
      cases ap; cases bp
      simp_all

theorem setup_effect (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    setup mode p state = {state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (bodyStart mode p)
        accumulator := StringInit.accumulator mode p.destination state
        memory := StringFields.prepared mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex}
      sourceIndex := Arithmetic.encodeNat mode p.source
      destinationIndex := Arithmetic.encodeNat mode p.destination} := StringMacroImage.prefix_effect mode p state ready

theorem copied_effect (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    copied mode p state = {state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (sourceTail mode p)
        accumulator := StringInit.accumulator mode p.destination state
        memory := StringFields.copied mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex}
      sourceIndex := Arithmetic.encodeNat mode p.source+Arithmetic.encodeNat mode p.size
      destinationIndex := Arithmetic.encodeNat mode p.destination+Arithmetic.encodeNat mode p.size} := by
  have forward : (setup mode p state).backwards=false := by rw [setup_effect mode p state ready]; exact ready.forward
  have si : (setup mode p state).sourceIndex.toNat=p.source := by
    rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ (source_capacity mode p state ready).2.2]
  have di : (setup mode p state).destinationIndex.toNat=p.destination := by
    rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ (destination_capacity mode p state ready).2.2]
  have total := StringPlan.total mode p.size
  change (StringPlan.widths mode p.size).sum=p.size at total
  have sf : (setup mode p state).sourceIndex.toNat+(StringPlan.widths mode p.size).sum < 2^(8*mode.wordBytes) := by
    rw [si,total]; exact (source_capacity mode p state ready).1
  have dfit : (setup mode p state).destinationIndex.toNat+(StringPlan.widths mode p.size).sum < 2^(8*mode.wordBytes) := by
    rw [di,total]; exact (destination_capacity mode p state ready).1
  have apart : StringCopy.Apart (setup mode p state).sourceIndex.toNat (setup mode p state).destinationIndex.toNat (StringPlan.widths mode p.size).sum := by
    rw [si,di,total]; exact ready.buffers
  unfold copied
  apply state_eq
  · rw [StringMoves.run_pc,setup_effect mode p state ready]
    change Arithmetic.encodeNat mode (bodyStart mode p)+Arithmetic.encodeNat mode (body mode p).length = _
    rw [Arithmetic.encodeNat,Arithmetic.encodeNat,BitVec.ofNat_add_ofNat,(coordinates mode p).2.1]
    rfl
  · rw [StringMoves.run_accumulator,setup_effect mode p state ready]
  · rw [StringMoves.run_stack,setup_effect mode p state ready]
  · rw [StringMoves.run_carry,setup_effect mode p state ready]
  · rw [StringMoves.effect mode _ _ forward sf dfit apart,si,di,total,setup_effect mode p state ready]
    rfl
  · rw [StringMoves.run_source mode _ _ forward,total,setup_effect mode p state ready]
  · rw [StringMoves.run_destination mode _ _ forward,total,setup_effect mode p state ready]
  · rw [run_direction,setup_effect mode p state ready]

theorem copied_source_load (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Execution.load mode (copied mode p state).principal.memory (Arithmetic.encodeNat mode (StringCodec.sourceField mode p.start)) = state.sourceIndex := by
  have sep := fields_separate mode p state ready
  have fit := StringSetup.source_field_fits mode p.start (prefix_capacity mode p state ready)
  rw [copied_effect mode p state ready]
  unfold StringFields.copied
  unfold Execution.load
  rw [Arithmetic.encode_nat_toNat mode _ fit]
  rw [bytes_at_frame _ _ _ _ _ (by simpa only [bytes_at_length,layout] using sep.2.2.2.2.1)]
  have saved : Execution.load mode (StringFields.prepared mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex)
      (Arithmetic.encodeNat mode (StringCodec.sourceField mode p.start)) = state.sourceIndex := by
    unfold StringFields.prepared layout
    rw [StringWindow.load_frame mode _ (StringCodec.destinationField mode p.start) (StringCodec.sourceField mode p.start) _ fit (by simpa only [layout] using StringFields.cursor_outside mode _ sep),StringRestore.loaded_exchange mode _ _ _ fit]
  unfold Execution.load at saved
  rw [Arithmetic.encode_nat_toNat mode _ fit] at saved
  exact saved

theorem copied_destination_load (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Execution.load mode (copied mode p state).principal.memory (Arithmetic.encodeNat mode (StringCodec.destinationField mode p.start)) = state.destinationIndex := by
  have sep := fields_separate mode p state ready
  have fit := StringSetup.destination_field_fits mode p.start (prefix_capacity mode p state ready)
  rw [copied_effect mode p state ready]
  unfold StringFields.copied Execution.load
  rw [Arithmetic.encode_nat_toNat mode _ fit]
  rw [bytes_at_frame _ _ _ _ _ (by simpa only [bytes_at_length,layout] using sep.2.2.2.2.2)]
  have saved : Execution.load mode (StringFields.prepared mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex)
      (Arithmetic.encodeNat mode (StringCodec.destinationField mode p.start)) = state.destinationIndex := by
    unfold StringFields.prepared layout
    exact StringRestore.loaded_exchange mode _ _ _ fit
  unfold Execution.load at saved
  rw [Arithmetic.encode_nat_toNat mode _ fit] at saved
  exact saved

theorem source_effect (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    sourceRestored mode p state = {copied mode p state with
      principal := {(copied mode p state).principal with
        pc := Arithmetic.encodeNat mode (destinationTail mode p)
        carry := false
        memory := putWord mode (copied mode p state).principal.memory (StringCodec.sourceField mode p.start) (Arithmetic.encodeNat mode p.source)}
      sourceIndex := state.sourceIndex} := by
  have ranges := tail_ranges mode p ready.sizeFits
  unfold sourceRestored
  rw [StringRestore.source_effect mode _ _ _ p.source _
    (by rw [copied_effect mode p state ready]) (fun _ => ranges.1) (fun _ => ranges.2.1)
    (StringSetup.source_field_fits mode p.start (prefix_capacity mode p state ready)) ready.sizeFits
    (source_capacity mode p state ready).1 (by rw [copied_effect mode p state ready]),copied_source_load mode p state ready]
  rfl

theorem source_destination_load (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    Execution.load mode (sourceRestored mode p state).principal.memory (Arithmetic.encodeNat mode (StringCodec.destinationField mode p.start)) = state.destinationIndex := by
  rw [source_effect mode p state ready]
  have fit := StringSetup.destination_field_fits mode p.start (prefix_capacity mode p state ready)
  rw [StringWindow.load_frame mode _ _ _ _ fit]
  · exact copied_destination_load mode p state ready
  · intro index
    have pos := field_coordinates mode p
    unfold Inside
    omega

theorem finish_effect (mode : Mode) (p : Params) (state : State mode) (ready : Ready mode p state) :
    finish mode p state = {state with
      principal := {state.principal with
        pc := Arithmetic.encodeNat mode (endpoint mode p)
        accumulator := StringInit.accumulator mode p.destination state
        carry := false
        memory := putBytes state.principal.memory p.destination (bytesAt state.principal.memory p.source p.size)}} := by
  have ranges := tail_ranges mode p ready.sizeFits
  have endPC : StringRestore.endpoint mode (destinationTail mode p) p.size = endpoint mode p := by
    simp only [StringRestore.endpoint,destinationTail,sourceTail,endpoint,StringCodec.endpoint]; omega
  have restoredMemory : putWord mode (putWord mode (StringFields.copied mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex)
      (StringCodec.sourceField mode p.start) (Arithmetic.encodeNat mode p.source))
      (StringCodec.destinationField mode p.start) (Arithmetic.encodeNat mode p.destination) =
      putBytes state.principal.memory p.destination (bytesAt state.principal.memory p.source p.size) := by
    have words := StringMacroImage.initial_words mode p state ready
    rw [←words.1,←words.2]
    exact StringFields.effect mode (layout mode p) state.principal.memory state.sourceIndex state.destinationIndex (fields_separate mode p state ready)
  unfold finish
  rw [StringRestore.destination_effect mode _ _ _ p.destination _
    (by rw [source_effect mode p state ready]) (fun _ => ranges.2.2.1) (fun _ => by rw [endPC]; exact ranges.2.2.2)
    (StringSetup.destination_field_fits mode p.start (prefix_capacity mode p state ready)) ready.sizeFits
    (destination_capacity mode p state ready).1 (by rw [source_effect mode p state ready,copied_effect mode p state ready]),
    source_destination_load mode p state ready,source_effect mode p state ready,copied_effect mode p state ready,endPC]
  rw [restoredMemory]

theorem program_run (mode : Mode) (p : Params) (state : State mode) :
    run mode (StringProgram.forms mode p.start p.source p.destination p.size) state = finish mode p state := by
  simp only [StringProgram.forms,run_append]
  rfl

end SmcTuring.Native.StringMacroEffects
