module
public import SmcTuring.Native.StringPCWindows
public import SmcTuring.Native.StringPCEncoding
public import SmcTuring.Appendix.Listing8MacroWriteBounds

public section
namespace SmcTuring.Appendix.Listing8MacroPCWindows
open Native StringProgram StringMacroLayout

theorem setup_sequential (mode : Mode) (start source destination : Nat) (form : StringForm.Form mode)
    (member : form ∈ StringSetup.forms mode start source destination) : StringPCSteps.StringSequential mode form := by
  cases mode with
  | x86 =>
    simp [StringSetup.forms,StringSetup.sourceForms,StringInit.forms,StringOperands.exchange] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial
  | x64 =>
    simp [StringSetup.forms,StringSetup.sourceForms,StringInit.forms,StringOperands.exchange] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem restore_sequential (mode : Mode) (destination : Bool) (pc field size : Nat) (form : StringForm.Form mode)
    (member : form ∈ StringRestore.forms mode destination pc field size) : StringPCSteps.StringSequential mode form := by
  simp only [StringRestore.forms,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · trivial
  · unfold StringOperands.subtract
    split <;> trivial

theorem forms_sequential (mode : Mode) (start source destination size : Nat) (form : StringForm.Form mode)
    (member : form ∈ forms mode start source destination size) : StringPCSteps.StringSequential mode form := by
  simp only [forms,List.mem_append] at member
  rcases member with ((setup | body) | sourceRestore) | destinationRestore
  · exact setup_sequential mode start source destination form setup
  · rcases List.mem_map.mp body with ⟨width,member,rfl⟩
    exact by trivial
  · exact restore_sequential mode false _ _ size form sourceRestore
  · exact restore_sequential mode true _ _ size form destinationRestore

theorem subtract_margin (mode : Mode) (pc field size : Nat) :
    3≤StringPCSteps.size mode (StringWrites.liftString mode (StringOperands.subtract mode pc field size)) := by
  rw [StringPCEncoding.string_size]
  unfold StringOperands.subtract
  split <;> cases mode <;> simp [StringForm.encode,wordPrefix,LittleEndian.word_encode_length]

theorem guard (mode : Mode) (p : Params) :
    StringPCWindows.Guard mode ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) := by
  let pc:=StringMacroLayout.destinationTail mode p
  let exchange:=StringOperands.exchange mode true pc (StringCodec.destinationField mode p.start)
  let last:=StringOperands.subtract mode (pc+StringCodec.exchangeSize mode) (StringCodec.destinationField mode p.start) p.size
  let before:=(StringSetup.forms mode p.start p.source p.destination++StringMoves.forms mode (StringPlan.widths mode p.size)++
    StringRestore.forms mode false (StringCodec.bodyEnd mode p.start p.size) (StringCodec.sourceField mode p.start) p.size).map (StringWrites.liftString mode)++
      [StringWrites.liftString mode exchange]
  have guarded:=StringPCWindows.guard_last mode before (StringWrites.liftString mode last)
    (subtract_margin mode _ _ _)
  simpa only [before,exchange,last,pc,StringProgram.forms,StringRestore.forms,StringMacroLayout.destinationTail,
    StringMacroLayout.sourceTail,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append] using guarded

/-- The actual whole TRANSFERDATA PC windows follow original code placement,
initial ready entry and the preserved encoder's exact byte footprint. -/
theorem contained (mode : Mode) (start stop : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Listing8MacroWriteBounds.Placement mode start stop p)
    (capacity : stop<2^(8*mode.wordBytes)) :
    StringPCWindows.Run mode ⟨start,stop⟩
      ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state := by
  apply StringPCWindows.sequential mode ⟨start,stop⟩ _ state p.start
  · intro form member
    rcases List.mem_map.mp member with ⟨original,inside,rfl⟩
    exact forms_sequential mode p.start p.source p.destination p.size original inside
  · exact ready.entry
  · exact guard mode p
  · exact placed.code.1
  · rw [StringPCEncoding.program_total mode p.start p.source p.destination p.size ready.sizeFits]
    have beginning : p.start≤StringCodec.endpoint mode p.start p.size := by
      unfold StringCodec.endpoint StringCodec.bodyEnd StringCodec.bodyStart
      omega
    have ending:=placed.code.2
    change StringCodec.endpoint mode p.start p.size≤stop at ending
    change p.start+(StringCodec.endpoint mode p.start p.size-p.start)≤stop
    omega
  · exact capacity

end SmcTuring.Appendix.Listing8MacroPCWindows
