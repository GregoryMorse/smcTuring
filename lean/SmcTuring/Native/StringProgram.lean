module
public import SmcTuring.Native.StringSetupTrace
public import SmcTuring.Native.StringRestore

public section
namespace SmcTuring.Native.StringProgram

@[expose] def forms (mode : Mode) (start source destination size : Nat) : List (StringForm.Form mode) :=
  StringSetup.forms mode start source destination++StringMoves.forms mode (StringPlan.widths mode size)++
  StringRestore.forms mode false (StringCodec.bodyEnd mode start size) (StringCodec.sourceField mode start) size++
  StringRestore.forms mode true (StringRestore.endpoint mode (StringCodec.bodyEnd mode start size) size) (StringCodec.destinationField mode start) size

theorem body_encoding (mode : Mode) (widths : List Nat) :
    ((StringMoves.forms mode widths).map (StringForm.encode mode)).flatten = StringMoves.code widths := by
  simp [StringMoves.forms,StringMoves.code,List.map_map,Function.comp_def,StringForm.encode]

theorem prefix_extent (mode : Mode) (start source destination : Nat) :
    (StringSetupTrace.bytes mode start source destination).length = StringCodec.bodyStart mode start-start := by
  simp only [StringSetupTrace.bytes,List.length_append,StringInit.bytes,StringCodec.initial_length,StringCodec.exchange_length]
  unfold StringCodec.bodyStart
  omega

/-- These are the exact printed complete macro bytes, using the actual
initializer/index/MOVS/SUB forms rather than a separately named effect oracle. -/
theorem encoding (mode : Mode) (start source destination size : Nat) (fits : size < 2^31) :
    ((forms mode start source destination size).map (StringForm.encode mode)).flatten = StringCodec.bytes mode start source destination size := by
  simp only [forms,List.map_append,List.flatten_append,StringSetupTrace.forms_encoding,body_encoding,
    StringRestore.forms_encoding mode _ _ _ _ fits]
  simp only [StringSetupTrace.bytes,StringInit.bytes,StringRestore.bytes,StringRestore.endpoint,StringCodec.bytes]
  rw [show StringCodec.bodyEnd mode start size+StringCodec.exchangeSize mode+StringCodec.subSize mode size+StringCodec.exchangeSize mode =
    StringCodec.bodyEnd mode start size+2*StringCodec.exchangeSize mode+StringCodec.subSize mode size by omega]
  simp only [List.append_assoc]
  rfl

theorem code_extent (mode : Mode) (start source destination size : Nat) (fits : size < 2^31) :
    (((forms mode start source destination size).map (StringForm.encode mode)).flatten).length = StringCodec.endpoint mode start size-start := by
  rw [encoding mode start source destination size fits]
  exact StringCodec.whole_length mode start source destination size

theorem instruction_count (mode : Mode) (start source destination size : Nat) :
    (forms mode start source destination size).length = (StringPlan.widths mode size).length+(if mode = .x86 then 8 else 14) := by
  cases mode <;> simp [forms,StringSetup.forms,StringSetup.sourceForms,StringInit.forms,StringRestore.forms,StringMoves.forms]

theorem setup_legal (mode : Mode) (start source destination : Nat) (form : StringForm.Form mode)
    (member : form ∈ StringSetup.forms mode start source destination) : StringForm.Legal mode form := by
  cases mode with
  | x86 =>
    simp [StringSetup.forms,StringSetup.sourceForms,StringInit.forms,StringOperands.exchange] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial
  | x64 =>
    simp [StringSetup.forms,StringSetup.sourceForms,StringInit.forms,StringOperands.exchange] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem restore_legal (mode : Mode) (destination : Bool) (pc field size : Nat) (form : StringForm.Form mode)
    (member : form ∈ StringRestore.forms mode destination pc field size) : StringForm.Legal mode form := by
  simp only [StringRestore.forms,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · trivial
  · unfold StringOperands.subtract
    split <;> trivial

theorem legal (mode : Mode) (start source destination size : Nat) (form : StringForm.Form mode)
    (member : form ∈ forms mode start source destination size) : StringForm.Legal mode form := by
  simp only [forms,List.mem_append] at member
  rcases member with ((setup | body) | sourceRestore) | destinationRestore
  · exact setup_legal mode start source destination form setup
  · rcases List.mem_map.mp body with ⟨width,member,rfl⟩
    exact StringPlan.legal mode size width member
  · exact restore_legal mode false _ _ size form sourceRestore
  · exact restore_legal mode true _ _ size form destinationRestore

end SmcTuring.Native.StringProgram
