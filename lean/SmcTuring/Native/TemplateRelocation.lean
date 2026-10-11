module
public import SmcTuring.Native.StringMacroTrace
public import SmcTuring.Native.ConversionOperands

public section
namespace SmcTuring.Native.TemplateRelocation
open ByteMemory

/-- Internal references move with the template. External references retain
their declared address. Every absolute/MOFFS and relative field is bound at
the destination before the blueprint is copied, as allowed by the paper. -/
inductive Reference where
  | internal (offset : Nat)
  | external (address : Nat)
  deriving DecidableEq, Repr

@[expose] def resolve (base : Nat) : Reference -> Nat
  | .internal offset => base+offset
  | .external address => address

inductive Spec where
  | moffs (reference : Reference)
  | memory (operation : MemoryOp) (reference : Reference)
  | call (reference : Reference)
  | exchangeIndirect
  deriving DecidableEq, Repr

@[expose] def bind (mode : Mode) (base pc : Nat) : Spec -> Form mode
  | .moffs reference => .moffs (Arithmetic.encodeNat mode (resolve base reference))
  | .memory operation reference => .memory operation (Relocation.instructionDisp mode operation pc (resolve base reference))
  | .call reference => .callRelative (Relocation.relative32 (pc+5) (resolve base reference))
  | .exchangeIndirect => .exchangeIndirect

@[expose] def length (mode : Mode) (spec : Spec) : Nat := instructionLength mode (bind mode 0 0 spec)
@[expose] def span (mode : Mode) (specs : List Spec) : Nat := (specs.map (length mode)).sum

@[expose] def places (mode : Mode) : Nat -> List Spec -> List (Nat × Spec)
  | _, [] => []
  | pc, spec::rest => (pc,spec)::places mode (pc+length mode spec) rest
@[expose] def forms (mode : Mode) (base : Nat) : Nat -> List Spec -> List (Form mode)
  | _, [] => []
  | pc, spec::rest => bind mode base pc spec::forms mode base (pc+length mode spec) rest
@[expose] def bytes (mode : Mode) (base pc : Nat) (specs : List Spec) : List LittleEndian.Byte :=
  ((forms mode base pc specs).map (encode mode)).flatten

@[expose] def Reachable (mode : Mode) (base pc : Nat) : Spec -> Prop
  | .memory operation reference => mode=.x64 -> Relocation.SignedDelta (pc+length mode (.memory operation reference)) (resolve base reference)
  | .call reference => Relocation.SignedDelta (pc+5) (resolve base reference)
  | _ => True

theorem bound_length (mode : Mode) (base pc : Nat) (spec : Spec) :
    instructionLength mode (bind mode base pc spec)=length mode spec := by
  cases spec <;> rfl

theorem encoded_length (mode : Mode) (base pc : Nat) (spec : Spec) :
    (encode mode (bind mode base pc spec)).length=length mode spec := by
  rw [instruction_length,bound_length]

theorem length_positive (mode : Mode) (spec : Spec) : 0<length mode spec := by
  cases spec with
  | moffs ref => cases mode <;> simp [length,bind,instructionLength,wordPrefix,Mode.wordBytes]
  | memory op ref => cases mode <;> cases op <;> simp [length,bind,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix]
  | call ref => simp [length,bind,instructionLength]
  | exchangeIndirect => cases mode <;> decide

theorem length_bound (mode : Mode) (spec : Spec) : length mode spec<=15 :=
  instruction_length_bound mode (bind mode 0 0 spec)

theorem bytes_cons (mode : Mode) (base pc : Nat) (spec : Spec) (rest : List Spec) :
    bytes mode base pc (spec::rest) = encode mode (bind mode base pc spec)++bytes mode base (pc+length mode spec) rest := rfl

theorem bytes_length (mode : Mode) (base pc : Nat) (specs : List Spec) :
    (bytes mode base pc specs).length=span mode specs := by
  induction specs generalizing pc with
  | nil => rfl
  | cons spec rest ih => simp only [bytes_cons,List.length_append,encoded_length,ih,span,List.map_cons,List.sum_cons]

theorem instruction_count (mode : Mode) (base pc : Nat) (specs : List Spec) :
    (forms mode base pc specs).length=specs.length := by
  induction specs generalizing pc with
  | nil => rfl
  | cons spec rest ih => simp only [forms,List.length_cons,ih]

theorem places_lower (mode : Mode) (start : Nat) (specs : List Spec) (pc : Nat) (spec : Spec)
    (member : (pc,spec) ∈ places mode start specs) : start<=pc := by
  induction specs generalizing start with
  | nil => cases member
  | cons head rest ih =>
    simp only [places,List.mem_cons] at member
    rcases member with same | tail
    · cases same; omega
    · have bound := ih _ tail; omega

theorem places_upper (mode : Mode) (start : Nat) (specs : List Spec) (pc : Nat) (spec : Spec)
    (member : (pc,spec) ∈ places mode start specs) : pc+length mode spec<=start+span mode specs := by
  induction specs generalizing start with
  | nil => cases member
  | cons head rest ih =>
    simp only [places,List.mem_cons] at member
    simp only [span,List.map_cons,List.sum_cons]
    rcases member with same | tail
    · cases same; omega
    · have bound := ih _ tail; simp only [span] at bound; omega

theorem bound_member (mode : Mode) (base start : Nat) (specs : List Spec) (pc : Nat) (spec : Spec)
    (member : (pc,spec) ∈ places mode start specs) : bind mode base pc spec ∈ forms mode base start specs := by
  induction specs generalizing start with
  | nil => cases member
  | cons head rest ih =>
    simp only [places,List.mem_cons] at member
    simp only [forms,List.mem_cons]
    rcases member with same | tail
    · cases same; exact Or.inl rfl
    · exact Or.inr (ih _ tail)

theorem whole_packet (mode : Mode) (base start : Nat) (specs : List Spec) (memory : Memory)
    (original : bytesAt memory start (bytes mode base start specs).length=bytes mode base start specs)
    (pc : Nat) (spec : Spec) (member : (pc,spec) ∈ places mode start specs) :
    bytesAt memory pc (length mode spec)=encode mode (bind mode base pc spec) := by
  induction specs generalizing start with
  | nil => cases member
  | cons head rest ih =>
    simp only [places,List.mem_cons] at member
    rw [bytes_cons] at original
    rcases member with same | tail
    · cases same
      have packet := StringWindow.packet_window memory pc [] (encode mode (bind mode base pc spec)) (bytes mode base (pc+length mode spec) rest)
        (by simpa only [List.nil_append] using original)
      simpa only [List.length_nil,Nat.add_zero,encoded_length] using packet
    · apply ih _ _ tail
      have packet := StringWindow.packet_window memory start (encode mode (bind mode base start head)) (bytes mode base (start+length mode head) rest) []
        (by simpa only [List.append_nil] using original)
      simpa only [encoded_length] using packet

theorem whole_fetch (mode : Mode) (base start : Nat) (specs : List Spec) (memory : Memory)
    (original : bytesAt memory start (bytes mode base start specs).length=bytes mode base start specs)
    (pc : Nat) (spec : Spec) (member : (pc,spec) ∈ places mode start specs) :
    Fetch.fetch mode memory pc=some (bind mode base pc spec) := by
  apply Fetch.fetch_current_encoding
  rw [encoded_length]
  exact whole_packet mode base start specs memory original pc spec member

theorem moffs_address (mode : Mode) (base pc : Nat) (reference : Reference) :
    bind mode base pc (.moffs reference)=.moffs (Arithmetic.encodeNat mode (resolve base reference)) := rfl

theorem moffs_field (mode : Mode) (base pc : Nat) (reference : Reference) :
    (encode mode (bind mode base pc (.moffs reference))).drop (moffsOperandOffset mode) =
      LittleEndian.wordEncode mode.wordBytes (Arithmetic.encodeNat mode (resolve base reference)) :=
  moffs_operand_bytes mode _

theorem memory_field (mode : Mode) (base pc : Nat) (op : MemoryOp) (reference : Reference) :
    ((encode mode (bind mode base pc (.memory op reference))).drop ((op.prefix mode).length+2)).take 4 =
      LittleEndian.wordEncode 4 (Relocation.instructionDisp mode op pc (resolve base reference)) :=
  memory_displacement_bytes mode _ _

theorem memory_target (mode : Mode) (base pc : Nat) (op : MemoryOp) (reference : Reference) (state : Execution.State mode)
    (location : state.pc=Arithmetic.encodeNat mode pc) (reachable : Reachable mode base pc (.memory op reference)) :
    Execution.memoryAddress mode (Execution.nextPC mode (bind mode base pc (.memory op reference)) state)
      (Relocation.instructionDisp mode op pc (resolve base reference)) = Arithmetic.encodeNat mode (resolve base reference) := by
  exact Relocation.instruction_memory_hits mode op pc _ state location reachable

theorem call_target (mode : Mode) (base pc : Nat) (reference : Reference) (state : Execution.State mode)
    (location : state.pc=Arithmetic.encodeNat mode pc) (reachable : Reachable mode base pc (.call reference)) :
    (Execution.execute mode (bind mode base pc (.call reference)) state).pc = Arithmetic.encodeNat mode (resolve base reference) :=
  Relocation.relative_call_pc mode pc _ state location reachable

theorem internal_rip (source destination offset : Nat) (op : MemoryOp) (targetOffset : Nat) :
    bind .x64 source (source+offset) (.memory op (.internal targetOffset)) =
      bind .x64 destination (destination+offset) (.memory op (.internal targetOffset)) := by
  unfold bind Relocation.instructionDisp resolve
  apply congrArg (Form.memory op)
  simpa only [Nat.add_assoc] using StringTemplate.rip_internal source destination (offset+instructionLength .x64 (.memory op 0)) targetOffset

theorem internal_call (mode : Mode) (source destination offset targetOffset : Nat) :
    bind mode source (source+offset) (.call (.internal targetOffset)) =
      bind mode destination (destination+offset) (.call (.internal targetOffset)) := by
  unfold bind resolve
  apply congrArg Form.callRelative
  simpa only [Nat.add_assoc] using StringTemplate.relative_internal source destination (offset+5) targetOffset

theorem external_moffs (mode : Mode) (source destination oldPC newPC address : Nat) :
    bind mode source oldPC (.moffs (.external address))=bind mode destination newPC (.moffs (.external address)) := rfl

theorem external_absolute (source destination oldPC newPC address : Nat) (op : MemoryOp) :
    bind .x86 source oldPC (.memory op (.external address))=bind .x86 destination newPC (.memory op (.external address)) := rfl


theorem moffs_position (mode : Mode) (base : Nat) (reference : Reference)
    (fits : resolve base reference<2^(8*mode.wordBytes)) :
    (Arithmetic.encodeNat mode (resolve base reference)).toNat=resolve base reference :=
  Arithmetic.encode_nat_toNat mode _ fits

theorem memory_position (mode : Mode) (base pc : Nat) (op : MemoryOp) (reference : Reference) (state : Execution.State mode)
    (location : state.pc=Arithmetic.encodeNat mode pc) (reachable : Reachable mode base pc (.memory op reference))
    (fits : resolve base reference<2^(8*mode.wordBytes)) :
    (Execution.memoryAddress mode (Execution.nextPC mode (bind mode base pc (.memory op reference)) state)
      (Relocation.instructionDisp mode op pc (resolve base reference))).toNat=resolve base reference := by
  rw [memory_target mode base pc op reference state location reachable,Arithmetic.encode_nat_toNat mode _ fits]

theorem call_position (mode : Mode) (base pc : Nat) (reference : Reference) (state : Execution.State mode)
    (location : state.pc=Arithmetic.encodeNat mode pc) (reachable : Reachable mode base pc (.call reference))
    (fits : resolve base reference<2^(8*mode.wordBytes)) :
    (Execution.execute mode (bind mode base pc (.call reference)) state).pc.toNat=resolve base reference := by
  rw [call_target mode base pc reference state location reachable,Arithmetic.encode_nat_toNat mode _ fits]


@[expose] def target (base : Nat) : Spec -> Option Nat
  | .moffs reference | .memory _ reference | .call reference => some (resolve base reference)
  | .exchangeIndirect => none

@[expose] def TargetFits (mode : Mode) (base : Nat) : Spec -> Prop
  | .moffs reference | .memory _ reference | .call reference => resolve base reference<2^(8*mode.wordBytes)
  | .exchangeIndirect => True

/-- Address observed from the compiled operand and its actual complete next PC.
This is not a promise about executing arbitrary copied programs. -/
@[expose] def observed (mode : Mode) (base pc : Nat) : Spec -> Option Nat
  | .moffs reference => some (Arithmetic.encodeNat mode (resolve base reference)).toNat
  | .memory op reference => some (Execution.memoryAddress mode (Arithmetic.encodeNat mode (pc+length mode (.memory op reference)))
      (Relocation.instructionDisp mode op pc (resolve base reference))).toNat
  | .call reference => some (Arithmetic.encodeNat mode (pc+5)+Execution.displacementWord mode
      (Relocation.relative32 (pc+5) (resolve base reference))).toNat
  | .exchangeIndirect => none

theorem observed_target (mode : Mode) (base pc : Nat) (spec : Spec)
    (reachable : Reachable mode base pc spec) (fits : TargetFits mode base spec) :
    observed mode base pc spec=target base spec := by
  cases spec with
  | moffs reference =>
    simp only [observed,target,Arithmetic.encode_nat_toNat mode _ fits]
  | memory op reference =>
    simp only [observed,target]
    have address := Relocation.memory_hits mode (pc+length mode (.memory op reference)) (resolve base reference) reachable
    change Execution.memoryAddress mode (Arithmetic.encodeNat mode (pc+length mode (.memory op reference)))
      (Relocation.instructionDisp mode op pc (resolve base reference))=Arithmetic.encodeNat mode (resolve base reference) at address
    rw [address,Arithmetic.encode_nat_toNat mode _ fits]
  | call reference =>
    simp only [observed,target]
    rw [Relocation.add_relative32 mode _ _ reachable,Arithmetic.encode_nat_toNat mode _ fits]
  | exchangeIndirect => rfl

end SmcTuring.Native.TemplateRelocation
