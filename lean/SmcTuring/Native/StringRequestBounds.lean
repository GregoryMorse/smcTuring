module
public import SmcTuring.Native.StringMixedRequests

public section
namespace SmcTuring.Native.StringRequestBounds
open LittleEndian StringFetchRequests

theorem string_classified (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringForm.Form mode)
    (fetched : StringForm.fetch mode memory pc=some form) :
    StringForm.lengthOfBytes mode (ByteMemory.bytesAt memory pc 3)=some (StringForm.encode mode form).length := by
  unfold StringForm.fetch at fetched
  rcases Option.bind_eq_some_iff.mp fetched with ⟨count,classified,parsed⟩
  have image:=(StringDecodeImage.decode mode (ByteMemory.bytesAt memory pc count) form parsed).1
  have size:=congrArg List.length image
  simp only [ByteMemory.bytes_at_length] at size
  rw [←size]
  exact classified

theorem string_fetched (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringForm.Form mode)
    (fetched : StringForm.fetch mode memory pc=some form) :
    ∀ count∈string mode memory pc,count≤max 3 (StringForm.encode mode form).length := by
  rw [string,string_classified mode memory pc form fetched]
  intro count member
  simp only [selected,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

theorem packet_string (mode : Mode) (packet : Packet mode) (memory : ByteMemory.Memory) (pc : Nat)
    (current : ByteMemory.bytesAt memory pc (bytes mode packet).length=bytes mode packet) :
    ∀ count∈string mode memory pc,count≤(bytes mode packet).length := by
  intro count member
  simp only [string,List.mem_cons] at member
  rcases member with rfl | member
  · exact packet_minimum mode packet
  · cases classified : StringForm.lengthOfBytes mode (ByteMemory.bytesAt memory pc 3) with
    | none => simp only [classified,selected,List.not_mem_nil] at member
    | some value =>
      simp only [classified,selected,List.mem_cons,List.not_mem_nil,or_false] at member
      subst count
      exact StringMixedRequests.string_count mode packet memory pc value current classified

theorem packet_dword (mode : Mode) (packet : Packet mode) (memory : ByteMemory.Memory) (pc : Nat)
    (current : ByteMemory.bytesAt memory pc (bytes mode packet).length=bytes mode packet)
    (last : 6≤(bytes mode packet).length) :
    ∀ count∈dword mode memory pc,count≤(bytes mode packet).length := by
  cases initial : StringForm.fetch mode memory pc with
  | some value =>
    simp only [dword,initial,List.append_nil]
    exact packet_string mode packet memory pc current
  | none =>
    cases next : MixedDword.fetch mode memory pc with
    | some value =>
      simp only [dword,initial,next,List.append_nil]
      intro count member
      rcases List.mem_append.mp member with leading | trailing
      · exact packet_string mode packet memory pc current count leading
      · exact StringMixedRequests.mixed_counts mode packet memory pc current count trailing
    | none =>
      simp only [dword,initial,next]
      intro count member
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with leading | middle | rfl
      · exact packet_string mode packet memory pc current count leading
      · exact StringMixedRequests.mixed_counts mode packet memory pc current count middle
      · exact last

theorem packet_control (mode : Mode) (packet : Packet mode) (memory : ByteMemory.Memory) (pc : Nat)
    (current : ByteMemory.bytesAt memory pc (bytes mode packet).length=bytes mode packet)
    (xorFits : 6≤(bytes mode packet).length) (negFits : WordNegation.length mode≤(bytes mode packet).length) :
    ∀ count∈control mode memory pc,count≤(bytes mode packet).length := by
  cases initial : StringDword.fetch mode memory pc with
  | some value =>
    simp only [StringFetchRequests.control,initial,List.append_nil]
    exact packet_dword mode packet memory pc current xorFits
  | none =>
    simp only [StringFetchRequests.control,initial]
    intro count member
    rcases List.mem_append.mp member with leading | trailing
    · exact packet_dword mode packet memory pc current xorFits count leading
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at trailing
      subst count
      exact negFits

theorem dword_fetched (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringDword.Form mode)
    (fetched : StringDword.fetch mode memory pc=some form) :
    ∀ count∈dword mode memory pc,count≤max 3 (StringPCSteps.dwordSize mode form) := by
  unfold StringDword.fetch at fetched
  cases initial : StringForm.fetch mode memory pc with
  | some value =>
    simp only [initial] at fetched
    rw [←Option.some.inj fetched]
    simp only [dword,initial,List.append_nil,StringPCSteps.dwordSize,StringStackImage.string_size]
    exact string_fetched mode memory pc value initial
  | none =>
    simp only [initial] at fetched
    cases next : MixedDword.fetch mode memory pc with
    | some value =>
      simp only [next] at fetched
      rw [←Option.some.inj fetched]
      simp only [dword,initial,next,List.append_nil,StringPCSteps.dwordSize,←MixedDword.encode_length]
      have image:=StringStackImage.mixed_fetch mode memory pc value next
      intro count member
      apply Nat.le_trans _ (Nat.le_max_right _ _)
      rcases List.mem_append.mp member with leading | trailing
      · exact packet_string mode (.mixed value) memory pc image count leading
      · exact StringMixedRequests.mixed_counts mode (.mixed value) memory pc image count trailing
    | none =>
      simp only [next] at fetched
      rcases Option.map_eq_some_iff.mp fetched with ⟨d,parsed,same⟩
      rw [←same]
      have image:=DwordXor.decode_image mode (ByteMemory.bytesAt memory pc 6) d parsed
      change ∀ count∈dword mode memory pc,count≤6
      exact packet_dword mode (.xor d) memory pc image (by simp [bytes,DwordXor.encode])

theorem control_fetched (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringControl.Form mode)
    (fetched : StringControl.fetch mode memory pc=some form) :
    ∀ count∈control mode memory pc,count≤max 3 (StringPCSteps.controlSize mode form) := by
  unfold StringControl.fetch at fetched
  cases initial : StringDword.fetch mode memory pc with
  | some value =>
    simp only [initial] at fetched
    rw [←Option.some.inj fetched]
    simp only [StringFetchRequests.control,initial,List.append_nil,StringPCSteps.controlSize]
    exact dword_fetched mode memory pc value initial
  | none =>
    simp only [initial] at fetched
    rcases Option.map_eq_some_iff.mp fetched with ⟨d,parsed,same⟩
    rw [←same]
    have image:=WordDecodeImage.negation_fetch mode memory pc d parsed
    have bound:=packet_control mode (.negation d) memory pc image
      (by simp [bytes,WordNegation.encode_length,WordNegation.length])
      (by simp [bytes,WordNegation.encode_length])
    intro count member
    have within:=bound count member
    simp only [bytes,WordNegation.encode_length] at within
    exact Nat.le_trans within (Nat.le_max_right _ _)

/-- Bound every actually requested classifier/packet window from successful
current decoding. Failed fallbacks are included; no packet image is a premise. -/
theorem fetched (mode : Mode) (memory : ByteMemory.Memory) (pc : Nat) (form : StringStack.Form mode)
    (fetched : StringStack.fetch mode memory pc=some form) :
    ∀ count∈requests mode memory pc,count≤max 3 (StringPCSteps.size mode form) := by
  unfold StringStack.fetch at fetched
  cases initial : StringControl.fetch mode memory pc with
  | some value =>
    simp only [initial] at fetched
    rw [←Option.some.inj fetched]
    simp only [requests,initial,List.append_nil,StringPCSteps.size]
    exact control_fetched mode memory pc value initial
  | none =>
    simp only [initial] at fetched
    rcases Option.map_eq_some_iff.mp fetched with ⟨pair,parsed,same⟩
    rw [←same]
    have image:=WordDecodeImage.addition_fetch mode memory pc pair parsed
    have bound:=packet_control mode (.addition pair.1 pair.2) memory pc image
      (by simp [bytes,WordAddImmediate.encode_length,WordAddImmediate.length])
      (by simp [bytes,WordAddImmediate.encode_length,WordAddImmediate.length,WordNegation.length])
    simp only [requests,initial]
    intro count member
    rcases List.mem_append.mp member with leading | trailing
    · have within:=bound count leading
      simp only [bytes,WordAddImmediate.encode_length] at within
      exact Nat.le_trans within (Nat.le_max_right _ _)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at trailing
      subst count
      exact Nat.le_max_right _ _

end SmcTuring.Native.StringRequestBounds
