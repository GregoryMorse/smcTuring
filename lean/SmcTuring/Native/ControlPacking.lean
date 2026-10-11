module
public import SmcTuring.Native.ControlImage

public section

namespace SmcTuring.Native.ControlPacking

open ControlImage

@[expose] def size (mode : Mode) (packets : List (Packet mode)) : Nat :=
  (packets.map (fun packet => (packet.bytes mode).length)).sum

/-- Computed adjacent packet placement for a finite fragment. Padding outside
the fragment may be supplied by its backing image; it is not a fetched packet. -/
@[expose] def place (mode : Mode) : Nat -> List (Packet mode) -> List (Entry mode)
  | _, [] => []
  | start, packet :: rest => { pc := start, packet := packet } ::
      place mode (start + (packet.bytes mode).length) rest

theorem placed_lower (mode : Mode) (packets : List (Packet mode)) (start : Nat) (entry : Entry mode)
    (member : List.Mem entry (place mode start packets)) : start <= entry.pc := by
  induction packets generalizing start with
  | nil => cases member
  | cons packet rest ih =>
    change List.Mem entry ({ pc := start, packet := packet } :: place mode (start + (packet.bytes mode).length) rest) at member
    cases member with
    | head => exact Nat.le_refl start
    | tail _ next => exact Nat.le_trans (Nat.le_add_right start _) (ih _ next)

theorem placed_upper (mode : Mode) (packets : List (Packet mode)) (start : Nat) (entry : Entry mode)
    (member : List.Mem entry (place mode start packets)) :
    entry.pc + (entry.bytes mode).length <= start + size mode packets := by
  induction packets generalizing start with
  | nil => cases member
  | cons packet rest ih =>
    change List.Mem entry ({ pc := start, packet := packet } :: place mode (start + (packet.bytes mode).length) rest) at member
    cases member with
    | head => simp [size, Entry.bytes]
    | tail _ next =>
      have bound := ih _ next
      simpa [size, Nat.add_assoc] using bound

/-- Byte separation is a consequence of computed placement, rather than an
input premise of the initialized control-fragment theorem. -/
theorem placed_separated (mode : Mode) (packets : List (Packet mode)) (start : Nat) :
    Separated mode (place mode start packets) := by
  induction packets generalizing start with
  | nil => intro first member; cases member
  | cons packet rest ih =>
    intro first member second secondMember different
    change List.Mem first ({ pc := start, packet := packet } :: place mode (start + (packet.bytes mode).length) rest) at member
    change List.Mem second ({ pc := start, packet := packet } :: place mode (start + (packet.bytes mode).length) rest) at secondMember
    cases member with
    | head =>
      cases secondMember with
      | head => exact False.elim (different rfl)
      | tail _ next => exact Or.inl (placed_lower mode rest _ second next)
    | tail _ firstNext =>
      cases secondMember with
      | head => exact Or.inr (placed_lower mode rest _ first firstNext)
      | tail _ secondNext => exact ih _ first firstNext second secondNext different

theorem initial_packet (mode : Mode) (packets : List (Packet mode)) (start : Nat) (memory : ByteMemory.Memory)
    (entry : Entry mode) (member : List.Mem entry (place mode start packets)) :
    ByteMemory.bytesAt (image mode (place mode start packets) memory) entry.pc (entry.bytes mode).length = entry.bytes mode :=
  image_packet mode _ memory (placed_separated mode packets start) entry member

theorem initially_intact (mode : Mode) (packets : List (Packet mode)) (start : Nat) (memory : ByteMemory.Memory) :
    Intact mode (place mode start packets) (image mode (place mode start packets) memory) :=
  initialized_intact mode _ memory (placed_separated mode packets start)

theorem initial_fetch (mode : Mode) (packets : List (Packet mode)) (start : Nat) (memory : ByteMemory.Memory)
    (entry : Entry mode) (member : List.Mem entry (place mode start packets)) :
    Fetch.fetch mode (image mode (place mode start packets) memory) entry.pc =
      some (currentForm mode entry (image mode (place mode start packets) memory)) :=
  fetch_current mode entry _ (initially_intact mode packets start memory entry member)

/-- The fragment initializer preserves backing bytes outside its exact extent. -/
theorem image_frame (mode : Mode) (packets : List (Packet mode)) (start : Nat) (memory : ByteMemory.Memory)
    (position : Nat) (outside : Or (position < start) (start + size mode packets <= position)) :
    image mode (place mode start packets) memory position = memory position := by
  induction packets generalizing start with
  | nil => rfl
  | cons packet rest ih =>
    have headOutside : Not (ByteMemory.Inside start (packet.bytes mode).length position) := by
      simp only [size, List.map_cons, List.sum_cons] at outside
      rcases outside with before | after <;> unfold ByteMemory.Inside <;> omega
    have restOutside : Or (position < start + (packet.bytes mode).length)
        (start + (packet.bytes mode).length + size mode rest <= position) := by
      simp only [size, List.map_cons, List.sum_cons] at outside
      rcases outside with before | after
      · exact Or.inl (by omega)
      · exact Or.inr (by simpa [size, Nat.add_assoc] using after)
    change ByteMemory.putBytes (image mode (place mode (start + (packet.bytes mode).length) rest) memory)
      start (packet.bytes mode) position = memory position
    rw [ByteMemory.put_frame _ _ _ position headOutside]
    exact ih _ restOutside

/-- Intact placed code yields an actual automatic step when PC names an entry. -/
theorem step_at_entry (mode : Mode) (entries : List (Entry mode)) (state : Execution.State mode)
    (entry : Entry mode) (member : List.Mem entry entries) (intact : Intact mode entries state.memory)
    (location : state.pc.toNat = entry.pc) :
    Fetch.step mode state = some (Execution.execute mode (currentForm mode entry state.memory) state) := by
  simp only [Fetch.step, location, fetch_current mode entry state.memory (intact entry member), Option.map_some]

/-- A word beginning beyond the constructed fragment is external to every
control packet, by the proved extent bound. -/
theorem above_external (mode : Mode) (packets : List (Packet mode)) (start : Nat) (address : Word mode)
    (after : start + size mode packets <= address.toNat) : External mode (place mode start packets) address := by
  intro entry member index
  have bound := placed_upper mode packets start entry member
  have small := index.isLt
  unfold ByteMemory.Inside
  omega

/-- The finite constructed fragment retains its fetch invariant throughout
actual instruction sequences whose writes target its owned operand fields. -/
theorem reached_intact (mode : Mode) (packets : List (Packet mode)) (start : Nat) (memory : ByteMemory.Memory)
    (state : Execution.State mode) (forms : List (Form mode))
    (initialMemory : state.memory = image mode (place mode start packets) memory)
    (owned : Writes.OwnedRun mode (Owned mode (place mode start packets)) forms state) :
    Intact mode (place mode start packets) (Execution.runForms mode forms state).memory := by
  apply run_intact mode _ state forms (placed_separated mode packets start) _ owned
  rw [initialMemory]
  exact initially_intact mode packets start memory

end SmcTuring.Native.ControlPacking
