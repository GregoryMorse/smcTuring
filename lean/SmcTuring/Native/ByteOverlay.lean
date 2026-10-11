module
public import SmcTuring.Native.Writes
public import SmcTuring.Native.ByteWindow

public section
namespace SmcTuring.Native.ByteOverlay
structure Site where
  pc : Nat
  bytes : List LittleEndian.Byte
@[expose] def run : List Site → ByteMemory.Memory → ByteMemory.Memory
  | [],memory => memory
  | site::rest,memory => run rest (ByteMemory.putBytes memory site.pc site.bytes)
theorem commute (memory : ByteMemory.Memory) (first second : Nat) (a b : List LittleEndian.Byte)
    (separate : first+a.length ≤ second ∨ second+b.length ≤ first) :
    ByteMemory.putBytes (ByteMemory.putBytes memory first a) second b=
      ByteMemory.putBytes (ByteMemory.putBytes memory second b) first a := by
  apply Writes.put_bytes_commute
  intro position inside
  unfold ByteMemory.Inside at *
  rcases separate with before | after <;> omega
theorem run_put (sites : List Site) (memory : ByteMemory.Memory) (pc : Nat) (bytes : List LittleEndian.Byte)
    (separate : ∀ site∈sites, pc+bytes.length ≤ site.pc ∨ site.pc+site.bytes.length ≤ pc) :
    run sites (ByteMemory.putBytes memory pc bytes)=ByteMemory.putBytes (run sites memory) pc bytes := by
  induction sites generalizing memory with
  | nil => rfl
  | cons site rest ih =>
    rw [run,commute memory pc site.pc bytes site.bytes (separate site (List.Mem.head _))]
    exact ih _ (fun later member => separate later (List.Mem.tail _ member))
end SmcTuring.Native.ByteOverlay
