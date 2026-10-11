module
public import SmcTuring.Native.ConversionLayout

public section
namespace SmcTuring.Native.ConversionEffects
open Execution ConversionLayout

@[expose] def swapped (mode : Mode) (layout : Layout) (native : State mode) : State mode := execute mode (first mode layout) native
@[expose] def stored (mode : Mode) (layout : Layout) (native : State mode) : State mode := execute mode (second mode layout) (swapped mode layout native)
@[expose] def finish (mode : Mode) (layout : Layout) (native : State mode) : State mode := execute mode (third mode layout) (stored mode layout native)

theorem source_outside (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (index : Fin mode.wordBytes) :
    ¬ByteMemory.Inside layout.destination mode.wordBytes (layout.source + index.val) := by
  have bound := index.isLt
  have separate := valid.separate
  unfold ByteMemory.Inside
  omega

theorem destination_outside (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (index : Fin mode.wordBytes) :
    ¬ByteMemory.Inside layout.source mode.wordBytes (layout.destination + index.val) := by
  have bound := index.isLt
  have separate := valid.separate
  unfold ByteMemory.Inside
  omega

theorem first_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    swapped mode layout native =
      { native with
        pc := Arithmetic.encodeNat mode (secondPC mode layout),
        accumulator := load mode native.memory (Arithmetic.encodeNat mode layout.source),
        memory := ByteMemory.putWord mode native.memory layout.source native.accumulator } := by
  change Reader.swapped mode native (firstDisp mode layout) = _
  have next := first_next mode layout native entry
  change nextPC mode (.memory .exchangeAcc (firstDisp mode layout)) native = _ at next
  rw [Reader.exchange_effect mode native _ _ (first_hits mode layout valid native entry), next, source_toNat mode layout valid]

theorem second_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode (secondPC mode layout)) :
    execute mode (second mode layout) native =
      { native with
        pc := Arithmetic.encodeNat mode (thirdPC mode layout),
        memory := ByteMemory.putWord mode native.memory layout.destination native.accumulator } := by
  change execute mode (Reader.storeForm mode _ (secondDisp mode layout)) native = _
  rw [Reader.store_effect mode native _ _ (second_hits mode layout valid native entry)]
  change { native with
    pc := nextPC mode (second mode layout) native,
    memory := ByteMemory.putWord mode native.memory (Arithmetic.encodeNat mode layout.destination).toNat native.accumulator } = _
  rw [second_next mode layout native entry, destination_toNat mode layout valid]

theorem third_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode (thirdPC mode layout)) :
    execute mode (third mode layout) native =
      { native with
        pc := Arithmetic.encodeNat mode (endPC mode layout),
        accumulator := load mode native.memory (Arithmetic.encodeNat mode layout.source),
        memory := ByteMemory.putWord mode native.memory layout.source native.accumulator } := by
  change Reader.swapped mode native (thirdDisp mode layout) = _
  have next := third_next mode layout native entry
  change nextPC mode (.memory .exchangeAcc (thirdDisp mode layout)) native = _ at next
  rw [Reader.exchange_effect mode native _ _ (third_hits mode layout valid native entry), next, source_toNat mode layout valid]

theorem swapped_pc (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    (swapped mode layout native).pc = Arithmetic.encodeNat mode (secondPC mode layout) := by
  rw [first_effect mode layout valid native entry]

theorem stored_effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    stored mode layout native =
      { native with
        pc := Arithmetic.encodeNat mode (thirdPC mode layout),
        accumulator := load mode native.memory (Arithmetic.encodeNat mode layout.source),
        memory := ByteMemory.putWord mode (ByteMemory.putWord mode native.memory layout.source native.accumulator)
          layout.destination (load mode native.memory (Arithmetic.encodeNat mode layout.source)) } := by
  rw [stored, second_effect mode layout valid _ (swapped_pc mode layout valid native entry), first_effect mode layout valid native entry]

theorem stored_pc (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    (stored mode layout native).pc = Arithmetic.encodeNat mode (thirdPC mode layout) := by
  rw [stored_effect mode layout valid native entry]

theorem original_source_read (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (memory : ByteMemory.Memory) (value : Word mode) :
    load mode (ByteMemory.putWord mode memory layout.destination value) (Arithmetic.encodeNat mode layout.source) =
      load mode memory (Arithmetic.encodeNat mode layout.source) := by
  have framed := Writes.load_frame mode memory (Arithmetic.encodeNat mode layout.destination) (Arithmetic.encodeNat mode layout.source) value
    (fun index => by rw [source_toNat mode layout valid, destination_toNat mode layout valid]; exact source_outside mode layout valid index)
  rwa [destination_toNat mode layout valid] at framed

theorem source_read_after_stored (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode) :
    load mode (ByteMemory.putWord mode (ByteMemory.putWord mode native.memory layout.source native.accumulator)
      layout.destination (load mode native.memory (Arithmetic.encodeNat mode layout.source)))
      (Arithmetic.encodeNat mode layout.source) = native.accumulator := by
  rw [original_source_read mode layout valid]
  have read := load_put_word mode native.memory (Arithmetic.encodeNat mode layout.source) native.accumulator
  rwa [source_toNat mode layout valid] at read

/-- Three complete byte stores restore the whole source field, leaving only
the destination store. The result is exact for every original memory byte. -/
theorem restored_memory (mode : Mode) (layout : Layout) (valid : Admissible mode layout)
    (memory : ByteMemory.Memory) (accumulator : Word mode) :
    ByteMemory.putWord mode (ByteMemory.putWord mode (ByteMemory.putWord mode memory layout.source accumulator)
      layout.destination (load mode memory (Arithmetic.encodeNat mode layout.source)))
      layout.source (load mode memory (Arithmetic.encodeNat mode layout.source)) =
    ByteMemory.putWord mode memory layout.destination (load mode memory (Arithmetic.encodeNat mode layout.source)) := by
  rw [Writes.put_words_commute mode _ layout.destination layout.source _ _ (destination_outside mode layout valid), Writes.put_word_overwrite]
  have back := Writes.put_word_back mode memory (Arithmetic.encodeNat mode layout.source)
  rw [source_toNat mode layout valid] at back
  rw [back]

theorem effect (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    finish mode layout native =
      { native with
        pc := Arithmetic.encodeNat mode (endPC mode layout),
        memory := ByteMemory.putWord mode native.memory layout.destination (load mode native.memory (Arithmetic.encodeNat mode layout.source)) } := by
  rw [finish, third_effect mode layout valid _ (stored_pc mode layout valid native entry), stored_effect mode layout valid native entry]
  rw [source_read_after_stored mode layout valid native, restored_memory mode layout valid native.memory native.accumulator]

theorem destination_value (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    load mode (finish mode layout native).memory (Arithmetic.encodeNat mode layout.destination) =
      load mode native.memory (Arithmetic.encodeNat mode layout.source) := by
  rw [effect mode layout valid native entry]
  have written := load_put_word mode native.memory (Arithmetic.encodeNat mode layout.destination) (load mode native.memory (Arithmetic.encodeNat mode layout.source))
  rwa [destination_toNat mode layout valid] at written

theorem source_value (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) :
    load mode (finish mode layout native).memory (Arithmetic.encodeNat mode layout.source) =
      load mode native.memory (Arithmetic.encodeNat mode layout.source) := by
  rw [effect mode layout valid native entry]
  exact original_source_read mode layout valid native.memory _

theorem frame (mode : Mode) (layout : Layout) (valid : Admissible mode layout) (native : State mode)
    (entry : native.pc = Arithmetic.encodeNat mode layout.start) (position : Nat)
    (outside : ¬ByteMemory.Inside layout.destination mode.wordBytes position) :
    (finish mode layout native).memory position = native.memory position := by
  rw [effect mode layout valid native entry]
  exact ByteMemory.put_frame _ _ _ _ (by simpa using outside)

end SmcTuring.Native.ConversionEffects
