module
public import SmcTuring.Appendix.Listing9MetadataPackets
public import SmcTuring.Appendix.Listing9SelfDeclaration

public section
namespace SmcTuring.Appendix.Listing9Storage
open Native Listing9PackedLayout

/-- Observations of both declaration packets in the same present memory. -/
structure Current (mode : Mode) (start transitions nodes : Nat) (memory : ByteMemory.Memory) : Prop where
  save : ByteMemory.bytesAt memory (saveOwner mode start transitions nodes) (StringCodec.initialSize mode)=
    StringInit.bytes mode (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save
  pointer : ByteMemory.bytesAt memory (pointerOwner mode start transitions nodes) (StringCodec.initialSize mode)=
    StringInit.bytes mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save

@[expose] def afterSave (mode : Mode) (start transitions nodes : Nat) (state : StringExecution.State mode) :=
  StringExecution.run mode (StringInit.forms mode (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save) state
@[expose] def finish (mode : Mode) (start transitions nodes : Nat) (state : StringExecution.State mode) :=
  StringExecution.run mode (StringInit.forms mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save)
    (afterSave mode start transitions nodes state)
@[expose] def forms (mode : Mode) (start transitions nodes : Nat) :=
  StringInit.forms mode (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save++
    StringInit.forms mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save
@[expose] def program (mode : Mode) (start transitions nodes : Nat) :=
  (((forms mode start transitions nodes).map StringDword.Form.string).map StringControl.Form.previous).map StringStack.Form.previous

theorem current_of_retained (mode : Mode) (start transitions nodes : Nat) (backing memory : ByteMemory.Memory)
    (retained : ∀ observed size, saveOwner mode start transitions nodes≤observed →
      ByteMemory.bytesAt memory observed size=ByteMemory.bytesAt
        (ByteMemory.putWord mode (Listing9Image.memory mode start transitions nodes backing)
          (layout mode start transitions nodes).save (Arithmetic.encodeNat mode (layout mode start transitions nodes).save)) observed size) :
    Current mode start transitions nodes memory := by
  constructor
  · rw [retained _ _ (Nat.le_refl _)]
    exact Listing9MetadataPackets.save_current mode start transitions nodes backing
  · rw [retained _ _ (by dsimp [pointerOwner];omega)]
    exact Listing9MetadataPackets.pointer_current mode start transitions nodes backing

theorem after_save_effect (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start transitions nodes))
    (current : Current mode start transitions nodes state.principal.memory) :
    afterSave mode start transitions nodes state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (pointerOwner mode start transitions nodes)
      accumulator:=if mode=.x86 then state.principal.accumulator else Arithmetic.encodeNat mode (layout mode start transitions nodes).save}} :=
  Listing9SelfDeclaration.effect mode (saveOwner mode start transitions nodes) state entry
    (owner_capacity mode start transitions nodes bounds).1 current.save

theorem pointer_entry (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start transitions nodes))
    (current : Current mode start transitions nodes state.principal.memory) :
    (afterSave mode start transitions nodes state).principal.pc=Arithmetic.encodeNat mode (pointerOwner mode start transitions nodes) ∧
    (afterSave mode start transitions nodes state).principal.memory=state.principal.memory := by
  rw [after_save_effect mode start transitions nodes bounds state entry current]
  exact ⟨rfl,rfl⟩

theorem trace (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start transitions nodes))
    (current : Current mode start transitions nodes state.principal.memory) :
    StringStack.Trace mode state (program mode start transitions nodes) (finish mode start transitions nodes state) := by
  have capacities:=owner_capacity mode start transitions nodes bounds
  have coords:=positions mode start transitions nodes
  have first:=Listing9SelfDeclaration.trace mode (saveOwner mode start transitions nodes) state entry capacities.1 current.save
  have next:=pointer_entry mode start transitions nodes bounds state entry current
  have packet : ByteMemory.bytesAt (afterSave mode start transitions nodes state).principal.memory
      (pointerOwner mode start transitions nodes) (StringCodec.initialSize mode)=
      StringInit.bytes mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save := by
    rw [next.2];exact current.pointer
  have targetFits : (layout mode start transitions nodes).save+mode.wordBytes<2^(8*mode.wordBytes) := by
    rw [coords.2.2.2.1];omega
  have second:=StringInitTrace.trace mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save
    (afterSave mode start transitions nodes state) next.1 capacities.2 targetFits (Or.inl (Nat.le_of_eq coords.2.2.2.1)) packet
  exact StringStack.previous_trace mode (StringControl.previous_trace mode (StringDword.string_trace mode
    (StringExecution.trace_append mode first second)))

/-- Both trailing packets preserve the complete byte memory. x86 retains AX;
x64 has the exact self-address value loaded by the printed pointer declaration. -/
theorem effect (mode : Mode) (start transitions nodes : Nat) (bounds : Bounds mode start transitions nodes)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode (saveOwner mode start transitions nodes))
    (current : Current mode start transitions nodes state.principal.memory) :
    finish mode start transitions nodes state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (endPC mode start transitions nodes)
      accumulator:=if mode=.x86 then state.principal.accumulator else Arithmetic.encodeNat mode (layout mode start transitions nodes).save}} := by
  have capacities:=owner_capacity mode start transitions nodes bounds
  have next:=pointer_entry mode start transitions nodes bounds state entry current
  have packet : ByteMemory.bytesAt (afterSave mode start transitions nodes state).principal.memory
      (pointerOwner mode start transitions nodes) (StringCodec.initialSize mode)=
      StringInit.bytes mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save := by
    rw [next.2];exact current.pointer
  have second:=StringInit.effect mode (pointerOwner mode start transitions nodes) (layout mode start transitions nodes).save
    (afterSave mode start transitions nodes state) next.1 capacities.2 packet
  have value:=StringInit.initialized_pointer mode (saveOwner mode start transitions nodes) (layout mode start transitions nodes).save
    state.principal.memory capacities.1 current.save
  change Execution.load mode state.principal.memory (Arithmetic.encodeNat mode (layout mode start transitions nodes).save)=
    Arithmetic.encodeNat mode (layout mode start transitions nodes).save at value
  rw [finish,second,after_save_effect mode start transitions nodes bounds state entry current]
  cases mode with
  | x86 => rfl
  | x64 =>
    change {state with principal:={state.principal with pc:=Arithmetic.encodeNat .x64 (endPC .x64 start transitions nodes), accumulator:=Execution.load .x64 state.principal.memory (Arithmetic.encodeNat .x64 (layout .x64 start transitions nodes).save)}}=_
    rw [value]
    simp only [reduceCtorEq,ite_false]

theorem instruction_count (mode : Mode) (start transitions nodes : Nat) :
    (program mode start transitions nodes).length=if mode=.x86 then 2 else 8 := by
  cases mode <;> rfl

end SmcTuring.Appendix.Listing9Storage
