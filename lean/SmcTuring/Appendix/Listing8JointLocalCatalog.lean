module
public import SmcTuring.Appendix.Listing8InactiveLocalInput

public section
namespace SmcTuring.Appendix.Listing8JointLocalCatalog
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets
abbrev head (mode : Mode) (l : Layout):=Listing8DirectionGeometry.region mode l
abbrev transition (mode : Mode) (l : Layout):=Listing8StateGeometry.region mode l
abbrev failure (mode : Mode) (l : Layout) (sentinel begin : Nat):=Listing8FailureGeometry.region mode l sentinel begin
set_option maxHeartbeats 2000000
/-- One fixed local executable inventory, shared by all suffix phases. -/
structure Property (mode : Mode) (l : Layout) (sentinel begin : Nat) (memory : ByteMemory.Memory) : Prop where
  input : DwordTemplateCollection.All (Listing8InputExecutableTemplates.templates mode l.input) memory
  inputFixed : MixedFixedTemplates.All mode (Listing8InputFixedTemplates.entries mode l.input) memory
  headArithmetic : DwordTemplateCollection.All (Listing8DirectionTemplateFields.templates mode (head mode l)) memory
  headFixed : MixedFixedTemplates.All mode (Listing8DirectionTemplateFields.fixed mode (head mode l)) memory
  headXor : DwordXorSequence.Intact mode (Listing8HeadTailBounds.xorLayouts mode (head mode l)) memory
  stateArithmetic : DwordTemplateCollection.All (Listing8StateTemplateFields.arithmetic mode (transition mode l)) memory
  stateFixed : MixedFixedTemplates.All mode (Listing8StateTemplateFields.fixed mode (transition mode l)) memory
  failure : Listing8FailureExecutableTemplates.Property mode (failure mode l sentinel begin) memory
structure Compatible (mode : Mode) (l : Layout) (sentinel begin address count : Nat) : Prop where
  input : DwordTemplateCollection.CompatibleAll (Listing8InputExecutableTemplates.templates mode l.input) address count
  inputFixed : MixedFixedTemplates.OutsideAll mode (Listing8InputFixedTemplates.entries mode l.input) address count
  headArithmetic : DwordTemplateCollection.CompatibleAll (Listing8DirectionTemplateFields.templates mode (head mode l)) address count
  headFixed : MixedFixedTemplates.OutsideAll mode (Listing8DirectionTemplateFields.fixed mode (head mode l)) address count
  headXor : DwordXorTemplates.OutsideAll (Listing8HeadTailBounds.xorLayouts mode (head mode l)) address count
  stateArithmetic : DwordTemplateCollection.CompatibleAll (Listing8StateTemplateFields.arithmetic mode (transition mode l)) address count
  stateFixed : MixedFixedTemplates.OutsideAll mode (Listing8StateTemplateFields.fixed mode (transition mode l)) address count
  failure : Listing8FailureTemplateFields.Allowed mode (failure mode l sentinel begin) address count
structure Decodes (mode : Mode) (l : Layout) (sentinel begin : Nat) (memory : ByteMemory.Memory) : Prop where
  input : ∀ template∈Listing8InputExecutableTemplates.templates mode l.input,DwordTemplateCollection.Decodes mode template memory
  inputFixed : ∀ template∈Listing8InputFixedTemplates.entries mode l.input,MixedFixedTemplates.Decodes mode template memory
  headArithmetic : ∀ template∈Listing8DirectionTemplateFields.templates mode (head mode l),DwordTemplateCollection.Decodes mode template memory
  headFixed : ∀ template∈Listing8DirectionTemplateFields.fixed mode (head mode l),MixedFixedTemplates.Decodes mode template memory
  headXor : ∀ helper∈Listing8HeadTailBounds.xorLayouts mode (head mode l),DwordXorTemplates.Decodes mode helper memory
  stateArithmetic : ∀ template∈Listing8StateTemplateFields.arithmetic mode (transition mode l),DwordTemplateCollection.Decodes mode template memory
  stateFixed : ∀ template∈Listing8StateTemplateFields.fixed mode (transition mode l),MixedFixedTemplates.Decodes mode template memory
  failure : Listing8FailureExecutableTemplates.Decodes mode (failure mode l sentinel begin) memory

theorem decodes (mode : Mode) (l : Layout) (sentinel begin : Nat) (memory : ByteMemory.Memory)
    (current : Property mode l sentinel begin memory) : Decodes mode l sentinel begin memory :=
  ⟨fun template member => DwordTemplateCollection.decodes mode template memory (current.input template member),
    fun template member => MixedFixedTemplates.decodes mode template memory (current.inputFixed template member),
    fun template member => DwordTemplateCollection.decodes mode template memory (current.headArithmetic template member),
    fun template member => MixedFixedTemplates.decodes mode template memory (current.headFixed template member),
    fun helper member => DwordXorTemplates.decodes mode helper memory (current.headXor helper member),
    fun template member => DwordTemplateCollection.decodes mode template memory (current.stateArithmetic template member),
    fun template member => MixedFixedTemplates.decodes mode template memory (current.stateFixed template member),
    Listing8FailureExecutableTemplates.decodes mode _ memory current.failure⟩

theorem store (mode : Mode) (l : Layout) (sentinel begin : Nat) (memory : ByteMemory.Memory)
    (address : Nat) (packet : List LittleEndian.Byte) (current : Property mode l sentinel begin memory)
    (compatible : Compatible mode l sentinel begin address packet.length) :
    Property mode l sentinel begin (ByteMemory.putBytes memory address packet) :=
  ⟨DwordTemplateCollection.store_all _ memory address packet current.input compatible.input,
    MixedFixedTemplates.store_all mode _ memory address packet current.inputFixed compatible.inputFixed,
    DwordTemplateCollection.store_all _ memory address packet current.headArithmetic compatible.headArithmetic,
    MixedFixedTemplates.store_all mode _ memory address packet current.headFixed compatible.headFixed,
    DwordXorTemplates.frame mode _ memory address packet current.headXor compatible.headXor,
    DwordTemplateCollection.store_all _ memory address packet current.stateArithmetic compatible.stateArithmetic,
    MixedFixedTemplates.store_all mode _ memory address packet current.stateFixed compatible.stateFixed,
    Listing8FailureExecutableTemplates.store mode _ memory address packet current.failure compatible.failure⟩

theorem ordering (mode : Mode) (l : Layout) (sentinel begin : Nat) :
    l.input.start≤(head mode l).start ∧ (head mode l).start≤(transition mode l).start ∧
    (transition mode l).start≤(failure mode l sentinel begin).start ∧
    (failure mode l sentinel begin).start≤Listing8FailureLayout.callPC mode (failure mode l sentinel begin)+5 := by
  have input:=(Listing8LiteralInput.positions mode l.input).2.2.2.2.2.2.2
  have h:=(Listing8DirectionLayout.positions mode (head mode l)).2.2.2.2.2.2.2
  have s:=(Listing8StateLayout.positions mode (transition mode l)).2.2.2
  change Listing8DirectionLayout.endPC mode (head mode l)=(head mode l).start+(if mode=.x86 then 91 else 202) at h
  change Listing8StateLayout.endPC mode (transition mode l)=(transition mode l).start+(if mode=.x86 then 47 else 96) at s
  change _ ∧ (head mode l).start≤Listing8DirectionLayout.endPC mode (head mode l) ∧
    (transition mode l).start≤Listing8StateLayout.endPC mode (transition mode l) ∧ _
  have f:=Listing8FailureLayout.positions mode (failure mode l sentinel begin)
  cases mode <;> simp only [head,Listing8DirectionGeometry.region,reduceCtorEq,ite_true,ite_false] at input h s f ⊢ <;> omega

/-- Every inactive input/head/state template survives a complete write before
input or after state. The executing failure catalog has its own mutable fields. -/
theorem exterior (mode : Mode) (l : Layout) (sentinel begin address count : Nat)
    (outside : address+count≤l.input.start ∨ (failure mode l sentinel begin).start≤address)
    (own : Listing8FailureTemplateFields.Allowed mode (failure mode l sentinel begin) address count) :
    Compatible mode l sentinel begin address count := by
  have order:=ordering mode l sentinel begin
  have h:=Listing8DirectionLayout.positions mode (head mode l)
  have s:=Listing8StateLayout.positions mode (transition mode l)
  refine ⟨Listing8InputExecutableTemplates.exterior mode l.input address count (by
    rcases outside with early | late
    · exact Or.inl early
    · exact Or.inr (by change (head mode l).start≤address;omega)),
    Listing8InputFixedTemplates.exterior mode l.input address count (by
      rcases outside with early | late
      · exact Or.inl early
      · exact Or.inr (by change (head mode l).start≤address;omega)),?_,?_,?_,?_,?_,own⟩
  · intro template member
    have bounds:=Listing8DirectionTemplateFields.template_bounds mode (head mode l) template member
    right;rcases outside with early | late
    · left;omega
    · right
      have endBefore : Listing8DirectionLayout.endPC mode (head mode l)≤(failure mode l sentinel begin).start := order.2.2.1
      omega
  · intro template member
    have bounds:=Listing8DirectionTemplateFields.fixed_bounds mode (head mode l) template member
    rcases outside with early | late
    · left;exact early.trans (order.1.trans bounds.1)
    · right
      have endBefore : Listing8DirectionLayout.endPC mode (head mode l)≤(failure mode l sentinel begin).start := order.2.2.1
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at h <;> omega
  · intro helper member
    have bounds:=Listing8HeadTemplateFields.xor_bounds mode (head mode l) helper member
    rcases outside with early | late
    · left;omega
    · right
      have endBefore : Listing8DirectionLayout.endPC mode (head mode l)≤(failure mode l sentinel begin).start := order.2.2.1
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at h <;> omega
  · intro template member
    have bounds:=Listing8StateTemplateFields.arithmetic_bounds mode (transition mode l) template member
    right;rcases outside with early | late
    · left;omega
    · right;exact bounds.2.trans late
  · intro template member
    have bounds:=Listing8StateTemplateFields.fixed_bounds mode (transition mode l) template member
    rcases outside with early | late
    · left;omega
    · right
      change Listing8StateLayout.endPC mode (transition mode l)≤address at late
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at s <;> omega

/-- Head stores touch only its live operand words or the earlier cursor. -/
theorem head_write (mode : Mode) (l : Layout) (sentinel begin address : Nat)
    (own : Listing8DirectionTemplateFields.Allowed mode (head mode l) address)
    (input : address+4≤l.input.start ∨ (head mode l).start≤address)
    (upper : address+4≤(transition mode l).start) : Compatible mode l sentinel begin address 4 := by
  have order:=ordering mode l sentinel begin
  refine ⟨Listing8InputExecutableTemplates.exterior mode l.input address 4 input,
    Listing8InputFixedTemplates.exterior mode l.input address 4 input,
    Listing8DirectionTemplateFields.compatible mode _ address own,
    Listing8DirectionTemplateFields.fixed_frames mode _ address own,
    Listing8DirectionTemplateFields.xor_frames mode _ address own,
    Listing8StateTemplateFields.compatible mode _ address (Or.inl upper),
    Listing8StateTemplateFields.frames mode _ address (Or.inl upper),Or.inl (upper.trans order.2.2.1)⟩

theorem state_write (mode : Mode) (l : Layout) (sentinel begin address : Nat)
    (own : Listing8StateTemplateFields.Allowed mode (transition mode l) address)
    (outside : address+4≤l.input.start ∨ (transition mode l).start≤address)
    (upper : address+4≤(failure mode l sentinel begin).start) : Compatible mode l sentinel begin address 4 := by
  have order:=ordering mode l sentinel begin
  have h:=Listing8DirectionLayout.positions mode (head mode l)
  refine ⟨Listing8InputExecutableTemplates.exterior mode l.input address 4 (by
    rcases outside with early | late
    · exact Or.inl early
    · exact Or.inr (order.2.1.trans late)),
    Listing8InputFixedTemplates.exterior mode l.input address 4 (by
      rcases outside with early | late
      · exact Or.inl early
      · exact Or.inr (order.2.1.trans late)),?_,?_,?_,
    Listing8StateTemplateFields.compatible mode _ address own,
    Listing8StateTemplateFields.frames mode _ address own,Or.inl upper⟩
  · intro template member
    have bounds:=Listing8DirectionTemplateFields.template_bounds mode (head mode l) template member
    right;rcases outside with early | late
    · left;omega
    · right;exact bounds.2.trans late
  · intro template member
    have bounds:=Listing8DirectionTemplateFields.fixed_bounds mode (head mode l) template member
    rcases outside with early | late
    · left;omega
    · right
      change Listing8DirectionLayout.endPC mode (head mode l)≤address at late
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at h <;> omega
  · intro helper member
    have bounds:=Listing8HeadTemplateFields.xor_bounds mode (head mode l) helper member
    rcases outside with early | late
    · left;omega
    · right
      change Listing8DirectionLayout.endPC mode (head mode l)≤address at late
      cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at h <;> omega

@[expose] def headSlots (mode : Mode) (l : Layout) : List Nat :=
  [(head mode l).cursor,Listing8DirectionLayout.combinedPC mode (head mode l)+6,
    Listing8DirectionLayout.directionPC mode (head mode l)+6] ++
    (if mode=.x64 then [(head mode l).cursor+4,Listing8DirectionLayout.combinedPC mode (head mode l)+16,
      Listing8DirectionLayout.directionPC mode (head mode l)+16] else [])
@[expose] def stateSlots (mode : Mode) (l : Layout) : List Nat :=
  [(transition mode l).cursor,Listing8StateLayout.updatePC mode (transition mode l)+6] ++
    (if mode=.x64 then [(transition mode l).cursor+4,Listing8StateLayout.updatePC mode (transition mode l)+16] else [])

theorem head_slot (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address : Nat) (member : address∈headSlots mode l) :
    Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) address 4 := by
  have cursor:=(Listing8InputBounds.cursor_bounds mode l t ctx.body.state.head.input.fields ctx.body.state.head.input.joined ctx.resources).2.2.1
  change (head mode l).cursor+mode.wordBytes≤l.input.start at cursor
  have order:=ordering mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have coords:=Listing8DirectionLayout.positions mode (head mode l)
  have ending : (transition mode l).start=Listing8DirectionLayout.endPC mode (head mode l) := rfl
  cases mode
  all_goals simp only [headSlots,reduceCtorEq,ite_true,ite_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply head_write
  all_goals simp only [Listing8DirectionTemplateFields.Allowed,Mode.wordBytes,reduceCtorEq,true_and,false_and,or_false,or_true,true_or,ite_true,ite_false] at cursor coords ⊢
  all_goals omega

theorem state_slot (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address : Nat) (member : address∈stateSlots mode l) :
    Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) address 4 := by
  have cursor:=Listing8PointerCopies.cursor_before mode l
  change (transition mode l).cursor+mode.wordBytes≤codeEnd mode l at cursor
  have before:=ctx.resources.inputAfter
  have order:=ordering mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have coords:=Listing8StateLayout.positions mode (transition mode l)
  have ending : (failure mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)).start=
    Listing8StateLayout.endPC mode (transition mode l) := rfl
  cases mode
  all_goals simp only [stateSlots,reduceCtorEq,ite_true,ite_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  all_goals apply state_write
  all_goals simp only [Listing8StateTemplateFields.Allowed,Mode.wordBytes,reduceCtorEq,true_and,false_and,or_false,or_true,true_or,ite_true,ite_false] at cursor coords ⊢
  all_goals omega


theorem head_helpers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ helper∈Listing8DirectionLayout.helpers mode (head mode l),
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) helper.source 4 ∧
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) helper.destination 4 := by
  intro helper member
  cases mode
  all_goals simp only [Listing8DirectionLayout.helpers,Listing8DirectionLayout.duplicate,Listing8DirectionLayout.copy,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at member
  all_goals rcases member with rfl | rfl | rfl
  all_goals constructor
  all_goals apply head_slot _ origin l t g node rule ctx
  all_goals simp [headSlots]

theorem head_xors (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ helper∈Listing8HeadTailBounds.xorLayouts mode (head mode l),
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) helper.source 4 ∧
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) helper.destination 4 := by
  intro helper member
  cases mode
  all_goals simp only [Listing8HeadTailBounds.xorLayouts,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals constructor
  all_goals apply head_slot _ origin l t g node rule ctx
  all_goals simp [headSlots]

theorem head_packets (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ site∈Listing8DirectionTemplateFields.sites mode (head mode l),
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) site.target 4 := by
  intro site member
  cases mode
  all_goals simp only [Listing8DirectionTemplateFields.sites,Listing8DirectionLayout.arithmetic,Listing8DirectionLayout.masks,
    Listing8DirectionLayout.heads,Listing8DirectionLayout.group,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply head_slot _ origin l t g node rule ctx
  all_goals simp [headSlots,Nat.add_assoc]

theorem state_helpers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ helper∈Listing8StateLayout.helpers mode (transition mode l),
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) helper.source 4 ∧
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) helper.destination 4 := by
  intro helper member
  cases mode
  all_goals simp only [Listing8StateLayout.helpers,Listing8PointerCopies.split,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals constructor
  all_goals apply state_slot _ origin l t g node rule ctx
  all_goals simp [stateSlots]

theorem state_packets (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule) :
    ∀ site∈Listing8StateLayout.packets mode (transition mode l),
      Compatible mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) site.target 4 := by
  intro site member
  cases mode
  all_goals simp only [Listing8StateLayout.packets,Listing8StateLayout.newPackets,Listing8StateLayout.masks,Listing8StateLayout.updates,
    Listing8DirectionLayout.group,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply state_slot _ origin l t g node rule ctx
  all_goals simp [stateSlots,Nat.add_assoc]


theorem input_windows (mode : Mode) (l : Layout) (v : Values mode) (sentinel begin : Nat) (memory : ByteMemory.Memory)
    (current : Property mode l sentinel begin memory) : Listing8JointInputCatalog.Local mode l v memory := by
  intro window member
  exact Listing8InputJointTemplates.valid_windows mode l.input memory current.input current.inputFixed window
    (Listing8InputJointTemplates.coverage mode l.input v.rule v.tape v.fresh window member)

theorem descriptor_count (mode : Mode) (l : Layout) (sentinel begin : Nat) :
    (Listing8InputExecutableTemplates.templates mode l.input).length+
    (Listing8InputFixedTemplates.entries mode l.input).length+
    (Listing8DirectionTemplateFields.templates mode (head mode l)).length+
    (Listing8DirectionTemplateFields.fixed mode (head mode l)).length+
    3*(Listing8HeadTailBounds.xorLayouts mode (head mode l)).length+
    (Listing8StateTemplateFields.arithmetic mode (transition mode l)).length+
    (Listing8StateTemplateFields.fixed mode (transition mode l)).length+
    (Listing8FailureTemplateFields.arithmetic mode (failure mode l sentinel begin)).length+
    (StringInit.forms mode (Listing8FailureLayout.ownerPC (failure mode l sentinel begin)) 0).length+
    (Listing8FailComparison.sites mode (Listing8FailureLayout.comparison mode (failure mode l sentinel begin))).length+1=
      if mode=.x86 then 52 else 82 := by
  cases mode <;> rfl


end SmcTuring.Appendix.Listing8JointLocalCatalog
