module
public import SmcTuring.Appendix.Listing8JointRetargetOwnerPhase
public import SmcTuring.Appendix.Listing8GraphBackedgeSources

public section
namespace SmcTuring.Appendix.Listing8OriginalGraphCatalog
open Native Listing8CopyImage Listing8Prototypes Listing8SourceGraph Listing8OwnerTemplateCollection
@[expose] def original (mode : Mode) : Listing8OriginalOwners.Owner mode → Template mode
  | .pointer pc _ => .pointer pc pc
  | .scalar pc _ => .scalar pc (Relocation.memoryDisp mode (pc+10) (pc+6))
@[expose] def nodeTemplates (mode : Mode) (pc : Nat) : List (Template mode) :=
  [.scalar pc (Relocation.memoryDisp mode (pc+10) (pc+6)),
    .pointer (backEntry mode pc) (backEntry mode pc),.pointer (forwardEntry mode pc) (forwardEntry mode pc)]
@[expose] def ruleTemplates (mode : Mode) (pc : Nat) : List (Template mode) :=
  [.pointer pc pc,
    .scalar (currentEntry mode pc) (Relocation.memoryDisp mode (currentEntry mode pc+10) (currentEntry mode pc+6)),
    .scalar (newEntry mode pc) (Relocation.memoryDisp mode (newEntry mode pc+10) (newEntry mode pc+6)),
    .scalar (directionEntry mode pc) (Relocation.memoryDisp mode (directionEntry mode pc+10) (directionEntry mode pc+6)),
    .pointer (stateEntry mode pc) (stateEntry mode pc)]
@[expose] def catalog (mode : Mode) (origin : Nat) (g : Graph) :=
  (List.ofFn (fun query : Fin g.nodes => nodeTemplates mode (nodePC mode origin g query))).flatten++
    (List.ofFn (fun query : Fin g.transitions => ruleTemplates mode (rulePC mode origin g query))).flatten

theorem original_current (mode : Mode) (owner : Listing8OriginalOwners.Owner mode) (memory : ByteMemory.Memory)
    (current : Listing8OriginalOwners.Current mode owner memory) : Intact mode (original mode owner) memory := by
  cases owner with
  | pointer pc value => exact Listing8PointerTemplate.initial mode pc pc value memory current
  | scalar pc value => exact Listing8ScalarTemplate.original mode pc value memory current

theorem node_current (mode : Mode) (pc : Nat) (v : Listing8NodeBlock.Values mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory pc (nodeSpan mode)=Listing8NodeBlock.bytes mode pc v) :
    All mode (nodeTemplates mode pc) memory := by
  have owners:=Listing8NodeBlock.current mode pc v memory current
  have shape : nodeTemplates mode pc=(Listing8NodeBlock.owners mode pc v).map (original mode) := rfl
  rw [shape];intro template member
  obtain ⟨owner,inside,rfl⟩:=List.mem_map.mp member
  exact original_current mode owner memory (owners owner inside)

theorem rule_current (mode : Mode) (pc : Nat) (v : Values mode) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory pc (transitionSpan mode)=transitionBytes mode pc v.next v.newState v.rule v.fresh v.direction) :
    All mode (ruleTemplates mode pc) memory := by
  have owners:=Listing8TransitionBlock.current mode pc v memory current
  have shape : ruleTemplates mode pc=(Listing8TransitionBlock.owners mode pc v).map (original mode) := rfl
  rw [shape];intro template member
  obtain ⟨owner,inside,rfl⟩:=List.mem_map.mp member
  exact original_current mode owner memory (owners owner inside)

theorem from_initial (mode : Mode) (origin : Nat) (g : Graph) (memory : ByteMemory.Memory)
    (nodes : Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions)
      (Listing8GraphNodeImage.declarations mode origin g) memory)
    (rules : Listing8TransitionTable.Initial mode (Listing8FullTableImage.start mode origin) (table mode origin g) memory) :
    All mode (catalog mode origin g) memory := by
  intro template member
  simp only [catalog,List.mem_append,List.mem_flatten] at member
  rcases member with ⟨items,inside,selected⟩ | ⟨items,inside,selected⟩
  · obtain ⟨query,rfl⟩:=List.mem_ofFn.mp inside
    exact node_current mode _ _ memory
      (Listing8NodeTable.selected_current mode _ _ query.val _ (Listing8GraphNodeImage.lookup mode origin g query) memory nodes) template selected
  · obtain ⟨query,rfl⟩:=List.mem_ofFn.mp inside
    exact rule_current mode _ _ memory
      (Listing8TransitionTable.selected_current mode _ _ query.val _ (lookup mode origin g query) memory rules) template selected

theorem node_bounds (mode : Mode) (pc : Nat) (template : Template mode) (member : template∈nodeTemplates mode pc) :
    pc≤start mode template ∧ start mode template+span mode template≤pc+nodeSpan mode := by
  simp only [nodeTemplates,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals cases mode <;> simp only [start,span,backEntry,forwardEntry,nodeSpan,pointerSpan,ReaderImage.totalSize] <;> omega

theorem rule_bounds (mode : Mode) (pc : Nat) (template : Template mode) (member : template∈ruleTemplates mode pc) :
    pc≤start mode template ∧ start mode template+span mode template≤pc+transitionSpan mode := by
  simp only [ruleTemplates,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals cases mode <;> simp only [start,span,currentEntry,newEntry,directionEntry,stateEntry,transitionSpan,pointerSpan,ReaderImage.totalSize] <;> omega

end SmcTuring.Appendix.Listing8OriginalGraphCatalog
