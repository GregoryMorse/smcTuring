module
public import SmcTuring.Appendix.Listing8FullTableRun

public section
namespace SmcTuring.Appendix.Listing8GraphLayout
open Native Listing8Prototypes

/-- Immutable packed labels: the transition table follows the fail target,
the reset follows that table, and the input-node code follows DOHALT. -/
@[expose] def transition (mode : Mode) (origin index : Nat) :=
  Listing8FullTableImage.start mode origin+index*transitionSpan mode
@[expose] def reset (mode : Mode) (origin transitions : Nat) := transition mode origin transitions
@[expose] def input (mode : Mode) (origin transitions : Nat) := reset mode origin transitions+(if mode=.x86 then 64 else 89)
@[expose] def node (mode : Mode) (origin transitions index : Nat) := input mode origin transitions+index*nodeSpan mode
@[expose] def endPC (mode : Mode) (origin transitions nodes : Nat) := node mode origin transitions nodes

structure Bounds (mode : Mode) (origin transitions nodes : Nat) : Prop where
  capacity : endPC mode origin transitions nodes<2^(8*mode.wordBytes)
  resetReach : mode=.x64 → input mode origin transitions≤origin+2^31

theorem table_before_input (mode : Mode) (origin transitions : Nat) :
    reset mode origin transitions≤input mode origin transitions := by
  dsimp [input]
  omega
theorem transition_lower (mode : Mode) (origin index : Nat) :
    Listing8FullTableImage.start mode origin≤transition mode origin index := by dsimp [transition];omega
theorem transition_upper (mode : Mode) (origin transitions index : Nat) (within : index<transitions) :
    transition mode origin index+transitionSpan mode≤reset mode origin transitions := by
  have mult:=Nat.mul_le_mul_right (transitionSpan mode) (show index+1≤transitions by omega)
  simp only [Nat.add_mul,Nat.one_mul] at mult
  dsimp [transition,reset]
  omega
theorem node_lower (mode : Mode) (origin transitions index : Nat) :
    input mode origin transitions≤node mode origin transitions index := by dsimp [node];omega
theorem node_upper (mode : Mode) (origin transitions nodes index : Nat) (within : index<nodes) :
    node mode origin transitions index+nodeSpan mode≤endPC mode origin transitions nodes := by
  have mult:=Nat.mul_le_mul_right (nodeSpan mode) (show index+1≤nodes by omega)
  simp only [Nat.add_mul,Nat.one_mul] at mult
  dsimp [node,endPC]
  omega
theorem transition_capacity (mode : Mode) (origin transitions nodes index : Nat)
    (bounds : Bounds mode origin transitions nodes) (within : index<transitions) :
    transition mode origin index+transitionSpan mode<2^(8*mode.wordBytes) := by
  have upper:=transition_upper mode origin transitions index within
  have before:=table_before_input mode origin transitions
  have nodeBefore:=node_lower mode origin transitions nodes
  have cap:=bounds.capacity
  change node mode origin transitions nodes<_ at cap
  omega
theorem node_capacity (mode : Mode) (origin transitions nodes index : Nat)
    (bounds : Bounds mode origin transitions nodes) (within : index<nodes) :
    node mode origin transitions index+nodeSpan mode<2^(8*mode.wordBytes) :=
  Nat.lt_of_le_of_lt (node_upper mode origin transitions nodes index within) bounds.capacity
theorem table_node_apart (mode : Mode) (origin transitions tableIndex nodeIndex : Nat) (within : tableIndex<transitions) :
    transition mode origin tableIndex+transitionSpan mode≤node mode origin transitions nodeIndex :=
  Nat.le_trans (transition_upper mode origin transitions tableIndex within)
    (Nat.le_trans (table_before_input mode origin transitions) (node_lower mode origin transitions nodeIndex))
theorem nodes_apart (mode : Mode) (origin transitions first second : Nat) (before : first<second) :
    node mode origin transitions first+nodeSpan mode≤node mode origin transitions second := by
  have mult:=Nat.mul_le_mul_right (nodeSpan mode) (show first+1≤second by omega)
  simp only [Nat.add_mul,Nat.one_mul] at mult
  dsimp [node]
  omega
theorem transitions_apart (mode : Mode) (origin first second : Nat) (before : first<second) :
    transition mode origin first+transitionSpan mode≤transition mode origin second := by
  have mult:=Nat.mul_le_mul_right (transitionSpan mode) (show first+1≤second by omega)
  simp only [Nat.add_mul,Nat.one_mul] at mult
  dsimp [transition]
  omega
end SmcTuring.Appendix.Listing8GraphLayout
