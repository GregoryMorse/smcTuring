module
public import SmcTuring.Appendix.Listing8FailComparisonEffects
public import SmcTuring.Native.StringInitTrace
public import SmcTuring.Native.DwordPackets
public import SmcTuring.Appendix.Listing8CallSelection

public section
namespace SmcTuring.Appendix.Listing8FailureLayout
open Native
structure Layout where
  start : Nat
  cursor : Nat
  sentinel : Nat
  begin : Nat
@[expose] def ownerPC (l : Layout) := l.start+10
@[expose] def source (mode : Mode) (l : Layout) := StringInit.field mode (ownerPC l)
@[expose] def comparisonPC (mode : Mode) (l : Layout) := ownerPC l+StringCodec.initialSize mode
@[expose] def notPC (mode : Mode) (l : Layout) := comparisonPC mode l+6*WordMemoryArithmetic.size mode+7
@[expose] def storePC (mode : Mode) (l : Layout) := notPC mode l+6
@[expose] def andPC (mode : Mode) (l : Layout) := storePC mode l+10
@[expose] def xorPC (mode : Mode) (l : Layout) := andPC mode l+10
@[expose] def endPC (mode : Mode) (l : Layout) := xorPC mode l+10
/-- The printed JUMP's stack exchange prefix is six bytes on x86; long mode
uses XCHG, ADD imm8, XCHG (7+8+7). Execution of that prefix is separate work. -/
@[expose] def stackSpan (mode : Mode) := if mode=.x86 then 6 else 22
@[expose] def callPC (mode : Mode) (l : Layout) := endPC mode l+stackSpan mode
@[expose] def mask (mode : Mode) (l : Layout) := xorPC mode l+6
@[expose] def original (mode : Mode) (l : Layout) := Listing8CallSelection.displacement (callPC mode l) l.begin
@[expose] def comparison (mode : Mode) (l : Layout) : Listing8FailComparison.Layout :=
  ⟨comparisonPC mode l,l.cursor,source mode l,mask mode l⟩
@[expose] def reset (mode : Mode) (l : Layout) := DwordArithmetic.located mode (.store 0 0) l.start (mask mode l)
@[expose] def post (mode : Mode) (l : Layout) : List DwordPackets.Site :=
  [⟨notPC mode l,.complement,mask mode l⟩,⟨storePC mode l,.store,andPC mode l+6⟩,
    ⟨andPC mode l,.bitAnd,mask mode l⟩,⟨xorPC mode l,.bitXor,callPC mode l+1⟩]
@[expose] def force : BitVec 32 := BitVec.ofNat 32 0x80000000
@[expose] def postBytes (mode : Mode) (l : Layout) :=
  DwordArithmetic.encode (DwordPackets.form mode ⟨notPC mode l,.complement,mask mode l⟩ 0) ++
  DwordArithmetic.encode (DwordPackets.form mode ⟨storePC mode l,.store,andPC mode l+6⟩ (original mode l)) ++
  DwordArithmetic.encode (DwordPackets.form mode ⟨andPC mode l,.bitAnd,mask mode l⟩ force) ++
  DwordArithmetic.encode (DwordPackets.form mode ⟨xorPC mode l,.bitXor,callPC mode l+1⟩ force)
@[expose] def bytes (mode : Mode) (l : Layout) :=
  DwordArithmetic.encode (reset mode l) ++ StringInit.bytes mode (ownerPC l) l.sentinel ++
    Listing8FailComparison.bytes mode (comparison mode l) ++ postBytes mode l

theorem comparison_end (mode : Mode) (l : Layout) : Listing8FailComparison.endPC mode (comparison mode l)=notPC mode l := rfl

theorem source_end (mode : Mode) (l : Layout) : source mode l+mode.wordBytes=comparisonPC mode l := by
  cases mode <;> simp [source,StringInit.field,comparisonPC,StringCodec.fieldOffset,StringCodec.initialSize,Mode.wordBytes]

theorem positions (mode : Mode) (l : Layout) :
    comparisonPC mode l=l.start+(if mode=.x86 then 20 else 37) ∧
    notPC mode l=l.start+(if mode=.x86 then 63 else 86) ∧
    mask mode l=l.start+(if mode=.x86 then 95 else 118) ∧
    endPC mode l=l.start+(if mode=.x86 then 99 else 122) ∧
    callPC mode l=l.start+(if mode=.x86 then 105 else 144) := by
  cases mode <;> simp [comparisonPC,ownerPC,notPC,mask,xorPC,andPC,storePC,endPC,callPC,stackSpan,
    StringCodec.initialSize,WordMemoryArithmetic.size,wordPrefix,Nat.add_assoc] <;> omega

theorem post_length (mode : Mode) (l : Layout) : (postBytes mode l).length=36 := by
  cases mode <;> rfl

theorem bytes_length (mode : Mode) (l : Layout) : (bytes mode l).length=if mode=.x86 then 99 else 122 := by
  rw [bytes,List.length_append,List.length_append,List.length_append,
    post_length,Listing8FailComparison.bytes_length]
  have owner : (StringInit.bytes mode (ownerPC l) l.sentinel).length=StringCodec.initialSize mode :=
    StringCodec.initial_length mode _ _ _
  rw [owner,DwordArithmetic.encode_length]
  cases mode <;> rfl

theorem post_chain (mode : Mode) (l : Layout) : DwordPackets.Contiguous (notPC mode l) (post mode l) := by
  simp [post,DwordPackets.Contiguous,DwordPackets.size,DwordPackets.raw,DwordArithmetic.length,
    storePC,andPC,xorPC,Nat.add_assoc]

theorem post_span (mode : Mode) (l : Layout) : ((post mode l).map DwordPackets.size).sum=36 := rfl

theorem printed_displacement (mode : Mode) (l : Layout) (dollar : Int) :
    (dollar-(Listing8CallSelection.failPC (callPC mode l) : Int))-(dollar-(l.begin : Int))=
      Relocation.delta (Listing8CallSelection.failPC (callPC mode l)) l.begin :=
  Listing8CallSelection.printed_expression dollar (callPC mode l) l.begin

end SmcTuring.Appendix.Listing8FailureLayout
