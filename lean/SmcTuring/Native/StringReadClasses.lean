module
public import SmcTuring.Native.StringReadWindows
public import SmcTuring.Native.StringMixed
public import SmcTuring.Native.StringStoreWrites

public section
namespace SmcTuring.Native.StringReadClasses

theorem mixed (mode : Mode) (form : MixedDword.Form mode) :
    StringReadWindows.Local mode (StringStoreWrites.liftDword mode (StringMixed.canonical mode form)) := by
  cases form with
  | arithmetic form => cases mode <;> cases form <;> trivial
  | copy form => cases mode <;> cases form <;> trivial
  | wideExchange d => trivial

theorem copy (mode : Mode) (form : DwordCode.Form mode) :
    StringReadWindows.Local mode (StringStoreWrites.liftDword mode (StringDwordCopy.copy mode form)) := by
  cases mode <;> cases form <;> trivial

theorem native (mode : Mode) (form : Native.Form mode) (localRead : StringReadWindows.NativeLocal mode form) :
    StringReadWindows.Local mode (StringStack.native mode form) := by
  cases mode <;> cases form with
  | memory operation d => cases operation <;> first | trivial | exact False.elim localRead
  | moffs address => trivial
  | exchangeIndirect => trivial
  | callRelative d => trivial

theorem negation (mode : Mode) (d : BitVec 32) :
    StringReadWindows.Local mode (.previous (StringControl.negation mode d)) := by
  cases mode <;> trivial

theorem add (mode : Mode) (d : BitVec 32) (value : LittleEndian.Byte) :
    StringReadWindows.Local mode (.addSmall d value) := True.intro

end SmcTuring.Native.StringReadClasses
