module
public meta import SmcTuring.Native.ImageInitialization
public meta import Lean

open Lean SmcTuring.Native
open RoleInitialization LayoutPass

meta def readerName : Reader -> String
  | .register reg => s!"R{(SmcTuring.Dolan.Four.slot reg).val}"
  | .candidate => "Candidate" | .boundary => "BoundaryValue" | .zero => "ZeroValue"
  | .resume => "ResumeValue" | .terminal => "TerminalValue" | .mask => "SMCMask"
  | .offsetZero => "OffsetZero" | .offsetOne => "OffsetOne" | .pointerWord => "PointerWord" | .pointer => "Pointer"
meta def fieldName : Field -> String
  | .top => "StackTop" | .slot => "ReturnField" | .candidate => "Candidate" | .boundary => "BoundaryValue"
  | .zero => "ZeroValue" | .resume => "ResumeValue" | .terminal => "TerminalValue" | .mask => "SMCMask"
  | .scratch => "Scratch" | .selected => "Selected" | .loop => "PureLoopTarget" | .offsetZero => "OffsetZero" | .offsetOne => "OffsetOne"

meta def layoutJson (mode : Mode) (request : Request) : Json :=
  let layout := roleLayout mode request
  let source := match KernelImage.compile mode (roles mode request []) (kernelStart mode request) SmcTuring.Dolan.Mov.kernelProgram with
    | none => []
    | some (blocks, _) => blocks.map (BlockImage.start mode)
  Json.mkObj [
    ("architecture", toJson (if mode = .x64 then "x64" else "x86")),
    ("origin", toJson request.origin), ("host_span", toJson request.hostSpan),
    ("terminal_offset", toJson request.terminalOffset), ("cells", toJson request.cells),
    ("base_guard", toJson (baseGuardStart mode request)), ("offset_guard", toJson (offsetGuardStart mode request)),
    ("kernel", toJson (kernelStart mode request)), ("backedge", toJson (backedgeStart mode request)),
    ("boundary", toJson (boundaryStart mode request)), ("terminal", toJson layout.terminalPC),
    ("metadata_start", toJson (metadataStart mode request)), ("metadata_limit", toJson (metadataLimit mode request)),
    ("grid", toJson (gridBase mode request)), ("heap", toJson (Layout.heapBase mode (gridBase mode request))),
    ("source_positions", toJson source),
    ("readers", toJson (readers.map fun role => Json.mkObj [
      ("name", toJson (readerName role)), ("entry", toJson (readerPosition mode layout role)),
      ("operand", toJson (readerPosition mode layout role + ReaderImage.labelOffset mode)),
      ("initial", toJson (readerValue mode layout role).toNat)])),
    ("fields", toJson (fields.map fun role => Json.mkObj [
      ("name", toJson (fieldName role)), ("operand", toJson (fieldPosition mode layout role)),
      ("initial", toJson (fieldValue mode layout role).toNat)]))]

#eval IO.println (toJson [layoutJson .x86 ⟨11, 21, 9, false, 4096⟩,
  layoutJson .x64 ⟨12, 23, 10, false, 4096⟩]).compress
