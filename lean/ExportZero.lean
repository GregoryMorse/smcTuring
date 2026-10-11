module
public meta import SmcTuring.Appendix.ZeroImage
public meta import Lean
open Lean SmcTuring.Appendix
public meta def main : IO Unit := do
  let entry := ZeroImage.owner 0 0x80000000
  IO.println (Json.mkObj [("bytes", toJson (entry.bytes.map BitVec.toNat)),
    ("fields", toJson entry.fields), ("length", toJson entry.bytes.length)]).compress
