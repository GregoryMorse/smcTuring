module
public meta import SmcTuring.Native.StringMacroTrace
public meta import Lean
open Lean SmcTuring.Native
public meta def packetLengths (mode : Mode) : Nat -> List LittleEndian.Byte -> Option (List Nat)
  | 0, _ => none
  | fuel+1, bytes =>
    if bytes.isEmpty then some [] else do
      let count <- StringForm.lengthOfBytes mode (bytes.take 3)
      if count = 0 ∨ bytes.length < count then none else do
        let form <- StringForm.fetch mode (fun position => bytes[position]?.getD 0) 0
        if StringForm.encode mode form = bytes.take count then
          let rest <- packetLengths mode fuel (bytes.drop count)
          return count :: rest
        else none
public meta def rows (mode : Mode) : List String -> List Json
  | start :: source :: destination :: size :: rest =>
    let pc := start.toNat!
    let count := size.toNat!
    let bytes := StringCodec.bytes mode pc source.toNat! destination.toNat! count
    let body := StringPlan.bytes mode count
    let program := StringProgram.forms mode pc source.toNat! destination.toNat! count
    Json.mkObj [("start",toJson pc), ("size",toJson count),
      ("sourceField",toJson (StringCodec.sourceField mode pc)),
      ("destinationField",toJson (StringCodec.destinationField mode pc)),
      ("body",toJson (StringCodec.bodyStart mode pc)),
      ("bodyEnd",toJson (StringCodec.bodyEnd mode pc count)),
      ("end",toJson (StringCodec.endpoint mode pc count)),
      ("widths",toJson (StringPlan.widths mode count)),
      ("bodyBytes",toJson ((StringPlan.bytes mode count).map BitVec.toNat)),
      ("bytes",toJson (bytes.map BitVec.toNat)),
      ("programBytes",toJson ((program.map (StringForm.encode mode)).flatten.map BitVec.toNat)),
      ("programInstructions",toJson program.length),
      ("prefixBytes",toJson ((StringSetupTrace.bytes mode pc source.toNat! destination.toNat!).map BitVec.toNat)),
      ("decodedPacketLengths",toJson (packetLengths mode (bytes.length+1) bytes)),
      ("decodedBodyLengths",toJson (packetLengths mode (body.length+1) body))] :: rows mode rest
  | _ => []
public meta def main (args : List String) : IO Unit := do
  let mode := if args[0]! == "x64" then Mode.x64 else Mode.x86
  IO.println (toJson (rows mode args.tail)).compress
