# Selected Palomar statement

The selected result is the mathematical construction from Gregory Morse's
2018 paper, adapted by the proved M01-M20 minimal errata. The user selected
this scope on 2026-10-11. Conditional native/COFF theorems remain checked
supporting material in this development. Their proofs are not selected
registered declarations.

`Challenge.lean` is an independent statement using only pinned Mathlib/core
imports. It retains the actual machine semantics, initializer, finite source
data and run predicates. Its four theorem holes are deliberate. Its result
definitions have their intended values. `Solution.lean` imports the development
and uses the individual proofs; it has no holes. Acceptance receipts apply to
their exact tested definitions and commits. See [the execution revision ledger](EXECUTION_REVISION_LEDGER.md)
and [the audit](PALOMAR_AUDIT.md) for current and historical source bindings.

| Selected declaration | Meaning and scope |
| --- | --- |
| `PalomarSMC.mathematical_result` | Conjunction of the four result definitions below; each is proved from the existing construction. |
| `SmcTuring.CorrectedPaper.Unbounded` | For every finite TM and finite input, the initialized pure SMC trace preserves halting and divergence and writes code at every computational instruction. Source divergence implies arbitrarily late changes caused by fetched instructions. The selected fixed `activeInitial` has literal registers and identity integer memory, explicitly proved primitive recursive; its traversal of the same image changes unboundedly many distinct fields and fetches each field's owning STORE on the very next step, reading its changed operand. |
| `SmcTuring.CorrectedPaper.FourMov` | One fixed 2,252-instruction four-register MOV body and unconditional backedge simulate every finite TM/input, preserving halt/divergence. Every source halt also reaches a certified literal load with zero base and zero offset, which traps. Invalid reads stop execution; they do not return zero. This follows Dolan Section 5's intentional invalid-zero-address read. |
| `SmcTuring.CorrectedPaper.EffectiveInterpreter` | A constructed finite numbered interpreter receives only an encoded finite machine/input. It preserves halt/divergence and purity. Every terminal journal is on a configuration actually reached by this numbered interpreter from the exact encoded input and satisfying its halt equation. That same configuration has the library/source tape representation in the actual SMC terminal state. |
| `SmcTuring.CorrectedPaper.Observations` | Every actual finite source run has a corresponding boundary on the same initialized pure trace, with the logical head and the whole integer-indexed tape represented. Trace witnesses are conclusions. |
| `SmcTuring.Dolan.Encoding.zigzag_injective` | The explicit sign/interleaving encoding of integer tape positions into natural addresses is injective. |
| `SmcTuring.SMC.Concrete.data_owner` | Every nonnegative data field belongs to the explicit executable storage template whose fetch reads that mutable operand field. |
| `SmcTuring.SMC.Concrete.metadata_owner` | Each of the 38 fixed metadata fields belongs to its explicit executable storage template. |

The ideal machine has unbounded integer addresses and values; finite x86/x64
hardware is a separately conditional bounded realization. `TM.Machine` contains
a blank symbol and a start state, so an inhabited machine has positive alphabet
and state counts. Zero-count quantification has no such machine; empty inputs
and immediate halting remain genuine cases. Halting means a reached missing
transition, divergence means every finite prefix exists, and unbounded changed
fields are an additional witness property. The distinct-field initializer is
`acc = 39`, `stack = 0`, `pc = owner 40 - 1`, `carry = false`, and
`memory p = p` everywhere. It is named directly in the statement, with the
positive `Primrec` memory clause; no arbitrary initial-memory witness is chosen. Its five-instruction cycles visit fields
`40 + n`; all headers have sequential next PC, and an actual CALL supplies the
cycle transfer. The uniform storage region and finite control graph do not take
future execution information as input.

In the MOV word encoding, `.offset false` is numeric zero and `.offset true`
is numeric one. `.address cell` denotes a valid cell at normalized numeric
address `2 * (cell + 1)`. In particular `.address 0` is valid scratch storage;
it is not the invalid numeric address zero. The target compiler shifts valid
heap cells by 13 and leaves the offset tags unchanged. `ZeroTrapHalts` exhibits
successful completed loop bodies and a successful instruction prefix, then
the actual `.load .a .a .b` with both operands `.offset false` and execution
result `none`. Halt reflection excludes unrelated compiler faults on represented
runs. A total machine returning zero on invalid reads is outside this claim.

Native head observation is before cleanup. Full seeded AX restoration is at
the epilogue boundary, with the later x64 M20 effect explicitly retained.
Native proofs assume present object/entry agreement and disclosed local ISA,
mapping, capacity, reach and ABI conditions. No whole CPU/OS or physical RET
stopping theorem is part of this registry statement.

The Challenge must satisfy the hard 1,000-line / 100 KiB limits. Its surface
exceeds the preferred 300-line / 32 KiB size; that readability warning is
disclosed. Official full preflight and editorial review remain distinct gates
on an exact public commit. No registration is claimed.
