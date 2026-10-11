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
and uses the individual existing proofs; it has no holes. Comparator, NanoDa
and Lean's kernel accept the selected declarations under the standard three
axioms. See [the audit](PALOMAR_AUDIT.md) for source bindings and remaining gates.

| Selected declaration | Meaning and scope |
| --- | --- |
| `PalomarSMC.mathematical_result` | Conjunction of the four result definitions below; each is proved from the existing construction. |
| `SmcTuring.CorrectedPaper.Unbounded` | For every finite TM and finite input, the initialized pure SMC trace preserves halting and divergence and writes code at every computational instruction. Source divergence implies arbitrarily late fetched-code changes. A constructed walker also changes unboundedly many distinct fields. |
| `SmcTuring.CorrectedPaper.FourMov` | One fixed static four-register MOV body and unconditional backedge simulate every finite TM/input, preserving halt/divergence. This is Stephen Dolan's foundation, distinct from instruction-level pure SMC. |
| `SmcTuring.CorrectedPaper.EffectiveInterpreter` | A constructed finite numbered interpreter receives only an encoded finite machine/input. It preserves halt/divergence and purity; terminal output has a positive journal and library/source tape representation. |
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
fields are an additional witness property. The finite initializer and fixed
control graph do not take future execution information as input.

Native head observation is before cleanup. Full seeded AX restoration is at
the epilogue boundary, with the later x64 M20 effect explicitly retained.
Native proofs assume present object/entry agreement and disclosed local ISA,
mapping, capacity, reach and ABI conditions. No whole CPU/OS or physical RET
stopping theorem is part of this registry statement.

The 984-line / 60,700-byte Challenge satisfies the hard 1,000-line / 100 KiB
limits and exceeds the preferred 300-line / 32 KiB surface. That readability
warning is disclosed. Official full preflight and editorial review are still
required on an exact public commit. No submission or registration is claimed.
