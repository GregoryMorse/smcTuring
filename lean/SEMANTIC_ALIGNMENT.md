# Statement and source alignment

This account checks the meanings of the selected declarations after the semantic
revision. Kernel acceptance establishes their proofs under these definitions;
it does not by itself establish agreement with a publication or its description.
Acceptance runs and exact source bindings are recorded separately.

| Selected surface | Definition-level obligation | Positive proof and description |
| --- | --- | --- |
| `CorrectedPaper.Unbounded`: TM simulation | Every finite machine/input has halt and divergence equivalences, reachable instruction-level code-write purity, and arbitrarily late actual changes on divergence. | `Concrete.pure_infinitely_smc_universality`; the fixed control graph, initial representation and finite scans are constructed from source data. |
| `CorrectedPaper.Unbounded`: distinct fields | Beyond every address bound, an actual changed field has a reached owner PC at the next instruction time, and fetch decodes that field's current word as the owning STORE operand. | `Concrete.active_unbounded_fields` and `pure_unbounded_smc_witness`; the same infinite trace is also pure and total. This is stronger than the retained `UnboundedOwnedFields` supporting property. |
| `CorrectedPaper.FourMov` | One static 2,252-MOV body has four available registers, halt/divergence equivalences, and an explicit deliberate zero-trap equivalence for every finite machine/input. | `Four.four_register_mov_certified_simulation`, `zero_trap_halting_iff`. The successful prefix and exact trapping load are conclusions, not supplied execution assumptions. |
| `CorrectedPaper.EffectiveInterpreter` | A finite numbered interpreter receives only encoded finite machine/input; terminal output has a positive journal and tape representation. | `Effective.terminal_search_pure_smc`; initializer definitions are retained, rather than replaced with abstract oracle assumptions. |
| `CorrectedPaper.Observations` | Every finite actual source run has a boundary on its own initialized pure trace, with the entire integer-indexed tape and head represented. | `CorrectedPaper.observations`, `Concrete.tm_run_correct`; the reached states and trace witnesses are conclusions. |
| `Encoding.zigzag_injective` | The explicit integer-to-natural encoding is injective. | Existing direct proof; unchanged definition and description. |
| `Concrete.data_owner`, `metadata_owner` | Each qualifying field has a header decoding that mutable field as the STORE operand. | Constructive placement proofs. Placement alone is not claimed to establish execution; the distinct-field predicate additionally requires execution on its trace. |
| `PalomarSMC.mathematical_result` | Exactly the conjunction of the four selected result definitions. | `Solution.lean` uses their individual proved results; protected comparison must agree with the independent `Challenge.lean`. |

## Deliberate MOV stopping

[Dolan's paper](https://harrisonwl.github.io/assets/courses/malware/spring2017/papers/mov-is-turing-complete.pdf),
Section 5, page 4, stops by attempting an invalid memory read at address zero.
It does not specify a successful read returning zero. The previous metadata
sentence saying that invalid reads returned zero was incorrect.

The normalized model distinguishes a valid cell `.address c` from the two
offset values `.offset false` and `.offset true`. Valid cell addresses can be
encoded numerically as `2 * (c + 1)`; the offsets encode zero and one. Thus the
valid scratch cell `.address 0` is distinct from the invalid zero pointer.
Only a cell base and a valid offset form a valid dereference; an invalid
dereference returns execution failure `none`. The four-register ring compiler
preserves this distinction and shifts valid heap cells by 13.

`ZeroTrapHalts` exhibits successful whole loop bodies and a successful prefix
of the next body. Immediately afterward the literal instruction
`.load .a .a .b` has both operands `.offset false`, and its execution is `none`.
The first eight guard MOVs succeed at the sentinel; the compiled operand-fetch
prefix succeeds too. Finite scan progress reaches that sentinel when the source
TM halts. Compiler fault reflection and source halt reflection prove the reverse
implication. Consequently a generic unrelated invalid address is insufficient
as the certificate of a simulated halt. A zero-return total-load machine is a
different model, and no result about its stopping is asserted.

Dolan's source adaptations D01–D05 remain explicitly disclosed in
[the standalone guide](DOLAN_FORMALIZATION.md). This strengthening does not
claim the printed assembly executes byte for byte without those corrections.

## Changed fields are executed operands

`UnboundedChangedFields` now requires, for each bound, a field and change time,
an actual `FieldChangeAt`, and a state reached at `time + 1` whose PC is
`image.templatePC field`. Fetch in that state must produce
`.store (state.memory field)`: the current changed word is decoded as the
owning instruction's destination operand. Mere membership in `image.codeField`
or fetching the writer cannot establish this additional clause.

The concrete witness uses the same image as the TM simulation. Its uniform
negative-PC storage blocks have spacing eight, while the finite nonnegative
TM control graph is retained. Every header has sequential next PC `pc + 1`;
the final CALL performs the explicit control transfer. For cycle `n`, field
`f = 40 + n` initially contains `f`, and the accumulator contains `f - 1`:

1. EXCHANGE changes field `f` to `f - 1` and loads accumulator `f`.
2. The owning STORE is fetched immediately, decoding destination `f - 1`.
3. EXCHANGE of the stack pointer with its code-backed reset field.
4. STORE of the stack pointer restores that reset field.
5. CALL to the next block writes its return PC to a code-backed return field.

The invariant frames every not-yet-visited field. Five-step blocks compose into
one infinite pure trace; actual changes occur at times `5 * n`. Owners fetched
at `5 * n + 1` belong to distinct fields beyond every finite address bound.
All write footprints, including CALL's stack write, are code-backed.

`Effective.fixed_headers_code_correct` proves that the primitive-recursive
encoded decoder is this exact image, including the new storage EXCHANGE,
stack-reset instructions and CALL target. `fixed_headers_code_primrec` and the
effective interpreter's terminal simulation are checked for the updated layout.
The generated unbounded storage family is not an oracle for fetch.

The unbounded template family and memory have a finite computable description;
they are an ideal unbounded image, not a finite physical executable with
infinitely many preallocated instructions. The initializer is the elementary
rule `memory p = p`, except at one fixed stack-reset field. No future execution
information is encoded in this rule. Bounded x86/x64 realization remains a
separate conditional result. The older tape walker proves an owned-field
property and remains supporting material; it is not the witness for the new
executed-owner claim.

## Reproduction and release checks

Lean remains `4.35.0-rc3`, compiler commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`. The current Mathlib dependency is
`5e043698502894993991089b2dd893867c0db5c2`. Historical acceptance at
`1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4` used
`302343bb9a029d4edab4f736703f0736896c1b64`; aligned acceptance at
`a97fbd690b4051463a3b3fe86b5823823aa91bac` used the current pin. Those runs
cannot certify the strengthened definitions in this revision.

Affected-module checks use source-bound artifact reuse and a fresh selected
axiom audit. The [frozen candidate acceptance](acceptance/semantic-revision.json) passes
the full proof/native audit, unmodified Palomar mechanical preflight and
unmodified Challenge rendering.
The Challenge includes the actual stopping and ownership predicates and must
stay below the hard 1,000-line / 100 KiB limits. Mechanical and semantic claims
are reported separately; no registry acceptance is inferred from CI success.
