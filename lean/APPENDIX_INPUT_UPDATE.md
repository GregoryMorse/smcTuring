# Printed Listing 8 input update

The exact five instructions at lines 555-562 of the cached paper are now
modeled and proved: DWORD XOR into the pending immediate, DWORD AND into
that immediate, full-width cursor XCHG, DWORD XOR at AX+6, and full-width
cursor XCHG back. They occupy 39 bytes in x86 and 41 bytes in x64.

InputUpdateTrace.trace derives every opcode-based current fetch from a single
original finite byte image, including the later XOR after its operand is
changed twice. The initial pending operand is the old tape symbol; the first
instruction computes old XOR new, and the second applies the zero/all-ones
match mask. The final symbol is new on a match and old otherwise.

InputUpdateTrace.effect proves the complete final state. Full AX and SP are
preserved, the full-width cursor word is restored, CF is clear and PC reaches
the exact endpoint. Only the computed pending immediate and selected tape
DWORD differ from the initial memory. The whole resulting image is retained
and every one of the five instructions performs a nonempty owned code write.
The ownership contract accounts for four-byte immediates separately from the
four/eight-byte cursor field.

The caller must establish the initialized full cursor pointing to the tape
instruction, the initial pending operand equal to the live tape symbol, the
correct match mask, valid capacity/relative reach and actual instruction-field
ownership. Ten executable layout checks are proved equivalent to the static
contract. The printed earlier M13 copy and comparison provide the symbol and
mask; composing their actual interleaving remains the next proof stage.

The four new modules contribute 38 locally kernel-audited declarations with
only standard axioms. Their 31-module dependency closure is checked under
Lean 4.35.0-rc3. Each native architecture passes 204,800 cases over sixteen
full accumulator seeds, forty old/new symbols, both choices/entry CFs and
repeat invocation after current-symbol reinitialization. Full AX/cursor/GPR/SP,
defined XOR flags/endpoint/symbol/pending operand/exterior code checks pass.
AF after XOR is undefined and excluded. x64 code/cursor/tape/operand addresses
are above 4 GiB.

All 41 prepared complete images, the original force-wide object image and both
owners (1,653/1,742 bytes per mode), five COFF relocations and ten static checks
match the actual Lean encoders. The printed CNSTFRC32 placeholder forces the
correct immediate width; native execution supplies the proved match mask.
Host setup, observation, source-copy reinitialization, flush and return are
outside the five-instruction purity claim.

Reproduce the local checks serially from the repository root:

```powershell
python validation/limited_run.py --report validation/.build/memory-input-update-local.json -- python validation/run_input_update_lean.py
python validation/limited_run.py --report validation/.build/memory-input-update-native.json -- python validation/run_input_update.py
python validation/limited_run.py -- python validation/audit_input_update.py
```

The memory cap remains 1.5 GB, with resident monitoring and one Lean thread.
The goal stays active: full printed comparison/helper/owner setup, generalized
node/direction/state selection, backedge/loop/finalization and whole-project
fresh provenance remain open. This checkpoint establishes no additional
erratum; preserve the compact M01-M14 correction.


## Verified import reduction and bounded whole-build status

The unchanged memory-update theorems, the required core omega tactic and
Function.Injective interface compile with Init alone. SmcTuring/Memory.lean
now imports Init instead of all Std. Both local proof audits and both native
bindings were refreshed after that production change: 63 cursor declarations
and 38 full-input-update declarations remain checked, with current source,
cache and artifact hashes. Across those two fragments, 819,200 native cases pass.

The current input-update native peak is 630,366,208 bytes committed and
373,358,592 bytes sampled resident; the cursor native peak is 626,995,200 /
370,941,952 bytes. The Windows allocation limit remains 1.5 GB and checks remain
serial. The launcher now preserves Unicode output and records launcher errors.

At that earlier stage, the whole-library build was incomplete. An initial serial pass compiled
75 modules before the Mathlib TM0 adapter hit the cap. After reducing the
foundation import, a targeted adapter recheck still hit the same cap while
loading Lean/Elab/Tactic/Grind/Main.olean.private. Both failed commands are
terminal, with logs in validation/.build/full-bounded-build.log and
mathlib-adapter-bounded.log. Do not treat either as a passing whole-library
snapshot or retry without the cap. Resolve the heavy import path while
continuing the printed interpreter obligations. The import path was later
resolved; the fresh Linux proof audit passed on 2026-10-06. Bounded Windows
validation and the full printed interpreter obligations remain open.
