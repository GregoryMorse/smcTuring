# Listing 8 cursor update

The literal `XCHG; XOR DWORD PTR [AX+6], immediate; XCHG` fragment is now
proved in both modes: 19 bytes in x86 and 21 bytes in x64. The x64 exchanges
use REX.W and preserve the full cursor pointer and entry RAX; the tape write
remains exactly four bytes. The proof uses one deterministic current-memory
decoder across the mixed instruction widths.

For arbitrary old/new DWORD symbols and a Boolean match decision, the XOR
operand is `(old xor new) and (if chosen then all-ones else zero)`. The final
symbol is new exactly when chosen. The complete final memory is the initial
memory with only that tape operand replaced. Full AX, the cursor word and SP
are restored, CF is false, the PC advances to the proved endpoint, and the
complete code image remains intact for reuse.

`CursorImage.trace` derives every fetch from the original finite image and
preceding actual stores. `CursorImage.correct` combines that trace and effect.
`CursorImage.pure` accounts for all three nonempty writes: the full cursor
operand, the tape DWORD operand, and the restored cursor operand. The caller
must supply code-field ownership for those two locations.

The static contract requires address capacity, cursor/tape disjointness,
both writable fields outside this fragment, and signed RIP-relative reach in
x64. Cursor initialization is an explicit current full-word read premise.
These hypotheses must be discharged from the complete Listing 8 layout.

The six modules contribute 63 declarations in the local kernel audit,
`validation/cursor_lean.json`, under Lean 4.35.0-rc3. Whole-project freshness is pending. The native fixture now passes 204,800
cases per mode, with complete packet/COFF binding, all eight proved static
checks, independent symbol/full AX/cursor/GPR/SP/defined flag/endpoint/exterior
code/reuse checks and actual x64 code/cursor/tape addresses above 4 GiB.
AF after XOR is undefined and excluded. The actual preceding XOR/AND patch
trace, interleaved comparison/helper/owner setup, node initialization and
complete loop/finalization remain separate ledger gates. No additional paper
erratum is established by this checkpoint.

Reproduce the local evidence from the repository root:

```powershell
python validation/limited_run.py --report validation/.build/memory-cursor-current.json -- python validation/run_cursor_lean.py
```

The runner verifies the exact rc3 compiler, the complete module closure, the
build configuration and artifact hashes, all 63 audit names and their standard
axiom inventories. It refreshes only the local evidence, preserving the whole-library gate above.
Run the matching native and freshness checks serially with:

```powershell
python validation/limited_run.py --report validation/.build/memory-cursor-native.json -- python validation/run_cursor.py
python validation/limited_run.py -- python validation/audit_cursor.py
```

The native fixture uses MOFFS full-width cursor ownership and a C7/05 DWORD
tape owner. The host setup, capture, flush and return lie outside the pure block.
The next step derives the pending XOR immediate from the actual preceding
XOR/AND instructions and composes the complete Listing 8 transition body.
