# DWORD comparison and input selection

The comparison uses the published SUB/NEG/SBB pattern, followed by NOT in
Listing 8. It compares arbitrary 32-bit candidate and tape words, including
zero, the high-bit boundary and wraparound. In both native modes it produces
all ones exactly when the candidate equals the tape symbol; otherwise it
produces zero. Address width remains the mode's full width.

## Checked contracts

- Native.DwordArithmetic has 19 declarations for eight bare opcode forms:
  C7/05 store, 81/2D SUB, 81/35 XOR, 81/25 AND, F7/1D NEG, F7/15 NOT,
  83/1D SBB zero and 81/70/06 XOR at AX/RAX plus six. The decoder validates
  current packet length, fixed trailers and mutable operands. Effects include
  exact four-byte stores, PC, CF, preserved full AX/SP, exterior bytes and
  nonempty architectural writes. ModRM 05 is absolute in x86 and RIP relative
  in x64, measured from the complete six-, seven- or ten-byte instruction.
- Appendix.DwordComparison has 24 declarations for a packed 39-byte fixture:
  reset the mask, SUB the current tape symbol from the candidate, NEG the
  difference, SBB zero into the mask, then NOT. From one original byte image,
  the theorem derives all five current fetches after earlier stores, the exact
  negated scalar difference and equality mask, AX/SP/CF/PC, purity, byte frames
  and retained code. Eleven executable static checks are proved equivalent
  to its capacities, separation, code exclusions and signed RIP ranges.
- Appendix.InputSelection has 10 declarations proving the printed
  old-XOR-new, AND-match-mask and tape-XOR identities for all DWORDs. Patching
  the pending XOR operand derives its complete current seven-byte packet.
  The actual final base-addressed XOR step writes the new symbol on a match
  and retains the old symbol on a mismatch, preserving full AX/SP and every
  byte outside the tape word. This step requires the caller's full-width
  accumulator to contain the tape-node address.

These statements use the selected nonfaulting byte/state projection.
The physical configuration and instruction-fetch bridge stays explicit.

## Native binding

The packed fixture uses the same printed opcode forms in the same order,
with the existing DEFDATA32 scalar owner and an AND immediate as mask owner.
Each native mode passes 51,200 cases, including 1,280 matches, over eight
full-width accumulator seeds, forty DWORD candidates and symbols, both
entry CF values and repeated invocation. An independent equality oracle
checks the scalar, mask, full GPRs/SP, status flags, endpoint and every
unrelated code byte.

Actual Lean encoding matches forty live complete images, the initial image
and both owner packets: 1,619 compared bytes and seven COFF relocation
targets per architecture, including long-mode REL32, REL32_1 and REL32_4.
All eleven proved static checks pass, and actual x64 code/scalar/mask
addresses are above 4 GiB.

Reproduce with:

~~~powershell
python validation/run_lean.py
python validation/run_dword_comparison.py
python validation/audit_evidence.py
~~~

## Remaining composition

The packed fixture places reset immediately before SUB. In printed Listing 8,
the separately proved M13 input copy and M14 scalar owner occur between those
instructions. Their interleaved byte trace and live-field invariant still need
composition; this checkpoint does not certify the whole printed body.

The two wide cursor exchanges around inputupdate, the actual preceding
XOR/AND instruction trace and future-packet frames remain caller work.
Next compose those contracts before proceeding to direction/neighbor/state
selection, backedge/finalization and the whole loop invariant. No new paper
correction is introduced here.
