# Listing 6 DEFZERO: complete live-operand zeroing

The exact published p.125 line is
`labelname: xor [labelname + IMMOFFS], 0`. Table II defines
IMMOFFS=6 and CNSTFRC32=0x80000000. The minimum M09 correction is
`labelname: xor SZW32 ptr [labelname + IMMOFFS], CNSTFRC32`.
The operation remains one self-targeted XOR. The explicit DWORD type and
existing force-32-bit constant select its intended complete operand word.

[ZeroImage.lean](SmcTuring/Appendix/ZeroImage.lean) contains 18 positive
kernel-checked results. The ten-byte 81/35 packet owns its imm32 at PC+6;
its opcode and address are protected. The actual current-byte fetch loads
that same word v as its immediate and reads v at the destination, giving
v XOR v = 0 for every initial bit pattern. `correct` constructs the actual
one-event trace, complete DWORD zero store, EAX/ESP restoration, CF=false,
next PC=start+10, code ownership, reusable Intact image and exact exterior
byte frame. Its only execution premises are the intact original packet,
entry and complete extent capacity; no future fetch or result is supplied.
`original_image_correct` derives that invariant from the actual initializer.
`reentry_intact` and `reentry_trace` prove actual live fetching after the
immediate becomes zero; the packet remains the original full-width encoding.
An unchanged zero still has the checked four-byte architectural write.

The native macro [listing6_smc.inc](../smcTuring/listing6_smc.inc) expands the
corrected line with the published constant values. The production macro is
included directly by the regression fixture. `validation/run_zero.py` builds
with MASM and MSVC /W4 /WX on both x86 and x64, and retains the typed printed
baseline separately: MASM selects 83/35 with a single zero immediate. The
corrected full packet matches the actual Lean byte codec, actual x86 absolute
address or x64 RIP-relative displacement -4, complete own-operand offset and
host return boundary. The emitted imm32 becomes zero at runtime without
reassembly, so it never shortens to the imm8 form.

Each architecture passes **9,312 executions for 582 live words**, including
zero, every one-bit/complement pattern, boundary and random words, both CF
states, arbitrary accumulator seeds (full 64-bit RAX in long mode), two
successive calls per case, all observed GPRs/SP/CF and every exterior byte.
Host initialization, CALL/RET and observation remain outside the pure event.
The universal kernel contract is for the selected x86 byte projection; the
x64 native result checks the corresponding literal encoding and finite cases.
Full physical ISA/fetch/configuration refinement remains E05.

M09 is included immediately in the compact two-page errata and exact diff,
with five individually audited positive correction references. The main
unbounded computation/purity proof and corrected native construction retain
their existing scope. Remaining E01 work is Listing 6's code/data conversion
and the associated template-copy/relocation contracts in P04.

Reproduce from the repository root:

```powershell
python validation/run_lean.py
python validation/run_zero.py
python validation/audit_errata.py
python validation/audit_evidence.py
```

When the full Lean source manifest changes, refresh the other native reports
as specified by validation/README.md before the aggregate audit.
