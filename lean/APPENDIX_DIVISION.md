# Listing 12 division proof and minimal repair

The published p.129 restoring-division algorithm and instruction order are
retained. M11 makes four local substitutions; M06 already fixes the counter
offset spelling. The signed `if(!mod)` scope and wrapped hexadecimal immediate
are correct as printed. The exact substitutions and positive repair proofs are
in [the minimal diff](errata/morse-2018-minimal.diff),
[the compact TeX errata](errata/morse-2018-errata.tex) and
[DivisionRepairs.lean](SmcTuring/Appendix/DivisionRepairs.lean).

[DivisionByteCorrect.correct](SmcTuring/Appendix/DivisionByteCorrect.lean)
constructs the entire terminating current-byte execution from one original
emitted image, entry PC, static ordered finite placement/capacity bounds and a
nonzero divisor. It proves the four signed/unsigned quotient/remainder results,
original input/EAX/ESP restoration, exact carry, zero displacement and endpoint
PC. Every reached DWORD write is to a complete code-operand field. Every
original byte outside the actual scratch/result fields is restored, including
input and DEFSTACK owners and arbitrary backing gaps. No future trace, target,
result, fetch or intermediate Ready invariant is a premise.

`reusable_correct` proves another invocation from the maintained image,
code-backed stack, current inputs and reset displacement, with arbitrary
scratch/result values. The returned protected-image, stack, input and reset
properties supply that setup again after restoring the entry PC.

Signed quotient truncates toward zero. Only MIN_INT/-1 is excluded when
asserting an in-range mathematical signed quotient; the wrapped word result
is still specified. Signed remainder has the dividend's sign when nonzero,
and the theorem includes MIN_INT/-1 with remainder zero.

The proof chain is explicit in [PROOF_LEDGER.md](PROOF_LEDGER.md):

- E98-E109 prove restoring arithmetic, signed magnitude including MIN_INT,
  actual initialization, the printed 23-instruction body and its 32-pass packed
  dividend/quotient/remainder invariant, then original result/sign selection.
- E110-E115 derive the actual counter-driven guard/body/exit schedule,
  code-backed CALL/continuations, original-input results, registers/CF/PC,
  word frame and write purity.
- E116-E120 check strict byte codecs and effects (including SUB imm32, SHR 31,
  ADC 0 and CF-preserving DEC), finite field refinement, mutable packet image,
  original packet placement and independent complete native packet comparison.
- E121-E129 derive the full original byte image, capacities, complete actual
  owner separation, current own operands and every data/CALL/continuation block
  trace from static geometry and the preserved evolving image.
- E130-E131 compose the continuous actual-PC loop and all-input original-image
  and reusable byte correctness. E132 matches the constructed whole original
  image, actual owner fields and its six admissibility premises against native.

The pure region, inactive input/result owners and DEFSTACK are ordered and
nonoverlapping; arbitrary gaps are supported. All emitted bytes and accessed
full DWORD words fit below `2^32`. Inactive logical view slots receive no
fictitious physical owner or allocation requirement. Actual scratch/input/
result fields derive their ownership and containment from the emitted layout.

The independently exported Lean image matches **344** unique native packets,
**2,532** complete bytes, **333** DIR32 symbol/section/addend sites and **91**
mode-owned complete disjoint fields. Pure packet counts are 65/65/103/98;
pure spans are 464/464/756/718 bytes. All 247 data lengths, twelve E8 operands,
exit delta 218 and back delta -324 modulo `2^32` match.

The minimally corrected x86 fixture passes **52,648** executions, with an
independent C++ integer oracle, input/all-GPR/ESP/CF/exterior-code checks and
repeated calls. Refresh with `python validation/run_division.py` after the
Lean audit and before `python validation/audit_evidence.py`.

E04 is complete for the selected nonfaulting, coherent-current-fetch x86 byte
machine and stated finite layout bounds. Full physical ISA/configuration/fetch
refinement remains E05/A01; the conceptual unbounded-machine theorem is a
separate checked result. The audit has **3,496** declarations and **370**
unique ledger IDs. No additional paper erratum was needed for this proof.
