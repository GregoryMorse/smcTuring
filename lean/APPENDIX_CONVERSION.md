# Listing 6 full-width code/data conversion

The printed USEWORD expansion is XCHG accumulator/source; MOV destination/
accumulator; XCHG accumulator/source. The helper uses the original source
word for the destination and restores the entire source byte range and the
accumulator. This is proved for selected x86 (four bytes) and x64 (eight bytes)
execution, including every current-byte fetch, unchanged stack/carry, exact
endpoint, reusable helper image and every original byte outside the destination.

`Native/ConversionLayout.lean` derives the complete actual encoded three-packet
fragment and geometry: 17 bytes on x86, 21 on x64. Source and destination are
complete disjoint fields outside the helper, before or after it. Complete word
capacities and signed x64 RIP relocations are explicit initial resources.
`ConversionEffects.lean` proves the exact byte-memory equation;
`ConversionImage.lean` constructs the live trace and original-image/re-entry
contracts. No future trace or intermediate effect is a proof premise.

`ConversionOperands.lean` proves actual destination MOFFS decoding of the copied
word, as well as restoration of a decodable source owner. `ConversionOwnership.lean`
proves all three writes code-owned when both fields are actual MOFFS operands
in a separated initialized image. Its `original_image_correct` derives the
pure code-to-code trace and whole-image invariant. Each reached operation
performs a full word store, even when its value already equals the old bytes.

Export to ordinary data is the paper's observation boundary; import from
ordinary data is initialization. The generic helper effect does not assert
those boundaries are pure. A four-byte imm32 field in long mode uses the
printed USEWORD32 convention and its low-EAX/upper-RAX contract (Y04/A02),
rather than an eight-byte load. This full-width x64 result applies to the
actual complete eight-byte address field, such as a MOFFS operand.

`validation/run_conversion.py` compares eighteen complete helper packets and
eight original code-owner packets per architecture against the actual Lean
encoder. Its six layouts cover export/import with owners before/after the
helper and code-copy in both orders. Native checks cover arbitrary current
words, both incoming CF values, full-width accumulator seeds, all GPRs/SP,
source/destination, exact entire code/data exterior bytes and repeated calls.

The finite suites pass 21,792 x86 and 24,912 x64 executions over 454/519 live
words. All eighteen helper packets and eight MOFFS code owners per architecture
match the actual Lean codec.

The 53 positive declarations are included in the pinned full axiom audit.
No additional verified erratum is introduced by this step. Whole-template MOVS
copying, restoration of its index/initializer fields and relocation of copied
address/displacement operands remain P04. The universal physical CPU/configuration/
fetch bridge remains E05/A01; successful native tests do not close that bridge.
