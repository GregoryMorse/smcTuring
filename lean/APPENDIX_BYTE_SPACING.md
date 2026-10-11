# Arbitrarily spaced x86 branch blocks

The complete original-image branch theorem now permits any disjoint address
order of DEFSTACK, the branch core, the taken continuation and input storage.
The core retains the printed predicate, two-instruction tail and fall
continuation contiguously. The taken continuation can be before or after it;
input and stack owners can occur on either side. Every pure instruction and
its length is unchanged. M05's independent-target normalization is retained.

`SpacedLayout.Sites` names Stack, Start, Taken and Data. Fall is derived from
the literal core. The four region intervals have lengths 10, the actual core
span, 30 and 20 bytes. `SpacedLayout.Valid` requires only:

- Complete stack and data extents at most `2^32`.
- Both pure continuation endpoints strictly below `2^32`, so observations do
  not wrap.
- Each of the six region pairs disjoint, in either order.

`valid_checks` proves that these are exactly the ten executable checks used by
the independent comparator. `ordered_valid` includes the prior forward-ordered
placement contract. `ByteRegions.separated_disjoint` composes protected packet
images independently of physical order. Metadata-word preservation now covers
both sides of the core. `Gap` is every byte outside the four complete regions;
arbitrary host/backing bytes are preserved exactly.

`SpacedWhole.correct` constructs the entire continuous current-byte trace from
one original emitted image, its entry PC and static placement. All signed/
unsigned inputs and six relations are covered. The actual displacement is
encoded Taken minus encoded Fall, including negative differences modulo
`2^32`. False ends at Fall+30 and true at Taken+30. Inputs/EAX/ESP are restored,
CF=false, every reached DWORD store is code-owned and every original byte outside
the three final scratch fields is restored. No future trace, fetch, target,
intermediate Ready or repeated initializer is supplied.

These endpoints are finite observation boundaries. The result uses the selected
nonfaulting coherent-current-fetch x86 byte projection; physical ISA/configuration/
segments/CET/fetch and literal x64 conventions remain separate gates.

The original twelve forward fixtures retain 74,400 executions and 338 complete
packets. `generate_branch_geometries.py` places the unchanged pure blocks in all
24 physical orders. Host setup/capture stays outside pure intervals. The expanded
matrix has 288 layouts, 144 backward targets and 1,785,600 native executions,
checking comparison results, both CF values/outcomes, all GPRs/ESP, all seven
owner words and every code byte outside the three final scratch fields.

`ExportBranchSpaced.lean` emits definitions at independent actual COFF
coordinates. Complete opcodes/operands/owners/ends and DIR32 symbol/section/addend
sites are checked; address operands alone are normalized for comparison. All
ten premises and actual region orders are checked. This finite comparison
supplements the universal kernel theorem.

Run `python validation/run_branch_geometries.py` after the pinned Lean audit,
then `python validation/audit_evidence.py` after all native suites finish.
No new paper correction was required.
