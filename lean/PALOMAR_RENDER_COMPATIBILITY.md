# Palomar renderer dependency compatibility

The submitted source at `e6aaea4723a82ee50385ac4d7991fbde9ba8ae03` passed
[actual mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/38141132403).
Its subsequent [render attempt](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/38148604396)
stopped before rendering the Challenge: the renderer refused two different
Git revisions of the package named `plausible`.

| Source | Plausible revision |
| --- | --- |
| Pinned Mathlib's dependency manifest | `afc2695efcb6855264d85a45632db1ddc56c8774` |
| Verso for Lean 4.35.0-rc3 | `fb13df72ecefd8ddbf9291021d7f33a8673eb57b` |

Palomar's renderer uses Verso commit
`8fc7a297f14d5adc1a551b5b4ecf283c08bd691f` and rejects differing package
identities in `merge_renderer_manifest`. This is a setup conflict rather than
a failed Lean proof or a Challenge-size diagnostic. The downloaded report
classifies it as Palomar-owned and retryable.

## Minimal project workaround

Both Lake configurations now explicitly require Plausible at Verso's revision;
the committed manifest records that same direct requirement. This keeps the
choice reproducible and prevents a dependency refresh from silently restoring
the conflicting inherited revision. The direct Plausible requirement follows
Mathlib because Lake processes direct requirements in reverse order.

[The complete upstream comparison](https://github.com/leanprover-community/plausible/compare/fb13df72ecefd8ddbf9291021d7f33a8673eb57b...afc2695efcb6855264d85a45632db1ddc56c8774)
shows exactly one changed file, `.github/workflows/lean_action_ci.yml`, from two
CI-pinning commits. Every Lean source, Lake configuration, toolchain and other
package file is identical. The workaround changes the Git identity used by the
dependency merger, with no change to the code consumed by Lean.

Lean remains `leanprover/lean4:v4.35.0-rc3`, compiler
`470d5ce1400764999581fd26d5d72b00d990b0f4`. Mathlib remains
`302343bb9a029d4edab4f736703f0736896c1b64`. No project theorem, Challenge,
Solution, Comparator declaration, native source or errata is modified.

## Validation boundaries

The focused compatibility check verifies the complete upstream Git trees,
package configurations, retained compiler/Mathlib pins and unchanged project
proof sources. It also executes the actual pinned renderer's manifest-merging
functions: the previous manifest reproduces the conflict and the corrected
manifest merges successfully, including every shared dependency.

An isolated `lake --keep-toolchain update plausible` with the exact pinned
compiler also selects the required revision and leaves every other dependency
entry unchanged. The committed manifest is the actual output of that command.
Mathlib post-update cache downloads were disabled; no project proof was rebuilt.
The check ran serially under the existing 1.5 GB local memory guard. See
[the focused check receipt](acceptance/palomar-render-compatibility.json).

This resolves the observed workspace conflict. Full Challenge HTML generation
and acceptance of a new submission remain separate checks; a successful manifest
merge is not presented as completed editorial review or registration. Earlier
proof/native acceptance receipts remain evidence for their original source and
must not be relabeled as runs of the new commit.
