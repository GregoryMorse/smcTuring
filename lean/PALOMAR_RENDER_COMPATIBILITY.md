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

## Tested project workaround — reverted

Trial commit `7b0206dd6f1f97b832ab07aef4603b2c30e1cee1` explicitly required
Plausible at Verso's revision in both Lake configurations and the manifest.
The direct requirement followed Mathlib because Lake processes direct
requirements in reverse order. It passed the manifest merger, but failed the
complete renderer probe described below. This override has been reverted;
the current dependency configurations and manifest are restored byte for byte
from the previously verified source.

[The complete upstream comparison](https://github.com/leanprover-community/plausible/compare/fb13df72ecefd8ddbf9291021d7f33a8673eb57b...afc2695efcb6855264d85a45632db1ddc56c8774)
shows exactly one changed file, `.github/workflows/lean_action_ci.yml`, from two
CI-pinning commits. Every Lean source, Lake configuration, toolchain and other
package file is identical. The trial changed the Git identity used by the
dependency merger, with no change to the code consumed by Lean.

Lean remains `leanprover/lean4:v4.35.0-rc3`, compiler
`470d5ce1400764999581fd26d5d72b00d990b0f4`. Mathlib remains
`302343bb9a029d4edab4f736703f0736896c1b64`. No project theorem, Challenge,
Solution, Comparator declaration, native source or errata is modified.

## Validation boundaries

The focused compatibility check verified the complete upstream Git trees,
package configurations, retained compiler/Mathlib pins and unchanged project
proof sources. It also executed the actual pinned renderer's manifest-merging
functions: the previous manifest reproduces the conflict and the corrected
trial manifest merged successfully, including every shared dependency.

An isolated `lake --keep-toolchain update plausible` with the exact pinned
compiler selected the required revision and left every other dependency
entry unchanged. The trial manifest was the actual output of that command.
Mathlib post-update cache downloads were disabled; no project proof was rebuilt.
The check ran serially under the existing 1.5 GB local memory guard. See
[the focused check receipt](acceptance/palomar-render-compatibility.json).

## Complete renderer probe: a second incompatible requirement

[The corrected advisory renderer probe](https://github.com/GregoryMorse/smcTuring/actions/runs/38152118403)
used the actual pinned Palomar renderer, its sandbox and the unchanged Challenge.
It passed the dependency merger, then failed at workspace preparation:

```text
Mathlib cache discovery was incomplete (0 of 0 keys); cache command exited 1
```

This did not reach Challenge HTML generation. The report truncates the cache
command's output, so the following diagnosis comes from the pinned source and
manifests, rather than an untruncated runtime warning:
[Mathlib's `checkForManifestMismatch`](https://github.com/leanprover-community/mathlib4/blob/302343bb9a029d4edab4f736703f0736896c1b64/Cache/Requests.lean#L1066-L1127)
requires matching Git revisions for shared packages and exits with code 1 on
a mismatch. The cache download path calls it before downloading. It requires
Plausible `afc2695…`; the renderer merger requires `fb13df7…`. Changing the
project pin therefore cannot satisfy both checks with these upstream pins.

The first advisory run failed because our harness omitted the runner's user-bus
environment. That harness error was repaired before the cache failure above;
it is not attributed to Palomar. The second run uses bounded user scopes and
does not modify the upstream renderer or its security checks.

## Remediation and submission status

**No demonstrated working retry candidate yet.** Keep the mechanically verified
submission open. Hash-only retries and the reverted Plausible override do not
resolve the complete renderer path. The narrow upstream remedy is to reconcile
Verso's shared-dependency pin with Mathlib's pin, or support source-identical
dependencies throughout both renderer merging and cache preparation. The two
upstream Plausible revisions differ only in CI; changing the mathematics or
rebuilding the closed proof audit would not address this setup issue.

When a complete renderer probe passes, submit the corrected commit and select
replacement of the earlier submission after GitHub authentication. Palomar's
[replacement contract](https://github.com/PalomarRegistry/PalomarServer#the-state-a-submission-holds)
closes the earlier record and admits the new record in one transaction. A
separate withdrawal or waiting for an abort is unnecessary. An existing
Palomar ID remains blank because no result has been registered.

Earlier proof/native acceptance receipts remain bound to their original sources.
The formal proofs, native source, compiler/Mathlib pins and errata remain unchanged.

Suggested follow-up for issue #131 (not posted by the agent):

> On Lean 4.35.0-rc3, aligning Plausible with Verso clears the manifest conflict,
> but the complete renderer then fails Mathlib cache discovery. Pinned Mathlib's
> `checkForManifestMismatch` requires `afc2695…`, whereas Verso requires `fb13df7…`;
> those revisions differ only in CI. We reverted the override. Could the renderer
> reconcile these pins? Reproduction:
> https://github.com/GregoryMorse/smcTuring/actions/runs/38152118403.
