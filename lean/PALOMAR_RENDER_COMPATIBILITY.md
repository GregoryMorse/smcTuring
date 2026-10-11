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
complete renderer probe described below. This override was reverted before
the subsequently approved alignment to a coherent Mathlib snapshot.

[The complete upstream comparison](https://github.com/leanprover-community/plausible/compare/fb13df72ecefd8ddbf9291021d7f33a8673eb57b...afc2695efcb6855264d85a45632db1ddc56c8774)
shows exactly one changed file, `.github/workflows/lean_action_ci.yml`, from two
CI-pinning commits. Every Lean source, Lake configuration, toolchain and other
package file is identical. The trial changed the Git identity used by the
dependency merger, with no change to the code consumed by Lean.

In the rejected override, Lean remained `leanprover/lean4:v4.35.0-rc3`, compiler
`470d5ce1400764999581fd26d5d72b00d990b0f4`. Mathlib remained
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

A concrete [proposed upstream patch](../validation/ci/palomar-renderer-plausible.patch)
now retains the submitted Mathlib-compatible revision while accepting the exact
known source-identical Plausible pair during manifest merging. It rejects every
other revision/fork and altered package configuration or subdirectory. Eight
focused regression tests pass. The
[advisory workflow](../.github/workflows/palomar-render.yml) checks the complete
upstream Git trees before applying it, then runs the complete renderer path.
The [complete patched render](https://github.com/GregoryMorse/smcTuring/actions/runs/38154282274)
**passes**: all 8,998 requested cache archives download, the unchanged Challenge
builds and renders, all eight selected declaration surfaces pass, and the final
sanitized Verso HTML bundle is produced. Preparation through rendering takes
under five minutes. The submitted proof and dependency pins are
unchanged, as are the renderer's cache, sandbox and declaration checks. This is
a proposed Palomar code change; it does not update Palomar's deployed service.

The artifact records the upstream base renderer SHA-256
`0cde8c3082a672fe99435ed0bed237b719e8041288e4ffa535cebbfbdb1395b9`
and patched renderer SHA-256
`d6881326999ac2af47485eeef9f6b6d50970fe976b116e5912fc2f42f22f93b9`.
The report's `renderer_commit` is the base revision, not an assertion that
Palomar ran the patch. Its separate repair receipt and workflow identify the
modified code. A [ready PR description](../validation/ci/palomar-renderer-fix-pr.md)
accompanies the exact patch. The optional upstream PR is now
[open as #166](https://github.com/PalomarRegistry/PalomarSubmission/pull/166).

### Ordinary dependency alignment is also available

An upstream PR is **not established as a prerequisite for submission**. The
earlier claim that we needed deployment of the patch was too broad: it applied
to keeping our exact current Mathlib snapshot unchanged.

Mathlib's official `v4.35.0-rc3` release resolves to
`c55e6e786f49471c72fbddbec5415808896aec1e`; a later compatible mainline commit is
`5e043698502894993991089b2dd893867c0db5c2`, immediately before the dependency
update introducing the mismatch. Both keep Lean `4.35.0-rc3`, pin Plausible
`fb13df7…` and pass the **unmodified** Palomar manifest merger, including all
shared dependencies. Using either complete coherent dependency snapshot is
ordinary version alignment, rather than a renderer exception.

These Mathlib snapshots change more than a dependency manifest. The closest
compatible commit differs from the previous snapshot in 1,747 tracked files,
including 1,719 Lean files and six computability modules. A compatible merge
therefore does not establish that all existing proofs compile with it. Fresh
proof and unmodified renderer verification are needed before integrating or
submitting that candidate. The user approved alignment to
`5e043698502894993991089b2dd893867c0db5c2`. Both Lake configurations, the
Lake-generated manifest, CI pins and dependency metadata now record this
coherent snapshot. AGENTS.md retains the new pin. The unmodified merger and
upstream manifest equality checks pass. The
[full unmodified render](https://github.com/GregoryMorse/smcTuring/actions/runs/38162124185)
passes on `720a682c9e9185992200efd2a7467b2438704348`: both patch steps were
skipped, all 8,941 cache archives downloaded and all eight selected declarations
rendered into the sanitized HTML bundle. The validation-driver-only follow-up
does not change any input consumed by rendering. Fresh full proof and official
mechanical verification both pass on `a97fbd690b4051463a3b3fe86b5823823aa91bac`; see
[the completed acceptance receipt](acceptance/palomar-render-compatibility.json).

The proposed renderer repair is an alternative compatibility improvement that
retains the exact previously verified Mathlib snapshot. The user authorized an
optional upstream PR with the tested reproduction and restrictive regression
coverage. [PR #166](https://github.com/PalomarRegistry/PalomarSubmission/pull/166)
is open with the unchanged tested patch and three new upstream regression
methods. Five focused upstream tests and locked Ruff pass. Our submission
route uses aligned dependencies and unmodified
Palomar code. The patch does not alter Lean proofs or proof verification,
but it is a proposed exception to the renderer's dependency identity check and
must not be described as an unmodified Palomar run.

The aligned candidate passes proof, mechanical and unmodified rendering checks.
Use the exact commit in [the submission packet](PALOMAR_SUBMISSION.md) and select
replacement of the earlier submission after GitHub authentication. Palomar's
[replacement contract](https://github.com/PalomarRegistry/PalomarServer#the-state-a-submission-holds)
closes the earlier record and admits the new record in one transaction. A
separate withdrawal or waiting for an abort is unnecessary. An existing
Palomar ID remains blank because no result has been registered.

Earlier proof/native acceptance receipts remain bound to their original sources.
The project proof source, native source, Lean compiler and errata remain unchanged;
Mathlib and its dependencies now use the approved coherent snapshot.
