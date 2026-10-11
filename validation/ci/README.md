# Exact-source proof and native CI

The workflow in `.github/workflows/proof-native.yml` is prepared for coordinator
review and a subsequent push/run. Preparing it is not evidence that GitHub ran it.

## Scope

- Linux: pinned Lean 4.35.0-rc3 / commit
  `470d5ce1400764999581fd26d5d72b00d990b0f4`, pinned Mathlib
  `302343bb9a029d4edab4f736703f0736896c1b64`, every production module and every
  registered declaration, complete standard-axiom audit, exact proved errata.
- Windows: fresh Windows compiler and exporter dependency objects; all existing
  baseline and corrected native validators, actual MSVC/MASM/COFF/loaded-image
  comparisons, x86/x64 where supported. Printed constant and multiply tests retain
  their established x86 scope. Baseline covers Debug/Release × Win32/x64.
- The Linux JSON report supplies checked declaration names to native tests. It is
  explicitly labeled Linux evidence. No Linux `.olean`/IR is transferred to
  Windows, and no complete Windows Lean audit is claimed.

Both release archives have fixed SHA-256 checksums in `pins.json`. Dependency Git
revisions come from the pinned manifest and are checked after checkout. Actions
are pinned by full commit. Runner image and MSVC updates are recorded in fresh
tool reports rather than described as fixed compiler versions.

`reference/` carries the exact already reviewed paper PDF and two-page errata PDF
and log, with checked hashes. Bootstrap restores their established validation
paths on a clean checkout. CI checks the immutable errata, its TeX/excerpts and
current positive proofs; it does not silently regenerate the reviewed PDF.

The Linux job creates a separate bounded CI cgroup (7.5 GB, no swap, eight CPU
equivalents, 512 tasks). Fresh Windows exporter compilation uses a 6 GB Lean heap
on the GitHub runner. Every native test and its descendants retain the existing
1.5 GB Windows job guard. None of these entrypoints changes the remote scope or
the local Windows guard. The CI installer/compiler refuse non-GitHub execution.

## Review and acceptance

1. Coordinator publishes the reviewed exact source commit and starts this workflow.
2. Require both `linux-proof` and `windows-native` to pass for that same commit/run.
3. Download both evidence artifacts. Verify the complete source manifest, proof
   report hash, compiler archive/package pins, declaration registry, native report
   hashes, object/executable/loaded packet manifests, tool identities and all four
   baseline configuration outcomes.
4. Record the actual run URL, commit, checks and artifact digests in round 7 and
   the final handoff. Any failed step remains an open gate; an uploaded failure log
   is not acceptance. Physical ISA/mapping/ABI/CET/observation conditions remain
   those disclosed in `lean/PHYSICAL_BINDING_CONTRACT.md`.

GitHub's [runner specification](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)
documents the selected `ubuntu-24.04` and `windows-2022` labels. The action pins
were checked against the official `actions` repositories' release-tag Git refs.
Choose adequate runner resources before running a private repository workflow;
resource limitations do not become mathematical assumptions.

The deliberate local cold project replay is separate from CI. CI begins with no
project artifacts and compiles the complete Linux project afresh; it can use the
exact pinned dependency cache. A normal rerun after an actual CI failure is a
release repair, not a reason to reopen completed mathematical rounds.

Remote replay command (inside the unchanged parent scope):
`python3 validation/ci/linux_entry.py --cold-existing`. This mode preserves the
installed pinned compiler/dependencies and invokes exactly one `--force` project
replay, then the current full errata gate and source snapshot. It never runs the
CI installer or starts another cgroup on the workstation/server.
