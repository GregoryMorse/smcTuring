# Resource limit

The user's local sub-2-GB preference prevents workstation thrashing; it is not
a proof-completion criterion. Keep the existing local execution guard below.
Run verification and build commands serially through validation/limited_run.py.
Its Windows Job Object caps the aggregate committed memory of the launcher and
all descendants at 1,500,000,000 bytes, leaving room below the user ceiling.
It also bounds process count at eight, allowing sequential Visual Studio SDK
discovery helpers without parallel builds. A 25 ms monitor sums descendant working sets and
stops the command at a 1.5 GB resident threshold; this is a sampled guard, while
the allocation cap is enforced by Windows. Do not raise that cap, bypass
the guard, or run separate checks concurrently. A memory-limit failure is a
failed check; use a smaller or direct check rather than retrying without limits.
Do not terminate unrelated workspace or editor processes to free memory.
Keep the full formalization objective intact while honoring this constraint.
Fresh full proof verification may run on the authorized server or GitHub.
A complete Windows Lean build within this local cap is optional; do not spend
proof rounds on resource-only refactors merely to satisfy the cap. Windows
native/assembler checks remain required for the native binding. Follow the
seven deliverable rounds in lean/CLOSURE_ROUNDS.md.

# Toolchain

Use Lean 4.35.0-rc3, commit 470d5ce1400764999581fd26d5d72b00d990b0f4.
Keep lean/lean-toolchain pinned to leanprover/lean4:v4.35.0-rc3.

# Authorized remote resources

The user authorizes SSH work on the configured hosts 157.181.172.111 or 157.181.172.78 with up to
8 GB RAM and multiple CPU cores. This is a remote-only exception to the local
resource policy above; local checks remain capped at 1.5 GB and serial.
Create a dedicated task/run directory on the chosen server. Enforce a remote
allocation limit below 8 GB (prefer a cgroup/systemd limit of 7.5 GB) before
heavy work. Keep Lean 4.35.0-rc3 and the existing Mathlib revision pinned.
Fetch changed source, logs, reports and artifact manifests at every completed
checkpoint, and at failure/termination. Keep remote platform artifacts in a
separate local evidence directory; do not substitute Linux compiled objects
for the Windows proof cache. Never leave progressed work only on the server.

The user corrected the second server to .78: stop all proof jobs on .79 and
transfer this task's work to .78 or .111. Use .79 only to finish that transfer.
