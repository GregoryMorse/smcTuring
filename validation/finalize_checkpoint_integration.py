"""Record exact checkpoint/local verification scopes and preserve evidence by integration."""
import hashlib,json,shutil,sys
from datetime import datetime,timezone
from pathlib import Path
from zoneinfo import ZoneInfo
from memory_budget import ROOT,require_budget
from accepted_rounds import checkpoint_rounds
require_budget();sys.stdout.reconfigure(encoding="utf-8")
latest=ROOT/"validation/remote/157.181.172.78/20261006/latest-integration.json"
record=json.loads(latest.read_text(encoding="utf-8"));plan=json.loads((ROOT/"validation/.build/checkpoint-integration-plan.json").read_text(encoding="utf-8"))
client_date=datetime.fromisoformat(record["integrated_at"]).astimezone(ZoneInfo("Europe/Budapest")).date().isoformat()
source_only=plan.get("validation_scope")=="source_integrity_and_errata_only"
errata=json.loads((ROOT/"validation/.build/checkpoint-errata-check.json").read_text(encoding="utf-8"))
assert errata["passed"] and errata["checkpoint"]==record["commit"]==plan["commit"]
if source_only:
 assert plan["validation_targets"]==[]
 changed=[r for r in plan["changes"] if r["path"].startswith("lean/SmcTuring/") and r["path"].endswith(".lean")]
 assert len(changed)==len(plan["skipped_windows_targets"])
 build_path=None
 build={"targets":[],"modules":{},"compiled":[]}
 audit={"modules":[],"declarations":[],"requested_changed_modules":len(changed),"partial_windows_scope":True}
 resource_files=[("errata","memory-checkpoint-errata-check.json")]
else:
 build_path=ROOT/plan.get("validation_build_report","validation/.build/checkpoint-delta-build.json")
 build=json.loads(build_path.read_text(encoding="utf-8"));audit=json.loads((ROOT/"validation/.build/checkpoint-delta-audit.json").read_text(encoding="utf-8"))
 assert build["passed"] and audit["passed"] and audit["checkpoint"]==record["commit"]
 assert build["targets"]==audit["modules"]
 resource_files=[("changed_modules","memory-checkpoint-partial-build.json" if plan.get("validation_targets") else "memory-checkpoint-delta-build.json"),("changed_module_axioms","memory-checkpoint-delta-audit.json"),("errata","memory-checkpoint-errata-check.json")]
resources={key:json.loads((ROOT/"validation/.build"/file).read_text(encoding="utf-8")) for key,file in resource_files}
assert all(r["exit"]==0 and r["memory_limit_bytes"]<=1500000000 for r in resources.values())
previous_windows=plan["previous_integration"].get("local_validation",{}).get("full_windows_build",{})
skipped=plan.get("skipped_windows_targets",{})
inherited_blocks=bool(skipped) and not plan.get("memory_block_retried_this_integration",False)
windows={"state":"pending_prior_memory_limit","failed_module":previous_windows.get("failed_module","SmcTuring.Appendix.DivisionSetup"),"last_attempt_checkpoint":previous_windows.get("last_attempt_checkpoint","8f92ac6235e7e7d06f0af31a17d4fa3dd2fd8cae"),"retried_this_integration":False,"current_changed_module_block":plan.get("local_memory_block"),"known_memory_blocked_modules":plan.get("known_memory_blocked_modules",[]),"memory_block_retried_this_integration":plan.get("memory_block_retried_this_integration",False),"skipped_changed_modules":skipped,"prior_failure_integration":str(Path(plan["previous_integration"]["backup"])/"integration.json")}
if plan.get("local_memory_block") and not inherited_blocks:
 windows["current_failed_build_resource"]=json.loads((ROOT/"validation/.build/memory-checkpoint-delta-build.json").read_text(encoding="utf-8"))
 windows["current_direct_check_resource"]=json.loads((ROOT/"validation/.build/memory-checkpoint-input-bounds-direct.json").read_text(encoding="utf-8"))
record["local_validation"]={"state":"source_integrity_and_errata_passed_all_changed_windows_pending" if source_only else ("partial_changed_modules_and_errata_passed_remaining_windows_pending" if audit.get("partial_windows_scope") else "changed_modules_and_errata_passed_full_windows_pending"),"requested_changed_production_modules":audit.get("requested_changed_modules",len(audit["modules"])),"changed_production_modules":len(audit["modules"]),"all_changed_modules_passed":not audit.get("partial_windows_scope",False),"dependency_closure_modules":len(build["modules"]),"locally_compiled_modules":len(build["compiled"]),"audited_declarations":len(audit["declarations"]),"targeted_axiom_audit_performed":not source_only,"standard_axioms_only":None if source_only else True,"build_report":str(build_path.relative_to(ROOT)) if build_path else None,"audit_report":None if source_only else "validation/.build/checkpoint-delta-audit.json","errata_report":"validation/.build/checkpoint-errata-check.json","resources":resources,"full_windows_build":windows,"fresh_native_aggregate":False,"prior_validation_integration":str(Path(plan["previous_integration"]["backup"])/"integration.json")}
record["local_pdf_after_rebuild_sha256"]=errata["pdf_sha256"]
windows["required_for_proof_completion"]=False
round_tracker=checkpoint_rounds(Path(record['snapshot']),record['commit'])
record["validation_policy"]={"full_windows_lean_required":False,"local_memory_target_is_proof_gate":False,"formal_verification":"Complete source-bound Linux kernel/axiom audit","final_windows_native_assembler_required":True,"round_plan":"lean/CLOSURE_ROUNDS.md"}
record["closure_rounds"]={"accepted":[r["id"] for r in round_tracker["rounds"] if r["state"]=="ACCEPTED"],"current":round_tracker["current_round"],"total":round_tracker["round_count"],"mathematical_proof_complete":round_tracker["mathematical_proof_complete"],"release_ci_complete":round_tracker["release_ci_complete"]}
if plan.get('optional_windows_checks_deferred'):
 windows['state']='optional_windows_lean_deferred'
 windows['memory_blocked_changed_modules']=plan.get('windows_memory_blocked_targets',{})
 windows['optional_available_targets']=plan.get('optional_windows_available_targets',[])
 record['local_validation']['optional_windows_checks_deferred']=True
correction_count=errata.get("correction_count",19)
excerpt_count=errata["source_excerpts_checked"]
positive_count=len(errata["positive_proofs"])
record["pdf_action"]=(f"Rebuilt and visually inspected the two-page M01-M{correction_count:02d} PDF; previous local PDF preserved as before-image" if plan.get("pdf_rebuild_required") else f"Preserved previously rebuilt and visually inspected M01-M{correction_count:02d} PDF")
record["finalized_at"]=datetime.now(timezone.utc).isoformat();record["overall_paper_complete"]=False
backup=Path(record["backup"]);evidence=backup/"validation-evidence";evidence.mkdir(exist_ok=True)
current_evidence=[ROOT/"validation/.build/checkpoint-integration-plan.json"]
if not source_only:
 current_evidence.extend([build_path,ROOT/"validation/.build/checkpoint-delta-audit.json",ROOT/"validation/.build/checkpoint-delta-axiom-audit.log",ROOT/"validation/.build/CheckpointDeltaAudit.lean"])
current_evidence.extend(ROOT/"validation/.build"/file for _,file in resource_files)
current_evidence.extend(ROOT/"validation/.build"/name for name in ["checkpoint-errata-check.json","memory-checkpoint-pull.json","memory-checkpoint-plan.json","memory-checkpoint-integration.json","memory-checkpoint-select.json"])
if plan.get("pdf_rebuild_required"):
 current_evidence.extend(ROOT/"validation/.build"/name for name in ["checkpoint-errata-render.json","memory-checkpoint-pdf-resolution.json","memory-checkpoint-pdf-marker.json","memory-checkpoint-pdf-build-1.json","memory-checkpoint-pdf-render.json"])
 render=json.loads((ROOT/"validation/.build/checkpoint-errata-render.json").read_text(encoding="utf-8"))
 assert render["visual_inspection_complete"] and render["pdf_sha256"]==errata["pdf_sha256"]
 current_evidence.extend(Path(name) for name in render["images"])
 current_evidence.extend(ROOT/"output/pdf"/name for name in ["morse-2018-errata.pdf","morse-2018-errata.log"])
live_progress=ROOT/"validation/.build/checkpoint-live-progress.json"
if live_progress.exists() and json.loads(live_progress.read_text(encoding="utf-8"))["published"].get("commit")==record["commit"]:
 current_evidence.extend([live_progress,ROOT/"validation/.build/memory-checkpoint-live-progress.json"])
 dashboard=ROOT/"lean/CLOSURE_STATUS.md"
 if dashboard.exists():
  current_evidence.append(dashboard)
  record["coordinator_progress"]={"dashboard":"lean/CLOSURE_STATUS.md","dashboard_sha256":hashlib.sha256(dashboard.read_bytes()).hexdigest(),"live_activity_report":"validation/.build/checkpoint-live-progress.json","live_activity_is_checkpoint_proof_evidence":False}
for p in current_evidence:
 if p.is_file():shutil.copyfile(p,evidence/p.name)
record["local_evidence_archive"]=str(evidence)
for p in [latest,backup/"integration.json"]:p.write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
statuspath=ROOT/"REMOTE_STATUS.json";status=json.loads(statuspath.read_text(encoding="utf-8"));status["coordinator_integration"]={"checkpoint":record["commit"],"integrated_at":record["integrated_at"],"local_validation_state":record["local_validation"]["state"],"changed_production_modules_passed":len(audit["modules"]),"targeted_standard_axiom_declarations_passed":len(audit["declarations"]),"full_windows_build_passed":False,"fresh_native_aggregate":False,"report":"validation/remote/157.181.172.78/20261006/latest-integration.json"};statuspath.write_text(json.dumps(status,indent=2)+"\n",encoding="utf-8")
if source_only:
 verification_summary=f"All {len(skipped)} changed production modules depend on the recorded local memory blocker. No Windows Lean build or targeted axiom audit was run in this integration. Their complete Linux audit passes; Windows proof checks remain pending. Prior Windows checks retain their original integration scope. Source and errata checks run serially under the unchanged 1.5 GB guard."
else:
 verification_summary=f"The targeted Windows build passes {len(audit['modules'])} of {audit.get('requested_changed_modules',len(audit['modules']))} changed production modules and their {len(build['modules'])}-module dependency closure; {len(build['compiled'])} modules were compiled. The targeted axiom audit passes {len(audit['declarations'])} registered declarations, using only propext, Classical.choice and Quot.sound. Build/audit peak group allocations were {resources['changed_modules']['peak_group_commit_bytes']:,} / {resources['changed_module_axioms']['peak_group_commit_bytes']:,} bytes. All checks ran serially through the unchanged 1.5 GB guard."
summary=f"""

## Local integration of checkpoint {record['commit'][:7]} ({client_date})

The immutable completed-turn checkpoint `{record['commit']}` is integrated from `{record['base_commit']}`: {len(record['changes'])} source/document/status files, with before-images preserved and coordinator notes merged. Production Lean sources exactly match it. Its complete Linux audit passes {record['remote_audit']['modules']} modules and {record['remote_audit']['declarations']:,} declarations on pinned Lean 4.35.0-rc3/Mathlib. Linux evidence and artifacts remain separate from the Windows cache.

{verification_summary} Current evidence is preserved in this integration's validation-evidence directory.

The latest full changed-module attempt and its smaller direct check stopped at the enforced memory guard in Listing8InputBounds. Remaining changed-module checks are pending; the cap was unchanged. The full Windows rebuild also remains pending after the recorded DivisionSetup memory-limit failures; it was not repeated in this integration. Historical native reports retain their original scope, and no fresh complete native/COFF aggregate is claimed. The source graph, maintained interpreter loop/purity, Listing 9/output and remaining ledger obligations stay open.

The compact M01-M{correction_count:02d} errata has {excerpt_count} exact published excerpts and {positive_count} references freshly checked against the complete latest Linux audit. PDF action: {record['pdf_action']}. Original C++/ASM, baseline/native reports and local resource settings are preserved. The manifest is `validation/remote/157.181.172.78/20261006/latest-integration.json`.
"""
if inherited_blocks:
 summary=summary.replace("The latest full changed-module attempt and its smaller direct check stopped at the enforced memory guard in Listing8InputBounds. Remaining changed-module checks are pending; the cap was unchanged.",f"{len(skipped)} changed modules have dependency closures containing previously memory-blocked modules: {', '.join(plan.get('known_memory_blocked_modules',[]))}. Those failures were not retried in this integration; their evidence is preserved in the preceding integration archive. Remaining Windows checks are pending; the cap was unchanged.")
summary=summary.replace("The source graph, maintained interpreter loop/purity, Listing 9/output and remaining ledger obligations stay open.","Current source-verified closing obligations are recorded in lean/CLOSURE_STATUS.md. Overall completion is false.")
if plan.get('optional_windows_checks_deferred'):
 summary=summary.replace(verification_summary,f"All {len(skipped)} optional Windows Lean checks were deferred. No Windows Lean build or targeted axiom audit was run in this integration. Source/errata checks and the full source-bound Linux kernel/axiom audit pass. Historical Windows checks and failures retain their actual scope; unchanged failures were not retried.")
 block_sentence=f"{len(skipped)} changed modules have dependency closures containing previously memory-blocked modules: {', '.join(plan.get('known_memory_blocked_modules',[]))}. Those failures were not retried in this integration; their evidence is preserved in the preceding integration archive. Remaining Windows checks are pending; the cap was unchanged."
 summary=summary.replace(block_sentence,"Actual prior memory-block dependencies are retained separately from optional checks deferred by policy; no new memory failure is claimed. The local cap was unchanged.")
summary += f"\n\nThe current seven-round tracker accepts rounds {', '.join(str(n) for n in record['closure_rounds']['accepted'])}; round {record['closure_rounds']['current']} is active. Full Windows Lean compilation and fitting below 2 GB are optional convenience checks, not proof-completion gates. Recorded local memory failures remain failed local checks and were not relabeled as passes. Final source-bound Linux proof validation and actual Windows native/assembler CI evidence remain required; resource-only refactors are off the critical path.\n"
for name in ["CHECKPOINT.md","lean/COMPLETION_AUDIT.md"]:
 p=ROOT/name;p.write_text(p.read_text(encoding="utf-8")+summary,encoding="utf-8")
p=ROOT/"validation/remote/157.181.172.78/20261006/INTEGRATION.md";p.write_text("# Latest checkpoint integration\n"+summary,encoding="utf-8")
print("Finalized "+record["commit"]+": source/errata scope only; all changed Windows proof checks pending." if source_only else "Finalized "+record["commit"]+": "+str(len(audit["modules"]))+" changed modules / "+str(len(audit["declarations"]))+" standard-axiom declarations passed locally.")
