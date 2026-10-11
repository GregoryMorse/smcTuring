"""Record measured task settings and the completed incremental-audit evidence."""
import hashlib,json,re
from pathlib import Path
from memory_budget import ROOT,require_budget
require_budget()
folder=ROOT/'validation/remote/157.181.172.78/20261006/efficiency/20261009T120706Z'
receipt=json.loads((folder/'efficiency-adoption.json').read_text())
report_path=folder/'adoption-lean.json';report=json.loads(report_path.read_text())
resources=json.loads((folder/'adoption-resource.json').read_text())
before=json.loads((ROOT/'validation/.build/agent-efficiency-before.json').read_text())
after=json.loads((ROOT/'validation/.build/agent-efficiency-after.json').read_text())
assert receipt['passed'] and receipt['configuration_installation_complete']
assert hashlib.sha256(report_path.read_bytes()).hexdigest()==receipt['report_sha256']
assert report['passed'] and report['kernel_compiled']==0 and report['verified_reused']==len(report['modules'])==1063
assert all(record['cache_hit'] and re.fullmatch('[0-9a-f]{64}',record['input_artifacts_sha256']) for record in report['modules'].values())
assert len(report['declarations'])==7448
assert all(set(record['axioms'])<={'propext','Classical.choice','Quot.sound'} for record in report['declarations'])
assert report['commit']=='470d5ce1400764999581fd26d5d72b00d990b0f4'
assert resources['exit']==0 and resources['memory_limit_bytes']<=7500000000
assert before['session_id']==after['session_id'] and after['context']['effort']=='medium'
settings=receipt['coordinator_configuration']['content']
for value in ['model_reasoning_effort = "medium"','service_tier = "default"','fast_mode = false',
 'memories = false','generate_memories = false','use_memories = false']:assert value in settings
memory=[]
for path in (ROOT/'validation/.build').glob('memory-efficiency-*.json'):
 item=json.loads(path.read_text())
 if item.get('exit')==0:memory.append(item['peak_group_commit_bytes'])
summary={'passed':True,'session_id':after['session_id'],'model':after['context']['model'],
 'reasoning_effort':'medium','service_tier':'default','fast_mode':False,'background_memories':False,
 'same_thread_preserved':True,'no_restart':True,'configuration_task_only':True,
 'cached_input_fraction_before':before['recent_usage'][-1]['total']['cached_input_tokens']/before['recent_usage'][-1]['total']['input_tokens'],
 'cached_input_fraction_after':after['cumulative_cached_input_fraction'],
 'cache_integrity_tests':5,'tested_platforms':['Windows','Linux'],'production_modules_reused':1063,
 'production_modules_recompiled':0,'complete_axiom_declarations':7448,'adoption_report_sha256':receipt['report_sha256'],
 'maximum_successful_local_group_commit_bytes':max(memory),'remote_adoption_resource':resources,
 'prior_checkpoint':receipt['prior_checkpoint'],'prior_checkpoint_fetched':True,
 'proof_goal_complete':False,'proof_goal_continues':True,'evidence_directory':str(folder)}
(folder.parent/'latest.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
text=f'''# Proof-agent efficiency — 2026-10-09

The existing GPT-6.1-Sol session now uses **medium** reasoning; its thread and active full formalization goal were preserved. Task-only launcher overrides and configuration select standard service and explicitly disable fast mode, background memories, memory generation and memory injection. Shared user/account configuration was not changed. Higher reasoning is reserved for a named mathematical obstacle after a concrete attempt; routine composition may use low when practical.

The deployed incremental verifier passed a real adoption audit: **1,063 modules reused, zero modules recompiled, 7,448 declarations in the full axiom audit**. Only propext/Classical.choice/Quot.sound occurred. Five integrity tests passed on both Windows and Linux. Reuse requires a source-bound passing audit, exact compiler/version/options, source, complete import-map hash, every selected dependency hash and all produced companion hashes. Changed, missing or corrupted inputs invalidate reuse. The current complete declaration/axiom audit remains required for new proof checkpoints; final replay uses `--force`.

The agent stopped extra build-progress polling and resumed positive proof work. Focused checks of the new deterministic phase-transport and maintained joint-phase modules passed after adoption. The compact [workflow and proof strategy](remote-agent/EFFICIENCY.md) directs it to reuse completed source-TM global-control, output/fetch/read/store and native-head results, compose remaining executable families/owners at the same reached prefix, then close binding/ledger/native-validation gates. Historical repair instructions were removed from the active handoff.

Recorded cumulative cached input was {100*summary['cached_input_fraction_before']:.2f}% before tuning and {100*summary['cached_input_fraction_after']:.2f}% afterward. This measures cache use, not subscription billing or a guaranteed 10× quota saving. [Prompt caching is automatic](https://developers.openai.com/api/docs/guides/prompt-caching); the workflow preserves stable instructions, the same thread/model and supported automatic compaction defaults. No speculative context-window or caching knobs were added.

The agent sandbox protected `.codex`; the coordinator completed the authorized task configuration through SSH. The passing adoption report, exact logs, resource/compiler records, configuration, prior reports and launcher backup have been collected in [the local evidence directory](remote/157.181.172.78/20261006/efficiency/20261009T120706Z). Its Lean report SHA-256 is `{receipt['report_sha256']}`. The previous genuine turn-end checkpoint `{receipt['prior_checkpoint']}` was also fetched and verified locally. All successful local operations used the unchanged serial 1.5 GB guard; maximum recorded group commit was {summary['maximum_successful_local_group_commit_bytes']:,} bytes. Remote resource limits and Lean/Mathlib pins were preserved.

The efficiency upgrade is complete. The full paper proof remains active and incomplete; its remaining mathematical and fresh Windows/native gates are unchanged.
'''
(ROOT/'validation/AGENT_EFFICIENCY.md').write_text(text,encoding='utf-8')
print('Efficiency evidence verified:',summary['production_modules_reused'],'reused, 0 recompiled,',summary['complete_axiom_declarations'],'declarations.')
print('Local maximum group commit:',summary['maximum_successful_local_group_commit_bytes'])
print('Report:',ROOT/'validation/AGENT_EFFICIENCY.md')
