"""Interpret pre-publication round metadata using verified immutable checkpoint evidence."""
import hashlib
import json
from pathlib import Path

def checkpoint_rounds(snapshot: Path, commit: str):
    tracker=json.loads((snapshot/'lean/CLOSURE_ROUNDS.json').read_text(encoding='utf-8'))
    round5=next(r for r in tracker['rounds'] if r['id']==5)
    if round5['state']=='PROOF_COMPLETE_AWAITING_CHECKPOINT':
        verified=json.loads((snapshot.parent/'PULL_VERIFIED.json').read_text(encoding='utf-8'))
        manifest=json.loads((snapshot.parent/'manifest.json').read_text(encoding='utf-8'))
        assert verified['passed'] and manifest['commit']==commit
        report=snapshot/'validation/remote-evidence/lean.json'
        digest=hashlib.sha256(report.read_bytes()).hexdigest()
        assert digest==manifest['checkpoint']['audit']['report_sha256']==round5['progress']['linux_report_sha256']
        assert round5['proof_complete'] and tracker['mathematical_proof_complete']
        assert len(round5['remaining_acceptance'])==1 and 'immutable turn-end publication' in round5['remaining_acceptance'][0]
        round5['state']='ACCEPTED'
        round5['accepted']=True
        round5['remaining_acceptance']=[]
        round5['coordinator_verified_publication']={'checkpoint':commit,'report_sha256':digest,'pull_verified':True}
        tracker['current_round']=max(tracker['current_round'],6)
    return tracker
