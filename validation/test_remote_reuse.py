"""Cache integrity checks, including old full-audit migration and companion corruption."""
import copy,json,tempfile,unittest
from pathlib import Path
from remote_reuse import digest,input_fingerprint,read_previous,reusable,CONFIG_INPUTS

class ReuseIntegrity(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
  self.root=Path(self.temp.name)
  self.public=self.root/'A.olean';self.private=self.root/'A.olean.private'
  self.public.write_bytes(b'compiled public');self.private.write_bytes(b'compiled private')
  self.inputs={'project/B.olean':'dependency-public','project/B.olean.private':'dependency-private'}
  self.outputs={str(path):digest(path) for path in (self.public,self.private)}
  self.record={'source':'source-hash','command':['lean','-M6000','-j8','A.lean'],
   'setup_sha256':'complete-map-hash','artifacts':self.outputs,
   'input_artifacts_sha256':input_fingerprint(self.inputs)}
  self.report={'modules':{'A':self.record},'imported_artifacts':self.inputs}
 def hit(self,**changes):
  args=dict(previous=self.report,name='A',source='source-hash',command=self.record['command'],
   setup_sha256='complete-map-hash',inputs=self.inputs,outputs=self.outputs)
  args.update(changes);return reusable(**args)
 def test_unchanged_verified_module_reused(self):self.assertTrue(self.hit())
 def test_all_proof_inputs_invalidate(self):
  for changes in ({'source':'new-source'},{'command':['lean','-M6000','-j1','A.lean']},
    {'setup_sha256':'new-import-map'},{'inputs':dict(self.inputs,**{'project/B.olean.private':'changed'})},
    {'inputs':dict(self.inputs,**{'project/C.ir':'new-meta-import'})},{'outputs':{}},{'force':True}):
   with self.subTest(changes=changes):self.assertFalse(self.hit(**changes))
 def test_companion_artifact_corruption_invalidates(self):
  self.private.write_bytes(b'corrupt companion')
  self.assertFalse(self.hit(outputs={str(path):digest(path) for path in (self.public,self.private)}))
 def test_legacy_migration_binds_every_selected_dependency(self):
  old=copy.deepcopy(self.report);del old['modules']['A']['input_artifacts_sha256']
  self.assertTrue(self.hit(previous=old))
  del old['imported_artifacts']['project/B.olean.private']
  self.assertFalse(self.hit(previous=old))
 def test_unverified_report_and_toolchain_cannot_seed_cache(self):
  context={'version':'rc3 exact commit','toolchain':'pinned','commit':'commit','compiler_sha256':'binary',
   'options':{'autoImplicit':False},'heap_mb':6000,'threads':8}
  sources={name:'config-hash' for name in CONFIG_INPUTS}
  log=self.root/'axiom-audit.log';log.write_text("'A' does not depend on any axioms\n")
  report=dict(self.report,passed=True,version=context['version'],toolchain='pinned',commit='commit',
   sources=sources,declarations=[{'name':'A','axioms':[]}],audit_sha256=digest(log))
  compiler={'version':context['version'],'toolchain':'pinned','binary_sha256':'binary'}
  def write():
   (self.root/'lean.json').write_text(json.dumps(report))
   (self.root/'toolchain.json').write_text(json.dumps(compiler))
  write();self.assertTrue(read_previous(self.root,context,sources))
  for key,value in [('passed',False),('commit','different'),('declarations',[{'name':'A','axioms':['unsafe']}])]:
   old=report[key];report[key]=value;write()
   self.assertEqual(read_previous(self.root,context,sources),{})
   report[key]=old
  compiler['binary_sha256']='changed';write();self.assertEqual(read_previous(self.root,context,sources),{})
  compiler['binary_sha256']='binary';write();log.write_text('different audit')
  self.assertEqual(read_previous(self.root,context,sources),{})

if __name__=='__main__':unittest.main()
