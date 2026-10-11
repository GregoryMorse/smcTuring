"""Focused checks of the user's cap, resident monitor and serial guard."""
import subprocess,sys
from memory_budget import Budget,MAX_BYTES,ROOT,require_budget
require_budget()
try:Budget(MAX_BYTES+1)
except ValueError:pass
else:raise AssertionError('An excessive cap was accepted')
result=subprocess.run([sys.executable,str(ROOT/'validation/limited_run.py'),'--',
 sys.executable,'-c','print("unexpected concurrent verification")'],capture_output=True,
 text=True,timeout=10,creationflags=subprocess.CREATE_NO_WINDOW)
assert result.returncode!=0,result.stdout
assert 'Another verification command is active' in result.stderr,result.stderr
print('Oversized cap rejected; concurrent verification rejected; inherited job verified.')
