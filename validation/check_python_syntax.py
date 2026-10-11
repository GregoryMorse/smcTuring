"""Check the edited validation entry points without importing or executing them."""
import ast
from memory_budget import ROOT,require_budget
require_budget()
files=sorted((ROOT/'validation').glob('*.py'))
for path in files:ast.parse(path.read_text(encoding='utf-8'),filename=str(path))
print('Python syntax passed: '+str(len(files))+' files')
