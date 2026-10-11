"""Record the actual MSVC/MASM/COFF toolchain under the native job guard."""
import os, platform, shutil, subprocess, sys
from common import ROOT, digest, write
sys.path.insert(0,str(ROOT/'validation'))
from run_defaddr import vc_environment
from memory_budget import require_budget

def main():
    require_budget()
    tools={}
    for arch in ['x86','x64']:
        env=vc_environment(arch)
        for name in ['cl.exe','link.exe','dumpbin.exe','ml.exe' if arch=='x86' else 'ml64.exe']:
            binary=shutil.which(name,path=env['PATH'])
            assert binary, (arch,name)
            result=subprocess.run([binary],env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
            tools[arch+'/'+name]=dict(path=binary,sha256=digest(binary),version_banner=(result.stdout+result.stderr).splitlines()[:5])
    write(ROOT/'validation/ci-results/windows-tools.json',dict(passed=True,os=platform.platform(),processor=os.environ.get('PROCESSOR_IDENTIFIER'),tools=tools))

if __name__=='__main__':main()
