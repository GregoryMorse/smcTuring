"""CI entrypoint: pinned bootstrap, complete kernel/axiom audit, exact errata, snapshot."""
import argparse, subprocess, sys
from common import ROOT, require_ci

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--cold-existing',action='store_true',help='ONE deliberate replay using this existing remote scope/compiler/dependencies; no installer')
    args=parser.parse_args()
    if args.cold_existing:
        commands=[('remote_build.py',['--force'])]
    else:
        require_ci()
        commands=[('ci/bootstrap.py',[]),('remote_build.py',[])]
    commands += [('audit_errata.py',['--remote-source-proof']),('ci/linux_finish.py',[])]
    for script,args in commands:
        subprocess.run([sys.executable,str(ROOT/'validation'/script),*args],cwd=ROOT,check=True)

if __name__=='__main__': main()
