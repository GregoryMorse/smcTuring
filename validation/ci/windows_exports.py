"""Fresh Windows-only exporter closure compilation on a GitHub runner (6 GB Lean heap).

Native tests still use the unchanged 1.5 GB job guard. This is neither the local
Windows builder nor a complete Windows proof audit; no Linux objects are loaded.
"""
import json, os, re, subprocess, sys
from pathlib import Path
from common import ROOT, CHAIN, COMMIT, digest, require_ci, write
sys.path.insert(0, str(ROOT/'validation'))
from module_artifacts import ArtifactResolver, TOOLCHAIN
from lean_build import lake_command

def imports(source):
    text = source.read_text(encoding='utf-8-sig')
    return [name for line in re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)',text,re.M)
            for name in line.split('--',1)[0].split()]

def main():
    require_ci()
    assert os.name == 'nt'
    project = ROOT/'lean'
    cache = project/'.lake/proof-build'
    assert not (cache/'lib/lean').exists(), 'Never reuse transferred or unverified project objects'
    binary = TOOLCHAIN/'bin/lean.exe'
    lake_command(project,binary.parent)
    version = subprocess.check_output([str(binary),'--version'],text=True).strip()
    assert COMMIT in version
    resolver = ArtifactResolver()
    done = {}
    active = set()
    def visit(name):
        if name in done: return
        assert name not in active, 'Import cycle'
        active.add(name)
        source = project/Path(*name.split('.')).with_suffix('.lean')
        for dep in imports(source):
            if dep == 'SmcTuring' or dep.startswith('SmcTuring.'): visit(dep)
        maps, _ = resolver.select(name)
        setup = cache/'ir'/Path(*name.split('.')).with_suffix('.setup.json')
        write(setup,dict(name=name,package='smcTuring',isModule=True,options={'autoImplicit':False},importArts=maps,plugins=[],dynlibs=[]))
        obj = cache/'lib/lean'/Path(*name.split('.')).with_suffix('.olean')
        obj.parent.mkdir(parents=True,exist_ok=True)
        c = cache/'ir'/Path(*name.split('.')).with_suffix('.c')
        command = [str(binary),'-M6000','-j8',str(source),'-o',str(obj),'-i',str(obj.with_suffix('.ilean')),'-c',str(c),'--setup',str(setup)]
        result = subprocess.run(command,cwd=project,capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=1800)
        log = ROOT/'validation/ci-results/windows-module-logs'/Path(*name.split('.')).with_suffix('.log')
        log.parent.mkdir(parents=True,exist_ok=True)
        log.write_text(result.stdout+result.stderr,encoding='utf-8')
        assert result.returncode == 0, name+' failed: '+result.stdout+result.stderr
        artifacts = {p.relative_to(ROOT).as_posix():digest(p) for suffix in ['.olean','.olean.server','.olean.private','.ir','.ir.sig','.ilean']
                     if (p:=Path(str(obj.with_suffix(''))+suffix)).is_file()}
        assert obj.is_file() and artifacts
        done[name] = dict(source=digest(source),setup=digest(setup),artifacts=artifacts,
                          dependencies={k:digest(Path(p)) for groups in maps.values() for group in groups for p in group for k in [Path(p).relative_to(ROOT).as_posix()]})
        active.remove(name)
        print('Windows exporter dependency: '+name,flush=True)
    exporters = sorted(project.glob('Export*.lean'))
    roots = sorted({dep for p in exporters for dep in imports(p) if dep=='SmcTuring' or dep.startswith('SmcTuring.')})
    for name in roots: visit(name)
    write(ROOT/'validation/ci-results/windows-exports.json',dict(passed=True,scope='Fresh Windows exporter dependency closure only; Linux complete audit is separate',platform=sys.platform,version=version,compiler_sha256=digest(binary),heap_mb=6000,threads=8,roots=roots,modules=done))

if __name__ == '__main__': main()
