"""Install checksum-pinned Lean and commit-pinned dependency sources on a fresh CI runner."""
import json, os, shutil, subprocess, sys, urllib.request, zipfile
from pathlib import Path
from common import ROOT, CHAIN, COMMIT, digest, require_ci, write

def main():
    require_ci()
    pins = json.loads((Path(__file__).with_name('pins.json')).read_text())
    for reference in pins['reference_files']:
        source=ROOT/reference['packaged_path']
        assert digest(source)==reference['sha256'], 'Reference checksum'
        destination=ROOT/reference['path']
        destination.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(source,destination)
    windows = os.name == 'nt'
    asset = pins['windows' if windows else 'linux']
    archive = ROOT.parent/asset['name']
    urllib.request.urlretrieve(asset['browser_download_url'], archive)
    assert digest(archive) == asset['digest'].removeprefix('sha256:'), 'Compiler archive checksum'
    compiler = (ROOT/'lean/.elan/toolchains'/CHAIN.replace('/','--').replace(':','---')) if windows else ROOT.parent/'toolchain/lean-4.35.0-rc3-linux'
    assert not compiler.exists(), 'CI bootstrap requires a fresh compiler destination'
    if windows:
        staging = ROOT.parent/'windows-toolchain'
        with zipfile.ZipFile(archive) as z:
            assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
            z.extractall(staging)
        children = list(staging.iterdir())
        assert len(children) == 1 and (children[0]/'bin/lean.exe').is_file()
        compiler.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(children[0]), compiler)
    else:
        compiler.parent.mkdir(parents=True, exist_ok=True)
        listing = subprocess.check_output(['tar','--zstd','-tf',str(archive)], text=True)
        assert all(Path(n).parts[0] == compiler.name and '..' not in Path(n).parts for n in listing.splitlines())
        subprocess.run(['tar','--zstd','-xf',str(archive),'-C',str(compiler.parent)], check=True)
        write(ROOT.parent/'lean-release.json', {'assets':[asset]})
    binary = compiler/'bin'/('lean.exe' if windows else 'lean')
    version = subprocess.check_output([str(binary),'--version'], text=True)
    assert COMMIT in version and 'version 4.35.0-rc3,' in version
    project = ROOT/'lean'
    assert (project/'lean-toolchain').read_text().strip() == CHAIN
    manifest = json.loads((project/'lake-manifest.json').read_text())
    assert next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib') == pins['mathlib_revision']
    for package in manifest['packages']:
        destination = project/'.lake/packages'/package['name']
        assert not destination.exists(), 'CI dependency bootstrap requires fresh sources'
        assert package['url'].startswith('https://github.com/')
        destination.mkdir(parents=True)
        for command in [['git','init'],['git','fetch','--depth','1',package['url'],package['rev']],['git','checkout','--detach','FETCH_HEAD']]:
            subprocess.run(command, cwd=destination, check=True)
        assert subprocess.check_output(['git','rev-parse','HEAD'], cwd=destination, text=True).strip() == package['rev']
    env = dict(os.environ, PATH=str(compiler/'bin')+os.pathsep+os.environ['PATH'], LEAN_NUM_THREADS='8', RAYON_NUM_THREADS='1')
    subprocess.run([str(compiler/'bin'/('lake.exe' if windows else 'lake')),'-f','lakefile.proof.toml','exe','cache','get'], cwd=project, env=env, check=True)
    write(ROOT/'validation/ci-results/bootstrap.json', {'passed':True,'platform':sys.platform,'version':version.strip(),'archive_sha256':digest(archive),'packages':{p['name']:p['rev'] for p in manifest['packages']}})

if __name__ == '__main__': main()
