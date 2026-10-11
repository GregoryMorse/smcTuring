"""Use an equivalent Lake configuration with a cache separate from the editor."""
from pathlib import Path
import tomllib


def lake_command(project: Path, binary: Path) -> list[str]:
    canonical = tomllib.loads((project / "lakefile.toml").read_text(encoding="utf-8"))
    proof = tomllib.loads((project / "lakefile.proof.toml").read_text(encoding="utf-8"))
    assert proof.pop("buildDir") == ".lake/proof-build", "Unexpected proof-cache directory"
    assert proof == canonical, "Proof and editor Lake configurations differ beyond the cache directory"
    return [str(binary / "lake.exe"), "--file", "lakefile.proof.toml"]
