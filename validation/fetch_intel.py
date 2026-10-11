"""Cache current primary Intel manuals; downloads are evidence, not ISA proofs."""
from pathlib import Path
import hashlib
import json
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "validation/.cache/intel-093"
SOURCES = {
    "vol3a": "https://cdrdv2-public.intel.com/929359/253668-093-sdm-vol-3a.pdf",
    "vol2a": "https://cdrdv2-public.intel.com/929353/253666-093-sdm-vol-2a.pdf",
    "vol2b": "https://cdrdv2-public.intel.com/929354/253667-093-sdm-vol-2b.pdf",
    "vol2d": "https://cdrdv2-public.intel.com/929356/334569-093-sdm-vol-2d.pdf",
}

def main():
    DEST.mkdir(parents=True, exist_ok=True)
    report = {}
    for name, url in SOURCES.items():
        path = DEST / (name + ".pdf")
        try:
            if not path.is_file():
                request = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
                with urllib.request.urlopen(request, timeout=45) as response:
                    data = response.read()
                assert data.startswith(b"%PDF"), "Not a PDF"
                path.write_bytes(data)
            data = path.read_bytes()
            report[name] = {"url": url, "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
            print(name, len(data), flush=True)
        except Exception as error:
            report[name] = {"url": url, "error": str(error)}
            print(name, type(error).__name__, str(error), flush=True)
    (ROOT / "validation/intel-manuals.json").write_text(json.dumps(report, indent=2) + "\n")

if __name__ == "__main__":
    main()
