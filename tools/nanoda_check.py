"""Second-kernel check of one project: nanoda on an export, then tampered copies that must all be rejected.

    cd <project> && lake env lean4export <module> -- <theorems> > export     (lean4export at the tag of the project's Lean)
    python3 ../tools/nanoda_check.py verify/nanoda.json export /path/to/nanoda_bin

`verify/nanoda.json` names the module, the theorems, the definitions to print, and the controls [target, donor, "value" | "type"]:
the target gets the donor's proof term or statement. A control must change what is claimed; two proofs of the same statement may be swapped freely. The donor
must come before the target in the export, or the copy is rejected for a forward reference and tests nothing.
"""
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

spec, ex, nanoda = json.loads(pathlib.Path(sys.argv[1]).read_text()), pathlib.Path(sys.argv[2]), sys.argv[3]
tmp = pathlib.Path(tempfile.mkdtemp())


def run(path, show=()):
    cfg = {"export_file_path": str(path), "use_stdin": False, "num_threads": 8, "stack_size_bytes": 1 << 29, "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
           "unpermitted_axiom_hard_error": True, "nat_extension": True, "string_extension": True, "print_success_message": True,
           "pp_to_stdout": bool(show), "pp_declars": list(show), "pp_options": {"proofs": False}}
    (tmp / "c.json").write_text(json.dumps(cfg))
    r = subprocess.run([nanoda, str(tmp / "c.json")], text=True, capture_output=True)
    return r.returncode, r.stdout, " ".join(r.stderr.split())[:160]


rc, out, err = run(ex, [*spec["theorems"], *spec["show"]])
print(out, err)
bad = rc != 0
thms, names, off = [], {}, 0
with ex.open("rb") as f:
    for line in f:
        if line.startswith(b'{"thm"'):
            thms.append((off, json.loads(line)["thm"]))
        elif b'"str":{' in line[:60]:
            d = json.loads(line)
            names[d["in"]] = (d["str"]["pre"], d["str"]["str"])
        off += len(line)


def name(i):
    r = []
    while i in names:
        i, s = names[i]
        r.append(s)
    return ".".join(reversed(r))


ix = {name(t["name"]): i for i, (_, t) in enumerate(thms)}
if not spec["controls"]:
    sys.exit("no controls listed")
for a, b, field in spec["controls"]:
    new = thms[ix[a]][1] | {field: thms[ix[b]][1][field]}
    p = tmp / "bad"
    with ex.open("rb") as f, p.open("wb") as g:
        left = thms[ix[a]][0]
        while left:
            x = f.read(min(1 << 24, left))
            g.write(x)
            left -= len(x)
        f.readline()
        g.write((json.dumps({"thm": new}) + "\n").encode())
        shutil.copyfileobj(f, g, 1 << 24)
    rc, _, err = run(p)
    p.unlink()
    bad |= rc == 0
    print("REJECTED" if rc else "ACCEPTED (!)", "|", a, "with the", field, "of", b, "|", err[:100])
print("RESULT", "FAILED" if bad else "accepted, all controls rejected")
sys.exit(bad)
