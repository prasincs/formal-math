"""Check an export of `padded_permanent_not_mem` with nanoda, then check that tampered copies are rejected.

    lean4export OrbitMain -- padded_permanent_not_mem > export      (lean4export at tag v4.33.0, with LEAN_PATH from `lake env`)
    python3 check_export.py export /path/to/nanoda_bin
"""
import json, pathlib, shutil, subprocess, sys, tempfile

ex, nanoda = pathlib.Path(sys.argv[1]), sys.argv[2]
tmp = pathlib.Path(tempfile.mkdtemp())
DEFS = ["PaddedPermanentNotMem"] + ["PEqualNP.Gct." + x for x in ("detPoly", "permPoly", "linSubst", "orbitClosure", "padIndex", "paddedPerm")]


def run(path, show=()):
    cfg = {"export_file_path": str(path), "use_stdin": False, "num_threads": 8, "stack_size_bytes": 1 << 29, "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
           "unpermitted_axiom_hard_error": True, "nat_extension": True, "string_extension": True, "print_success_message": True,
           "pp_to_stdout": bool(show), "pp_declars": list(show), "pp_options": {"proofs": False}}
    (tmp / "c.json").write_text(json.dumps(cfg))
    r = subprocess.run([nanoda, str(tmp / "c.json")], text=True, capture_output=True)
    return r.returncode, r.stdout, " ".join(r.stderr.split())[:160]


rc, out, err = run(ex, ["padded_permanent_not_mem", *DEFS])
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


def control(a, b, field="value"):
    global bad
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


T = "padded_permanent_not_mem"
for a, b in ((T, "MS.approximates_of_mem"), (T, "Solution.mainTheoremApprox"), (T, "MS.bridge"), ("MS.bridge", "MS.approximates_of_mem"),
             ("MS.approximates_of_mem", "MS.arc_of_orbit"), ("MS.arc", "MS.conj"), ("MS.conj", "MS.extend"), ("MS.cost_det", "MS.cost_cp")):
    control(a, b)
control(T, "Solution.mainTheoremApprox", "type")
print("RESULT", "FAILED" if bad else "accepted, all controls rejected")
sys.exit(bad)
