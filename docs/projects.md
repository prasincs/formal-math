# Layout of a project

    <project>/
      README.md            the statement in words and in Lean, what is ours and what is not, related work with dates, limits
      <Name>Statement.lean definitions and the statement as a `Prop`; imports Mathlib only
      ...                  the proof
      <Name>Main.lean      the theorem, and `#print axioms`
      <Name>Challenge.lean the statement with `sorry`; nothing imports it
      comparator.json      for leanprover/comparator
      lakefile.toml, lake-manifest.json, lean-toolchain   exact pins
      NOTICE               copied and used work, with licenses
      PROCESS.md           who and what wrote it, time line, mistakes, what was not done
      verify/              nanoda.json (theorem, definitions to print, controls), logs, SHA256SUMS

Module names carry the project's prefix, so that a project can depend on another repository with modules called `Statement` or `Challenge`.

# Before a project is listed

1. A search for earlier work, before the proof if possible; what was searched and when goes into the README.
2. `lake build` from a clean copy with no network after the pinned dependencies are in place; no `sorry` outside the challenge file; axioms `propext`, `Classical.choice`, `Quot.sound` only; no `native_decide`.
3. A second kernel: `tools/nanoda_check.py`, with controls that change what is claimed. All must be rejected.
4. Sources from elsewhere are scanned for code that runs during a build before they are built, and are built in a container without network.
5. The README says what the result rests on. A theorem that depends on an unreviewed proof says so in its first paragraph.
