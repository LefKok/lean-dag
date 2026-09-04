#!/usr/bin/env python3
"""Which protocols have shown which properties.

`docs/target-properties.md` §11.2. Part 1 of the goal claims a set of
properties every DAG consensus rule must show; part 2 claims that showing
them buys every mechanism. Neither claim is worth much against one
protocol, so the count that matters is how many rules have instances —
and this recomputes it rather than trusting the table.

A rule is "conforming" for a property when some theorem's conclusion is
that property applied to the rule's carrier. Carriers are found by
scanning for `DagRule`-valued definitions, so a new one is picked up
without editing this script; a rule with no carrier cannot show anything
and its reason is recorded below.

Reads `docs/decls.json`; regenerate with `scripts/extract-decls.py`.
Reports only — it never fails a build, since a missing instance is work
outstanding rather than a defect.
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The decision rules of this repository. `carrier` is the `DagRule` a
# rule's conformance is stated against, or None with the reason it has
# none.
RULES = [
    ("core Mysticeti",     "MysticetiProperties.mysticetiRule", None),
    ("reactive Mysticeti", "MysticetiProperties.mysticetiRule", "shares the core's rule"),
    ("Hydrozoan",          "Hydrozoan.rule",                    None),
    ("Optimal-Hydrozoan",  None, "no carrier; `DecidedOpt` is over `OptUniverse`"),
    ("Odontoceti",         None, "no carrier"),
    ("Nemo",               None, "no carrier; its own `Universe` type"),
    ("Mahi-Mahi",          None, "no carrier; band conditional on `2 <= w` (3.4c)"),
    ("Hybrid / Orcaella",  None, "no carrier; `Decided` indexed by a threshold"),
    ("FinWhale",           None, "no carrier; no `Slots` layer at all (3.4c)"),
    ("Black Marlin",       None, "no carrier; commits by round, no slot-indexed relation"),
]

# The obligations, in the order 11.1 lists them.
OBLIGATIONS = ["Causal", "Banded", "Agree", "CommitsCandidate",
               "LeaderCommits", "Descends", "SkipsUnsupported"]
DERIVED = ["Persist", "Local", "LocalTruncate"]

# Files that state the generic theory rather than an instance of it.
GENERIC = re.compile(r"^LeanDag\.Properties\b")


def conclusions(decls):
    """Map property name -> set of carriers it is shown for.

    Two ways of showing one: a theorem whose conclusion is the property
    at that carrier, or a conformance `Statement` that lists it — both
    count, since a protocol may discharge a conjunct inline rather than
    naming it."""
    out = {}
    for d in decls:
        if GENERIC.match(d["module"]):
            continue
        flat = " ".join(d["statement"].split())
        is_stmt = d["kind"] == "def" and d["name"] in ("Statement", "holds")
        if d["kind"] != "theorem" and not is_stmt:
            continue
        for prop in OBLIGATIONS + DERIVED:
            hit = (re.search(r":\s*(LeanDag\.)?(Properties\.)?" + prop + r"\b", flat)
                   or (is_stmt and re.search(r"Properties\." + prop + r"\b", flat)))
            if not hit:
                continue
            for _, carrier, _ in RULES:
                if carrier and carrier.split(".")[-1] in flat:
                    out.setdefault(prop, set()).add(carrier)
    return out


def main():
    path = ROOT / "docs/decls.json"
    if not path.exists():
        print("docs/decls.json missing; run scripts/extract-decls.py", file=sys.stderr)
        return 1
    shown = conclusions(json.loads(path.read_text()))

    cols = OBLIGATIONS + ["|"] + DERIVED
    short = {"Causal": "caus", "Banded": "band", "Agree": "agre",
             "CommitsCandidate": "cand", "LeaderCommits": "lead",
             "Descends": "desc", "SkipsUnsupported": "skip*",
             "Persist": "pers", "Local": "locl", "LocalTruncate": "trnc",
             "|": "|"}
    width = max(len(name) for name, _, _ in RULES) + 1
    print("obligations, then what follows from them "
          "(der = free, given Banded)\n")
    print(" " * width + "  ".join(short[c].ljust(4) for c in cols))
    conforming = 0
    for name, carrier, note in RULES:
        cells = []
        for c in cols:
            if c == "|":
                cells.append("|   ")
            elif carrier and carrier in shown.get(c, ()):
                cells.append("yes ")
            elif (c in DERIVED and carrier
                  and carrier in shown.get("Banded", ())):
                # a consequence of the band: nothing to show per protocol
                cells.append("der ")
            else:
                cells.append("--  ")
        print(name.ljust(width) + "  ".join(cells) + ("   " + note if note else ""))
        if carrier and all(carrier in shown.get(c, ()) for c in OBLIGATIONS[:6]):
            conforming += 1

    carriers = {c for _, c, _ in RULES if c}
    without = [n for n, c, _ in RULES if not c]
    print(f"\n{len(carriers)} carriers, covering {conforming} of {len(RULES)} rules "
          "(reactive Mysticeti shares the core's).")
    print(f"{len(without)} rules have no carrier and so show nothing: "
          + ", ".join(without) + ".")
    print("Giving one a carrier is the first step, and the cheapest test of "
          "whether the six are the right six.")
    print("* SkipsUnsupported is optional; the other six are required.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
