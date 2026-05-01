#!/usr/bin/env python3
"""
Lean translation checker for Verilog-to-Lean benchmark.

Scans Leans-Handcrafted/ and Leans-Chat/ for .lean files and checks each for:
  Level 0: Per-file compilation success (via `lean <file>`)
  Level 1: Structural checks
    - No `sorry` usage
    - Has required declarations (Inputs/State, Outputs/Output, eval/step)
    - Namespace present
    - Has at least one theorem

Usage:
  python3 check.py                        # check all tiers, both sources
  python3 check.py --tier 2               # only Tier 2
  python3 check.py --source chat          # only ChatGPT-generated files
  python3 check.py --source handcrafted   # only hand-crafted files
  python3 check.py --csv                  # output as CSV
  python3 check.py --logs                 # write per-module .log logs to logs/
  python3 check.py --no-compile           # structural checks only (faster)
"""

import subprocess
import sys
import re
import csv
import datetime
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent

SOURCE_DIRS = {
    "handcrafted": PROJECT_ROOT / "Leans-Handcrafted",
    "chat":        PROJECT_ROOT / "Leans-Chat",
}
LOG_DIR = PROJECT_ROOT / "logs"


# ---------------------------------------------------------------------------
# Compilation check (per-file)
# ---------------------------------------------------------------------------

def compile_lean_file(path: Path) -> tuple[bool, bool, str]:
    """Compile a single .lean file.

    Returns:
        (compiles, sorry_in_output, full_output)
        - compiles: True if exit code 0
        - sorry_in_output: True if the compiler printed a 'declaration uses sorry' warning
          (indicates sorry axiom used even if file doesn't spell it out literally)
    """
    result = subprocess.run(
        ["lean", str(path)],
        capture_output=True,
        text=True,
        timeout=120,
    )
    success = result.returncode == 0
    output = (result.stdout + result.stderr).strip()
    # Lean 4 uses backticks: `sorry`; some versions use straight quotes: 'sorry'
    sorry_warning = bool(re.search(r"declaration uses [`']sorry[`']", output))
    return success, sorry_warning, output


# ---------------------------------------------------------------------------
# Structural checks (Level 1)
# ---------------------------------------------------------------------------

def check_structural(path: Path) -> dict:
    text = path.read_text()
    r = {}

    # Check for sorry on non-comment lines (word boundary match, ignores `-- ...` lines)
    code_lines = [l for l in text.splitlines() if not l.lstrip().startswith("--")]
    code_text = "\n".join(code_lines)
    r["sorry_free"]         = not bool(re.search(r"\bsorry\b", code_text))
    r["has_namespace"]      = bool(re.search(r"^namespace\s+\S+", text, re.MULTILINE))
    r["has_eval"]           = bool(re.search(r"^def eval\b", text, re.MULTILINE))
    r["has_step"]           = bool(re.search(r"^def step\b", text, re.MULTILINE))
    r["has_inputs_or_state"]= bool(re.search(r"^structure\s+(Inputs|State)\b", text, re.MULTILINE))
    r["has_outputs"]        = bool(re.search(r"^structure\s+(Outputs|Output)\b", text, re.MULTILINE))
    r["has_theorems"]       = bool(re.search(r"^theorem\b", text, re.MULTILINE))

    if r["has_eval"] and not r["has_step"]:
        r["module_type"] = "combinational"
    elif r["has_step"]:
        r["module_type"] = "sequential"
    else:
        r["module_type"] = "unknown"

    r["schema_ok"] = (
        r["has_namespace"]
        and r["has_inputs_or_state"]
        and r["has_outputs"]
        and (r["has_eval"] or r["has_step"])
        and r["sorry_free"]
    )
    return r


# ---------------------------------------------------------------------------
# File collection
# ---------------------------------------------------------------------------

def collect_files(tiers: list[int], sources: list[str]) -> list[dict]:
    """Return list of dicts with keys: tier, source, path."""
    entries = []
    for source in sources:
        base = SOURCE_DIRS.get(source)
        if not base or not base.exists():
            continue
        for tier_dir in sorted(base.iterdir()):
            # Match "Tier 1", "Tier 2", "Tier 3" etc.
            m = re.match(r"Tier\s*(\d+)", tier_dir.name, re.IGNORECASE)
            if not m:
                continue
            tier = int(m.group(1))
            if tiers and tier not in tiers:
                continue
            for f in sorted(tier_dir.glob("*.lean")):
                entries.append({"tier": tier, "source": source, "path": f})
    return entries


# ---------------------------------------------------------------------------
# Log generation
# ---------------------------------------------------------------------------

def write_log(entry: dict, struct: dict, compiles: bool, sorry_warned: bool, error_output: str) -> None:
    tier = entry["tier"]
    source = entry["source"]
    module = entry["path"].stem
    log_path = LOG_DIR / f"Tier{tier}" / f"{module}_{source}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)

    sorry_ok = struct["sorry_free"] and not sorry_warned
    status = "PASS" if (compiles and struct["schema_ok"] and sorry_ok) else "FAIL"
    date = datetime.date.today().isoformat()

    lines = [
        f"## {module} ({source})",
        f"",
        f"- **Date**: {date}",
        f"- **Tier**: {tier}",
        f"- **Source**: {source}",
        f"- **Module type**: {struct['module_type']}",
        f"",
        f"### Level 0: Compilation",
        f"- Compiles: {'yes' if compiles else 'NO'}",
        f"- Sorry axiom in compiler output: {'YES (warning)' if sorry_warned else 'no'}",
    ]
    if not compiles or sorry_warned:
        lines += [f"- Compiler output:", "```", error_output or "(no output)", "```"]

    lines += [
        f"",
        f"### Level 1: Structural checks",
        f"- Sorry-free (source text): {'yes' if struct['sorry_free'] else 'NO'}",
        f"- Has namespace: {'yes' if struct['has_namespace'] else 'NO'}",
        f"- Has Inputs/State: {'yes' if struct['has_inputs_or_state'] else 'NO'}",
        f"- Has Outputs/Output: {'yes' if struct['has_outputs'] else 'NO'}",
        f"- Has eval/step: {'yes' if (struct['has_eval'] or struct['has_step']) else 'NO'}",
        f"- Has theorems: {'yes' if struct['has_theorems'] else 'NO'}",
        f"- Schema OK: {'YES' if struct['schema_ok'] else 'NO'}",
        f"",
        f"### Overall status: {status}",
        f"",
        f"### Notes",
        f"<!-- Add manual observations here: error categories, repair rounds, etc. -->",
        f"",
    ]
    log_path.write_text("\n".join(lines))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    import argparse

    parser = argparse.ArgumentParser(description="Check Lean translations")
    parser.add_argument("--tier",   type=int, choices=[1, 2, 3, 4], help="Check only one tier")
    parser.add_argument("--source", choices=["handcrafted", "chat"], help="Check only one source")
    parser.add_argument("--csv",    action="store_true", help="Output results as CSV")
    parser.add_argument("--logs",   action="store_true", help="Write per-module .log log files to logs/")
    parser.add_argument("--no-compile", action="store_true", help="Skip compilation (structural checks only)")
    args = parser.parse_args()

    tiers   = [args.tier]   if args.tier   else []
    sources = [args.source] if args.source else ["handcrafted", "chat"]

    entries = collect_files(tiers, sources)
    if not entries:
        print("No .lean files found.")
        sys.exit(0)

    rows = []
    for entry in entries:
        path   = entry["path"]
        struct = check_structural(path)

        compiles      = True
        sorry_warned  = False
        error_output  = ""
        if not args.no_compile:
            compiles, sorry_warned, error_output = compile_lean_file(path)
            compile_str = "yes" if compiles else "NO"
        else:
            compile_str = "skip"

        sorry_ok = struct["sorry_free"] and not sorry_warned
        row = {
            "tier":          entry["tier"],
            "source":        entry["source"],
            "module":        path.stem,
            "compiles":      compile_str,
            "sorry_free":    "yes" if sorry_ok        else "NO",
            "sorry_detail":  ("text+compiler" if (struct["sorry_free"] and not sorry_warned)
                              else ("compiler_warn" if (struct["sorry_free"] and sorry_warned)
                              else "text")),
            "schema_ok":     "YES" if struct["schema_ok"] else "NO",
            "has_theorems":  "yes" if struct["has_theorems"] else "NO",
            "module_type":   struct["module_type"],
        }
        rows.append(row)

        if args.logs:
            write_log(entry, struct, compiles, sorry_warned, error_output)
            print(f"  Logged: logs/Tier{entry['tier']}/{path.stem}_{entry['source']}.log")

        # Print per-file issues immediately
        if not compiles and not args.csv:
            print(f"\n[COMPILE ERROR] {path.name}")
            print(error_output[:800])
            print()
        elif sorry_warned and not args.csv:
            print(f"\n[SORRY WARNING] {path.name}")
            lines = [l for l in error_output.splitlines() if "sorry" in l.lower()]
            print("\n".join(lines[:5]))
            print()

    if args.csv:
        writer = csv.DictWriter(sys.stdout, fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
        return

    # Pretty table
    col = f"{'T':<2} {'Source':<13} {'Module':<35} {'Compiles':<10} {'Sorry-free':<12} {'Schema OK':<10} {'Type':<14}"
    print(col)
    print("-" * len(col))
    for r in rows:
        print(
            f"{r['tier']:<2} {r['source']:<13} {r['module']:<35} "
            f"{r['compiles']:<10} {r['sorry_free']:<12} {r['schema_ok']:<10} {r['module_type']:<14}"
        )

    print()
    total      = len(rows)
    compiled   = sum(1 for r in rows if r["compiles"] == "yes")
    sorry_free = sum(1 for r in rows if r["sorry_free"] == "yes")
    schema_ok  = sum(1 for r in rows if r["schema_ok"] == "YES")

    skipped = any(r["compiles"] == "skip" for r in rows)
    if not skipped:
        print(f"Compiles: {compiled}/{total}  |  Sorry-free: {sorry_free}/{total}  |  Schema-OK: {schema_ok}/{total}")
    else:
        print(f"Sorry-free: {sorry_free}/{total}  |  Schema-OK: {schema_ok}/{total}  (compilation skipped)")

    # Summary by source
    for src in ["handcrafted", "chat"]:
        src_rows = [r for r in rows if r["source"] == src]
        if not src_rows:
            continue
        n = len(src_rows)
        c = sum(1 for r in src_rows if r["compiles"] == "yes")
        s = sum(1 for r in src_rows if r["schema_ok"] == "YES")
        if not skipped:
            print(f"  [{src}]  compiles={c}/{n}  schema-ok={s}/{n}")
        else:
            print(f"  [{src}]  schema-ok={s}/{n}")


if __name__ == "__main__":
    main()
