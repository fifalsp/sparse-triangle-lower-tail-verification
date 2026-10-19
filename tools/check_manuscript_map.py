#!/usr/bin/env python3
"""Compare stable LaTeX anchors with the Lean proof-map snapshot.

Read-only: this tool never updates proof status or accepts changed statements.
Run against a freshly exported .tex file after any manuscript revision.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

ENV = re.compile(r"\\(begin|end)\{(theorem|lemma|corollary|proposition|definition|equation\*?|align\*?)\}")
LABEL = re.compile(r"\\label\{([^{}]+)\}")


def strip_comments(text: str) -> str:
    lines = []
    for line in text.splitlines():
        for i, char in enumerate(line):
            if char == "%":
                slashes = len(line[:i]) - len(line[:i].rstrip("\\"))
                if slashes % 2 == 0:
                    line = line[:i]
                    break
        lines.append(line)
    return "\n".join(lines)


def normalize(text: str) -> str:
    return " ".join(LABEL.sub("", strip_comments(text)).split())


def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def extract(text: str) -> dict[str, dict]:
    clean = strip_comments(text)
    stack = []
    spans = []
    for m in ENV.finditer(clean):
        kind, env = m.groups()
        if kind == "begin":
            stack.append((env, m.start(), m.end()))
        else:
            if not stack or stack[-1][0] != env:
                raise ValueError(f"Unmatched environment {env} at offset {m.start()}")
            _, start, body = stack.pop()
            spans.append((start, m.end(), body, m.start(), env))
    if stack:
        raise ValueError("Unclosed statement environment")
    result = {}
    for label in LABEL.finditer(clean):
        enclosing = [s for s in spans if s[0] <= label.start() < s[1]]
        if not enclosing:
            continue  # Section labels are not theorem statements.
        start, end, body, finish, env = min(enclosing, key=lambda s: s[1]-s[0])
        key = label.group(1)
        if key in result:
            raise ValueError(f"Duplicate statement label: {key}")
        statement = normalize(clean[body:finish])
        tail = clean[end:]
        proof = re.match(r"\s*\\begin\{proof\}(?:\[[^\]]*\])?", tail)
        proof_hash = None
        if proof:
            stop = tail.find(r"\end{proof}", proof.end())
            if stop < 0:
                raise ValueError(f"Unclosed proof following {key}")
            proof_hash = digest(normalize(tail[proof.end():stop]))
        result[key] = {
            "environment": env,
            "statement": statement,
            "statement_sha256": digest(statement),
            "proof_sha256": proof_hash,
            "source_line": clean.count("\n", 0, start) + 1,
        }
    return result


def compare(text: str, mapping: dict) -> dict:
    current = extract(text)
    changes = []
    for entry in mapping["entries"]:
        key = entry["paper_label"]
        baseline = entry["baseline"]
        now = current.get(key)
        if now is None:
            changes.append({"paper_label": key, "status": "missing_or_renamed"})
        elif now["statement_sha256"] != baseline["statement_sha256"]:
            changes.append({"paper_label": key, "status": "statement_changed",
                            "old_statement": baseline["statement"],
                            "new_statement": now["statement"]})
        elif now["proof_sha256"] != baseline["proof_sha256"]:
            changes.append({"paper_label": key, "status": "proof_changed"})
    return {
        "status": "review_required" if changes else "mapped_statements_unchanged",
        "checked_labels": len(mapping["entries"]),
        "source_sha256": digest(text),
        "baseline_source_sha256": mapping["manuscript"]["sha256"],
        "changes": changes,
        "scope": "Only mapped statements and adjacent proofs are checked; this is not mathematical verification.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manuscript", type=Path)
    parser.add_argument("--map", type=Path, default=Path(__file__).resolve().parents[1]/"lean/proof-map.json")
    args = parser.parse_args()
    try:
        report = compare(args.manuscript.read_text(), json.loads(args.map.read_text()))
    except (ValueError, OSError, KeyError) as exc:
        parser.exit(2, f"Cannot compare manuscript: {exc}\n")
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 1 if report["changes"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
