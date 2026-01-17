import sys
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
sys.path.append(str(ROOT / "metamath-logic" / "src"))
sys.path.append(str(ROOT / "metamath-prelude" / "src"))
sys.path.append(str(ROOT / "proof-scaffold" / "src"))

from logic.propositional.hilbert import (
    SETMM_TO_HILBERT_AXIOMS,
    SETMM_TO_HILBERT_RULES,
)
from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS

setmm_path = ROOT / "metamath" / "set.mm"
out_path = ROOT / "metamath-logic" / "LEMMA_CATALOGUE.md"

lines = []
if setmm_path.exists():
    with setmm_path.open("r", encoding="utf-8", errors="ignore") as f:
        lines = f.readlines()

def find_label_line(label: str) -> int | None:
    pat = re.compile(rf"^\s*{re.escape(label)}\s+\$(?:a|p|f|e)\b")
    for i, ln in enumerate(lines, start=1):
        if pat.search(ln):
            return i
    return None

rows: list[tuple[str, str, str, str, str]] = []
for k, v in sorted(SETMM_TO_HILBERT_AXIOMS.items()):
    ln = find_label_line(k)
    link = f"file://{setmm_path}#L{ln}" if ln else f"file://{setmm_path}"
    rows.append((k, v, "Axiom", link, "✔️ 实现"))
for k, v in sorted(SETMM_TO_HILBERT_RULES.items()):
    ln = find_label_line(k)
    link = f"file://{setmm_path}#L{ln}" if ln else f"file://{setmm_path}"
    rows.append((k, v, "Rule", link, "✔️ 实现"))
for k, ctor in sorted(SETMM_TO_HILBERT_LEMMAS.items()):
    ln = find_label_line(k)
    link = f"file://{setmm_path}#L{ln}" if ln else f"file://{setmm_path}"
    rows.append((k, getattr(ctor, "__name__", str(ctor)), "Lemma", link, "✔️ 实现"))

md: list[str] = []
md.append("# Lemma Catalogue")
md.append("")
md.append("| set.mm 标签 | 本地名称/函数 | 类别 | set.mm 链接 | 状态 |")
md.append("|-------------|----------------|------|-------------|------|")
for k, v, cat, link, st in rows:
    md.append(f"| {k} | {v} | {cat} | {link} | {st} |")
content = "\n".join(md) + "\n"
out_path.write_text(content, encoding="utf-8")

