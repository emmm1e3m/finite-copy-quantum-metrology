"""重建正式 Lean 库，并审计已导出的定理公理依赖。"""

from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "verification"
REPORT.mkdir(exist_ok=True)
ENV = dict(os.environ, LEAN_NUM_THREADS="2")
LAKE = shutil.which("lake")
if LAKE is None:
    raise SystemExit("找不到 lake；请先按 lean-toolchain 配置 Lean。")


def without_comments(source):
    """保留换行，移除 Lean 的行注释与可嵌套块注释。"""
    result, depth, i = [], 0, 0
    while i < len(source):
        pair = source[i : i + 2]
        if pair == "/-":
            depth += 1
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            i += 2
        elif depth:
            if source[i] == "\n":
                result.append("\n")
            i += 1
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


def declarations(path):
    source = without_comments(path.read_text(encoding="utf-8-sig"))
    bad = re.findall(r"\b(?:sorry|admit|axiom|native_decide)\b", source)
    if bad:
        raise RuntimeError(f"{path.relative_to(ROOT)} 包含未许可证明标记：{bad}")
    scopes = []
    names = []
    for line in source.splitlines():
        line = line.strip()
        ns = re.fullmatch(r"namespace\s+(\S+)", line)
        if ns:
            scopes.append(("namespace", ns[1]))
            continue
        if re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+\S+)?", line):
            scopes.append(("section", ""))
            continue
        if re.fullmatch(r"end(?:\s+\S+)?", line):
            if scopes:
                scopes.pop()
            continue
        line = re.sub(r"^@\[[^]]*\]\s*", "", line)
        match = re.match(r"(?:protected\s+)?(?:theorem|lemma)\s+([^\s(:{\[]+)", line)
        if match:
            names.append(".".join([name for kind, name in scopes if kind == "namespace"] + [match[1]]))
    return names


def run(args, filename):
    process = subprocess.run(
        [LAKE, *args], cwd=ROOT, env=ENV, text=True,
        encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    (REPORT / filename).write_text(process.stdout, encoding="utf-8")
    if process.returncode:
        raise RuntimeError(f"命令失败，详见 verification/{filename}")
    return process.stdout


run(["build"], "build.log")
names = sorted(set(name for path in sorted((ROOT / "FiniteCopy").glob("*.lean"))
                   for name in declarations(path)))
audit = ROOT / "PublicationAudit.lean"
audit.write_text("import FiniteCopy\n\n" + "\n".join(f"#print axioms {name}" for name in names) + "\n",
                 encoding="utf-8")
result = run(["env", "lean", str(audit)], "axioms.log")
allowed = {"propext", "Classical.choice", "Quot.sound"}
used = {name.strip() for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", result)
        for name in group.split(",") if name.strip()}
unexpected = sorted(used - allowed)
summary = {"build_passed": True, "audited_declarations": len(names),
           "used_axioms": sorted(used), "unexpected_axioms": unexpected,
           "scope_note": "编译及公理审计不替代对最终定理前提与物理对象的覆盖审查。"}
(REPORT / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n",
                                     encoding="utf-8")
if unexpected:
    raise RuntimeError(f"发现非预期公理：{unexpected}")
print(json.dumps(summary, ensure_ascii=False, indent=2))
