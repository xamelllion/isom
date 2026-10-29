#!/usr/bin/env python3
"""
Готовит данные для отчёта из результатов compare.py.

Читает ../../bench/results.csv, ../../bench/samples.json и ../../bench/full_run.log (их пишет
`python3 compare.py` в корне проекта). Пишет рядом с собой:
  scale_<набор>.csv   — время Python и C++ от размера задачи (для графиков);
  speedup_*.csv       — ускорение по задачам и среднее по наборам;
  results_table.tex   — строки таблицы времён;
  macros.tex          — числа, которые упоминаются в тексте.

Время в таблице — среднее ± стандартное отклонение, округлённые по правилам
шпаргалки https://github.com/spbu-se/measurements: в погрешности одна значащая
цифра (две, если первая — единица), среднее — до той же точности.

Запуск: python3 data/prepare.py (из каталога report) или make data.
"""

from __future__ import annotations

import csv
import json
import math
import re
import statistics
from decimal import ROUND_HALF_UP, Decimal
from pathlib import Path

HERE = Path(__file__).resolve().parent
BENCH = HERE.parent.parent / "bench"

FAMILIES = ["paper", "rigid", "rigid-non", "cycle", "cycle-non", "brothers", "ladder", "ladder-non"]
BULK = ["random", "random-mid"]


def tex_number(s: str) -> str:
    """Десятичная запятая и тонкие пробелы между разрядами у чисел от 10 000."""
    whole, _, frac = s.partition(".")
    if len(whole.lstrip("-")) > 4:
        whole = re.sub(r"(?<=\d)(?=(\d{3})+$)", r"\\,", whole)
    return whole + ("{,}" + frac if frac else "")


def num(x: float, digits: int = 3) -> str:
    """Число с `digits` значащими цифрами."""
    if x == 0:
        return "0"
    decimals = max(0, digits - 1 - math.floor(math.log10(abs(x))))
    return tex_number(f"{x:.{decimals}f}")


def rounded(x: float, decimals: int) -> str:
    """x, округлённое до `decimals` знаков после запятой (может быть отрицательным)."""
    q = Decimal(1).scaleb(-decimals)
    v = (Decimal(repr(x)) / q).quantize(Decimal(1), rounding=ROUND_HALF_UP) * q
    return f"{v:.{max(decimals, 0)}f}"


def pm(mean: float, std: float) -> str:
    """Среднее ± с.о. по правилам округления шпаргалки."""
    e = math.floor(math.log10(std))
    first = int(Decimal(repr(std)).scaleb(-e))
    decimals = (1 if first == 1 else 0) - e
    return f"{tex_number(rounded(mean, decimals))} $\\pm$ {tex_number(rounded(std, decimals))}"


def times(x: float) -> str:
    """Кратность: целое число раз, если не меньше 10, иначе с одним знаком."""
    s = f"{x:.0f}" if x >= 10 else f"{x:.1f}".replace(".", "{,}")
    return s + "$\\times$"


def percent(x: float) -> str:
    return f"{x * 100:.1f}".replace(".", "{,}")


def main() -> None:
    rows = list(csv.DictReader(open(BENCH / "results.csv", encoding="utf-8")))
    for r in rows:
        for k in ("py_mean_ms", "py_std_ms", "cpp_mean_ms", "cpp_std_ms", "speedup"):
            r[k] = float(r[k])
        for k in ("tasks", "n", "n_min", "edges", "iso", "unifiers", "nodes", "py_n", "cpp_n",
                  "py_dropped", "cpp_dropped", "py_number", "cpp_number"):
            r[k] = int(r[k])
    by_fam = {f: [r for r in rows if r["family"] == f] for f in FAMILIES + BULK}

    # --- графики зависимости от размера ---
    def param(r: dict) -> int:
        if r["family"] == "brothers":
            return int(r["case"].rsplit("k", 1)[1])
        if r["family"].startswith("ladder"):
            return int(r["case"].rsplit("d", 1)[1])
        return r["n"]

    for fam in FAMILIES[1:]:
        with open(HERE / f"scale_{fam}.csv", "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(["x", "py", "py_std", "cpp", "cpp_std"])
            for r in sorted(by_fam[fam], key=param):
                w.writerow([param(r), f"{r['py_mean_ms']:.6g}", f"{r['py_std_ms']:.3g}",
                            f"{r['cpp_mean_ms']:.6g}", f"{r['cpp_std_ms']:.3g}"])

    # --- ускорение по задачам (точки с небольшим разносом по x) и среднее геометрическое ---
    gmeans = {}
    with open(HERE / "speedup_points.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["x", "speedup"])
        for i, fam in enumerate(FAMILIES, 1):
            sp = sorted(r["speedup"] for r in by_fam[fam])
            gmeans[fam] = math.exp(statistics.fmean(map(math.log, sp)))
            for j, s in enumerate(sp):
                dx = -0.22 + 0.44 * j / (len(sp) - 1) if len(sp) > 1 else 0.0
                w.writerow([f"{i + dx:.3f}", f"{s:.2f}"])
    with open(HERE / "speedup_means.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["x", "gmean"])
        for i, fam in enumerate(FAMILIES, 1):
            w.writerow([i, f"{gmeans[fam]:.2f}"])

    # --- таблица времён: самая большая задача каждого набора + суммы по наборам из многих задач ---
    lines = []
    for fam in FAMILIES[1:]:
        r = max(by_fam[fam], key=lambda r: r["py_mean_ms"])
        lines.append(" & ".join([
            f"\\texttt{{{r['case'].replace('_', chr(92) + '_')}}}",
            str(r["n"]), str(r["edges"]), str(r["nodes"]),
            pm(r["py_mean_ms"], r["py_std_ms"]), pm(r["cpp_mean_ms"], r["cpp_std_ms"]),
            times(r["speedup"])]) + " \\\\")
    lines.append("\\midrule")
    fr = by_fam["paper"]  # примеры статьи: сумма по задачам
    py, cpp = sum(r["py_mean_ms"] for r in fr), sum(r["cpp_mean_ms"] for r in fr)
    py_sd = math.sqrt(sum(r["py_std_ms"] ** 2 for r in fr))
    cpp_sd = math.sqrt(sum(r["cpp_std_ms"] ** 2 for r in fr))
    lines.append(" & ".join([
        f"\\texttt{{paper}}: {len(fr)} задач", f"{min(r['n'] for r in fr)}--{max(r['n'] for r in fr)}",
        "", "", pm(py, py_sd), pm(cpp, cpp_sd), times(py / cpp)]) + " \\\\")
    for fam in BULK:  # все задачи набора подряд — один замер
        (r,) = by_fam[fam]
        lines.append(" & ".join([
            f"\\texttt{{{fam}}}: {r['tasks']} задач", f"{r['n_min']}--{r['n']}", "", "",
            pm(r["py_mean_ms"], r["py_std_ms"]), pm(r["cpp_mean_ms"], r["cpp_std_ms"]),
            times(r["speedup"])]) + " \\\\")
    (HERE / "results_table.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")

    # --- числа для текста ---
    log = (BENCH / "full_run.log").read_text(encoding="utf-8")
    checks = int(re.search(r"Проверок корректности: (\d+)", log).group(1))
    mismatches = int(re.search(r"Проверок корректности: \d+, расхождений: (\d+)", log).group(1))
    retried = int(re.search(r"повторных серий: (\d+)", log).group(1))
    min_sample = float(re.search(r"min_sample=([\d.]+)", log).group(1))
    sp_all = [r["speedup"] for f in FAMILIES for r in by_fam[f]]
    cv_py = [r["py_std_ms"] / r["py_mean_ms"] for r in rows]
    cv_cpp = [r["cpp_std_ms"] / r["cpp_mean_ms"] for r in rows]
    sp_err = [math.hypot(a, b) for a, b in zip(cv_py, cv_cpp)]
    # серии, где больше одного значения лежит дальше 3 с.о. от среднего (по сырым замерам)
    raw = json.loads((BENCH / "samples.json").read_text(encoding="utf-8"))
    multi_outliers = 0
    for d in raw.values():
        for xs in (d["py"], d["cpp"]):
            m, sd = statistics.fmean(xs), statistics.stdev(xs)
            multi_outliers += sum(abs(x - m) > 3 * sd for x in xs) > 1

    def ratio(fam: str, key: str) -> float:
        pts = sorted(by_fam[fam], key=param)[-2:]
        return pts[1][key] / pts[0][key]

    bulk = {f: by_fam[f][0]["speedup"] for f in BULK}
    macros = {
        "NChecks": str(checks),
        "NMismatches": str(mismatches),
        "NCases": str(sum(r["tasks"] for r in rows)),
        "NRepeat": str(max(r["py_n"] + r["py_dropped"] for r in rows)),
        "MinSampleMs": num(min_sample * 1e3, 2),
        "NSeries": str(2 * len(rows)),
        "NDropped": str(sum(r["py_dropped"] + r["cpp_dropped"] for r in rows)),
        "NRetried": str(retried),
        "NMultiOutliers": str(multi_outliers),
        "CvPyMedian": percent(statistics.median(cv_py)),
        "CvPyMax": percent(max(cv_py)),
        "CvCppMedian": percent(statistics.median(cv_cpp)),
        "CvCppMax": percent(max(cv_cpp)),
        "SpeedupErrMax": f"{max(sp_err) * 100:.0f}",
        "SpeedupMin": f"{min(sp_all):.0f}",
        "SpeedupMax": f"{max(sp_all):.0f}",
        "SpeedupGeo": f"{math.exp(statistics.fmean(map(math.log, sp_all))):.0f}",
        "SpeedupRandom": f"{bulk['random']:.0f}",
        "SpeedupRandomMid": f"{bulk['random-mid']:.0f}",
        "RigidRatioPy": num(ratio("rigid", "py_mean_ms"), 2),
        "RigidRatioCpp": num(ratio("rigid", "cpp_mean_ms"), 2),
        "RigidRatioEdges": num(ratio("rigid", "edges"), 2),
        "BrothersRatioPy": num(ratio("brothers", "py_mean_ms"), 2),
        "BrothersRatioCpp": num(ratio("brothers", "cpp_mean_ms"), 2),
        "CycleRatioPy": num(ratio("cycle", "py_mean_ms"), 2),
        "CycleRatioCpp": num(ratio("cycle", "cpp_mean_ms"), 2),
        "LadderRatioPy": num(ratio("ladder", "py_mean_ms"), 2),
        "LadderRatioCpp": num(ratio("ladder", "cpp_mean_ms"), 2),
    }
    for fam in FAMILIES:
        name = "".join(p.capitalize() for p in fam.split("-"))
        macros[f"Gmean{name}"] = f"{gmeans[fam]:.0f}"
    (HERE / "macros.tex").write_text(
        "% Сгенерировано data/prepare.py — не редактировать вручную.\n"
        + "".join(f"\\newcommand{{\\{k}}}{{{v}}}\n" for k, v in macros.items()),
        encoding="utf-8")
    print("готово:", ", ".join(f"{k}={v}" for k, v in macros.items()))


if __name__ == "__main__":
    main()
