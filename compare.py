#!/usr/bin/env python3
"""
Сравнение двух реализаций алгоритмов статьи Т. М. Косовской
«On the isomorphism of hypergraphs of relations»:

  * hypergraph_isomorphism.py  — Python;
  * hypergraph_isomorphism.cpp — C++ (собирается автоматически, g++ -O2).

Обе реализации получают одни и те же задачи (пары G1, G2) в текстовом формате
examples.txt. Скрипт проверяет, что результаты совпадают, и сравнивает время.

Проверки корректности на каждой задаче:
  * ответ «изоморфны / нет» и множество изоморфизмов G2 → G1;
  * статистика дерева поиска ISOM-n: вызовы MAP, отсечения MAP, вершины
    (вызовы ISOM⁻-1), кандидаты r, согласованные T, полные и частичные
    унификаторы. Совпадение означает, что обе реализации делают один и тот же поиск;
  * на малых задачах — полный перебор n! (в обеих реализациях) и ISOM-1,
    если предикат один;
  * на примерах статьи — построчное совпадение подробных логов (verbose).

Скорость: время isom_n с поиском всех унификаторов, без чтения входа и
построения шаблона H. Замеры — по шпаргалке https://github.com/spbu-se/measurements:
прогревочный запуск, затем --repeat замеров (40); короткие задачи замеряются
пачками запусков не короче --min-sample (20 мс), как в timeit; в наборах из
многих мелких задач (random, random-mid) замер — решение всех задач подряд.
По серии считаются
среднее и стандартное отклонение (ddof=1); с.о. должно быть меньше 10 % среднего,
одиночный выброс можно отбросить, иначе серия замеряется заново (до двух раз).
Сырые замеры сохраняются в bench/samples.json.

Наборы задач:
  paper      — примеры из статьи (examples.txt);
  random     — малые случайные пары, как в self_test (сверка с перебором);
  random-mid — случайные пары с 3–5 предикатами и n = 12…20 (сверка Python и C++);
  rigid      — у всех вершин разные характеристики: классы отображения
               одноэлементны, поиск идёт без ветвлений, видна полиномиальная часть;
  rigid-non  — то же, но в G2 у двух рёбер переставлены аргументы на одном месте:
               характеристики совпадают, гиперграфы не изоморфны;
  cycle      — ориентированный цикл: один класс из n вершин, ISOM⁻-1 перебирает
               n! перестановок (худший случай); унификаторов n;
  cycle-non  — цикл длины n против двух циклов: характеристики совпадают,
               не изоморфны, перебор n! впустую;
  brothers   — одно коммутативное ребро арности k: k! унификаторов;
  ladder     — «лестница» из d перекладин: дерево ISOM-n растёт как 2^d,
               видна стоимость MAP / CONSISTENCY / REDUCTION и очереди;
  ladder-non — то же, но второй цикл переставлен: не изоморфны, обходится всё дерево.

Запуск:
  python3 compare.py                  # все наборы
  python3 compare.py --quick          # уменьшенные размеры
  python3 compare.py --cases my.txt   # свои задачи в формате examples.txt
Результаты: таблица в терминале, bench/results.csv, bench/samples.json,
bench/cases_*.txt (входы C++).
"""

from __future__ import annotations

import argparse
import contextlib
import csv
import io
import json
import math
import random
import statistics
import subprocess
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

import hypergraph_isomorphism as hi

ROOT = Path(__file__).resolve().parent
CPP_SRC = ROOT / "hypergraph_isomorphism.cpp"
CPP_BIN = ROOT / "hypergraph_isomorphism"
BENCH = ROOT / "bench"
BULK = ("random", "random-mid")  # наборы из многих мелких задач
STAT_KEYS = ("map_calls", "map_fail", "nodes", "cands", "consistent", "complete", "partial")


@dataclass
class Case:
    name: str
    G1: hi.Hypergraph
    G2: hi.Hypergraph
    family: str = "custom"


# ---------------------------------------------------------------------------
#  Формат файла с задачами (см. examples.txt)
# ---------------------------------------------------------------------------

def read_cases(path: Path, family: str = "custom") -> list[Case]:
    cases, cur, preds = [], None, {}
    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        tok = line.split("#", 1)[0].split()
        if not tok:
            continue
        kw = tok[0]
        if kw == "case":
            cur, preds = {"name": tok[1], "g1": [], "g2": []}, {}
        elif kw == "pred":
            preds[tok[1]] = hi.Pred(tok[1], int(tok[2]), tok[3] == "c")
        elif kw in ("g1", "g2"):
            cur[kw].append(hi.edge(preds[tok[1]], *tok[2:]))
        elif kw == "end":
            cases.append(Case(cur["name"], hi.Hypergraph(cur["g1"]),
                              hi.Hypergraph(cur["g2"]), family))
        else:
            raise ValueError(f"{path}:{lineno}: неизвестное слово {kw}")
    return cases


def write_cases(path: Path, cases: list[Case]) -> None:
    lines = []
    for c in cases:
        preds = sorted({e.pred for e in c.G1.edges} | {e.pred for e in c.G2.edges}, key=str)
        assert len({p.name for p in preds}) == len(preds), f"{c.name}: имена предикатов повторяются"
        lines.append(f"case {c.name}")
        lines += [f"pred {p.name} {p.arity} {'c' if p.commutative else 'n'}" for p in preds]
        for tag, G in (("g1", c.G1), ("g2", c.G2)):
            for e in G.edges.elements():
                args = sorted(e.args, key=hi.natural_key) if e.pred.commutative else e.args
                lines.append(f"{tag} {e.pred.name} {' '.join(map(str, args))}")
        lines.append("end")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
#  Генераторы задач
# ---------------------------------------------------------------------------

SELF_TEST_POOL = [hi.Pred("p", 1), hi.Pred("q", 2), hi.Pred("r", 3), hi.Pred("s", 2, True),
                  hi.Pred("t", 3, True), hi.Pred("u", 3)]


def gen_random(count: int, rng: random.Random) -> list[Case]:
    """Малые случайные пары, как в self_test: примерно половина изоморфны."""
    cases = []
    for i in range(1, count + 1):
        n = rng.randint(3, 7)
        preds = rng.sample(SELF_TEST_POOL, rng.randint(1, 3))
        spec = [(p, rng.randint(1, 5)) for p in preds]
        G1 = hi.random_hypergraph(n, spec, rng)
        other = G1 if rng.random() < 0.5 else hi.random_hypergraph(n, spec, rng)
        cases.append(Case(f"random_{i:03d}", G1, hi.relabel(other, rng), "random"))
    return cases


MID_POOL = SELF_TEST_POOL + [hi.Pred("v", 2), hi.Pred("w", 4)]


def gen_random_mid(count: int, rng: random.Random) -> list[Case]:
    """Случайные пары с 3–5 предикатами и n = 12…20; около 70 % изоморфны."""
    cases = []
    for i in range(1, count + 1):
        n = rng.choice([12, 16, 20])
        preds = rng.sample(MID_POOL, rng.randint(3, 5))
        spec = [(p, rng.randint(2, n // 2)) for p in preds]
        G1 = hi.random_hypergraph(n, spec, rng)
        other = G1 if rng.random() < 0.7 else hi.random_hypergraph(n, spec, rng)
        cases.append(Case(f"mid_{i:03d}_n{n}", G1, hi.relabel(other, rng), "random-mid"))
    return cases


def random_edges(pred: hi.Pred, vs: list[str], count: int, rng: random.Random) -> set:
    out: set = set()
    while len(out) < count:
        out.add(hi.edge(pred, *rng.sample(vs, pred.arity)))
    return out


def rigid_hypergraph(m: int, rng: random.Random) -> hi.Hypergraph:
    """
    n = 3m вершин. Рёбра r^3 построены так, что характеристики (n1, n2, n3) всех
    вершин различны: m случайных характеристик берутся вместе с их циклическими
    сдвигами, поэтому суммы по местам равны и рёбра собираются из трёх
    перемешанных списков вхождений. Плюс рёбра s^{c,2}, t^{c,3} и p^1 на
    случайных вершинах — у них классы большие, BESTMAP откладывает их, а
    REDUCTION проверяет, когда переменные уже подставлены.
    """
    R = 1
    while ((R + 1) ** 3 - (R + 1)) // 3 < 2 * m:
        R += 1
    bases: set = set()
    while len(bases) < m:
        s = tuple(rng.randint(0, R) for _ in range(3))
        if len(set(s)) > 1:  # (c, c, c) при сдвиге не меняется
            bases.add(min(s[j:] + s[:j] for j in range(3)))
    sigs = [b[j:] + b[:j] for b in sorted(bases) for j in range(3)]
    rng.shuffle(sigs)
    vs = [f"a{i}" for i in range(1, len(sigs) + 1)]
    cols = [[v for v, s in zip(vs, sigs) for _ in range(s[j])] for j in range(3)]
    for col in cols:
        rng.shuffle(col)

    # чиним рёбра с повторами вершин и совпадающие рёбра обменами внутри столбца:
    # обмен внутри столбца j не меняет характеристик
    E = len(cols[0])
    used: set = set()
    for t in range(E):
        for _ in range(10_000):
            e = (cols[0][t], cols[1][t], cols[2][t])
            if len(set(e)) == 3 and e not in used:
                break
            j, t2 = rng.randrange(3), rng.randrange(E)
            if t2 < t:  # обмен не должен испортить уже собранное ребро t2
                old = (cols[0][t2], cols[1][t2], cols[2][t2])
                new = tuple(cols[j][t] if jj == j else old[jj] for jj in range(3))
                if len(set(new)) < 3 or new in used:
                    continue
                used.discard(old)
                used.add(new)
            cols[j][t], cols[j][t2] = cols[j][t2], cols[j][t]
        else:
            raise RuntimeError("не удалось собрать рёбра")
        used.add(e)

    r, s, t3, p = hi.Pred("r", 3), hi.Pred("s", 2, True), hi.Pred("t", 3, True), hi.Pred("p", 1)
    edges = [hi.edge(r, *e) for e in zip(*cols)]
    n = len(vs)
    edges += random_edges(s, vs, n // 4, rng)
    edges += random_edges(t3, vs, n // 6, rng)
    edges += [hi.edge(p, v) for v in rng.sample(vs, n // 3)]
    return hi.Hypergraph(edges)


def swap_in_column(G: hi.Hypergraph, rng: random.Random) -> hi.Hypergraph:
    """У двух рёбер r^3 обменять аргументы на одном месте: характеристики те же."""
    r_edges = [e for e in G.edges if e.pred.name == "r"]
    others = [e for e in G.edges if e.pred.name != "r"]
    have = {e.args for e in r_edges}
    while True:
        e1, e2 = rng.sample(r_edges, 2)
        j = rng.randrange(3)
        a1, a2 = list(e1.args), list(e2.args)
        a1[j], a2[j] = a2[j], a1[j]
        a1, a2 = tuple(a1), tuple(a2)
        if a1 != e1.args and len(set(a1)) == 3 and len(set(a2)) == 3 \
                and a1 not in have and a2 not in have:
            break
    rest = [e for e in r_edges if e not in (e1, e2)]
    return hi.Hypergraph(others + rest + [hi.edge(e1.pred, *a1), hi.edge(e1.pred, *a2)])


def cycle(lengths: list[int], prefix: str = "a") -> hi.Hypergraph:
    """Объединение ориентированных циклов q(v_i, v_{i+1})."""
    q, edges, start = hi.Pred("q", 2), [], 1
    for n in lengths:
        vs = [f"{prefix}{start + i}" for i in range(n)]
        edges += [hi.edge(q, vs[i], vs[(i + 1) % n]) for i in range(n)]
        start += n
    return hi.Hypergraph(edges)


def ladder(d: int, y_order: list[int] | None = None) -> hi.Hypergraph:
    """
    «Лестница»: ориентированные циклы a_1 → … → a_d и b_1 → … → b_d (предикат f^2)
    и перекладины p_j^{c,2} → {a_j, b_j}, у каждой свой предикат. В f у всех вершин
    характеристика (1, 1), поэтому перестановку концов перекладины не видит ни одна
    характеристика: BESTMAP берёт перекладины по одной (стоимость 2), обе
    подстановки проходят MAP, CONSISTENCY и REDUCTION, и дерево ISOM-n растёт как
    2^d. Лишние ветки отсекаются, только когда f остаётся без переменных.
    y_order — порядок обхода второго цикла.
    """
    y_order = y_order or list(range(1, d + 1))
    f = hi.Pred("f", 2)
    edges = [hi.edge(f, f"a{j}", f"a{j % d + 1}") for j in range(1, d + 1)]
    edges += [hi.edge(f, f"b{y_order[i]}", f"b{y_order[(i + 1) % d]}") for i in range(d)]
    edges += [hi.edge(hi.Pred(f"p{j}", 2, True), f"a{j}", f"b{j}") for j in range(1, d + 1)]
    return hi.Hypergraph(edges)


def make_suites(quick: bool, rng: random.Random) -> list[tuple[str, list[Case], bool]]:
    """(набор, задачи, малые ли — для сверки с перебором и ISOM-1)."""
    rigid_m = [8, 16, 32, 64] if quick else [8, 16, 32, 64, 128, 256]
    cycle_n = range(4, 8) if quick else range(4, 10)
    brothers_k = range(3, 7) if quick else range(3, 9)
    ladder_d = range(2, 8) if quick else range(2, 12)

    rigid, rigid_non = [], []
    for m in rigid_m:
        G1 = rigid_hypergraph(m, rng)
        rigid.append(Case(f"rigid_n{3 * m}", G1, hi.relabel(G1, rng), "rigid"))
        rigid_non.append(Case(f"rigid_non_n{3 * m}", G1, hi.relabel(swap_in_column(G1, rng), rng),
                              "rigid-non"))
    cycles = [Case(f"cycle_n{n}", cycle([n]), hi.relabel(cycle([n]), rng), "cycle")
              for n in cycle_n]
    cycles_non = [Case(f"cycle_non_n{n}", cycle([n]), hi.relabel(cycle([n // 2, n - n // 2]), rng),
                       "cycle-non") for n in cycle_n]
    brothers = []
    for k in brothers_k:
        b = hi.Pred("brothers", k, commutative=True)
        G1 = hi.Hypergraph([hi.edge(b, *[f"a{i}" for i in range(1, k + 1)])])
        brothers.append(Case(f"brothers_k{k}", G1, hi.relabel(G1, rng), "brothers"))
    ladders = [Case(f"ladder_d{d}", ladder(d), hi.relabel(ladder(d), rng), "ladder")
               for d in ladder_d]
    ladders_non = [Case(f"ladder_non_d{d}", ladder(d),
                        hi.relabel(ladder(d, [2, 1, *range(3, d + 1)]), rng), "ladder-non")
                   for d in ladder_d if d >= 3]
    return [
        ("paper", read_cases(ROOT / "examples.txt", "paper"), True),
        ("random", gen_random(100 if quick else 300, rng), True),
        ("random-mid", gen_random_mid(30 if quick else 100, rng), False),
        ("rigid", rigid, False),
        ("rigid-non", rigid_non, False),
        ("cycle", cycles, False),
        ("cycle-non", cycles_non, False),
        ("brothers", brothers, False),
        ("ladder", ladders, False),
        ("ladder-non", ladders_non, False),
    ]


# ---------------------------------------------------------------------------
#  Запуск реализаций
# ---------------------------------------------------------------------------

def build_cpp() -> None:
    if CPP_BIN.exists() and CPP_BIN.stat().st_mtime >= CPP_SRC.stat().st_mtime:
        return
    cmd = ["g++", "-O2", "-std=c++17", "-o", str(CPP_BIN), str(CPP_SRC)]
    print("сборка:", " ".join(cmd))
    subprocess.run(cmd, check=True)


def run_cpp(path: Path, *opts: str) -> dict[str, dict]:
    out = subprocess.run([str(CPP_BIN), *opts, str(path)], capture_output=True, text=True,
                         check=True).stdout
    results: dict[str, dict] = {}
    cur: dict = {}
    for line in out.splitlines():
        if line.startswith("case "):
            cur = results[line[5:]] = {"log": [], "isos": set()}
        elif line == "end":
            cur = {}
        elif line.startswith("| "):
            cur["log"].append(line[2:])
        elif line == "u" or line.startswith("u "):
            cur["isos"].add(line[2:])
        else:
            key, _, val = line.partition(" ")
            if key == "stats":
                cur["stats"] = {k: int(v) for k, v in (kv.split("=") for kv in val.split())}
            else:
                cur[key] = val
    return results


def iso_strings(unifiers: list[dict], rename: dict) -> set[str]:
    """Унификаторы λ → изоморфизмы G2 → G1 в том же виде, что печатает C++."""
    order = sorted(rename, key=hi.natural_key)
    return {" ".join(f"{b}={lam[rename[b]]}" for b in order) for lam in unifiers}


@contextlib.contextmanager
def instrumented():
    """Обёртки над подпроцедурами ISOM-n, считающие ту же статистику, что и C++."""
    st: Counter = Counter()
    names = ("map_procedure", "isom_minus_1", "consistency", "reduction")
    orig = {f: getattr(hi, f) for f in names}

    def map_procedure(*a):
        res = orig["map_procedure"](*a)
        st["map_calls"] += 1
        st["map_fail"] += res is None
        return res

    def isom_minus_1(*a):
        res = orig["isom_minus_1"](*a)
        st["nodes"] += 1
        st["cands"] += len(res)
        return res

    def consistency(*a):
        res = orig["consistency"](*a)
        st["consistent"] += len(res)
        return res

    def reduction(*a):
        complete, partial = orig["reduction"](*a)
        st["complete"] += len(complete)
        st["partial"] += len(partial)
        return complete, partial

    for f, fn in zip(names, (map_procedure, isom_minus_1, consistency, reduction)):
        setattr(hi, f, fn)
    try:
        yield st
    finally:
        for f, fn in orig.items():
            setattr(hi, f, fn)


CV_LIMIT = 0.10  # шпаргалка: с.о. должно быть меньше 10 % среднего


def measure(fn, repeat: int, min_sample: float) -> tuple[list[float], int]:
    """
    Прогревочный запуск, затем `repeat` замеров. Короткие задачи замеряются пачками
    из `number` запусков не короче min_sample (как в timeit), замер — среднее время
    одного запуска в пачке. Возвращает (замеры в мс, number). Так же устроен C++.
    """
    def batch(k: int) -> float:
        t0 = time.perf_counter()
        for _ in range(k):
            fn()
        return time.perf_counter() - t0

    t, number = batch(1), 1
    while t < min_sample:
        number *= 2
        t = batch(number)
    return [batch(number) / number * 1e3 for _ in range(repeat)], number


def summarize(samples: list[float]) -> dict:
    """Среднее и с.о. (ddof=1); одиночный выброс отбрасывается, если без него с.о. < 10 %."""
    mean, sd, dropped = statistics.fmean(samples), statistics.stdev(samples), 0
    if sd >= CV_LIMIT * mean:
        rest = list(samples)
        rest.remove(max(samples, key=lambda x: abs(x - mean)))
        if statistics.stdev(rest) < CV_LIMIT * statistics.fmean(rest):
            mean, sd, dropped = statistics.fmean(rest), statistics.stdev(rest), 1
    return {"mean": mean, "std": sd, "n": len(samples) - dropped, "dropped": dropped,
            "stable": sd < CV_LIMIT * mean}


def run_python(c: Case, verbose: bool) -> dict:
    H, rename = hi.make_template(c.G2)
    with instrumented() as st:
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            res = hi.isom_n(c.G1, H, verbose=verbose)
    return {"iso": res.isomorphic, "isos": iso_strings(res.unifiers, rename),
            "n_unifiers": len(res.unifiers),
            "stats": {k: st[k] for k in STAT_KEYS}, "log": buf.getvalue().splitlines(),
            "H": H, "rename": rename}


def time_python(c: Case, H: hi.Hypergraph, repeat: int, min_sample: float) -> tuple[list[float], int]:
    return measure(lambda: hi.isom_n(c.G1, H), repeat, min_sample)


def cpp_samples(r: dict) -> tuple[list[float], int]:
    return [float(x) for x in r["samples_ms"].split()], int(r["number"])


def rerun_cpp(cases: list[Case], timing: tuple) -> dict[str, dict]:
    one = BENCH / "retry.txt"
    write_cases(one, cases)
    try:
        return run_cpp(one, "--no-maps", *timing)
    finally:
        one.unlink()


def timed_series(py_measure, cpp_first, cpp_again):
    """
    Замеры Python и C++; серия, где с.о. ≥ 10 % и после отбрасывания одиночного
    выброса, замеряется заново (до двух раз). Возвращает замеры и число повторов.
    """
    retried = 0
    py_s, py_num = py_measure()
    for _ in range(2):
        if summarize(py_s)["stable"]:
            break
        retried += 1
        py_s, py_num = py_measure()
    cpp_s, cpp_num = cpp_first()
    for _ in range(2):
        if summarize(cpp_s)["stable"]:
            break
        retried += 1
        cpp_s, cpp_num = cpp_samples(cpp_again())
    return py_s, py_num, cpp_s, cpp_num, retried


def make_row(family: str, name: str, infos: list[dict], py_s, py_num, cpp_s, cpp_num) -> dict:
    pt, ct = summarize(py_s), summarize(cpp_s)
    return {
        "family": family, "case": name, "tasks": len(infos),
        "n": max(i["n"] for i in infos), "n_min": min(i["n"] for i in infos),
        "edges": sum(i["edges"] for i in infos), "iso": sum(i["iso"] for i in infos),
        "unifiers": sum(i["unifiers"] for i in infos), "nodes": sum(i["nodes"] for i in infos),
        "py_mean_ms": pt["mean"], "py_std_ms": pt["std"], "py_n": pt["n"],
        "py_dropped": pt["dropped"], "py_number": py_num,
        "cpp_mean_ms": ct["mean"], "cpp_std_ms": ct["std"], "cpp_n": ct["n"],
        "cpp_dropped": ct["dropped"], "cpp_number": cpp_num,
        "speedup": pt["mean"] / ct["mean"],
    }


# ---------------------------------------------------------------------------
#  Сравнение
# ---------------------------------------------------------------------------

def check_case(c: Case, py: dict, cpp: dict, extra: dict, problems: list[str]) -> int:
    """Сверяет результаты одной задачи; возвращает число выполненных проверок."""
    checks = 0

    def expect(ok: bool, what: str) -> None:
        nonlocal checks
        checks += 1
        if not ok:
            problems.append(f"{c.family}/{c.name}: {what}")

    if "error" in cpp:
        expect(False, f"C++ сообщил об ошибке: {cpp['error']}")
        return checks
    expect(py["iso"] == (cpp["iso"] == "1"), "ответ «изоморфны» различается")
    expect(py["n_unifiers"] == len(py["isos"]), "Python выдал один унификатор дважды")
    expect(int(cpp["unifiers"]) == len(cpp["isos"]), "C++ выдал один унификатор дважды")
    expect(py["isos"] == cpp["isos"], f"изоморфизмы различаются (Python {len(py['isos'])}, "
                                      f"C++ {len(cpp['isos'])})")
    stats_cpp = {k: cpp["stats"][k] for k in STAT_KEYS}
    expect(py["stats"] == stats_cpp, f"статистика дерева различается: Python {py['stats']}, "
                                     f"C++ {stats_cpp}")
    if py["log"]:
        expect(py["log"] == cpp["log"], "подробные логи различаются")

    if "brute" in extra:
        H, rename = py["H"], py["rename"]
        brute_py = iso_strings(hi.brute_force(c.G1, H), rename)
        expect(brute_py == py["isos"], "ISOM-n (Python) расходится с перебором")
        expect(extra["brute"][c.name]["isos"] == brute_py, "перебор C++ расходится с Python")
        if len({e.pred for e in c.G1.edges} | {e.pred for e in c.G2.edges}) == 1:
            isom1_py = iso_strings(hi.isom_1(c.G1, H), rename)
            expect(isom1_py == brute_py, "ISOM-1 (Python) расходится с перебором")
            expect(extra["isom_1"][c.name]["isos"] == brute_py, "ISOM-1 (C++) расходится с перебором")
    return checks


def fmt_ms(ms: float) -> str:
    return f"{ms:.3f}" if ms < 10 else f"{ms:.1f}" if ms < 1000 else f"{ms:,.0f}".replace(",", " ")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--quick", action="store_true", help="уменьшенные размеры задач")
    ap.add_argument("--cases", type=Path, help="свой файл задач вместо стандартных наборов")
    ap.add_argument("--repeat", type=int, default=40, help="число замеров на задачу (40)")
    ap.add_argument("--min-sample", type=float, default=0.02,
                    help="минимальная длительность одного замера, с (0.02)")
    ap.add_argument("--seed", type=int, default=2026)
    args = ap.parse_args()
    if args.repeat < 3:
        ap.error("--repeat должен быть не меньше 3")

    build_cpp()
    BENCH.mkdir(exist_ok=True)
    rng = random.Random(args.seed)
    suites = ([("custom", read_cases(args.cases), True)] if args.cases
              else make_suites(args.quick, rng))
    timing = ("--repeat", str(args.repeat), "--min-sample", str(args.min_sample))

    problems: list[str] = []
    rows: list[dict] = []
    samples: dict[str, dict] = {}
    n_checks = retried = 0
    for family, cases, small in suites:
        done: list = []
        path = BENCH / f"cases_{family}.txt"
        write_cases(path, cases)
        t0 = time.perf_counter()
        bulk = family in BULK
        # в наборах из многих мелких задач замером служит решение всех задач подряд
        cpp = run_cpp(path, *(("--repeat", "0") if bulk else timing))
        verbose = family in ("paper", "custom")
        if verbose:
            for name, r in run_cpp(path, "-v", "--no-maps", "--repeat", "0").items():
                cpp[name]["log"] = r["log"]
        extra = {}
        if small:
            extra["brute"] = run_cpp(path, "--algo", "brute", "--repeat", "0")
            extra["isom_1"] = run_cpp(path, "--algo", "isom_1", "--repeat", "0")
        for c in cases:
            py = run_python(c, verbose)
            n_checks += check_case(c, py, cpp[c.name], extra, problems)
            info = {"n": len(c.G1.vertices()), "edges": sum(c.G1.edges.values()),
                    "iso": int(py["iso"]), "unifiers": len(py["isos"]),
                    "nodes": py["stats"]["nodes"], "H": py["H"]}
            if bulk:
                done.append((c, info))
                continue
            if "error" in cpp[c.name]:
                continue
            py_s, py_num, cpp_s, cpp_num, r = timed_series(
                lambda: time_python(c, info["H"], args.repeat, args.min_sample),
                lambda: cpp_samples(cpp[c.name]),
                lambda: rerun_cpp([c], timing)[c.name])
            retried += r
            rows.append(make_row(family, c.name, [info], py_s, py_num, cpp_s, cpp_num))
            samples[c.name] = {"family": family, "py": py_s, "cpp": cpp_s}
        if bulk and done:
            pairs = [(c.G1, info["H"]) for c, info in done]
            run_all = lambda: [hi.isom_n(G1, H) for G1, H in pairs]
            py_s, py_num, cpp_s, cpp_num, r = timed_series(
                lambda: measure(run_all, args.repeat, args.min_sample),
                lambda: cpp_samples(run_cpp(path, "--whole", *timing)["__all__"]),
                lambda: run_cpp(path, "--whole", *timing)["__all__"])
            retried += r
            name = f"{family}_all"
            rows.append(make_row(family, name, [info for _, info in done],
                                 py_s, py_num, cpp_s, cpp_num))
            samples[name] = {"family": family, "py": py_s, "cpp": cpp_s}
        print(f"[{family}] {len(cases)} задач, {time.perf_counter() - t0:.1f} с", flush=True)

    with open(BENCH / "results.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    (BENCH / "samples.json").write_text(json.dumps(samples), encoding="utf-8")

    # --- таблица: среднее и с.о. в процентах от среднего ---
    def cell(mean: float, std: float) -> str:
        return f"{fmt_ms(mean)} ±{std / mean:.0%}"

    head = ("набор", "задача", "n", "|E|", "изом.", "#λ", "вершин", "Python, мс", "C++, мс",
            "ускорение")
    table = []
    for fam in dict.fromkeys(r["family"] for r in rows):
        fam_rows = [r for r in rows if r["family"] == fam]
        for r in fam_rows:
            if r["tasks"] > 1:  # набор из многих задач, решаемых подряд
                table.append((fam, f"{r['tasks']} задач подряд", f"{r['n_min']}–{r['n']}", "",
                              f"{r['iso']}/{r['tasks']}", "", "",
                              cell(r["py_mean_ms"], r["py_std_ms"]),
                              cell(r["cpp_mean_ms"], r["cpp_std_ms"]), f"{r['speedup']:.0f}×"))
                continue
            table.append((fam, r["case"], str(r["n"]), str(r["edges"]), "да" if r["iso"] else "нет",
                          str(r["unifiers"]), str(r["nodes"]),
                          cell(r["py_mean_ms"], r["py_std_ms"]),
                          cell(r["cpp_mean_ms"], r["cpp_std_ms"]), f"{r['speedup']:.0f}×"))
    widths = [max(len(h), *(len(t[i]) for t in table)) for i, h in enumerate(head)]
    right = {2, 3, 5, 6, 7, 8, 9}
    fmt = lambda t: "  ".join(s.rjust(wd) if i in right else s.ljust(wd)
                              for i, (s, wd) in enumerate(zip(t, widths)))
    print()
    print(fmt(head))
    print("  ".join("-" * wd for wd in widths))
    prev = None
    for t in table:
        if prev and t[0] != prev:
            print()
        print(fmt(t))
        prev = t[0]

    sp = [r["speedup"] for r in rows if r["family"] not in BULK and r["py_mean_ms"] >= 1]
    if sp:
        gm = math.exp(sum(map(math.log, sp)) / len(sp))
        print(f"\nУскорение C++ на задачах, где Python работает ≥ 1 мс: "
              f"от {min(sp):.0f}× до {max(sp):.0f}×, среднее геометрическое {gm:.0f}×")
    cvs = [r[f"{k}_std_ms"] / r[f"{k}_mean_ms"] for r in rows for k in ("py", "cpp")]
    unstable = [f"{r['case']} ({k})" for r in rows for k in ("py", "cpp")
                if r[f"{k}_std_ms"] >= CV_LIMIT * r[f"{k}_mean_ms"]]
    dropped = sum(r["py_dropped"] + r["cpp_dropped"] for r in rows)
    print(f"Время — среднее ± с.о. по {args.repeat} замерам isom_n (поиск всех унификаторов); "
          f"«вершин» — вызовов ISOM⁻-1.")
    print(f"Параметры замеров: repeat={args.repeat}, min_sample={args.min_sample} с")
    print(f"С.о. от среднего: медиана {statistics.median(cvs):.1%}, максимум {max(cvs):.1%}; "
          f"отброшено одиночных выбросов: {dropped}; повторных серий: {retried}; "
          f"серий с с.о. ≥ 10 %: {len(unstable)}")
    for u in unstable[:20]:
        print("  ! с.о. ≥ 10 %:", u)
    print(f"Таблица сохранена в {BENCH / 'results.csv'}, замеры — в {BENCH / 'samples.json'}")

    print(f"\nПроверок корректности: {n_checks}, расхождений: {len(problems)}")
    for p in problems[:30]:
        print("  ✗", p)
    if problems:
        raise SystemExit(1)
    print("Python и C++ дают одинаковые ответы, унификаторы и деревья поиска.")


if __name__ == "__main__":
    main()
