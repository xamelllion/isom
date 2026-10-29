"""
Проверка изоморфизма гиперграфов отношений по статье
Т. М. Косовской «On the isomorphism of hypergraphs of relations».

Реализовано:
  * характеристики вершин и гиперграфа (определения 2–5);
  * структурное отображение (structure mapping);
  * ISOM-1   — гиперграфы с одной предикатной вершиной;
  * ISOM⁻-1  — ISOM-1 без шагов 1–3 (подпрограмма ISOM-n);
  * ISOM-n   — несколько предикатных вершин:
               MAP → BESTMAP → ISOM⁻-1 → CONSISTENCY → REDUCTION,
               с очередью частичных унификаторов, упорядоченной по стоимости.

Соглашения:
  * объектные вершины в G — любые hashable-константы (обычно строки 'a1');
  * объектные вершины шаблона H — объекты класса Var;
  * унификатор — dict {Var: константа}, т.е. подстановка λ, для которой Hλ = G;
  * гиперребро типа (1): p^k → (ω1, ..., ωk)      — Pred(..., commutative=False);
    гиперребро типа (2): p^{c,k} → {ω1, ..., ωk}  — Pred(..., commutative=True).
"""

from __future__ import annotations

import heapq
import itertools
import math
import random
import re
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from typing import Hashable, Iterable


# ---------------------------------------------------------------------------
#  Базовые структуры
# ---------------------------------------------------------------------------

def natural_key(s) -> list:
    """Ключ «естественной» сортировки: a2 < a10."""
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", str(s))]


@dataclass(frozen=True)
class Var:
    """Переменная — имя объектной вершины в шаблоне H."""
    name: str

    def __repr__(self) -> str:
        return self.name


def is_var(v) -> bool:
    return isinstance(v, Var)


@dataclass(frozen=True)
class Pred:
    """Предикатная вершина: p^k (некоммутативная) или p^{c,k} (коммутативная)."""
    name: str
    arity: int
    commutative: bool = False

    def __post_init__(self) -> None:
        if self.arity < 1:
            raise ValueError(f"арность предиката {self.name} должна быть не меньше 1")

    def __repr__(self) -> str:
        return f"{self.name}^{'c,' if self.commutative else ''}{self.arity}"


@dataclass(frozen=True)
class Edge:
    """Гиперребро: предикатная вершина + кортеж (тип 1) или множество (тип 2)."""
    pred: Pred
    args: tuple | frozenset

    def substitute(self, s: dict) -> "Edge":
        mapped = (s.get(v, v) for v in self.args)
        return Edge(self.pred,
                    frozenset(mapped) if self.pred.commutative else tuple(mapped))

    def is_ground(self) -> bool:
        """Ребро без переменных."""
        return not any(is_var(v) for v in self.args)

    def __repr__(self) -> str:
        if self.pred.commutative:
            inner = "{" + ", ".join(sorted(map(str, self.args), key=natural_key)) + "}"
        else:
            inner = "(" + ", ".join(map(str, self.args)) + ")"
        return f"{self.pred} → {inner}"


def edge(pred: Pred, *args) -> Edge:
    """Удобный конструктор гиперребра с проверками из определения."""
    if len(args) != pred.arity:
        raise ValueError(f"{pred}: ожидалось {pred.arity} аргументов, получено {len(args)}")
    if len(set(args)) != len(args):
        raise ValueError(f"{pred}: аргументы гиперребра должны быть различны: {args}")
    return Edge(pred, frozenset(args) if pred.commutative else tuple(args))


def substitute_edges(edges: Counter, s: dict) -> Counter:
    """Применить подстановку к мультимножеству рёбер."""
    out: Counter = Counter()
    for e, m in edges.items():
        out[e.substitute(s)] += m
    return out


class Hypergraph:
    """Гиперграф отношений как мультимножество гиперрёбер."""

    def __init__(self, edges: Iterable[Edge] | Counter):
        self.edges: Counter = Counter(edges)

    def by_pred(self) -> dict[Pred, Counter]:
        """Подграфы G^i с единственной i-й предикатной вершиной."""
        d: dict[Pred, Counter] = defaultdict(Counter)
        for e, m in self.edges.items():
            d[e.pred][e] += m
        return dict(d)

    def vertices(self) -> set:
        return {v for e in self.edges for v in e.args}

    def substitute(self, s: dict) -> "Hypergraph":
        return Hypergraph(substitute_edges(self.edges, s))

    def __eq__(self, other) -> bool:
        return isinstance(other, Hypergraph) and self.edges == other.edges

    def __repr__(self) -> str:
        items = sorted(self.edges.elements(), key=lambda e: (str(e.pred), natural_key(e)))
        return "{" + ", ".join(map(repr, items)) + "}"


def fmt_sub(s: dict) -> str:
    """Подстановка в виде x1→a6, x2→a1, ..."""
    if not s:
        return "∅"
    return ", ".join(f"{x}→{a}" for x, a in sorted(s.items(), key=lambda kv: natural_key(kv[0])))


# ---------------------------------------------------------------------------
#  Характеристики (определения 2–5)
# ---------------------------------------------------------------------------

def vertex_characteristics(edges: Counter) -> dict:
    """
    χ(v) для каждой вершины подграфа с ОДНОЙ предикатной вершиной.
      тип (1): χ(v) = (n1, ..., nk), nj — число вхождений v на j-е место;
      тип (2): χ(v) = число вхождений v в аргументы рёбер.
    """
    preds = {e.pred for e in edges}
    if len(preds) > 1:
        raise ValueError("характеристики считаются для подграфа с одной предикатной вершиной")
    chars: dict = {}
    for e, m in edges.items():
        if e.pred.commutative:
            for v in e.args:
                chars[v] = chars.get(v, 0) + m
        else:
            for j, v in enumerate(e.args):
                chars.setdefault(v, [0] * e.pred.arity)[j] += m
    return {v: tuple(c) if isinstance(c, list) else c for v, c in chars.items()}


def graph_characteristic(edges: Counter) -> tuple:
    """
    χ(G) — упорядоченный набор характеристик вершин.
    В статье (опр. 3) задан свой порядок; для проверки РАВЕНСТВА характеристик
    годится любой канонический порядок, здесь — лексикографическая сортировка.
    """
    return tuple(sorted(vertex_characteristics(edges).values()))


# ---------------------------------------------------------------------------
#  Структурное отображение
# ---------------------------------------------------------------------------

@dataclass
class StructureMapping:
    """
    {[x_i1, ..., x_it1] : [a_j1, ..., a_jt1], ...}
    Переменные класса можно отображать только в константы того же класса.
    """
    pred: Pred
    classes: list[tuple[tuple, tuple]] = field(default_factory=list)

    @property
    def cost(self) -> int:
        """Число возможных подстановок Π t_k! — мера сложности для BESTMAP."""
        return math.prod(math.factorial(len(xs)) for xs, _ in self.classes)

    def __repr__(self) -> str:
        parts = [f"[{', '.join(map(str, xs))}] : [{', '.join(map(str, cs))}]"
                 for xs, cs in self.classes]
        return "{" + ", ".join(parts) + "}"


def build_mapping(pred: Pred, G_i: Counter, H_i: Counter) -> StructureMapping | None:
    """
    Строит структурное отображение между G^i (константы) и H^iλ
    (переменные + уже подставленные константы). None — если необходимое
    условие изоморфизма нарушено и ветку можно отсечь.
    """
    if sum(G_i.values()) != sum(H_i.values()):
        return None
    chG = vertex_characteristics(G_i)
    chH = vertex_characteristics(H_i)
    if sorted(chG.values()) != sorted(chH.values()):
        return None
    # константы, уже стоящие в H^iλ, должны играть в G^i ту же роль
    fixed = {v for v in chH if not is_var(v)}
    for c in fixed:
        if chG.get(c) != chH[c]:
            return None

    var_classes: dict = defaultdict(list)
    const_classes: dict = defaultdict(list)
    for v, ch in chH.items():
        if is_var(v):
            var_classes[ch].append(v)
    for a, ch in chG.items():
        if a not in fixed:
            const_classes[ch].append(a)

    m = StructureMapping(pred)
    for ch in sorted(var_classes):
        xs, cs = var_classes[ch], const_classes.get(ch, [])
        if len(xs) != len(cs):
            return None
        m.classes.append((tuple(sorted(xs, key=natural_key)),
                          tuple(sorted(cs, key=natural_key))))
    return m


# ---------------------------------------------------------------------------
#  ISOM⁻-1 и ISOM-1
# ---------------------------------------------------------------------------

def isom_minus_1(G_i: Counter, H_i: Counter, mapping: StructureMapping) -> list[dict]:
    """
    ISOM⁻-1: ISOM-1, начиная с шага 4 (отображение уже построено).
    Перебирает подстановки внутри классов отображения с ранним отсечением:
    как только часть рёбер H^iλ становится без переменных, они обязаны
    встречаться в G^i (аналог шагов 8–11: проверка части с уже известными
    константами). Возвращает все локальные унификаторы λ: H^iλ = G^i.

    Каждое ребро проверяется один раз — после назначения того класса, на
    котором в нём не остаётся переменных (рёбра без переменных с самого
    начала — до перебора): образ ранее проверенных рёбер уже не меняется.
    Сравнивать кратности можно поштучно: подстановка вместе с константами,
    уже стоящими в H^iλ, инъективна (классы этих констант не содержат),
    поэтому разные рёбра H^iλ переходят в разные рёбра.
    """
    classes = mapping.classes
    g_args = {e.args: m for e, m in G_i.items()}  # предикат один: ребро задают аргументы
    level = {x: k + 1 for k, (xs, _) in enumerate(classes) for x in xs}
    checks: list[list] = [[] for _ in range(len(classes) + 1)]
    for e, m in H_i.items():
        k = max((level[v] for v in e.args if is_var(v)), default=0)
        checks[k].append((e.args, e.pred.commutative, m))

    s: dict = {}
    result: list[dict] = []

    def fits(edges: list) -> bool:
        for args, commutative, m in edges:
            image = map(s.get, args, args)
            if g_args.get(frozenset(image) if commutative else tuple(image), 0) < m:
                return False
        return True

    def rec(k: int) -> None:
        if k == len(classes):
            if substitute_edges(H_i, s) == G_i:  # шаг 7: H^iλ = G^i
                result.append(dict(s))
            return
        xs, cs = classes[k]
        for perm in itertools.permutations(cs):
            s.update(zip(xs, perm))
            if fits(checks[k + 1]):
                rec(k + 1)
        for x in xs:
            del s[x]

    if fits(checks[0]):
        rec(0)
    return result


def isom_1(G: Hypergraph, H: Hypergraph) -> list[dict]:
    """
    ISOM-1 для гиперграфов с одной предикатной вершиной.
    Возвращает список всех унификаторов λ (Hλ = G); пустой список — не изоморфны.
    """
    preds = {e.pred for e in G.edges} | {e.pred for e in H.edges}
    if len(preds) > 1:
        raise ValueError("ISOM-1 работает с одной предикатной вершиной; используйте isom_n")
    if not preds:
        return [{}]
    (p,) = preds
    G_i = G.by_pred().get(p, Counter())
    H_i = H.by_pred().get(p, Counter())
    # шаги 1–2: характеристики
    if graph_characteristic(G_i) != graph_characteristic(H_i):
        return []
    # шаг 3: структурное отображение
    m = build_mapping(p, G_i, H_i)
    if m is None:
        return []
    # шаги 4–12
    return isom_minus_1(G_i, H_i, m)


# ---------------------------------------------------------------------------
#  Подпроцедуры ISOM-n
# ---------------------------------------------------------------------------

def map_procedure(Gp: dict, Hp: dict, lam: dict, remaining: frozenset):
    """
    MAP: строит mapping^i для каждого ещё не удалённого предиката i, у которого
    в H^iλ остались переменные. None — какое-то отображение невозможно (ветка отсекается).
    """
    maps: dict[Pred, StructureMapping] = {}
    for p in remaining:
        H_i = substitute_edges(Hp[p], lam)
        if all(e.is_ground() for e in H_i):
            continue  # такие подграфы проверяет REDUCTION
        m = build_mapping(p, Gp[p], H_i)
        if m is None:
            return None
        maps[p] = m
    return maps


def bestmap(maps: dict) -> tuple[Pred, StructureMapping]:
    """BESTMAP: выбирает предикат i0 с минимальным Π t_k!."""
    return min(maps.items(), key=lambda kv: (kv[1].cost, str(kv[0])))


def consistency(lam: dict, candidates: list[dict]) -> list[dict]:
    """
    CONSISTENCY: оставляет только те λ^{i0}_j, что вместе с уже найденным λ
    образуют биекцию — нет пар (x/a, x/b) и (x/a, y/a) при x≠y, a≠b.
    """
    inverse = {a: x for x, a in lam.items()}
    return [c for c in candidates
            if all(lam.get(x, a) == a and inverse.get(a, x) == x for x, a in c.items())]


def reduction(Gp: dict, Hp: dict, lam: dict, remaining: frozenset,
              i0: Pred, candidates: list[dict]):
    """
    REDUCTION (рис. 1): для каждого λ_t формирует H_E = Hλλ_t; подграфы H_E^j без
    переменных сравнивает с G^j (совпал — удаляется, нет — ветка отбрасывается).
    H_E = ∅ → полный унификатор; иначе → частичный, в очередь.
    """
    rest = sorted(set(remaining) - {i0}, key=str)  # G := G \ G^{i0} (шаг 5)
    variables = {j: {v for e in Hp[j] for v in e.args if is_var(v)} for j in rest}
    complete, partial = [], []
    for lt in candidates:
        lam2 = {**lam, **lt}
        rem = set(rest)
        ok = True
        for j in rest:
            if lam2.keys() >= variables[j]:  # в H^jλλ_t не осталось переменных
                if substitute_edges(Hp[j], lam2) == Gp[j]:
                    rem.discard(j)
                else:
                    ok = False
                    break
        if not ok:
            continue
        (partial if rem else complete).append((lam2, frozenset(rem)))
    return complete, partial


# ---------------------------------------------------------------------------
#  ISOM-n
# ---------------------------------------------------------------------------

@dataclass
class IsomResult:
    isomorphic: bool
    unifiers: list[dict]
    reason: str = ""

    def __bool__(self) -> bool:
        return self.isomorphic


def isom_n(G: Hypergraph, H: Hypergraph, find_all: bool = True,
           verbose: bool = False) -> IsomResult:
    """
    ISOM-n: проверка изоморфизма гиперграфов отношений G (константы) и H (переменные)
    с несколькими предикатными вершинами. Возвращает все унификаторы λ: Hλ = G
    (или первый найденный, если find_all=False).

    Склейка вершин дерева (замечание в разделе 5) здесь не возникает: BESTMAP
    выбирает i0 однозначно по λ, дети одной вершины различаются значениями
    переменных H^{i0}λ, а у потомков λ только растёт. Поэтому все вершины
    дерева и все найденные унификаторы различны.
    """
    log = print if verbose else (lambda *a, **k: None)
    Gp, Hp = G.by_pred(), H.by_pred()

    # предварительная проверка: те же предикаты и равные характеристики подграфов
    if set(Gp) != set(Hp):
        return IsomResult(False, [], "разные наборы предикатных вершин")
    for p in sorted(Gp, key=str):
        if graph_characteristic(Gp[p]) != graph_characteristic(Hp[p]):
            return IsomResult(False, [], f"характеристики подграфов с {p} различны")
    if not Gp:
        return IsomResult(True, [{}])

    queue: list = []
    counter = itertools.count()
    unifiers: list[dict] = []

    def push(lam: dict, rem: frozenset, depth: int) -> None:
        maps = map_procedure(Gp, Hp, lam, rem)
        if maps is None:
            log(f"{'  ' * depth}✗ MAP: при λ={fmt_sub(lam)} характеристики не согласуются — ветка отсечена")
            return
        i0, m = bestmap(maps)
        log(f"{'  ' * depth}MAP/BESTMAP: λ={fmt_sub(lam)} → предикат {i0}, "
            f"mapping={m}, Π t_k! = {m.cost}")
        heapq.heappush(queue, (m.cost, next(counter), depth, lam, rem, i0, m))

    push({}, frozenset(Gp), 0)

    while queue:
        _, _, depth, lam, rem, i0, m = heapq.heappop(queue)
        ind = "  " * depth
        H_i = substitute_edges(Hp[i0], lam)

        cands = isom_minus_1(Gp[i0], H_i, m)
        log(f"{ind}ISOM⁻-1({i0}): r = {len(cands)}"
            + (f": {'; '.join(fmt_sub(c) for c in cands)}" if cands else ""))
        if not cands:
            continue

        cands = consistency(lam, cands)
        log(f"{ind}CONSISTENCY: T = {len(cands)}")
        if not cands:
            continue

        complete, partial = reduction(Gp, Hp, lam, rem, i0, cands)
        if not complete and not partial:
            log(f"{ind}✗ REDUCTION: все ветки противоречат G")
        for lam2, _ in complete:
            unifiers.append(lam2)
            log(f"{ind}✓ REDUCTION: найден унификатор {fmt_sub(lam2)}")
            if not find_all:
                return IsomResult(True, unifiers)
        for lam2, rem2 in partial:
            log(f"{ind}→ REDUCTION: частичный унификатор {fmt_sub(lam2)} в очередь, "
                f"осталось предикатов: {len(rem2)}")
            push(lam2, rem2, depth + 1)

    return IsomResult(bool(unifiers), unifiers,
                      "" if unifiers else "ни одна ветка дерева не дала унификатора")


# ---------------------------------------------------------------------------
#  Обёртки
# ---------------------------------------------------------------------------

def make_template(G2: Hypergraph, prefix: str = "x") -> tuple[Hypergraph, dict]:
    """H из G2: разные константы → разные переменные (b1→x1, b2→x2, ...)."""
    consts = sorted(G2.vertices(), key=natural_key)
    rename = {b: Var(f"{prefix}{k}") for k, b in enumerate(consts, 1)}
    return G2.substitute(rename), rename


def check_isomorphism(G1: Hypergraph, G2: Hypergraph, verbose: bool = False,
                      find_all: bool = True):
    """
    Полная проверка: строит H по G2, запускает ISOM-n.
    Возвращает (IsomResult, список изоморфизмов G2 → G1 в виде {b: a}).
    """
    H, rename = make_template(G2)
    res = isom_n(G1, H, find_all=find_all, verbose=verbose)
    isos = [{b: lam[x] for b, x in rename.items()} for lam in res.unifiers]
    return res, isos


# ---------------------------------------------------------------------------
#  Проверка корректности: полный перебор
# ---------------------------------------------------------------------------

def brute_force(G: Hypergraph, H: Hypergraph) -> list[dict]:
    """Все биекции переменных H на константы G с Hλ = G (перебор n!)."""
    xs = sorted(H.vertices(), key=natural_key)
    cs = sorted(G.vertices(), key=natural_key)
    if len(xs) != len(cs):
        return []
    out = []
    for perm in itertools.permutations(cs):
        s = dict(zip(xs, perm))
        if H.substitute(s) == G:
            out.append(s)
    return out


def random_hypergraph(n: int, spec: list[tuple[Pred, int]], rng: random.Random,
                      prefix: str = "a") -> Hypergraph:
    vs = [f"{prefix}{i}" for i in range(1, n + 1)]
    edges = []
    for p, cnt in spec:
        pool: set = set()
        for _ in range(cnt * 20):
            if len(pool) >= cnt:
                break
            pool.add(edge(p, *rng.sample(vs, p.arity)))
        edges.extend(pool)
    return Hypergraph(edges)


def relabel(G: Hypergraph, rng: random.Random, prefix: str = "b") -> Hypergraph:
    vs = sorted(G.vertices(), key=natural_key)
    targets = [f"{prefix}{i}" for i in range(1, len(vs) + 1)]
    rng.shuffle(targets)
    return G.substitute(dict(zip(vs, targets)))


def self_test(trials: int = 400, seed: int = 1) -> None:
    rng = random.Random(seed)
    pool = [Pred("p", 1), Pred("q", 2), Pred("r", 3), Pred("s", 2, True),
            Pred("t", 3, True), Pred("u", 3)]
    agree = iso_cnt = 0
    for _ in range(trials):
        n = rng.randint(3, 7)
        preds = rng.sample(pool, rng.randint(1, 3))
        spec = [(p, rng.randint(1, 5)) for p in preds]
        G1 = random_hypergraph(n, spec, rng)
        G2 = relabel(G1, rng) if rng.random() < 0.5 else relabel(random_hypergraph(n, spec, rng), rng)
        H, _ = make_template(G2)
        res = isom_n(G1, H)
        got = {frozenset(s.items()) for s in res.unifiers}
        exp = {frozenset(s.items()) for s in brute_force(G1, H)}
        assert got == exp, f"расхождение:\nG1={G1}\nG2={G2}\nISOM-n={got}\nперебор={exp}"
        assert len(got) == len(res.unifiers), "ISOM-n выдал один унификатор дважды"
        first = isom_n(G1, H, find_all=False)
        assert bool(first) == bool(exp) and all(frozenset(s.items()) in exp
                                                for s in first.unifiers), "find_all=False"
        if len(preds) == 1:
            got1 = {frozenset(s.items()) for s in isom_1(G1, H)}
            assert got1 == exp, "ISOM-1 расходится с перебором"
        agree += 1
        iso_cnt += bool(exp)
    print(f"self-test: {agree}/{trials} случаев совпали с полным перебором "
          f"(изоморфных пар: {iso_cnt})")


# ---------------------------------------------------------------------------
#  Примеры из статьи
# ---------------------------------------------------------------------------

def demo() -> None:
    line = "=" * 72

    # --- пример для рёбер типа (1), раздел 3 ---
    p3 = Pred("p", 3)
    G1 = Hypergraph([edge(p3, "a4", "a2", "a5"), edge(p3, "a5", "a6", "a1"),
                     edge(p3, "a1", "a2", "a3"), edge(p3, "a5", "a4", "a3"),
                     edge(p3, "a1", "a6", "a4")])
    G2 = Hypergraph([edge(p3, "b5", "b4", "b6"), edge(p3, "b6", "b1", "b2"),
                     edge(p3, "b2", "b4", "b3"), edge(p3, "b6", "b5", "b3"),
                     edge(p3, "b2", "b1", "b5")])
    H, _ = make_template(G2)
    print(line, "\nПример 1 (тип (1), ISOM-1)")
    print("χ(G1) =", graph_characteristic(G1.edges))
    print("χ(H)  =", graph_characteristic(H.edges))
    print("mapping:", build_mapping(p3, G1.edges, H.edges))
    for lam in isom_1(G1, H):
        print("унификатор:", fmt_sub(lam))

    # --- пример для рёбер типа (2), раздел 3 ---
    pc3 = Pred("p", 3, commutative=True)
    G1 = Hypergraph([edge(pc3, "a2", "a4", "a5"), edge(pc3, "a1", "a5", "a6"),
                     edge(pc3, "a1", "a2", "a3"), edge(pc3, "a3", "a4", "a5"),
                     edge(pc3, "a1", "a4", "a6")])
    G2 = Hypergraph([edge(pc3, "b4", "b5", "b6"), edge(pc3, "b1", "b2", "b6"),
                     edge(pc3, "b2", "b3", "b4"), edge(pc3, "b3", "b5", "b6"),
                     edge(pc3, "b1", "b2", "b5")])
    H, _ = make_template(G2)
    print(line, "\nПример 2 (тип (2), ISOM-1)")
    print("χ(G1) =", graph_characteristic(G1.edges))
    print("χ(H)  =", graph_characteristic(H.edges))
    print("mapping:", build_mapping(pc3, G1.edges, H.edges))
    res = isom_1(G1, H)
    print("унификаторы:" if res else "унификаторов нет — не изоморфны")
    for lam in res:
        print("  ", fmt_sub(lam))

    # --- модельный пример ISOM-n, раздел 5 ---
    p1, p2, p3c = Pred("p1", 1), Pred("p2", 2), Pred("p3", 3, commutative=True)
    G1 = Hypergraph([edge(p1, "a1"), edge(p1, "a2"), edge(p1, "a3"),
                     edge(p2, "a1", "a2"), edge(p2, "a1", "a4"),
                     edge(p3c, "a2", "a3", "a4")])
    G2 = Hypergraph([edge(p1, "b2"), edge(p1, "b3"), edge(p1, "b4"),
                     edge(p2, "b4", "b1"), edge(p2, "b4", "b3"),
                     edge(p3c, "b1", "b3", "b4")])
    print(line, "\nПример 3 (раздел 5, ISOM-n)")
    res, _ = check_isomorphism(G1, G2, verbose=True)
    print("итог:", "изоморфны" if res else f"не изоморфны ({res.reason})")

    # --- вариант: G2 — переименование G1 ---
    G2_renamed = Hypergraph([edge(p1, "b4"), edge(p1, "b3"), edge(p1, "b2"),
                             edge(p2, "b4", "b3"), edge(p2, "b4", "b1"),
                             edge(p3c, "b1", "b2", "b3")])
    print(line, "\nПример 3' (ISOM-n) — G2 переименование G1")
    res, isos = check_isomorphism(G1, G2_renamed, verbose=True)
    print("итог:", "изоморфны" if res else "не изоморфны")
    for iso in isos:
        print("изоморфизм G2 → G1:", fmt_sub(iso))

    # --- «пять братьев»: одно коммутативное ребро против 20 формул ---
    brothers = Pred("brothers", 5, commutative=True)
    G1 = Hypergraph([edge(brothers, "Иван", "Пётр", "Олег", "Сергей", "Павел")])
    G2 = Hypergraph([edge(brothers, "b1", "b2", "b3", "b4", "b5")])
    res, _ = check_isomorphism(G1, G2)
    print(line, "\nПример «пять братьев»: изоморфны —", bool(res),
          f"| унификаторов: {len(res.unifiers)} (= 5!, все перестановки)")
    print(line)


if __name__ == "__main__":
    demo()
    self_test()
