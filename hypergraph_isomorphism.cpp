// Проверка изоморфизма гиперграфов отношений по статье
// Т. М. Косовской «On the isomorphism of hypergraphs of relations» —
// C++-версия hypergraph_isomorphism.py.
//
// Реализовано то же, что и в Python:
//   * характеристики вершин и гиперграфа (определения 2–5);
//   * структурное отображение (structure mapping);
//   * ISOM-1   — гиперграфы с одной предикатной вершиной;
//   * ISOM⁻-1  — ISOM-1 без шагов 1–3 (подпрограмма ISOM-n);
//   * ISOM-n   — MAP → BESTMAP → ISOM⁻-1 → CONSISTENCY → REDUCTION
//                с очередью частичных унификаторов по стоимости Π t_k!;
//   * полный перебор n! для проверки.
//
// Порт сохраняет логику и порядок обхода Python-версии: те же классы
// отображения, тот же порядок перестановок в ISOM⁻-1, та же очередь
// (стоимость, затем порядок добавления), тот же текст подробного лога (-v).
// Поэтому на одинаковых входах обе реализации строят одно и то же дерево
// поиска и находят одни и те же унификаторы — это проверяет compare.py.
//
// Отличается только представление данных: вершины и переменные — целые
// числа (в естественном порядке имён: a2 < a10), подстановка λ — массив
// «переменная → константа» (−1 — не задана), рёбра G^i — хеш-множество.
// Гиперграф считается множеством рёбер (как в статье): повторяющиеся рёбра
// во входе — ошибка.
//
// Сборка:  g++ -O2 -std=c++17 -o hypergraph_isomorphism hypergraph_isomorphism.cpp
// Запуск:  ./hypergraph_isomorphism [опции] cases.txt   (формат — в usage())

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

// ---------------------------------------------------------------------------
//  Естественный порядок имён
// ---------------------------------------------------------------------------

// Как re.split(r"(\d+)", s) в Python: нецифровые и цифровые куски по очереди,
// первый и последний куски нецифровые (возможно, пустые).
std::vector<std::string> natural_split(const std::string& s) {
    std::vector<std::string> parts(1);
    for (char ch : s) {
        const bool digit = ch >= '0' && ch <= '9';
        const bool in_digits = parts.size() % 2 == 0;
        if (digit != in_digits) parts.emplace_back();
        parts.back() += ch;
    }
    if (parts.size() % 2 == 0) parts.emplace_back();
    return parts;
}

int compare_numbers(const std::string& a, const std::string& b) {
    const size_t i = std::min(a.find_first_not_of('0'), a.size());
    const size_t j = std::min(b.find_first_not_of('0'), b.size());
    if (a.size() - i != b.size() - j) return a.size() - i < b.size() - j ? -1 : 1;
    return a.compare(i, std::string::npos, b, j, std::string::npos);
}

// Ключ «естественной» сортировки: a2 < a10 (natural_key в Python).
bool natural_less(const std::string& a, const std::string& b) {
    const auto pa = natural_split(a), pb = natural_split(b);
    for (size_t i = 0; i < std::min(pa.size(), pb.size()); ++i) {
        const int c = i % 2 ? compare_numbers(pa[i], pb[i]) : pa[i].compare(pb[i]);
        if (c != 0) return c < 0;
    }
    return pa.size() < pb.size();
}

// ---------------------------------------------------------------------------
//  Входные данные
// ---------------------------------------------------------------------------

// Предикатная вершина: p^k (тип (1)) или p^{c,k} (тип (2), коммутативная).
struct Pred {
    std::string name;
    int arity = 0;
    bool comm = false;

    std::string repr() const {
        return name + "^" + (comm ? "c," : "") + std::to_string(arity);
    }
};

struct RawEdge {
    int pred;                        // индекс в Case::preds
    std::vector<std::string> args;
};

struct Case {
    std::string name;
    std::vector<Pred> preds;
    std::vector<RawEdge> g1, g2;
};

std::vector<Case> read_cases(std::istream& in) {
    std::vector<Case> cases;
    Case* cur = nullptr;
    std::string line;
    int lineno = 0;
    auto fail = [&](const std::string& msg) {
        throw std::runtime_error("строка " + std::to_string(lineno) + ": " + msg);
    };
    while (std::getline(in, line)) {
        ++lineno;
        if (const auto h = line.find('#'); h != std::string::npos) line.erase(h);
        std::istringstream ss(line);
        std::vector<std::string> tok;
        for (std::string t; ss >> t;) tok.push_back(t);
        if (tok.empty()) continue;
        const std::string& kw = tok[0];
        if (kw == "case") {
            if (cur) fail("предыдущая задача не закрыта словом end");
            if (tok.size() != 2) fail("ожидалось: case <имя>");
            cases.emplace_back();
            cur = &cases.back();
            cur->name = tok[1];
        } else if (!cur) {
            fail("ожидалось слово case");
        } else if (kw == "pred") {
            if (tok.size() != 4 || (tok[3] != "n" && tok[3] != "c"))
                fail("ожидалось: pred <имя> <арность> <n|c>");
            Pred p{tok[1], std::stoi(tok[2]), tok[3] == "c"};
            if (p.arity < 1) fail("арность предиката должна быть не меньше 1");
            for (const Pred& q : cur->preds)
                if (q.name == p.name) fail("предикат " + p.name + " объявлен дважды");
            cur->preds.push_back(p);
        } else if (kw == "g1" || kw == "g2") {
            if (tok.size() < 2) fail("ожидалось: " + kw + " <предикат> <вершины>");
            int pi = -1;
            for (size_t i = 0; i < cur->preds.size(); ++i)
                if (cur->preds[i].name == tok[1]) pi = static_cast<int>(i);
            if (pi < 0) fail("неизвестный предикат " + tok[1]);
            RawEdge e{pi, {tok.begin() + 2, tok.end()}};
            if (static_cast<int>(e.args.size()) != cur->preds[pi].arity)
                fail(cur->preds[pi].repr() + ": неверное число аргументов");
            std::vector<std::string> s = e.args;
            std::sort(s.begin(), s.end());
            if (std::adjacent_find(s.begin(), s.end()) != s.end())
                fail(cur->preds[pi].repr() + ": аргументы гиперребра должны быть различны");
            (kw == "g1" ? cur->g1 : cur->g2).push_back(std::move(e));
        } else if (kw == "end") {
            cur = nullptr;
        } else {
            fail("неизвестное слово " + kw);
        }
    }
    if (cur) throw std::runtime_error("последняя задача не закрыта словом end");
    return cases;
}

// ---------------------------------------------------------------------------
//  Задача: G (константы, из G1) и шаблон H (переменные, из G2)
// ---------------------------------------------------------------------------

using Rows = std::vector<std::vector<int>>;  // рёбра одного предиката: [ребро][место]

struct Problem {
    std::vector<Pred> preds;        // предикаты с рёбрами, по возрастанию repr()
    std::vector<std::string> cname; // константы G (вершины G1) в естественном порядке
    std::vector<std::string> vname; // переменные H: x1, ..., xn
    std::vector<std::string> bname; // bname[x] — вершина G2, заменённая на x
    std::vector<Rows> G, H;         // [предикат]; у коммутативных строки отсортированы
};

// Номера вершин в естественном порядке имён.
std::map<std::string, int> number_vertices(const std::vector<RawEdge>& edges,
                                           std::vector<std::string>& names) {
    std::set<std::string> all;
    for (const RawEdge& e : edges) all.insert(e.args.begin(), e.args.end());
    names.assign(all.begin(), all.end());
    std::stable_sort(names.begin(), names.end(), natural_less);
    std::map<std::string, int> id;
    for (size_t i = 0; i < names.size(); ++i) id[names[i]] = static_cast<int>(i);
    return id;
}

// H из G2 строится как make_template в Python: b-вершины в естественном
// порядке получают имена x1, x2, ...
Problem make_problem(const Case& c) {
    Problem P;
    std::vector<int> used;
    for (size_t i = 0; i < c.preds.size(); ++i) {
        auto has = [&](const std::vector<RawEdge>& es) {
            return std::any_of(es.begin(), es.end(),
                               [&](const RawEdge& e) { return e.pred == static_cast<int>(i); });
        };
        if (has(c.g1) || has(c.g2)) used.push_back(static_cast<int>(i));
    }
    std::sort(used.begin(), used.end(),
              [&](int a, int b) { return c.preds[a].repr() < c.preds[b].repr(); });
    std::vector<int> index(c.preds.size(), -1);
    for (size_t i = 0; i < used.size(); ++i) {
        index[used[i]] = static_cast<int>(i);
        P.preds.push_back(c.preds[used[i]]);
    }

    const auto cid = number_vertices(c.g1, P.cname);
    const auto bid = number_vertices(c.g2, P.bname);
    for (size_t x = 0; x < P.bname.size(); ++x) P.vname.push_back("x" + std::to_string(x + 1));

    P.G.assign(P.preds.size(), {});
    P.H.assign(P.preds.size(), {});
    auto load = [&](const std::vector<RawEdge>& es, const std::map<std::string, int>& id,
                    std::vector<Rows>& out, const char* tag) {
        for (const RawEdge& e : es) {
            std::vector<int> row;
            for (const std::string& a : e.args) row.push_back(id.at(a));
            if (c.preds[e.pred].comm) std::sort(row.begin(), row.end());
            out[index[e.pred]].push_back(std::move(row));
        }
        for (size_t i = 0; i < out.size(); ++i) {
            Rows s = out[i];
            std::sort(s.begin(), s.end());
            if (std::adjacent_find(s.begin(), s.end()) != s.end())
                throw std::runtime_error(std::string("в ") + tag + " повторяется ребро с " +
                                         P.preds[i].repr());
        }
    };
    load(c.g1, cid, P.G, "G1");
    load(c.g2, bid, P.H, "G2");
    return P;
}

// ---------------------------------------------------------------------------
//  Вспомогательные структуры
// ---------------------------------------------------------------------------

// Рёбра G^i: строки длины k в плоском массиве + открытая адресация.
class EdgeSet {
public:
    void build(int k, const Rows& rows) {
        k_ = k;
        data_.clear();
        for (const auto& r : rows) data_.insert(data_.end(), r.begin(), r.end());
        size_t cap = 4;
        while (cap < 2 * rows.size() + 2) cap <<= 1;
        mask_ = cap - 1;
        slot_.assign(cap, -1);
        for (size_t t = 0; t < rows.size(); ++t) {
            size_t h = hash(&data_[t * k_]) & mask_;
            while (slot_[h] >= 0) h = (h + 1) & mask_;
            slot_[h] = static_cast<int>(t);
        }
    }

    bool contains(const int* row) const {
        for (size_t h = hash(row) & mask_; slot_[h] >= 0; h = (h + 1) & mask_)
            if (std::equal(row, row + k_, &data_[size_t(slot_[h]) * k_])) return true;
        return false;
    }

private:
    uint64_t hash(const int* r) const {
        uint64_t h = 0x9E3779B97F4A7C15ull;
        for (int j = 0; j < k_; ++j) {
            h ^= static_cast<uint32_t>(r[j]);
            h *= 0xBF58476D1CE4E5B9ull;
            h ^= h >> 31;
        }
        return h;
    }

    int k_ = 0;
    size_t mask_ = 0;
    std::vector<int> data_, slot_;
};

// Стоимость Π t_k! считается точно, пока помещается в 128 бит, дальше насыщается.
using Cost = unsigned __int128;
constexpr Cost COST_MAX = ~Cost(0);

Cost sat_mul(Cost a, Cost b) {
    if (a != 0 && b > COST_MAX / a) return COST_MAX;
    return a * b;
}

std::string cost_str(Cost c) {
    if (c == COST_MAX) return ">=2^128";
    std::string s;
    do {
        s += static_cast<char>('0' + static_cast<int>(c % 10));
        c /= 10;
    } while (c != 0);
    return {s.rbegin(), s.rend()};
}

// Характеристики χ(v) вершин подграфа с одной предикатной вершиной:
// строка длины w (тип (1): w = k, места 1..k; тип (2): w = 1, число вхождений).
std::vector<int> characteristic_table(const Pred& p, const Rows& rows, int nids,
                                      std::vector<char>& present) {
    const int w = p.comm ? 1 : p.arity;
    std::vector<int> ch(size_t(nids) * w, 0);
    present.assign(nids, 0);
    for (const auto& e : rows)
        for (int j = 0; j < p.arity; ++j) {
            ++ch[size_t(e[j]) * w + (p.comm ? 0 : j)];
            present[e[j]] = 1;
        }
    return ch;
}

// Строки длины w, отсортированные по возрастанию.
std::vector<int> sorted_rows(const std::vector<int>& flat, int w) {
    std::vector<size_t> idx(flat.size() / w);
    std::iota(idx.begin(), idx.end(), 0);
    std::sort(idx.begin(), idx.end(), [&](size_t a, size_t b) {
        return std::lexicographical_compare(&flat[a * w], &flat[a * w] + w, &flat[b * w],
                                            &flat[b * w] + w);
    });
    std::vector<int> out;
    out.reserve(flat.size());
    for (size_t t : idx) out.insert(out.end(), &flat[t * w], &flat[t * w] + w);
    return out;
}

// χ(G) — набор характеристик вершин в каноническом (отсортированном) порядке.
std::vector<int> graph_characteristic(const Pred& p, const Rows& rows, int nids) {
    std::vector<char> present;
    const auto ch = characteristic_table(p, rows, nids, present);
    const int w = p.comm ? 1 : p.arity;
    std::vector<int> flat;
    for (int v = 0; v < nids; ++v)
        if (present[v]) flat.insert(flat.end(), &ch[size_t(v) * w], &ch[size_t(v) * w] + w);
    return sorted_rows(flat, w);
}

// Структурное отображение {[x_i1, ..., x_it1] : [a_j1, ..., a_jt1], ...}:
// классы подряд в xs/cs, класс q занимает [start[q], start[q + 1]).
struct Mapping {
    std::vector<int> xs, cs, start;
    Cost cost = 1;
};

struct Stats {
    long long map_calls = 0, map_fail = 0, nodes = 0, cands = 0, consistent = 0,
              complete = 0, partial = 0;
};

struct Result {
    bool iso = false;
    std::vector<std::vector<int>> unifiers;  // λ: переменная → константа
    std::string reason;
    Stats stats;
};

struct Node {
    Cost cost;
    uint64_t seq;
    int depth;
    std::vector<int> lam;  // частичный унификатор
    std::vector<int> rem;  // оставшиеся предикаты (индексы по возрастанию)
    int pred;              // i0, выбранный BESTMAP
    Mapping m;
};

// ---------------------------------------------------------------------------
//  Алгоритмы
// ---------------------------------------------------------------------------

class Solver {
public:
    explicit Solver(const Problem& problem);

    Result isom_n(bool find_all, std::ostream* log);
    Result isom_1();
    Result brute_force();

private:
    bool build_mapping(int i, const std::vector<int>& lam, Mapping& m);
    void isom_minus_1(int i, std::vector<int>& cur, const Mapping& m, std::vector<int>& out);
    void isom_minus_1_rec(int i, std::vector<int>& cur, const Mapping& m, size_t q,
                          const std::vector<std::vector<int>>& checks, std::vector<int>& out);
    bool edge_fits(int i, const std::vector<int>& e, const std::vector<int>& lam);
    bool edges_fit(int i, const std::vector<int>& lam, const std::vector<int>& edges);
    bool all_ground(int i, const std::vector<int>& lam) const;
    bool matches(int i, const std::vector<int>& lam);
    void consistency(const std::vector<int>& lam, const Mapping& m, std::vector<int>& cands);
    void reduction(const std::vector<int>& lam, const std::vector<int>& rem, int i0,
                   const Mapping& m, const std::vector<int>& cands,
                   std::vector<std::vector<int>>& complete,
                   std::vector<std::pair<std::vector<int>, std::vector<int>>>& partial);

    std::string fmt_sub(const std::vector<int>& lam) const;
    std::string fmt_cand(const Mapping& m, const int* vals) const;
    std::string mapping_repr(const Mapping& m) const;

    const Problem& P;
    const int nv, nc, np;
    std::vector<int> w;                    // длина характеристики у предиката
    std::vector<EdgeSet> gset;             // рёбра G^i
    std::vector<std::vector<int>> chG;     // [i][a * w + j] — χ констант в G^i
    std::vector<std::vector<char>> inG;    // [i][a] — константа a входит в G^i
    std::vector<std::vector<int>> gconsts; // [i] — константы G^i по возрастанию
    std::vector<std::vector<int>> chGsorted;
    std::vector<std::vector<int>> hvars;   // [i] — переменные H^i

    // рабочие массивы
    std::vector<int> chV, chC, touchedV, touchedC, row, level;
    std::vector<char> markV, markC;
};

Solver::Solver(const Problem& problem)
    : P(problem),
      nv(static_cast<int>(problem.vname.size())),
      nc(static_cast<int>(problem.cname.size())),
      np(static_cast<int>(problem.preds.size())) {
    int maxw = 1, maxk = 1;
    for (int i = 0; i < np; ++i) {
        const Pred& p = P.preds[i];
        w.push_back(p.comm ? 1 : p.arity);
        maxw = std::max(maxw, w.back());
        maxk = std::max(maxk, p.arity);
        gset.emplace_back();
        gset.back().build(p.arity, P.G[i]);
        std::vector<char> present;
        chG.push_back(characteristic_table(p, P.G[i], nc, present));
        std::vector<int> gc;
        for (int a = 0; a < nc; ++a)
            if (present[a]) gc.push_back(a);
        gconsts.push_back(std::move(gc));
        inG.push_back(std::move(present));
        chGsorted.push_back(graph_characteristic(p, P.G[i], nc));
        std::vector<int> xs;
        for (const auto& e : P.H[i]) xs.insert(xs.end(), e.begin(), e.end());
        std::sort(xs.begin(), xs.end());
        xs.erase(std::unique(xs.begin(), xs.end()), xs.end());
        hvars.push_back(std::move(xs));
    }
    chV.assign(size_t(nv) * maxw, 0);
    chC.assign(size_t(nc) * maxw, 0);
    markV.assign(nv, 0);
    markC.assign(nc, 0);
    row.assign(maxk, 0);
    level.assign(nv, 0);
}

// Структурное отображение между G^i и H^iλ. false — необходимое условие
// изоморфизма нарушено и ветку можно отсечь.
bool Solver::build_mapping(int i, const std::vector<int>& lam, Mapping& m) {
    const Pred& p = P.preds[i];
    const int W = w[i];
    if (P.H[i].size() != P.G[i].size()) return false;

    // характеристики вершин H^iλ: свободных переменных и уже подставленных констант
    touchedV.clear();
    touchedC.clear();
    for (const auto& e : P.H[i])
        for (int j = 0; j < p.arity; ++j) {
            const int x = e[j], a = lam[x], col = p.comm ? 0 : j;
            if (a < 0) {
                if (!markV[x]) {
                    markV[x] = 1;
                    touchedV.push_back(x);
                }
                ++chV[size_t(x) * W + col];
            } else {
                if (!markC[a]) {
                    markC[a] = 1;
                    touchedC.push_back(a);
                }
                ++chC[size_t(a) * W + col];
            }
        }
    std::vector<int> varCh, fixCh;
    for (int x : touchedV) {
        const auto b = chV.begin() + size_t(x) * W;
        varCh.insert(varCh.end(), b, b + W);
        std::fill(b, b + W, 0);
        markV[x] = 0;
    }
    for (int a : touchedC) {
        const auto b = chC.begin() + size_t(a) * W;
        fixCh.insert(fixCh.end(), b, b + W);
        std::fill(b, b + W, 0);
        markC[a] = 0;
    }

    // χ(G^i) и χ(H^iλ) должны совпадать как мультимножества
    std::vector<int> all = varCh;
    all.insert(all.end(), fixCh.begin(), fixCh.end());
    if (sorted_rows(all, W) != chGsorted[i]) return false;

    // константы, уже стоящие в H^iλ, должны играть в G^i ту же роль
    for (size_t t = 0; t < touchedC.size(); ++t) {
        const int a = touchedC[t];
        if (!inG[i][a] || !std::equal(fixCh.begin() + t * W, fixCh.begin() + (t + 1) * W,
                                      chG[i].begin() + size_t(a) * W))
            return false;
    }
    for (int a : touchedC) markC[a] = 1;
    std::vector<int> freeC;
    for (int a : gconsts[i])
        if (!markC[a]) freeC.push_back(a);
    for (int a : touchedC) markC[a] = 0;

    // классы: переменные и свободные константы, упорядоченные по (χ, номер)
    const int* vch = varCh.data();
    const int* gch = chG[i].data();
    auto less_by = [W](const int* base, const std::vector<int>* id) {
        return [W, base, id](size_t s, size_t t) {
            const int *a = base + s * W, *b = base + t * W;
            if (std::equal(a, a + W, b)) return (*id)[s] < (*id)[t];
            return std::lexicographical_compare(a, a + W, b, b + W);
        };
    };
    std::vector<size_t> vi(touchedV.size());
    std::iota(vi.begin(), vi.end(), 0);
    std::sort(vi.begin(), vi.end(), less_by(vch, &touchedV));
    std::vector<int> cRows;  // χ свободных констант в том же порядке, что и freeC
    for (int a : freeC) cRows.insert(cRows.end(), gch + size_t(a) * W, gch + size_t(a + 1) * W);
    std::vector<size_t> ci(freeC.size());
    std::iota(ci.begin(), ci.end(), 0);
    std::sort(ci.begin(), ci.end(), less_by(cRows.data(), &freeC));
    if (vi.size() != ci.size()) return false;

    auto same = [W](const int* a, const int* b) { return std::equal(a, a + W, b); };
    m = Mapping{};
    for (size_t s = 0; s < vi.size();) {
        const int* ch = vch + vi[s] * W;
        size_t e = s;
        while (e < vi.size() && same(vch + vi[e] * W, ch)) ++e;
        for (size_t t = s; t < e; ++t)
            if (!same(cRows.data() + ci[t] * W, ch)) return false;
        if (e < ci.size() && same(cRows.data() + ci[e] * W, ch)) return false;
        m.start.push_back(static_cast<int>(s));
        for (size_t t = s; t < e; ++t) {
            m.xs.push_back(touchedV[vi[t]]);
            m.cs.push_back(freeC[ci[t]]);
            m.cost = sat_mul(m.cost, t - s + 1);  // (e − s)!
        }
        s = e;
    }
    m.start.push_back(static_cast<int>(vi.size()));
    return true;
}

// Ребро e подграфа H^i без переменных при подстановке λ встречается в G^i.
bool Solver::edge_fits(int i, const std::vector<int>& e, const std::vector<int>& lam) {
    const Pred& p = P.preds[i];
    for (int j = 0; j < p.arity; ++j) row[j] = lam[e[j]];
    if (p.comm) std::sort(row.begin(), row.begin() + p.arity);
    return gset[i].contains(row.data());
}

bool Solver::edges_fit(int i, const std::vector<int>& lam, const std::vector<int>& edges) {
    for (int t : edges)
        if (!edge_fits(i, P.H[i][t], lam)) return false;
    return true;
}

bool Solver::all_ground(int i, const std::vector<int>& lam) const {
    for (int x : hvars[i])
        if (lam[x] < 0) return false;
    return true;
}

// H^iλ = G^i. Рёбра различны, а λ инъективна, поэтому при равном числе рёбер
// достаточно, чтобы каждое ребро H^iλ было ребром G^i.
bool Solver::matches(int i, const std::vector<int>& lam) {
    if (P.H[i].size() != P.G[i].size() || !all_ground(i, lam)) return false;
    for (const auto& e : P.H[i])
        if (!edge_fits(i, e, lam)) return false;
    return true;
}

// ISOM⁻-1: ISOM-1, начиная с шага 4 (отображение уже построено). Перебирает
// перестановки внутри классов и отсекает ветку, как только часть рёбер без
// переменных не встречается в G^i (аналог шагов 8–11). Каждое ребро
// проверяется один раз — после назначения класса, на котором в нём не
// остаётся переменных (checks[q + 1]; checks[0] — рёбра без переменных с самого
// начала). Значения переменных m.xs каждого найденного локального унификатора
// дописываются в out.
void Solver::isom_minus_1(int i, std::vector<int>& cur, const Mapping& m,
                          std::vector<int>& out) {
    const size_t nq = m.start.size() - 1;
    for (size_t q = 0; q < nq; ++q)
        for (int t = m.start[q]; t < m.start[q + 1]; ++t) level[m.xs[t]] = static_cast<int>(q + 1);
    std::vector<std::vector<int>> checks(nq + 1);
    for (size_t t = 0; t < P.H[i].size(); ++t) {
        int k = 0;
        for (int x : P.H[i][t])
            if (cur[x] < 0) k = std::max(k, level[x]);
        checks[k].push_back(static_cast<int>(t));
    }
    if (edges_fit(i, cur, checks[0])) isom_minus_1_rec(i, cur, m, 0, checks, out);
}

void Solver::isom_minus_1_rec(int i, std::vector<int>& cur, const Mapping& m, size_t q,
                              const std::vector<std::vector<int>>& checks,
                              std::vector<int>& out) {
    if (q + 1 == m.start.size()) {
        if (matches(i, cur))  // шаг 7: H^iλ = G^i
            for (int x : m.xs) out.push_back(cur[x]);
        return;
    }
    const int b = m.start[q], e = m.start[q + 1];
    std::vector<int> perm(m.cs.begin() + b, m.cs.begin() + e);  // по возрастанию
    do {
        for (int t = b; t < e; ++t) cur[m.xs[t]] = perm[t - b];
        if (edges_fit(i, cur, checks[q + 1])) isom_minus_1_rec(i, cur, m, q + 1, checks, out);
    } while (std::next_permutation(perm.begin(), perm.end()));
    for (int t = b; t < e; ++t) cur[m.xs[t]] = -1;
}

// CONSISTENCY: оставляет только тех кандидатов λ^{i0}_j, что вместе с λ
// образуют биекцию — нет пар (x/a, x/b) и (x/a, y/a) при x ≠ y, a ≠ b.
void Solver::consistency(const std::vector<int>& lam, const Mapping& m,
                         std::vector<int>& cands) {
    std::vector<int> inv(nc, -1);
    for (int x = 0; x < nv; ++x)
        if (lam[x] >= 0) inv[lam[x]] = x;
    const size_t k = m.xs.size();
    size_t kept = 0;
    for (size_t t = 0; t < cands.size(); t += k) {
        bool ok = true;
        for (size_t s = 0; s < k && ok; ++s) {
            const int x = m.xs[s], a = cands[t + s];
            ok = (lam[x] < 0 || lam[x] == a) && (inv[a] < 0 || inv[a] == x);
        }
        if (ok) {
            std::copy(cands.begin() + t, cands.begin() + t + k, cands.begin() + kept);
            kept += k;
        }
    }
    cands.resize(kept);
}

// REDUCTION (рис. 1): для каждого λ_t строит Hλλ_t; подграфы без переменных
// сравнивает с G^j (совпал — удаляется, нет — ветка отбрасывается).
// Не осталось подграфов — полный унификатор, иначе — частичный, в очередь.
void Solver::reduction(const std::vector<int>& lam, const std::vector<int>& rem, int i0,
                       const Mapping& m, const std::vector<int>& cands,
                       std::vector<std::vector<int>>& complete,
                       std::vector<std::pair<std::vector<int>, std::vector<int>>>& partial) {
    const size_t k = m.xs.size();
    for (size_t t = 0; t < cands.size(); t += k) {
        std::vector<int> lam2 = lam;
        for (size_t s = 0; s < k; ++s) lam2[m.xs[s]] = cands[t + s];
        std::vector<int> rem2;
        bool ok = true;
        for (int j : rem) {
            if (j == i0) continue;  // G := G \ G^{i0} (шаг 5)
            if (!all_ground(j, lam2)) {
                rem2.push_back(j);
            } else if (!matches(j, lam2)) {
                ok = false;
                break;
            }
        }
        if (!ok) continue;
        if (rem2.empty())
            complete.push_back(std::move(lam2));
        else
            partial.emplace_back(std::move(lam2), std::move(rem2));
    }
}

// ISOM-n: все унификаторы λ (Hλ = G) или первый найденный, если find_all = false.
// Склейка вершин дерева (замечание в разделе 5) не возникает: BESTMAP выбирает
// i0 однозначно по λ, дети одной вершины различаются значениями переменных
// H^{i0}λ, а у потомков λ только растёт — все вершины и унификаторы различны.
Result Solver::isom_n(bool find_all, std::ostream* log) {
    Result res;
    auto out = [&](const std::string& s) { *log << "| " << s << '\n'; };

    // предварительная проверка: те же предикаты и равные характеристики подграфов
    for (int i = 0; i < np; ++i)
        if (P.G[i].empty() != P.H[i].empty()) {
            res.reason = "разные наборы предикатных вершин";
            return res;
        }
    for (int i = 0; i < np; ++i)
        if (chGsorted[i] != graph_characteristic(P.preds[i], P.H[i], nv)) {
            res.reason = "характеристики подграфов с " + P.preds[i].repr() + " различны";
            return res;
        }
    if (np == 0) {
        res.iso = true;
        res.unifiers.emplace_back();
        return res;
    }

    std::vector<Node> heap;
    auto later = [](const Node& a, const Node& b) {
        return a.cost != b.cost ? a.cost > b.cost : a.seq > b.seq;
    };
    uint64_t seq = 0;

    auto push = [&](std::vector<int> lam, std::vector<int> rem, int depth) {
        const std::string ind(2 * depth, ' ');
        // MAP: отображения для предикатов, у которых в H^iλ остались переменные
        ++res.stats.map_calls;
        Mapping best, m;
        int i0 = -1;
        for (int p : rem) {
            if (all_ground(p, lam)) continue;  // такие подграфы проверяет REDUCTION
            if (!build_mapping(p, lam, m)) {
                ++res.stats.map_fail;
                if (log)
                    out(ind + "✗ MAP: при λ=" + fmt_sub(lam) +
                        " характеристики не согласуются — ветка отсечена");
                return;
            }
            // BESTMAP: минимальная Π t_k!, при равенстве — меньший repr() предиката
            if (i0 < 0 || m.cost < best.cost) {
                i0 = p;
                std::swap(best, m);
            }
        }
        if (i0 < 0) return;  // недостижимо: в очередь попадают только λ с переменными
        if (log)
            out(ind + "MAP/BESTMAP: λ=" + fmt_sub(lam) + " → предикат " + P.preds[i0].repr() +
                ", mapping=" + mapping_repr(best) + ", Π t_k! = " + cost_str(best.cost));
        heap.push_back(Node{best.cost, seq++, depth, std::move(lam), std::move(rem), i0,
                            std::move(best)});
        std::push_heap(heap.begin(), heap.end(), later);
    };

    std::vector<int> all(np);
    std::iota(all.begin(), all.end(), 0);
    push(std::vector<int>(nv, -1), all, 0);

    std::vector<int> cands;
    while (!heap.empty()) {
        std::pop_heap(heap.begin(), heap.end(), later);
        const Node node = std::move(heap.back());
        heap.pop_back();
        const std::string ind(2 * node.depth, ' ');
        const Mapping& m = node.m;
        const int i0 = node.pred;
        const size_t k = m.xs.size();
        const std::string pname = P.preds[i0].repr();

        ++res.stats.nodes;
        cands.clear();
        std::vector<int> cur = node.lam;
        isom_minus_1(i0, cur, m, cands);
        const size_t r = cands.size() / k;
        res.stats.cands += r;
        if (log) {
            std::string s = ind + "ISOM⁻-1(" + pname + "): r = " + std::to_string(r);
            for (size_t t = 0; t < r; ++t) s += (t ? "; " : ": ") + fmt_cand(m, &cands[t * k]);
            out(s);
        }
        if (r == 0) continue;

        consistency(node.lam, m, cands);
        const size_t T = cands.size() / k;
        res.stats.consistent += T;
        if (log) out(ind + "CONSISTENCY: T = " + std::to_string(T));
        if (T == 0) continue;

        std::vector<std::vector<int>> complete;
        std::vector<std::pair<std::vector<int>, std::vector<int>>> partial;
        reduction(node.lam, node.rem, i0, m, cands, complete, partial);
        res.stats.complete += complete.size();
        res.stats.partial += partial.size();
        if (complete.empty() && partial.empty() && log)
            out(ind + "✗ REDUCTION: все ветки противоречат G");
        for (auto& lam2 : complete) {
            if (log) out(ind + "✓ REDUCTION: найден унификатор " + fmt_sub(lam2));
            res.unifiers.push_back(std::move(lam2));
            if (!find_all) {
                res.iso = true;
                return res;
            }
        }
        for (auto& [lam2, rem2] : partial) {
            if (log)
                out(ind + "→ REDUCTION: частичный унификатор " + fmt_sub(lam2) +
                    " в очередь, осталось предикатов: " + std::to_string(rem2.size()));
            push(std::move(lam2), std::move(rem2), node.depth + 1);
        }
    }
    res.iso = !res.unifiers.empty();
    if (!res.iso) res.reason = "ни одна ветка дерева не дала унификатора";
    return res;
}

// ISOM-1 для гиперграфов с одной предикатной вершиной.
Result Solver::isom_1() {
    Result res;
    if (np > 1)
        throw std::runtime_error("ISOM-1 работает с одной предикатной вершиной; используйте isom_n");
    if (np == 0) {
        res.iso = true;
        res.unifiers.emplace_back();
        return res;
    }
    // шаги 1–2: характеристики
    if (chGsorted[0] != graph_characteristic(P.preds[0], P.H[0], nv)) return res;
    // шаг 3: структурное отображение
    std::vector<int> lam(nv, -1);
    Mapping m;
    if (!build_mapping(0, lam, m)) return res;
    // шаги 4–12
    std::vector<int> cands;
    isom_minus_1(0, lam, m, cands);
    const size_t k = m.xs.size();
    for (size_t t = 0; t < cands.size(); t += k) {
        std::vector<int> u(nv, -1);
        for (size_t s = 0; s < k; ++s) u[m.xs[s]] = cands[t + s];
        res.unifiers.push_back(std::move(u));
    }
    res.iso = !res.unifiers.empty();
    return res;
}

// Все биекции переменных H на константы G с Hλ = G (перебор n!).
Result Solver::brute_force() {
    Result res;
    if (nv != nc) return res;
    std::vector<int> perm(nc);
    std::iota(perm.begin(), perm.end(), 0);
    do {
        bool ok = true;
        for (int i = 0; i < np && ok; ++i) ok = matches(i, perm);
        if (ok) res.unifiers.push_back(perm);
    } while (std::next_permutation(perm.begin(), perm.end()));
    res.iso = !res.unifiers.empty();
    return res;
}

std::string Solver::fmt_sub(const std::vector<int>& lam) const {
    std::string s;
    for (int x = 0; x < nv; ++x)
        if (lam[x] >= 0) s += (s.empty() ? "" : ", ") + P.vname[x] + "→" + P.cname[lam[x]];
    return s.empty() ? "∅" : s;
}

std::string Solver::fmt_cand(const Mapping& m, const int* vals) const {
    std::vector<std::pair<int, int>> sub;
    for (size_t s = 0; s < m.xs.size(); ++s) sub.emplace_back(m.xs[s], vals[s]);
    std::sort(sub.begin(), sub.end());
    std::string out;
    for (const auto& [x, a] : sub) out += (out.empty() ? "" : ", ") + P.vname[x] + "→" + P.cname[a];
    return out;
}

std::string Solver::mapping_repr(const Mapping& m) const {
    std::string s = "{";
    for (size_t q = 0; q + 1 < m.start.size(); ++q) {
        std::string xs, cs;
        for (int t = m.start[q]; t < m.start[q + 1]; ++t) {
            xs += (t > m.start[q] ? ", " : "") + P.vname[m.xs[t]];
            cs += (t > m.start[q] ? ", " : "") + P.cname[m.cs[t]];
        }
        s += (q ? ", [" : "[") + xs + "] : [" + cs + "]";
    }
    return s + "}";
}

// ---------------------------------------------------------------------------
//  Командная строка
// ---------------------------------------------------------------------------

// Серия замеров по шпаргалке https://github.com/spbu-se/measurements: после
// прогревочного запуска (его длительность — first) выполняется repeat замеров;
// короткие задачи замеряются пачками не короче min_sample, как в timeit.
struct Timing {
    std::vector<double> samples;  // время одного запуска в каждом замере, с
    long number = 1;              // запусков в одном замере
};

template <class F>
Timing measure(F run_once, double first, long repeat, double min_sample) {
    using clock = std::chrono::steady_clock;
    auto batch = [&](long k) {
        const auto t0 = clock::now();
        for (long j = 0; j < k; ++j) run_once();
        return std::chrono::duration<double>(clock::now() - t0).count();
    };
    Timing tm;
    for (double t = first; repeat > 0 && t < min_sample;) {
        tm.number *= 2;
        t = batch(tm.number);
    }
    for (long i = 0; i < repeat; ++i) tm.samples.push_back(batch(tm.number) / tm.number);
    return tm;
}

void print_timing(const Timing& tm) {
    if (tm.samples.empty()) return;
    const auto& xs = tm.samples;
    double mean = 0, sd = 0;
    for (double x : xs) mean += x / xs.size();
    for (double x : xs) sd += (x - mean) * (x - mean);
    sd = xs.size() > 1 ? std::sqrt(sd / (xs.size() - 1)) : 0;
    std::cout << "time_mean_ms " << mean * 1e3 << "\ntime_std_ms " << sd * 1e3
              << "\nsamples " << xs.size() << "\nnumber " << tm.number << "\nsamples_ms";
    for (double x : xs) std::cout << ' ' << x * 1e3;
    std::cout << '\n';
}

void usage() {
    std::cerr <<
R"(Использование: hypergraph_isomorphism [опции] файл|-

Опции:
  --algo A        isom_n (по умолчанию), isom_1 или brute (полный перебор)
  --first         ISOM-n: остановиться на первом унификаторе
  --repeat N      число замеров времени после прогревочного запуска
                  (по умолчанию 1, 0 — не замерять)
  --min-sample S  минимальная длительность одного замера, с (по умолчанию 0):
                  короткие задачи замеряются пачками запусков, как в timeit
  --whole         замерять ISOM-n на всех задачах файла подряд как на одной
                  программе (для наборов из многих мелких задач); печатается
                  один блок case __all__
  --no-maps       не печатать найденные изоморфизмы
  -v              подробный лог ISOM-n (как verbose=True в Python), строки с «| »

Формат входа (# — комментарий):
  case <имя>
  pred <имя> <арность> <n|c>     n — рёбра типа (1), c — типа (2)
  g1 <предикат> <вершина> ...    ребро G1 (G — константы)
  g2 <предикат> <вершина> ...    ребро G2 (из него строится шаблон H)
  end

Выход для каждой задачи:
  case <имя> / algo / iso 0|1 / reason ... / unifiers N /
  time_mean_ms / time_std_ms / samples N / number K (запусков в замере) /
  samples_ms ... (все замеры) / stats ... (для isom_n) /
  u b1=a4 b2=a3 ... (изоморфизмы G2 → G1) / end
)";
}

}  // namespace

int main(int argc, char** argv) {
    std::string algo = "isom_n", path;
    bool find_all = true, verbose = false, print_maps = true, whole = false;
    double min_sample = 0;
    long repeat = 1;
    for (int i = 1; i < argc; ++i) {
        const std::string a = argv[i];
        auto value = [&]() -> std::string {
            if (i + 1 >= argc) {
                usage();
                std::exit(2);
            }
            return argv[++i];
        };
        if (a == "--algo") algo = value();
        else if (a == "--first") find_all = false;
        else if (a == "--repeat") repeat = std::stol(value());
        else if (a == "--min-sample") min_sample = std::stod(value());
        else if (a == "--no-maps") print_maps = false;
        else if (a == "--whole") whole = true;
        else if (a == "-v") verbose = true;
        else if (a == "-h" || a == "--help") { usage(); return 0; }
        else if (path.empty()) path = a;
        else { usage(); return 2; }
    }
    if (path.empty() || (algo != "isom_n" && algo != "isom_1" && algo != "brute")) {
        usage();
        return 2;
    }

    std::vector<Case> cases;
    try {
        if (path == "-") {
            cases = read_cases(std::cin);
        } else {
            std::ifstream in(path);
            if (!in) throw std::runtime_error("не удалось открыть " + path);
            cases = read_cases(in);
        }
    } catch (const std::exception& e) {
        std::cerr << "ошибка: " << e.what() << '\n';
        return 1;
    }

    using clock = std::chrono::steady_clock;
    if (whole) {
        std::cout << "case __all__\nalgo isom_n\n";
        try {
            std::vector<Problem> problems;
            for (const Case& c : cases) problems.push_back(make_problem(c));
            std::vector<Solver> solvers;
            solvers.reserve(problems.size());
            for (const Problem& P : problems) solvers.emplace_back(P);
            auto run_all = [&] {
                for (Solver& S : solvers) S.isom_n(find_all, nullptr);
            };
            const auto t0 = clock::now();
            run_all();  // прогрев
            const double first = std::chrono::duration<double>(clock::now() - t0).count();
            print_timing(measure(run_all, first, repeat, min_sample));
        } catch (const std::exception& e) {
            std::cout << "error " << e.what() << '\n';
        }
        std::cout << "end\n";
        return 0;
    }
    for (const Case& c : cases) {
        std::cout << "case " << c.name << "\nalgo " << algo << '\n';
        try {
            const Problem P = make_problem(c);
            Solver S(P);
            auto run = [&](std::ostream* log) {
                if (algo == "isom_n") return S.isom_n(find_all, log);
                if (algo == "isom_1") return S.isom_1();
                return S.brute_force();
            };
            // первый запуск даёт результат и журнал и служит прогревом
            const auto t0 = clock::now();
            const Result res = run(verbose ? &std::cout : nullptr);
            const double first = std::chrono::duration<double>(clock::now() - t0).count();
            const Timing tm = measure([&] { run(nullptr); }, first, repeat, min_sample);

            std::cout << "iso " << res.iso << '\n';
            if (!res.reason.empty()) std::cout << "reason " << res.reason << '\n';
            std::cout << "unifiers " << res.unifiers.size() << '\n';
            print_timing(tm);
            if (algo == "isom_n") {
                const Stats& s = res.stats;
                std::cout << "stats map_calls=" << s.map_calls << " map_fail=" << s.map_fail
                          << " nodes=" << s.nodes << " cands=" << s.cands
                          << " consistent=" << s.consistent << " complete=" << s.complete
                          << " partial=" << s.partial << '\n';
            }
            if (print_maps)
                for (const auto& lam : res.unifiers) {
                    std::cout << 'u';
                    for (size_t x = 0; x < lam.size(); ++x)
                        std::cout << ' ' << P.bname[x] << '=' << P.cname[lam[x]];
                    std::cout << '\n';
                }
        } catch (const std::exception& e) {
            std::cout << "error " << e.what() << '\n';
        }
        std::cout << "end\n";
    }
    return 0;
}
