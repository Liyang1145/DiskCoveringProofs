// Enumerate the faces incident to the exterior of an abstract triangulated disk.
// Usage: outer_layer b n none|u,v:u,v node_limit [shells.tsv]
// The integer arc constants are verified by verify_outer_chords.py.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace {
using Mask = std::uint32_t;
using Count = std::uint64_t;
using Face = std::array<int, 3>;
constexpr int MaxB = 17, MaxN = 26;
constexpr int A = 473822, FloorTwoPi = 6283185;
constexpr int Cap[] = {A, 978000, 1562320, 2440000};
Mask bit(int i) { return Mask{1} << i; }

template <class F>
void each(Mask set, F f) {
    while (set) {
        int i = __builtin_ctz(set);
        set &= set - 1;
        f(i);
    }
}

struct Poly {
    std::array<int, MaxN> v{};
    int size = 0;

    int at(int i) const { return v[i % size]; }
    void add(int u) { v[size++] = u; }

    Poly slice(int i, int j) const {
        Poly p;
        for (; i <= j; ++i) p.add(at(i));
        return p;
    }
};

struct Cut { int u, v, w; };
struct State {
    std::array<Mask, MaxN> adj{};
    std::array<std::array<unsigned char, MaxB>, MaxB> hop{};
    std::array<std::array<int, MaxB>, MaxB> deficit{};
    int sites = 0;
};

struct Search {
    int b, n, total, span;
    Mask exterior;
    Count limit, visited = 0, shells = 0, representatives = 0, fillings = 0;
    bool truncated = false, filling = false;
    Count shell_index = 0;
    std::array<Count, MaxN> by_layer{};
    std::array<std::array<std::array<std::vector<Cut>, MaxB>, MaxB>, 4> cuts;
    std::vector<Poly> holes;
    std::vector<Face> faces;
    std::vector<std::pair<int, int>> symmetries;
    std::ostream* output;

    Search(int boundary, int sites, Count max_nodes, std::ostream* out)
        : b(boundary), n(sites), total(b*A - FloorTwoPi), span(b-12),
          exterior(bit(b)-1), limit(max_nodes), output(out) {
        for (int d = 1; d <= 3; ++d) {
            for (int i = 0; i < b; ++i) {
                for (int j = i+1; j < b; ++j) {
                    for (int di = 0; di <= 1; ++di) {
                        for (int dj = 0; dj <= 1; ++dj) {
                            int u = (i+di)%b, v = (j+dj)%b, s = (v+b-u)%b;
                            if (2*s > b) {
                                s = b-s;
                                std::swap(u, v);
                            }
                            int w = s*A - Cap[d];
                            if (w > 0) cuts[d][i][j].push_back({u, v, w - (u+s >= b ? total : 0)});
                        }
                    }
                }
            }
        }
    }

    int circular(int i, int j) const {
        int d = i < j ? j-i : i-j;
        return std::min(d, b-d);
    }

    bool constrain(State& s, Cut c) const {
        auto& d = s.deficit;
        if (d[c.v][c.u] + c.w > 0) return false;
        if (d[c.u][c.v] >= c.w) return true;
        for (int i = 0; i < b; ++i) {
            const int add = d[i][c.u] + c.w;
            for (int j = 0; j < b; ++j) d[i][j] = std::max(d[i][j], add + d[c.v][j]);
        }
        return true;
    }

    std::array<Mask, 3> reach(const State& s, int u) const {
        std::array<Mask, 3> r{bit(u) & exterior, (bit(u) | s.adj[u]) & exterior, 0};
        r[2] = r[1];
        each(s.adj[u], [&](int v) { r[2] |= s.adj[v] & exterior; });
        return r;
    }

    bool add_edge(State& s, int a, int c, bool fixed_chord = false) const {
        if (a == c || (s.adj[a] & bit(c))) return false;
        if (a < b && c < b && !fixed_chord) return false;
        if ((a < b) != (c < b)) {
            int outer = a < b ? a : c;
            int inner = a < b ? c : a;
            bool fits = true;
            each(s.adj[inner] & exterior, [&](int v) { fits &= circular(outer, v) <= span; });
            if (!fits) return false;
        }
        auto x = reach(s, a), y = reach(s, c);
        bool valid = true;
        for (int d = 1; d <= 3 && valid; ++d) {
            for (int k = 0; k < d && valid; ++k) {
                each(x[k], [&](int i) {
                    each(y[d-1-k], [&](int j) {
                        if (!valid || d >= s.hop[i][j]) return;
                        s.hop[i][j] = s.hop[j][i] = d;
                        for (auto cut : cuts[d][std::min(i,j)][std::max(i,j)]) {
                            if (!constrain(s, cut)) {
                                valid = false;
                                break;
                            }
                        }
                    });
                });
            }
        }
        if (!valid) return false;
        s.adj[a] |= bit(c);
        s.adj[c] |= bit(a);
        return true;
    }

    State initial() const {
        State s;
        s.sites = b;
        for (int i = 0; i < b; ++i) {
            s.adj[i] = bit((i+1)%b) | bit((i+b-1)%b);
            for (int j = 0; j < b; ++j) {
                s.hop[i][j] = std::min(circular(i, j), 4);
                s.deficit[i][j] = i <= j ? 0 : -total;
            }
        }
        return s;
    }

    void run(const std::vector<std::pair<int, int>>& chords) {
        std::vector<std::pair<int, int>> given = chords;
        for (auto& c : given) if (c.first > c.second) std::swap(c.first, c.second);
        std::sort(given.begin(), given.end());
        for (int shift = 0; shift < b; ++shift) for (int sign : {1, -1}) {
            std::vector<std::pair<int, int>> mapped;
            for (auto [i, j] : given) {
                int u = (b + shift + sign*i)%b, v = (b + shift + sign*j)%b;
                mapped.emplace_back(std::min(u,v), std::max(u,v));
            }
            std::sort(mapped.begin(), mapped.end());
            if (mapped == given) symmetries.emplace_back(shift, sign);
        }
        State s = initial();
        Poly outer;
        for (int i = 0; i < b; ++i) outer.add(i);
        holes.push_back(outer);
        for (auto [u, v] : chords) {
            if (u < 0 || v < 0 || u >= b || v >= b || !add_edge(s, u, v, true))
                throw std::invalid_argument("Invalid initial chord");
            bool found = false;
            for (std::size_t i = 0; i < holes.size(); ++i) {
                Poly p = holes[i];
                auto a = std::find(p.v.begin(), p.v.begin()+p.size, u) - p.v.begin();
                auto c = std::find(p.v.begin(), p.v.begin()+p.size, v) - p.v.begin();
                if (a == p.size || c == p.size) continue;
                if (a > c) std::swap(a, c);
                if (c-a < 2 || p.size-c+a < 2) throw std::invalid_argument("Chord is a boundary edge");
                holes[i] = p.slice(a,c);
                holes.push_back(p.slice(c,a+p.size));
                found = true;
                break;
            }
            if (!found) throw std::invalid_argument("Crossing initial chords");
        }
        visit(s);
    }

    void fill(Count index, const std::string& line) {
        filling = true;
        shell_index = index;
        holes.clear();
        faces.clear();
        State s = initial();
        std::istringstream input(line);
        std::string field;
        if (!std::getline(input, field, '\t')) throw std::invalid_argument("No shell header");
        int h = std::stoi(field);
        if (h < 1 || b+h >= n) throw std::invalid_argument("Invalid layer count");
        s.sites = b+h;
        bool hole = false;
        while (std::getline(input, field, '\t')) {
            if (field == "/") {
                if (hole) throw std::invalid_argument("Duplicate hole marker");
                hole = true;
                continue;
            }
            Poly p;
            std::istringstream segment(field);
            std::string item;
            Mask seen = 0;
            while (std::getline(segment, item, ',')) {
                int v = std::stoi(item);
                if (v < 0 || v >= s.sites || (seen & bit(v)) || (hole && v < b))
                    throw std::invalid_argument("Invalid shell vertex");
                seen |= bit(v);
                p.add(v);
            }
            if (hole) {
                if (p.size < 3) throw std::invalid_argument("Invalid hole");
                holes.push_back(p);
            } else {
                if (p.size != 3) throw std::invalid_argument("Invalid shell face");
                for (int j = 0; j < 3; ++j) {
                    int u = p.at(j), v = p.at(j+1);
                    if (!(s.adj[u] & bit(v)) && !add_edge(s,u,v,true))
                        throw std::invalid_argument("Invalid shell edge");
                }
            }
        }
        if (holes.empty()) throw std::invalid_argument("Missing inner holes");
        visit(s);
    }

    bool canonical() const {
        std::array<std::array<int, MaxN>, MaxB> after;
        for (auto& row : after) row.fill(-1);
        for (const auto& f : faces) for (int k = 0; k < 3; ++k) {
            int v = f[k];
            if (v < b) {
                int u = f[(k+1)%3], w = f[(k+2)%3];
                if (after[v][u] >= 0) throw std::logic_error("Duplicate link step");
                after[v][u] = w;
            }
        }
        std::array<Poly, MaxB> links;
        for (int i = 0; i < b; ++i) {
            int u = (i+1)%b;
            while (u >= 0) {
                if (links[i].size == MaxN) throw std::logic_error("Cyclic exterior link");
                links[i].add(u);
                u = after[i][u];
            }
            if (links[i].at(links[i].size-1) != (i+b-1)%b)
                throw std::logic_error("Open exterior link");
        }
        auto key = [&](int shift, int sign) {
            std::array<int, MaxN> names;
            names.fill(-1);
            int next = b;
            std::vector<int> result;
            for (int i = 0; i < b; ++i) {
                const Poly& link = links[(b+sign*(i-shift))%b];
                for (int j = 0; j < link.size; ++j) {
                    int u = link.at(sign > 0 ? j : link.size-1-j);
                    if (u < b) result.push_back((b+shift+sign*u)%b);
                    else {
                        if (names[u] < 0) names[u] = next++;
                        result.push_back(names[u]);
                    }
                }
                result.push_back(-1);
            }
            return result;
        };
        auto original = key(0, 1);
        for (auto [shift, sign] : symmetries)
            if ((shift != 0 || sign != 1) && key(shift, sign) < original) return false;
        return true;
    }

    void visit(const State& s) {
        if (truncated) return;
        if (limit && visited == limit) {
            truncated = true;
            return;
        }
        ++visited;
        int hole = -1, start = -1;
        std::tuple<int, int, int> best{1, 0, 0};
        for (int i = 0; i < static_cast<int>(holes.size()); ++i) {
            const Poly& p = holes[i];
            for (int j = 0; j < p.size; ++j) {
                int u = p.at(j), v = p.at(j+1), exterior_count = (u < b) + (v < b);
                if (!filling && !exterior_count) continue;
                auto key = std::make_tuple(-exterior_count, u, v);
                if (key < best) {
                    best = key;
                    hole = i;
                    start = j;
                }
            }
        }
        if (hole < 0) {
            if (filling) {
                if (s.sites == n && holes.empty()) {
                    ++fillings;
                    if (output) {
                        *output << shell_index;
                        for (const Face& f : faces)
                            *output << '\t' << f[0] << ',' << f[1] << ',' << f[2];
                        *output << '\n';
                    }
                }
                return;
            }
            if (holes.empty()) return;  // There must be room for the origin site.
            ++shells;
            if (!canonical()) return;
            ++representatives;
            ++by_layer[s.sites-b];
            if (output) {
                *output << s.sites-b;
                for (const Face& f : faces) *output << '\t' << f[0] << ',' << f[1] << ',' << f[2];
                *output << "\t/";
                for (const Poly& p : holes) {
                    *output << '\t' << p.at(0);
                    for (int j = 1; j < p.size; ++j) *output << ',' << p.at(j);
                }
                *output << '\n';
            }
            return;
        }
        std::swap(holes[hole], holes.back());
        Poly original = holes.back(), p = original.slice(start,start+original.size-1);
        holes.pop_back();
        int u = p.at(0), v = p.at(1);
        for (int k = 2; k < p.size && !truncated; ++k) {
            int w = p.at(k);
            bool uw = k != p.size-1, vw = k != 2;
            State next = s;
            if ((uw && !add_edge(next, u, w)) || (vw && !add_edge(next, v, w))) continue;
            if (vw) holes.push_back(p.slice(1,k));
            if (uw) holes.push_back(p.slice(k,p.size));
            faces.push_back({u, v, w});
            visit(next);
            faces.pop_back();
            if (uw) holes.pop_back();
            if (vw) holes.pop_back();
        }
        if (s.sites < n-int(!filling) && !truncated) {
            State next = s;
            int w = next.sites++;
            if (add_edge(next, u, w) && add_edge(next, v, w)) {
                Poly q;
                q.add(u);
                q.add(w);
                for (int j = 1; j < p.size; ++j) q.add(p.at(j));
                holes.push_back(q);
                faces.push_back({u, v, w});
                visit(next);
                faces.pop_back();
                holes.pop_back();
            }
        }
        holes.push_back(original);
        std::swap(holes[hole], holes.back());
    }
};
}

int main(int argc, char** argv) {
    if (argc >= 8 && argc <= 9 && std::string(argv[1]) == "--fill") {
        int b = std::stoi(argv[2]), n = std::stoi(argv[3]);
        if (b < 14 || b > 17 || n < 25 || n > 26 || n-b < 9) return 1;
        std::ifstream input(argv[4]);
        if (!input) return 1;
        Count first = std::stoull(argv[5]), stop = std::stoull(argv[6]), limit = std::stoull(argv[7]);
        std::ofstream output;
        if (argc == 9) {
            output.open(argv[8], std::ios::binary);
            if (!output) return 1;
        }
        Search search(b, n, limit, argc == 9 ? &output : nullptr);
        std::string line;
        Count index = 0;
        for (; index < first && std::getline(input,line); ++index) {}
        for (; index < stop && !search.truncated && std::getline(input,line); ++index)
            search.fill(index, line);
        std::cout << "b=" << b << " n=" << n << " visited=" << search.visited
                  << " fillings=" << search.fillings << " truncated=" << search.truncated << '\n';
        return 0;
    }
    if (argc != 5 && argc != 6) {
        std::cerr << "Usage: outer_layer b n none|u,v:u,v node_limit [shells.tsv]\n";
        return 1;
    }
    int b = std::stoi(argv[1]), n = std::stoi(argv[2]);
    if (b < 14 || b > 17 || n < 25 || n > 26 || n-b < 9) return 1;
    std::vector<std::pair<int, int>> chords;
    if (std::string(argv[3]) != "none") {
        std::istringstream chord_list(argv[3]);
        std::string x;
        while (std::getline(chord_list,x,':')) {
            auto cut = x.find(',');
            if (cut == std::string::npos) return 1;
            chords.emplace_back(std::stoi(x.substr(0,cut)), std::stoi(x.substr(cut+1)));
        }
    }
    std::ofstream output;
    if (argc == 6) {
        output.open(argv[5], std::ios::binary);
        if (!output) return 1;
    }
    Search search(b, n, std::stoull(argv[4]), argc == 6 ? &output : nullptr);
    search.run(chords);
    std::cout << "b=" << b << " n=" << n << " chords=" << argv[3]
              << " visited=" << search.visited << " shells=" << search.shells
              << " representatives=" << search.representatives
              << " truncated=" << search.truncated << '\n';
    for (int h = 0; h < MaxN; ++h) if (search.by_layer[h])
        std::cout << h << ' ' << search.by_layer[h] << '\n';
}
