// Exact enumeration of the outer layer in the b=14, n=26 disk triangulations.
// Build: g++ -O3 -std=c++17 belt14.cpp -o belt14.exe
// Run:   .\belt14.exe [output.tsv]
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

namespace {
constexpr int B = 14;
constexpr int Inside = 12;
constexpr int Layer = Inside - 1;  // A disk covering 0 cannot neighbor the exterior.
constexpr int MaxVertices = B + Layer + (Layer - 1) / 2;
using Mask = std::uint32_t;
using Path = std::vector<int>;
using Face = std::array<int, 3>;

int mod(int i) { return (i + B) % B; }
Mask bit(int i) { return Mask{1} << i; }

int distance_on_boundary(int i, int j) {
    int d = std::abs(i - j);
    return std::min(d, B - d);
}

std::array<Mask, 1 << B> forbidden_masks() {
    std::array<Mask, 1 << B> masks{};
    for (int i = 0; i < B; ++i) {
        for (int j = 0; j < B; ++j) {
            if (distance_on_boundary(i, j) >= 5) masks[bit(i)] |= bit(j);
        }
    }
    for (Mask m = 1; m < masks.size(); ++m) {
        const Mask least = m & (0u - m);
        masks[m] = masks[least] | masks[m ^ least];
    }
    return masks;
}

const auto far = forbidden_masks();

bool is_dihedral_representative(Path lengths) {
    const Path original = lengths;
    for (int orientation = 0; orientation < 2; ++orientation) {
        for (std::size_t j = 0; j < lengths.size(); ++j) {
            if (lengths < original) return false;
            std::rotate(lengths.begin(), lengths.begin() + 1, lengths.end());
        }
        std::reverse(lengths.begin(), lengths.end());
    }
    return true;
}

// Decompose a closed face walk at repeated vertices. The paths returned
// include their closing vertex. A length-two walk represents a bridge.
void split_walk(const Path& walk, std::vector<Path>& blocks) {
    std::array<int, Layer> first;
    first.fill(-1);
    for (int i = 0; i + 1 < static_cast<int>(walk.size()); ++i) {
        int& j = first[walk[i]];
        if (j >= 0) {
            Path part(walk.begin() + j, walk.begin() + i + 1);
            Path rest(walk.begin(), walk.begin() + j);
            rest.insert(rest.end(), walk.begin() + i, walk.end());
            split_walk(part, blocks);
            split_walk(rest, blocks);
            return;
        }
        j = i;
    }
    blocks.push_back(walk);
}

// Check a provisional filling with one temporary apex per non-bridge block.
// The oriented links check the local manifold property including the boundary.
bool disk(const std::vector<Face>& faces, int vertices) {
    std::array<std::array<int, MaxVertices>, MaxVertices> next, prev;
    for (auto& row : next) row.fill(-1);
    for (auto& row : prev) row.fill(-1);
    std::array<Mask, MaxVertices> neighbors{};
    for (const Face& f : faces) {
        for (int i = 0; i < 3; ++i) {
            int a = f[i], u = f[(i + 1) % 3], v = f[(i + 2) % 3];
            if (a == u || a == v || u == v || next[a][u] != -1 || prev[a][v] != -1) {
                return false;
            }
            next[a][u] = v;
            prev[a][v] = u;
            neighbors[a] |= bit(u) | bit(v);
        }
    }
    int twice_edges = 0;
    for (int a = 0; a < vertices; ++a) {
        Mask used = 0;
        int start = -1;
        for (int j = 0; j < vertices; ++j) {
            if (!(neighbors[a] & bit(j))) continue;
            ++twice_edges;
            start = j;
            bool open_start = a < B && j == mod(a + 1);
            bool open_end = a < B && j == mod(a - 1);
            if ((prev[a][j] == -1) != open_start || (next[a][j] == -1) != open_end) {
                return false;
            }
        }
        if (start == -1) return false;
        if (a < B) start = mod(a + 1);
        int j = start, last = -1;
        while (j != -1 && !(used & bit(j))) {
            used |= bit(j);
            last = j;
            j = next[a][j];
        }
        if (used != neighbors[a] || (a < B ? (j != -1 || last != mod(a - 1)) : j != start)) {
            return false;
        }
    }
    return twice_edges % 2 == 0 &&
           vertices - twice_edges / 2 + static_cast<int>(faces.size()) == 1;
}

struct Enumerator {
    explicit Enumerator(std::ostream* output) : out(output) {}

    std::ostream* out;
    Path lengths;
    std::array<int, B> apex{};
    std::array<Mask, Layer> profile{}, compatible{}, outgoing{};
    std::array<std::vector<Path>, B> options;
    std::array<const Path*, B> selected{};
    std::vector<Mask> gap_profiles;
    Path walk;
    int apices = 0, h = 0;
    Mask active_slots = 0;
    std::uint64_t compositions = 0, profile_choices = 0, path_choices = 0;
    std::uint64_t valid_disks = 0, retained = 0;
    std::map<std::tuple<int, int, int, int>, std::uint64_t> counts;

    void enumerate(int left) {
        if (left == 0) {
            if (is_dihedral_representative(lengths)) start_composition();
            return;
        }
        if (lengths.size() >= Layer) return;
        for (int j = 1; j <= 2 && j <= left; ++j) {
            lengths.push_back(j);
            enumerate(left - j);
            lengths.pop_back();
        }
    }

    void start_composition() {
        ++compositions;
        apices = static_cast<int>(lengths.size());
        int j = 0;
        for (int a = 0; a < apices; ++a) {
            profile[a] = bit(j);
            for (int s = 0; s < lengths[a]; ++s) {
                apex[j] = a;
                profile[a] |= bit(mod(++j));
            }
        }
        active_slots = 0;
        for (j = 0; j < B; ++j) {
            if (apex[mod(j - 1)] != apex[j]) active_slots |= bit(j);
        }
        std::set<Mask> gaps;
        for (j = 0; j < B; ++j) {
            Mask m = (bit(j) | bit(mod(j + 1)) | bit(mod(j + 2))) & active_slots;
            for (Mask sub = m; sub; sub = (sub - 1) & m) gaps.insert(sub);
        }
        gap_profiles.assign(gaps.begin(), gaps.end());
        extend_apices(0, 0);
    }

    void extend_apices(int a, int first) {
        if (a == apices) {
            h = apices;
            add_gaps(0);
            return;
        }
        const Mask original = profile[a];
        extend_apices(a + 1, first + lengths[a]);
        if (lengths[a] != 1) return;
        for (int j : {mod(first - 1), mod(first + 2)}) {
            if (!(active_slots & bit(j))) continue;
            profile[a] = original | bit(j);
            extend_apices(a + 1, first + 1);
        }
        profile[a] = original;
    }

    void add_gaps(std::size_t first) {
        build_paths();
        if (h == Layer) return;
        for (std::size_t j = first; j < gap_profiles.size(); ++j) {
            profile[h++] = gap_profiles[j];
            add_gaps(j);
            --h;
        }
    }

    void build_paths() {
        ++profile_choices;
        for (int i = 0; i < h; ++i) {
            compatible[i] = 0;
            for (int j = 0; j < h; ++j) {
                if (i != j && !(far[profile[i]] & profile[j])) compatible[i] |= bit(j);
            }
        }
        for (int j = 0; j < B; ++j) {
            options[j].clear();
            int u = apex[mod(j - 1)], v = apex[j];
            if (u == v) {
                options[j].push_back({u});
                continue;
            }
            Path extras;
            for (int i = 0; i < h; ++i) {
                if (i != u && i != v && (profile[i] & bit(j))) extras.push_back(i);
            }
            do {
                int last = u;
                bool ok = true;
                for (int a : extras) {
                    if (!(compatible[last] & bit(a))) {
                        ok = false;
                        break;
                    }
                    last = a;
                }
                if (ok && (compatible[last] & bit(v))) {
                    Path p{u};
                    p.insert(p.end(), extras.begin(), extras.end());
                    p.push_back(v);
                    options[j].push_back(std::move(p));
                }
            } while (std::next_permutation(extras.begin(), extras.end()));
            if (options[j].empty()) return;
        }
        outgoing.fill(0);
        walk = {apex[B - 1]};
        choose_paths(0);
    }

    void choose_paths(int j) {
        if (j == B) {
            assess_walk();
            return;
        }
        for (const Path& p : options[j]) {
            std::size_t s = 1;
            while (s < p.size() && !(outgoing[p[s - 1]] & bit(p[s]))) {
                outgoing[p[s - 1]] |= bit(p[s]);
                ++s;
            }
            if (s == p.size()) {
                selected[j] = &p;
                const auto before = walk.size();
                walk.insert(walk.end(), p.begin() + 1, p.end());
                choose_paths(j + 1);
                walk.resize(before);
            }
            for (std::size_t i = 1; i < s; ++i) outgoing[p[i - 1]] &= ~bit(p[i]);
        }
    }

    bool triangulates_without_core(const Path& loop) const {
        const int n = static_cast<int>(loop.size()) - 1;
        std::array<std::array<bool, Layer>, Layer> dp{};
        for (int i = 0; i + 1 < n; ++i) dp[i][i + 1] = true;
        for (int width = 2; width < n; ++width) {
            for (int i = 0; i + width < n; ++i) {
                int j = i + width, u = loop[i], v = loop[j];
                if (width != n - 1 &&
                    (!(compatible[u] & bit(v)) || (outgoing[u] & bit(v)) ||
                     (outgoing[v] & bit(u)))) continue;
                for (int k = i + 1; k < j; ++k) {
                    if (dp[i][k] && dp[k][j]) {
                        dp[i][j] = true;
                        break;
                    }
                }
            }
        }
        return dp[0][n - 1];
    }

    void assess_walk() {
        std::array<int, Layer> first;
        first.fill(-1);
        for (int j = 0; j < static_cast<int>(walk.size()); ++j) {
            if (first[walk[j]] == -1) first[walk[j]] = j;
        }
        for (int i = apices + 1; i < h; ++i) {
            if (profile[i - 1] == profile[i] && first[i - 1] > first[i]) return;
        }
        ++path_choices;
        if (walk.front() != walk.back()) throw std::logic_error("Unclosed walk");
        std::vector<Path> blocks;
        split_walk(walk, blocks);
        int total = 0, polygons = 0, needed = 0;
        for (const Path& p : blocks) {
            if (p.size() < 3) return;
            total += static_cast<int>(p.size()) - 2;
            if (p.size() == 3) continue;
            for (std::size_t j = 1; j < p.size(); ++j) {
                if (outgoing[p[j]] & bit(p[j - 1])) return;
            }
            ++polygons;
            needed += !triangulates_without_core(p);
        }
        // The face-edge blocks of an outer face walk form a cactus.
        if (total != h - 1) return;

        std::vector<Face> faces;
        for (int j = 0; j < B; ++j) {
            faces.push_back({j, mod(j + 1), B + apex[j]});
            const Path& p = *selected[j];
            for (std::size_t i = 1; i < p.size(); ++i) {
                faces.push_back({j, B + p[i], B + p[i - 1]});
            }
        }
        int vertex = B + h;
        for (const Path& p : blocks) {
            if (p.size() == 3) continue;
            for (std::size_t j = 1; j < p.size(); ++j) {
                faces.push_back({B + p[j - 1], B + p[j], vertex});
            }
            ++vertex;
        }
        if (!disk(faces, vertex)) return;
        ++valid_disks;
        if (polygons == 0 || needed > Inside - h) return;
        ++retained;
        ++counts[{apices, h, polygons, needed}];
        if (out) save(polygons, needed);
    }

    void save(int polygons, int needed) const {
        *out << apices << '\t' << h << '\t' << polygons << '\t' << needed;
        for (const Path* p : selected) {
            *out << '\t';
            for (std::size_t i = 0; i < p->size(); ++i) {
                if (i) *out << ',';
                *out << (*p)[i];
            }
        }
        *out << '\n';
    }

    void summarize() const {
        std::cout << "compositions=" << compositions << '\n'
                  << "profiles=" << profile_choices << '\n'
                  << "walks=" << path_choices << '\n'
                  << "disk_belts=" << valid_disks << '\n'
                  << "retained=" << retained << '\n';
        std::cout << "apices layer polygons core_needed count\n";
        for (const auto& [key, count] : counts) {
            const auto [a, s, p, c] = key;
            std::cout << a << ' ' << s << ' ' << p << ' ' << c << ' ' << count << '\n';
        }
    }
};

using Count = std::uint64_t;

Count add(Count a, Count b) {
    if (b > std::numeric_limits<Count>::max() - a) throw std::overflow_error("Count overflow");
    return a + b;
}

Count multiply(Count a, Count b) {
    if (a && b > std::numeric_limits<Count>::max() / a) throw std::overflow_error("Count overflow");
    return a * b;
}

struct Filler {
    bool emit = false;
    Count emit_left = 0, belt_index = 0;
    std::array<Mask, Inside> allowed{}, used{};
    std::vector<Path> holes;
    std::vector<Face> faces;
    Count calls = 0;

    bool new_edge(int u, int v) const {
        return (allowed[u] & bit(v)) && !(used[u] & bit(v));
    }

    void toggle(int u, int v) {
        used[u] ^= bit(v);
        used[v] ^= bit(u);
    }

    Count no_core(const Path& poly) const {
        const int n = static_cast<int>(poly.size());
        std::array<std::array<Count, Inside>, Inside> dp{};
        for (int i = 0; i + 1 < n; ++i) dp[i][i + 1] = 1;
        for (int width = 2; width < n; ++width) {
            for (int i = 0; i + width < n; ++i) {
                int j = i + width;
                if (width != n - 1 && !new_edge(poly[i], poly[j])) continue;
                for (int k = i + 1; k < j; ++k) {
                    dp[i][j] = add(dp[i][j], multiply(dp[i][k], dp[k][j]));
                }
            }
        }
        return dp[0][n - 1];
    }

    void write_fill() const {
        std::cout << belt_index;
        for (const Face& f : faces) std::cout << '\t' << f[0] << ',' << f[1] << ',' << f[2];
        std::cout << '\n';
    }

    Count fill(int next_core) {
        ++calls;
        if (emit && !emit_left) return 0;
        if (!emit && next_core == Inside) {
            Count ways = 1;
            for (const Path& p : holes) ways = multiply(ways, no_core(p));
            return ways;
        }
        if (holes.empty()) {
            if (next_core != Inside) return 0;
            write_fill();
            --emit_left;
            return 1;
        }
        Path poly = std::move(holes.back());
        holes.pop_back();
        const int m = static_cast<int>(poly.size());
        const int u = poly[0], v = poly[1];
        Count result = 0;
        // The third corner is an existing vertex of the current hole.
        for (int k = 2; k < m; ++k) {
            int w = poly[k];
            bool uw = k != m - 1, vw = k != 2;
            if ((uw && !new_edge(u, w)) || (vw && !new_edge(v, w))) continue;
            if (uw) toggle(u, w);
            if (vw) toggle(v, w);
            if (vw) holes.emplace_back(poly.begin() + 1, poly.begin() + k + 1);
            if (uw) {
                holes.emplace_back(poly.begin() + k, poly.end());
                holes.back().push_back(u);
            }
            if (emit) faces.push_back({u, v, w});
            result = add(result, fill(next_core));
            if (emit) faces.pop_back();
            if (uw) {
                holes.pop_back();
                toggle(u, w);
            }
            if (vw) {
                holes.pop_back();
                toggle(v, w);
            }
        }
        // Or it is an unseen core vertex. Its name is fixed by discovery order.
        if (next_core < Inside) {
            toggle(u, next_core);
            toggle(v, next_core);
            holes.push_back(poly);
            holes.back().insert(holes.back().begin() + 1, next_core);
            if (emit) faces.push_back({u, v, next_core});
            result = add(result, fill(next_core + 1));
            if (emit) faces.pop_back();
            holes.pop_back();
            toggle(v, next_core);
            toggle(u, next_core);
        }
        holes.push_back(std::move(poly));
        return result;
    }

    Count count_line(const std::string& line, int& apices, int& h,
                     const std::vector<std::pair<int, int>>& blocked) {
        std::istringstream in(line);
        int polygons, needed;
        if (!(in >> apices >> h >> polygons >> needed) || h < apices || h > Layer) {
            throw std::runtime_error("Invalid belt row");
        }
        faces.clear();
        Path walk;
        std::array<Mask, Inside> profile{};
        used.fill(0);
        for (int j = 0; j < B; ++j) {
            std::string field;
            if (!(in >> field)) throw std::runtime_error("Missing boundary link");
            std::replace(field.begin(), field.end(), ',', ' ');
            std::istringstream row(field);
            Path path;
            int x;
            while (row >> x) {
                if (x < 0 || x >= h) throw std::runtime_error("Invalid layer vertex");
                path.push_back(x);
                profile[x] |= bit(j);
            }
            if (path.empty() || (!walk.empty() && walk.back() != path.front())) {
                throw std::runtime_error("Unjoined boundary link");
            }
            for (std::size_t k = 1; k < path.size(); ++k) {
                used[path[k]] |= bit(path[k - 1]);
                used[path[k - 1]] |= bit(path[k]);
            }
            walk.insert(walk.end(), path.begin() + (j > 0), path.end());
        }
        if (walk.front() != walk.back()) throw std::runtime_error("Unclosed belt");
        for (int u = 0; u < Inside; ++u) {
            allowed[u] = 0;
            for (int v = 0; v < Inside; ++v) {
                if (u != v && !(far[profile[u]] & profile[v])) allowed[u] |= bit(v);
            }
        }
        for (const auto& [u, v] : blocked) {
            if (u < 0 || v < 0 || u >= h || v >= h || u == v) {
                throw std::runtime_error("Invalid forbidden chord");
            }
            if (used[u] & bit(v)) return 0;
            allowed[u] &= ~bit(v);
            allowed[v] &= ~bit(u);
        }
        std::vector<Path> blocks;
        split_walk(walk, blocks);
        holes.clear();
        for (Path& p : blocks) {
            if (p.size() < 3) throw std::runtime_error("Malformed inner face walk");
            if (p.size() > 3) {
                p.pop_back();
                holes.push_back(std::move(p));
            }
        }
        if (static_cast<int>(holes.size()) != polygons) {
            throw std::runtime_error("Inconsistent polygon count");
        }
        return fill(h);
    }
};

void count_fillings(const char* name, Count first, Count limit,
                    const char* blocked_file = nullptr, Count emit_limit = 0) {
    std::ifstream input(name);
    if (!input) throw std::runtime_error("Cannot open belt file");
    std::map<Count, std::vector<std::pair<int, int>>> blocked;
    if (blocked_file) {
        std::ifstream cuts(blocked_file);
        if (!cuts) throw std::runtime_error("Cannot open chord file");
        Count i;
        int u, v;
        while (cuts >> i >> u >> v) blocked[i].emplace_back(u, v);
        if (!cuts.eof()) throw std::runtime_error("Invalid chord file");
    }
    Filler filler;
    filler.emit = emit_limit != 0;
    filler.emit_left = emit_limit;
    std::string line;
    std::uint64_t skipped = 0, belts = 0, empty = 0;
    std::map<std::pair<int, int>, Count> hist;
    Count total = 0;
    while (skipped < first && std::getline(input, line)) ++skipped;
    while (belts < limit && (!filler.emit || filler.emit_left) && std::getline(input, line)) {
        int a, h;
        filler.belt_index = first + belts;
        Count count = filler.count_line(line, a, h, blocked[filler.belt_index]);
        total = add(total, count);
        hist[{a, h}] = add(hist[{a, h}], count);
        empty += count == 0;
        ++belts;
    }
    if (filler.emit) return;
    std::cout << "belts=" << belts << " empty=" << empty << " fillings=" << total
              << " calls=" << filler.calls << '\n';
    std::cout << "apices layer fillings\n";
    for (const auto& [p, n] : hist) std::cout << p.first << ' ' << p.second << ' ' << n << '\n';
}
}  // namespace

int main(int argc, char** argv) {
    if (argc >= 3 && argc <= 5 && std::string(argv[1]) == "--fill") {
        count_fillings(argv[2], argc >= 4 ? std::stoull(argv[3]) : 0,
                       argc >= 5 ? std::stoull(argv[4]) : std::numeric_limits<Count>::max());
        return 0;
    }
    if (argc == 4 && std::string(argv[1]) == "--chords") {
        count_fillings(argv[2], 0, std::numeric_limits<Count>::max(), argv[3]);
        return 0;
    }
    if ((argc == 6 || argc == 7) && std::string(argv[1]) == "--emit") {
        count_fillings(argv[2], std::stoull(argv[3]), std::stoull(argv[4]),
                       argc == 7 ? argv[6] : nullptr, std::stoull(argv[5]));
        return 0;
    }
    if (argc > 2) {
        std::cerr << "Usage: belt14 [output.tsv]\n";
        return 1;
    }
    std::ofstream output;
    if (argc == 2) {
        output.open(argv[1], std::ios::binary);
        if (!output) {
            std::cerr << "Cannot open the output file\n";
            return 1;
        }
    }
    Enumerator search(argc == 2 ? &output : nullptr);
    search.enumerate(B);
    search.summarize();
    if (argc == 2 && !output) {
        std::cerr << "Writing the output file failed\n";
        return 1;
    }
}
