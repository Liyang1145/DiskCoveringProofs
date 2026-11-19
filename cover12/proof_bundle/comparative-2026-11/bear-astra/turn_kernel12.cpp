#include <cstdint>

// Entries below zero encode impossible paths. All finite angle entries are
// less than 2^20, and the sentinel is -2^24.
extern "C" __declspec(dllexport)
void turn_maxplus(const std::int32_t* a, const std::int32_t* b,
                  std::int32_t* result, int n) {
    constexpr std::int32_t bad = -(1 << 24);
    for (int i = 0; i < n; ++i) {
        auto* row = result + i * n;
        for (int j = 0; j < n; ++j)
            row[j] = bad;
        for (int k = 0; k < n; ++k) {
            const auto x = a[i * n + k];
            if (x < 0)
                continue;
            const auto* source = b + k * n;
            for (int j = 0; j < n; ++j) {
                const auto y = source[j];
                const auto next = y < 0 ? bad : x + y;
                if (row[j] < next)
                    row[j] = next;
            }
        }
    }
}
