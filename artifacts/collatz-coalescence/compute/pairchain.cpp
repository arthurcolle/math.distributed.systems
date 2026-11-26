// Exact merger counts C_k for neighbours under the shortcut Collatz map, via the pair chain.
//
//   T(x) = x/2 (x even), (3x+1)/2 (x odd)
//   C_k  = #{ r mod 2^k : T^k(r + 2^k q) = T^k(r + 1 + 2^k q) for every q >= 0 }
//
// On the cylinder of r the two iterates p, p' satisfy p' = 3^d p + mu (roles swapped when needed so
// that d >= 0; for d = 0 the sign is normalised to mu >= 0).  The state (d, mu) moves by one fair
// coin (the parity of p) per step, and (0,0) is absorbing = merged:
//   mu even: coin0 -> (d, mu/2)            coin1 -> (d, (3mu + 1 - 3^d)/2)
//   mu odd : coin0 -> (d+1, (3mu+1)/2)     coin1 -> (d-1, (mu - 3^(d-1))/2)   [d >= 1]
//                                          coin1 -> (1, (1-3mu)/2)            [d = 0]
// C_k = number of coin words of length k that lead from (0,1) to (0,0).
//
// Modes
//   fwd J frontier.bin       forward pass with merging to depth J: prints  k C_k #states ; writes the frontier
//   bwd frontier.bin I       backward pass: A_i(s) = #words of length i from s to (0,0), i = 1..I,
//                            joined with the frontier: prints  J+i C_{J+i} #states(A_i)
//
// Counts are exact integers.  mu is held in 128 bits; |mu| <= 3^k/18 on the forward side.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <thread>
#include <vector>
typedef __int128 i128;
typedef unsigned __int128 u128;
struct R { uint64_t lo; int64_t hi; uint64_t vd; };              // mu = hi:lo, vd = (value << 8) | d ; 24 bytes
static i128 P3[81];
static inline i128 MU(const R& r) { return ((i128)r.hi << 64) | (i128)(u128)r.lo; }
static inline uint32_t D(const R& r) { return (uint32_t)(r.vd & 255); }
static inline uint64_t VAL(const R& r) { return r.vd >> 8; }
static inline R mk(uint32_t d, i128 mu, uint64_t v) { R r; r.lo = (uint64_t)(u128)mu; r.hi = (int64_t)(mu >> 64); r.vd = (v << 8) | d; return r; }
static inline bool mu_less(const R& a, const R& b) { return a.hi != b.hi ? a.hi < b.hi : a.lo < b.lo; }
static inline bool same_key(const R& a, const R& b) { return a.lo == b.lo && a.hi == b.hi && D(a) == D(b); }
static void print_u128(u128 v) { char buf[48]; int n = 0; if (v == 0) { putchar('0'); return; } while (v) { buf[n++] = '0' + (int)(v % 10); v /= 10; } while (n--) putchar(buf[n]); }

// sort by (d, mu) and add up values of equal keys.  Bucket by d, then sort buckets in parallel.
static void sort_merge(std::vector<R>& v) {
    size_t n = v.size(); if (n == 0) return;
    std::vector<size_t> cnt(257, 0);
    for (const R& r : v) cnt[D(r) + 1]++;
    for (int i = 0; i < 256; i++) cnt[i + 1] += cnt[i];
    {
        std::vector<R> tmp(n); std::vector<size_t> pos(cnt.begin(), cnt.end() - 1);
        for (const R& r : v) tmp[pos[D(r)]++] = r;
        v.swap(tmp);
    }
    std::vector<int> order; for (int d = 0; d < 256; d++) if (cnt[d + 1] > cnt[d]) order.push_back(d);
    std::sort(order.begin(), order.end(), [&](int a, int b) { return cnt[a + 1] - cnt[a] > cnt[b + 1] - cnt[b]; });
    std::vector<size_t> newlen(256, 0);
    unsigned nt = std::max(1u, std::min(16u, std::thread::hardware_concurrency()));
    std::vector<std::thread> th; size_t next = 0; std::mutex* mx = new std::mutex();
    for (unsigned t = 0; t < nt; t++) th.emplace_back([&]() {
        for (;;) {
            size_t k; { std::lock_guard<std::mutex> g(*mx); if (next >= order.size()) return; k = next++; }
            int d = order[k]; R* b = v.data() + cnt[d]; R* e = v.data() + cnt[d + 1];
            std::sort(b, e, mu_less);
            R* w = b;
            for (R* i = b; i < e;) { R* j = i; uint64_t s = 0; while (j < e && j->lo == i->lo && j->hi == i->hi) { s += VAL(*j); ++j; } *w = *i; w->vd = (s << 8) | (uint32_t)d; ++w; i = j; }
            newlen[d] = (size_t)(w - b);
        }
    });
    for (auto& t : th) t.join();
    delete mx;
    size_t w = 0;
    for (int d = 0; d < 256; d++) { if (newlen[d] && w != cnt[d]) memmove(v.data() + w, v.data() + cnt[d], newlen[d] * sizeof(R)); w += newlen[d]; }
    v.resize(w);
}
static inline void emit(std::vector<R>& out, u128& absorbed, uint32_t d, i128 mu, uint64_t v) {
    if (d == 0) { if (mu < 0) mu = -mu; if (mu == 0) { absorbed += v; return; } }
    out.push_back(mk(d, mu, v));
}
// one forward level; returns the weight absorbed at this step
static u128 forward_level(std::vector<R>& cur, std::vector<R>& nxt) {
    nxt.clear(); nxt.reserve(cur.size() * 2); u128 absorbed = 0;
    for (const R& s : cur) {
        i128 mu = MU(s); uint32_t d = D(s); uint64_t v = VAL(s);
        if ((mu & 1) == 0) { emit(nxt, absorbed, d, mu / 2, v); emit(nxt, absorbed, d, (3 * mu + 1 - P3[d]) / 2, v); }
        else {
            emit(nxt, absorbed, d + 1, (3 * mu + 1) / 2, v);
            if (d >= 1) emit(nxt, absorbed, d - 1, (mu - P3[d - 1]) / 2, v); else emit(nxt, absorbed, 1, (1 - 3 * mu) / 2, v);
        }
    }
    sort_merge(nxt);
    return absorbed;
}
// one backward level: nxt(parent) += cur(child) over all transitions parent -> child.  (0,0) is never stored;
// its only other parent is (1,1), which receives 2^(i-1) at backward level i.
static void backward_level(std::vector<R>& cur, std::vector<R>& nxt, int i) {
    nxt.clear(); nxt.reserve(cur.size() * 2 + cur.size() / 2 + 16);
    nxt.push_back(mk(1, 1, (uint64_t)1 << (i - 1)));
    for (const R& s : cur) {
        i128 nu = MU(s); uint32_t d = D(s); uint64_t v = VAL(s);
        if (d >= 80) continue;
        if (d >= 2) {
            nxt.push_back(mk(d, 2 * nu, v));
            i128 t = 2 * nu - 1 + P3[d]; if (t % 3 == 0 && ((t / 3) & 1) == 0) nxt.push_back(mk(d, t / 3, v));
            t = 2 * nu - 1; if (t % 3 == 0 && ((t / 3) & 1) != 0) nxt.push_back(mk(d - 1, t / 3, v));
            nxt.push_back(mk(d + 1, 2 * nu + P3[d], v));
        } else if (d == 1) {
            nxt.push_back(mk(1, 2 * nu, v));
            i128 t = 2 * nu + 2; if (t % 3 == 0 && ((t / 3) & 1) == 0) nxt.push_back(mk(1, t / 3, v));
            t = 2 * nu - 1; if (t % 3 == 0 && ((t / 3) & 1) != 0 && t > 0) nxt.push_back(mk(0, t / 3, v));
            t = 1 - 2 * nu; if (t % 3 == 0 && ((t / 3) & 1) != 0 && t > 0) nxt.push_back(mk(0, t / 3, v));
            nxt.push_back(mk(2, 2 * nu + 3, v));
        } else {                                   // d == 0, nu > 0
            nxt.push_back(mk(0, 2 * nu, v));
            if (nu % 3 == 0) nxt.push_back(mk(0, 2 * nu / 3, v));
            nxt.push_back(mk(1, 2 * nu + 1, v));
            nxt.push_back(mk(1, 1 - 2 * nu, v));
        }
    }
    sort_merge(nxt);
}
int main(int argc, char** argv) {
    P3[0] = 1; for (int i = 1; i <= 80; i++) P3[i] = P3[i - 1] * 3;
    if (argc >= 4 && !strcmp(argv[1], "fwd")) {
        int J = atoi(argv[2]);
        std::vector<R> cur, nxt; cur.push_back(mk(0, 1, 1));
        u128 C = 0;
        for (int k = 1; k <= J; k++) {
            u128 a = forward_level(cur, nxt); C = 2 * C + a; cur.swap(nxt);
            if (k == J) std::vector<R>().swap(nxt);
            printf("%d ", k); print_u128(C); printf(" %zu\n", cur.size()); fflush(stdout);
        }
        FILE* f = fopen(argv[3], "wb"); if (!f) { perror("open"); return 1; }
        uint64_t hdr[4] = { cur.size(), (uint64_t)J, (uint64_t)C, (uint64_t)(C >> 64) };
        fwrite(hdr, 8, 4, f); fwrite(cur.data(), sizeof(R), cur.size(), f); fclose(f);
        return 0;
    }
    if (argc >= 4 && !strcmp(argv[1], "bwd")) {
        FILE* f = fopen(argv[2], "rb"); if (!f) { perror("open"); return 1; }
        uint64_t hdr[4]; if (fread(hdr, 8, 4, f) != 4) return 1;
        std::vector<R> F(hdr[0]); if (fread(F.data(), sizeof(R), hdr[0], f) != hdr[0]) { fprintf(stderr, "short read\n"); return 1; }
        fclose(f);
        int J = (int)hdr[1]; u128 CJ = ((u128)hdr[3] << 64) | hdr[2]; int I = atoi(argv[3]);
        std::vector<R> cur, nxt;
        for (int i = 1; i <= I; i++) {
            backward_level(cur, nxt, i); cur.swap(nxt);
            u128 sum = 0; size_t a = 0, b = 0;         // both sorted by (d, mu)
            while (a < F.size() && b < cur.size()) {
                uint32_t da = D(F[a]), db = D(cur[b]);
                if (da != db) { if (da < db) ++a; else ++b; continue; }
                if (mu_less(F[a], cur[b])) ++a; else if (mu_less(cur[b], F[a])) ++b;
                else { sum += (u128)VAL(F[a]) * VAL(cur[b]); ++a; ++b; }
            }
            u128 C = (CJ << i) + sum;
            printf("%d ", J + i); print_u128(C); printf(" %zu\n", cur.size()); fflush(stdout);
        }
        return 0;
    }
    fprintf(stderr, "usage: fwd J frontier.bin | bwd frontier.bin I\n"); return 2;
}
