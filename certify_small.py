#!/usr/bin/env python3
"""certify_small.py -- independent pure-Python checks for cutwidth.md.  Standard library only.

    python3 certify_small.py                 # full run: CHECKS + sup_t G_d(t) <= 0.1366   (under a minute, one core)
    python3 certify_small.py --gamma 0.1364  # a sharper target (slower)
    python3 certify_small.py --quick         # CHECKS + the four base intervals around the maximum (seconds)

It proves, with outward-rounded interval arithmetic and its own enclosures of exp and of the normal cdf Phi
(no math-library function enters any bound; math is not even imported), or with exact integer/rational
arithmetic, the following facts used in cutwidth.md:

 (C1) the window energy f = s_0 - s_0 s_1 s_2 s_3 - (1/2)(1 - s_0)(k - 1)^+ (cutwidth.md section 4) on {0,1}^10:
      2f takes values in [-2, 2]; flipping the centre (resp. a neighbour, a leaf) changes 2f by at most 3 (2, 1);
      every mixed difference of 2f lies in [-2, 1], and |.| = 2 occurs only for the pairs {0,i}, {i,j}; f is
      invariant under the 48 automorphisms of the window; (k-1)^+ = sum_{i<j} b_i b_j - b_1 b_2 b_3.  Exhaustive.
 (C2) the wave window (cutwidth.md section 5): the explicit construction has covariance w_d = (1 + d/3) 2^(-d/2)
      at tree distance d, d = 0..4, exactly (arithmetic in Q(sqrt2)).
 (C3) sup over all real t of G_d(t) = V(t) - (3/2) P2(t) + P3(t)/2 is <= gamma (default 0.1366), with V, P2, P3
      the wave probabilities of cutwidth.md section 5: a weaker form of Proposition C, by a different method and
      different code than edcert.c.
 (C4) every numerical witness (N1)-(N8) of cutwidth.md section 7, as exact rational inequalities.
 (C5) the binary64 constants hard-coded in edcert.c (enclosures of pi, pi/2, 1/sqrt(2 pi), the literals of the
      Phi routine, PI3_UP > pi/3, the double below pi used by icos, the range-reduction constants of exp against
      ln 2), read from edcert.c in the same directory; pi from Machin's formula, ln 2 from sum 1/(k 2^k) (Python's
      float() of a decimal literal is correctly rounded, as is the C compiler's).
 (C6) global submodularity (cutwidth.md Lemma 4.4): for p, q at tree distance d = 1..4 the sum over all windows
      containing p and q of the mixed difference of 2f is <= 0 for every assignment of the other coordinates
      (exact maximum by enumeration of the coordinates shared by two or more windows and, for each window,
      maximisation over its private coordinates); for lambda = 51/100 the maximum is positive (sharpness).
 (C7) every scalar inequality of the error analysis of edcert.c (cutwidth.md section 6.2, items (A2)-(A4), (A8)),
      as exact rational inequalities (u = 2^-53).

Method for (C3) (all identities are proved in cutwidth.md section 5; tau = tan psi there):
  V(t), t >= 0:  (3/pi) int_0^sqrt3 g_t(tau) dtau,  g_t = exp(-al t^2) Phi(be t) / ((1+tau^2) sqrt(9+8tau^2)),
                 al = 9(1+tau^2)/(2(9+8tau^2)),  be = (1 - kap(1+tau^2))/sqrt(9+8tau^2),  kap = 6 sqrt2 - 8.
                 For t in [a,b] (0 <= a): g_t(tau) <= exp(-al a^2) Phi(max(be a, be b)) / (...), which is
                 nonincreasing in tau, so its left Riemann sum on tau_k = k/2048 (k < 3548, 3548/2048 > sqrt3)
                 is an upper bound.
  V(t), t <= 0:  Phi(t) - Phi(c0 t) + (3/pi) int_0^sqrt3 exp(-al t^2) Phi(c0 t/sqrt(9+8tau^2)) / (...) dtau,
                 c0 = 3/(2 sqrt2); for t in [a,b], b <= 0: Phi(t) - Phi(c0 t) <= (c0-1)|a| phi(b), and the
                 integrand is <= [exp(-al b^2)/(...)](tau_k) * Phi(c0 b/sqrt(9+8tau^2))(tau_{k+1}) on a cell.
  P2(t) >= P2(a,b) = P[Y >= b, the six others < a] = int_{u>=b} phi(u) K_a(u) du, K_a(u) = E[G(x1) G(x2)],
                 G(x) = 1{x < M} H(kap_u - lam x), H = (2Phi - 1)^+, M = 3(a - r1 u), kap_u = sqrt12(a - 5u/6),
                 lam = 2 sqrt6/3, (x1, x2) standard normal with correlation -1/2.  Write x1 = x, x2 = -x/2 +
                 (sqrt3/2) y with x, y independent.  G(x1) is nonincreasing in x, E_y G(x2) is nondecreasing in x,
                 G(x2) is nonincreasing in y, K_a is nonincreasing in u.  Lower sums on the lattice
                 x_k = x0 + k sqrt3 h, y_l = sqrt3 x0 + l h, u_i = b + i (sqrt6/5) h: then every H argument that
                 occurs is base + J sqrt2 h (J integer) and every indicator is "J >= cut_i"; the double sum over
                 (x, y) becomes a running convolution (cutwidth.md section 6.5).
  P3(t) <= (1/r1 - 1) t phi(0) (1 - exp(-18 (1-r1)^2 t^2)) for t > 0, and P3 = 0 for t <= 0; increasing in t.
  Leaf [a,b]: G_d <= Vup + P3up(b)/2 - (3/2) P2low.  Tails: t <= -1.25: G_d <= V <= Phi(-1.25);  t >= 2:
  G_d <= V + P3/2 <= (7/2) Phi(-2).

Arithmetic and error bounds (u = 2^-53, every float operation is IEEE binary64 round-to-nearest):
  up(x) = x + (|x| 2^-52 + 2^-1074) evaluated in floating point is >= the next float above x, hence >= any real
      number whose round-to-nearest value is x; dn(x) = -up(-x).  Interval operations apply up/dn to each result.
  exp(z), z <= 0: z = 2^s y with -1/32 <= y <= 0 (exact scaling); P(y) = sum_{n<=12} y^n/n! by Horner.  The
      Horner error is <= 1.2u (each step adds <= 1.15u and damps the previous error by |y|/n <= 1/32) and the
      Taylor remainder is <= |y|^13/13! < 1e-29, so |P - e^y| <= 1e-15 P; then s interval squarings.
  Phi(x), |x| <= 9: Phi(|x|) = 1/2 + phi(x) S(|x|), S(x) = sum_n x^(2n+1)/(2n+1)!! (positive terms; S' = 1 + xS);
      the loop stops at n = N once x^2/(2N+3) <= 1/2 and the last term T_N <= 1e-17 S, so the omitted tail is
      <= T_N; each computed term and the sum carry a relative error <= 4.1 (N+1) u (<= 5 (N+2) u is used).
      |x| > 9: 1 - Phi(|x|) <= Phi(-9) <= phi(9)/9 < 1.2e-19 (Mills; checked in exact rationals by C5).
      |x| < 1e-150: |Phi(x) - 1/2| <= 0.4 |x|.
  Square roots: a float candidate is moved by dn/up until its square, rounded outward, brackets the radicand;
      pi from Machin's formula in exact rationals; 1/sqrt(2 pi) enclosed by exact rational squaring.
  Sums of nonnegative lower (upper) bounds are formed in plain floating point and multiplied by 1 - 1e-9
      (1 + 1e-9): with at most 10^5 roundings on any path, (1 + u)^(10^5) < 1 + 1.2e-11; underflow adds less
      than 10^5 * 2^-1074, covered by subtracting (adding) 1e-300.
Deterministic; no randomness, no threads.  Last line: "CERTIFIED gamma <= ..." or "FAILED".
"""
import itertools, sys, time
from fractions import Fraction as Fr

T0 = time.time()
def say(*a):
    print("[%7.1fs]" % (time.time() - T0), *a, flush=True)

# ------------------------------------------------------------------ outward rounding, intervals
EPS52, TINY = 2.0 ** -52, 5e-324
def up(x): return x + (abs(x) * EPS52 + TINY)
def dn(x): return x - (abs(x) * EPS52 + TINY)
def iadd(a, b): return (dn(a[0] + b[0]), up(a[1] + b[1]))
def isub(a, b): return (dn(a[0] - b[1]), up(a[1] - b[0]))
def imul(a, b):
    p = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (dn(min(p)), up(max(p)))
def idiv(a, b):
    assert b[0] > 0 or b[1] < 0
    p = (a[0] / b[0], a[0] / b[1], a[1] / b[0], a[1] / b[1])
    return (dn(min(p)), up(max(p)))
def pt(x): return (x, x)
def fr_iv(q):                       # enclosure of a rational
    f = float(q)
    lo, hi = f, f
    while Fr(lo) > q: lo = dn(lo)
    while Fr(hi) < q: hi = up(hi)
    return (lo, hi)
def isqrt(a):                       # enclosure of sqrt over a positive interval (no library sqrt)
    assert a[0] > 0
    def root(x, lower):
        r = x ** 0.5                # any approximation; verified below
        if lower:
            while up(r * r) > x: r = dn(r)
        else:
            while dn(r * r) < x: r = up(r)
        return r
    return (root(a[0], True), root(a[1], False))

def machin_pi():                    # 16 atan(1/5) - 4 atan(1/239), alternating partial sums bracket atan
    def at(x, n): return sum(Fr((-1) ** k) * x ** (2 * k + 1) / (2 * k + 1) for k in range(n + 1))
    lo = 16 * at(Fr(1, 5), 21) - 4 * at(Fr(1, 239), 6)
    hi = 16 * at(Fr(1, 5), 22) - 4 * at(Fr(1, 239), 5)
    assert lo < hi
    return lo, hi
PI_Q = machin_pi()
PI = (fr_iv(PI_Q[0])[0], fr_iv(PI_Q[1])[1])
def inv_sqrt_2pi():
    f = 0.3989422804014327
    lo, hi = f, f
    while Fr(lo) ** 2 * 2 * PI_Q[1] > 1: lo = dn(lo)
    while Fr(hi) ** 2 * 2 * PI_Q[0] < 1: hi = up(hi)
    return (lo, hi)
INVS2PI = inv_sqrt_2pi()
S2, S3, S6 = isqrt(pt(2.0)), isqrt(pt(3.0)), isqrt(pt(6.0))
S12 = imul(pt(2.0), S3)
R1 = idiv(imul(pt(2.0), S2), pt(3.0))
LAM = idiv(imul(pt(2.0), S6), pt(3.0))
KAP = isub(imul(pt(6.0), S2), pt(8.0))
C0 = idiv(pt(3.0), imul(pt(2.0), S2))
THREE_OVER_PI = idiv(pt(3.0), PI)

# ------------------------------------------------------------------ exp and Phi
def exp_neg(z):
    """enclosure (lo, hi) of e^z for a float z <= 0"""
    assert z <= 0.0
    if z < -700.0: return (0.0, 1e-300)
    s, y = 0, z
    while y < -0.03125: y *= 0.5; s += 1
    p = 1.0
    for n in range(12, 0, -1): p = 1.0 + (y / n) * p
    lo, hi = dn(p * (1.0 - 1e-15)), up(p * (1.0 + 1e-15))
    for _ in range(s): lo, hi = dn(lo * lo), up(hi * hi)
    return (lo, hi)
def exp_iv(a):  # a = (lo, hi), hi <= 0
    return (exp_neg(a[0])[0], exp_neg(a[1])[1])
def halfphi_part(ax):
    """enclosure of Phi(ax) - 1/2 = phi(ax) S(ax) for a float 1e-150 <= ax <= 9"""
    x2 = ax * ax
    T, S, n = ax, ax, 0
    while True:
        T = T * x2 / (2 * n + 3); n += 1; S += T
        if x2 <= 0.5 * (2 * n + 3) and T <= 1e-17 * S: break
    d = 5.0 * (n + 2) * 1.1102230246251565e-16
    Slo, Shi = dn(S * (1.0 - d)), up(up(S + T * (1.0 + d)) * (1.0 + d))
    e = exp_iv((-up(x2) * 0.5, -dn(x2) * 0.5))
    lo = dn(dn(e[0] * INVS2PI[0]) * Slo)
    hi = up(up(e[1] * INVS2PI[1]) * Shi)
    return (lo, min(hi, 0.5))
def Phi_pt(x):
    ax = abs(x)
    if ax > 9.0: return (0.9999999999999998, 1.0) if x > 0 else (0.0, 1.2e-19)    # Phi(-9) <= phi(9)/9 < 1.2e-19
    if ax < 1e-150: return (dn(0.5 - 0.4 * ax), up(0.5 + 0.4 * ax))
    lo, hi = halfphi_part(ax)
    if x >= 0: return (dn(0.5 + lo), min(1.0, up(0.5 + hi)))
    return (max(0.0, dn(0.5 - hi)), up(0.5 - lo))
def H_lo(z):
    """lower bound of H(z) = (2 Phi(z) - 1)^+ for a float z"""
    if z <= 1e-150: return 0.0
    if z > 9.0: return 0.9999999999999998
    return dn(2.0 * halfphi_part(z)[0])

# ------------------------------------------------------------------ (C1), (C6), (C2)
def f2(s, lnum=1, lden=2):
    """lden * f on a window pattern s (0 = centre, 1..3 = neighbours, children of i: 2i+2, 2i+3); lambda = lnum/lden"""
    k = sum(s[i] * s[2 * i + 2] * s[2 * i + 3] for i in (1, 2, 3))
    return lden * s[0] - lden * s[0] * s[1] * s[2] * s[3] - lnum * (1 - s[0]) * max(k - 1, 0)

def window_autos():
    """the 48 automorphisms of the rooted window: permute the branches, swap the two children inside a branch"""
    res = []
    for perm in itertools.permutations((1, 2, 3)):
        for sw in itertools.product((0, 1), repeat=3):
            m = [0] * 10
            for i, j in zip((1, 2, 3), perm):
                m[i] = j
                m[2 * i + 2], m[2 * i + 3] = (2 * j + 2, 2 * j + 3) if not sw[i - 1] else (2 * j + 3, 2 * j + 2)
            res.append(m)
    return res

def check_f():
    """(C1): range, flips, mixed differences, symmetry of 2f; the identity for (k-1)^+"""
    pats = list(itertools.product((0, 1), repeat=10))
    vals = {s: f2(s) for s in pats}
    par = [None, 0, 0, 0, 1, 1, 2, 2, 3, 3]
    def path(x):
        r = [x]
        while par[r[-1]] is not None: r.append(par[r[-1]])
        return r
    def dist(x, y):
        px, py = path(x), path(y)
        c = [z for z in px if z in py][0]
        return px.index(c) + py.index(c)
    big, md_all, npairs = set(), set(), {}
    for p, q in itertools.combinations(range(10), 2):
        npairs[dist(p, q)] = npairs.get(dist(p, q), 0) + 1
        mds = set()
        for s in pats:
            if s[p] == 0 and s[q] == 0:
                s11 = list(s); s11[p] = s11[q] = 1
                s10 = list(s); s10[p] = 1
                s01 = list(s); s01[q] = 1
                mds.add(vals[tuple(s11)] - vals[tuple(s10)] - vals[tuple(s01)] + vals[s])
        md_all |= mds
        if max(abs(m) for m in mds) > 1: big.add((p, q))
    rng = (min(vals.values()), max(vals.values()))
    flip = [max(abs(vals[s] - vals[s[:x] + (1 - s[x],) + s[x + 1:]]) for s in pats) for x in range(10)]
    sym = all(vals[s] == vals[tuple(s[m[x]] for x in range(10))] for m in window_autos() for s in pats)
    ident = all(max(k - 1, 0) == b[0] * b[1] + b[0] * b[2] + b[1] * b[2] - b[0] * b[1] * b[2]
                for b in itertools.product((0, 1), repeat=3) for k in [sum(b)])
    want_big = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}
    ok = (rng == (-2, 2) and flip == [3, 2, 2, 2, 1, 1, 1, 1, 1, 1] and min(md_all) == -2 and max(md_all) == 1
          and big == want_big and sym and ident and npairs == {1: 9, 2: 12, 3: 12, 4: 12})
    say("C1 f: range of 2f %s, flip sizes %s, mixed differences of 2f in [%d, %d], |.| = 2 only at %s, "
        "48 automorphisms %s, (k-1)^+ identity %s, pairs per distance %s -> %s"
        % (rng, flip, min(md_all), max(md_all), sorted(big), sym, ident, npairs, "ok" if ok else "FAIL"))
    return ok

def check_globsub():
    """(C6): exact maximum over all assignments of the summed mixed difference, distances 1..4 (and none beyond)"""
    adj, dep = {0: []}, {0: 0}
    n, frontier = 1, [0]
    while frontier:
        nxt = []
        for v in frontier:
            if dep[v] >= 6: continue
            for _ in range(3 if v == 0 else 2):
                w = n; n += 1
                adj[w] = [v]; adj[v].append(w); dep[w] = dep[v] + 1; nxt.append(w)
        frontier = nxt
    def bfs(s):
        d, fr = {s: 0}, [s]
        while fr:
            nf = []
            for v in fr:
                for w in adj[v]:
                    if w not in d: d[w] = d[v] + 1; nf.append(w)
            fr = nf
        return d
    D0 = bfs(0)
    def window(a):
        assert dep[a] <= 4 and len(adj[a]) == 3
        pos = [a] + list(adj[a])
        for y in adj[a]:
            assert len(adj[y]) == 3
            pos += [z for z in adj[y] if z != a]
        return pos
    ok, pos51 = True, 0
    report = []
    for d in range(1, 7):
        q = 1
        for _ in range(d - 1): q = adj[q][1]          # a child of q (adj[q][0] is the parent)
        assert D0[q] == d
        Dq = bfs(q)
        cent = [a for a in adj if D0.get(a, 99) <= 2 and Dq.get(a, 99) <= 2]
        if not cent:
            report.append("d=%d: no window" % d)
            ok = ok and d >= 5
            continue
        ok = ok and d <= 4
        wins = {a: window(a) for a in cent}
        owners = {}
        for a in cent:
            for x in wins[a]:
                if x not in (0, q): owners.setdefault(x, set()).add(a)
        shared = sorted(x for x in owners if len(owners[x]) >= 2)
        for lnum, lden in ((1, 2), (51, 100)):
            tabs = []
            for a in cent:
                w = wins[a]
                ip, iq = w.index(0), w.index(q)
                sh = [x for x in w if x in shared]
                pv = [x for x in w if x not in (0, q) and x not in shared]
                tmax, tmin = {}, {}
                for ssh in itertools.product((0, 1), repeat=len(sh)):
                    hi, lo = None, None
                    for spv in itertools.product((0, 1), repeat=len(pv)):
                        asg = dict(zip(sh, ssh)); asg.update(zip(pv, spv))
                        v = []
                        for e in range(4):
                            asg[0], asg[q] = e & 1, e >> 1
                            v.append(f2([asg[x] for x in w], lnum, lden))
                        m = v[3] - v[1] - v[2] + v[0]
                        hi = m if hi is None else max(hi, m)
                        lo = m if lo is None else min(lo, m)
                    tmax[ssh], tmin[ssh] = hi, lo
                tabs.append(([shared.index(x) for x in sh], tmax, tmin))
            best, worst = None, None
            for sig in itertools.product((0, 1), repeat=len(shared)):
                hi = sum(t[1][tuple(sig[i] for i in t[0])] for t in tabs)
                lo = sum(t[2][tuple(sig[i] for i in t[0])] for t in tabs)
                best = hi if best is None else max(best, hi)
                worst = lo if worst is None else min(worst, lo)
            if lden == 2: ok = ok and best <= 0
            elif best > 0: pos51 += 1
            report.append("d=%d lambda=%d/%d: %d windows, |U|=%d, %d shared, max %s, min %s"
                          % (d, lnum, lden, len(cent), len(owners) + 2, len(shared), Fr(best, lden), Fr(worst, lden)))
    ok = ok and pos51 > 0
    say("C6 global submodularity: " + "; ".join(report) + " -> " + ("ok" if ok else "FAIL"))
    return ok

def check_wave():
    # numbers p + q sqrt2 as (p, q); variables as coefficient vectors over (U, x1, x2, x3, d1, d2, d3)
    def mul(a, b): return (a[0] * b[0] + 2 * a[1] * b[1], a[0] * b[1] + a[1] * b[0])
    def add(a, b): return (a[0] + b[0], a[1] + b[1])
    Z, ONE = (Fr(0), Fr(0)), (Fr(1), Fr(0))
    base = [[ONE if i == j else (Fr(-1, 2), Fr(0)) if 1 <= i <= 3 and 1 <= j <= 3 else Z for j in range(7)]
            for i in range(7)]
    for i in (4, 5, 6): base[i][i] = (Fr(1, 12), Fr(0))
    r1 = (Fr(0), Fr(2, 3))
    def var(**c):
        v = [Z] * 7
        for k, x in c.items(): v[int(k[1:])] = x
        return v
    pos = [var(c0=ONE)]
    for i in (1, 2, 3): pos.append(var(c0=r1, **{"c%d" % i: (Fr(1, 3), Fr(0))}))
    for i in (1, 2, 3):
        for sg in (1, -1):   # child = sqrt2 z_i - U/2 +- d_i = (5/6) U + (sqrt2/3) x_i +- d_i
            pos.append(var(c0=(Fr(5, 6), Fr(0)), **{"c%d" % i: (Fr(0), Fr(1, 3)), "c%d" % (i + 3): (Fr(sg), Fr(0))}))
    def cov(a, b):
        s = Z
        for i in range(7):
            for j in range(7):
                s = add(s, mul(mul(a[i], base[i][j]), b[j]))
        return s
    par = [None, 0, 0, 0, 1, 1, 2, 2, 3, 3]
    def path(x):
        r = [x]
        while par[r[-1]] is not None: r.append(par[r[-1]])
        return r
    def dist(x, y):
        px, py = path(x), path(y)
        common = [z for z in px if z in py][0]
        return px.index(common) + py.index(common)
    w = {0: (Fr(1), Fr(0)), 1: (Fr(0), Fr(2, 3)), 2: (Fr(5, 6), Fr(0)), 3: (Fr(0), Fr(1, 2)), 4: (Fr(7, 12), Fr(0))}
    ok = all(cov(pos[x], pos[y]) == w[dist(x, y)] for x in range(10) for y in range(10))
    ok = ok and all(w[d] == ((1 + Fr(d, 3)) / 2 ** (d // 2), Fr(0)) if d % 2 == 0 else
                    w[d] == (Fr(0), (1 + Fr(d, 3)) / 2 ** (d // 2 + 1)) for d in w)
    say("C2 wave window: covariance of the construction = (1+d/3) 2^(-d/2) exactly ->", "ok" if ok else "FAIL")
    return ok

# ------------------------------------------------------------------ (C4), (C5)
GAMMA_D = Fr(13617, 100000)
DECLARED = Fr(23359, 5000)

def check_witnesses(verbose=True):
    """(N1)-(N8) of cutwidth.md section 7, exact"""
    lo_pi, hi_pi = PI_Q
    D = Fr
    W = []
    def w(name, cond): W.append((name, bool(cond)))
    w("N1 1.41421^2 < 2 < 1.41422^2", D("1.41421") ** 2 < 2 < D("1.41422") ** 2)
    w("N1 3.3166^2 < 11, 9.7467^2 < 95", D("3.3166") ** 2 < 11 and D("9.7467") ** 2 < 95)
    w("N1 3.14159 < pi < 3.1416", D("3.14159") < lo_pi and hi_pi < D("3.1416"))
    s = 6 * D("1.41422") + 60 / D("3.3166") + 19 + 216 / D("9.7467")
    w("N2 6*1.41422 + 60/3.3166 + 19 + 216/9.7467 < 67.738", s < D("67.738"))
    w("N2 3.1416*67.738/2 < 106.41", D("3.1416") * D("67.738") / 2 < D("106.41"))
    w("N2 eps^2 term: 45*2*1.41422/(2*3.14159) < 21", 45 * 2 * D("1.41422") / (2 * D("3.14159")) < 21)
    wd2 = [((1 + Fr(d, 3)) ** 2) / 2 ** d for d in (1, 2, 3, 4)]         # w_d^2
    w("N2 w_d^2/(1 - w_d^2) = 8, 25/11, 1, 49/95 <= 8 (so w_d/sqrt(1-w_d^2) <= 2 sqrt2)",
      [x / (1 - x) for x in wd2] == [8, Fr(25, 11), 1, Fr(49, 95)])
    w("N3 4*48 = 192 < 13.857^2", 4 * 48 < D("13.857") ** 2)
    w("N3 3 < 1.7321^2", 3 < D("1.7321") ** 2)
    w("N3 13.857 + (15/2)*1.7321 < 26.85", D("13.857") + Fr(15, 2) * D("1.7321") < D("26.85"))
    w("N3 (12 - 15/2)^2 * 3 = 243/4 < 192", (12 - Fr(15, 2)) ** 2 * 3 == Fr(243, 4) < 192)
    w("N3 26.85*1.41422/2 < 18.99", D("26.85") * D("1.41422") / 2 < D("18.99"))
    w("N4 45^2 < 17.96^2 * 2 * 3.14159", 45 ** 2 < D("17.96") ** 2 * 2 * D("3.14159"))
    w("N4 18.99 + 17.96 + 0.46 <= 38 and 30 < 0.46*2^35", D("18.99") + D("17.96") + D("0.46") <= 38
      and 30 < D("0.46") * 2 ** 35)
    w("N5 106.41*9 = 957.69 < 958", D("106.41") * 9 < 958)
    fact, e45 = 1, Fr(0)
    for k in range(30):
        if k: fact *= k
        e45 += Fr(9, 2) ** k / fact               # partial sum < e^(9/2)
    w("N6 e^4.5 > 90 (partial sum of the exponential series)", e45 > 90)
    w("N6 4/(90*2.5066) < 0.0178 < gamma_d and 2.5066^2 < 2*3.14159", Fr(4) / (90 * D("2.5066")) < D("0.0178")
      < GAMMA_D and D("2.5066") ** 2 < 2 * D("3.14159"))
    w("N7 2^40 < 22^9 and 38/22 > 3/2 - gamma_d = 136383/100000", Fr(2) ** 40 < Fr(22) ** 9
      and Fr(38, 22) > Fr(3, 2) - GAMMA_D == Fr(136383, 100000))
    cstar = 1 + 1 / (2 * GAMMA_D)
    w("N8 1 + 1/(2*13617/100000) = 63617/13617 and 63617/13617 - 23359/5000 = 5497/68085000 > 0",
      cstar == Fr(63617, 13617) and cstar - DECLARED == Fr(5497, 68085000) > 0)
    bad = [n for n, c in W if not c]
    if verbose:
        for n, c in W: print("      %s %s" % ("PASS" if c else "FAIL", n))
    say("C4 witnesses (N1)-(N8) of cutwidth.md section 7: %d/%d PASS" % (len(W) - len(bad), len(W)))
    return not bad

def ln2_bracket():
    """ln 2 = sum_{k>=1} 1/(k 2^k); the tail after K terms is <= 2^-K/(K+1) * 2"""
    K = 80
    s = sum(Fr(1, k * 2 ** k) for k in range(1, K + 1))
    return s, s + Fr(2, (K + 1) * 2 ** K)

def check_edcert_constants(path=None):
    """(C5): the binary64 constants of edcert.c against pi (Machin) and ln 2 (series); Mills bounds of the Phi tails"""
    import os, re
    path = path or os.path.join(os.path.dirname(os.path.abspath(__file__)), "edcert.c")
    if not os.path.exists(path):
        say("C5 edcert.c constants: %s not found -> FAIL" % path); return False
    src = open(path).read()
    lo_pi, hi_pi = PI_Q
    def pair(name):
        m = re.search(r"static const iv %s = \{ ([0-9.e+-]+), ([0-9.e+-]+) \}" % name, src)
        return Fr(float(m.group(1))), Fr(float(m.group(2)))
    a, b = pair("PI_IV"); ok = a <= lo_pi and hi_pi <= b
    a, b = pair("HALFPI"); ok = ok and 2 * a <= lo_pi and hi_pi <= 2 * b
    a, b = pair("INVS2PI"); ok = ok and a * a * 2 * hi_pi <= 1 <= b * b * 2 * lo_pi
    lits = set(re.findall(r"0\.398942280401432[0-9]*", src))          # every literal near 1/sqrt(2 pi)
    ok = ok and lits == {"0.39894228040143265", "0.39894228040143271"}
    m = re.search(r"#define PI3_UP ([0-9.]+)", src)
    ok = ok and 3 * Fr(float(m.group(1))) > hi_pi
    ok = ok and Fr(float("3.141592653589793")) < lo_pi and "a.hi >= 3.141592653589793" in src   # icos: a double < pi
    l2lo, l2hi = ln2_bracket()
    c1, c2 = Fr(float("1.4426950408889634")), Fr(float("0.6931471805599453"))
    ok = ok and "x * 1.4426950408889634" in src and "k * 0.6931471805599453" in src
    ok = ok and abs(c1 * l2lo - 1) <= Fr(111, 10 ** 18) * l2lo and abs(c1 * l2hi - 1) <= Fr(111, 10 ** 18) * l2hi
    ok = ok and max(abs(c2 - l2lo), abs(c2 - l2hi)) <= Fr(24, 10 ** 18)
    # Mills: Phi(-x) <= phi(x)/x.  phi(9)/9 < 1.2e-19 (Python Phi tail) and phi(7)/7 < 1.39e-12 (edcert.c Phi tail)
    def exp_lower(z, terms=200):      # e^z > partial sum, z > 0
        s, t = Fr(0), Fr(1)
        for k in range(terms):
            s += t; t = t * z / (k + 1)
        return s
    phi9 = 1 / (exp_lower(Fr(81, 2)) * 9)       # * 1/sqrt(2pi) < 1: phi(9)/9 < this * 0.4
    phi7 = 1 / (exp_lower(Fr(49, 2)) * 7)
    ok = ok and phi9 * Fr(2, 5) < Fr(12, 10 ** 20) and phi7 * Fr(2, 5) < Fr(139, 10 ** 14)
    say("C5 edcert.c constants: PI_IV, HALFPI, INVS2PI enclose pi, pi/2, 1/sqrt(2pi); the Phi literals are those two; "
        "PI3_UP > pi/3; icos uses a double < pi; |1.4426950408889634*ln2 - 1| <= 1.11e-16, |0.6931471805599453 - ln2| "
        "<= 2.4e-17; phi(9)/9 < 1.2e-19, phi(7)/7 < 1.39e-12 ->", "ok" if ok else "FAIL")
    return ok

def check_error_budget():
    """(C7): every scalar inequality of the error analysis cutwidth.md (A2)-(A4), (A8), in exact rationals"""
    u = Fr(1, 2 ** 53)
    def E(m, e): return Fr(m) * Fr(10) ** e                  # m * 10^e
    def fact(n):
        r = 1
        for k in range(2, n + 1): r *= k
        return r
    def exp_up(z, terms=80):          # e^z for 0 <= z <= 4: partial sum + tail <= 2 * next term (z/(terms+1) < 1/2)
        s, t = Fr(0), Fr(1)
        for k in range(terms):
            s += t; t = t * z / (k + 1)
        return s + 2 * t
    l2lo, l2hi = ln2_bracket()
    c = []
    # (A2) exp
    c.append(1010 * u + 700 * E(111, -18) < E(191, -15))                     # |y - x/ln2|
    c.append(l2hi * E(191, -15) < E(133, -15) and l2hi * (1 + E(191, -15)) < E(69315, -5))
    c.append(701 * u + 1011 * E(24, -18) + u < E(103, -15))                  # |r~ - r*|
    c.append(E(69315, -5) + E(133, -15) < E(6932, -4))                       # r < 0.6932 (< 0.75)
    c.append((1 + u) ** 66 - 1 < E(74, -16))                                # Horner
    c.append(E(6932, -4) ** 23 * exp_up(E(6932, -4)) / fact(23) < E(21, -27))   # Taylor truncation
    c.append(exp_up(E(133, -15)) <= 1 + E(134, -15))                         # e^{|r - r*|}
    hi = (1 + E(1, -12) - E(112, -18)) * (1 - u) * (1 - E(74, -16)) * (1 - E(21, -27)) * (1 - E(134, -15))
    lo = (1 - E(1, -12) + E(112, -18)) * (1 + u) * (1 + E(74, -16)) * (1 + E(134, -15))
    c.append(hi > 1 + E(85, -14) and lo < 1 - E(85, -14))
    c.append(exp_up(E(8, -13)) <= 1 + E(801, -15) and 1 + E(801, -15) <= 1 + E(85, -14))
    e4lo = sum(Fr(4) ** k / fact(k) for k in range(40))                     # e^4 > partial sum
    c.append(e4lo ** 175 > E(1, 300) * exp_up(E(8, -13)))                  # e^{-700 + 8e-13} < 1e-300
    # (A3) Phi
    c.append(Fr(4901, 100) / 99 < Fr(4951, 10000) and Fr(4951, 10000) ** 56 * (1 + 3 * u) ** 56 < E(1, -17))
    c.append(Fr(99, 2) > Fr(4901, 100))                                      # the first test holds from N = 48 on
    c.append((1 + u) ** 416 - 1 < E(47, -15))
    c.append((1 + u) / (1 - u) <= 1 + 3 * u and (1 + 3 * u) * E(1, -17) * (1 + E(47, -15)) <= E(10001, -21))
    c.append(Fr(49, 2) * u + Fr(1, 2 ** 1076) < E(28, -16) and E(28, -16) < E(8, -13))
    c.append((1 - E(85, -14)) * exp_up(E(28, -16)) <= 1 - E(847, -15))
    c.append((1 + E(85, -14)) * (1 - E(28, -16)) >= 1 + E(847, -15))
    c.append((1 - E(847, -15)) * (1 + E(47, -15)) * (1 - E(1, -12) + E(112, -18)) * (1 + u) ** 3 <= 1 - E(17, -13))
    c.append((1 + E(847, -15)) * (1 - E(47, -15)) * (1 + E(1, -12) - E(112, -18)) * (1 - u) ** 3
             * (1 - E(10001, -21)) >= 1 + E(17, -13))
    c.append(E(17, -13) * Fr(1, 2 ** 1020) > Fr(1, 2 ** 1060))
    d14 = Fr(float("1.4e-12")); hl = Fr(0.5 - float("1.4e-12"))             # Python float ops are IEEE binary64
    c.append(abs(hl - (Fr(1, 2) - d14)) <= Fr(1, 2 ** 55) and hl <= Fr(1, 2) - E(139, -14))
    # (A4) cos
    c.append(Fr(32, 10) ** 50 / fact(50) < E(1, -39))
    e32lo = sum(Fr(32, 10) ** k / fact(k) for k in range(60))              # e^3.2 > partial sum
    c.append((exp_up(Fr(32, 10)) + 1 / e32lo) / 2 < Fr(123, 10))            # cosh 3.2 < 12.3
    c.append((1 + u) ** 72 - 1 < Fr(721, 10) * u and (1 + u) ** 24 - 1 < Fr(241, 10) * u)
    c.append(Fr(123, 10) * (Fr(721, 10) + Fr(241, 10)) * u < E(14, -14))
    c.append(E(1, -12) - E(14, -14) - 2 * u > 0 and E(1, -9) ** 2 / 2 < E(1, -18))
    # (A8) K_lo: x* - xm <= 5e-15 + one ulp below 8 (2^-50) < 1e-14; 1e-14 * 0.4 = 0.4e-14
    c.append(E(5, -15) + Fr(1, 2 ** 50) < E(1, -14))
    ok = all(c)
    say("C7 error budget of (A2)-(A4), (A8): %d exact inequalities ->" % len(c), "ok" if ok else "FAIL %s" % c)
    return ok

# ------------------------------------------------------------------ V
NT = 3548                                   # tau_k = k/2048, 3548/2048 = 1.732421875 > sqrt3
DT = 1.0 / 2048
assert Fr(NT, 2048) ** 2 > 3
_vtab = None
def vtab():
    global _vtab
    if _vtab is None:
        _vtab = []
        for k in range(NT + 1):
            tau = k * DT                    # exact
            q = 9.0 + 8.0 * tau * tau       # exact
            one = 1.0 + tau * tau           # exact
            sq = isqrt(pt(q))
            A = idiv(pt(1.0), imul(pt(one), sq))                       # 1/((1+tau^2) sqrt(9+8tau^2))
            al = idiv(imul(pt(9.0), pt(one)), pt(2.0 * q))             # 9(1+tau^2)/(2(9+8tau^2))
            be = idiv(isub(pt(1.0), imul(KAP, pt(one))), sq)           # (1 - kap(1+tau^2))/sqrt(9+8tau^2)
            c0A = idiv(C0, sq)                                         # c0/sqrt(9+8tau^2)
            _vtab.append((A, al, be, c0A))
    return _vtab
def V_up(a, b):
    """upper bound of V on [a, b]; a, b floats with a >= 0 or b <= 0"""
    T = vtab()
    s = 0.0
    if a >= 0.0:
        a2 = max(0.0, dn(a * a))
        for k in range(NT):
            A, al, be, _ = T[k]
            e = exp_neg(-max(0.0, dn(al[0] * a2)))[1]
            arg = max(imul(be, pt(a))[1], imul(be, pt(b))[1])
            s += up(A[1] * e) * Phi_pt(arg)[1]
        return up(up(up(THREE_OVER_PI[1] * DT) * s) * (1.0 + 1e-9)) + 1e-300
    assert b <= 0.0
    b2 = max(0.0, dn(b * b))
    for k in range(NT):
        A, al, _, _ = T[k]
        e = exp_neg(-max(0.0, dn(al[0] * b2)))[1]
        arg = imul(T[k + 1][3], pt(b))[1]
        s += up(A[1] * e) * Phi_pt(arg)[1]
    integral = up(up(up(THREE_OVER_PI[1] * DT) * s) * (1.0 + 1e-9)) + 1e-300
    ph = up(exp_neg(-b2 * 0.5)[1] * INVS2PI[1])
    diff = up(up(isub(C0, pt(1.0))[1] * (-a)) * ph)
    return up(integral + diff)

def P3_up(b):
    if b <= 0.0: return 0.0
    c1 = imul(isub(idiv(pt(1.0), R1), pt(1.0)), INVS2PI)[1]                # >= (1/r1 - 1) phi(0)
    c2 = imul(pt(18.0), imul(isub(pt(1.0), R1), isub(pt(1.0), R1)))[1]     # >= 18 (1 - r1)^2
    return up(up(c1 * b) * up(1.0 - exp_neg(-up(c2 * up(b * b)))[0]))

# ------------------------------------------------------------------ P2
class P2Grid:
    def __init__(self, h, x0=-3.5, xmax=6.5, ulen=1.0, m=1):
        self.h, self.x0, self.m, self.ulen = h, x0, m, ulen
        hh = pt(h)
        self.s2h = imul(S2, hh)
        self.du = imul(idiv(imul(pt(float(m)), S6), pt(5.0)), hh)
        s3h = imul(S3, hh)
        nx = int((xmax - x0) / (1.7320508 * h)) + 1
        xs = [iadd(pt(x0), imul(pt(float(k)), s3h)) for k in range(nx + 1)]
        P = [Phi_pt(x[0])[0] for x in xs], [Phi_pt(x[1])[1] for x in xs]
        self.wx = [max(0.0, dn(P[0][k + 1] - P[1][k])) for k in range(nx)]
        y0 = imul(S3, pt(x0))
        ny = int((2 * xmax + 2 - 1.7320508 * x0) / h) + 1
        ys = [iadd(y0, imul(pt(float(l)), hh)) for l in range(ny + 1)]
        Q = [Phi_pt(y[0])[0] for y in ys], [Phi_pt(y[1])[1] for y in ys]
        self.wy = [max(0.0, dn(Q[0][l + 1] - Q[1][l])) for l in range(ny)]
        self.nx, self.ny = nx, ny

    def lower(self, a, b):
        """lower bound of P2(a, b) = int_{u >= b} phi(u) K_a(u) du (a <= b floats)"""
        g, m, h = self, self.m, self.h
        base = isub(imul(S12, isub(pt(a), idiv(imul(pt(5.0), pt(b)), pt(6.0)))), imul(LAM, pt(g.x0)))
        nu = 0
        while True:
            e = iadd(pt(b), imul(pt(float(nu + 1)), g.du))
            if e[0] - b >= g.ulen: break
            nu += 1
        es = [iadd(pt(b), imul(pt(float(i)), g.du)) for i in range(nu + 1)]
        cuts = []
        for i in range(1, nu + 1):
            M = imul(pt(3.0), isub(pt(a), imul(R1, es[i])))
            c = idiv(imul(idiv(pt(2.0), S3), isub(M, pt(g.x0))), pt(h))       # c_i
            hi = up(-c[0] - i * m)                                              # >= -c_i - i m
            cuts.append(int(hi // 1) + 1)                                       # J >= cut  =>  J > -c_i - i m
        # the running sum R below keeps every J >= the current cut, so the cuts must not decrease in i (in exact
        # arithmetic -c_i - i m increases by 3m/5 per step; checked here instead of assumed)
        assert all(cuts[i] >= cuts[i - 1] for i in range(1, len(cuts))), "cuts not monotone"
        # H0[J] = H(base + J sqrt2 h), lower bounds, J from Jmin (argument > 0) upwards
        Jmin = int(-base[1] / g.s2h[0] // 1) - 1
        H0 = {}
        def H0f(J):
            v = H0.get(J)
            if v is None:
                arg = iadd(base, imul(pt(float(J)), g.s2h))[0]
                v = H_lo(arg); H0[J] = v
            return v
        nmin, nmax = -1 - nu * m, g.nx
        R = [0.0] * (nmax - nmin + 1)
        wy, wx, ny = g.wy, g.wx, g.ny
        cur, total = nmax + 1, 0.0
        for i in range(nu, 0, -1):
            c = max(cuts[i - 1], Jmin)
            while cur > c:
                cur -= 1
                hv = H0f(cur)
                if hv == 0.0: continue
                lo, hi = max(cur, nmin), min(cur + ny - 1, nmax)
                if lo > hi: continue
                seg = wy[lo - cur:hi - cur + 1]
                o = lo - nmin
                R[o:o + len(seg)] = [r + hv * w for r, w in zip(R[o:o + len(seg)], seg)]
            J = 0.0
            for k in range(g.nx):
                JJ = -2 * (k + 1) - i * m
                if JJ < c: break
                g1 = H0f(JJ)
                if g1 == 0.0: break
                J += wx[k] * g1 * R[k - 1 - i * m - nmin]
            mass = dn(Phi_pt(es[i][0])[0] - Phi_pt(es[i - 1][1])[1])
            if mass > 0.0: total += mass * J
        return max(0.0, total * (1.0 - 1e-9) - 1e-300)

# ------------------------------------------------------------------ cover
def certify(gamma, h, kden=64, maxdepth=7, only=None):
    G = Fr(gamma)
    gam = fr_iv(G)[0]
    grid = P2Grid(h)
    say("P2 lattice: h = %g, %d x-cells, %d y-cells" % (h, grid.nx, grid.ny))
    # tails
    t_lo, t_hi = -1.25, 2.0
    c_lo = Phi_pt(t_lo)[1] <= gam
    c_hi = up(up(7.0 * Phi_pt(-t_hi)[1]) / 2.0) <= gam
    say("tails: t <= %g: G_d <= Phi(%g) <= %.6f; t >= %g: G_d <= (7/2)Phi(-2) <= %.6f -> %s"
        % (t_lo, t_lo, Phi_pt(t_lo)[1], t_hi, up(up(7.0 * Phi_pt(-t_hi)[1]) / 2.0), "ok" if c_lo and c_hi else "FAIL"))
    ok = c_lo and c_hi
    ks = range(int(t_lo * kden), int(t_hi * kden)) if only is None else only
    worst, nV, nP = 0.0, 0, 0
    for k in ks:
        stack = [(k / kden, (k + 1) / kden, 0)]            # exact dyadic ends
        while stack:
            a, b, d = stack.pop()
            U = up(V_up(a, b) + up(P3_up(b) / 2.0)); nV += 1
            if U > gam:
                U = up(U - dn(1.5 * grid.lower(a, b))); nP += 1
            if U <= gam:
                worst = max(worst, U); continue
            if d >= maxdepth:
                say("not certified on [%r, %r]: bound %.8f" % (a, b, U)); return False, worst
            m = 0.5 * (a + b)
            stack += [(m, b, d + 1), (a, m, d + 1)]
        if (k - ks[0]) % 16 == 15 or k == ks[-1]:
            say("base intervals up to t = %.4f done: %d V bounds, %d P2 bounds, largest bound %.8f"
                % ((k + 1) / kden, nV, nP, worst))
    covered = ks[0] / kden == t_lo and (ks[-1] + 1) / kden == t_hi and len(ks) == (t_hi - t_lo) * kden
    return ok and (covered or only is not None), worst

def main():
    args = sys.argv[1:]
    gamma = "0.1366"
    h = 0.0025
    if "--gamma" in args: gamma = args[args.index("--gamma") + 1]
    if "--h" in args: h = float(args[args.index("--h") + 1])
    if "--range" in args:            # a block of base intervals [k/64, (k+1)/64], k0 <= k < k1 (no verdict)
        k0, k1 = (int(x) for x in args[args.index("--range") + 1].split(":"))
        ok = check_f() & check_globsub() & check_wave() & check_witnesses(False) & check_edcert_constants()
        ok = ok & check_error_budget()
        r, w = certify(gamma, h, only=range(k0, k1))
        print("RANGE %d:%d %s largest bound %.8f" % (k0, k1, "OK" if ok and r else "FAILED", w))
        return 0 if ok and r else 1
    say("certify_small.py: pi in [%.17g, %.17g], 1/sqrt(2pi) in [%.17g, %.17g]" % (PI + INVS2PI))
    ok = check_f() & check_globsub() & check_wave() & check_witnesses() & check_edcert_constants()
    ok = ok & check_error_budget()
    if "--quick" in args:
        r, w = certify(gamma, h, only=range(2, 6))
        say("quick: t in [1/32, 3/32] (contains the maximum) certified for gamma = %s: %s, largest bound %.8f"
            % (gamma, r, w))
        print("QUICK", "OK" if ok and r else "FAILED")
        return 0 if ok and r else 1
    r, w = certify(gamma, h)
    ok = ok and r
    say("largest certified bound %.8f" % w)
    print("CERTIFIED gamma <= %s" % gamma if ok else "FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
