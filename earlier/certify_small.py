#!/usr/bin/env python3
"""certify_small.py -- independent pure-Python certificate for cutwidth.md (variant c).  Standard library only.

    python3 certify_small.py                 # full run: CHECKS + sup_t G(t) <= 0.1380   (about 11 s, one core)
    python3 certify_small.py --gamma 0.13760 # a sharper target (about 40 s)
    python3 certify_small.py --quick         # CHECKS + the four base intervals around the maximum (seconds)

It proves, with outward-rounded interval arithmetic and its own enclosures of exp and of the normal cdf Phi
(no math-library function enters any bound; math is not even imported), the following facts used in
cutwidth.md:

 (C1) F (cutwidth.md section 4) on {0,1}^10: every mixed difference of 3F is -1 or 0 (all 45 pairs x 256
      contexts), 3F takes values in [-6, 7], and flipping the centre (resp. any other position) changes 3F by at
      most 7 (resp. 1).  Exhaustive, exact integers.
 (C2) The wave window (cutwidth.md section 5): the explicit construction has covariance w_d = (1 + d/3) 2^(-d/2)
      at tree distance d, d = 0..4, exactly (arithmetic in Q(sqrt2)).
 (C3) sup over all real t of G(t) = V(t) - P2(t) + P3(t)/3 is <= gamma (default 0.1380), with V, P2, P3 the
      wave probabilities of cutwidth.md section 5.  This re-verifies, by a different method and different code,
      a weaker form of the bound 0.1375 that edcert.c certifies (cutwidth.md section 6).
 (C4) every numerical witness (N1)-(N8) of cutwidth.md section 7, as exact rational inequalities.
 (C5) the binary64 constants hard-coded in edcert.c, read from edcert.c in the same directory: the enclosures
      PI_IV, HALFPI, INVS2PI of pi, pi/2, 1/sqrt(2 pi) (pi from Machin's formula) and the two literals for
      1/sqrt(2 pi) in Phi_pt; PI3_UP > pi/3; the literals of exp_pt: |L1 - 1/ln2| < 2.1e-17, |L2 - ln2| <
      2.4e-17 (ln 2 = sum 1/(k 2^k)); EPS_TAIL >= 0.99e-7.  (Python's float() of a decimal literal is correctly
      rounded, as is the C compiler's.)
 (C6) the rational inequalities used in the error analysis of edcert.c (cutwidth.md sections 6.2-6.3: Lemmas
      6.2-6.4, 6.7) and the tail constant of Phi_pt below, as exact rational comparisons.

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
  Tails: t <= -1.25: G <= Phi(-1.25);  t >= 2: G <= (10/3) Phi(-2).

Arithmetic and error bounds (u = 2^-53, every float operation is IEEE binary64 round-to-nearest):
  up(x) = x + (|x| 2^-52 + 2^-1074) evaluated in floating point is >= the next float above x, hence >= any real
      number whose round-to-nearest value is x; dn(x) = -up(-x).  Interval operations apply up/dn to each result.
  exp(z), z <= 0: z = 2^s y with -1/32 <= y <= 0 (exact scaling); P(y) = sum_{n<=12} y^n/n! by Horner.  The
      Horner error is <= 1.2u (each step adds <= 1.15u and damps the previous error by |y|/n <= 1/32) and the
      Taylor remainder is <= |y|^13/13! < 1e-29, so |P - e^y| <= 1e-15 P; then s interval squarings.
  Phi(x), |x| <= 9: Phi(|x|) = 1/2 + phi(x) S(|x|), S(x) = sum_n x^(2n+1)/(2n+1)!! (positive terms; S' = 1 + xS);
      the loop stops at n = N once x^2/(2N+3) <= 1/2 and the last term T_N <= 1e-17 S, so the omitted tail is
      <= T_N; each computed term and the sum carry a relative error <= 4.1 (N+1) u (<= 5 (N+2) u is used).
      |x| > 9: 1 - Phi(|x|) <= 1 - Phi(9) <= phi(9)/9 < 1.2e-19 (Mills; C6).  |x| < 1e-150: |Phi(x) - 1/2| <=
      0.4 |x|.  (With the default grids every argument of Phi_pt is > -6.1, so the branch x < -9 is not reached.)
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
    if ax > 9.0: return (0.9999999999999998, 1.0) if x > 0 else (0.0, 1.2e-19)
    if ax < 1e-150: return (dn(0.5 - 0.4 * ax), up(0.5 + 0.4 * ax))
    lo, hi = halfphi_part(ax)
    if x >= 0: return (dn(0.5 + lo), min(1.0, up(0.5 + hi)))
    return (max(0.0, dn(0.5 - hi)), up(0.5 - lo))
def H_lo(z):
    """lower bound of H(z) = (2 Phi(z) - 1)^+ for a float z"""
    if z <= 1e-150: return 0.0
    if z > 9.0: return 0.9999999999999998
    return dn(2.0 * halfphi_part(z)[0])

# ------------------------------------------------------------------ (C1), (C2)
def check_F():
    # positions: 0 = v, 1..3 = z_i, children of z_i: 2i+2, 2i+3
    def F3(s):
        k = sum(s[i] * s[2 * i + 2] * s[2 * i + 3] for i in (1, 2, 3))
        return sum(s[1:]) - 6 * s[0] - (s[0] * k + (1 - s[0]) * max(k - 1, 0))
    vals = {s: F3(s) for s in itertools.product((0, 1), repeat=10)}
    md = set()
    for p, q in itertools.combinations(range(10), 2):
        for s in vals:
            if s[p] == 0 and s[q] == 0:
                s11 = list(s); s11[p] = s11[q] = 1
                s10 = list(s); s10[p] = 1
                s01 = list(s); s01[q] = 1
                md.add(vals[tuple(s11)] - vals[tuple(s10)] - vals[tuple(s01)] + vals[s])
    rng = (min(vals.values()), max(vals.values()))
    flip = [max(abs(vals[s] - vals[s[:x] + (1 - s[x],) + s[x + 1:]]) for s in vals) for x in range(10)]
    ok = md <= {-1, 0} and rng == (-6, 7) and flip == [7] + [1] * 9
    say("C1 F: mixed differences of 3F %s, range of 3F %s, flip sizes %s -> %s"
        % (sorted(md), rng, flip, "ok" if ok else "FAIL"))
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
def check_witnesses(verbose=True):
    """(N1)-(N8) of cutwidth.md section 7, exact"""
    lo_pi, hi_pi = PI_Q
    D = Fr
    W = []
    def w(name, cond): W.append((name, bool(cond)))
    w("N1 1.41421^2 < 2 < 1.41422^2", D("1.41421") ** 2 < 2 < D("1.41422") ** 2)
    w("N1 3.3166^2 < 11, 9.7467^2 < 95", D("3.3166") ** 2 < 11 and D("9.7467") ** 2 < 95)
    w("N1 3.14159 < pi < 3.1416", D("3.14159") < lo_pi and hi_pi < D("3.1416"))
    s = 9 * D("1.41422") / 2 + 48 / D("3.3166") + 19 + 216 / D("9.7467")
    w("N2 9*1.41422/2 + 48/3.3166 + 19 + 216/9.7467 < 61.998", s < D("61.998"))
    w("N2 3.1416*61.998/3 < 64.93", D("3.1416") * D("61.998") / 3 < D("64.93"))
    w("N2 eps^2 term: 45*(1/3)*1.41422/3.14159 < 8", 45 * Fr(1, 3) * D("1.41422") / D("3.14159") < 8)
    w("N3 48*169/36 = 676/3", Fr(48 * 169, 36) == Fr(676, 3))
    w("N3 4*676/3 < 30.03^2", Fr(4 * 676, 3) < D("30.03") ** 2)
    w("N3 3 < 1.7321^2", 3 < D("1.7321") ** 2)
    w("N3 30.03 + (16/3)*1.7321 < 39.27", D("30.03") + Fr(16, 3) * D("1.7321") < D("39.27"))
    w("N3 (12 - 16/3)^2 * 3 = 400/3 < 4*676/3", (12 - Fr(16, 3)) ** 2 * 3 == Fr(400, 3) < Fr(4 * 676, 3))
    w("N3 39.27*1.41422/2 < 27.77", D("39.27") * D("1.41422") / 2 < D("27.77"))
    w("N4 32^2 < 12.77^2 * 2 * 3.14159", 32 ** 2 < D("12.77") ** 2 * 2 * D("3.14159"))
    w("N4 27.77 + 12.77 + 0.46 <= 41 and 30 < 0.46*2^35", D("27.77") + D("12.77") + D("0.46") <= 41
      and 30 < D("0.46") * 2 ** 35)
    w("N5 64.93*9 = 584.37 < 585", D("64.93") * 9 < 585)
    fact, e45 = 1, Fr(0)
    for k in range(30):
        if k: fact *= k
        e45 += Fr(9, 2) ** k / fact               # partial sum < e^(9/2)
    w("N6 e^4.5 > 90 (partial sum of the exponential series)", e45 > 90)
    w("N6 4/(90*2.5066) < 0.0178 and 2.5066^2 < 2*3.14159", Fr(4) / (90 * D("2.5066")) < D("0.0178")
      and D("2.5066") ** 2 < 2 * D("3.14159"))
    w("N7 2^40 < 22^9 and 41/22 > 109/80", Fr(2) ** 40 < Fr(22) ** 9 and Fr(41, 22) > Fr(109, 80))
    w("N8 1 + 1/(2*11/80) = 51/11 and 51/11 - 1159/250 = 1/2750", 1 + 1 / (2 * Fr(11, 80)) == Fr(51, 11)
      and Fr(51, 11) - Fr(1159, 250) == Fr(1, 2750))
    bad = [n for n, c in W if not c]
    if verbose:
        for n, c in W: print("      %s %s" % ("PASS" if c else "FAIL", n))
    say("C4 witnesses (N1)-(N8) of cutwidth.md section 7: %d/%d PASS" % (len(W) - len(bad), len(W)))
    return not bad

def check_edcert_constants(path=None):
    """(C5): the binary64 constants of edcert.c against pi from Machin's formula"""
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
    m = re.search(r"#define PI3_UP ([0-9.]+)", src)
    ok = ok and 3 * Fr(float(m.group(1))) > hi_pi
    # the two literals for 1/sqrt(2 pi) inside Phi_pt (lower and upper)
    a = Fr(float(re.search(r"el \* S \* ([0-9.]+)", src).group(1)))
    b = Fr(float(re.search(r"eh \* S \* ([0-9.]+)", src).group(1)))
    ok = ok and a * a * 2 * hi_pi <= 1 <= b * b * 2 * lo_pi
    # the literals L1 ~ 1/ln2 and L2 ~ ln2 of exp_pt; ln 2 = sum_k 1/(k 2^k), tail after k = 79 <= 1/(80 2^79)
    ln2_lo = sum(Fr(1, k * 2 ** k) for k in range(1, 80))
    ln2_hi = ln2_lo + Fr(1, 80 * 2 ** 79)
    L1 = Fr(float(re.search(r"floor\(x \* ([0-9.]+)\)", src).group(1)))
    L2 = Fr(float(re.search(r"r = x - k \* ([0-9.]+);", src).group(1)))
    ok = ok and max(abs(L1 - 1 / ln2_lo), abs(L1 - 1 / ln2_hi)) < Fr(21, 10 ** 18)
    ok = ok and max(abs(L2 - ln2_lo), abs(L2 - ln2_hi)) < Fr(24, 10 ** 18)
    m = re.search(r"#define EPS_TAIL ([0-9.e-]+)", src)
    ok = ok and Fr(float(m.group(1))) >= Fr(99, 10 ** 9)
    say("C5 edcert.c constants: PI_IV, HALFPI, INVS2PI and the Phi_pt literals enclose pi, pi/2, 1/sqrt(2pi); "
        "PI3_UP > pi/3; exp_pt literals within 2.1e-17 of 1/ln2 and 2.4e-17 of ln2; EPS_TAIL >= 0.99e-7 ->",
        "ok" if ok else "FAIL")
    return ok

def check_numerics(verbose=True):
    """(C6): the rational inequalities of cutwidth.md sections 6.2-6.3 (error analysis of edcert.c), exact"""
    lo_pi = PI_Q[0]
    u = Fr(1, 2 ** 53)
    D = Fr
    W = []
    def w(name, cond): W.append((name, bool(cond)))
    def exp_sum(x, n):              # partial sum of the exponential series and its last term (x >= 0)
        s, t = Fr(0), Fr(1)
        for k in range(n):
            s += t; t = t * x / (k + 1)
        return s, t                 # e^x >= s;  e^x <= s + t/(1 - x/(n+1)) if x < n + 1
    def exp_lo(x, n=200): return exp_sum(Fr(x), n)[0]
    def exp_hi(x, n=200):
        s, t = exp_sum(Fr(x), n)
        return s + t / (1 - Fr(x) / (n + 1))
    def fact(n):
        p = 1
        for j in range(2, n + 1): p *= j
        return p
    def dfact(n):
        p = 1
        for j in range(1, n + 1, 2): p *= j
        return p
    s2pi = D("2.5066")                                    # sqrt(2 pi) > 2.5066
    w("sqrt(2 pi) > 2.5066", s2pi ** 2 < 2 * lo_pi)
    # Lemma 6.2 (exp_pt)
    w("6.2 e > 2.718 and 2.718^699 > 10^303, so e^-699 < 10^-303", exp_lo(1, 30) > D("2.718")
      and D("2.718") ** 699 > 10 ** 303)
    w("6.2 1010 (1.46e-17 + u)(1 + u) < 1.27e-13 and ln2 * 1.27e-13 < 8.9e-14",
      1010 * (D("1.46e-17") + u) * (1 + u) < D("1.27e-13") and D("0.6932") * D("1.27e-13") < D("8.9e-14"))
    ln2_hi = sum(Fr(1, k * 2 ** k) for k in range(1, 80)) + Fr(1, 80 * 2 ** 79)
    w("6.2 ln 2 < 0.6932 and 0.6932 * 2.1e-17 < 1.46e-17 (relative error of L1)", ln2_hi < D("0.6932")
      and D("0.6932") * D("2.1e-17") < D("1.46e-17"))
    w("6.2 2^-44 + 1010 * 2.4e-17 + u < 8.2e-14", Fr(1, 2 ** 44) + 1010 * D("2.4e-17") + u < D("8.2e-14"))
    w("6.2 ln2 + 1e-13 + 8.2e-14 < 0.6934", D("0.6932") + D("1e-13") + D("8.2e-14") < D("0.6934"))
    w("6.2 e^0.6934 < 2.001", exp_hi(D("0.6934"), 40) < D("2.001"))
    w("6.2 Horner: 0.6934 ((1+u)^2 2e-15 + 2.0001 u 2.001) + 2.002 u + 3*2^-1075 < 2e-15",
      D("0.6934") * ((1 + u) ** 2 * D("2e-15") + D("2.0001") * u * D("2.001")) + D("2.002") * u
      + 3 * Fr(1, 2 ** 1075) < D("2e-15") and (1 + u) ** 2 - 1 < D("2.0001") * u)
    w("6.2 Taylor remainder 0.6934^23/23! * 24/(24 - 0.6934) < 1e-26",
      D("0.6934") ** 23 / fact(23) * 24 / (24 - D("0.6934")) < D("1e-26"))
    w("6.2 8.9e-14 + 2e-15 + 1e-26 + 1e-27 < 9.2e-14", D("8.9e-14") + D("2e-15") + D("1e-26") + D("1e-27") < D("9.2e-14"))
    e1, e2, e3 = D("9.2e-14"), D("1e-12"), D("1.2e-16")
    w("6.2 (1+9.2e-14)(1-1e-12+1.2e-16)(1+u) < 1 - 0.9e-12 < 1 + 0.9e-12 < (1-9.2e-14)(1+1e-12-1.2e-16)(1-u)",
      (1 + e1) * (1 - e2 + e3) * (1 + u) < 1 - D("0.9e-12") and (1 - e1) * (1 + e2 - e3) * (1 - u) > 1 + D("0.9e-12"))
    w("6.2 (1-9.2e-14)(1-1e-12-1.2e-16)(1-u) > 1 - 1.1e-12 and (1+9.2e-14)(1+1e-12+1.2e-16)(1+u) < 1 + 1.1e-12",
      (1 - e1) * (1 - e2 - e3) * (1 - u) > 1 - D("1.1e-12") and (1 + e1) * (1 + e2 + e3) * (1 + u) < 1 + D("1.1e-12"))
    w("6.2 e^(8e-13) - 1 < 0.9e-12", exp_hi(D("8e-13"), 6) - 1 < D("0.9e-12"))
    # Lemma 6.3 (Phi_pt)
    w("6.3 e^24.5 > 4.3e10, so phi(7)/7 < 1/(7 * 2.5066 * 4.3e10) < 1.33e-12 < 1.4e-12 - 1e-16",
      exp_lo(D("24.5")) > D("4.3e10") and 1 / (7 * s2pi * D("4.3e10")) < D("1.33e-12") < D("1.4e-12") - D("1e-16"))
    w("6.3 31!! > 1.9e17 (y < 1: N <= 15) and 211!! < 1e201 (y >= 1: terms > 1e-201)",
      dfact(31) > D("1.9e17") and dfact(211) < 10 ** 201)
    w("6.3 2^-57 < 1e-17 (1 - 1e-13)", Fr(1, 2 ** 57) < D("1e-17") * (1 - D("1e-13")))
    w("6.3 (1+u)^420 - 1 < 4.7e-14 and 24.5 u < 8e-13", (1 + u) ** 420 - 1 < D("4.7e-14") and D("24.5") * u < D("8e-13"))
    e1 = D("4.8e-14")
    w("6.3 (1-4.8e-14)(1+1e-12-1.2e-16)(1-u)^3 > 1 > (1+4.8e-14)(1-1e-12+1.2e-16)(1+u)^3",
      (1 - e1) * (1 + e2 - e3) * (1 - u) ** 3 > 1 > (1 + e1) * (1 - e2 + e3) * (1 + u) ** 3)
    # Lemma 6.4 (cosval)
    w("6.4 e^3.2 < 24.6 and 3.2^50/50! < 1e-39", exp_hi(D("3.2"), 60) < D("24.6") and D("3.2") ** 50 / fact(50) < D("1e-39"))
    w("6.4 (1+u)^72 - 1 < 73u and (73*24.6 + 24*24.61) u + 1e-300 < 2.7e-13 < 1e-12 - 3u",
      (1 + u) ** 72 - 1 < 73 * u and (73 * D("24.6") + 24 * D("24.61")) * u + D("1e-300") < D("2.7e-13")
      < D("1e-12") - 3 * u)
    # Lemma 6.7 (K_lo): the omitted pieces of the Hermite integrals
    w("6.7 e^32 > 7.8e13, so phi(8)/8 < 1/(8 * 2.5066 * 7.8e13) < 6.4e-16", exp_lo(32) > D("7.8e13")
      and 1 / (8 * s2pi * D("7.8e13")) < D("6.4e-16"))
    w("6.7 6e-15 phi(0) < 0.4e-14; 2.53^2 > 6.4, 6.33^2 > 40, 2.53e-8 + 6.33e-8 < 0.99e-7",
      D("6e-15") / s2pi < D("0.4e-14") and D("2.53") ** 2 > D("6.4") and D("6.33") ** 2 > 40
      and D("2.53e-8") + D("6.33e-8") < D("0.99e-7"))
    w("6.7 5e-15 (1 + 2u) + 2^-50 < 6e-15", D("5e-15") * (1 + 2 * u) + Fr(1, 2 ** 50) < D("6e-15"))
    # this file: Phi_pt for x < -9
    w("Phi_pt here: e^40.5 > 3.8e17, so phi(9)/9 < 1/(9 * 2.5066 * 3.8e17) < 1.2e-19",
      exp_lo(D("40.5")) > D("3.8e17") and 1 / (9 * s2pi * D("3.8e17")) < D("1.2e-19"))
    bad = [n for n, c in W if not c]
    if verbose:
        for n, c in W: print("      %s %s" % ("PASS" if c else "FAIL", n))
    say("C6 rational inequalities of cutwidth.md sections 6.2-6.3: %d/%d PASS" % (len(W) - len(bad), len(W)))
    return not bad

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
    c_hi = up(up(10.0 * Phi_pt(-t_hi)[1]) / 3.0) <= gam
    say("tails: t <= %g: G <= Phi(%g) <= %.6f; t >= %g: G <= (10/3)Phi(-2) <= %.6f -> %s"
        % (t_lo, t_lo, Phi_pt(t_lo)[1], t_hi, up(up(10.0 * Phi_pt(-t_hi)[1]) / 3.0), "ok" if c_lo and c_hi else "FAIL"))
    ok = c_lo and c_hi
    ks = range(int(t_lo * kden), int(t_hi * kden)) if only is None else only
    worst, nV, nP = 0.0, 0, 0
    for k in ks:
        stack = [(k / kden, (k + 1) / kden, 0)]            # exact dyadic ends
        while stack:
            a, b, d = stack.pop()
            U = up(V_up(a, b) + up(P3_up(b) / 3.0)); nV += 1
            if U > gam:
                U = up(U - grid.lower(a, b)); nP += 1
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
    gamma = "0.1380"
    h = 0.0025
    if "--gamma" in args: gamma = args[args.index("--gamma") + 1]
    if "--h" in args: h = float(args[args.index("--h") + 1])
    if "--range" in args:            # a block of base intervals [k/64, (k+1)/64], k0 <= k < k1 (no verdict)
        k0, k1 = (int(x) for x in args[args.index("--range") + 1].split(":"))
        ok = check_F() & check_wave() & check_witnesses(False) & check_edcert_constants() & check_numerics(False)
        r, w = certify(gamma, h, only=range(k0, k1))
        print("RANGE %d:%d %s largest bound %.8f" % (k0, k1, "OK" if ok and r else "FAILED", w))
        return 0 if ok and r else 1
    say("certify_small.py: pi in [%.17g, %.17g], 1/sqrt(2pi) in [%.17g, %.17g]" % (PI + INVS2PI))
    ok = check_F() & check_wave() & check_witnesses() & check_edcert_constants() & check_numerics()
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
