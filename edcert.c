/* edcert.c -- the certificate of Proposition C of cutwidth.md (section 6): for every real t,
 *     V(t) - W(t)/2 = V(t) - (3/2) P2(t) + P3(t)/2 <= gamma = G/10^8
 * for the Gaussian wave on the 3-regular tree (covariance (1 + d/3) 2^{-d/2} at tree distance d).  Self-contained:
 * the mathematics is in cutwidth.md sections 5-6; every enclosure used here is derived in cutwidth.md section 6.2,
 * items (A0)-(A10), which the comments below cite by number.  No other file is needed.
 *
 *   on [-1.125, 2]:  V(t) - (3/2) P2(t) + P3up(t)/2 <= gamma, by bisection of dyadic slabs (cutwidth.md 6.1);
 *   tails (`check`): t <= -1.125: V - W/2 <= V <= Phi(t) <= Phi(-1.125);  t >= 2: V - W/2 <= V + P3/2 <=
 *   (7/2) Phi(-t) <= (7/2) Phi(-2), with the TRUE P3 (P3 <= Phi(-t)); the majorant P3up is used only on [-1.125, 2].
 *
 * Exact endpoints.  Base slabs are [k/1024, (k+1)/1024] for -1152 <= k < 2048 (exact doubles; -1152/1024 =
 * -1.125, 2048/1024 = 2); bisection midpoints of dyadic numbers are exact; the four V sub-slabs and all panel
 * ends are doubles shared by neighbouring pieces, so the pieces cover their parent exactly.  gamma is the
 * rational G/10^8; a leaf is accepted only if its upper bound is <= the lower end of a rigorous enclosure of
 * G/10^8.  The constants 0.02434, 0.0589 (P3up), 1e-7 (EPS_TAIL) and 1.4e-12 (Phi tail) denote the binary64
 * numbers nearest to these decimals; every inequality they must satisfy is checked by `check` on those binary64
 * values.  PI3_UP is a double > pi/3 (checked).  A FAIL line means "not certified", never "false".
 *
 * Wave quantities (cutwidth.md 5.2-5.5), r1 = 2 sqrt2/3:
 *   V(t)  = (3/pi) int_0^{pi/3} A e^{-alpha t^2} Phi(beta t) dpsi                           (t >= 0)
 *         = Phi(t) - Phi(c0 t) + (3/pi) int_0^{pi/3} A e^{-alpha t^2} Phi(c0 A t) dpsi       (t <= 0)
 *           c = cos psi, A = c/sqrt(c^2+8), alpha = 9/(2(c^2+8)), beta = (c^2-(6 sqrt2-8))/(c sqrt(c^2+8)),
 *           c0 = 3/(2 sqrt2).
 *   P2(t) >= P2(a,b) := int_{u >= b} phi(u) K_a(u) du  for t in [a,b];  K_a(u) = E[G(x1) G(x2)], (x1,x2) standard
 *           normal with correlation -1/2, G(x) = 1{x < M} (2 Phi(kappa - lambda x) - 1)^+, M = 3(a - r1 u),
 *           kappa = sqrt12 (a - 5u/6), lambda = 2 sqrt6/3; K_a is nonincreasing in u (lower Riemann sum);
 *           Mehler: K = sum_n rho^n I_n^2, I_n = int phi hhat_n G, rho = -1/2, |sum_{n>N} rho^n I_n^2| <= 2^{-(N+1)} I_0.
 *   P3(t) <= P3up(t) = 0.02434 t (1 - exp(-0.0589 t^2)) for t > 0;  P3 = 0 for t <= 0.
 *
 * Arithmetic (cutwidth.md (A0)-(A6)): intervals with binary64 ends; every interval operation is one IEEE operation
 * followed by one ulp outward (A1); exp, Phi, cos by series with the a-priori error bounds proved in (A2)-(A4);
 * degree-4 Taylor arithmetic with interval coefficients (A5); Simpson rule with the remainder -h^5/2880 f''''(xi)
 * enclosed on the panel (A6).  No libm call enters an enclosure except sqrt (correctly rounded), floor and ldexp
 * (exact).  Requirements, all checked: binary64 evaluation without extra precision (FLT_EVAL_METHOD == 0,
 * DBL_MANT_DIG == 53; compile time), rounding mode round-to-nearest (fegetround; run time, in `check`, `slab`,
 * `full`), no contraction into fused operations (compile with -ffp-contract=off).
 * Compile: gcc -O2 -std=c11 -ffp-contract=off -fno-fast-math -o edcert edcert.c -lm
 *
 * Usage:
 *   edcert selftest                   float sanity values (not a proof step)
 *   edcert V a b                      upper bound of V on [a,b]   (a,b on the same side of 0)
 *   edcert P2 a b [du0 growth P]      lower bound of P2(a,b)
 *   edcert check G                    side conditions (tails, constants, rounding mode) for gamma = G/10^8
 *   edcert slab G kden k0 k1 [du0 growth P]
 *        certifies the base slabs [k/kden,(k+1)/kden], k0 <= k < k1, by adaptive bisection; one line per slab;
 *        exit code 0 iff every slab is OK.
 *   edcert full G [du0 growth P]
 *        side conditions + all 3200 base slabs of [-1.125, 2] with kden = 1024 (one thread), cover check, last
 *        line "RESULT: CERTIFIED for gamma = G/10^8" (exit 0) or "RESULT: NOT certified ..." (exit 1).
 *   edcert globsub
 *        exhaustive global-submodularity check (cutwidth.md Lemma 4.4); last line "globsub: OK" (exit 0) or FAIL.
 *   Exit code 4 with "INTERNAL ERROR": two enclosures of one number were disjoint (a bug); nothing is certified.
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <float.h>
#include <fenv.h>

#if !defined(FLT_EVAL_METHOD) || FLT_EVAL_METHOD != 0 || DBL_MANT_DIG != 53
#error "binary64 evaluation without extra precision is required (cutwidth.md (A0))"
#endif

#define DEG 4

typedef struct { double lo, hi; } iv;
static int g_fail;   /* set when an interval operation is undefined (division by an interval containing 0, ...) */
static int g_deg;    /* current Taylor degree: 0 (point/range evaluation) or DEG */

static inline double up(double x) {
    if (!(x == x) || x == INFINITY) return x;
    if (x == 0.0) return 4.9406564584124654e-324;
    uint64_t b; memcpy(&b, &x, 8);
    if (x > 0) b++; else b--;
    memcpy(&x, &b, 8); return x;
}
static inline double dn(double x) { return -up(-x); }
static inline iv mk(double lo, double hi) { iv r; r.lo = lo; r.hi = hi; return r; }
static inline iv pt(double x) { return mk(x, x); }
static inline iv iadd(iv a, iv b) { return mk(dn(a.lo + b.lo), up(a.hi + b.hi)); }
static inline iv isub(iv a, iv b) { return mk(dn(a.lo - b.hi), up(a.hi - b.lo)); }
static inline iv ineg(iv a) { return mk(-a.hi, -a.lo); }
static inline iv imul(iv a, iv b) {
    double p1 = a.lo * b.lo, p2 = a.lo * b.hi, p3 = a.hi * b.lo, p4 = a.hi * b.hi;
    double lo = p1, hi = p1;
    if (p2 < lo) lo = p2; if (p2 > hi) hi = p2;
    if (p3 < lo) lo = p3; if (p3 > hi) hi = p3;
    if (p4 < lo) lo = p4; if (p4 > hi) hi = p4;
    if (!(lo == lo) || !(hi == hi)) { g_fail = 1; return mk(-INFINITY, INFINITY); }
    return mk(dn(lo), up(hi));
}
static inline iv idiv(iv a, iv b) {
    if (!(b.lo > 0.0) && !(b.hi < 0.0)) { g_fail = 1; return mk(-INFINITY, INFINITY); }
    double p1 = a.lo / b.lo, p2 = a.lo / b.hi, p3 = a.hi / b.lo, p4 = a.hi / b.hi;
    double lo = p1, hi = p1;
    if (p2 < lo) lo = p2; if (p2 > hi) hi = p2;
    if (p3 < lo) lo = p3; if (p3 > hi) hi = p3;
    if (p4 < lo) lo = p4; if (p4 > hi) hi = p4;
    if (!(lo == lo) || !(hi == hi)) { g_fail = 1; return mk(-INFINITY, INFINITY); }
    return mk(dn(lo), up(hi));
}
static inline iv isqrt_pos(iv a) {      /* requires a > 0 */
    if (!(a.lo > 0.0)) { g_fail = 1; return mk(0.0, INFINITY); }
    return mk(dn(sqrt(a.lo)), up(sqrt(a.hi)));
}
static inline iv isqr(iv a) {          /* a^2, tight when a contains 0 */
    double l = a.lo * a.lo, h = a.hi * a.hi;
    if (a.lo <= 0.0 && a.hi >= 0.0) return mk(0.0, up(l > h ? l : h));
    return mk(dn(l < h ? l : h), up(l > h ? l : h));
}
static void contradiction(void) {        /* two enclosures of one number are disjoint: a bug, never a bound */
    fflush(stdout);
    printf("INTERNAL ERROR: disjoint enclosures of the same number; nothing is certified\n");
    fflush(stdout);
    exit(4);
}
static inline iv iint(iv a, iv b) {     /* intersection of two enclosures of the same number */
    iv r = mk(a.lo > b.lo ? a.lo : b.lo, a.hi < b.hi ? a.hi : b.hi);
    if (r.lo > r.hi) contradiction();
    return r;
}

/* ---- elementary functions with a-priori error bounds: exp (A2), Phi (A3), cos (A4) of cutwidth.md 6.2 ---- */

/* exp(x) for x <= 700: outward enclosure with the one-sided margins proved in cutwidth.md 6.2 (A2) */
static void exp_pt(double x, double *lo, double *hi) {
    if (!(x <= 700.0)) { g_fail = 1; *lo = 0.0; *hi = INFINITY; return; }
    if (x < -700.0) { *lo = 0.0; *hi = 1e-300; return; }
    double k = floor(x * 1.4426950408889634);
    double r = x - k * 0.6931471805599453;
    if (r < 0.0) r = 0.0;
    if (r > 0.75) { g_fail = 1; *lo = 0.0; *hi = INFINITY; return; }
    double s = 1.0;
    for (int n = 22; n >= 1; n--) s = 1.0 + (r / n) * s;
    *lo = ldexp(s * (1.0 - 1e-12), (int)k);
    *hi = ldexp(s * (1.0 + 1e-12), (int)k);
}
static inline iv iexp(iv a) {
    double l1, h1, l2, h2;
    exp_pt(a.lo, &l1, &h1);
    if (a.hi == a.lo) return mk(l1, h1);
    exp_pt(a.hi, &l2, &h2);
    return mk(l1, h2);
}
/* Phi(x): absolute error of the returned bounds < 2e-12 */
static void Phi_pt(double x, double *lo, double *hi) {
    double ax = fabs(x), Hlo, Hhi;       /* H = Phi(|x|) - 1/2 */
    if (!(ax == ax)) { g_fail = 1; *lo = 0.0; *hi = 1.0; return; }
    if (ax > 7.0) { Hlo = 0.5 - 1.4e-12; Hhi = 0.5; }
    else {
        double x2 = ax * ax, term = ax, S = ax;
        int n = 0;
        for (;;) {
            term = term * x2 / (2 * n + 3); n++; S += term;
            if (x2 < 0.5 * (2 * n + 3) && term <= 1e-17 * S) break;
            if (n > 2000) { g_fail = 1; break; }
        }
        double el, eh;
        exp_pt(-0.5 * x2, &el, &eh);
        Hlo = el * S * 0.39894228040143265 * (1.0 - 1e-12);
        Hhi = eh * S * 0.39894228040143271 * (1.0 + 1e-12);
        if (Hhi > 0.5) Hhi = 0.5;
        if (Hlo > 0.5) Hlo = 0.5;
    }
    if (x >= 0) { *lo = dn(0.5 + Hlo); *hi = up(0.5 + Hhi); }
    else { *lo = dn(0.5 - Hhi); *hi = up(0.5 - Hlo); }
    if (*lo < 0.0) *lo = 0.0;
    if (*hi > 1.0) *hi = 1.0;
}
static inline iv iPhi(iv a) {
    double l1, h1, l2, h2;
    Phi_pt(a.lo, &l1, &h1);
    if (a.hi == a.lo) return mk(l1, h1);
    Phi_pt(a.hi, &l2, &h2);
    return mk(l1, h2);
}
/* cos(x) for 0 <= x <= 3.2: absolute error < 1e-12 */
static double cosval(double x) {
    double x2 = x * x, term = 1.0, S = 1.0;
    for (int n = 0; n < 24; n++) { term = -term * x2 / ((2 * n + 1) * (2 * n + 2)); S += term; }
    return S;
}
/* enclosure of cos over (a intersect [0,pi]); requires a within [-1e-9, 3.2] */
static iv icos(iv a) {
    if (!(a.lo >= -1e-9) || !(a.hi <= 3.2)) { g_fail = 1; return mk(-1.0, 1.0); }
    double lo = cosval(a.hi) - 1e-12, hi = cosval(a.lo < 0 ? 0.0 : a.lo) + 1e-12;
    if (lo < -1.0 || a.hi >= 3.141592653589793) lo = -1.0;   /* the interval may reach pi */
    if (hi > 1.0) hi = 1.0;
    return mk(lo, hi);
}
static const iv PI_IV = { 3.141592653589793, 3.1415926535897936 };
static const iv INVS2PI = { 0.39894228040143265, 0.39894228040143271 };

/* ---- Taylor arithmetic with interval coefficients ---- */
typedef struct { iv c[DEG + 1]; } ts;
static ts ts_const(iv a) { ts r; r.c[0] = a; for (int k = 1; k <= DEG; k++) r.c[k] = pt(0.0); return r; }
static ts ts_var(iv x0) { ts r = ts_const(x0); r.c[1] = pt(1.0); return r; }
static ts ts_add(ts a, ts b) { ts r; for (int k = 0; k <= DEG; k++) r.c[k] = k <= g_deg ? iadd(a.c[k], b.c[k]) : pt(0.0); return r; }
static ts ts_sub(ts a, ts b) { ts r; for (int k = 0; k <= DEG; k++) r.c[k] = k <= g_deg ? isub(a.c[k], b.c[k]) : pt(0.0); return r; }
static ts ts_scale(ts a, iv s) { ts r; for (int k = 0; k <= DEG; k++) r.c[k] = k <= g_deg ? imul(a.c[k], s) : pt(0.0); return r; }
static ts ts_mul(ts a, ts b) {
    ts r;
    for (int k = 0; k <= DEG; k++) {
        if (k > g_deg) { r.c[k] = pt(0.0); continue; }
        iv s = imul(a.c[0], b.c[k]);
        for (int j = 1; j <= k; j++) s = iadd(s, imul(a.c[j], b.c[k - j]));
        r.c[k] = s;
    }
    return r;
}
static ts ts_div(ts a, ts b) {
    ts q;
    for (int k = 0; k <= DEG; k++) {
        if (k > g_deg) { q.c[k] = pt(0.0); continue; }
        iv s = a.c[k];
        for (int j = 1; j <= k; j++) s = isub(s, imul(b.c[j], q.c[k - j]));
        q.c[k] = idiv(s, b.c[0]);
    }
    return q;
}
static ts ts_sqrt(ts a) {
    ts s;
    s.c[0] = isqrt_pos(a.c[0]);
    iv two_s0 = imul(pt(2.0), s.c[0]);
    for (int k = 1; k <= DEG; k++) {
        if (k > g_deg) { s.c[k] = pt(0.0); continue; }
        iv v = a.c[k];
        for (int j = 1; j <= k - 1; j++) v = isub(v, imul(s.c[j], s.c[k - j]));
        s.c[k] = idiv(v, two_s0);
    }
    return s;
}
static ts ts_exp(ts a) {
    ts e;
    e.c[0] = iexp(a.c[0]);
    for (int k = 1; k <= DEG; k++) {
        if (k > g_deg) { e.c[k] = pt(0.0); continue; }
        iv v = pt(0.0);
        for (int j = 1; j <= k; j++) v = iadd(v, imul(imul(pt((double)j), a.c[j]), e.c[k - j]));
        e.c[k] = idiv(v, pt((double)k));
    }
    return e;
}
/* Phi(u(x)): derivative phi(u) u' */
static ts ts_Phi(ts u) {
    ts F;
    F.c[0] = iPhi(u.c[0]);
    if (g_deg == 0) { for (int k = 1; k <= DEG; k++) F.c[k] = pt(0.0); return F; }
    ts p = ts_scale(ts_exp(ts_scale(ts_mul(u, u), pt(-0.5))), INVS2PI);
    for (int k = 1; k <= DEG; k++) {
        iv v = pt(0.0);
        for (int j = 1; j <= k; j++) v = iadd(v, imul(imul(pt((double)j), u.c[j]), p.c[k - j]));
        F.c[k] = idiv(v, pt((double)k));
    }
    return F;
}

typedef ts (*integrand)(const void *, ts);

static long g_panels;
static double g_tol = 2e-8;   /* target width of each of the two integrals */

/* enclosure of f at the thin interval x; *ok = 0 if undefined */
static iv f_point(integrand f, const void *p, iv x, iv apriori, int *ok) {
    g_deg = 0; g_fail = 0;
    ts F = f(p, ts_const(x));
    if (g_fail) { *ok = 0; return apriori; }
    *ok = 1;
    return iint(F.c[0], apriori);
}
/* adaptive Simpson with rigorous remainder; apriori = enclosure of the range of f, valid everywhere */
static iv integ(integrand f, const void *p, double a, double b, iv fa, int oka, iv fb, int okb,
                iv apriori, double tolrate, int depth) {
    g_panels++;
    iv h = isub(pt(b), pt(a));
    iv X = mk(a, b);
    iv E = imul(h, apriori);
    g_deg = DEG; g_fail = 0;
    ts F = f(p, ts_var(X));
    int ok4 = !g_fail;
    if (ok4) E = iint(E, imul(h, F.c[0]));
    iv mI = imul(pt(0.5), iadd(pt(a), pt(b)));
    int okm;
    iv fm = f_point(f, p, mI, apriori, &okm);
    if (ok4 && oka && okb && okm) {
        iv S = imul(idiv(h, pt(6.0)), iadd(iadd(fa, fb), imul(pt(4.0), fm)));
        iv h2 = imul(h, h), h5 = imul(imul(h2, h2), h);
        iv R = imul(idiv(h5, pt(120.0)), F.c[4]);
        iv Es = isub(S, R);
        if (Es.lo <= E.hi && Es.hi >= E.lo) E = iint(E, Es);
        else if (Es.lo > E.hi || Es.hi < E.lo) contradiction();
    }
    double w = E.hi - E.lo;
    if (w <= tolrate * (b - a) || w <= g_tol * 1e-5 || depth >= 60 || !(b - a > 1e-15)) return E;
    double m = 0.5 * (a + b);
    int okmm;
    iv fmm = (m >= mI.lo && m <= mI.hi) ? fm : f_point(f, p, pt(m), apriori, &okmm);
    if (m >= mI.lo && m <= mI.hi) okmm = okm;
    iv L = integ(f, p, a, m, fa, oka, fmm, okmm, apriori, tolrate, depth + 1);
    iv Rr = integ(f, p, m, b, fmm, okmm, fb, okb, apriori, tolrate, depth + 1);
    return iadd(L, Rr);
}
static iv integrate(integrand f, const void *p, double a, double b, iv apriori, double tol, int pieces) {
    iv tot = pt(0.0);
    if (!(b > a)) return tot;
    double tolrate = tol / (b - a);
    double x0 = a;
    int ok0;
    iv f0 = f_point(f, p, pt(x0), apriori, &ok0);
    for (int i = 1; i <= pieces; i++) {
        double x1 = (i == pieces) ? b : a + (b - a) * i / pieces;
        int ok1;
        iv f1 = f_point(f, p, pt(x1), apriori, &ok1);
        tot = iadd(tot, integ(f, p, x0, x1, f0, ok0, f1, ok1, apriori, tolrate, 0));
        x0 = x1; f0 = f1; ok0 = ok1;
    }
    return tot;
}

/* ======================= V, P3up, P2 (cutwidth.md (A7)-(A10)) ======================= */
#define NH 20                 /* Hermite degrees 0..NH in the Mehler expansion */
#define XLOW (-8.0)           /* lower cut of the x-integrals */
#define EPS_TAIL 1e-7         /* >= sqrt(Phi(-8)) + sqrt(0.4e-14) = 2.6e-8 + 6.4e-8 (Cauchy-Schwarz, cutwidth.md (A8)) */
#define PI3_UP 1.0471975511966     /* a double > pi/3 = 1.04719755119659774... (checked in side_conditions) */
static const iv HALFPI = { 1.5707963267948966, 1.5707963267948968 };
static iv C_SQRT2, C_R1, C_KAP0, C_C0, C_SQ12, C_LAM, C_3OVERPI, C_SQRTN[NH + 2];
static void init_consts(void) {
    g_fail = 0;
    C_SQRT2 = isqrt_pos(pt(2.0));
    C_R1 = idiv(imul(pt(2.0), C_SQRT2), pt(3.0));                 /* 2 sqrt2 / 3 */
    C_KAP0 = isub(imul(pt(6.0), C_SQRT2), pt(8.0));               /* 6 sqrt2 - 8 */
    C_C0 = idiv(pt(3.0), imul(pt(2.0), C_SQRT2));                 /* 3/(2 sqrt2) */
    C_SQ12 = isqrt_pos(pt(12.0));
    C_LAM = idiv(imul(pt(2.0), isqrt_pos(pt(6.0))), pt(3.0));     /* 2 sqrt6 / 3 */
    C_3OVERPI = idiv(pt(3.0), PI_IV);
    for (int n = 1; n <= NH + 1; n++) C_SQRTN[n] = isqrt_pos(pt((double)n));
    if (g_fail) { fprintf(stderr, "init failed\n"); exit(3); }
}

/* ---- V ---- */
typedef struct { iv t, t2; int neg; } vpar;
/* A e^{-alpha t^2} Phi(beta t)  (neg = 0)   or   A e^{-alpha t^2} Phi(c0 A t)  (neg = 1), as a function of psi */
static ts f_V(const void *vp, ts psi) {
    const vpar *p = (const vpar *)vp;
    iv X = psi.c[0];
    iv c0 = icos(X), s0 = icos(isub(HALFPI, X));      /* sin X = cos(pi/2 - X), X within [0, pi/3 + tiny] */
    if (s0.lo < 0.0) s0.lo = 0.0;
    ts c;
    c.c[0] = c0;
    c.c[1] = ineg(s0); c.c[2] = ineg(imul(c0, pt(0.5))); c.c[3] = idiv(s0, pt(6.0)); c.c[4] = idiv(c0, pt(24.0));
    if (g_deg == 0) for (int k = 1; k <= DEG; k++) c.c[k] = pt(0.0);
    ts c2 = ts_mul(c, c);
    ts q = ts_add(c2, ts_const(pt(8.0)));
    ts sq = ts_sqrt(q);
    ts A = ts_div(c, sq);
    ts E = ts_exp(ts_scale(ts_div(ts_const(pt(1.0)), q), ineg(imul(pt(4.5), p->t2))));
    ts arg;
    if (!p->neg) arg = ts_scale(ts_div(ts_sub(c2, ts_const(C_KAP0)), ts_mul(c, sq)), p->t);
    else arg = ts_scale(A, imul(C_C0, p->t));
    return ts_mul(ts_mul(A, E), ts_Phi(arg));
}
/* upper bound of sup_{t in [a,b]} V(t); requires a >= 0 or b <= 0 */
static double V_up1(double a, double b) {
    vpar p; p.t = mk(a, b); p.t2 = isqr(p.t); p.neg = (b <= 0.0 && a < 0.0);
    if (a < 0.0 && b > 0.0) return INFINITY;
    /* 48 fixed Simpson panels, no adaptive refinement (tol = 1): with an interval t the width cannot go to 0 */
    iv I = integrate(f_V, &p, 0.0, PI3_UP, mk(0.0, 0.3334), 1.0, 48);    /* 0 <= integrand <= A <= 1/3 */
    double v = up(C_3OVERPI.hi * I.hi);
    if (p.neg) {
        /* Phi(t) - Phi(c0 t) = (c0-1)|t| phi(xi), xi in [c0 t, t]  =>  <= (c0-1) |a| phi(b) */
        double el, eh; exp_pt(-0.5 * b * b, &el, &eh);
        iv e = imul(imul(isub(C_C0, pt(1.0)), pt(-a)), imul(INVS2PI, mk(el, up(eh))));
        iv d = isub(iPhi(p.t), iPhi(imul(C_C0, p.t)));      /* direct enclosure (sharp for thin t) */
        v = up(v + (d.hi < e.hi ? d.hi : e.hi));
    }
    return v;
}
static double V_up(double a, double b, int nsub) {
    double v = 0.0;
    for (int i = 0; i < nsub; i++) {
        double x0 = (i == 0) ? a : a + (b - a) * i / nsub, x1 = (i == nsub - 1) ? b : a + (b - a) * (i + 1) / nsub;
        double w = V_up1(x0, x1);
        if (w > v) v = w;
    }
    return v;
}
/* P3(t) <= (1/r1 - 1) t phi(0) (1 - exp(-2 (3 t (1-r1))^2)) <= 0.02434 t (1 - exp(-0.0589 t^2)), increasing in t */
static double P3_up(double b) {
    if (b <= 0.0) return 0.0;
    iv e = iexp(ineg(imul(pt(0.0589), isqr(pt(b)))));
    return imul(imul(pt(0.02434), pt(b)), isub(pt(1.0), e)).hi;
}

/* ---- P2 ---- */
static int g_P = 80;                 /* Simpson panels on [XLOW, xm] */
static double g_du0 = 1e-4, g_growth = 1.002, g_ulen = 1.2;
/* f_n(x) = phi(x) hhat_n(x) (2 Phi(kappa - lambda x) - 1), n = 0..NH, at x (Taylor variable or thin constant) */
static void f_all(iv kappa, ts X, ts *f) {
    ts ph = ts_scale(ts_exp(ts_scale(ts_mul(X, X), pt(-0.5))), INVS2PI);
    ts G = ts_sub(ts_scale(ts_Phi(ts_sub(ts_const(kappa), ts_scale(X, C_LAM))), pt(2.0)), ts_const(pt(1.0)));
    ts base = ts_mul(ph, G);
    ts Hm = ts_const(pt(1.0)), H = X;
    f[0] = base;
    f[1] = ts_mul(base, H);
    for (int n = 1; n < NH; n++) {
        /* hhat_{n+1} = (x hhat_n - sqrt(n) hhat_{n-1}) / sqrt(n+1) */
        ts Hn = ts_scale(ts_sub(ts_mul(X, H), ts_scale(Hm, C_SQRTN[n])), idiv(pt(1.0), C_SQRTN[n + 1]));
        Hm = H; H = Hn;
        f[n + 1] = ts_mul(base, H);
    }
}
/* lower bound of K_a(u) */
static double K_lo(double a, double u) {
    g_fail = 0;
    iv M = imul(pt(3.0), isub(pt(a), imul(C_R1, pt(u))));
    iv kappa = imul(C_SQ12, isub(pt(a), idiv(imul(pt(5.0), pt(u)), pt(6.0))));
    iv X0 = idiv(kappa, C_LAM);
    if (g_fail || M.hi - M.lo > 5e-15 || X0.hi - X0.lo > 5e-15) return 0.0;
    double xm = dn(M.lo < X0.lo ? M.lo : X0.lo);       /* xm <= min(M, X0): on (-inf, xm], G = 2 Phi(kappa - lambda x) - 1 > 0 */
    if (!(xm > XLOW + 0.1)) return 0.0;
    iv I[NH + 1];
    ts fa[NH + 1], fb[NH + 1], fm[NH + 1], F[NH + 1];
    for (int n = 0; n <= NH; n++) I[n] = pt(0.0);
    double x0 = XLOW;
    g_deg = 0; f_all(kappa, ts_const(pt(x0)), fa);
    for (int i = 1; i <= g_P; i++) {
        double x1 = (i == g_P) ? xm : XLOW + (xm - XLOW) * i / g_P;
        iv h = isub(pt(x1), pt(x0));
        iv mI = imul(pt(0.5), iadd(pt(x0), pt(x1)));
        g_deg = 0; f_all(kappa, ts_const(pt(x1)), fb); f_all(kappa, ts_const(mI), fm);
        g_deg = DEG; f_all(kappa, ts_var(mk(x0, x1)), F);
        if (g_fail) return 0.0;
        iv h2 = imul(h, h), h5 = imul(imul(h2, h2), h);
        iv h6 = idiv(h, pt(6.0)), h120 = idiv(h5, pt(120.0));
        for (int n = 0; n <= NH; n++) {
            iv E = imul(h, F[n].c[0]);
            iv S = imul(h6, iadd(iadd(fa[n].c[0], fb[n].c[0]), imul(pt(4.0), fm[n].c[0])));
            iv Es = isub(S, imul(h120, F[n].c[4]));
            if (Es.lo <= E.hi && Es.hi >= E.lo) E = iint(E, Es);
            else if (Es.lo > E.hi || Es.hi < E.lo) contradiction();
            I[n] = iadd(I[n], E);
        }
        for (int n = 0; n <= NH; n++) fa[n] = fb[n];
        x0 = x1;
    }
    if (g_fail) return 0.0;
    /* K >= sum_{n even} 2^-n I_n^2 - sum_{n odd} 2^-n I_n^2 - 2^-(NH+1) I_0 */
    iv tot = pt(0.0);
    double w = 1.0;
    for (int n = 0; n <= NH; n++) {
        iv In = iadd(I[n], mk(-EPS_TAIL, EPS_TAIL));
        iv term = imul(pt(w), isqr(In));
        tot = (n % 2 == 0) ? iadd(tot, term) : isub(tot, term);
        w *= 0.5;                                   /* exact */
    }
    double I0hi = up(I[0].hi + EPS_TAIL);
    double res = dn(tot.lo - up(w * I0hi));         /* w = 2^-(NH+1) */
    return res > 0.0 ? res : 0.0;
}
static long g_knodes;
/* lower bound of P2(a,b) = int_{u>=b} phi(u) K_a(u) du */
static double P2_lo(double a, double b) {
    double total = 0.0, u0 = b, du = g_du0;
    double l0, h0, l1, h1;
    Phi_pt(u0, &l0, &h0);
    while (u0 - b < g_ulen) {
        double u1 = u0 + du;
        Phi_pt(u1, &l1, &h1);
        double mass = dn(l1 - h0);
        double K = K_lo(a, u1);
        g_knodes++;
        if (mass > 0.0 && K > 0.0) total = dn(total + dn(K * mass));
        u0 = u1; h0 = h1; du *= g_growth;
    }
    return total;
}

/* ---- certification of one base slab by bisection ---- */
typedef struct { long leaves, nP2; double worst; int ok; double fa, fb, fv; } sstat;
/* one leaf [a,b] (cutwidth.md 6.1 and (A10)): accepted iff Vup + P3up(b)/2 <= gamma or Vup + P3up(b)/2 - (3/2) P2lo
   <= gamma, all roundings directed; otherwise bisected (midpoints of dyadic numbers are exact), depth <= 16 */
static void certify(double gam_lo, double a, double b, int depth, sstat *st) {
    if (!st->ok) return;
    double Vu = V_up(a, b, 4);                              /* >= sup of V on [a,b] (A7) */
    double bound = up(Vu + up(P3_up(b) / 2.0));             /* >= sup V + P3up(b)/2 */
    if (!(bound <= gam_lo)) {
        double p2 = P2_lo(a, b);                            /* <= P2(a,b) <= P2(t), t in [a,b] (A9) */
        st->nP2++;
        bound = up(bound - dn(1.5 * p2));                   /* dn(fl(1.5 p2)) <= 1.5 p2 */
    }
    if (bound <= gam_lo) { st->leaves++; if (bound > st->worst) st->worst = bound; return; }
    if (depth >= 16) { st->ok = 0; st->fa = a; st->fb = b; st->fv = bound; return; }
    double m = 0.5 * (a + b);                               /* exact: a, b dyadic */
    certify(gam_lo, a, m, depth + 1, st);
    certify(gam_lo, m, b, depth + 1, st);
}
#define KMIN_NUM (-9)      /* t_min = -9/8 = -1.125 */
#define KMAX_NUM 2         /* t_max = 2 */
/* side conditions (cutwidth.md 6.1 and (A3), (A8), (A10)); every comparison is between rigorous bounds */
static int side_conditions(long G, int verbose) {
    iv gam = idiv(pt((double)G), pt(1e8));
    double l, h;
    Phi_pt(-1.125, &l, &h);
    int c1 = h <= gam.lo;                                   /* t <= -1.125: V - W/2 <= V <= Phi(t) <= Phi(-1.125) */
    Phi_pt(-2.0, &l, &h);
    int c2 = up(up(7.0 * h) / 2.0) <= gam.lo;               /* t >= 2: V <= 3 Phi(-t), P3/2 <= Phi(-t)/2 */
    /* constants used in P3_up: 1/r1 - 1 <= 0.061, phi(0) <= 0.39895, 0.061*0.39895 <= 0.02434, 18 (1-r1)^2 <= 0.0589 */
    iv a1 = isub(idiv(pt(1.0), C_R1), pt(1.0));
    int c3 = a1.hi <= 0.061 && INVS2PI.hi <= 0.39895 && up(0.061 * 0.39895) <= 0.02434;
    iv a2 = imul(pt(18.0), isqr(isub(pt(1.0), C_R1)));
    int c4 = a2.hi <= 0.0589;
    /* EPS_TAIL >= sqrt(Phi(-8)) + sqrt(0.4e-14), with Phi(-8) <= phi(8)/8 (Mills: Phi(-x) <= phi(x)/x) */
    double el, eh;
    exp_pt(-32.0, &el, &eh);
    double e = up(up(INVS2PI.hi * eh) / 8.0);
    int c5 = up(up(sqrt(e)) + up(sqrt(0.4e-14))) <= EPS_TAIL && INVS2PI.hi <= 0.4;
    int c6 = PI3_UP * 3.0 > PI_IV.hi;                       /* PI3_UP > pi/3 (3*PI3_UP is computed with error < 3e-16) */
    c6 = c6 && (PI3_UP * 3.0 - PI_IV.hi > 1e-15);
    /* Phi_pt for |x| > 7 uses 1 - Phi(|x|) <= Phi(-7) <= phi(7)/7 <= 1.39e-12 < 1.4e-12 (A3) */
    exp_pt(-24.5, &el, &eh);
    int c7 = up(up(INVS2PI.hi * eh) / 7.0) <= 1.39e-12;
    int c8 = fegetround() == FE_TONEAREST;                  /* (A0): round-to-nearest */
    int ok = c1 && c2 && c3 && c4 && c5 && c6 && c7 && c8;
    if (verbose) printf("check G=%ld gamma=[%.17g,%.17g] tails:%d,%d P3 consts:%d,%d eps_tail:%d pi/3:%d phi7:%d rounding:%d => %s\n",
                        G, gam.lo, gam.hi, c1, c2, c3, c4, c5, c6, c7, c8, ok ? "OK" : "FAIL");
    return ok;
}
static int selftest(void) {
    int bad = 0;
    /* V(0) = (3/(4 pi)) arccos(5/6) = 0.139822124008 (closed form; libm only as a cross-check) */
    double v0 = V_up1(0.0, 0.0), ex = 3.0 / (4.0 * 3.141592653589793) * acos(5.0 / 6.0);
    printf("V(0) <= %.12f, closed form %.12f\n", v0, ex);
    if (!(v0 >= ex - 1e-12 && v0 <= ex + 1e-7)) bad++;
    double vm = V_up1(-1e-300, 0.0);
    vpar p; p.t = pt(0.0); p.t2 = pt(0.0); p.neg = 1;
    iv I = integrate(f_V, &p, 0.0, PI3_UP, mk(0.0, 0.3334), 1.0, 48);
    printf("neg branch at t=0: V <= %.12f (integral %.12f)\n", vm, I.hi);
    /* at t = 0 the neg-branch integrand is A/2 and Phi(t) - Phi(c0 t) = 0; both branches must agree */
    if (!(vm >= ex - 1e-12 && vm <= ex + 1e-7)) bad++;
    (void)vm;
    double v68 = V_up1(0.068, 0.068);
    printf("V(0.068) <= %.12f (float value 0.14015825)\n", v68);
    if (!(v68 > 0.1401582 && v68 < 0.1401584)) bad++;
    double vn = V_up1(-0.1, -0.1);
    printf("V(-0.1) <= %.12f (float value 0.13812384)\n", vn);
    if (!(vn > 0.1381238 && vn < 0.1381239)) bad++;
    /* K at rho-independent sanity: I_0 = E G; and P2(0,0) against the float value 0.0025248 */
    double p2 = P2_lo(0.0, 0.0);
    printf("P2(0) >= %.9f (float value 0.0025248), %ld K-nodes\n", p2, g_knodes);
    if (!(p2 > 0.00250 && p2 <= 0.0025249)) bad++;
    /* EDH at t = 0.04 (float value of V - W/2: 0.1361516; the enclosure loses about 5e-6 there) */
    double ge = up(up(V_up1(0.04, 0.04) + up(P3_up(0.04) / 2.0)) - dn(1.5 * P2_lo(0.04, 0.04)));
    printf("V - (3/2) P2 + P3up/2 at t = 0.04 <= %.10f (float value of V - W/2: 0.1361516)\n", ge);
    if (!(ge > 0.1361515 && ge < 0.13617)) bad++;
    printf("selftest: %s\n", bad ? "FAIL" : "OK");
    return bad;
}

/* ---- exhaustive check of global submodularity (cutwidth.md Lemma 4.4), exact integer arithmetic ----
 * Tree ball B_6(0) of the 3-regular tree: vertex 0 has 3 children, every other vertex 2 (190 vertices).
 * Window energy, scaled by lden:  lden*f_a = lden*s_a - lden*s_a*s_y1*s_y2*s_y3 - lnum*(1-s_a)*psi(k_a),
 * k_a = sum over the neighbours y of a of s_y*prod_{z ~ y, z != a} s_z,  psi(k) = max(k-1, 0),  lambda = lnum/lden.
 * For p = 0 and q at distance d = 1..4 (on one geodesic; every pair at distance d is the image of this one under an
 * automorphism of the tree), A = {a : p, q in B_2(a)}, U = union of the B_2(a), a in A.  For every assignment of
 * the |U| - 2 other coordinates the program sums the mixed differences Delta_p Delta_q (lden f_a) over a in A and
 * records the maximum and minimum.  It also checks that A is empty for d = 5 and 6. */
#define GN 190
static int gadj[GN][3], gnadj[GN], gdep[GN], gdist[GN][GN];
static void build_ball(void) {
    int n = 1; gdep[0] = 0; gnadj[0] = 0;
    for (int v = 0; v < GN; v++) {
        int want = (v == 0) ? 3 : 2;
        if (gdep[v] >= 6) continue;
        for (int c = 0; c < want; c++) {
            int w = n++;
            gdep[w] = gdep[v] + 1; gnadj[w] = 0;
            gadj[v][gnadj[v]++] = w; gadj[w][gnadj[w]++] = v;
        }
    }
    if (n != GN) { printf("globsub: ball size %d\n", n); exit(3); }
    for (int s = 0; s < GN; s++) {             /* BFS distances */
        int qu[GN], h = 0, t = 0;
        for (int v = 0; v < GN; v++) gdist[s][v] = -1;
        gdist[s][s] = 0; qu[t++] = s;
        while (h < t) { int v = qu[h++]; for (int i = 0; i < gnadj[v]; i++) { int w = gadj[v][i];
            if (gdist[s][w] < 0) { gdist[s][w] = gdist[s][v] + 1; qu[t++] = w; } } }
    }
}
/* the 10 window positions of a (centre, 3 neighbours, 2 further neighbours of each); requires depth(a) <= 4 */
static void window(int a, int *pos) {
    if (gdep[a] > 4 || gnadj[a] != 3) { printf("globsub: window outside the ball\n"); exit(3); }
    pos[0] = a;
    for (int i = 0; i < 3; i++) {
        int y = gadj[a][i], m = 0;
        pos[1 + i] = y;
        if (gnadj[y] != 3) { printf("globsub: window outside the ball\n"); exit(3); }
        for (int j = 0; j < 3; j++) if (gadj[y][j] != a) pos[4 + 2 * i + m++] = gadj[y][j];
    }
}
static long fwin(const int *s, long lnum, long lden) {      /* lden * f on a window pattern s[0..9] */
    int k = 0;
    for (int i = 0; i < 3; i++) k += s[1 + i] & s[4 + 2 * i] & s[5 + 2 * i];
    long psi = k > 1 ? k - 1 : 0;
    return lden * s[0] - lden * (s[0] & s[1] & s[2] & s[3]) - lnum * (1 - s[0]) * psi;
}
static int globsub_run(int d, long lnum, long lden, long *mx, long *mn, long *npos, int *ncent, int *nU) {
    int p = 0, q = 0;
    for (int v = 0; v < GN; v++) if (gdist[0][v] == d && gdep[v] == d) { int ok = 1;   /* first vertex at depth d */
        for (int w = v; w != 0; w = gadj[w][0]) if (gdist[0][w] != gdep[w]) ok = 0;
        if (ok) { q = v; break; } }
    if (gdist[p][q] != d) return 0;
    int cent[GN], nc = 0, inU[GN] = {0}, other[GN], no = 0, idx[GN];
    for (int a = 0; a < GN; a++) if (gdist[a][p] >= 0 && gdist[a][p] <= 2 && gdist[a][q] <= 2) cent[nc++] = a;
    *ncent = nc;
    if (nc == 0) { *nU = 0; *mx = *mn = 0; *npos = 0; return 1; }
    int wpos[GN][10];
    for (int c = 0; c < nc; c++) { window(cent[c], wpos[c]); for (int i = 0; i < 10; i++) inU[wpos[c][i]] = 1; }
    int u = 0;
    for (int v = 0; v < GN; v++) if (inU[v]) { u++; if (v != p && v != q) { idx[v] = no; other[no++] = v; } }
    *nU = u;
    if (no > 30) return 0;
    /* per centre: positions of p, q in its window, and a table of the mixed difference over the other 8 bits */
    long tab[GN][256]; int obit[GN][8];
    for (int c = 0; c < nc; c++) {
        int ip = -1, iq = -1, m = 0, ord[8];
        for (int i = 0; i < 10; i++) { if (wpos[c][i] == p) ip = i; else if (wpos[c][i] == q) iq = i; else ord[m++] = i; }
        if (ip < 0 || iq < 0 || m != 8) return 0;
        for (int j = 0; j < 8; j++) obit[c][j] = idx[wpos[c][ord[j]]];
        for (int x = 0; x < 256; x++) {
            int s[10]; long v[4];
            for (int j = 0; j < 8; j++) s[ord[j]] = (x >> j) & 1;
            for (int e = 0; e < 4; e++) { s[ip] = e & 1; s[iq] = (e >> 1) & 1; v[e] = fwin(s, lnum, lden); }
            tab[c][x] = v[3] - v[1] - v[2] + v[0];             /* f(1,1) - f(1,0) - f(0,1) + f(0,0) */
        }
    }
    long best = -1000000, worst = 1000000, cnt = 0;
    for (long pat = 0; pat < (1L << no); pat++) {
        long sum = 0;
        for (int c = 0; c < nc; c++) {
            int x = 0;
            for (int j = 0; j < 8; j++) x |= (int)((pat >> obit[c][j]) & 1) << j;
            sum += tab[c][x];
        }
        if (sum > best) best = sum;
        if (sum < worst) worst = sum;
        if (sum > 0) cnt++;
    }
    *mx = best; *mn = worst; *npos = cnt;
    return 1;
}
static int globsub(void) {
    build_ball();
    int ok = 1;
    long L[2][2] = { { 1, 2 }, { 51, 100 } };
    long pos51 = 0;
    for (int l = 0; l < 2; l++)
        for (int d = 1; d <= 6; d++) {
            long mx, mn, np; int nc, nu;
            if (!globsub_run(d, L[l][0], L[l][1], &mx, &mn, &np, &nc, &nu)) { printf("globsub: setup error d=%d\n", d); return 0; }
            printf("lambda = %ld/%ld, distance %d: %d centres, |U| = %d, %s patterns, summed mixed difference in [%ld/%ld, %ld/%ld], %ld patterns > 0\n",
                   L[l][0], L[l][1], d, nc, nu, nc ? "all 2^(|U|-2)" : "no", mn, L[l][1], mx, L[l][1], np);
            if (l == 0) ok = ok && mx <= 0 && (d <= 4 ? nc > 0 : nc == 0);
            else pos51 += np;
        }
    printf("globsub: lambda = 1/2 globally submodular: %s; lambda = 51/100 has %ld positive patterns (sharpness)\n",
           ok ? "yes" : "NO", pos51);
    printf("globsub: %s\n", ok && pos51 > 0 ? "OK" : "FAIL");
    return ok && pos51 > 0;
}
int main(int argc, char **argv) {
    init_consts();
    if (argc >= 2 && !strcmp(argv[1], "selftest")) return selftest() ? 1 : 0;
    if (argc >= 4 && !strcmp(argv[1], "V")) { printf("%.17g\n", V_up(atof(argv[2]), atof(argv[3]), 1)); return 0; }
    if (argc >= 4 && !strcmp(argv[1], "P2")) {
        if (argc >= 7) { g_du0 = atof(argv[4]); g_growth = atof(argv[5]); g_P = atoi(argv[6]); }
        printf("%.17g %ld\n", P2_lo(atof(argv[2]), atof(argv[3])), g_knodes); return 0;
    }
    if (argc >= 4 && !strcmp(argv[1], "K")) { printf("%.17g\n", K_lo(atof(argv[2]), atof(argv[3]))); return 0; }
    if (argc >= 3 && !strcmp(argv[1], "check")) return side_conditions(atol(argv[2]), 1) ? 0 : 1;
    if (argc >= 2 && !strcmp(argv[1], "globsub")) return globsub() ? 0 : 1;
    if (argc >= 3 && !strcmp(argv[1], "full")) {
        long G = atol(argv[2]);
        if (argc >= 6) { g_du0 = atof(argv[3]); g_growth = atof(argv[4]); g_P = atoi(argv[5]); }
        if (!(g_du0 > 0) || !(g_growth >= 1.0) || g_P < 4 || G <= 0 || G >= 100000000) return 2;
        int ok = side_conditions(G, 1);
        iv gam = idiv(pt((double)G), pt(1e8));
        const int kden = 1024, kmin = KMIN_NUM * 128, kmax = KMAX_NUM * 1024;   /* -1152 .. 2048 */
        double worst = 0.0, prev_b = (double)kmin / kden;
        long leaves = 0, nP2 = 0, nslab = 0;
        for (int k = kmin; k < kmax; k++) {
            double a = (double)k / kden, b = (double)(k + 1) / kden;
            sstat st; st.leaves = st.nP2 = 0; st.worst = 0.0; st.ok = 1; st.fa = st.fb = st.fv = 0.0;
            g_knodes = 0;
            certify(gam.lo, a, b, 0, &st);
            ok = ok && st.ok && a == prev_b && st.worst <= gam.lo;
            prev_b = b; nslab++; leaves += st.leaves; nP2 += st.nP2;
            if (st.worst > worst) worst = st.worst;
            printf("slab %d G %ld kden %d t [%a, %a] = [%.6f, %.6f] du0 %g growth %g P %d leaves %ld nP2 %ld knodes %ld worst %.10f gamma %.10f %s",
                   k, G, kden, a, b, a, b, g_du0, g_growth, g_P, st.leaves, st.nP2, g_knodes, st.worst, gam.lo, st.ok ? "OK" : "FAIL");
            if (!st.ok) printf(" bad leaf [%.9f,%.9f] bound %.10f", st.fa, st.fb, st.fv);
            printf("\n");
            fflush(stdout);
        }
        ok = ok && nslab == kmax - kmin && (double)kmin / kden == -1.125 && prev_b == 2.0;
        printf("base slabs %ld, leaves %ld, P2 evaluations %ld, largest certified bound %.10f\n", nslab, leaves, nP2, worst);
        printf("RESULT: %s for gamma = %ld/10^8\n", ok ? "CERTIFIED" : "NOT certified", G);
        return ok ? 0 : 1;
    }
    if (argc >= 6 && !strcmp(argv[1], "slab")) {
        long G = atol(argv[2]);
        int kden = atoi(argv[3]), k0 = atoi(argv[4]), k1 = atoi(argv[5]);
        if (argc >= 9) { g_du0 = atof(argv[6]); g_growth = atof(argv[7]); g_P = atoi(argv[8]); }
        if (kden <= 0 || (kden & (kden - 1)) || kden > 65536 || !(g_du0 > 0) || !(g_growth >= 1.0) || g_P < 4) return 2;
        if (G <= 0 || G >= 100000000 || fegetround() != FE_TONEAREST) return 2;
        iv gam = idiv(pt((double)G), pt(1e8));
        int allok = 1;
        for (int k = k0; k < k1; k++) {
            double a = (double)k / kden, b = (double)(k + 1) / kden;     /* exact (kden a power of two) */
            sstat st; st.leaves = st.nP2 = 0; st.worst = 0.0; st.ok = 1; st.fa = st.fb = st.fv = 0.0;
            g_knodes = 0;
            certify(gam.lo, a, b, 0, &st);
            allok = allok && st.ok;
            printf("slab %d G %ld kden %d t [%a, %a] = [%.6f, %.6f] du0 %g growth %g P %d leaves %ld nP2 %ld knodes %ld worst %.10f gamma %.10f %s",
                   k, G, kden, a, b, a, b, g_du0, g_growth, g_P, st.leaves, st.nP2, g_knodes, st.worst, gam.lo, st.ok ? "OK" : "FAIL");
            if (!st.ok) printf(" bad leaf [%.9f,%.9f] bound %.10f", st.fa, st.fb, st.fv);
            printf("\n");
            fflush(stdout);
        }
        return allok ? 0 : 1;
    }
    fprintf(stderr, "usage: see the header of edcert.c\n");
    return 2;
}
