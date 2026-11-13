# Cutwidth of cubic multigraphs is at most (34039/250000)·D + h_d(D)

Status: one of the proof files (with `circuit.md`, `certificate.md` and `krs.md`). Theorem 1
below is the hypothesis H(γ,h) of `circuit.md` §0 for γ = γ_d = 34039/250000 and the explicit h = h_d of §0;
`proof.md` §6 combines this file with `circuit.md`. Proposition C (sup_t G_d(t) ≤ γ_d = 34039/250000) is proved
in `certificate.md` (see §6) and established by the program `certify.py` (Python
standard library only, its own outward-rounded interval arithmetic), which anyone can run in a few seconds; its
method and error analysis are in `certificate.md`, and its output object reports `certified: true` together with
the cover and the largest certified bound. The same program re-checks by exhaustive enumeration the finite facts
(C1), (C2), (C6) and the rational witnesses of §7 (C4), all of which are also proved in the text.

**Credit.** The route from cutwidth bounds to circuit lower bounds is due to S. McGuire, S. Schlesinger and
R. Williams (preprint, November 2026). Ordering the vertices of a cubic graph by thresholds of a Gaussian field
goes back to that preprint and to S. Gaspers (arXiv:2611.05146). New here: the comparison of the field on any
cubic multigraph with the field on the 3-regular tree for local energies whose *formal sum over the tree* is
submodular, although the local terms are not (Theorem 3.3), and the post-processing of the level sets by the set
maps E and D with the energy f (§4). They reduce the constant to an integral on the tree, certified in interval
arithmetic (§5; `certificate.md`). Every step is proved in this file or in `certificate.md`; none of the sources
is used as a premise. McGuire,
Schlesinger and Williams also have a computer-assisted cutwidth constant of about 0.1383 in this normalisation,
i.e. (4.6155 − ε)n (public repository github.com/rrwilliams0/circuit-lb-4.6155n); it is not used here.

**Labels.** [P] = proved here, from the facts listed in §1.0. [C] = checked by the program `certify.py`
(interval arithmetic, `certificate.md`; exact integer or rational checks are marked [C, exact]).
[S] = checked by
script, never used as a proof step. Notation is local to this file: D is a number of vertices, R a walk length,
N_k a walk count; N and L of `circuit.md` do not appear.

## 0. Statements

A **multigraph** K has a finite vertex set V and a finite edge set; each edge has an unordered pair of ends
{u, v}, u = v allowed (a *loop*). deg(v) is the number of non-loop edges at v plus twice the number of loops at
v; K is **cubic** if every degree is 3. For P ⊆ V, **cut(P)** is the number of edges with exactly one end in P
(loops never count). An ordering σ = (v_1, …, v_D) of V has cw(σ) := max_{1≤i<D} cut({v_1, …, v_i}) (0 if
D = 1), and cw(K) := min_σ cw(σ). This is the convention of `circuit.md` Definition 4.3.

    γ_d := 34039/250000 = 0.136156,
    h_d(D) := (340961/250000)·D                                       for 1 ≤ D < 2^40,
    h_d(D) := min{ (340961/250000)·D,  958·D/(log₂D − 3)² + 38·D^{8/9} }   for D ≥ 2^40.

**Theorem 1** [P + C]. Every cubic multigraph K on D vertices (connected or not; loops and parallel edges
allowed) satisfies cw(K) ≤ γ_d·D + h_d(D). The function h_d is nonnegative and nondecreasing on the positive
integers and h_d(D)/D → 0. In particular **H(γ_d, h_d) holds** in the sense of `circuit.md` §0.

**Theorem 2** [P + C]. Every cubic multigraph K on D vertices satisfies, for all integers R ≥ 4 and M ≥ 2,

    cw(K) ≤ γ_d·D + 106.41·D/(R+1)² + 17.96·D/(M−1) + 26.85·2^R·√(M·D) + 30.

**Proposition C** [C]. For every real t, G_d(t) := V(t) − W(t)/2 = V(t) − (3/2)P2(t) + (1/2)P3(t) ≤ γ_d, where
V, P2, P3 are probabilities of three events for one explicit Gaussian vector on ten coordinates and W = 3P2 − P3
(§5.1–§5.2). Equivalently G_d = Φ − P4 − (3/2)P2 + P3/2 with P4 = Φ − V.

[S] Floating-point quadrature gives max_t G_d(t) ≈ 0.1361516 at t ≈ 0.0404 (two independent quadratures), a
margin of about 4·10⁻⁶ below γ_d; the largest bound certified by `certify.py` is reported in its output
(`certificate.md` §6).

**Plan.** §1 preliminaries (walks, the universal cover, deck transformations). §2 the field and the lifting lemma;
tree correlations in closed form with an error bound for all R ≥ 4. §3 Gaussian comparison: smoothing, the
two-field estimate (Lemma 3.2) and the global comparison theorem (Theorem 3.3). §4 the set maps, the charging
inequalities, the window energy f and its global submodularity (Lemma 4.4). §5 the tree vector and the reduction
of the constant to G_d. §6 the certificate: Proposition C is proved in `certificate.md`, with the full error
analysis of its arithmetic. §7 proofs of Theorems 2 and 1 with rational witnesses (N1)–(N8).

## 1. Preliminaries

**1.0 Assumed.** Undergraduate analysis and probability: fundamental theorem of calculus; mean value theorem;
Taylor's theorem with Lagrange remainder; differentiation under the
integral sign (continuous integrand and derivative, integrable dominating function); Fubini and Tonelli; polar
coordinates; dominated and monotone convergence; Lebesgue measure on Rⁿ: inner regularity (a measurable set of
finite measure contains compact sets of measure arbitrarily close to its own) and the layer-cake formula
∫f = ∫_0^∞ |{f ≥ μ}|dμ for measurable f ≥ 0 (both used only for Theorem PL in `certificate.md`); linearity of expectation; the union bound; Chebyshev's inequality; Jensen's inequality for
conditional expectations; independence of functions of disjoint sets of independent variables; for random
variables with values in intervals of length w, |Cov| ≤ w²/4. Hilbert space L²(φ): an orthonormal sequence whose
span is dense gives the expansion G = Σ⟨G, e_n⟩e_n and Parseval's identity. An entire function equals its Taylor
series everywhere. Gaussian vectors: a centred Gaussian vector with covariance C has the law of A·η for any A with
AAᵀ = C, η standard normal; its law is determined by C; jointly Gaussian uncorrelated blocks are independent; a
nondegenerate centred Gaussian pair with variances v and covariance c has density at most 1/(2π√(v² − c²)).
One-dimensional Gaussian integration by parts: E[η h(η)] = E[h′(η)] for η ~ N(0,1), h ∈ C¹ with h, h′ bounded.
Fourier uniqueness: an integrable function on R whose Fourier transform vanishes is 0 a.e. The Hermite generating
function e^{sx − s²/2} = Σ_{n≥0} sⁿ He_n(x)/n! (He_n monic, ∫He_mHe_nφ = n!·[m=n]). φ(x) = e^{−x²/2}/√(2π),
Φ(x) = ∫_{−∞}^x φ. IEEE 754 binary64 arithmetic: +, −, ×, ÷, √ return the correctly rounded result
(`certificate.md` §6).

**1.1 Darts and walks** [P]. Every edge has two *darts*, one for each direction; d̄ is the reverse of d; the two
darts of a loop at v both have tail = head = v and are distinct; no dart equals its reverse. Cubic means: every
vertex is the tail of exactly 3 darts. A *non-backtracking (NB) walk* of length k ≥ 1 from v is a sequence of
darts d_1, …, d_k with tail(d_1) = v, head(d_i) = tail(d_{i+1}) and d_{i+1} ≠ d̄_i; it ends at head(d_k); the
empty walk (length 0) ends at v. N_k(v,w) is the number of NB walks of length k from v ending at w.
(W1) There are 3·2^{k−1} NB walks of length k ≥ 1 from v (3 first darts, then 2 continuations each time).
(W2) Reversal (d̄_k, …, d̄_1) is a bijection between NB walks from v to w and from w to v of the same length; so
every vertex is the end of exactly 3·2^{k−1} NB walks of length k ≥ 1, and of 1 + 3 + 6 = 10 NB walks of
length ≤ 2.
(W3) d(v,w) is the graph distance (+∞ between components); B(v,r) := {w : d(v,w) ≤ r}. A shortest walk is NB
(a step d followed by d̄ could be deleted), so the vertices at distance k ≥ 1 are ends of NB walks of length k:
there are at most 3·2^{k−1} of them, and |B(v,r)| ≤ 3·2^r − 2.
(W4) cut(P) ≤ number of non-loop edges ≤ 3D/2; adding or removing one vertex changes cut(P) by at most 3.

**1.2 The universal cover** [P]. Fix v. T_v is the set of NB walks from v; two walks are adjacent when one
extends the other by one dart. The empty walk o has 3 neighbours (its one-dart extensions); a walk ω ≠ o ending
with the dart e has one parent (ω without e) and two children ωd (d ≠ ē, tail(d) = head(e)). Every walk has a
unique path to o, so T_v is the 3-regular tree. π(ω) := end of ω. Send the tree dart ω → ωd to d and ωd → ω to
d̄. At each tree vertex ω the three tree darts go bijectively onto the three darts at π(ω) (at o: the three first
darts; at ω ending with e: parent ↦ ē, children ↦ the two other darts), and reverse pairs go to reverse pairs.
Hence (L) NB walks of length k from ω in T_v correspond bijectively, by mapping darts, to NB walks of length k
from π(ω) in K, and the end of the image is π of the end. In the tree, the NB walks from ω are the geodesics: one
to each vertex, of length the tree distance.

**1.3 Deck transformations** [P]. Let K be connected and T = T_v. A *deck transformation* is a bijection γ of
V(T) preserving adjacency with π∘γ = π on vertices and on darts (γ sends the dart x→y to γx→γy); they form a group
Γ. A deck transformation maps NB walks to NB walks (reverse darts go to reverse darts).

**Lemma 1.1** [P]. (a) For a, b ∈ T with π(a) = π(b) exactly one γ ∈ Γ satisfies γ(a) = b. Hence Γ acts freely
on V(T) (only the identity fixes a vertex), its orbits are the fibres π^{−1}(u), u ∈ V(K), and there are D
orbits. (b) No γ ∈ Γ exchanges the two ends of a tree edge, and no γ ≠ id maps a set {p, q} of two distinct tree
vertices onto itself.
*Proof.* (a) For x ∈ T let geo(a,x) be the NB walk from a to x and define γ(x) := end of the lift from b (by (L))
of the walk π(geo(a,x)) of K. Lifts of walks are lifted dart by dart, so if y is a neighbour of x with geo(a,y) =
geo(a,x)·(x→y), then γ(y) is joined to γ(x) by the tree dart at γ(x) whose image is π(x→y); the case geo(a,x) =
geo(a,y)·(y→x) is symmetric. So γ preserves adjacency and π on darts, and π∘γ = π on vertices (a walk and its lift
have the same end image). The lift from b is an NB walk of T, hence geo(b, γx), whose image is π(geo(a,x)), whose
lift from a is geo(a,x); so the map defined from (b, a) inverts γ, and γ ∈ Γ. If γ′ ∈ Γ and γ′(a) = b, γ′ maps
geo(a,x) to an NB walk from b with the same image, i.e. to the lift, so γ′(x) = γ(x). Taking b = a: γ′ = id. Every
u ∈ V(K) is the end of a shortest, hence NB, walk from v (W3), so π is onto and the orbits are the D fibres.
(b) If γ(x) = y and γ(y) = x for a tree edge, then γ maps the dart x→y to y→x, so π(x→y) = π(y→x), a dart of K
equal to its own reverse: impossible. If γ{p,q} = {p,q} and γ ≠ id, then γp ≠ p by (a), so γ exchanges p and q
and maps the tree path from p to q onto itself reversed: it fixes its middle vertex (d(p,q) even; impossible by
(a)) or exchanges the ends of its middle edge (d(p,q) odd; impossible). ∎

## 2. The field

Fix an integer R ≥ 4 (the walk length) and ε ∈ (0, 1/2). Put θ := π/(R+1), a_k := sin(kθ) for 0 ≤ k ≤ R+1 and
a_k := 0 for k > R+1 (so a_0 = a_{R+1} = 0). Since Σ_{k=0}^{R} cos(2kθ) = 0 (real parts of the (R+1)-th roots of
unity), Σ_{k=1}^{R} a_k² = (R+1)/2. Put S_R := (3/2)Σ a_k² = 3(R+1)/4, c_k := a_k² 2^{−k}/S_R and

    P_v(w) := Σ_{k=1}^{R} c_k N_k(v,w),   Y_v := Σ_w √(P_v(w))·g_w,   Y′_v := √(1−ε²)·Y_v + ε·ξ_v,

with (g_w), (ξ_w) independent standard normals.

**Lemma 2.1** [P]. (a) Σ_w P_v(w) = 1. Y′ is a centred Gaussian vector with Var Y′_v = 1 and, for u ≠ w,
Cov(Y′_u, Y′_w) = (1−ε²)·BC(u,w), BC(u,w) := Σ_x √(P_u(x)P_w(x)). (b) Y′_v is a function of (g_x)_{x∈B(v,R)} and
ξ_v. (c) With probability 1 the D numbers Y′_v are pairwise distinct, and P[Y′_v = t] = 0 for every t.
*Proof.* (a) By (W1), Σ_w P_v(w) = Σ_k c_k 3·2^{k−1} = (3/2)Σa_k²/S_R = 1; the rest is bilinearity. (b) P_v is
supported in B(v,R). (c) Y′_u − Y′_w has variance ≥ 2ε² > 0 for u ≠ w, and Y′_v ~ N(0,1). ∎

**Lemma 2.2 (lifting)** [P]. For a, b ∈ T_v put p_a(x) := c_{d_T(a,x)} if 1 ≤ d_T(a,x) ≤ R and 0 otherwise
(x ∈ T_v, d_T the tree distance), and ρ(a,b) := Σ_{x∈T_v} √(p_a(x)p_b(x)). Then BC(π a, π b) ≥ ρ(a,b) for all
a, b (any distance, π a = π b allowed).
*Proof.* By (L), N_k(πa, y) = #{x ∈ π^{−1}(y) : d_T(a,x) = k}, so P_{πa}(y) = Σ_{x∈π^{−1}(y)} p_a(x) (finitely
many nonzero terms). By Cauchy–Schwarz, √((Σ_x p_a(x))(Σ_x p_b(x))) ≥ Σ_x √(p_a(x)p_b(x)) over each fibre
π^{−1}(y); sum over y. ∎

**Lemma 2.3 (tree correlations)** [P]. ρ(a,b) depends only on d = d_T(a,b); write r_d = r_d(R). With
s := sin²θ:

    r_1 = (2√2/3)·cos θ,                       r_2 = (2/3)·cos 2θ + 1/6 + 5s/(3(R+1)),
    r_3 = (√2/3)·[cos 3θ + (1/2)cos θ + 5·sinθ·sin2θ/(R+1)],
    r_4 = (1/3)·[cos 4θ + (1/2)cos 2θ + 1/4 + s(51/2 − 30s)/(R+1)].

Let w_d := (1 + d/3)·2^{−d/2}, so w_0 = 1, w_1 = 2√2/3, w_2 = 5/6, w_3 = √2/2, w_4 = 7/12. Then for d = 1, …, 4

    0 ≤ w_d − r_d(R) ≤ C_d·θ²,   C_1 = √2/3, C_2 = 4/3, C_3 = 19√2/12, C_4 = 3.

*Proof.* Let a = q_0, q_1, …, q_d = b be the tree path. A vertex x is attached to the path at some q_i at depth
j ≥ 0, and then d_T(a,x) = i + j, d_T(b,x) = d − i + j. There is 1 such x with j = 0; for j ≥ 1 there are 2^j if
i ∈ {0, d} and 2^{j−1} if 0 < i < d (3-regularity). Since √(c_m c_n) = a_m a_n 2^{−(m+n)/2}/S_R and
m + n = d + 2j, and a_0 = 0 kills the terms j = 0 at i ∈ {0,d}:

    r_d = 2^{−d/2}·B_d/S_R,   B_d := 2A(d) + Σ_{i=1}^{d−1} [ a_i a_{d−i} + (1/2)Σ_{j≥1} a_{i+j} a_{d−i+j} ],

with A(m) := Σ_{j≥1} a_j a_{j+m}. For 0 ≤ m ≤ R, 2a_ja_{j+m} = cos mθ − cos((2j+m)θ), and telescoping
2 sinθ cos(xθ) = sin((x+1)θ) − sin((x−1)θ) over x = m+2, m+4, …, 2R−m gives Σ_{j=1}^{R−m} cos((2j+m)θ) =
(sin((2R−m+1)θ) − sin((m+1)θ))/(2 sinθ) = −sin((m+1)θ)/sinθ, since (2R−m+1)θ = 2π − (m+1)θ. Hence
A(m) = ((R−m)/2)cos mθ + sin((m+1)θ)/(2 sinθ). With sin2θ/sinθ = 2cosθ, sin3θ/sinθ = 1 + 2cos2θ,
sin4θ/sinθ = 2cosθ + 2cos3θ, sin5θ/sinθ = 1 + 2cos2θ + 2cos4θ (each from 2 sinθ cos xθ = sin(x+1)θ − sin(x−1)θ):

    A(0) = (R+1)/2,  A(1) = ((R+1)/2)cos θ,  A(2) = (R/2)cos 2θ + 1/2,
    A(3) = ((R−1)/2)cos 3θ + cos θ,  A(4) = ((R−2)/2)cos 4θ + cos 2θ + 1/2.

Using Σ_{j≥1} a_{p+j}a_{q+j} = A(q−p) − Σ_{k=1}^{p} a_k a_{k+q−p} for p ≤ q:
* B_1 = 2A(1) = (R+1)cos θ.
* B_2 = 2A(2) + a_1² + (1/2)(A(0) − a_1²) = R cos2θ + 1 + s/2 + (R+1)/4 = (R+1)(cos2θ + 1/4) + (5/2)s, using
  1 − cos 2θ = 2s.
* B_3 = 2A(3) + 2a_1a_2 + (A(1) − a_1a_2) = (R+1)(cos3θ + (1/2)cosθ) + 2(cosθ − cos3θ) + sinθ sin2θ, and
  cosθ − cos3θ = 2 sin2θ sinθ, so B_3 = (R+1)(cos3θ + (1/2)cosθ) + 5 sinθ sin2θ.
* B_4 = 2A(4) + [a_1a_3 + A(2)] + [a_2² + (1/2)(A(0) − a_1² − a_2²)] (the terms i = 1, 3 give
  2·(a_1a_3 + (1/2)(A(2) − a_1a_3))) = (R+1)(cos4θ + (1/2)cos2θ + 1/4) + E_4, where
  E_4 = −3cos4θ + (3/2)cos2θ + 3/2 + sinθ sin3θ + (sin²2θ − sin²θ)/2. With cos2θ = 1 − 2s,
  cos4θ = 1 − 8s + 8s², sinθ sin3θ = s(3 − 4s), sin²2θ = 4s − 4s²: E_4 = s(51/2 − 30s).

Dividing by S_R = 3(R+1)/4 and multiplying by 2^{−d/2} gives the four formulas. Then, with 1 − cos x ≤ x²/2,
s ≤ θ², θ ≤ π/5 and s ≤ sin²(π/5) < 0.35 (R ≥ 4):
* w_1 − r_1 = (2√2/3)(1 − cos θ) ∈ [0, (√2/3)θ²].
* w_2 − r_2 = (2/3)(1 − cos2θ) − 5s/(3(R+1)) = s·(4/3 − 5/(3(R+1))) ∈ [0, (4/3)θ²].
* w_3 − r_3 = (√2/3)[(1 − cos3θ) + (1/2)(1 − cosθ) − 5 sinθ sin2θ/(R+1)]. The subtracted term is ≥ 0, so
  w_3 − r_3 ≤ (√2/3)(9/2 + 1/4)θ² = (19√2/12)θ². For the lower bound write y = θ/2 and c = cosθ ≥ 0:
  1 − cos3θ = 2sin²y·(1 + 2c)², 1 − cosθ = 2sin²y, sinθ sin2θ = 8 sin²y cos²y·c; after division by 2sin²y
  it suffices that (1 + 2c)² + 1/2 ≥ 20c/(R+1), and 20c/(R+1) ≤ 4c < (1+2c)².
* w_4 − r_4 = (1/3)[(1 − cos4θ) + (1/2)(1 − cos2θ) − E_4/(R+1)] = (s/3)[9 − 8s − (51/2 − 30s)/(R+1)].
  Here 51/2 − 30s > 15 > 0, so w_4 − r_4 ≤ (s/3)(9 − 8s) ≤ 3s ≤ 3θ²; and (51/2 − 30s)/(R+1) ≤ 51/10 < 6.2 <
  9 − 8s, so w_4 − r_4 ≥ 0. ∎

[S] A float script (not supplied; not a proof step): the four formulas agree with a direct count over the tree
ball for R = 4..60 (error ≤ 1.1e−15), and the bounds hold for R = 4..2999, 10⁴, 10⁵.

## 3. Gaussian comparison

**Lemma 3.1 (interpolation)** [P]. Let X, X′ be independent centred Gaussian vectors in Rⁿ with covariances C, C′,
and Z_r := √(1−r)X + √r X′ (0 ≤ r ≤ 1). For g ∈ C² bounded with bounded first and second derivatives,

    E g(Z_1) − E g(Z_0) = (1/2)·∫_0^1 Σ_{i,j} (C′_ij − C_ij)·E[∂_i∂_j g(Z_r)] dr.

*Proof.* Gaussian integration by parts for vectors: if (W, Z) is a centred Gaussian vector and h ∈ C¹ has bounded
derivatives, then E[W_i h(Z)] = Σ_j Cov(W_i, Z_j)·E[∂_j h(Z)]. Indeed write (W, Z) = (Aη, Bη), η standard normal
in R^m (§1.0); by Fubini and §1.0, E[η_k h(Bη)] = Σ_j B_jk E[∂_j h(Bη)]; multiply by A_ik and sum over k. For
r ∈ (0,1), d/dr g(Z_r) = Σ_i ∂_i g(Z_r)·(X′_i/(2√r) − X_i/(2√(1−r))), dominated by a constant times |X| + |X′| on
compact subintervals; differentiate under E and apply the identity with Cov(X′_i, Z_{r,j}) = √r C′_ij,
Cov(X_i, Z_{r,j}) = √(1−r) C_ij. The derivative (1/2)Σ(C′_ij − C_ij)E[∂_i∂_j g(Z_r)] is bounded, and r ↦ E g(Z_r)
is continuous on [0,1] (dominated convergence), so integrate. ∎ (C, C′ may be singular.)

For f : {0,1}ⁿ → R and i ≠ j, the *mixed difference* Δ_iΔ_j f(s) := f(s^{11}) − f(s^{10}) − f(s^{01}) + f(s^{00}),
where s^{ab} is s with coordinates i, j set to a, b. f is *submodular* if all mixed differences are ≤ 0.

**Smoothing** [P]. Let f̃(p) := Σ_s f(s)Π_k p_k^{s_k}(1 − p_k)^{1−s_k} on [0,1]ⁿ (multilinear extension; f̃ = f on
{0,1}ⁿ, and adding dummy coordinates does not change f̃).
(S1) For i ≠ j, ∂_i∂_j f̃(p) = E[Δ_iΔ_j f(B)], B_k independent Bernoulli(p_k): a convex combination of mixed
differences of f.
(S2) For δ > 0 let σ_δ(y) := Φ(−y/δ), φ_δ(y) := φ(y/δ)/δ = −σ′_δ(y), and g_δ(z) := f̃(σ_δ(z_1 − t), …,
σ_δ(z_n − t)): smooth, bounded by max|f|, with bounded derivatives, and for i ≠ j
∂_i∂_j g_δ(z) = (∂_i∂_j f̃)(σ_δ(z − t))·φ_δ(z_i − t)φ_δ(z_j − t) (f̃ is affine in each coordinate).
(S3) As δ → 0, σ_δ(y) → 1{y < 0} for y ≠ 0, so g_δ(z) → f(s(z)), s(z) := (1{z_i < t})_i, unless some z_i = t. If a
random vector Z has P[Z_i = t] = 0 for each i (e.g. Var Z_i = 1), E g_δ(Z) → E f(s(Z)) (dominated convergence).

**Lemma 3.2 (two fields)** [P]. Let X, X′ be centred Gaussian vectors in Rⁿ with all variances 1, t ∈ R, and f
with |Δ_iΔ_j f| ≤ μ_ij for all i ≠ j. If ρ*_ij := max(|Cov(X_i,X_j)|, |Cov(X′_i,X′_j)|) < 1 for all i ≠ j, then

    |E f(s(X)) − E f(s(X′))| ≤ Σ_{i<j} μ_ij·|Cov(X′_i,X′_j) − Cov(X_i,X_j)| / (2π√(1 − ρ*_ij²)).

Singular covariance matrices are allowed, subject to ρ*_ij < 1 (so coinciding coordinates are not; they are
allowed in Theorem 3.3).
*Proof.* Apply Lemma 3.1 to g_δ of (S2) (independent copies of X, X′); diagonal terms vanish (C′_ii = C_ii = 1):
|E g_δ(X′) − E g_δ(X)| ≤ ∫_0^1 Σ_{i<j} |C′_ij − C_ij|·μ_ij·E[φ_δ(Z_{r,i} − t)φ_δ(Z_{r,j} − t)] dr by (S1). The last
expectation is the density at (t,t) of (Z_{r,i} + δη_1, Z_{r,j} + δη_2) (η independent standard normals), a centred
Gaussian pair with variances 1 + δ² and covariance ρ_r between Cov(X_i,X_j) and Cov(X′_i,X′_j); it is at most
1/(2π√((1+δ²)² − ρ_r²)) ≤ 1/(2π√(1 − ρ*_ij²)). Let δ → 0 (S3). ∎

**Setting of Theorem 3.3.** T is the 3-regular tree; for a ∈ V(T), B(a) is the set of the 10 vertices at
distance ≤ 2. Let Ω be the window of §4 (positions 0; 1, 2, 3; (i,1), (i,2)); a *frame* of a is a bijection
ι: Ω → B(a) with ι(0) = a, ι(1), ι(2), ι(3) the neighbours of a and ι(i,1), ι(i,2) the two other neighbours of
ι(i). Let f: {0,1}^Ω → R be invariant under the automorphisms of Ω (permutations of the branches, exchange of the
two leaves of a branch); then f_a(s) := f(s∘ι) (s ∈ {0,1}^{B(a)}) does not depend on the frame ι, and
f_{γa}(s) = f_a(s∘γ) for every automorphism γ of T. For distinct p, q let A_pq := {a : p, q ∈ B(a)} (empty if
d(p,q) > 4), U_pq := ∪_{a∈A_pq} B(a) (finite) and H_pq := Σ_{a∈A_pq} f_a, a function on {0,1}^{U_pq}.

**Theorem 3.3 (global comparison)** [P]. Let Γ be a group of automorphisms of T acting freely on V(T) with finitely
many orbits, and F a set containing exactly one vertex of each orbit. Let X⁰, X¹ be centred Gaussian processes indexed by
V(T) (every finite subfamily is a centred Gaussian vector) such that
* (G1) Var X⁰_a = Var X¹_a = 1 for every a;
* (G2) the laws of X⁰ and of X¹ are Γ-invariant: (X^i_{γa})_a has the law of (X^i_a)_a for γ ∈ Γ (for X⁰ it
  suffices that Cov(X⁰_a, X⁰_b) depends only on d(a,b), i.e. that its law is invariant under all automorphisms of
  T; X¹ may have X¹_a = X¹_b for a ≠ b);
* (G3) Cov(X¹_p, X¹_q) ≥ Cov(X⁰_p, X⁰_q) for all distinct p, q with d(p,q) ≤ 4;
* (G4) (global submodularity) Δ_pΔ_q H_pq ≤ 0 on {0,1}^{U_pq} for all distinct p, q with d(p,q) ≤ 4.
Then for every t ∈ R, with s_t(x) := (1{x_a < t})_a,

    Σ_{a∈F} E f_a(s_t(X¹)|_{B(a)}) ≤ Σ_{a∈F} E f_a(s_t(X⁰)|_{B(a)}).

No submodularity of the single f_a is assumed (the f of §4 has positive mixed differences, Lemma 4.3(d)).
*Proof.* *Step 1 (one window).* Take X⁰, X¹ independent and W_r := √(1−r)X⁰ + √r X¹. For a ∈ F the vectors
X⁰|_{B(a)}, X¹|_{B(a)} are independent centred Gaussian vectors in R^{B(a)} with unit variances; the coordinates
are the 10 distinct tree vertices of B(a), even if some X¹-coordinates coincide. With g_a the function g_δ of (S2)
for f_a, Lemma 3.1 gives E g_a(X¹) − E g_a(X⁰) = ∫_0^1 Σ_{(i,j)} φ_r(a,i,j) dr, the sum over ordered pairs i ≠ j
in B(a) (the diagonal terms vanish by (G1)), where
φ_r(a,i,j) := (1/2)·dC_ij·E[∂_i∂_j g_a(W_r|_{B(a)})], dC_ij := Cov(X¹_i, X¹_j) − Cov(X⁰_i, X⁰_j).
*Step 2 (invariance).* Let 𝒳 := {(a,i,j) : i ≠ j ∈ B(a)}; Γ acts on 𝒳 by γ(a,i,j) = (γa,γi,γj). For γ ∈ Γ,
φ_r(γa,γi,γj) = φ_r(a,i,j): dC is Γ-invariant by (G2), the law of W_r is Γ-invariant (X⁰, X¹ independent, both
invariant), and g_{γa}(w) = g_a(w∘γ) because f_{γa}(s) = f_a(s∘γ).
*Step 3 (two fundamental domains).* The action on 𝒳 is free: γ(a,i,j) = (a,i,j) gives γa = a, so γ = id.
F₁ := {(a,i,j) ∈ 𝒳 : a ∈ F} contains exactly one element of each orbit (F meets each vertex orbit once, and the
action on vertices is free). Let 𝒫 be the set of ordered pairs (i,j), i ≠ j, d(i,j) ≤ 4; Γ acts freely on 𝒫
(γi = i forces γ = id); let 𝒫₀ contain one element of each orbit. 𝒫₀ is finite: each orbit has an element with
i ∈ F, and each i has finitely many j with d(i,j) ≤ 4. Then F₂ := {(a,i,j) : (i,j) ∈ 𝒫₀, a ∈ A_ij} also contains
exactly one element of each orbit of 𝒳: for (a,i,j) ∈ 𝒳 there are a unique (i₀,j₀) ∈ 𝒫₀ and a unique γ with
γ(i₀,j₀) = (i,j), and γ^{−1}(a,i,j) ∈ F₂; two elements of F₂ in one orbit have equal pairs (one representative
per orbit) and then differ by the identity. Both F₁ and F₂ are finite, the map sending each element of F₁ to the
element of F₂ in its orbit is a bijection, and φ_r is constant on orbits, so

    Σ_{(a,i,j)∈F₁} φ_r(a,i,j) = Σ_{(i,j)∈𝒫₀} (1/2)·dC_ij·E[ Σ_{a∈A_ij} ∂_i∂_j g_a(W_r) ].

*Step 4 (sign).* Fix (i,j) ∈ 𝒫₀ and put U := U_ij, p := (σ_δ(W_{r,k} − t))_{k∈U}. Each g_a, a ∈ A_ij, is g_δ for
f_a viewed as a function on {0,1}^U, and its multilinear extension evaluated at p; so by (S2)
Σ_{a∈A_ij} ∂_i∂_j g_a(W_r) = φ_δ(W_{r,i} − t)φ_δ(W_{r,j} − t)·∂_i∂_j H̃_ij(p), where H̃_ij is the multilinear
extension of H_ij. By (S1) and (G4), ∂_i∂_j H̃_ij(p) ≤ 0 at every point p ∈ [0,1]^U (also at r = 1, where some
coordinates of W_1 coincide: the inequality is pointwise in p). With φ_δ ≥ 0 and dC_ij ≥ 0 (G3) every term is
≤ 0. Summing Step 1 over a ∈ F (finitely many) and using Step 3 inside the integral:
Σ_{a∈F} (E g_a(X¹) − E g_a(X⁰)) ≤ 0.
*Step 5 (limit).* Let δ → 0 by (S3) (unit variances, (G1)); finitely many terms. ∎

**Remarks.** (i) Windows that wrap around a short cycle, a loop or a parallel edge in a graph are still 10
distinct tree vertices here; only X¹ has equal coordinates there, and (G3) then reads 1 ≥ Cov(X⁰_p, X⁰_q).
(ii) With unordered pairs the same argument works because the stabiliser of a set {i,j} is trivial (Lemma 1.1(b)
for deck groups; in general a group acting freely without edge inversions). (iii) If every f_a is submodular, (G4)
holds termwise, and Theorem 3.3 reduces to the window-by-window comparison. (iv) An equivalent route compares the
two fields on a finite cover of the graph of large girth; it is not used.

## 4. Set maps and the window energy

For S ⊆ V let d_S(v) be the number of darts with tail v and head in S, int S := {v ∈ S : d_S(v) = 3},

    E(S) := {v ∈ S : d_S(v) ≥ 2},   D(A) := A ∪ {v : d_A(v) ≥ 2}.

Both maps are monotone. For x ∈ R^V let med_v(x) be the median of the three numbers x_{head(d)} over the three
darts d at v (repetitions kept), L^E_v(x) := max(x_v, med_v(x)) and L^{ED}_v(x) := min(L^E_v(x), med_v(L^E(x))).

**Lemma 4.1** [P]. For every t: {v : L^{ED}_v(x) < t} = D(E({v : x_v < t})).
*Proof.* The median of three numbers is < t iff at least two of them are < t; max(p,q) < t iff both are;
min(p,q) < t iff one is. ∎

**Lemma 4.2 (charging)** [P]. For S ⊆ V and v ∉ S let k_v be the number of darts d at v such that z := head(d) is
in S and both darts at z other than d̄ have their heads in S. Then
(a) cut(E(S)) ≤ |S| − |int S|;  (b) cut(D(E(S))) ≤ |S| − |int S| − Σ_{v∉S} (k_v − 1)^+.
*Proof.* cut(P) is the number of darts with tail in P and head outside P (a cut edge has exactly one such dart; a
loop has none). (a) Let A := E(S). Darts from A to V∖S: a vertex v ∈ A has 3 − d_S(v) ≤ 1 of them, and one only if
d_S(v) = 2. Darts from A to S∖A: their reverses go from w ∈ S∖A into A, and such w has d_S(w) ≤ 1. So
cut(A) ≤ #{v ∈ A : d_S(v) = 2} + #{w ∈ S∖A : d_S(w) = 1} ≤ #{v ∈ S : d_S(v) ≤ 2} = |S| − |int S|.
(b) Let S_1 := E(S) and A′ := D(S_1)∖S_1 = {v ∉ S_1 : d_{S_1}(v) ≥ 2}. Counting darts (and using that the darts
from S_1 to A′ are the reverses of those from A′ to S_1),
cut(S_1 ∪ A′) − cut(S_1) = Σ_{v∈A′} (3 − 2d_{S_1}(v) − d_{A′}(v)) ≤ −Σ_{v∈A′} (2d_{S_1}(v) − 3), each term
≥ 1. If v ∉ S and k_v ≥ 2, each counted dart d has head z with d_S(z) ≥ 2, so z ∈ S_1; hence d_{S_1}(v) ≥ k_v ≥ 2,
v ∉ S_1, v ∈ A′ and 2d_{S_1}(v) − 3 ≥ 2k_v − 3 ≥ k_v − 1. So cut(D(S_1)) ≤ cut(S_1) − Σ_{v∉S}(k_v − 1)^+; use (a). ∎

**The window.** Ω := {walks of length ≤ 2 in T_v} has ten *positions*: the centre o; e_1, e_2, e_3 (the three
darts at v); and e_i d_{i1}, e_i d_{i2} (the two continuations of e_i). Abstractly write the positions as 0;
1, 2, 3; (i,1), (i,2). For s ∈ {0,1}^Ω put b_i := s_i s_{i1} s_{i2}, k := b_1 + b_2 + b_3, ψ(k) := (k − 1)^+ and

    f(s) := s_0 − s_0 s_1 s_2 s_3 − (1/2)·(1 − s_0)·ψ(k).

For S ⊆ V and v ∈ V put f_v(S) := f((1{π(x) ∈ S})_{x∈Ω}), π: T_v → V the cover map (§1.2). For a tree vertex a
of T = T_w with π(a) = v, the frame of a sending a walk x ∈ Ω to the end of its lift from a (by (L)) satisfies
π∘ι(x) = end of x; so f_a((1{π(y) ∈ S})_{y∈B(a)}) = f_v(S) (*window reading*). In tree notation (s indexed by
V(T)): f_a = s_a − int_a − (1/2)gain_a, int_a := s_aΠ_{y∼a}s_y, gain_a := (1 − s_a)ψ(k_a),
k_a := Σ_{y∼a} b_{a→y}, b_{a→y} := s_yΠ_{z∼y, z≠a} s_z.

**Lemma 4.3** [P]. (a) Σ_v f_v(S) = |S| − |int S| − (1/2)Σ_{v∉S}(k_v − 1)^+; hence cut(D(E(S))) ≤ Σ_v f_v(S).
(b) −1 ≤ f ≤ 1.
(c) Changing s_0 changes f by at most 3/2; changing s_i (i = 1, 2, 3) by at most 1; changing s_{(i,j)} by at most 1/2.
(d) Every mixed difference of f lies in [−1, 1/2]. For the six pairs {0, i}, {i, j} (1 ≤ i < j ≤ 3) its absolute
value is ≤ 1, for the other 39 pairs ≤ 1/2. (It is positive for some patterns, e.g. pairs {0, (i,j)}.)
(e) f is invariant under the automorphisms of Ω.
*Proof.* (a) The first term sums to |S|. s_0s_1s_2s_3 = 1 iff v ∈ S and the heads of the three darts at v are in
S, i.e. iff v ∈ int S. For v ∉ S, k is the k_v of Lemma 4.2. Then Lemma 4.2(b) and (1/2)ψ(k_v) ≤ ψ(k_v).
(b) If s_0 = 1, f = 1 − s_1s_2s_3 ∈ {0, 1}; if s_0 = 0, f = −ψ(k)/2 ∈ [−1, 0].
(c) Δ_0 f = 1 − s_1s_2s_3 + ψ(k)/2; it is ψ(k)/2 ≤ 1 if s_1s_2s_3 = 1, and ≤ 1 + 1/2 otherwise (then k ≤ 2). For
x ≠ 0: if s_0 = 1 only s_0s_1s_2s_3 can change (by ≤ 1, and only for x ∈ {1,2,3}); if s_0 = 0, ψ(k)/2 changes by
≤ 1/2 (k changes by ≤ 1, ψ is 1-Lipschitz).
(d) Use ψ(m+1) − ψ(m) = 1{m ≥ 1} ∈ {0,1} and ψ(m+2) − 2ψ(m+1) + ψ(m) = 1{m = 0} ≥ 0; put g := (1 − s_0)ψ(k)/2.
For x, y ∈ {0,1,2,3}: Δ_xΔ_y(s_0s_1s_2s_3) = product of the other two ∈ {0,1}. For g: Δ_0 g = −ψ(k)/2, so
Δ_yΔ_0 g = −Δ_yψ(k)/2 ∈ [−1/2, 0] (k nondecreasing in s_y); for x, y in one branch i, g is affine in b_i with
slope (1 − s_0)1{k − b_i ≥ 1}/2 and Δ_xΔ_y b_i ∈ {0,1}, so Δ_xΔ_y g ∈ [0, 1/2]; for x in branch i and y in branch
j ≠ i, Δ_xΔ_y g = (1 − s_0)·Δ_x b_i·Δ_y b_j·1{m = 0}/2 ∈ [0, 1/2], m the third b. Hence: pairs {0, i}:
−s_js_l − Δ_0Δ_i g ∈ [−1, 1/2]; pairs {i, j}: −s_0s_l − Δ_iΔ_j g with at most one term nonzero (s_0 = 1 or 0),
∈ [−1, 0]; pairs {0, (i,j)}: −Δ_0Δ g ∈ [0, 1/2]; all other pairs: −Δ_xΔ_y g ∈ [−1/2, 0].
(e) Clear from the formula. ∎

[C, exact] `certify.py` (C1) checks (b)–(e) exhaustively for 2f in integers (45 pairs × 256 contexts; the
48 automorphisms), and the identity ψ(k) = Σ_{i<j}b_ib_j − b_1b_2b_3.

**Lemma 4.4 (global submodularity)** [P; C, exact]. With f of this section, (G4) of Theorem 3.3 holds: for all
distinct p, q ∈ V(T), Δ_pΔ_q H_pq ≤ 0 on {0,1}^{U_pq}. The coefficient 1/2 is optimal: with λ·gain_a in place of
(1/2)gain_a the statement is true for 0 ≤ λ ≤ 1/2 and false for every λ > 1/2.
*Proof.* Write H := H_pq = Σ_{a∈A_pq}(s_a − int_a − λ gain_a) (λ = 1/2). A term depending on both s_p and s_q
has p, q ∈ B(a) (int_a depends on B(a)'s first two levels, gain_a on B(a)), so Δ_pΔ_qH = −Σ_a Δ_pΔ_q int_a −
λΣ_a Δ_pΔ_q gain_a, the sums over all a ∈ V(T) (finitely many nonzero terms). All variables below other than
s_p, s_q are fixed.
(i) int_a is a monomial: Δ_pΔ_q int_a = Π_{N[a]∖{p,q}} s ≥ 0 if p, q ∈ N[a] := {a} ∪ {neighbours}, else 0.
(ii) a ∉ {p, q}: gain_a = (1 − s_a)ψ(k_a) with 1 − s_a constant, and k_a a sum of monomials not containing s_a.
Let k^{xy} be k_a at s_p = x, s_q = y. Monomials have nonnegative first and mixed differences, so k^{10}, k^{01} ≥
k^{00} and k^{11} ≥ k^{10} + k^{01} − k^{00}. ψ is nondecreasing and its increments are nondecreasing, so
ψ(k^{11}) − ψ(k^{10}) − ψ(k^{01}) + ψ(k^{00}) ≥ ψ(k^{10} + k^{01} − k^{00}) − ψ(k^{01}) − (ψ(k^{10}) − ψ(k^{00}))
≥ 0 (k^{10} − k^{00} unit increments starting at k^{01} ≥ k^{00}). So Δ_pΔ_q gain_a ≥ 0.
(iii) a = p: gain_p = (1 − s_p)ψ(k_p), k_p free of s_p, so Δ_pΔ_q gain_p = −Δ_qψ(k_p) ≥ −Δ_q k_p (ψ is
nondecreasing and 1-Lipschitz, k_p nondecreasing in s_q). b_{p→y} involves the set N[y]∖{p}; in a tree q lies in
N[y]∖{p} for at most one neighbour y of p (y = q, or y the midpoint if d(p,q) = 2), and then
Δ_q k_p = Π_{N[y]∖{p,q}} s. So −λΔ_pΔ_q gain_p ≤ λΠ_{N[y]∖{p,q}}s, and it is ≤ 0 if no such y exists
(d(p,q) ≥ 3). The same for a = q.
Now: d(p,q) = 1: the a with p, q ∈ N[a] are a = p and a = q (a third would close a triangle), so Δ_pΔ_qH ≤
−(1 − λ)(Π_{N[p]∖{p,q}}s + Π_{N[q]∖{p,q}}s) ≤ 0 (in (iii) y = q for a = p, y = p for a = q). d(p,q) = 2 with
midpoint y and third neighbour r of y: only a = y has p, q ∈ N[a], with Δ_pΔ_q int_y = s_ys_r, and both terms of
(iii) are ≤ λs_ys_r, so Δ_pΔ_qH ≤ −(1 − 2λ)s_ys_r ≤ 0 as λ ≤ 1/2. d(p,q) ≥ 3: every term is ≤ 0. Optimality: at
d(p,q) = 2 take s_y = s_r = 1, one other branch of p and one other branch of q full (b = 1), everything else 0;
then the terms of (iii) equal λ each, gain_y = gain_r = 0, and Δ_pΔ_qH = 2λ − 1 > 0 for λ > 1/2. ∎

*Exhaustive verification (redo).* Automorphisms of T act transitively on ordered pairs at a given distance (map
one geodesic onto another and extend outward level by level, as all vertices have degree 3), and they transport
H_pq; so it suffices to take p = root of the ball B_6 (190 vertices) and q at distance d = 1, …, 4 along one
geodesic. Then |A_pq| = 6, 4, 2, 1 and |U_pq| = 30, 22, 14, 10; for d ≥ 5, A_pq = ∅. `certify.py` (C6)
[C, exact] computes, in integers, the maximum over all assignments of the other coordinates of the sum of
Δ_pΔ_q(2f_a) over A_pq (each window read through its frame): coordinates in two or more windows of A_pq are
enumerated (12, 8, 4, 0 of them), the others are maximised window by window. For λ = 1/2 the maximum is 0 at
every distance; for λ = 51/100 (×100 in integers) it is +2/100 at d = 2 and ≤ 0 elsewhere.

## 5. The tree vector and the constant

**5.1 Construction.** Let U, ζ = (ζ_1, ζ_2), δ_1, δ_2, δ_3 be independent, U and ζ_1, ζ_2 standard normal,
δ_i ~ N(0, 1/12). Let f_i := (cos(2πi/3), sin(2πi/3)) and x_i := ⟨ζ, f_i⟩: standard normal, Cov(x_i,x_j) = −1/2
(i ≠ j), x_1 + x_2 + x_3 = 0. With r_1 := 2√2/3 define on the ten positions

    W_0 := U,   W_i := r_1·U + x_i/3,   W_{i1}, W_{i2} := √2·W_i − U/2 ± δ_i = (5/6)U + (√2/3)x_i ± δ_i.

**Lemma 5.1** [P]. Cov(W_x, W_y) = w_{d(x,y)} (d the tree distance between positions; w_d as in Lemma 2.3).
*Proof.* Var W_i = 8/9 + 1/9 = 1; Var W_{i1} = 25/36 + 2/9 + 1/12 = 1. Distance 1: Cov(U, W_i) = r_1 = w_1;
Cov(W_i, W_{i1}) = (5/6)r_1 + √2/9 = 2√2/3 = w_1. Distance 2: Cov(W_i, W_j) = 8/9 − 1/18 = 5/6;
Cov(U, W_{i1}) = 5/6; Cov(W_{i1}, W_{i2}) = 25/36 + 2/9 − 1/12 = 5/6. Distance 3: Cov(W_i, W_{j1}) =
(5/6)r_1 − √2/18 = √2/2. Distance 4: Cov(W_{i1}, W_{j1}) = 25/36 − 1/9 = 7/12. ∎ [C, exact: (C2) of
`certify.py`, arithmetic in Q(√2).] The covariance matrix is singular (rank 6); all pair correlations are
≤ w_1 < 1.

**5.2 Reduction.** For t ∈ R let s(t) := (1{W_x < t})_x and G_d(t) := E f(s(t)). Define

    V(t)  := P[U < t, max_i W_i ≥ t],          P4(t) := P[U, W_1, W_2, W_3 < t] = Φ(t) − V(t),
    P2(t) := P[U ≥ t; W_1, W_2, W_{11}, W_{12}, W_{21}, W_{22} < t],
    P3(t) := P[U ≥ t; the nine W_x, x ≠ 0, are < t],      W(t) := E[(1 − s_0)ψ(k)] = 3P2(t) − P3(t).

**Lemma 5.2** [P]. G_d(t) = Φ(t) − P4(t) − (3/2)P2(t) + (1/2)P3(t) = V(t) − W(t)/2.
*Proof.* E s_0 = Φ(t), E[s_0s_1s_2s_3] = P4. ψ(k) = Σ_{i<j}b_ib_j − b_1b_2b_3 for k ∈ {0,…,3} (C1); permuting the
branches preserves the covariance matrix, so E[(1 − s_0)b_ib_j] = P2 for each of the three pairs, and
E[(1 − s_0)b_1b_2b_3] = P3. Hence W = 3P2 − P3 and G_d = Φ − P4 − W/2. ∎

**5.3 V.** Write Tri(h) := {z ∈ R² : ⟨z, f_i⟩ < h, i = 1, 2, 3}: empty for h ≤ 0 (the three numbers sum to 0),
an equilateral triangle of inradius h for h > 0, with standard Gaussian measure

    γ_2(Tri(h)) = 1 − (3/π)∫_0^{π/3} exp(−h²/(2cos²ψ)) dψ                                          (5.1)

(polar coordinates: the ray at angle ϑ leaves Tri(h) at distance h/cos(ϑ − ϑ_i), ϑ_i the nearest normal
direction, |ϑ − ϑ_i| ≤ π/3; P[|ζ| > r] = e^{−r²/2}; six congruent half-sectors). Put c := cos ψ,
A := c/√(c² + 8), α := 9/(2(c² + 8)), β := (c² − (6√2 − 8))/(c√(c² + 8)), c_0 := 3/(2√2).

**Lemma 5.3** [P].

    t ≥ 0:  V(t) = (3/π)∫_0^{π/3} A·e^{−αt²}·Φ(βt) dψ;
    t ≤ 0:  V(t) = Φ(t) − Φ(c_0t) + (3/π)∫_0^{π/3} A·e^{−αt²}·Φ(c_0At) dψ.

*Proof.* Given U = u, all W_i < t iff ζ ∈ Tri(3(t − r_1u)). This needs t − r_1u > 0, i.e. u < t/r_1, so
P4(t) = ∫_{−∞}^{u*} φ(u)·γ_2(Tri(3(t − r_1u))) du with u* := min(t, t/r_1) (= t if t ≥ 0, = c_0t if t ≤ 0, as
1/r_1 = c_0). Insert (5.1) and use Fubini. Since 9r_1² = 8, completing the square gives
u² + 9(t − r_1u)²/c² = ((c²+8)/c²)(u − 6√2t/(c²+8))² + 9t²/(c²+8), hence
∫_{−∞}^{u*} φ(u)e^{−9(t−r_1u)²/(2c²)}du = A e^{−αt²} Φ(√((c²+8)/c²)·(u* − 6√2t/(c²+8))), and the argument equals
βt for u* = t and c_0At for u* = c_0t. Finally V = Φ(t) − P4(t). ∎

The substitution τ = tan ψ (c² = 1/(1+τ²), dψ = dτ/(1+τ²)) turns the integrands into algebraic functions of τ:
A = 1/√(9+8τ²), α = 9(1+τ²)/(2(9+8τ²)), β = (1 − (6√2−8)(1+τ²))/√(9+8τ²). On [0, π/3] A and c_0A increase
with c, α decreases with c, and β increases with c (dβ/dc has the sign of 8c² + 2κc² + 8κ > 0, κ = 6√2 − 8).

**5.4 P2.** Put λ := 2√6/3, H(z) := max(0, 2Φ(z) − 1), and for real a, u:
M := 3(a − r_1u), κ_u := √12·(a − 5u/6), G_{a,u}(x) := 1{x < M}·H(κ_u − λx), K_a(u) := E[G_{a,u}(x_1)G_{a,u}(x_2)].

**Lemma 5.4** [P]. For a ≤ b and every t ∈ [a, b]: P2(t) ≥ P2(a,b) := ∫_b^∞ φ(u)K_a(u) du. K_a(u) is nonincreasing
in u; hence for b = u_0 < u_1 < … < u_n, P2(a,b) ≥ Σ_{j<n} K_a(u_{j+1})·(Φ(u_{j+1}) − Φ(u_j)).
*Proof.* {U ≥ b; the six coordinates < a} ⊆ the event of P2(t). Condition on (U, ζ) = (u, ζ): W_i < a iff x_i < M;
W_{i1}, W_{i2} < a iff |δ_i| < a − √2W_i + u/2 = a − (5/6)u − (√2/3)x_i, which has probability
H(√12(a − (5/6)u − (√2/3)x_i)) = H(κ_u − λx_i); δ_1, δ_2 are independent of each other and of (U, ζ). G_{a,u}(x)
is pointwise nonincreasing in u (r_1 > 0, 5/6 > 0) and ≥ 0. ∎

**Lemma 5.5 (Mehler)** [P]. Let (x_1, x_2) be standard bivariate normal with correlation ρ ∈ (−1,1), G ∈ L²(φ),
ĥ_n := He_n/√(n!) (ĥ_0 = 1, ĥ_1 = x, ĥ_{n+1} = (xĥ_n − √n ĥ_{n−1})/√(n+1)), I_n := ∫φĥ_nG. Then
E[G(x_1)G(x_2)] = Σ_{n≥0} ρⁿ I_n². Consequently, if 0 ≤ G ≤ 1 and ρ = −1/2, for every N:

    E[G(x_1)G(x_2)] ≥ Σ_{n≤N} (−1/2)ⁿ I_n² − 2^{−(N+1)}·I_0.

*Proof.* (i) The ĥ_n are orthonormal in L²(φ) (§1.0). (ii) They are complete: if f ∈ L²(φ) is orthogonal to all
polynomials, F(z) := ∫f(x)e^{zx}φ(x)dx is entire (Cauchy–Schwarz gives integrability of |f|e^{|z||x|}φ, and
one may differentiate under the integral) with F^{(k)}(0) = ∫fxᵏφ = 0, so F ≡ 0; F(iy) = 0 is the Fourier
transform of fφ ∈ L¹, so fφ = 0 a.e. (iii) Write x_2 = ρx_1 + √(1−ρ²)η with η independent. Then
E[e^{sx_2 − s²/2} | x_1] = e^{sρx_1 − s²ρ²/2}; expanding both sides by the generating function and comparing
coefficients of sⁿ (both sides are entire in s; the left side may be expanded under the expectation by dominated
convergence) gives E[ĥ_n(x_2) | x_1] = ρⁿĥ_n(x_1). (iv) Tf(x_1) := E[f(x_2) | x_1] is a contraction of L²(φ)
(Jensen) with Tĥ_n = ρⁿĥ_n; with G = Σ I_nĥ_n in L², TG = Σ ρⁿI_nĥ_n and E[G(x_1)G(x_2)] = ⟨G, TG⟩_φ = Σ ρⁿI_n².
For the inequality: |Σ_{n>N}ρⁿI_n²| ≤ 2^{−(N+1)}Σ_n I_n² = 2^{−(N+1)}∫φG² ≤ 2^{−(N+1)}∫φG = 2^{−(N+1)}I_0. ∎

**5.5 P3 and the tails.**

**Lemma 5.6** [P]. P3(t) = 0 for t ≤ 0. For t > 0 and any c_1 ≥ (1/r_1 − 1)/√(2π) (= 0.024199…) and
c_2 ≥ 18(1 − r_1)² (= 0.058874…): P3(t) ≤ P3up(t) := c_1·t·(1 − e^{−c_2t²}), an increasing function of t.
(P3up grows linearly; it is meant only for bounded ranges of t, used in `certificate.md`; the tails use
P3 ≤ Φ(−t), Lemma 5.7.)
*Proof.* W_1 + W_2 + W_3 = 3r_1U = 2√2U, so all W_i < t forces U < 3t/(2√2) = t/r_1. Together with U ≥ t this is
impossible for t ≤ 0. For t > 0: given U = u ∈ [t, t/r_1), the event all W_i < t is ζ ∈ Tri(3(t − r_1u)) ⊆
Tri(3t(1 − r_1)); this triangle lies in the disc of radius twice its inradius, of Gaussian measure
1 − e^{−18t²(1−r_1)²}; and P[t ≤ U < t/r_1] ≤ (t/r_1 − t)φ(0). ∎

**Lemma 5.7 (tails)** [P]. For every t, G_d(t) ≤ V(t) + P3(t)/2 (as P2 ≥ 0), V(t) ≤ Σ_i P[W_i ≥ t] = 3Φ(−t) and
P3(t) ≤ P[U ≥ t] = Φ(−t); so G_d(t) ≤ (7/2)Φ(−t). For t ≤ 0, G_d(t) ≤ V(t) ≤ Φ(t) (P3 = 0).

**Lemma 5.8 (the leaf bound; the enclosure of W)** [P]. Let a ≤ b, V̄ ≥ sup_{[a,b]} V and 0 ≤ P̲2 ≤ P2(a,b). Then
for t ∈ [a, b]: W(t) ≥ 3P̲2 − P3up(b) (P3up := 0 for b ≤ 0), and G_d(t) ≤ V̄ + P3up(b)/2 − (3/2)P̲2.
*Proof.* P2(t) ≥ P2(a,b) ≥ P̲2 (Lemma 5.4), P3(t) ≤ P3up(t) ≤ P3up(b) (Lemma 5.6), and Lemma 5.2. ∎

## 6. The certificate (Proposition C)

Here γ_d = 34039/250000. Proposition C (§0: G_d(t) ≤ γ_d for every real t) is proved in `certificate.md`,
the companion file of this one. It contains Theorem PL (log-concavity of Gaussian marginals) and Lemmas
5.9–5.12, with their proofs, and in its §6.1–§6.6 the certificate itself: what is checked; the arithmetic; the
lower bound of P4 = Φ − V; the lower bound of P2; the leaf bound, P3 and the tails; the run. The computation is
the program `certify.py` (Python standard library only, its own outward-rounded
interval arithmetic in the model of §1.0), which anyone can run in a few seconds. Its output object has the field
`certified: true`, a cover of the whole real line (finitely many leaves and two tails) and the largest certified
bound; `certificate.md` §6 proves that `certified: true` implies Proposition C. The labels [P], [C],
[C, exact] and [S] are used there as in this file.

## 7. Proofs of Theorems 2 and 1

Fix R ≥ 4, ε ∈ (0, 1/2), the field Y′ of §2, and order V by L^{ED}(Y′) (nondecreasing, ties by a fixed
labelling); call the ordering σ. Put S_t := {v : Y′_v < t} and S2(t) := D(E(S_t)) = {v : L^{ED}_v(Y′) < t}
(Lemma 4.1). Let Ω_0 be the event of Lemma 2.1(c) (probability 1), and Z_t := Σ_v f_v(S_t).

**Lemma 7.1 (ties)** [P]. On Ω_0, cw(σ) ≤ 30 + sup_t cut(S2(t)).
*Proof.* Max, median and min return one of their arguments, so L^{ED}_v = Y′_x for some x ∈ B(v,2). For a proper
prefix P with last vertex u let τ := L^{ED}_u; then S2(τ) ⊆ P ⊆ {L^{ED} ≤ τ}. On Ω_0, τ = Y′_x for a unique x and
every vertex with L^{ED} = τ lies in B(x,2), which has at most 10 vertices (W3). So |P∖S2(τ)| ≤ 10 and, by (W4),
cut(P) ≤ cut(S2(τ)) + 30. ∎

**Lemma 7.2 (one threshold)** [P + C]. For every fixed t,
E Z_t ≤ D·(G_d(t) + K_d(R) + 21ε²) ≤ D·(γ_d + K_d(R) + 21ε²), K_d(R) := 106.41/(R+1)².
*Proof.* Y′ restricted to a component of K is the field of that component (P_v lives in v's component), and Z_t is
additive over components; so let K be connected. Take T = T_v, π, Γ and F (one lift of each vertex) as in §1.3.
Put X¹_a := Y′_{π(a)}, and let X⁰ be the same construction on T: X⁰_a := √(1−ε²)Σ_{x∈T}√(p_a(x))g′_x + εξ′_a with
independent standard normals g′, ξ′ indexed by V(T) (finite sums). (G1): Σ_x p_a(x) = 1. (G2): X¹∘γ = X¹ for
γ ∈ Γ; Cov(X⁰_a, X⁰_b) = (1−ε²)ρ(a,b) (a ≠ b) depends only on d(a,b) (Lemma 2.3), so the law of X⁰ is invariant
under all automorphisms of T. (G3): for p ≠ q, Cov(X¹_p, X¹_q) = (1−ε²)BC(πp, πq) + ε²1{πp = πq} ≥ (1−ε²)ρ(p,q)
by Lemma 2.2 (all pairs, in particular d(p,q) ≤ 4; BC(u,u) = 1). (G4): Lemma 4.4. By the window reading (§4),
f_a(s_t(X¹)|_{B(a)}) = f_{π(a)}(S_t), so Theorem 3.3 gives E Z_t ≤ Σ_{a∈F} E f_a(s_t(X⁰)) = D·E f(s(X^L)), where
X^L := X⁰∘ι on Ω (the same law for every a and frame): covariance (1−ε²)r_{d(x,y)}(R). Lemma 3.2 for X^L and W
(Lemma 5.1): μ from Lemma 4.3(d), ρ* = w_d < 1, and |w_d − (1−ε²)r_d| ≤ C_dθ² + ε²w_d (Lemma 2.3). The ten
positions have 9, 12, 12, 12 pairs at distances 1, 2, 3, 4; Σμ over them is 3·1 + 6·(1/2) = 6, 3·1 + 9·(1/2) =
15/2, 6, 6; and √(1 − w_d²) = 1/3, √11/6, √2/2, √95/12. So

    E f(s(X^L)) − G_d(t) ≤ (θ²/(2π))·[6C_1·3 + (15/2)C_2·6/√11 + 6C_3·√2 + 6C_4·12/√95]
                            + ε²·45·max_d w_d/(2π√(1−w_d²))
                        = (π/(2(R+1)²))·[6√2 + 60/√11 + 19 + 216/√95] + ε²·45·2√2/(2π)
                        < 106.41/(R+1)² + 21ε²                       (N2).

Finally G_d(t) ≤ γ_d (Proposition C). ∎

Fix also an integer M ≥ 2, T := 3, δ := 2T/(M−1), τ_j := −T + (j−1)δ (1 ≤ j ≤ M; τ_M = T),
n_j := #{u : Y′_u ∈ [τ_j, τ_{j+1})} (1 ≤ j < M), n_− := #{u : Y′_u < −T}, n_+ := #{u : Y′_u ≥ T}.

**Lemma 7.3 (all thresholds)** [P]. For every real t:
cut(S2(t)) ≤ max{ max_{1≤j<M} (Z_{τ_j} + (15/2)n_j), 12n_−, 12n_+ }.
*Proof.* *t ∈ [τ_j, τ_{j+1}):* cut(S2(t)) ≤ Z_t (Lemma 4.3(a)). S_t and S_{τ_j} differ exactly at the u with
τ_j ≤ Y′_u < t. A vertex u is π(x) for exactly 10 pairs (v, x), x ∈ Ω (W2): once with x = 0, 3 times with x a
neighbour position, 6 times with x a leaf position; changing the coordinates one at a time, Lemma 4.3(c) gives
|Z_t − Z_{τ_j}| ≤ (3/2 + 3·1 + 6·(1/2))·n_j = (15/2)n_j.
*t < −T:* S2(t) ⊆ D(S_t) ⊆ S_t ∪ {v : some dart at v has its head in S_t}, so |S2(t)| ≤ 4|S_t| ≤ 4n_− and
cut(S2(t)) ≤ 12n_− (W4). *t ≥ T:* v ∉ S2(t) forces v ∉ E(S_t), i.e. v ∉ S_t or two darts at v have heads outside
S_t; so |V∖S2(t)| ≤ 4|V∖S_t| ≤ 4n_+ and cut(S2(t)) = cut(V∖S2(t)) ≤ 12n_+. ∎

**Lemma 7.4 (moments)** [P]. E n_j ≤ Dδ/√(2π); E n_± = DΦ(−3); Var Z_t ≤ 48·4^R·D for each fixed t;
Var n_j, Var n_± ≤ (3/4)·4^R·D.
*Proof.* Y′_u ~ N(0,1) and φ ≤ 1/√(2π). f_v(S_t) is a function of Y′ on B(v,2), hence (Lemma 2.1(b)) of g on
B(v, R+2) and ξ on B(v,2); so f_u(S_t), f_v(S_t) are independent unless d(u,v) ≤ 2R+4, which holds for at most
3·2^{2R+4} − 2 < 48·4^R vertices u (W3); and |Cov| ≤ 2²/4 = 1 (Lemma 4.3(b)). The indicator 1{Y′_u ∈ I} depends on
g on B(u,R) and ξ_u: at most 3·4^R dependent partners, |Cov| ≤ 1/4. ∎

**Proof of Theorem 2.** Let λ_1 := √(4M·48·4^R·D) = √192·2^R√(MD) and λ_2 := √(4M·(3/4)·4^R·D) = √3·2^R√(MD).
By Chebyshev each of the 2M events {Z_{τ_j} ≥ EZ_{τ_j} + λ_1}, {n_j ≥ En_j + λ_2} (1 ≤ j < M), {n_± ≥ En_± + λ_2}
has probability ≤ 1/(4M), so with probability ≥ 1/2 none occurs; intersect with Ω_0 and fix such an outcome. By
Lemmas 7.1–7.4, for all t,

    cut(S2(t)) < max{ D(γ_d + K_d(R) + 21ε²) + λ_1 + (15/2)(Dδ/√(2π) + λ_2),  12(DΦ(−3) + λ_2) }.

The first entry is the larger: 12Φ(−3) < 0.0178 < γ_d (N6) and 12λ_2 < λ_1 + (15/2)λ_2 (N3). By (N3), (N4),
λ_1 + (15/2)λ_2 ≤ 26.85·2^R√(MD) and (15/2)Dδ/√(2π) = 45D/((M−1)√(2π)) ≤ 17.96D/(M−1). With Lemma 7.1,
cw(K) ≤ cw(σ) ≤ 30 + D(γ_d + K_d(R) + 21ε²) + 17.96D/(M−1) + 26.85·2^R√(MD). The left side does not depend on ε;
let ε → 0. ∎

**Proof of Theorem 1.** By (W4), cw(K) ≤ 3D/2 = γ_dD + (340961/250000)D always; this settles D < 2^40. Let
D ≥ 2^40, Λ := log₂D ≥ 40, R := ⌊Λ/3⌋ − 1 ≥ 12 and M := ⌈D^{1/9}⌉ + 1. Then R + 1 > (Λ − 3)/3, so K_d(R) <
9·106.41/(Λ−3)² < 958/(Λ−3)² (N5); 2^R ≤ 2^{Λ/3 − 1} = D^{1/3}/2; and D^{1/9} ≥ 2^{40/9} > 2 gives M ≤ D^{1/9} + 2
≤ 2D^{1/9}, M − 1 ≥ D^{1/9}. Hence 26.85·2^R√(MD) ≤ 26.85·(√2/2)·D^{1/3+1/18+1/2} < 18.99D^{8/9} (N3),
17.96D/(M−1) ≤ 17.96D^{8/9}, 30 < 0.46·2^{35} ≤ 0.46D^{8/9}, and Theorem 2 gives cw(K) ≤ γ_dD + 958D/(Λ−3)² +
38D^{8/9} (N4). Together with the trivial bound, cw(K) ≤ γ_dD + h_d(D).
*Properties of h_d.* h_d ≥ 0. f(D) := 958D/(log₂D − 3)² + 38D^{8/9} is increasing on [2^40, ∞): the derivative of
x/(log₂x − 3)² has the sign of (log₂x − 3) − 2/ln 2 > 0. A minimum of nondecreasing functions is nondecreasing,
so h_d is nondecreasing on [1, 2^40) and on [2^40, ∞); at the junction f(2^40) > (340961/250000)·2^40 (N7), so
h_d(2^40) = (340961/250000)·2^40 ≥ h_d(2^40 − 1). Finally h_d(D)/D ≤ 958/(log₂D − 3)² + 38D^{−1/9} → 0. ∎

**Numerical witnesses** (exact rational comparisons after inserting the stated rational bounds;
`certify.py` (C4) checks each in exact rational arithmetic):
- (N1) 1.41421² < 2 < 1.41422²; 3.3166² < 11; 9.7467² < 95; 3.14159 < π < 3.1416 (π enclosed by Machin's formula
  in exact rationals).
- (N2) 6·1.41422 + 60/3.3166 + 19 + 216/9.7467 < 67.738 and 3.1416·67.738/2 < 106.41; for the ε² term,
  w_d²/(1 − w_d²) = 8, 25/11, 1, 49/95 ≤ 8 (so w_d/√(1 − w_d²) ≤ 2√2) and 45·2·1.41422/(2·3.14159) < 21.
- (N3) 4·48 = 192 < 13.857², so λ_1 ≤ 13.857·2^R√(MD); 3 < 1.7321²; 13.857 + (15/2)·1.7321 < 26.85;
  (12 − 15/2)²·3 = 243/4 < 192, so (12 − 15/2)λ_2 < λ_1; 26.85·1.41422/2 < 18.99.
- (N4) 45² < 17.96²·2·3.14159, so 45/√(2π) < 17.96; 18.99 + 17.96 + 0.46 ≤ 38; 30 < 0.46·2^{35}.
- (N5) 9·106.41 = 957.69 < 958.
- (N6) e^{4.5} > Σ_{k<30} 4.5ᵏ/k! > 90 and 2.5066² < 2·3.14159, so 12Φ(−3) ≤ 4φ(3) < 4/(90·2.5066) < 0.0178 < γ_d
  (Φ(−T) ≤ φ(T)/T).
- (N7) 2^40 < 22⁹, so 38·2^{−40/9} > 38/22 > 1.363844 = 3/2 − γ_d.
- (N8) 1 + 1/(2γ_d) = 159039/34039 (used in `proof.md` §6.2).
