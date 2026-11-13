# Cutwidth of cubic multigraphs is at most (11/80)·D + h_c(D)

Status: one of the proof files (with `circuit.md` and `krs.md`). Theorem 1 below is the
hypothesis H(γ,h) of `circuit.md` §0 for γ = γ_c = 11/80 and the explicit h = h_c of §0; `proof.md` §6 combines
this file with `circuit.md`. Supplied code: `edcert.c` (the certificate of Proposition C, §6) and
`certify_small.py` (exact checks of the finite facts, of the witnesses of §7 and of the constants and rational
inequalities of §6, and an independent pure-Python re-proof of a weaker form of Proposition C, §6.5).

**Credit.** The route from cutwidth bounds to circuit lower bounds is due to S. McGuire, S. Schlesinger and
R. Williams (preprint, November 2026). Ordering the vertices of a cubic graph by thresholds of a Gaussian field
goes back to that preprint and to S. Gaspers (arXiv:2611.05146). Two ingredients are new here: the comparison
of the field on any cubic multigraph with the field on the 3-regular tree for submodular local functionals of the
threshold pattern (§2, §3, Lemma 7.2), and the post-processing of the level sets by the set maps E and D with the
charging function F (§4). Together they reduce the constant to an integral on the tree, which is certified in
interval arithmetic (§5–§6). Every step is proved in this file; none of the sources is used as a premise.

**Labels.** [P] = proved here, from the facts listed in §1.0. [C] = checked by supplied code, the program named
at each use: either an exact finite check in integer or rational arithmetic (`certify_small.py`, C1–C6), or the
interval-arithmetic computation of `edcert.c` (Proposition C only), every enclosure of which is proved in §6.
[S] = checked by script; never used as a proof step. Notation is local to this file: D is a number of vertices,
R a walk length, N_k a walk count; N and L of `circuit.md` do not appear.

## 0. Statements

A **multigraph** K has a finite vertex set V and a finite edge set; each edge has an unordered pair of ends
{u, v}, u = v allowed (a *loop*). deg(v) is the number of non-loop edges at v plus twice the number of loops at
v; K is **cubic** if every degree is 3. For P ⊆ V, **cut(P)** is the number of edges with exactly one end in P
(loops never count). An ordering σ = (v_1, …, v_D) of V has cw(σ) := max_{1≤i<D} cut({v_1, …, v_i}) (0 if
D = 1), and cw(K) := min_σ cw(σ). This is the convention of `circuit.md` Definition 4.3 (the empty and the full
prefix have empty cuts).

    γ_c := 11/80 = 0.1375,
    h_c(D) := (109/80)·D                                          for 1 ≤ D < 2^40,
    h_c(D) := min{ (109/80)·D,  585·D/(log₂D − 3)² + 41·D^{8/9} }   for D ≥ 2^40.

**Theorem 1** [P + C]. Every cubic multigraph K on D vertices (connected or not; loops and parallel edges
allowed) satisfies cw(K) ≤ γ_c·D + h_c(D). The function h_c is nonnegative and nondecreasing on the positive
integers and h_c(D)/D → 0. In particular **H(γ_c, h_c) holds** in the sense of `circuit.md` §0.

**Theorem 2** [P + C]. Every cubic multigraph K on D vertices satisfies, for all integers R ≥ 4 and M ≥ 2,

    cw(K) ≤ γ_c·D + 64.93·D/(R+1)² + 12.77·D/(M−1) + 39.27·2^R·√(M·D) + 30.

**Proposition C** [C]. For every real t, G(t) := V(t) − P2(t) + P3(t)/3 ≤ 11/80, where V, P2, P3 are the
probabilities of three events for one explicit Gaussian vector on ten coordinates (§5.1–§5.2).

[S] Floating-point quadrature gives max_t G(t) ≈ 0.1374748 at t ≈ 0.0497; the certified upper bounds of the
program are ≤ 0.13749969 everywhere (§6.4).

**Plan.** §1 preliminaries (walks, the universal cover). §2 the field and the lifting lemma (Lemma 2.2); tree
correlations in closed form with an analytic error bound valid for all R ≥ 4 (Lemma 2.3). §3 Gaussian comparison
(Lemma 3.2). §4 the set maps, the charging inequalities and the window function F (Lemmas 4.2, 4.3). §5 the
tree vector and the reduction of the constant to G(t) (Lemmas 5.1–5.8). §6 the certificate. §7 proofs of
Theorems 2 and 1, with rational witnesses (N1)–(N8).

## 1. Preliminaries

**1.0 Assumed.** Undergraduate analysis and probability: fundamental theorem of calculus; differentiation under
the integral sign (continuous integrand and derivative, integrable dominating function); Fubini; change of
variables (polar coordinates in R²); dominated convergence; linearity of expectation; the union bound;
Chebyshev's inequality; independence of functions of disjoint sets of independent variables; for random
variables X, Y with values in intervals of length w, |Cov(X,Y)| ≤ w²/4. Gaussian vectors: a centred Gaussian
vector with covariance C has the law of A·η for any matrix A with AAᵀ = C and η standard normal; its law is
determined by C; jointly Gaussian uncorrelated blocks are independent; a nondegenerate centred Gaussian pair with
variances v and covariance c has density at most 1/(2π√(v² − c²)). One-dimensional Gaussian integration by
parts: E[η h(η)] = E[h′(η)] for η ~ N(0,1) and h ∈ C¹ with h, h′ bounded (φ′(x) = −xφ(x)). Fourier uniqueness:
an integrable function on R whose Fourier transform vanishes is 0 a.e. The Hermite generating function
e^{sx − s²/2} = Σ_{n≥0} sⁿ He_n(x)/n! (He_n the monic probabilists' Hermite polynomials, ∫He_mHe_nφ = n!·[m=n]).
Also: an entire function equals its Taylor series at 0 on all of C; Jensen's inequality for conditional
expectations; in a Hilbert space, expansion in a complete orthonormal system with Parseval's identity, and
Bessel's inequality; the mean value theorem and Taylor's formula with integral remainder.
φ(x) = e^{−x²/2}/√(2π), Φ(x) = ∫_{−∞}^x φ.

**1.1 Darts and walks** [P]. Every edge has two *darts*, one for each direction; d̄ is the reverse of d; the two
darts of a loop at v both have tail = head = v and are distinct. Cubic means: every vertex is the tail of exactly
3 darts. A *non-backtracking (NB) walk* of length k ≥ 1 from v is a sequence of darts d_1, …, d_k with
tail(d_1) = v, head(d_i) = tail(d_{i+1}) and d_{i+1} ≠ d̄_i; it ends at head(d_k); the empty walk (length 0) ends
at v. N_k(v,w) is the number of NB walks of length k from v ending at w.
(W1) There are 3·2^{k−1} NB walks of length k ≥ 1 from v (3 first darts, then 2 continuations each time).
(W2) Reversal (d_k̄, …, d_1̄) is a bijection between NB walks from v to w and from w to v of the same length; so
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
from π(ω) in K, and the end of the image is π of the end. In the tree, the NB walks of length k from ω end exactly
at the vertices at tree distance k, one walk each.

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
(x ∈ T_v, d_T the tree distance), and ρ(a,b) := Σ_{x∈T_v} √(p_a(x)p_b(x)). Then BC(π a, π b) ≥ ρ(a,b).
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

[S] In floating point (script not supplied; not a proof step) the four formulas agree with a direct count over
the tree ball for R = 4..60 (error ≤ 1.1e−15), and the bounds hold for R = 4..2999, 10⁴, 10⁵.

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
is continuous on [0,1] (dominated convergence), so integrate. ∎

For f : {0,1}ⁿ → R and i ≠ j, the *mixed difference* Δ_iΔ_j f(s) := f(s^{11}) − f(s^{10}) − f(s^{01}) + f(s^{00}),
where s^{ab} is s with coordinates i, j set to a, b. f is *submodular* if all mixed differences are ≤ 0.

**Lemma 3.2 (threshold comparison)** [P]. Let X, X′ be centred Gaussian vectors in Rⁿ with all variances equal to
1, t ∈ R, s(x) := (1{x_i < t})_{i≤n}, and f : {0,1}ⁿ → R with −μ_ij ≤ Δ_iΔ_j f ≤ 0 for all i ≠ j (μ_ij ≥ 0).
(a) If Cov(X_i, X_j) ≤ Cov(X′_i, X′_j) for all i ≠ j, then E f(s(X′)) ≤ E f(s(X)).
(b) If ρ*_ij := max(|Cov(X_i,X_j)|, |Cov(X′_i,X′_j)|) < 1 for all i ≠ j, then

    E f(s(X)) ≤ E f(s(X′)) + Σ_{i<j} μ_ij·(Cov(X′_i,X′_j) − Cov(X_i,X_j))^+ / (2π√(1 − ρ*_ij²)).

Only equal positive variances are used (here 1). Singular covariance matrices are allowed in (a) and (b), subject
to the stated hypotheses; coinciding coordinates (correlation exactly 1) are allowed in (a) only, since (b)
assumes |correlation| < 1 for every pair.
*Proof.* Let f̃(p) := Σ_s f(s)Π_k p_k^{s_k}(1 − p_k)^{1−s_k} on [0,1]ⁿ (multilinear extension). For i ≠ j,
∂_i∂_j f̃(p) = E[Δ_iΔ_j f(B)] with B_k independent Bernoulli(p_k), so ∂_i∂_j f̃ ∈ [−μ_ij, 0]. For δ > 0 let
σ_δ(y) := Φ(−y/δ), φ_δ(y) := φ(y/δ)/δ = −σ′_δ(y), and g_δ(z) := f̃(σ_δ(z_1 − t), …, σ_δ(z_n − t)): smooth, bounded
by max|f|, with bounded derivatives. For i ≠ j, ∂_i∂_j g_δ(z) = ∂_i∂_j f̃(·)·φ_δ(z_i − t)φ_δ(z_j − t); diagonal
terms have C′_ii − C_ii = 0. Apply Lemma 3.1 (independent copies of X, X′). (a) Every off-diagonal term is
≤ 0, so E g_δ(X′) ≤ E g_δ(X). (b) E g_δ(X) − E g_δ(X′) = ∫_0^1 Σ_{i<j}(C′_ij − C_ij)E[−∂_i∂_j g_δ(Z_r)]dr, and
(C′_ij − C_ij)(−∂_i∂_j g_δ) ≤ (C′_ij − C_ij)^+ μ_ij φ_δφ_δ. E[φ_δ(Z_{r,i} − t)φ_δ(Z_{r,j} − t)] is the density
at (t,t) of (Z_{r,i} + δη_1, Z_{r,j} + δη_2) (η independent standard normals), a centred Gaussian pair with
variances 1 + δ² and covariance ρ_r between Cov(X_i,X_j) and Cov(X′_i,X′_j); its density is at most
1/(2π√((1+δ²)² − ρ_r²)) ≤ 1/(2π√(1 − ρ*_ij²)). Finally let δ → 0: σ_δ(y) → 1{y < 0} for y ≠ 0 and f̃ = f on
{0,1}ⁿ, so g_δ(z) → f(s(z)) unless some z_i = t, an event of probability 0 for X and X′ (unit variances);
dominated convergence. ∎

## 4. Set maps and the window function

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
darts at v, in a fixed order); and e_i d_{i1}, e_i d_{i2} (the two continuations of e_i). Abstractly write the
positions as 0; 1, 2, 3; (i,1), (i,2). For s ∈ {0,1}^Ω put b_i := s_i s_{i1} s_{i2}, k := b_1 + b_2 + b_3 and

    F(s) := (1/3)·Σ_{x≠0} s_x − 2s_0 − (1/3)·Q(s),   Q(s) := (k − 1)^+ + s_0·1{k ≥ 1} = s_0k + (1 − s_0)(k − 1)^+.

For S ⊆ V and v ∈ V put F_v(S) := F((1{π(x) ∈ S})_{x∈Ω}), π: T_v → V the cover map (§1.2).

**Lemma 4.3** [P]. (a) Σ_v F_v(S) = |S| − |int S| − (1/3)Σ_{v∉S}(k_v − 1)^+; hence cut(D(E(S))) ≤ Σ_v F_v(S).
(b) F is submodular and every mixed difference of F is −1/3 or 0.
(c) −2 ≤ F ≤ 7/3.
(d) Changing s_0 changes F by at most 7/3; changing one s_x, x ≠ 0, changes F by at most 1/3.
*Proof.* (a) By (W2) every u ∈ V is π(x) for exactly 9 pairs (v, x) with x ≠ 0 (NB walks of length 1 or 2 ending
at u); so the first term sums to 3|S|. For the dart e_i at v with head z: s_0 b_i = 1 iff z ∈ S and all three
dart-heads of z (v and the two continuation heads) are in S, i.e. iff z ∈ int S; every vertex is the head of
exactly 3 darts, so Σ_v s_0k = 3|int S|. For v ∉ S, k is the k_v of Lemma 4.2. Sum; then Lemma 4.2(b) and
(1/3)(k_v − 1)^+ ≤ (k_v − 1)^+.
(b) The linear part has zero mixed differences; we show Δ_xΔ_y Q ∈ {0,1}. Note Q(k+1) − Q(k) = 1{k ≥ 1} +
s_0·1{k = 0} ∈ {0,1} for fixed s_0. *Case x = 0, y in branch i:* Δ_0Q = 1{k ≥ 1} (k does not involve s_0), and k
is nondecreasing in s_y, so Δ_yΔ_0Q ∈ {0,1}. *Case x, y both in branch i:* Q depends on that branch only through
b_i and is affine in b_i ∈ {0,1} with slope in {0,1}; Δ_xΔ_y b_i is the value of the third coordinate of the
branch, in {0,1}. *Case x in branch i, y in branch j ≠ i:* Δ_x b_i, Δ_y b_j ∈ {0,1}, and when both are 1 the mixed
difference is Q(m+2) − 2Q(m+1) + Q(m) with m the third b; the second difference of (k − 1)^+ is 1{m = 0} and
that of 1{k ≥ 1} is −1{m = 0}, so Δ_xΔ_yQ = Δ_x b_i·Δ_y b_j·(1 − s_0)·1{m = 0} ∈ {0,1}.
(c) If s_0 = 1 then Q = k and F = (1/3)(Σ_{x≠0}s_x − k) − 2 ≥ −2 since Σ_{x≠0}s_x ≥ 3k. If s_0 = 0, F =
(1/3)(Σ_{x≠0}s_x − (k−1)^+) ∈ [0, 7/3] (value 7/3 needs Σ ≥ 8, then k ≥ 2 forces Σ − (k−1)^+ ≤ 7; Σ ≤ 7 gives ≤ 7/3).
(d) Δ_0(3F) = −6 − 1{k ≥ 1}; for x ≠ 0, Δ_x(3F) = 1 − Δ_xQ ∈ {0,1} (k changes by at most 1). ∎

[C] `certify_small.py` (C1) also checks (b), (c), (d) exhaustively in integers (all 45 pairs × 256 contexts of
3F); this exact finite check confirms the proof above and is not needed by it.

## 5. The tree vector and the constant

**5.1 Construction.** Let U, ζ = (ζ_1, ζ_2), δ_1, δ_2, δ_3 be independent, U and ζ_1, ζ_2 standard normal,
δ_i ~ N(0, 1/12). Let f_i := (cos(2πi/3), sin(2πi/3)) and x_i := ⟨ζ, f_i⟩: standard normal, Cov(x_i,x_j) = −1/2
(i ≠ j), x_1 + x_2 + x_3 = 0. With r_1 := 2√2/3 define on the ten positions

    W_0 := U,   W_i := r_1·U + x_i/3,   W_{i1}, W_{i2} := √2·W_i − U/2 ± δ_i = (5/6)U + (√2/3)x_i ± δ_i.

**Lemma 5.1** [P]. Cov(W_x, W_y) = w_{d(x,y)} (d the tree distance between positions; w_d as in Lemma 2.3).
*Proof.* Var W_i = 8/9 + 1/9 = 1; Var W_{i1} = 25/36 + 2/9 + 1/12 = 1. Distance 1: Cov(U, W_i) = r_1 = w_1;
Cov(W_i, W_{i1}) = (5/6)r_1 + √2/9 = 2√2/3 = w_1. Distance 2: Cov(W_i, W_j) = 8/9 − 1/18 = 5/6;
Cov(U, W_{i1}) = 5/6; Cov(W_{i1}, W_{i2}) = 25/36 + 2/9 − 1/12 = 5/6. Distance 3: Cov(W_i, W_{j1}) =
(5/6)r_1 − √2/18 = √2/2. Distance 4: Cov(W_{i1}, W_{j1}) = 25/36 − 1/9 = 7/12. ∎ [C: (C2) of `certify_small.py`,
exact arithmetic in Q(√2).]

**5.2 Reduction.** For t ∈ R let s(t) := (1{W_x < t})_x and G(t) := E F(s(t)). Define

    V(t)  := P[U < t, max_i W_i ≥ t],
    P2(t) := P[U ≥ t; W_1, W_2, W_{11}, W_{12}, W_{21}, W_{22} < t],
    P3(t) := P[U ≥ t; the nine W_x, x ≠ 0, are < t].

**Lemma 5.2** [P]. G(t) = V(t) − P2(t) + P3(t)/3.
*Proof.* E Σ_{x≠0}s_x = 9Φ(t) and E s_0 = Φ(t). The vectors (W_1; U, W_{11}, W_{12}) and (U; W_1, W_2, W_3) have
the same covariance matrix (w_1 from the first entry to the others, w_2 among the others), hence the same law, so
E[s_0b_1] = P[U, W_1, W_2, W_3 < t]; permuting branches preserves the covariance matrix, so E[s_0k] =
3P[U, W_1, W_2, W_3 < t]. (k − 1)^+ = Σ_{i<j}b_ib_j − b_1b_2b_3 for k ∈ {0,…,3}, so E[(1 − s_0)(k − 1)^+] =
3P2 − P3. Hence G = Φ − P[U, W_1, W_2, W_3 < t] − P2 + P3/3, and Φ(t) − P[U, W_1, W_2, W_3 < t] = V(t). ∎

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
P[U, W_1, W_2, W_3 < t] = ∫_{−∞}^{u*} φ(u)·γ_2(Tri(3(t − r_1u))) du with u* := min(t, t/r_1) (= t if t ≥ 0,
= c_0t if t ≤ 0, as 1/r_1 = c_0). Insert (5.1) and use Fubini. Since 9r_1² = 8, completing the square gives
u² + 9(t − r_1u)²/c² = ((c²+8)/c²)(u − 6√2t/(c²+8))² + 9t²/(c²+8), hence
∫_{−∞}^{u*} φ(u)e^{−9(t−r_1u)²/(2c²)}du = A e^{−αt²} Φ(√((c²+8)/c²)·(u* − 6√2t/(c²+8))), and the argument equals
βt for u* = t and c_0At for u* = c_0t. Finally V = Φ(t) − P[U, W_1, W_2, W_3 < t]. ∎

The substitution τ = tan ψ (c² = 1/(1+τ²), dψ = dτ/(1+τ²)) turns the integrands into algebraic functions of τ:
A = 1/√(9+8τ²), α = 9(1+τ²)/(2(9+8τ²)), β = (1 − (6√2−8)(1+τ²))/√(9+8τ²). On [0, π/3] A and c_0A increase
with c, α decreases with c, and β increases with c (dβ/dc has the sign of 8c² + 2κc² + 8κ > 0, κ = 6√2 − 8);
`certify_small.py` uses these monotonicities, `edcert.c` does not.

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
(P3up is a useful majorant only for small t: it grows linearly, and P3up(t)/3 > 11/80 for t ≥ 17. It is used
only on [−1.125, 2]; the tails use P3 ≤ Φ(−t), Lemma 5.7.)
*Proof.* W_1 + W_2 + W_3 = 3r_1U = 2√2U, so all W_i < t forces U < 3t/(2√2) = t/r_1. Together with U ≥ t this is
impossible for t ≤ 0. For t > 0: given U = u ∈ [t, t/r_1), the event all W_i < t is ζ ∈ Tri(3(t − r_1u)) ⊆
Tri(3t(1 − r_1)); this triangle lies in the disc of radius twice its inradius, of Gaussian measure
1 − e^{−18t²(1−r_1)²}; and P[t ≤ U < t/r_1] ≤ (t/r_1 − t)φ(0). ∎

**Lemma 5.7 (tails)** [P]. For every t, G(t) ≤ V(t) + P3(t)/3 (as P2 ≥ 0), V(t) ≤ Σ_i P[W_i ≥ t] = 3Φ(−t) and
P3(t) ≤ P[U ≥ t] = Φ(−t); so G(t) ≤ (10/3)Φ(−t). For t ≤ 0, G(t) ≤ V(t) ≤ Φ(t).

**Lemma 5.8** [P]. For t ∈ [a,b]: G(t) ≤ V̄ + P3up(b)/3 − P̲2, whenever V̄ ≥ sup_{[a,b]}V and 0 ≤ P̲2 ≤ P2(a,b)
(Lemmas 5.2, 5.4, 5.6; P3up(t) ≤ P3up(b) and P3up := 0 for t ≤ 0). ∎

## 6. The certificate (Proposition C)

`edcert.c` proves Proposition C by checking finitely many instances of Lemma 5.8 and the tails of Lemma 5.7.
§6.1 says what is checked; §6.2–§6.3 prove that every number the program uses as a bound is one (Lemmas
6.1–6.7); §6.4 proves that its last line implies Proposition C (Lemma 6.8) and records the run. Names in
`typewriter` are functions of `edcert.c`.

**6.1 What is checked.** (i) *Side conditions* (`edcert check ED 13750000`; also run by `full`): c1: Φ(−1.125) <
0.1304 < 11/80, so G ≤ 11/80 for t ≤ −1.125; c2: (10/3)Φ(−2) < 0.0759 < 11/80, so G ≤ 11/80 for t ≥ 2; c3, c4: the
inequalities of Lemma 5.6 for c_1 = 0.02434, c_2 = 0.0589 (the binary64 numbers nearest to these decimals;
margins 1.4·10⁻⁴ and 2.5·10⁻⁵), via 1/r_1 − 1 ≤ 0.061, 1/√(2π) ≤ 0.39895 and 0.061·0.39895 ≤ 0.02434; c5: the
constant EPS_TAIL of Lemma 6.7; c6: the double p := PI3_UP exceeds π/3.
(ii) *Cover*: the base slabs [k/1024, (k+1)/1024], −1152 ≤ k < 2048, which tile [−1.125, 2]. Each base slab is
bisected (depth ≤ 16) until every leaf [a,b] satisfies V̄(a,b) + P3up(b)/3 ≤ γ or V̄(a,b) + P3up(b)/3 − P̲2(a,b) ≤ γ,
where γ is the lower end of an enclosure of 13750000/10⁸ = 11/80. No slab straddles 0. A leaf still open at
depth 16 is reported as FAIL, which means "not certified", never "false".

**6.2 Arithmetic model and point functions.** *Model* (assumed of machine and compiler): `double` is IEEE 754
binary64; +, −, ×, ÷ and `sqrt` return RN(z), the double nearest to the exact result z (ties to even; ±∞ beyond
the largest double), in the default rounding mode, which the program never changes; there is no excess
precision (FLT_EVAL_METHOD = 0, as on arm64 and on x86-64 with SSE2) and no contraction into fused operations
(`-ffp-contract=off -fno-fast-math`); `floor`, `fabs`, `ldexp` (normal result) and the conversion of integers
below 2^53 are exact; a decimal literal denotes the double nearest to it (GCC and Clang round correctly);
comparisons involving NaN are false. Put u := 2^−53, η := 2^−1075. The spacing of the doubles gives
(R0) |RN(z) − z| ≤ u|z| + η, and ≤ u|z| when |z| ≥ 2^−1022.
The hard-coded constants are checked in exact rationals by `certify_small.py` (C5), and every other rational
inequality marked (C6) below by its check C6.

**Lemma 6.1 (outward rounding)** [P]. Let up(x) be the least double > x (up(±0) = 2^−1074, up(+∞) = +∞,
up(−∞) = −max), as `up` computes it (successor of the bit pattern), and dn(x) := −up(−x).
(a) dn(RN(z)) ≤ z ≤ up(RN(z)) for every real z.
(b) `iadd`, `isub`, `ineg`, `imul`, `idiv`, `isqr`, `isqrt_pos` return intervals that contain the result of the
operation at every pair of points of the arguments; `imul`, `idiv` return [−∞, ∞] and set `g_fail` if a NaN
arises; `idiv` (`isqrt_pos`) sets `g_fail` if the divisor contains 0 (if the radicand is not > 0).
(c) Every interval formed has lo < +∞ and hi > −∞; hence no interval end is ever NaN.
(d) `iint` returns the intersection of two enclosures of one number; if they are disjoint the program stops
(exit code 4, `INTERNAL ERROR`, no verdict).
*Proof.* (a) z lies between the two doubles adjacent to RN(z), else one of them would be nearer (this includes
overflow and subnormal results). (b) RN is nondecreasing, so min_i RN(p_i) = RN(min_i p_i), likewise max; the
extremes of a product, or of a quotient whose divisor avoids 0, of two intervals are among the four corner values;
√ and the square are monotone on the pieces used; then (a). (c) Lower ends are produced by dn, which never returns
+∞, or are finite (dually for upper ends), so the sums in `iadd`, `isub` are never ∞ − ∞. (d) Two sets that
contain the same number meet. ∎

**Lemma 6.2 (exp)** [P]. For a double x with |x| ≤ 700, `exp_pt` returns lo, hi with
e^x(1 − 1.1·10⁻¹²) ≤ lo ≤ e^x(1 − 0.9·10⁻¹²) and e^x(1 + 0.9·10⁻¹²) ≤ hi ≤ e^x(1 + 1.1·10⁻¹²). For x < −700 it
returns [0, 10⁻³⁰⁰] ∋ e^x (e^699 > 10^303, C6); for x > 700 or NaN, [0, ∞] and `g_fail`. Hence lo ≤ e^a ≤ hi for
every real a with |a − x| ≤ 8·10⁻¹³ (e^{8·10⁻¹³} − 1 < 0.9·10⁻¹²), and `iexp` encloses exp over an interval.
*Proof.* Let L_1, L_2 be the doubles of the two literals in `exp_pt`; |L_1 − 1/ln 2| < 2.1·10⁻¹⁷ and
|L_2 − ln 2| < 2.4·10⁻¹⁷ (C5). With y := x/ln 2, |y| < 1010, (R0) gives |RN(xL_1) − y| ≤ |y|(1.46·10⁻¹⁷ + u)(1 + u)
< 1.27·10⁻¹³; so k := floor(RN(xL_1)) ∈ [−1010, 1009] and r* := x − k·ln 2 ∈ (−8.9·10⁻¹⁴, ln 2 + 10⁻¹³). The
program forms r̃ := RN(x − RN(kL_2)): as |kL_2| < 2^10, |RN(kL_2) − kL_2| ≤ 2^−44; |k(L_2 − ln 2)| < 2.5·10⁻¹⁴;
the subtraction errs by < u; so |r̃ − r*| < 8.2·10⁻¹⁴. A negative r̃ is replaced by 0, and then |r*| < 8.9·10⁻¹⁴.
So the r used satisfies |r − r*| < 8.9·10⁻¹⁴ and 0 ≤ r < 0.6934 (the test r > 0.75 never fires). Horner: with
σ_23 := 1 and σ_n := 1 + (r/n)σ_{n+1}, σ_1 = P(r) := Σ_{j≤22} r^j/j! and 1 ≤ σ_n ≤ e^r < 2.001 (C6). The computed
s_n := RN(1 + RN(RN(r/n)·s_{n+1})) satisfy, by (R0) and downward induction from s_23 = σ_23 = 1,
|s_n − σ_n| ≤ (r/n)·[(1+u)²|s_{n+1} − σ_{n+1}| + 2.0001u·σ_{n+1}] + u·2.002 + 3η
≤ 0.6934·(2.0001·10⁻¹⁵ + 4.5·10⁻¹⁶) + 2.3·10⁻¹⁶ < 2·10⁻¹⁵.
Taylor: 0 ≤ e^r − P(r) ≤ (r^23/23!)·24/(24 − r) < 10⁻²⁶ (C6). Hence s_1 = e^{r*}(1 + θ) with |θ| < 9.2·10⁻¹⁴.
The factors RN(1 ∓ 10⁻¹²) equal 1 ∓ 10⁻¹² up to 1.2·10⁻¹⁶, the product with s_1 is rounded once, and
`ldexp(·, k)` is exact since the result lies in [2^−1011, 2^1011]. As e^x = 2^k e^{r*},
lo/e^x ∈ (1 ± 9.2·10⁻¹⁴)(1 − 10⁻¹² ± 1.2·10⁻¹⁶)(1 ± u) ⊂ [1 − 1.1·10⁻¹², 1 − 0.9·10⁻¹²], and symmetrically for hi. ∎

**Lemma 6.3 (Φ)** [P]. For every double x, `Phi_pt` returns lo ≤ Φ(x) ≤ hi (for NaN, [0, 1] and `g_fail`); so
`iPhi` encloses Φ over an interval (Φ is increasing).
*Proof.* Let y := |x|, H := Φ(y) − 1/2 = φ(y)S(y), S(y) := Σ_{n≥0} y^{2n+1}/(2n+1)!! (termwise S′ = 1 + yS, so
(φS)′ = φ; both sides vanish at 0). Mills: Φ(−y) = ∫_y^∞ φ ≤ ∫_y^∞ (s/y)φ(s)ds = φ(y)/y for y > 0.
(i) y > 7: 0 ≤ 1/2 − H = Φ(−y) ≤ φ(7)/7 < 1.33·10⁻¹² (C6), so H ∈ [RN(0.5 − 1.4·10⁻¹²), 0.5].
(ii) 2^−60 ≤ y ≤ 7. The loop forms x̃² := RN(y²), T̃_0 := y, T̃_n := RN(RN(T̃_{n−1}x̃²)/(2n+1)),
S̃_n := RN(S̃_{n−1} + T̃_n), and stops at the first N with x̃² < (2N+3)/2 and T̃_N ≤ RN(10⁻¹⁷S̃_N). For n ≥ 49,
x̃² ≤ 49 < (2n+1)/2, so the first condition holds and T̃_n < T̃_{n−1}/2; as 2^−57 < 10⁻¹⁷(1 − 10⁻¹³), N ≤ 105.
For y < 1 even N ≤ 15 (31!! > 1.9·10¹⁷, C6). No operation underflows: for y ≥ 1 every term is ≥ 1/211!! >
10⁻²⁰¹ (C6); for y < 1 the last term is ≥ 0.98·10⁻¹⁷·y³/31 > 10⁻⁷⁵ (if N ≥ 2 then T̃_{N−1} > 0.99·10⁻¹⁷y; if
N = 1, T̃_1 ≥ 0.99·y³/3). So each rounding is a factor 1 + δ, |δ| ≤ u: T̃_n = T_n(1 + θ_n) with
T_n := y^{2n+1}/(2n+1)!!, |θ_n| ≤ (1+u)^{3n} − 1, and, all terms being positive, S̃_N = Σ_{n≤N} T_n(1 + θ′_n) with
|θ′_n| ≤ (1+u)^{4N} − 1 < 4.7·10⁻¹⁴. The omitted tail is ≤ T_N·q/(1 − q), q := y²/(2N+3) < (1+u)/2, hence
≤ 1.0001·10⁻¹⁷·S_N. So S̃_N = S(y)(1 + θ), |θ| < 4.8·10⁻¹⁴. `exp_pt` is called at −x̃²/2 (exact halving), which
is within 24.5u < 8·10⁻¹³ of −y²/2, so el ≤ e^{−y²/2} ≤ eh (Lemma 6.2). The two literals c_lo, c_hi used for
1/√(2π) satisfy c_lo ≤ 1/√(2π) ≤ c_hi (C5), and RN(1 ± 10⁻¹²) = 1 ± 10⁻¹² up to 1.2·10⁻¹⁶. Three roundings
follow, so
Hhi ≥ H(1 − 4.8·10⁻¹⁴)(1 + 10⁻¹² − 1.2·10⁻¹⁶)(1 − u)³ > H,   Hlo ≤ H(1 + 4.8·10⁻¹⁴)(1 − 10⁻¹² + 1.2·10⁻¹⁶)(1 + u)³ < H.
(iii) y < 2^−60. Every computed quantity is ≥ 0, x̃² ≤ 2^−119, each term is at most 2^−119 times the previous one
plus 2η, and n ≤ 2001; so S̃ ≤ 1.0001y + 10⁴η and 0 ≤ Hlo, Hhi ≤ 0.4y + 10⁴η < 2^−61, while
|Φ(x) − 1/2| ≤ φ(0)y < 2^−61.
*Assembly.* For x ≥ 0, lo = dn(RN(1/2 + Hlo)) ≤ 1/2 + Hlo and hi = up(RN(1/2 + Hhi)) ≥ 1/2 + Hhi (Lemma
6.1(a)); for x < 0 the same with 1/2 − Hhi, 1/2 − Hlo and Φ(x) = 1/2 − H. In (i) and (ii) Hlo ≤ H ≤ Hhi, which
gives the claim. In (iii), RN(1/2 ± H̃) = 1/2 for 0 ≤ H̃ < 2^−55, so [lo, hi] = [1/2 − 2^−54, 1/2 + 2^−53] ∋ Φ(x).
Capping Hlo, Hhi at 1/2 and clamping lo, hi to [0, 1] keep the enclosure. (Width: hi − lo < 2·10⁻¹².) ∎

**Lemma 6.4 (cos)** [P]. For every double x ∈ [0, 3.2], |`cosval`(x) − cos x| < 2.7·10⁻¹³. Hence `icos`(a)
contains cos ξ for every ξ ∈ a, for every interval a ⊆ [0, 3.14]; `f_V` calls it only with a ⊆ [0, 1.5709].
*Proof.* The loop forms T̃_k := RN(RN(−T̃_{k−1}x̃²)/((2k−1)2k)), k ≤ 24 (exact integer divisors ≤ 2256), so
T̃_k = T_k(1 + θ_k) up to underflow terms (< 10³η in all), T_k := (−1)^k x^{2k}/(2k)!, |θ_k| ≤ (1+u)^{3k} − 1 <
73u. The partial sums are bounded by Σ|T_k| ≤ e^x < 24.6 (C6), so the 24 additions err by < 24·24.61u in all;
the omitted terms total < 3.2^50/50! < 10⁻³⁹ (C6). Altogether < (73·24.6 + 24·24.61)u + 10⁻³⁰⁰ < 2.7·10⁻¹³. cos
decreases on [0, π] ⊃ [0, 3.14]; `icos` returns [RN(cosval(a.hi) − 10⁻¹²), RN(cosval(a.lo) + 10⁻¹²)] clamped to
[−1, 1], and 10⁻¹² − 2.7·10⁻¹³ − 3u > 0. ∎

**6.3 The integrals.**

**Lemma 6.5 (Taylor arithmetic, Simpson)** [P]. Let f be one of the integrands: `f_V` (variable ψ, parameter
t ∈ [a,b]) or the f_n of `f_all`, n ≤ 20 (variable x, parameter κ_u in the interval `kappa`). Let X = [x_0, x_1]
be a panel with double ends, h := x_1 − x_0 > 0, m := (x_0 + x_1)/2.
(a) Evaluated with the Taylor variable on X (degree 4), f yields intervals F_k such that f^{(k)}(ξ)/k! ∈ F_k for
every ξ ∈ X, every parameter value and k ≤ 4, unless `g_fail` is set; evaluated at an interval Y it yields an
enclosure of f over Y.
(b) For f ∈ C⁴[x_0, x_1]: ∫_{x_0}^{x_1} f ∈ (h/6)(f(x_0) + 4f(m) + f(x_1)) − (h⁵/2880)·[min f⁗, max f⁗].
(c) `integ` returns an interval containing ∫_{x_0}^{x_1} f, for every parameter value; `integrate` and the panel
loop of `K_lo` return enclosures of the integral over the union of their panels.
*Proof.* (a) Write f_k(ξ) := f^{(k)}(ξ)/k!. For functions analytic near ξ: (fg)_k = Σ_j f_j g_{k−j} (Leibniz);
q = a/b gives q_k = (a_k − Σ_{j≥1} b_j q_{k−j})/b_0; s = √a gives s_k = (a_k − Σ_{0<j<k} s_j s_{k−j})/(2s_0);
e = exp∘a gives k·e_k = Σ_{j=1}^k j a_j e_{k−j} (from e′ = a′e); F = Φ∘u gives k·F_k = Σ_{j=1}^k j u_j p_{k−j} with
p = φ∘u (from F′ = φ(u)u′); the variable has coefficients (ξ, 1, 0, 0, 0); cos has (cos ξ, −sin ξ, −cos ξ/2,
sin ξ/6, cos ξ/24), with sin ξ = cos(π/2 − ξ) and π/2 ∈ HALFPI (C5). The `ts_*` routines evaluate exactly these
recurrences in interval arithmetic, starting from 0-th coefficients that contain the values at every ξ ∈ X
(`iexp`, `iPhi`, `icos`, Lemmas 6.2–6.4). By Lemma 6.1(b) (inclusion monotonicity) every computed interval
contains the true coefficient at ξ, for all ξ ∈ X and all parameter values at once. The integrands are analytic
where they are used (cos ψ ≥ cos p > 0.49, c² + 8 > 0); a step undefined in interval arithmetic sets `g_fail`, and
its result is then not used. The same argument at degree 0 gives the range enclosure.
(b) g(τ) := ∫_{m−τ}^{m+τ} f − (τ/3)(f(m−τ) + 4f(m) + f(m+τ)) has g(0) = g′(0) = g″(0) = 0 and
g‴(τ) = −(τ/3)(f‴(m+τ) − f‴(m−τ)) = −(2τ²/3)D(τ), D(τ) := (f‴(m+τ) − f‴(m−τ))/(2τ) ∈ [min f⁗, max f⁗] (mean
value theorem). With s := h/2, Taylor's formula gives g(s) = ∫_0^s ((s−τ)²/2)g‴(τ)dτ = −(1/3)∫_0^s (s−τ)²τ²D(τ)dτ,
and ∫_0^s (s−τ)²τ²dτ = s⁵/30, s⁵/90 = h⁵/2880.
(c) `integ` intersects three enclosures of one integral: h·apriori (apriori contains the range of f), h·F_0, and
S − R with S := (h/6)(f_a + f_b + 4f_m) and R := (h⁵/120)F_4 (as F_4 ∋ f⁗(ξ)/24, R ⊇ (h⁵/2880)[min f⁗, max f⁗]);
here h is the interval x_1 ⊖ x_0 ∋ h, f_m is evaluated at the interval 0.5 ⊗ (x_0 ⊕ x_1) ∋ m, and f_a, f_b at the
double ends. A NaN never reaches the result, which is always contained in h·apriori. Bisection splits at a double
between the ends and adds the two enclosures. In `integrate` the nodes a + (b − a)·i/pieces, evaluated in
floating point (b for i = pieces), increase strictly (consecutive exact values differ by > 0.02, rounding errors are < 10⁻¹⁵), and
adjacent panels share their double end; the same holds for the 80 panels of `K_lo` on [−8, x_m] (spacing ≥ 0.1/80).
For f_V with the interval t: for each fixed t ∈ [a,b] all intervals above contain the values for that t. ∎

**Lemma 6.6 (V̄)** [P]. For doubles a < b with a ≥ 0 or b ≤ 0, `V_up1`(a,b) ≥ sup_{t∈[a,b]} V(t), and
`V_up`(a,b,4) ≥ sup_{[a,b]} V.
*Proof.* For t ∈ [a,b] let f_t(ψ) := A e^{−αt²}Φ(βt) if t ≥ 0 and A e^{−αt²}Φ(c_0At) if t ≤ 0; by Lemma 5.3,
V(t) = (3/π)∫_0^{π/3} f_t, plus Φ(t) − Φ(c_0t) if t ≤ 0. `f_V` evaluates exactly f_t with t ∈ [a,b],
t² ∈ `isqr`([a,b]), 6√2 − 8 ∈ C_KAP0, c_0 ∈ C_C0 (constants built by interval operations from 2 and √2).
π/3 < p < π/2 (c6; C5 checks 3p > π exactly), and on [0, p] we have 0 ≤ f_t ≤ A ≤ 1/3 < 0.3334 = apriori; so
∫_0^{π/3} f_t ≤ ∫_0^p f_t ≤ I.hi (Lemma 6.5, 48 panels) with I.hi ≥ 0, and (3/π)I.hi ≤ up(RN(C_3OVERPI.hi·I.hi)),
C_3OVERPI ∋ 3/π. For b ≤ 0, Φ(t) − Φ(c_0t) ≥ 0 lies in the interval difference d, and it equals (c_0 − 1)|t|φ(ξ)
with c_0t ≤ ξ ≤ t ≤ b ≤ 0, hence is ≤ (c_0 − 1)|a|φ(b) ≤ e.hi: `exp_pt` is called at RN(RN(−0.5b)·b), which is
within u·b²/2 < 10⁻¹⁶ of −b²/2 (Lemma 6.2). The minimum of the two upper bounds is one; the sum is rounded up. The
4 sub-slabs of `V_up` are formed by one expression for adjacent ends, start at a, end at b and increase, so they
cover [a,b], and none straddles 0. ∎

**Lemma 6.7 (P̲2)** [P]. For doubles −1.125 ≤ a < b ≤ 2, 0 ≤ `P2_lo`(a,b) ≤ P2(a,b).
*Proof.* *Lower sum.* u_0 := b, u_{j+1} := RN(u_j + du_j) with du_0 = 10⁻⁴ and du_{j+1} = RN(1.002·du_j) ≥ 10⁻⁴, so
the u_j increase strictly; the mass dn(RN(l_{j+1} − h_j)) is ≤ Φ(u_{j+1}) − Φ(u_j) (Lemma 6.3); a term is added only
if mass and K are > 0, and products and sums are rounded down. By Lemma 5.4 the result is
≤ Σ_j K_a(u_{j+1})(Φ(u_{j+1}) − Φ(u_j)) ≤ P2(a,b), provided `K_lo`(a,u) ≤ K_a(u) for u > b.
*K_lo.* It returns 0 ≤ K_a(u) on `g_fail`, if M or X_0 := κ_u/λ is enclosed with width > 5·10⁻¹⁵, or if
x_m ≤ −7.9. Otherwise let x* := min(M, X_0) and m_lo := min(M.lo, X0.lo); then m_lo ≤ x* ≤ m_lo + 5.0001·10⁻¹⁵ (the
two width tests). Since u > b > a and a < 2, M = 3(a − r_1u) ≤ 6 and X_0 = (3/√2)(a − 5u/6) < 4.3, so −7.9 < m_lo ≤ 6,
and x_m = dn(m_lo) is within 2^−50 below m_lo: 0 < x* − x_m < 6·10⁻¹⁵. For x ≤ x_m, x < M and κ_u − λx > 0, so
G_{a,u}(x) = 2Φ(κ_u − λx) − 1, which `f_all` evaluates (κ_u ∈ `kappa`); G_{a,u} = 0 on [x*, ∞). Lemma 6.5 encloses
J_n := ∫_{−8}^{x_m} φĥ_nG_{a,u} (n ≤ 20; `f_all` uses the recurrence of Lemma 5.5 with √n ∈ C_SQRTN[n]). The rest
of I_n is the integral over (−∞, −8) and over (x_m, x*); by Cauchy–Schwarz with ∫φĥ_n² = 1 and 0 ≤ G_{a,u} ≤ 1,
each piece is at most (∫φ over the piece)^{1/2}, so |I_n − J_n| ≤ √Φ(−8) + √(6·10⁻¹⁵φ(0)) ≤ √(φ(8)/8) +
√(0.4·10⁻¹⁴) < 2.53·10⁻⁸ + 6.33·10⁻⁸ < 0.99·10⁻⁷ ≤ EPS_TAIL (C6; side condition c5 checks it again with outward
rounding). So J_n ⊕ [−EPS_TAIL, EPS_TAIL] ∋ I_n. By Lemma 5.5 with N = 20, K_a(u) ≥ Σ_{n≤20}(−1/2)ⁿI_n² − 2^−21·I_0;
the program encloses the sum in interval arithmetic (the weights 2^−n are exact), takes its lower end, subtracts
up(2^−21·I0hi) with I0hi ≥ I_0, rounds down, and replaces a negative result by 0 ≤ K_a(u). ∎

**6.4 Decision, cover and run.**

**Lemma 6.8 (the last line)** [P]. If `edcert full ED 13750000` (default parameters du0 = 10⁻⁴, growth 1.002,
P = 80) prints the last line `RESULT: (ED) CERTIFIED for gamma = 13750000/10^8` (it then exits with status 0),
then G(t) ≤ 11/80 for every real t, i.e. Proposition C holds.
*Proof.* The line is printed iff, at the end of `full`: (1) the side conditions c1–c6 hold; (2) for
k = −1152, …, 2047 in this order, `certify` accepted every leaf of [a_k, b_k] := [k/1024, (k+1)/1024] (an integer
divided by a power of 2: exact) and a_k equals the preceding b; (3) 3200 slabs were processed, a_{−1152} = −1.125
and the last b is 2. `certify` bisects at RN((a+b)/2), the exact midpoint (all ends are multiples of 2^−26 of
modulus ≤ 2), so the leaves of a slab tile it, and a slab with a leaf open at depth 16 clears the verdict. A leaf
[a,b] is accepted only if bound ≤ γ_lo, where γ_lo is the lower end of `idiv`(13750000, 10⁸), so γ_lo ≤ 11/80, and
bound ≥ V̄ + P3up(b)/3 − P̲2 (each sum and difference rounded up, Lemma 6.1(a); P̲2 := 0 if `P2_lo` was not
called), with V̄ := `V_up`(a,b,4) ≥ sup_{[a,b]}V (Lemma 6.6), P̲2 ≤ P2(a,b) (Lemma 6.7), and P3up(b) the upper end
of an interval enclosure of c_1·b·(1 − e^{−c_2b²}) (0 for b ≤ 0) with c_1, c_2 the doubles of 0.02434 and 0.0589,
which satisfy Lemma 5.6 by c3, c4 (comparisons of doubles are exact). By Lemma 5.8, G ≤ 11/80 on every leaf,
hence on [−1.125, 2]. Tails: c1 states `Phi_pt`(−1.125).hi ≤ γ_lo, so for t ≤ −1.125, G(t) ≤ Φ(t) ≤ Φ(−1.125)
≤ 11/80 (Lemma 5.7); c2 states up(up(10h)/3) ≤ γ_lo with h ≥ Φ(−2), so for t ≥ 2, G(t) ≤ (10/3)Φ(−t) ≤ 11/80. A
NaN cannot lead to acceptance: comparisons with NaN are false, and `V_up1`, `P3_up`, `P2_lo` return finite doubles
(Lemma 6.1(c); `integ` stays in h·apriori). An `INTERNAL ERROR` (exit 4) prints no RESULT line. ∎

*Run.* Compile with `gcc -O2 -std=c11 -ffp-contract=off -fno-fast-math -o edcert edcert.c -lm` and run

    ./edcert full ED 13750000                (one process, about 25 core-minutes)

It prints the side-condition line, one line per base slab (ends in hexadecimal, leaves, P2 evaluations, largest
accepted bound, OK/FAIL), a summary line and the RESULT line of Lemma 6.8. The same slab lines are produced by
`./edcert slab ED 13750000 1024 k0 k1` on disjoint ranges covering −1152 ≤ k < 2048 (exit status 0 iff all are
OK); each line is deterministic and does not depend on the split, so a parallel run must check the conditions
(1)–(3) of Lemma 6.8 itself. The exact checks C5 and C6 cited in §6.2–§6.3 are run by
`python3 certify_small.py --quick` (seconds; last line `QUICK OK`).
*Recorded run* (2026-11-13, compute host, aarch64 GNU/Linux, `gcc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0`, the
flags above) of the edcert.c with SHA-256 f44c8cc9304605c7…, which differs from the supplied file only in comments,
in rounding the sum of side condition c5 upward, and in the exit status of `slab` (formerly always 0): a driver
(not supplied) ran `check`, `selftest` and `slab ED 13750000 1024 k k+8 1e-4 1.002 80` for the 400 blocks of 8
slabs in 18 parallel processes and checked (1)–(3). Output: side conditions OK; 3200 base slabs, every one OK;
3214 leaves; 424 evaluations of P̲2; largest certified bound 0.1374996897 (slab [43/1024, 44/1024]); cover of
[−1.125, 2] complete; last line `CERTIFIED gamma_c <= 0.13750000`. Ten of these slab lines (k = −1152, −1151, −2,
−1, 0, 42, 43, 44, 2046, 2047) recomputed with the supplied file (laptop, arm64, Apple clang 21) are
byte-identical, and its `check ED 13750000` and `selftest` pass. A run for γ = 0.13748 also succeeded; it is not
used.

**6.5 Independent cross-check** [C, weaker constant]. `certify_small.py` (Python standard library only, its own
interval arithmetic and its own enclosures of exp and Φ, no library function in any bound) re-proves G(t) ≤ γ for
all t with a different method: V̄ by left Riemann sums of the τ-form of Lemma 5.3 (whose integrand bound is
monotone in τ, §5.3), and P̲2 without Mehler's formula, by a lower Riemann sum on a lattice in which x_2 =
−x_1/2 + (√3/2)y with x_1, y independent (G_{a,u}(x_1) is nonincreasing in x_1, E_yG_{a,u}(x_2) nondecreasing in
x_1, G_{a,u}(x_2) nonincreasing in y; on the lattice x_k = x_0 + k√3h, y_l = √3x_0 + lh, u_i = b + i(√6/5)h every
H-argument is κ_b − λx_0 + J√2h, J ∈ Z, and every indicator is J ≥ cut_i, so the double sum is a running
convolution). Results: γ = 0.1380 certified in 11 s; γ = 0.1376 in 40 s (one core). It also checks (C1) and (C2),
the witnesses of §7 (C4), the constants of `edcert.c` (C5) and the rational inequalities of §6.2–§6.3 (C6), all in
exact integer or rational arithmetic.

## 7. Proofs of Theorems 2 and 1

Fix R ≥ 4, ε ∈ (0, 1/2), the field Y′ of §2, and order V by L^{ED}(Y′) (nondecreasing, ties by a fixed
labelling); call the ordering σ. Put S_t := {v : Y′_v < t} and S2(t) := D(E(S_t)) = {v : L^{ED}_v(Y′) < t}
(Lemma 4.1). Let Ω_0 be the event of Lemma 2.1(c) (probability 1).

**Lemma 7.1 (ties)** [P]. On Ω_0, cw(σ) ≤ 30 + sup_t cut(S2(t)).
*Proof.* Max, median and min return one of their arguments, so L^{ED}_v = Y′_x for some x ∈ B(v,2). For a proper
prefix P with last vertex u let τ := L^{ED}_u; then S2(τ) ⊆ P ⊆ {L^{ED} ≤ τ}. On Ω_0, τ = Y′_x for a unique x and
every vertex with L^{ED} = τ lies in B(x,2), which has at most 10 vertices (W3). So |P∖S2(τ)| ≤ 10 and, by (W4),
cut(P) ≤ cut(S2(τ)) + 30. ∎

**Lemma 7.2 (one threshold)** [P + C]. For every vertex v and every fixed t,
E F_v(S_t) ≤ G(t) + K(R) + 8ε² ≤ 11/80 + K(R) + 8ε², K(R) := 64.93/(R+1)².
*Proof.* X_x := Y′_{π(x)} (x ∈ Ω) is a centred Gaussian vector with unit variances, and F_v(S_t) = F(s(X)). For
x ≠ y, Cov(X_x, X_y) = (1−ε²)BC(πx, πy) + ε²1{πx = πy} ≥ (1−ε²)r_{d(x,y)}(R) by Lemmas 2.1–2.3. Let X^L be the
same construction on the tree T_v (Y on T_v is a finite sum at each vertex), restricted to Ω: covariance
(1−ε²)r_{d(x,y)}(R). Lemma 3.2(a) gives E F(s(X)) ≤ E F(s(X^L)). Apply Lemma 3.2(b) to X^L and W (Lemma 5.1):
μ = 1/3 (Lemma 4.3(b)), 0 ≤ (1−ε²)r_d ≤ r_d ≤ w_d < 1, and w_d − (1−ε²)r_d ≤ C_dθ² + ε²w_d (Lemma 2.3). The ten
positions have 9, 12, 12, 12 pairs at distances 1, 2, 3, 4, and √(1 − w_d²) = 1/3, √11/6, √2/2, √95/12. So

    E F(s(X^L)) − G(t) ≤ (θ²/(3·2π))·[9C_1·3 + 12C_2·6/√11 + 12C_3·√2 + 12C_4·12/√95]
                          + ε²·45·(1/3)·max_d w_d/(2π√(1−w_d²))
                      = (π/(3(R+1)²))·[9√2/2 + 48/√11 + 19 + 216/√95] + ε²·15√2/π
                      < 64.93/(R+1)² + 8ε²            (N2; max_d w_d/(2√(1−w_d²)) = √2 at d = 1).

Finally G(t) ≤ 11/80 (Proposition C). ∎

Fix also an integer M ≥ 2, T := 3, δ := 2T/(M−1), τ_j := −T + (j−1)δ (1 ≤ j ≤ M; τ_M = T), Φ_t := Σ_v F_v(S_t),
n_j := #{u : Y′_u ∈ [τ_j, τ_{j+1})} (1 ≤ j < M), n_− := #{u : Y′_u < −T}, n_+ := #{u : Y′_u ≥ T}.

**Lemma 7.3 (all thresholds)** [P]. For every real t:
cut(S2(t)) ≤ max{ max_{1≤j<M} (Φ_{τ_j} + (16/3)n_j), 12n_−, 12n_+ }.
*Proof.* *t ∈ [τ_j, τ_{j+1}):* cut(S2(t)) ≤ Φ_t (Lemma 4.3(a)). S_t and S_{τ_j} differ exactly at the u with
τ_j ≤ Y′_u < t. A vertex u is π(x) for exactly 10 pairs (v, x), x ∈ Ω (W2), of which one has x = o; changing the
coordinates one at a time, Lemma 4.3(d) gives |Φ_t − Φ_{τ_j}| ≤ (7/3 + 9·1/3)·n_j = (16/3)n_j.
*t < −T:* S2(t) ⊆ D(S_t) ⊆ S_t ∪ {v : some dart at v has its head in S_t}, so |S2(t)| ≤ 4|S_t| ≤ 4n_− and
cut(S2(t)) ≤ 12n_− (W4). *t ≥ T:* v ∉ S2(t) forces v ∉ E(S_t), i.e. v ∉ S_t or two darts at v have heads outside
S_t; so |V∖S2(t)| ≤ 4|V∖S_t| ≤ 4n_+ and cut(S2(t)) = cut(V∖S2(t)) ≤ 12n_+. ∎

**Lemma 7.4 (moments)** [P]. E n_j ≤ Dδ/√(2π); E n_± = DΦ(−3); Var Φ_t ≤ (676/3)·4^R·D for each fixed t;
Var n_j, Var n_± ≤ (3/4)·4^R·D.
*Proof.* Y′_u ~ N(0,1) and φ ≤ 1/√(2π). F_v(S_t) is a function of Y′ on B(v,2), hence (Lemma 2.1(b)) of g on
B(v, R+2) and ξ on B(v,2); so F_u(S_t), F_v(S_t) are independent unless d(u,v) ≤ 2R+4, which holds for at most
3·2^{2R+4} − 2 < 48·4^R vertices u (W3); and |Cov| ≤ (13/3)²/4 (Lemma 4.3(c)). So Var Φ_t ≤ D·48·4^R·169/36. The
indicator 1{Y′_u ∈ I} depends on g on B(u,R) and ξ_u: at most 3·4^R dependent partners, |Cov| ≤ 1/4. ∎

**Proof of Theorem 2.** Let λ_1 := √(4M·(676/3)·4^R·D) and λ_2 := √(4M·(3/4)·4^R·D) = √3·2^R√(MD). By Chebyshev
each of the 2M events {Φ_{τ_j} ≥ EΦ_{τ_j} + λ_1}, {n_j ≥ En_j + λ_2} (1 ≤ j < M), {n_± ≥ En_± + λ_2} has
probability ≤ 1/(4M), so with probability ≥ 1/2 none occurs; intersect with Ω_0 and fix such an outcome. By
Lemmas 7.1–7.4, for all t,

    cut(S2(t)) < max{ D(11/80 + K(R) + 8ε²) + λ_1 + (16/3)(Dδ/√(2π) + λ_2),  12(DΦ(−3) + λ_2) }.

The first entry is the larger: 12Φ(−3) < 0.0178 < 11/80 (N6) and 12λ_2 < λ_1 + (16/3)λ_2 (N3). By (N3), (N4),
λ_1 + (16/3)λ_2 ≤ 39.27·2^R√(MD) and (16/3)Dδ/√(2π) = 32D/((M−1)√(2π)) ≤ 12.77D/(M−1). With Lemma 7.1,
cw(K) ≤ cw(σ) ≤ 30 + D(11/80 + K(R) + 8ε²) + 12.77D/(M−1) + 39.27·2^R√(MD). The left side does not depend on ε;
let ε → 0. ∎

**Proof of Theorem 1.** By (W4), cw(K) ≤ 3D/2 = γ_cD + (109/80)D always; this settles D < 2^40. Let D ≥ 2^40,
Λ := log₂D ≥ 40, R := ⌊Λ/3⌋ − 1 ≥ 12 and M := ⌈D^{1/9}⌉ + 1. Then R + 1 > (Λ − 3)/3, so K(R) < 9·64.93/(Λ−3)² <
585/(Λ−3)² (N5); 2^R ≤ 2^{Λ/3 − 1} = D^{1/3}/2; and D^{1/9} ≥ 2^{40/9} > 2 gives M ≤ D^{1/9} + 2 ≤ 2D^{1/9},
M − 1 ≥ D^{1/9}. Hence 39.27·2^R√(MD) ≤ 39.27·(√2/2)·D^{1/3+1/18+1/2} < 27.77D^{8/9} (N3), 12.77D/(M−1) ≤
12.77D^{8/9}, 30 < 0.46·2^{35} ≤ 0.46D^{8/9}, and Theorem 2 gives cw(K) ≤ γ_cD + 585D/(Λ−3)² + 41D^{8/9}
(N4). Together with the trivial bound, cw(K) ≤ γ_cD + h_c(D).
*Properties of h_c.* h_c ≥ 0. f(D) := 585D/(log₂D − 3)² + 41D^{8/9} is increasing on [2^40, ∞): the derivative of
x/(log₂x − 3)² has the sign of (log₂x − 3) − 2/ln 2 > 0. A minimum of nondecreasing functions is nondecreasing,
so h_c is nondecreasing on [1, 2^40) and on [2^40, ∞); at the junction f(2^40) > (109/80)·2^40 (N7), so
h_c(2^40) = (109/80)·2^40 ≥ h_c(2^40 − 1). Finally h_c(D)/D ≤ 585/(log₂D − 3)² + 41D^{−1/9} → 0. ∎

**Numerical witnesses** (exact rational comparisons after inserting the stated rational bounds;
`certify_small.py` (C4) checks each with `fractions.Fraction`):
- (N1) 1.41421² < 2 < 1.41422²; 3.3166² < 11; 9.7467² < 95; 3.14159 < π < 3.1416 (π enclosed by
  Machin's formula in exact rationals).
- (N2) 9·1.41422/2 + 48/3.3166 + 19 + 216/9.7467 < 61.998 and 3.1416·61.998/3 < 64.93; for the ε² term,
  45·(1/3)·√2/π < 8.
- (N3) 4·676/3 < 30.03², so λ_1 ≤ 30.03·2^R√(MD); 3 < 1.7321²; 30.03 + (16/3)·1.7321 < 39.27;
  (12 − 16/3)²·3 = 400/3 < 4·676/3, so (12 − 16/3)λ_2 < λ_1; 39.27·1.41422/2 < 27.77.
- (N4) 32² < 12.77²·2·3.14159, so 32/√(2π) < 12.77; 27.77 + 12.77 + 0.46 = 41; 30 < 0.46·2^{35}.
- (N5) 9·64.93 = 584.37 < 585.
- (N6) e^{4.5} > Σ_{k<30} 4.5ᵏ/k! > 90 and 2.5066² < 2·3.14159, so 12Φ(−3) ≤ 4φ(3) < 4/(90·2.5066) < 0.0178
  (Φ(−T) ≤ φ(T)/T).
- (N7) 2^40 < 22⁹, so 41·2^{−40/9} > 41/22 > 1.3625 = 109/80.
- (N8) 1 + 1/(2·11/80) = 51/11 (used in `proof.md` §6.2).
