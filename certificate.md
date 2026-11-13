# The certificate of Proposition C: sup_t G_d(t) <= 2452706089845207/18014398509481984

**Status.** This file is the companion of `cutwidth.md` for its Proposition C. It proves: *if the output of the
program `certify.py` (which runs in a few seconds) has "certified": true, then
G_d(t) ≤ γ_d := 2452706089845207/18014398509481984 = 2452706089845207·2^{−54} (the binary64 number
0x1.16d72467283aep-3 = 0.13615253867922433…) for every real t.* Labels as in `cutwidth.md`: [P] = proved here from undergraduate
analysis and probability (§1.0 of `cutwidth.md`) and the items of `cutwidth.md` named below; [C] = checked by
`certify`; [S] = not used in any proof.

*Used from `cutwidth.md`:* the construction and notation of §5.1 (U, ζ, δ_i, f_i, x_i, r_1 = 2√2/3, the positions
W_x); the definitions of §5.2 (G_d, V, P4, P2, P3); Lemma 5.2 (G_d = Φ − P4 − (3/2)P2 + (1/2)P3); Lemma 5.6 (P3 = 0
for t ≤ 0, P3(t) ≤ P3up(t) := c_1t(1 − e^{−c_2t²}) for t > 0, P3up increasing, for any c_1 ≥ (1/r_1 − 1)/√(2π) and
c_2 ≥ 18(1 − r_1)²); Lemma 5.7 (tails: G_d(t) ≤ Φ(t) for t ≤ 0, G_d(t) ≤ (7/2)Φ(−t) for all t); the notation
Tri(h) := {z ∈ R² : ⟨z, f_i⟩ < h, i = 1, 2, 3} of §5.3. Lemma 5.1 is the content of check (C2).
*Not used any more:* formula (5.1) and Lemma 5.3 (the closed form of V), Lemma 5.4 (the monotone lower sums for
P2), Lemma 5.5 (Mehler), Lemma 5.8 (the old leaf bound).

*Notation.* φ, Φ: standard normal density and distribution function; γ_n: the standard Gaussian measure on Rⁿ;
H(z) := max(0, 2Φ(z) − 1); λ := 2√6/3; c_0 := 1/r_1 = 3/(2√2); T(h) := γ_2(Tri(h)) (= 0 for h ≤ 0).

## 5. Additions to §5 of cutwidth.md

**5.6 Log-concavity.**

**Theorem PL (Prékopa 1971/1973, Leindler 1972)** [P]. Let 0 < s < 1 and let f, g, h : Rⁿ → [0, ∞] be measurable
with h((1−s)x + sy) ≥ f(x)^{1−s}·g(y)^s for all x, y ∈ Rⁿ. Then ∫h ≥ (∫f)^{1−s}·(∫g)^s.

*Proof.* (0) *Reductions.* If the claim holds for the pairs (min(f, N)·1{|x| ≤ N}, min(g, N)·1{|y| ≤ N}), N = 1, 2, …
(which satisfy the hypothesis with the same h), it holds for (f, g) by monotone convergence. So let f, g be
bounded with bounded support; if ∫f = 0 or ∫g = 0 there is nothing to prove, so let both integrals be positive.
(1) *Sums of compact sets on the line.* If K_1, K_2 ⊂ R are nonempty and compact, then |K_1 + K_2| ≥ |K_1| + |K_2|
(|·| Lebesgue measure; K_1 + K_2 is compact): translating, let max K_1 = 0 = min K_2; then K_1 = K_1 + 0 and
K_2 = 0 + K_2 are subsets of K_1 + K_2 that meet only in the point 0.
(2) *n = 1.* Let a := sup f > 0, b := sup g > 0 and replace (f, g, h) by (f/a, g/b, h/(a^{1−s}b^s)): hypothesis and
conclusion are unchanged, and now sup f = sup g = 1. For 0 < μ < 1 the sets F_μ := {f ≥ μ}, G_μ := {g ≥ μ} are
nonempty and measurable, and if x ∈ F_μ, y ∈ G_μ then h((1−s)x + sy) ≥ μ^{1−s}μ^s = μ; so {h ≥ μ} ⊇ (1−s)K_1 + sK_2
for all nonempty compact K_1 ⊆ F_μ, K_2 ⊆ G_μ, and by (1) |{h ≥ μ}| ≥ (1−s)|K_1| + s|K_2|. Taking the supremum
over K_1, K_2 (inner regularity of Lebesgue measure): |{h ≥ μ}| ≥ (1−s)|F_μ| + s|G_μ|. Integrate over μ ∈ (0, 1)
(layer-cake formula; f, g ≤ 1): ∫h ≥ ∫_0^1 |{h ≥ μ}|dμ ≥ (1−s)∫f + s∫g ≥ (∫f)^{1−s}(∫g)^s, the last step being the
inequality of the weighted arithmetic and geometric means.
(3) *Induction on n.* Write x = (x_1, x′) ∈ R × R^{n−1} and F(x_1) := ∫f(x_1, x′)dx′, G(y_1) := ∫g(y_1, y′)dy′,
H̃(z_1) := ∫h(z_1, z′)dz′ (measurable by Tonelli's theorem; F, G bounded by (0)). Fix x_1, y_1 and
z_1 := (1−s)x_1 + sy_1: the functions f(x_1, ·), g(y_1, ·), h(z_1, ·) on R^{n−1} satisfy the hypothesis, so by the
induction hypothesis H̃((1−s)x_1 + sy_1) ≥ F(x_1)^{1−s}G(y_1)^s. By the case n = 1 applied to F, G, H̃ and Tonelli,
∫h = ∫H̃ ≥ (∫F)^{1−s}(∫G)^s = (∫f)^{1−s}(∫g)^s. ∎

**Corollary PL** [P]. Let X be a centred Gaussian vector in R^k (its covariance may be singular), let
K ⊆ R^k × R be a convex Borel set, and p(t) := P[(X, t) ∈ K]. Then for t_0, t_1 ∈ R, 0 ≤ θ ≤ 1 and
t = (1−θ)t_0 + θt_1: p(t) ≥ p(t_0)^{1−θ}·p(t_1)^θ (with 0⁰ := 1).

*Proof.* X = BZ in distribution for a k × n matrix B and a standard Gaussian vector Z in Rⁿ (§1.0), and
K′ := {(z, t) ∈ Rⁿ × R : (Bz, t) ∈ K} is convex and Borel (preimage under a linear map) with p(t) = γ_n(K′_t),
K′_t := {z : (z, t) ∈ K′}. For θ ∈ {0, 1} there is nothing to prove. Let 0 < θ < 1 and f := φ_n·1_{K′_{t_0}},
g := φ_n·1_{K′_{t_1}}, h := φ_n·1_{K′_t}, φ_n(z) = (2π)^{−n/2}e^{−|z|²/2}. If x ∈ K′_{t_0} and y ∈ K′_{t_1} then
((1−θ)x + θy, t) = (1−θ)(x, t_0) + θ(y, t_1) ∈ K′, and |(1−θ)x + θy|² ≤ (1−θ)|x|² + θ|y|² (convexity of the square
of the norm) gives φ_n((1−θ)x + θy) ≥ φ_n(x)^{1−θ}φ_n(y)^θ; so h((1−θ)x + θy) ≥ f(x)^{1−θ}g(y)^θ, also when x ∉ K′_{t_0}
or y ∉ K′_{t_1} (the right side is then 0). Theorem PL with s = θ gives the claim. ∎

**5.7 The leaf bound, the quadrature rule, and the two integrals.**

**Lemma 5.9 (log-concavity in t; the leaf bound)** [P]. (a) For t_0, t_1 ∈ R, 0 ≤ θ ≤ 1 and
t = (1−θ)t_0 + θt_1: P4(t) ≥ P4(t_0)^{1−θ}P4(t_1)^θ and P2(t) ≥ P2(t_0)^{1−θ}P2(t_1)^θ.
(b) The function T(h) := γ_2(Tri(h)) (h ∈ R; T(h) = 0 for h ≤ 0) is nondecreasing and satisfies
T((1−θ)h_0 + θh_1) ≥ T(h_0)^{1−θ}T(h_1)^θ; in particular log T is concave on (0, ∞).
(c) Let a < b with a ≥ 0 or b ≤ 0, w := b − a, m := (a+b)/2, and let 0 < p ≤ P4(a), 0 < q ≤ P4(b),
0 < p′ ≤ P2(a), 0 < q′ ≤ P2(b). Put g := √(pq), L := ln(q/p), g′ := √(p′q′), L′ := ln(q′/p′), and
c_Φ := 0 if a ≥ 0, c_Φ := |a|·φ(0)·w²/8 if b ≤ 0. Then for every t ∈ [a, b]

    G_d(t) ≤ Φ(m) + c_Φ + P3up(b)/2 − g − (3/2)g′ + (1/2)·|φ(m)·w − g·L − (3/2)·g′·L′|,             (5.2)

and also (for any 0 ≤ p ≤ P4(a), 0 ≤ q ≤ P4(b), 0 ≤ p′ ≤ P2(a), 0 ≤ q′ ≤ P2(b))

    G_d(t) ≤ Φ(b) − min(p, q) − (3/2)·min(p′, q′) + P3up(b)/2.                                          (5.3)

(5.2) remains true if g′, L′ are replaced by min(p′, q′), 0 (for any 0 ≤ p′ ≤ P2(a), 0 ≤ q′ ≤ P2(b)).
(P3up(b) := 0 for b ≤ 0.)

*Proof.* (a) By §5.1 every W_x is a linear form in the centred Gaussian vector X := (U, ζ_1, ζ_2, δ_1, δ_2, δ_3).
P2(t) = P[(X, t) ∈ K] with K := {(x, t) : W_0 ≥ t; W_1, W_2, W_{11}, W_{12}, W_{21}, W_{22} < t}, and P4(t) = P[(X, t) ∈ K″]
with K″ := {(x, t) : W_0, W_1, W_2, W_3 < t} (the W_x read as linear forms in x). K and K″ are intersections of
half-spaces of R⁶ × R (each condition is a linear inequality in (x, t)), hence convex and Borel. Corollary PL.
(b) Tri(h) ⊆ Tri(h′) for h ≤ h′. T(h) = P[(ζ, h) ∈ K‴] with K‴ := {(z, h) ∈ R² × R : ⟨z, f_i⟩ − h < 0, i = 1, 2, 3},
an intersection of half-spaces; Corollary PL. Where T > 0 this says that log T is concave.
(c) Write t = a + θw, 0 ≤ θ ≤ 1. By (a) and monotonicity of (x, y) ↦ x^{1−θ}y^θ on [0, ∞)²,
P4(t) ≥ p^{1−θ}q^θ = g·e^{(θ−1/2)L} ≥ g·(1 + (θ − 1/2)L) (as e^x ≥ 1 + x), and likewise
P2(t) ≥ g′(1 + (θ − 1/2)L′); also P2(t) ≥ min(P2(a), P2(b)) ≥ min(p′, q′) and P4(t) ≥ min(p, q), since
x^{1−θ}y^θ ≥ min(x, y). By Taylor's formula Φ(t) = Φ(m) + φ(m)(t − m) + Φ″(ξ)(t − m)²/2 with ξ between m and t
and Φ″(ξ) = −ξφ(ξ): if a ≥ 0 then ξ ≥ 0 and Φ″(ξ) ≤ 0; if b ≤ 0 then 0 ≤ −ξ ≤ |a|, φ(ξ) ≤ φ(0) and
(t − m)² ≤ w²/4; in both cases Φ(t) ≤ Φ(m) + φ(m)w(θ − 1/2) + c_Φ. Finally P3(t) ≤ P3up(t) ≤ P3up(b) (Lemma 5.6;
P3 = 0 for t ≤ 0). Insert into G_d = Φ − P4 − (3/2)P2 + P3/2 (Lemma 5.2):

    G_d(t) ≤ [Φ(m) + c_Φ + P3up(b)/2 − g − (3/2)g′] + (θ − 1/2)·[φ(m)w − gL − (3/2)g′L′],

and |θ − 1/2| ≤ 1/2 gives (5.2). (5.3) follows from Φ(t) ≤ Φ(b) and the min-bounds. ∎

**Lemma 5.10 (geometric-mean rule)** [P]. Let B = Π_{d=1}^n [z_d⁰, z_d⁰ + w_d] ⊂ Rⁿ be a box and f = e^{−q}·g on B,
where q is a real polynomial of degree ≤ 2 in z_1, …, z_n with A_d := ∂²q/∂z_d² ≥ 0 (constants), and g : B → [0, ∞)
is measurable and such that either g > 0 on B and log g is concave on B, or g vanishes at some corner of B. Then,
with the product over the 2ⁿ corners c of B,

    ∫_B f(z) dz ≥ vol(B) · (Π_c f(c))^{2^{−n}} · Π_{d=1}^n (1 + A_d·w_d²/12).

*Proof.* If g vanishes at a corner the right side is 0. Otherwise parametrise z_d = z_d⁰ + w_dθ_d, θ ∈ [0,1]ⁿ, and
for a function F on B write ML[F](θ) := Σ_c λ_c(θ)F(c), λ_c(θ) := Π_d (θ_d if c_d = z_d⁰ + w_d, else 1 − θ_d), the
multilinear interpolant of the corner values (λ_c ≥ 0, Σ_c λ_c = 1).
(i) If F is affine in each coordinate separately (a polynomial in which no variable occurs squared), then
ML[F] = F: both sides are affine in each θ_d and agree at the corners, and such a function is determined by its
corner values (induction on n). For F = z_d²: z_d² − ML[z_d²] = (z_d⁰ + w_dθ_d)² − (1−θ_d)(z_d⁰)² − θ_d(z_d⁰ + w_d)²
= −w_d²θ_d(1 − θ_d). As q − Σ_d (A_d/2)z_d² contains no squared variable, −q = ML[−q] + Σ_d (A_dw_d²/2)·θ_d(1 − θ_d).
(ii) log g ≥ ML[log g] on B: a function concave in each coordinate separately satisfies
F(θ_1, θ′) ≥ (1 − θ_1)F(0, θ′) + θ_1F(1, θ′), and F(0, ·), F(1, ·) are again concave in each coordinate; induction.
(iii) Hence f ≥ exp(ML[log f])·Ψ on B, Ψ(θ) := Π_d ψ_d(θ_d), ψ_d(s) := e^{(A_dw_d²/2)s(1−s)}, and
∫_B f ≥ vol(B)·I, I := ∫_{[0,1]ⁿ} exp(ML[log f](θ))Ψ(θ)dθ. For σ ∈ {0,1}ⁿ let ρ_σ be the map that replaces θ_d by
1 − θ_d for the d with σ_d = 1; it preserves Lebesgue measure on the cube and Ψ, and λ_c(ρ_σθ) = λ_{σc}(θ), where
σc is the corner obtained from c by switching the coordinates d with σ_d = 1. So
I = 2^{−n}Σ_σ ∫exp(ML[log f](ρ_σθ))Ψ(θ)dθ ≥ ∫exp(2^{−n}Σ_σ ML[log f](ρ_σθ))Ψ(θ)dθ (arithmetic ≥ geometric mean),
and 2^{−n}Σ_σ ML[log f](ρ_σθ) = 2^{−n}Σ_c log f(c)·Σ_σ λ_{σc}(θ) = 2^{−n}Σ_c log f(c). Therefore
I ≥ (Π_c f(c))^{2^{−n}}·Π_d ∫_0^1 ψ_d, and ∫_0^1 ψ_d ≥ ∫_0^1 (1 + (A_dw_d²/2)s(1−s))ds = 1 + A_dw_d²/12. ∎

**Lemma 5.11 (P4 through the triangle function)** [P].
(a) For h > 0: T(h) = ∫_{−2h}^{h} φ(z)·H((z + 2h)/√3) dz, and T(h) ≥ 1 − 3Φ(−h).
(b) P4(t) = ∫_{−∞}^{u*} φ(u)·T(3(t − r_1u)) du, u* = min(t, c_0t); for every t the function u ↦ T(3(t − r_1u)) is
≥ 0, nonincreasing, and log-concave on the half-line where it is positive.
(c) H is nondecreasing, and concave on [0, ∞).
*Proof.* (a) f_3 = (1, 0), f_1 = (−1/2, √3/2), f_2 = (−1/2, −√3/2): z ∈ Tri(h) iff z_1 < h and
−z_1/2 ± (√3/2)z_2 < h, i.e. z_1 < h and |z_2| < (2h + z_1)/√3. Given z_1 the second condition has probability
H((2h + z_1)/√3) (0 if z_1 ≤ −2h). The complement of Tri(h) is the union of the three half-planes ⟨z, f_i⟩ ≥ h,
each of measure Φ(−h). (b) ζ is independent of U. Given U = u: W_i = r_1u + x_i/3 < t for i = 1, 2, 3 iff
⟨ζ, f_i⟩ < 3(t − r_1u) for all i, i.e. ζ ∈ Tri(3(t − r_1u)); so P4(t) = ∫_{−∞}^{t} φ(u)T(3(t − r_1u))du. The
integrand vanishes unless t − r_1u > 0, i.e. u < t/r_1 = c_0t, so the upper limit may be replaced by
u* = min(t, c_0t). T is nondecreasing and r_1 > 0, so u ↦ T(3(t − r_1u)) is nonincreasing; it is log-concave
where positive by Lemma 5.9(b), the argument being affine in u.
(c) H′ = 2φ ≥ 0 on (0, ∞), H″(z) = −2zφ(z) ≤ 0 for z ≥ 0, H = 0 on (−∞, 0], H continuous. ∎

**Lemma 5.12 (P2 on an orthant)** [P]. For u, t ∈ R put M := 3(t − r_1u) and c(u) := √3·u − (2√6 − 2√3)·t. Then

    P2(t) = ∫_t^∞ ∫_0^∞ ∫_0^∞ F_t(u, v_1, v_2) dv_2 dv_1 du,   F_t := e^{−q}·g,   where
    q(u, v_1, v_2) := u²/2 + (2/3)(x_1² + x_1x_2 + x_2²) + ln(√(2π)·√3·π),   x_i := M − v_i,
    g(u, v_1, v_2) := H(c(u) + λv_1)·H(c(u) + λv_2).

q is a quadratic polynomial in (u, v_1, v_2) with ∂²q/∂u² = 33 and ∂²q/∂v_i² = 4/3; g ≥ 0, and on every box on
whose corners g > 0, g is positive and log g is concave. Explicitly,

    F_t(u, v_1, v_2) = (√(2π)√3π)^{−1}·exp(−u²/2 − 2M²)·Π_{i=1,2}[exp(−(2/3)v_i² + 2Mv_i)·H(c(u) + λv_i)]·exp(−(2/3)v_1v_2).

*Proof.* Condition on (U, ζ) = (u, ζ). W_i = r_1u + x_i/3 < t iff x_i < M. W_{i1}, W_{i2} = (5/6)u + (√2/3)x_i ± δ_i
are both < t iff |δ_i| < t − (5/6)u − (√2/3)x_i; as √12·δ_i is standard normal and √12·(√2/3) = λ, this has
conditional probability H(κ_u − λx_i), κ_u := √12(t − 5u/6); δ_1, δ_2 are independent of each other and of (U, ζ).
(x_1, x_2) is
independent of U, bivariate normal with unit variances and correlation −1/2, so its density is
(2π·√(3/4))^{−1}exp(−(x_1² + x_1x_2 + x_2²)/(2·(3/4))) = (√3π)^{−1}exp(−(2/3)(x_1² + x_1x_2 + x_2²)). Hence
P2(t) = ∫_t^∞ φ(u)∫∫_{x_1, x_2 < M} (√3π)^{−1}e^{−(2/3)(x_1²+x_1x_2+x_2²)}H(κ_u − λx_1)H(κ_u − λx_2)dx du; substitute
x_i = M − v_i (v_i > 0). Now κ_u − λx_i = κ_u − λM + λv_i and κ_u − λM = 2√3t − (5√3/3)u − 2√6t + (8√3/3)u = c(u)
(λ·3 = 2√6, λ·3r_1 = 2√6·2√2/3 = 8√3/3). Derivatives: ∂x_i/∂u = −3r_1 = −2√2, so
∂²/∂u² (x_1² + x_1x_2 + x_2²) = 2·8 + 2·8 + 2·8 = 48 and ∂²q/∂u² = 1 + (2/3)·48 = 33; ∂²/∂v_1² gives (2/3)·2 = 4/3.
The arguments c(u) + λv_i are affine in (u, v_1, v_2); if they are positive at the corners of a box they are
positive on the box, and there log H(affine) is concave because H is positive and concave on (0, ∞)
(Lemma 5.11(c)) and log is increasing and concave. The explicit form: x_1² + x_1x_2 + x_2² =
3M² − 3M(v_1 + v_2) + v_1² + v_1v_2 + v_2². ∎

## 6. The certificate (Proposition C)

Here γ_d = 2452706089845207/18014398509481984 (= 0x1.16d72467283aep-3, the largest leaf bound of the recorded run;
see 6.6). The program `certify.py` (Python standard library, reads
no file) checks finitely many instances of Lemma 5.9(c) and the tails of Lemma 5.7. This section proves: *if its
output has "certified": true, then G_d(t) ≤ γ_d for all real t* (Proposition C). Function names: `certify.py`.

**6.1 What is checked.** `certify()` does three things; `main()` sets "certified": true only if all succeed and
(C1), (C2), (C4)–(C6) (exact finite checks belonging to §4, §5.1, §7 of `cutwidth.md` and to 6.2 below; see the
head of `certify.py`) hold; an exception gives "certified": false.
(i) *Tails.* Upper bounds (6.2) of Φ(−5/4) and of (7/2)Φ(−2) are ≤ γ_d. By Lemma 5.7, G_d(t) ≤ Φ(t) ≤ Φ(−5/4) for
t ≤ −5/4 and G_d(t) ≤ (7/2)Φ(−t) ≤ (7/2)Φ(−2) for t ≥ 2.
(ii) *Leaves.* Each base interval [k/32, (k+1)/32], −40 ≤ k < 64, is bisected (at most 5 times; all ends are dyadic
rationals with denominator ≤ 2^10, exact in binary64; the program re-checks 2m = a + b and w = b − a in rationals)
until each leaf [a, b] is accepted. For a leaf and a lattice level ℓ ∈ {0, 1, 2} the program computes binary64
numbers p_a ≤ P4(a), p_b ≤ P4(b) (6.3) and p′_a ≤ P2(a), p′_b ≤ P2(b) (6.4, lattice ℓ) and a binary64 number U
that is ≥ the smaller of the right sides of (5.3) and (5.2) (6.5). The leaf is accepted at the first ℓ with U ≤ γ_d,
compared exactly (`Fraction(U) <= GAMMA_D`). No leaf straddles 0. By Lemma 5.9(c), G_d ≤ U ≤ γ_d on every accepted
leaf. A leaf not accepted at depth 5 makes the run fail ("failed_leaf": not certified). The values p, p′ are cached
per point (and level); this affects only the running time.
(iii) *Cover.* From the list of accepted leaves the program checks in exact rationals that the first leaf starts at
−5/4, the last ends at 2, each leaf ends where the next begins, no leaf has a < 0 < b, and every stored U is ≤ γ_d
("cover": "contiguous", "every_leaf_bound_le_target"). So the leaves cover [−5/4, 2]; with (i), all of R. ∎

**6.2 Arithmetic** [P]. *Model* (§1.0: IEEE 754 binary64, round to nearest). A *double* is a binary64 number,
fl(z) the double nearest to the real z, u := 2^{−53}. Each of +, −, ×, ÷ on doubles returns fl of the exact
result, so |fl(z) − z| ≤ u|z| if |z| ≥ 2^{−1022} and ≤ 2^{−1075} otherwise; multiplication by 2 or 1/2 is
exact without underflow. All numbers in the program are below 10^6 in modulus, so there is no overflow.
*Library.* `certify.py` imports `itertools`, `json`, `math`, `sys`, `time`, `operator` (`mul`, `add`), `bisect`
(`bisect_left`), `functools` (`reduce`) and `fractions` (`Fraction`). No library function computes a number that
enters a bound, except as a *start value* that the program then verifies: `math.sqrt` in `isqrt` and `rootlo`
(below), and `float` of a `Fraction` in `fr_iv`. `operator.mul`/`add` (applied through `map`, `functools.reduce`,
`itertools.accumulate`) are the binary64 operations ×, +; `bisect_left` only compares doubles; the builtin `sum` is
treated below; `json`, `sys`, `time` only do input/output and timing; `itertools` also enumerates (C1), (C6).

*up, dn.* `up(x)` := fl(x + fl(fl(|x|·2^{−52}) + 2^{−1074})), `dn(x)` := −up(−x). Claim: if fl(z) = x then
dn(x) ≤ z ≤ up(x). Proof: let x⁺ be the double following x; z ≤ x⁺ since fl(z) = x. If 2^e ≤ |x| < 2^{e+1}
with e ≥ −1022, then x⁺ − x ≤ 2^{e−52} ≤ |x|2^{−52}, so the real number x + (the computed increment, which
is ≥ fl(|x|2^{−52}) ≥ 2^{e−52} by monotonicity of fl, or ≥ 2^{−1074} = x⁺ − x if |x|2^{−52} underflows or x is
subnormal) is ≥ x⁺, and so is its rounding, as x⁺ is a double. ∎ Hence if a double q was obtained by one
operation with exact result z, then z ∈ [dn(q), up(q)].

*Intervals.* An interval is a pair of doubles (lo, hi). `iadd`, `isub`, `imul`, `idiv` apply the operation to
the ends (all four products or quotients, then min and max; `idiv` asserts 0 ∉ divisor) and then dn to the
lower and up to the upper end. The exact result for any reals in the operands lies between the exact extreme
end combinations, which lie in [dn(min), up(max)] by the claim. `fr_iv(q)` moves a double by dn/up until exact
rational comparison shows lo ≤ q ≤ hi. `isqrt`: the start value r := `math.sqrt(x)` is decreased by dn until up(r·r) ≤ x;
then r² ≤ up(fl(r²)) ≤ x, so r ≤ √x; symmetrically for the upper end (increase by up until dn(r·r) ≥ x). Any
positive start value gives a valid enclosure (the loops verify it); `math.sqrt` is the IEEE 754 square root, which
is correctly rounded, so with it the result, and with it the whole run, is reproducible bit for bit.

*Constants* (`init_constants`). π: Machin's formula π = 16·arctan(1/5) − 4·arctan(1/239) with partial sums of
the alternating series Σ(−1)^k x^{2k+1}/(2k+1), which bracket arctan x for 0 < x < 1 (odd number of terms
above, even below), in exact rationals: PI_Q = (lower, upper), then `fr_iv`. 1/√(2π): doubles lo, hi with
lo²·2·PI_Q[1] ≤ 1 ≤ hi²·2·PI_Q[0] in exact rationals. √2, √3, √6 by `isqrt`; √12 = 2√3, r_1 = 2√2/3,
λ = 2√6/3, κ = 6√2 − 8, c_0 = 3/(2√2), 3/π by interval operations.

*exp* (`exp_neg(z)`, z ≤ 0 a double). If z < −700 it returns (0, 10^{−300}) ∋ e^z (e^7 > 2^{10}, so e^{700} >
2^{1000} > 10^{300}). Else y := z/2^s exactly, s ≤ 15 least with y ≥ −1/32 (found by `bisect_left` on the exact powers 2^{s−5}), and p̃ is the Horner value of
P(y) := Σ_{n≤12} yⁿ/n!: p_13 = 1, p_n = 1 + (y/n)p_{n+1}. All exact p_n and computed p̃_n lie in [0.96, 1].
With e_n := |p̃_n − p_n|: the computed product fl(fl(y/n)·p̃_{n+1}) differs from (y/n)p̃_{n+1} by at most
(1/32)(2u + u²) + 2^{−1074}, and the final addition adds an error ≤ u; so e_n ≤ e_{n+1}/32 + 1.07u, whence
e_1 ≤ 1.07u·32/31 < 1.2u. By Taylor's theorem |e^y − P(y)| ≤ |y|^{13}/13! < 10^{−29}. So |p̃ − e^y| < 1.4·10^{−16}
≤ 1.5·10^{−16}p̃. The doubles fl(1 ∓ 10^{−15}) are within 2^{−53} of 1 ∓ 10^{−15}, so dn(fl(p̃·fl(1 − 10^{−15}))) ≤
p̃(1 − 8·10^{−16}) ≤ e^y ≤ p̃(1 + 8·10^{−16}) ≤ up(fl(p̃·fl(1 + 10^{−15}))). Then s times (lo, hi) ← (dn(lo²),
up(hi²)): as 0 ≤ lo ≤ e^w ≤ hi implies dn(lo²) ≤ e^{2w} ≤ up(hi²) (lo stays > 0: e^z ≥ e^{−700}), the result
encloses e^z. `exp_iv` uses the lower value at the lower end and the upper value at the upper end.
*One-sided versions.* `_elo`, `_ehi` return the lower, upper end of `exp_neg`; `hp_lo`, `hp_hi` those of
`halfphi_part`; `phi_lo`, `phi_up` those of `Phi_pt`; `H_lo_f` equals `H_lo`. Each performs exactly the operations
that produce the end it returns, in the same order (up/dn written out; |x| replaced by x where x ≥ 0), so it returns
the same double and everything said here about the two-sided functions holds for it.

*Φ* (`halfphi_part`, `Phi_pt`, `H_lo`). For x ≥ 0, Φ(x) − 1/2 = φ(x)S(x), S(x) := Σ_{n≥0}T_n,
T_n := x^{2n+1}/(2n+1)!! (both sides vanish at 0 and have derivative φ(x): S′ = 1 + xS termwise). Let
10^{−150} ≤ x ≤ 9 be a double, x2 := fl(x²). The loop forms T̃_n = fl(fl(T̃_{n−1}·x2)/(2n+1)), T̃_0 = x,
S̃ = rounded sum, and stops at the first N ≥ 1 with x2 ≤ (2N+3)/2 and T̃_N ≤ 10^{−17}S̃. All terms are positive;
T̃_n carries 3n rounding factors (x2, product, quotient per step), the sum at most N more: without underflow
S̃ = S_N(1 + θ), T̃_N = T_N(1 + θ′), S_N := Σ_{n≤N}T_n, |θ|, |θ′| ≤ (1 + u)^{4N} − 1 ≤ 4.1(N+1)u (N ≤ 160:
x2 ≤ 81.01 gives the first test from N = 80 on, then the terms at least halve). Roundings that underflow add
at most 2^{−1075} each, in total < 2^{−1060} < uS (S ≥ x ≥ 10^{−150}). The tail: T_{n+1}/T_n = x²/(2n+3) ≤
q := x2(1 + 2u)/(2N+3) ≤ (1 + 2u)/2 for n ≥ N, so Σ_{n>N}T_n ≤ T_N q/(1 − q) ≤ (1 + 5u)T_N. With
d := 5(N+2)u (computed with the double nearest u; d ≥ 4.1(N+1)u + 5.9u): Slo := dn(fl(S̃(1 − d))) ≤ S_N ≤ S, and
Shi := up(fl(up(fl(S̃ + T̃_N(1 + d)))·(1 + d))) ≥ S, because S̃(1 + d) ≥ S_N(1 + 5u) and T̃_N(1 + d)² ≥
(1 + 6u)T_N, the roundings of the tiny term (relative 3u of ≤ 1.1·10^{−17}S) and the underflow being covered by
the 5u·S_N. Since x² ∈ [dn(x2), up(x2)], `exp_iv` on (−up(x2)/2, −dn(x2)/2) encloses e^{−x²/2}; the products
with the ends of 1/√(2π) and with Slo, Shi (all positive) are rounded outward. So `halfphi_part(x)` encloses
Φ(x) − 1/2 (upper end clipped to 1/2). `Phi_pt(x)` returns dn/up of 1/2 ± these ends (by the sign of x),
clipped to [0,1]. For |x| < 10^{−150}: |Φ(x) − 1/2| ≤ φ(0)|x| ≤ 0.4|x|. For |x| > 9: Φ(−9) ≤ φ(9)/9
(Φ(−T) ≤ ∫_T^∞ (v/T)φ(v)dv) ≤ (2/5)/(9·Σ_{k<200}(81/2)^k/k!) < 1.19·10^{−19} < the double 1.2e-19, and 1 − the
double 0.9999999999999998 > 2.4·10^{−19}: check (C5), exact; so (0, 1.2e-19) ∋ Φ(x) for x < −9 and
(0.9999999999999998, 1) ∋ Φ(x) for x > 9. `H_lo(z)` ≤ H(z) = max(0, 2Φ(z) − 1): 0 for z ≤ 10^{−150},
0.9999999999999998 for z > 9, else dn of twice (exact) the lower end of `halfphi_part(z)`.

*Sums of nonnegative bounds.* In 6.3, 6.4 sums of products of nonnegative doubles are formed in plain
arithmetic: by a loop, by `functools.reduce(add, …, 0.0)` (the same left-to-right additions), or by the builtin
`sum`, in the order and grouping stated in 6.3, 6.4. If every summand passes through at most n ≤ 10^5 roundings (its
own products and the later additions), the computed sum Σ̃ and the exact sum Σ of the same doubles satisfy
(1 − u)^nΣ − ρ ≤ Σ̃ ≤ (1 + u)^nΣ + ρ, ρ < 10^9·2^{−1074} (underflow, fewer than 10^9 operations); this holds for
every order and grouping of the additions and multiplications, since each rounding of a sum or product of
nonnegative numbers multiplies the exact intermediate result by a factor in [1 − u, 1 + u] (up to underflow). As
(1 + u)^{10^5} < 1 + 1.2·10^{−11}, Σ̃(1 + 10^{−9}) + 10^{−300} ≥ Σ and Σ̃(1 − 10^{−9}) − 10^{−300} ≤ Σ, also after the
roundings of these last operations. The program asserts n ≤ 10^5. Where the builtin `sum` is applied to a list or an
iterator of nonnegative doubles the same bounds hold: `sum` adds the items from left to right, and in CPython ≥ 3.12 it does so with a compensated
scheme whose result is at least as close to the exact sum of the items (relative difference below 10^{−13} for
nonnegative items), which the factors (1 ± 10^{−9}) cover as well.

*Further helpers.* *rootlo(x)* (x ≥ 0 a double): 0 if x ≤ 0; else the start value r := `math.sqrt(x)` is decreased
by dn until up(r·r) ≤ x; then r² ≤ up(fl(r²)) ≤ x, so 0 < r ≤ √x (as in `isqrt`; any positive start is valid).
*sq_hi((lo, hi))* := up(max(fl(lo²), fl(hi²))) ≥ z² for every z ∈ [lo, hi] (z² ≤ max(lo², hi²)).
*exp_lo(z)*: for z ≤ 0 the lower end of `exp_neg(z)`; for z > 0, dn(fl(1/h)) with h the upper end of
`exp_neg(−z)`: e^{−z} ≤ h gives e^z ≥ 1/h.
*atanh_iv(y)*, |y| ≤ 1/2 a double: for 0 ≤ y ≤ 1/2, atanh y = Σ_{k≥0} y^{2k+1}/(2k+1); the partial sum k ≤ 30 is
evaluated in interval arithmetic (enclosure [s_lo, s_hi]); the remainder is ≥ 0 and ≤ y^{63}/(63(1 − y²)) ≤
2^{−63}·(4/3)/63 < 4·10^{−21}; the function returns (s_lo, up(fl(s_hi + 4·10^{−21}))), whose upper end is
≥ s_hi + 4·10^{−21} (if the addition is absorbed by rounding, the spacing of doubles at s_hi exceeds 8·10^{−21},
and up adds at least one such spacing). For y < 0 it returns the negative of the enclosure for |y| (atanh is odd).
*log_ratio(p, q)*, p, q > 0 doubles: ln(q/p) = 2·atanh((q − p)/(q + p)); x := the interval quotient enclosing
(q − p)/(q + p); if x ⊄ [−1/2, 1/2] the function returns None (then only (5.3), or (5.2) with min(p′, q′), 0, is
used); otherwise, atanh being increasing, it returns (2·lower end of atanh_iv(x_lo), 2·upper end of atanh_iv(x_hi)).

**6.3 P̲4** (`TriTable`, `TriTable.P4_lo(t)`) [P]. Let ε = 0.001 (the double), ω := √3ε, h_m := mω (0 ≤ m ≤ M,
M = ⌊6.5/ω̄⌋, ω̄ the upper end of the enclosure of ω), z_k := kω, M_1 := ⌊2.5/ω̄⌋.
(a) *Table: T̲_m ≤ T(h_m).* T̲_0 := 0 = T(0). For 1 ≤ m ≤ M, by Lemma 5.11(a),
T(h_m) = Σ_{k=−2m}^{m−1} ∫_{z_k}^{z_{k+1}} φ(z)H((z + 2h_m)/√3)dz, and on the k-th cell the argument (z + 2h_m)/√3
runs through [jε, (j+1)ε], j := k + 2m ≥ 0. H is concave on [0, ∞) (Lemma 5.11(c)), so it lies above its chord:
H((z + 2h_m)/√3) ≥ H(jε)(z_{k+1} − z)/ω + H((j+1)ε)(z − z_k)/ω. With

    A_k := ω^{−1}∫_{z_k}^{z_{k+1}} φ(z)(z_{k+1} − z)dz = ω^{−1}[z_{k+1}(Φ(z_{k+1}) − Φ(z_k)) − (φ(z_k) − φ(z_{k+1}))] ≥ 0,
    B_k := ω^{−1}∫_{z_k}^{z_{k+1}} φ(z)(z − z_k)dz = ω^{−1}[(φ(z_k) − φ(z_{k+1})) − z_k(Φ(z_{k+1}) − Φ(z_k))] ≥ 0

(∫zφ(z)dz = −φ(z)), T(h_m) ≥ Σ_{k=−2m}^{m−1} [A_k·H((k+2m)ε) + B_k·H((k+2m+1)ε)]. The program evaluates A_k, B_k
(−2M_1 ≤ k < M_1) in interval arithmetic from enclosures of z_k, Φ(z_k) (`Phi_pt` at the ends of the enclosure of
z_k; Φ is increasing) and φ(z_k) (enclosure of 1/√(2π) times `exp_iv` on −z_k²/2), and keeps max(0, lower end);
H is replaced by `H_lo` at the lower end of the enclosure of jε. For m ≤ M_1 the sum is a sum of nonnegative
bounds (at most 3M_1 + 2 roundings on a path), and v_m := max(0, Σ̃(1 − 10^{−9}) − 10^{−300}) ≤ T(h_m); for m > M_1,
v_m := 0. Further b_m := dn(1 − up(3·(upper end of Φ at −(lower end of h_m)))) ≤ 1 − 3Φ(−h_m) ≤ T(h_m)
(Lemma 5.11(a)). T̲_m := max(v_m, b_m).
(b) *Nodes in u.* Let η := (√6/4)ε = ω/(3r_1) and u_m := c_0t − mη (c_0 = 1/r_1). Then 3(t − r_1u_m) = 3r_1mη = h_m.
Let m_0 := 0 if t ≤ 0, and m_0 := ⌊q̄⌋ + 1 if t > 0, where q̄ is the upper end of the interval evaluation of
(c_0 − 1)t/η; then u_m ≤ u* for all m ≥ m_0 (for t ≤ 0, u* = c_0t = u_0; for t > 0, u* = t and u_m ≤ t iff
mη ≥ (c_0 − 1)t). The program asserts m_0 < M. By Lemma 5.11(b) and since the integrand is ≥ 0,

    P4(t) ≥ Σ_{m=m_0}^{M−1} ∫_{u_{m+1}}^{u_m} φ(u)T(3(t − r_1u))du + ∫_{−∞}^{u_M} φ(u)T(3(t − r_1u))du.

(c) *Cells.* On [u_{m+1}, u_m] apply Lemma 5.10 with n = 1, q = u²/2 + ln√(2π) (A_1 = 1), g(u) = T(3(t − r_1u)):
g is log-concave where positive (Lemma 5.11(b)), and if g > 0 at both ends then g > 0 on the cell (g is monotone),
while if g = 0 at an end the bound is 0. So the cell integral is
≥ η(1 + η²/12)·(2π)^{−1/2}·exp(−(u_m² + u_{m+1}²)/4)·√(T(h_m)T(h_{m+1})). The program uses
ST_m := rootlo(dn(T̲_mT̲_{m+1})) ≤ √(T(h_m)T(h_{m+1})), the lower end of `exp_neg` at −up(up(s_m + s_{m+1})/4) with
s_m := `sq_hi`(enclosure of u_m) ≥ u_m², and the constant dn(dn(η̲·ι̲)·dn(1 + dn(η̲²)/12)) ≤ η(1 + η²/12)/√(2π)
(η̲, ι̲ the lower ends of the enclosures of η and 1/√(2π); the dn applied to 1 + … subtracts a full spacing of the
doubles in [1, 2), which exceeds the rounding errors of the division by 12 and of the addition). The sum over m is
a sum of nonnegative bounds (≤ M + 2 roundings).
(d) *Tail.* For u ≤ u_M, 3(t − r_1u) ≥ h_M and T is nondecreasing, so the last integral is ≥ T(h_M)Φ(u_M) ≥
dn(T̲_M·(lower end of Φ at the lower end of the enclosure of u_M)).
`P4_lo(t)` returns dn of the sum of (c) and (d): a lower bound of P4(t). ∎

**6.4 P̲2** (`P2Lattice(dv, a, b)`, `P2Lattice.lower(t)`) [P]. Three lattices ("levels") are used, with
(Δ_v, a, b) = (0.1, 1, 2), (0.04, 1, 3), (0.0088, 1, 3) (Δ_v a double, a, b positive integers). Put
e := λΔ_v/b, Δ_u := ae/√3 = (a/b)r_1Δ_v, n_v := ⌊4.5/Δ_v⌋, n_u := ⌊0.8/Δ̄_u⌋ (Δ̄_u the upper end of the enclosure), and

    u_i := t + iΔ_u (0 ≤ i ≤ n_u),   v_j := jΔ_v (0 ≤ j ≤ n_v),   M_i := 3(t − r_1u_i).

(a) *Boxes.* The boxes B_{i,j_1,j_2} := [u_i, u_{i+1}] × [v_{j_1}, v_{j_1+1}] × [v_{j_2}, v_{j_2+1}] (0 ≤ i < n_u,
0 ≤ j_1, j_2 < n_v) have disjoint interiors and lie in {u ≥ t, v_1, v_2 ≥ 0}; F_t ≥ 0; so by Lemma 5.12,
P2(t) ≥ Σ_{i,j_1,j_2} ∫_{B_{i,j_1,j_2}} F_t. By Lemma 5.12 the hypotheses of Lemma 5.10 hold on each box with
A_u = 33, A_{v_1} = A_{v_2} = 4/3, so

    ∫_{B_{i,j_1,j_2}} F_t ≥ Δ_uΔ_v²·(1 + 33Δ_u²/12)(1 + Δ_v²/9)²·Γ_{i,j_1,j_2},   Γ := (Π_{8 corners} F_t)^{1/8}.

(b) *The corner mean.* At the lattice points, c(u_i) + λv_j = c_t + (ai + bj)e with c_t := (3√3 − 2√6)t (since
c(t) = (3√3 − 2√6)t, √3Δ_u = ae, λΔ_v = be). By the explicit form of F_t in Lemma 5.12, log F_t at the corner
(u_{i′}, v_{j_1′}, v_{j_2′}) (i′ ∈ {i, i+1}, j_s′ ∈ {j_s, j_s+1}) is the sum of a constant, of a term depending on
i′ only, of two terms depending on (i′, j_1′) resp. (i′, j_2′) only, and of −(2/3)v_{j_1′}v_{j_2′}. Averaging over the
8 corners (the mean over {i, i+1} × {j, j+1} of M_{i′}v_{j′} is M̄_iv̄_j with M̄_i = (M_i + M_{i+1})/2,
v̄_j = (j + 1/2)Δ_v; the mean of v_{j_1′}v_{j_2′} is v̄_{j_1}v̄_{j_2}):

    Γ_{i,j_1,j_2} = (√(2π)√3π)^{−1}·E_i·β_i(j_1)·β_i(j_2)·K(j_1, j_2),
    E_i := exp(−(u_i² + u_{i+1}²)/4 − (M_i² + M_{i+1}²)),      K(j_1, j_2) := exp(−(2j_1+1)(2j_2+1)Δ_v²/6),
    β_i(j) := exp(−(v_j² + v_{j+1}²)/3)·ρ_i^{j+1/2}·Q(ai + bj),   ρ_i := exp((M_i + M_{i+1})Δ_v),
    Q(J) := [H(c_t + Je)·H(c_t + (J+b)e)·H(c_t + (J+a)e)·H(c_t + (J+a+b)e)]^{1/4}.

Hence P2(t) ≥ C·Σ_{i<n_u} E_i·Σ_{j_1<n_v} β_i(j_1)·Σ_{j_2<n_v} β_i(j_2)K(j_1, j_2), with
C := Δ_uΔ_v²(1 + 33Δ_u²/12)(1 + Δ_v²/9)²/(√(2π)√3π). The same holds with the sum restricted to any set of boxes
(each omitted box contributes ∫ F_t ≥ 0, and the remaining boxes still have disjoint interiors in the region).
(c) *Evaluation.* Every factor is replaced by a nonnegative double not larger than it:
exp(−(v_j² + v_{j+1}²)/3) and K(j_1, j_2) by lower ends of `exp_neg` at −up(up(n·up(Δ_v²))/3), n = j² + (j+1)², resp.
−up(up(n·up(Δ_v²))/6), n = (2j_1+1)(2j_2+1) (n an integer, exact); E_i by the lower end of `exp_neg` at minus an
upper bound of (u_i² + u_{i+1}²)/4 + M_i² + M_{i+1}² (from `sq_hi` of the enclosures of u_i, M_i); ρ_i by
r := `exp_lo` at the lower end of the interval product (M_i + M_{i+1})·Δ_v; ρ_i^{j+1/2} by the doubles
π_0 := rootlo(r), π_j := fl(π_{j−1}·r); H(c_t + Je) by `H_lo` at the lower end of the enclosure of c_t + Je (H is
nondecreasing); Q(J) by rootlo(rootlo(dn(dn(·)·dn(·)))) of the four lower bounds (if r_1² ≤ x and r_2² ≤ r_1 then
r_2⁴ ≤ x); C by the lower end of the interval product Δ_uΔ_v²·(1/√(2π))·(1/(√3π)) times
dn(dn(1 + dn(33·dn(Δ̲_u²))/12)·dn(c_v·c_v)), c_v := dn(1 + dn(Δ_v²)/9). Write b̃_j := fl(fl(G̃_j·π_j)·Q̃(ai + bj)) for the double replacing
β_i(j) (G̃_j, K̃(j_1, j_2), Q̃ the doubles just described), Ẽ_i for that of E_i.
*Omitted boxes* (by (b), a lower bound remains a lower bound): (1) rows i with Ẽ_i = 0; (2) a fixed set per lattice:
with thr := fl(10^{−5}·fl(fl(G̃_0·G̃_0)·K̃(0, 0))) (`P2_TAU` = 1e-5) and, for each j_1, J(j_1) := the least n ≥ j_1 with
fl(fl(G̃_{j_1}·G̃_n)·K̃(j_1, n)) < thr (or n_v), only the pairs with j_1 ≤ j_2 < J(j_1) are kept, together with their
mirror images (j_2, j_1); (3) per row i: with cut := fl(max_j b̃_j·3·10^{−5}) (`P2_BTAU` = 3e-5), j_lo := the least j with
b̃_j ≥ cut and j_hi := 1 + the largest such j, only j_1, j_2 ∈ [j_lo, j_hi) are kept. The kept set of ordered pairs
is symmetric; every omitted term is ≥ 0.
*Evaluation of the kept sum.* For row i, S̃_i := `sum` over j_1 ∈ [j_lo, j_hi), in increasing order, of
fl(b̃_{j_1}·Σ̃_{j_1}), where Σ̃_{j_1} := `sum` over j_2 from j_1 to min(J(j_1), j_hi) − 1 of fl(b̃_{j_2}·K̃′(j_1, j_2)), with
K̃′(j, j) := K̃(j, j) and K̃′(j_1, j_2) := 2K̃(j_1, j_2) (exact) for j_2 > j_1. Since K̃(j_1, j_2) and K̃(j_2, j_1) are the
same double (computed from the same integer n), the exact value of this expression with exact operations is the sum,
over the kept ordered pairs, of b̃_{j_1}b̃_{j_2}K̃(j_1, j_2); the program forms Σ̃ := Σ_i fl(Ẽ_i·S̃_i) (left to right).
This is a sum of nonnegative bounds in which every summand passes through at most 3n_v + n_u + 16 roundings (asserted
≤ 10⁵; π_j carries j of them; the factor 2 is exact), so by 6.2 (any order and grouping) the returned value
max(0, Σ̃·C̲·(1 − 10^{−9}) − 10^{−300}) is ≤ P2(t). ∎

**6.5 The leaf value, P3, the tails** [P]. `P3_up(b)`: 0 for b ≤ 0; else c_1, c_2 := the upper
ends of the interval evaluations of (1/r_1 − 1)/√(2π) and 18(1 − r_1)² (so they are admissible in Lemma 5.6), and
the value up(up(c_1b)·up(1 − lo)), lo ≤ e^{−up(c_2·up(b²))} ≤ e^{−c_2b²} the lower end of `exp_neg`: this is ≥ P3up(b).
`leaf_bound(a, b, p_a, p_b, p′_a, p′_b)`
with the lower bounds of 6.3, 6.4: p3h := up(P3up(b)/2);
U_1 := up(up(up(Φ̄(b) − min(p_a, p_b)) + p3h) − dn(1.5·min(p′_a, p′_b))) (Φ̄ the upper end of `Phi_pt`), an upper
bound of the right side of (5.3). If p_a ≤ 0 or p_b ≤ 0 or `log_ratio(p_a, p_b)` is None, U := U_1. Otherwise:
enclosures of g = √(p_ap_b) (`isqrt` of the interval product) and L = ln(p_b/p_a); of g′, L′ likewise if
p′_a, p′_b > 0 and `log_ratio` succeeds, else g′ := min(p′_a, p′_b) (a point interval) and L′ := 0 (the last
sentence of Lemma 5.9(c)); an enclosure of φ(m) (1/√(2π) times `exp_iv` on −m²/2, m² from the interval product,
its lower end clipped at 0); the interval S := φ(m)·w − (g·L + 1.5·g′·L′) and h := up(max(|S_lo|, |S_hi|)/2) ≥
|φ(m)w − gL − (3/2)g′L′|/2; c̄_Φ := 0 if a ≥ 0, else up(up(up(−a·ι̅)·up(w²))/8) ≥ |a|φ(0)w²/8 (ι̅ the upper end of
1/√(2π)); and U_2 := up(up(up(up(up(Φ̄(m) + c̄_Φ) + p3h) − g̲) − dn(1.5·g̲′)) + h), an upper bound of the right side
of (5.2) (g̲, g̲′ ≥ 0 lower ends). U := min(U_1, U_2). w = b − a and m = (a+b)/2 are exact (asserted in rationals).
Tails: upper end of `Phi_pt(-1.25)`, and up(up(7·(upper end of `Phi_pt(-2.0)`))/2).

**6.6 The run.** Program `certify.py`; it reads one JSON value from standard input, which it ignores
(`echo '{}' | python3 certify.py`). Output: one JSON object.
"certified": the conjunction described in 6.1; "checks": C1–C6; "tails": the two bounds; "cover": ends, number of
base intervals and leaves, contiguity; "counts": number of points at which P̲4 and (per level) P̲2 were computed,
the table and lattice sizes; "largest_certified_bound", "argmax_interval": the largest U (rounded up), its leaf;
"leaves_by_method": number of leaves accepted at each level; "block_table": leaves and largest U per block of
length 1/4; "leaf_table": 60 consecutive leaves [a, b, U rounded up, level] around the largest.
Recorded run (CPython 3.12.13, arm64, one core, about 3.4 s; the run is deterministic): certified true; tails
0.105649774 and 0.079625462; 104 base intervals, 119 leaves, contiguous; P̲4 at 120 points (ε = 0.001, M = 3752,
M_1 = 1443); P̲2 at 120, 20, 18 points on the three levels (n_v = 45, 112, 511; n_u = 16, 63, 289); leaves by level
100, 5, 14, by depth 0, …, 5: 101, 3, 3, 3, 3, 6; largest U = 0.136152539 on [41/1024, 21/512] (level 2, depth 5);
all of C1–C6 ok; output 4823 bytes. [S] The maximum of G_d is about 0.1361516 (near t = 0.0404).
*Choice of γ_d.* γ_d is the largest leaf bound L of this run: the double 0x1.16d72467283aep-3 =
2452706089845207/18014398509481984, the U of the leaf [41/1024, 21/512]. Every U the run computes (197 values) is
either ≤ L (the 119 accepted ones) or ≥ U_rej := 0x1.16d72945b131dp-3 = 4905413486777117/36028797018963968 =
0.13615257495816815… (the smallest rejected value, leaf [19/512, 5/128] at level 2 and depth 4, which is then
bisected). The target enters (C3) only through the exact comparisons U ≤ γ_d, so (C3) runs identically, with every
double the same, for every target in [L, U_rej), in particular for γ_d = L. The witnesses N6–N8 of (C4) are stated
for this γ_d: 0.0178 < γ_d; 38/22 > 3/2 − γ_d = 24568891674377769/18014398509481984 and 2^40 < 22^9;
1 + 1/(2γ_d) = 11459905344586199/2452706089845207.
*Negative controls.* If only the line `GAMMA_D = …` is changed, the run is not certified: to the double one ulp below
L (4905412179690413/36028797018963968), (C3) fails at the leaf [41/1024, 21/512] at depth 5 ("failed_leaf", last
level's U = 0.136152539 rounded up); to 2723/20000 = 0.13615, at [35/1024, 9/256] (depth 5, U = 0.136150593); to
1361/10000, at [13/1024, 7/512] (depth 5, U = 0.136101509); in all three (C4) fails as well (N6–N8 are stated for L).
*Reproducibility.* Every double of the run is determined by binary64 arithmetic with round to nearest: +, −, ×, ÷,
comparisons, exact conversions of small integers, decimal literals (correctly rounded by CPython), `math.sqrt` start
values (correctly rounded by IEEE 754), `float` of a `Fraction` as the start value in `fr_iv` (correctly rounded by
CPython), and the builtin `sum` on floats, which in CPython ≥ 3.12 is the compensated (Neumaier) summation, so the
bits are those of CPython 3.12; the comparisons with γ_d and the checks (C1), (C2), (C4)–(C6) are in exact integer or
rational arithmetic. The recorded run used CPython 3.12.13.
