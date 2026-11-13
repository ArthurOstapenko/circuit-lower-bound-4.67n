# Premise P1 (Kollár–Rónyai–Szabó, Theorem 3.3): a complete proof from textbook facts

Status: the supporting file for premise P1 of `circuit.md` §0, which `circuit.md` Lemma 2.6 uses. It
proves P1 for every field (§0, §3).

**Labels.** [cited: place] = a statement taken from the named source and place; [proved here] = proved in this
file.
**Notation is local to this file.** All letters (among them L, A, B, C, F, M, N, P, Q, R, S, T, D) denote objects
defined here, not the objects with the same names in `proof.md` and `circuit.md` (there L is the language, F the
subfield with q elements, R and Q the input polynomials, N the input length, D a vertex count).

**Outcome and credit.** Theorem A (P1 with its two indices exchanged; bound t!, every field, every right-hand
side) is proved completely in §3 from six textbook facts F1–F6 and five elementary facts E1–E5 (§2). The proof
keeps the skeleton of the published proof of KRS (finiteness by induction on t; the fibre over 0 consists of t!
points; Nakayama gives degree <= t!; a fibre bound for a finite map onto a polynomial ring), with four changes:
the valuation-ring characterisation of integral closure is replaced by the determinant trick; both uses of the
Nullstellensatz are replaced by an elementary "pigeonhole lemma" valid over every commutative ring (Lemma 1), so
no algebraic closure is needed; the radicality computation for the fibre over 0 is replaced by an interpolation
argument; and the fibre theorem that KRS cite from Shafarevich is proved inline from F5.

**Sources.**
- [KRS] J. Kollár, L. Rónyai, T. Szabó, "Norm-graphs and bipartite Turán numbers", Combinatorica 16(3) (1996)
  399–406.
- [ARS] N. Alon, L. Rónyai, T. Szabó, "Norm-graphs: variations and applications", J. Combin. Theory Ser. B 76
  (1999) 280–290.
- [AM] M. F. Atiyah, I. G. Macdonald, Introduction to Commutative Algebra, Addison-Wesley, 1969.
- [Milne] J. S. Milne, Fields and Galois Theory, version 5.10, Chapter 9 (transcendence bases).

## 0. Statements

**P1** [cited: KRS Theorem 3.3; also stated in `circuit.md` §0]. Let K be a field and a_ij, b_j ∈ K for
1 <= i, j <= t such that a_{i j1} ≠ a_{i j2} if j1 ≠ j2. Then the system of equations

    (x_1 − a_1j)(x_2 − a_2j)···(x_t − a_tj) = b_j        (j = 1, ..., t)

has at most t! solutions (x_1, ..., x_t) ∈ K^t. (Variable index i, equation index j.)

**Theorem A** (P1 with the two indices exchanged, the form stated in ARS; proved in §3). Let K be a field,
t >= 1, and a_ij, b_i ∈ K (1 <= i, j <= t) with a_ij ≠ a_i'j whenever i ≠ i'. Then the system

    f_i(x) := Π_{j=1}^{t} (x_j − a_ij) = b_i        (i = 1, ..., t)

has at most t! solutions x = (x_1, ..., x_t) ∈ K^t. (Equation index i, variable index j. For each variable x_j,
the t shifts a_1j, ..., a_tj are distinct. An array (a_ij) with this property is called *admissible*.)

**P1 follows from Theorem A** [proved here]. Let (a_ij), (b_j) be data as in P1 and put α_ij := a_ji. Writing
equation j of P1 as Π_{l=1}^{t} (x_l − a_lj) = b_j and renaming its index j as i and l as j, it reads
Π_{j=1}^{t} (x_j − α_ij) = b_i: the systems of P1 for (a, b) and of Theorem A for (α, b) consist of the same t
equations in the same unknowns x_1, ..., x_t, so they have the same solutions in K^t. The hypothesis of P1,
a_{i j1} ≠ a_{i j2} for j1 ≠ j2, says α_{j1 i} ≠ α_{j2 i} for j1 ≠ j2, i.e. that α is admissible. ∎

## 1. Use

`circuit.md` Lemma 2.6 applies P1 with K = E (a field of characteristic 2 with q^t elements, q = 2^m),
a_ij = d_j^{q^{i−1}} for t distinct d_1, ..., d_t ∈ E, b_j = 1 and x_i = y^{q^{i−1}}; its proof checks the
hypothesis of P1 and the injectivity of y ↦ (y, y^q, ..., y^{q^{t−1}}).

## 2. Facts used without proof

Textbook facts, stated with generic letters R, R', N, k, Ω, Γ chosen so as not to clash with §3:

- **F1** [cited: AM Corollary 2.5] (determinant trick). Let R be a ring, N a finitely generated R-module and 𝔞 an
  ideal of R with 𝔞N = N. Then some r ∈ R with r − 1 ∈ 𝔞 satisfies rN = 0.
- **F2** [cited: AM Proposition 2.8] (form of Nakayama's lemma). Let R be a local ring with maximal ideal 𝔫 and N
  a finitely generated R-module. If u_1, ..., u_n ∈ N have images forming a basis of the R/𝔫-vector space
  N/𝔫N, then u_1, ..., u_n generate N. Together with [cited: AM Chapter 3, Examples 1), p. 38]: for a prime
  ideal 𝔭 of R, the localization R_𝔭 is a local ring whose maximal ideal consists of the a/s with a ∈ 𝔭.
- **F3** [cited: AM Corollaries 5.2 and 5.3]. Let R ⊆ R' be rings. If u_1, ..., u_n ∈ R' are each integral over
  R, then R[u_1, ..., u_n] is a finitely generated R-module; the elements of R' integral over R form a subring
  of R' containing R.
- **F4** [cited: AM Chapter 5, the paragraph before Proposition 5.13]. Any unique factorization domain is
  integrally closed; in particular a polynomial ring k[T_1, ..., T_n] over a field k is integrally closed.
- **F5** [cited: AM Proposition 5.15]. Let R ⊆ R' be integral domains with R integrally closed, and 𝔞 an ideal
  of R. If u ∈ R' satisfies a monic equation whose non-leading coefficients lie in 𝔞, then u is algebraic over
  Frac R, and if its minimal polynomial over Frac R is T^n + c_1 T^{n−1} + ... + c_n, then its non-leading
  coefficients c_1, ..., c_n lie in the radical r(𝔞). Used only with 𝔞 = R (so r(𝔞) = R): *the minimal
  polynomial over Frac R of an element integral over R is monic with all non-leading coefficients in R, so all
  its coefficients lie in R.*
- **F6** [cited: Milne, Chapter 9]. Let Ω ⊇ k be fields and Γ ⊆ Ω a finite subset such that Ω is algebraic over
  k(Γ). Then every minimal subset Γ' ⊆ Γ such that Ω is algebraic over k(Γ') is a transcendence basis of Ω/k,
  and all transcendence bases of Ω/k are finite with the same number of elements.

Elementary facts, used without citation:
- **E1** A nonzero polynomial of degree n in one variable over a field has at most n roots in that field.
- **E2** A nonzero polynomial in several variables over an infinite field has a non-root (induction on the number
  of variables, using E1).
- **E3** Division with remainder by a monic polynomial in one variable, over any commutative ring.
- **E4** If k ⊆ Ω are fields with [Ω : k] finite and u ∈ Ω, the minimal polynomial of u over k has degree
  [k(u) : k] <= [Ω : k].
- **E5** If R is a domain and Σ ⊆ R ∖ {0} is multiplicatively closed, Σ^{-1}R is (isomorphic to) the subring
  {a/s : a ∈ R, s ∈ Σ} of Frac R.

## 3. Proof of Theorem A

All rings are commutative with 1.

**3.0 Reduction to an infinite field.** Let L := K(X), the rational function field over K in a new
indeterminate X. L is infinite, K ⊆ L, every solution in K^t is a solution in L^t, and the hypothesis
a_ij ≠ a_i'j is unchanged. So it suffices to prove Theorem A over L. (Only Lemma 6 uses that L is infinite.)
Fix L, t and an admissible array (a_ij) over L, and put

    A := L[x_1, ..., x_t],  f_i := Π_j (x_j − a_ij),  B := L[f_1, ..., f_t] ⊆ A,  M := Frac A = L(x_1, ..., x_t),
    F := Frac B = L(f_1, ..., f_t) ⊆ M,  g_i^{(k)} := Π_{j≠k} (x_j − a_ij)  (1 <= i, k <= t),

so that f_i = (x_k − a_ik)·g_i^{(k)} for every k. Below, T and T_1, ..., T_t denote further new indeterminates.

**3.1 Lemma 1 (pigeonhole lemma)** [proved here]. Let R be a ring, n > m >= 0, and ℓ_ij ∈ R (1 <= i <= n,
1 <= j <= m) such that ℓ_ij − ℓ_i'j is a unit of R whenever i ≠ i'. Put π_i := Π_{j=1}^{m} ℓ_ij. Then
π_1 R + ... + π_n R = R.

*Proof.* Induction on m, for all rings R and all n > m simultaneously. If m = 0, every π_i is the empty
product 1. Let m >= 1, J := π_1 R + ... + π_n R, and π'_i := Π_{j=1}^{m−1} ℓ_ij, so π_i = π'_i ℓ_im.
Step 1: for every k ∈ {1, ..., n}, J + ℓ_km R = R. Let R̄ := R/ℓ_km R. For i ≠ k, ℓ_im ≡ ℓ_im − ℓ_km
(mod ℓ_km), a unit of R̄. The n − 1 rows i ≠ k and the columns 1, ..., m − 1 satisfy the hypothesis in R̄
(images of units are units) and n − 1 > m − 1, so by induction the π'_i (i ≠ k) generate the unit ideal of R̄.
Since π_i = π'_i ℓ_im with ℓ_im a unit of R̄, the π_i (i ≠ k) also generate it: J + ℓ_km R = R.
Step 2: let R̂ := R/J. By Step 1 every ℓ_km (k = 1, ..., n) is a unit of R̂. In R̂, π_k = 0, hence
π'_k = π_k ℓ_km^{-1} = 0 for every k. The n rows and columns 1, ..., m − 1 satisfy the hypothesis in R̂ and
n > m − 1, so by induction the π'_k generate the unit ideal of R̂. They are all 0, so R̂ = 0, i.e. J = R. ∎

**Corollary 1.1** [proved here]. For each k there are h_i^{(k)} ∈ L[x_j : j ≠ k] with
Σ_{i=1}^{t} h_i^{(k)} g_i^{(k)} = 1.

*Proof.* Lemma 1 in R = L[x_j : j ≠ k] with n = t rows, the m = t − 1 variables x_j (j ≠ k) as columns, and
ℓ_ij = x_j − a_ij: ℓ_ij − ℓ_i'j = a_i'j − a_ij is a nonzero constant, a unit, because the array is admissible;
and π_i = g_i^{(k)}. ∎

**3.2 Lemma 2 (finiteness)** [proved here; uses F1, F3, Corollary 1.1]. A is integral over B. Consequently (F3)
A is a finitely generated B-module.

*Proof.* Induction on t, for all fields L and all admissible arrays simultaneously.
t = 1: f_1 = x_1 − a_11, so x_1 = f_1 + a_11 ∈ B.
t >= 2: since A = B[x_1, ..., x_t], by F3 (integral elements form a ring containing B) it suffices that each x_k
is integral over B. Exchanging the names of x_k and x_t, and the columns k and t of the array, gives a system of
the same form with an admissible array and the same f_i, so we may take k = t. Write x' := (x_1, ..., x_{t−1})
and g_i := g_i^{(t)} = Π_{j<t} (x_j − a_ij) ∈ L[x'].

(a) *Induction hypothesis.* The (t−1) × (t−1) array (a_ij)_{i,j<t} is admissible and g_1, ..., g_{t−1} are the
polynomials of Theorem A for it in the variables x'. By induction, L[x'] is integral over C := L[g_1, ..., g_{t−1}].

(b) *The ring S.* In M put y := x_t − a_1t ≠ 0, z := 1/y, and c_i := a_1t − a_it ∈ L (so c_1 = 0 and
x_t − a_it = y + c_i). Since x_t − a_it ≠ 0, also 1 + c_i z = (x_t − a_it)/y ≠ 0; put w := Π_{i=1}^{t} (1 + c_i z)
≠ 0 and S := B[z, w^{-1}] ⊆ M. Every element of S has the form P(z)/w^k with P ∈ B[T] and k >= 0. For each i,

    u_i := 1/(x_t − a_it) = z/(1 + c_i z) = z · w^{-1} · Π_{l≠i} (1 + c_l z) ∈ zS,   and   g_i = f_i·u_i ∈ zS

(f_i ∈ B ⊆ S). In particular C ⊆ S.

(c) *S' is module-finite.* Let S' := S[x_1, ..., x_{t−1}] ⊆ M. By (a) each x_j (j < t) satisfies a monic
equation with coefficients in C ⊆ S, so by F3 S' is a finitely generated S-module.

(d) *1 ∈ zS.* By Corollary 1.1 (k = t), 1 = Σ_{i=1}^{t} h_i g_i with h_i := h_i^{(t)} ∈ L[x'] ⊆ S'. By (b) each
g_i ∈ zS (all t of them, including g_t, which is not a generator of C), so 1 ∈ zS'. Hence the ideal 𝔞 := zS of
S satisfies 𝔞S' = zS' = S' (an ideal of S' containing 1). By F1 (R := S, N := S', 𝔞 := zS) there is s ∈ S with
s − 1 ∈ zS and sS' = 0. As 1 ∈ S', s = s·1 = 0, so 1 = 1 − s ∈ zS.

(e) *A monic equation for x_t.* By (d) and (b), 1 = z·P(z)/w^k for some P ∈ B[T] and k >= 0, i.e.
z·P(z) = w^k. Expanding the product, w^k = Π_i (1 + c_i z)^k = 1 + z·Q(z) with Q ∈ L[T]. Hence z·U(z) = 1 with
U := P − Q ∈ B[T], U ≠ 0. Write U = Σ_{n=0}^{D} r_n T^n (r_n ∈ B). Multiplying Σ_{n=0}^{D} r_n z^{n+1} = 1 by
y^{D+1} and using zy = 1 gives

    y^{D+1} − Σ_{n=0}^{D} r_n y^{D−n} = 0,

a monic equation for y with coefficients in B. So y is integral over B, and so is x_t = y + a_1t (F3). ∎

**3.3 Lemma 3 (the fibre over 0)** [proved here; elementary]. Let I_0 := (f_1, ..., f_t)A. Then
dim_L A/I_0 = t!.

*Proof.* Step 1: *P_k(x_k) := Π_{i=1}^{t} (x_k − a_ik) lies in I_0 for each k.* With g_i := g_i^{(k)},
P_k(x_k)·g_i = (x_k − a_ik) g_i · Π_{l≠i} (x_k − a_lk) = f_i · Π_{l≠i} (x_k − a_lk) ∈ I_0. By Corollary 1.1,
P_k(x_k) = Σ_i h_i^{(k)} P_k(x_k) g_i ∈ I_0.

Step 2: *the grid.* For a map τ : {1, ..., t} → {1, ..., t} put γ(τ) := (a_{τ(1)1}, a_{τ(2)2}, ..., a_{τ(t)t}) ∈ L^t,
and let G := {γ(τ)}. By admissibility distinct τ give distinct points, so |G| = t^t. Let L^G be the ring of
L-valued functions on G (pointwise operations) and ev : A → L^G, p ↦ (p(γ))_{γ∈G}, a ring homomorphism. Let
J := (P_1(x_1), ..., P_t(x_t))A ⊆ I_0 (Step 1).
(α) J ⊆ ker ev, since P_k vanishes at the k-th coordinate of every point of G.
(β) A/J is spanned over L by the classes of the t^t monomials x_1^{n_1}···x_t^{n_t} with all n_k <= t − 1: by E3,
x_k^n ≡ (remainder of x_k^n on division by the monic P_k) modulo J, and the remainder has degree <= t − 1;
apply this in each variable.
(γ) ev is onto: for γ = γ(τ) ∈ G, δ_γ := Π_k Π_{l≠τ(k)} (x_k − a_lk)/(a_{τ(k)k} − a_lk) (the denominators are
nonzero by admissibility) equals 1 at γ and 0 at every γ(τ') ≠ γ (choose k with τ'(k) ≠ τ(k); the factor with
l = τ'(k) vanishes there).
By (α), ev induces a surjection A/J → L^G; by (β), dim_L A/J <= t^t = dim_L L^G. So A/J → L^G is bijective and
ker ev = J.

Step 3: *the quotient.* Since J ⊆ I_0, A/I_0 ≅ L^G/𝔦 where 𝔦 := ev(I_0) is the ideal of L^G generated by
v_i := ev(f_i) (ev is onto). In L^G, the ideal generated by v_1, ..., v_t is the set of functions vanishing on
Z := {γ : v_1(γ) = ... = v_t(γ) = 0}: each v_i vanishes on Z; conversely, for γ ∉ Z pick i with v_i(γ) ≠ 0,
then the indicator 1_γ = v_i · v_i(γ)^{-1} 1_γ lies in the ideal, and every function vanishing on Z is a
combination of such 1_γ. Hence A/I_0 ≅ L^Z (restriction to Z) and dim_L A/I_0 = |Z|. Finally, for γ = γ(τ),
f_i(γ) = Π_k (a_{τ(k)k} − a_ik) is 0 iff τ(k) = i for some k (admissibility). So γ ∈ Z iff τ is onto, i.e. τ is
a permutation, and |Z| = t!. ∎

**3.4 Lemma 4 (degree)** [proved here; uses F2, E5, Lemmas 2 and 3]. [M : F] <= t!.

*Proof.* Let 𝔪 := (f_1, ..., f_t)B. The point p_0 := (a_11, a_22, ..., a_tt) satisfies f_i(p_0) = 0 for all i
(the factor j = i of f_i vanishes). Let ε : B → L, β ↦ β(p_0), an L-algebra homomorphism onto L. Every β ∈ B is
Ψ(f_1, ..., f_t) for some Ψ ∈ L[T_1, ..., T_t], so β − Ψ(0) ∈ 𝔪 and ε(β) = Ψ(0); hence ker ε = 𝔪, B/𝔪 ≅ L,
and 𝔪 is a maximal (so prime) ideal. Put Σ := B ∖ 𝔪, B_𝔪 := Σ^{-1}B ⊆ F and A_𝔪 := Σ^{-1}A ⊆ M (E5). By F2
(AM p. 38), B_𝔪 is local with maximal ideal 𝔪B_𝔪. By Lemma 2, B-module generators of A generate A_𝔪 over B_𝔪.

For s ∈ Σ write s = λ + μ with λ := ε(s) ∈ L^*, μ ∈ 𝔪. For any a ∈ A, a/s − λ^{-1}a = −μa/(λs) ∈ 𝔪A_𝔪. Hence
(i) every element of A_𝔪 is congruent modulo 𝔪A_𝔪 to an element of A, so the L-linear map A/𝔪A → A_𝔪/𝔪A_𝔪
is onto; (ii) for β ∈ B, β/s ≡ λ^{-1}β ≡ λ^{-1}ε(β) modulo 𝔪B_𝔪 (as β − ε(β) ∈ 𝔪), so the map L → κ := B_𝔪/𝔪B_𝔪
is onto, hence an isomorphism (a surjective homomorphism of fields), and the κ-dimension of a κ-vector space
equals its L-dimension. Since 𝔪A = I_0, Lemma 3 gives dim_κ A_𝔪/𝔪A_𝔪 <= dim_L A/I_0 = t!. By F2
(R := B_𝔪, N := A_𝔪) there are u_1, ..., u_n ∈ A_𝔪, n <= t!, generating A_𝔪 as a B_𝔪-module.

Let W := F u_1 + ... + F u_n ⊆ M; dim_F W <= n. Then A ⊆ A_𝔪 ⊆ W. The set F·A of finite sums Σ φ_k a_k
(φ_k ∈ F, a_k ∈ A) is a subring of M (A is a ring), contained in W, hence a domain of finite dimension over F.
For 0 ≠ v ∈ F·A, multiplication by v is an injective F-linear map F·A → F·A, hence onto, so v^{-1} ∈ F·A: F·A is
a field. It contains A, so it contains Frac A = M. Thus M ⊆ W and [M : F] <= n <= t!. ∎

**3.5 Lemma 5 (B is a polynomial ring)** [proved here; uses F6, F4, Lemma 4]. f_1, ..., f_t are algebraically
independent over L, so L[T_1, ..., T_t] → B, T_i ↦ f_i, is an isomorphism and B is integrally closed.

*Proof.* By Lemma 4, M = L(x_1, ..., x_t) is finite, hence algebraic, over L(f_1, ..., f_t). Since
{f_1, ..., f_t} is finite, it has a minimal subset Γ' with M algebraic over L(Γ'); by F6 (Ω := M, k := L,
Γ := {f_1, ..., f_t}), Γ' is a transcendence basis of M/L. {x_1, ..., x_t} is also one (algebraically independent
indeterminates, and M = L(x_1, ..., x_t)), so by F6 |Γ'| = t; hence Γ' consists of the t distinct elements
f_1, ..., f_t and these are algebraically independent: the map L[T_1, ..., T_t] → B is injective; it is onto by
definition of B. By F4, B is integrally closed. ∎

**3.6 Lemma 6 (fibre bound)** [proved here; uses F5, E1, E2, E4 and Lemmas 2, 4, 5]. For every
c = (c_1, ..., c_t) ∈ L^t, at most t! points p ∈ L^t satisfy f_i(p) = c_i for all i.

*Proof.* Let p_1, ..., p_r be distinct such points, r >= 2 (if r <= 1 there is nothing to prove, since t! >= 1).
The polynomial Π_{k<l} Σ_j λ_j (p_{k,j} − p_{l,j}) in λ = (λ_1, ..., λ_t) is a product of nonzero linear forms,
hence nonzero; by E2 (L infinite) choose λ ∈ L^t with all factors nonzero, and put g := Σ_j λ_j x_j ∈ A. Then
g(p_1), ..., g(p_r) are pairwise distinct. By Lemma 2, g is integral over B; by Lemma 5, B is integrally closed.
By F5 (R := B, R' := A, 𝔞 := B), the minimal polynomial of g over F is T^n + ν_1 T^{n−1} + ... + ν_n with
ν_l ∈ B, and by E4 and Lemma 4, n <= [M : F] <= t!. The relation g^n + ν_1 g^{n−1} + ... + ν_n = 0 holds in M,
hence in A. Write ν_l = Ψ_l(f_1, ..., f_t) with Ψ_l ∈ L[T_1, ..., T_t]. Evaluation at p_k is a ring
homomorphism A → L sending ν_l to Ψ_l(f_1(p_k), ..., f_t(p_k)) = Ψ_l(c) =: η_l, the same value for every k. So
each g(p_k) is a root of the monic polynomial T^n + η_1 T^{n−1} + ... + η_n ∈ L[T], and by E1, r <= n <= t!. ∎

**Proof of Theorem A.** Apply Lemma 6 with c = (b_1, ..., b_t) over L = K(X) (§3.0). ∎
