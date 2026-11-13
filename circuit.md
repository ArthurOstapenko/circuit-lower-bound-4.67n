# A conditional (1 + 1/(2γ))N lower bound for one explicit language in P

Status: one of the three proof files (with `cutwidth.md` and `krs.md`). Theorem 1 below is
conditional on the graph hypothesis H(γ,h) and uses premise P1, which `krs.md` proves; everything else is
proved here. `cutwidth.md` proves H(γ,h) for the explicit γ and h stated in its §0; `proof.md` §6 combines
the two files.

**Credit.** The route (circuit -> wire graph -> cutwidth-ordered read-once nondeterministic program ->
rectangle edge counting) is from S. McGuire, S. Schlesinger, R. Williams, "Explicit functions requiring larger
than 4.5n size circuits" (preprint, November 2026). Every step below is re-proved, and the explicit family is
different (theirs is a sumset extractor of Li; ours rests on the norm-graph theorem of Kollár–Rónyai–Szabó).
The validated-prefix device (an irreducible polynomial is part of the input and is checked by the evaluator) is
due to mooselumph (GitHub), who used it in a 4n lower bound for a certificate-prefix family.

## 0. Statement

**Hypothesis H(γ,h).** γ > 0 is a real number and h : {1,2,3,...} -> [0,∞) is nondecreasing with
h(D)/D -> 0. Every connected cubic multigraph on D vertices has cutwidth at most γD + h(D). (Multigraph:
parallel edges and loops allowed; a loop adds 2 to the degree of its vertex and never crosses a cut; cubic:
every vertex has degree 3; cuts and cutwidth as in Definition 4.3, which agrees with `cutwidth.md` §0.)

**Theorem 1.** Let L ⊆ {0,1}* be the language decided by the evaluator A of `proof.md` §1 and L_N its slice at
length N. Then L ∈ P (§2.2; NP membership with the empty witness is `proof.md` §2). If H(γ,h) holds then for
every integer N >= 256

    C_B2(L_N) >= (1 + 1/(2γ))·N − R(N),
    R(N) = 5√N + (1/2)√N·log2 N + 2
           + [ 7√N + √N·log2 N + 6 + 3·log2(2s_0) + h(2s_0) ] / (2γ),      s_0 = ⌈(1 + 1/(2γ))N⌉.

Since √N·log N = o(N), log s_0 = O(log N) and h(2s_0) = o(N), R(N)/N -> 0, so

    liminf over all integers N of C_B2(L_N)/N >= 1 + 1/(2γ).

For N < 256 put R(N) = (1 + 1/(2γ))N; the inequality is then trivial, so the displayed bound holds at EVERY
length. The exact (sharper) remainder, in terms of the length parameters t, m, ℓ, is (6.3).

**Premises not proved in this file.**

* **P1 (Kollár–Rónyai–Szabó, Combinatorica 16(3) (1996) 399–406, Theorem 3.3; proved in `krs.md` for every
  field from textbook facts).** *Let K be a field and a_ij, b_j ∈ K for 1 <= i, j <= t such that
  a_{i j1} ≠ a_{i j2} if j1 ≠ j2. Then the system of equations (x_1 − a_1j)(x_2 − a_2j)···(x_t − a_tj) = b_j,
  j = 1, ..., t, has at most t! solutions (x_1,...,x_t) ∈ K^t.* (Variable index i, equation index j.) It is used
  only in Lemma 2.6.
* **Standard algebra used without proof** (textbook facts): (S1) for a field K and an irreducible P ∈ K[X] of
  degree d, K[X]/(P) is a field and a K-vector space with basis 1, X, ..., X^{d−1}; K[X] has unique
  factorization and every ideal is principal; (S2) a nonzero polynomial of degree d over a field has at most d
  roots in that field; (S3) Lagrange: in a finite group of order n every element g has g^n = 1, and a group
  homomorphism ψ has |G| = |ker ψ|·|im ψ|; (S4) a finite field L containing a subfield L_0 is an L_0-vector
  space, so |L| is a power of |L_0|; (S5) if P^2 divides H in K[X] then P divides the formal derivative H';
  (S6) in characteristic 2, (a+b)^2 = a^2 + b^2, so u ↦ u^{2^j} is additive, and it is injective on a field.

## 1. The circuit model and a size-preserving normal form

A circuit on inputs x_1, ..., x_N consists of the input nodes, possibly constant nodes 0 and 1 (allowed only
for robustness: they cost nothing), and gates g_1, ..., g_s. Gate g has a type φ_g : {0,1}^2 -> {0,1} (any of
the 16 functions, including the two constants, the four projections and negated projections) and two ordered
pins, pin 1 and pin 2, each fed by an input node, a constant node or an earlier gate; both pins may be fed by
the same node. One node o is the output. On x ∈ {0,1}^N each node v gets a value val_x(v) in the obvious way,
and the circuit computes x ↦ val_x(o). Its size is s; every gate counts 1, whatever its type. C_B2(F) is the
least size of a circuit computing F exactly on all of {0,1}^N. Gate g is *fed by* v if some pin of g is fed by
v; the *fan-out* t(v) of a node v is the number of pins fed by v, counted with multiplicity (a gate with both
pins fed by v contributes 2). An *ancestor* of v is a node from which a directed path of feeding relations
leads to v (v is an ancestor of itself).

**Lemma 1.1 (normal form).** Let N >= 1 and let C have size s and compute a function F that is neither
constant nor equal to a projection x ↦ x_k. Then there is a circuit C' of size s' <= s computing F such that
(i) C' has no constant nodes, (ii) every gate of C' is an ancestor of its output o, and (iii) o is a gate, so
s' >= 1. Moreover in C' the output has fan-out 0 and every other gate has fan-out >= 1.

*Proof.* (i) Go through the gates. If pin 1 of g is fed by a constant node c and pin 2 by a node v that is
not a constant node, give g the new type φ'(a,b) = φ_g(c,b) and feed both pins by v; symmetrically if only
pin 2 is constant (φ'(a,b) = φ_g(a,c)). If both pins are constant nodes c, c', give g the constant type
φ'(a,b) = φ_g(c,c') and feed both pins by x_1 (N >= 1). In each case val_x(g) is unchanged for every x, and no
gate is added. If o itself were a constant node, F would be constant, which is excluded. Constant nodes now
feed nothing; delete them. (ii) Delete every gate that is not an ancestor of o. By induction along the gate
order, val_x(o) depends only on the values of the ancestors of o, and every pin of a remaining gate is fed by
an ancestor of o (an ancestor of an ancestor), so the result is a circuit computing F of size <= s.
(iii) If o is an input x_k, then F = x_k, excluded; so o is a gate. Finally, a gate fed by o would be an
ancestor of o (it lies in C') and a descendant of o, i.e. there would be a directed cycle, impossible since
pins are fed by earlier nodes; so t(o) = 0. Every other gate g of C' is a proper ancestor of o, so there is a
feeding path from g to o and g feeds some gate: t(g) >= 1. ∎

Nothing in what follows uses the gate types, so degenerate gates (constants, projections, negations) and
gates with repeated pins are treated exactly like all others and each is counted once.

## 2. The family

### 2.1 The evaluator

The language L, its evaluator A, the length parameters k, t, m0, m, ℓ, the input layout (R-prefix x_1..x_t,
Q-prefix x_{t+1}..x_{t+m}, payload bits c_{u,v} for 0 <= u < m, 0 <= v < t, where c_{u,v} is bit number
t + m + v·m + u + 1, and ℓ leftover bits), the test IrrTest, and R, Q, F, E, z, e are defined in `proof.md` §1;
this file uses that notation. Thus t is a power of two, m is odd, gcd(m, t) = 1 and N = t + m + t·m + ℓ.

### 2.2 Membership in P

The integers k, t, m0, m, ℓ are at most N, and computing them is arithmetic on O(log N)-bit numbers; the
exponent e is written down as a bit string of length (t − 1)m + 1 <= N. IrrTest on degree d <= N uses at most
d divisors, each needing at most d squarings modulo P (O(d^2) bit operations each) and one Euclid run (O(d^2)),
so O(d^4) in total. An element of E is a t×m bit array; a product in E is a product of polynomials of degree
< t in W with coefficients in F (t^2 products in F, each O(m^2) bit operations) followed by reduction modulo the
monic R (O(t^2) operations in F), so O(t^2 m^2) <= O(N^2) bit operations. Since e has (t − 1)m + 1 <= N bits,
step 5 uses O(N) products. In total A runs in O(N^4) bit operations on every input, so L ∈ P.

### 2.3 Finite-field lemmas

**Lemma 2.1.** Let P ∈ F_2[X] be irreducible of degree d and j >= 1. Then P divides X^{2^j} − X iff d | j.

*Proof.* L = F_2[X]/(P) is a field with 2^d elements (S1); let α be the class of X, so L = F_2[α], and P
divides a polynomial H iff H(α) = 0 in L. The Frobenius map σ(u) = u^2 is a ring homomorphism of L (S6),
injective, hence bijective; it fixes F_2. α^{2^j} = α means σ^j(α) = α, which (σ^j fixes F_2 and α, and L is
generated by α) is equivalent to σ^j = id on L. By (S3) applied to L^* and 0, every u ∈ L has u^{2^d} = u, so
σ^d = id. If σ^j = id, every element of L is a root of X^{2^j} − X, so 2^d <= 2^j (S2). Let o be the least
o >= 1 with σ^o = id; then o <= d and, taking j = o, d <= o, so o = d. Writing j = ad + b with 0 <= b < d,
σ^j = σ^b, which is the identity iff b = 0. ∎

**Lemma 2.2 (IrrTest is exact).** A monic P of degree d >= 1 is accepted iff P is irreducible.

*Proof.* If P is irreducible: P | X^{2^d} − X by Lemma 2.1; for a proper divisor d' of d the monic gcd of P
and X^{2^{d'}} − X is 1 or P, and P does not divide X^{2^{d'}} − X by Lemma 2.1 (d does not divide d' < d); so
the gcd is 1 and P is accepted. Conversely let P be accepted. H = X^{2^d} − X has derivative 2^d X^{2^d −1} − 1
= 1 in characteristic 2, so by (S5) H is squarefree; P | H, so every irreducible factor P_0 of P occurs once
and, by Lemma 2.1, has degree d_0 dividing d. If some d_0 < d, then P_0 divides X^{2^{d_0}} − X and P, so the
gcd tested for d' = d_0 is not 1: rejection. Hence every irreducible factor has degree d, and since deg P = d,
P is itself irreducible. ∎

**Lemma 2.3 (existence).** For every d >= 1 there is a monic irreducible polynomial of degree d over F_2.

*Proof.* Let I_j be the number of monic irreducibles of degree j. H_d = X^{2^d} − X is squarefree (as above),
monic, and by Lemma 2.1 its monic irreducible factors are exactly the monic irreducibles of degree dividing d.
Comparing degrees, 2^d = Σ_{j|d} j·I_j; in particular j·I_j <= 2^j for all j. Hence
d·I_d >= 2^d − Σ_{j|d, j<d} 2^j >= 2^d − Σ_{j=1}^{⌊d/2⌋} 2^j > 2^d − 2^{⌊d/2⌋+1} >= 0. ∎

**Lemma 2.4 (the field E).** Let Q, R ∈ F_2[Z], F_2[W] be irreducible of degrees m and t with gcd(m,t) = 1,
F = F_2[Z]/(Q), q = 2^m, E = F[W]/(R). Then E is a field with q^t = 2^{tm} elements, and the map
c ↦ z(c) = Σ_{u,v} c_{u,v} Z^u W^v from {0,1}^{tm} to E is a bijection with z(c ⊕ c') = z(c) + z(c').

*Proof.* F is a field with q elements (S1). Let P ∈ F[W] be a monic irreducible factor of R (in F[W]) of
degree d >= 1, and L = F[W]/(P), a field with q^d = 2^{md} elements (S1). Let ω ∈ L be the class of W; P | R
gives R(ω) = 0. The ring homomorphism F_2[W] -> L, W ↦ ω, has a kernel I that contains R and is proper
(1 ↦ 1 ≠ 0); I = (H) with H | R and H non-constant (S1), so I = (R) because R is irreducible over F_2. Its image
F_2[ω] ⊆ L is therefore isomorphic to F_2[W]/(R), a field with 2^t elements. By (S4), 2^{md} is a power of 2^t,
so t | md, hence t | d because gcd(t,m) = 1; also d <= t. So d = t and P = R: R is irreducible over F, and E is
a field with q^t elements (S1). By (S1) twice, {W^v : v < t} is an F-basis of E and {Z^u : u < m} an
F_2-basis of F, so {Z^u W^v} is an F_2-basis of E; z(c) is the coordinate map of this basis, hence bijective and
F_2-linear (addition in E is coordinatewise addition modulo 2). ∎

**Lemma 2.5 (number of ones).** In the setting of Lemma 2.4 let e = Σ_{j=0}^{t−1} q^j = (q^t − 1)/(q − 1).
Then |{z ∈ E : z^e = 1}| = e >= 2^{m(t−1)}.

*Proof.* ψ(z) = z^e is a homomorphism of the group E^* of order q^t − 1 = (q−1)e. For z ∈ E^*,
ψ(z)^{q−1} = z^{q^t −1} = 1 (S3), so im ψ lies in the root set of X^{q−1} − 1 and |im ψ| <= q − 1 (S2). By
(S3) |ker ψ| >= (q^t − 1)/(q − 1) = e, while ker ψ lies in the root set of X^e − 1, so |ker ψ| <= e. And
0^e = 0 ≠ 1. Finally e >= q^{t−1} = 2^{m(t−1)}. ∎

**Lemma 2.6 (t distinct translates; uses P1).** In the setting of Lemma 2.4, let d_1, ..., d_t ∈ E be
distinct. Then at most t! elements y ∈ E satisfy (d_j + y)^e = 1 for all j = 1, ..., t.

*Proof.* Since each q^i is a power of 2, (S6) gives (d_j + y)^e = Π_{i=1}^{t} (d_j + y)^{q^{i−1}}
= Π_{i=1}^{t} (y^{q^{i−1}} + d_j^{q^{i−1}}). In characteristic 2, u + a = u − a. So if y is a solution, then
(x_1, ..., x_t) = (y, y^q, ..., y^{q^{t−1}}) solves the system of P1 over K = E with a_ij = d_j^{q^{i−1}} and
b_j = 1. Hypothesis of P1: if a_{i j1} = a_{i j2} then (d_{j1} + d_{j2})^{q^{i−1}} = 0, so d_{j1} = d_{j2}
(S6), so j1 = j2. Hence there are at most t! such tuples, and y ↦ (y, y^q, ...) is injective (first
coordinate). ∎

### 2.4 The payload function and its rectangle property

**Definition (property D).** Let Y be a finite set of Boolean variables and g : {0,1}^Y -> {0,1}. For integers
K1, K2 >= 2, g has property D(K1,K2) if for every partition Y = S ⊔ T (S or T may be empty), every
A ⊆ {0,1}^S with |A| >= K1 and every B ⊆ {0,1}^T with |B| >= K2, some α ∈ A, β ∈ B have g(α ∪ β) = 0.
(α ∪ β is the assignment to Y that agrees with α on S and with β on T.) N1(g) = |g^{-1}(1)|.

Fix N >= 16 with its parameters, and fix (Lemma 2.3) monic irreducible R* of degree t and Q* of degree m;
let ρ* be the corresponding assignment of the prefix bits and 0 on the leftover bits. Let Y be the set of
the t·m payload variables, and define

    g_N : {0,1}^Y -> {0,1},   g_N(c) = A(ρ* ∪ c) = [ z(c)^e = 1 ]   (z, e computed with Q*, R*).

The second equality holds because R*, Q* pass IrrTest (Lemma 2.2) and the leftover bits are ignored.

**Lemma 2.7.** g_N has property D(t, t! + 1), and N1(g_N) = e >= 2^{m(t−1)}.

*Proof.* The count is Lemmas 2.4–2.5 (z is a bijection). Let Y = S ⊔ T, and for α ∈ {0,1}^S put
ι_S(α) = z(α ∪ 0_T), for β ∈ {0,1}^T put ι_T(β) = z(0_S ∪ β). By Lemma 2.4, z(α ∪ β) = ι_S(α) + ι_T(β) and
ι_S, ι_T are injective. Suppose g_N = 1 on A × B with |A| >= t and |B| >= t! + 1. Choose distinct
α_1, ..., α_t ∈ A; the d_j = ι_S(α_j) are distinct, and every y = ι_T(β), β ∈ B, satisfies (d_j + y)^e = 1 for
all j. Distinct β give distinct y, so |B| <= t! by Lemma 2.6, a contradiction. (If S or T is empty the
corresponding side has one element, below t and t! + 1, and there is nothing to prove.) ∎

## 3. Oblivious read-once programs and the edge lower bound

**Definition 3.0.** Let X be a finite set of Boolean variables. A *program* P over X consists of finite node
sets V_0, ..., V_λ (λ >= 0), pairwise disjoint, with V_0 = {start} and V_λ = {acc} (for λ = 0 there is one
set and start = acc), and a finite set of edges, each edge going from a node of V_{i−1} to a node of V_i for
some i ∈ {1, ..., λ} (several edges between the same two nodes are allowed and are distinct). Each *layer*
i ∈ {1, ..., λ} has a kind: either *guess* (its edges carry no label) or *reads y* for a variable y ∈ X (each
of its edges carries a label b ∈ {0,1}); different read layers read different variables. A path from start
to acc is *consistent* with x ∈ {0,1}^X if every labelled edge on it, in a layer reading y with label b, has
x(y) = b. P *computes* F : {0,1}^X -> {0,1} if, for every x, F(x) = 1 iff some start–acc path is consistent
with x. The size of P is its number of edges, |P|. (No unambiguity, width or degree condition is assumed.)

**Lemma 3.1 (restriction).** Let P over X compute F, let Y ⊆ X and ρ ∈ {0,1}^{X∖Y}. Delete from P every
edge in a layer reading some y ∉ Y whose label differs from ρ(y), then turn every layer reading a variable
outside Y into a guess layer (erasing its labels). The result P_ρ is a program over Y computing
g(c) = F(c ∪ ρ), |P_ρ| <= |P|, and a variable of Y is read by P_ρ iff it is read by P.

*Proof.* The start–acc paths of P_ρ are exactly the start–acc paths of P all of whose edges in layers reading
variables outside Y have labels agreeing with ρ. Such a path is consistent with c in P_ρ iff it is consistent
with c ∪ ρ in P. Layers reading variables of Y are untouched. ∎

**Lemma 3.2 (dependence).** Let g : {0,1}^Y -> {0,1} have D(K1,K2) and N1(g) >= 1. If U ⊆ Y and g(c) = g(c')
whenever c and c' agree outside U, then |U| <= ⌈log2 K1⌉ + ⌈log2 K2⌉ − 1.

*Proof.* Otherwise choose disjoint U1, U2 ⊆ U with |U1| = ⌈log2 K1⌉ and |U2| = ⌈log2 K2⌉, and ĉ with
g(ĉ) = 1. Take S = Y ∖ U2, T = U2, A = {α ∈ {0,1}^S : α agrees with ĉ outside U1} (so |A| = 2^{|U1|} >= K1)
and B = {0,1}^T (|B| >= K2). Every α ∪ β agrees with ĉ outside U, so g(α ∪ β) = 1 on A × B, contradicting
D(K1,K2). ∎

**Theorem 3.3 (edge lower bound).** Let P be a program over Y computing g, where g has D(K1,K2), K1,K2 >= 2.
Let U be the set of variables of Y read by no layer of P, r = |U|, and assume N1(g) >= 2^r·K2. Then

    |P| >= N1(g) / ( 2^r (K1 − 1)(K2 − 1) ).

*Proof.* Acceptance by P does not depend on the values of the variables in U, so g(c) = g'(c|_{Y'}) for a
function g' on Y' = Y ∖ U, and N1(g') = N1(g)/2^r >= K2. g' has D(K1,K2): if g' were 1 on A' × B' for a
partition Y' = S' ⊔ T' with |A'| >= K1, |B'| >= K2, then g would be 1 on (A' × {0,1}^U) × B' for the partition
(S' ∪ U, T'), and |A' × {0,1}^U| >= K1. P computes g' when viewed as a program over Y' (every read layer reads
a variable of Y').

Let R_i ⊆ Y' be the set of variables read in layers 1, ..., i (R_0 = ∅, R_λ = Y'). By the read-once
condition, the variables read in layers i+1, ..., λ are exactly those of Y' ∖ R_i. For a node v ∈ V_i let

    P_v = { π ∈ {0,1}^{R_i} : some start–v path is consistent with π },
    F_v = { φ ∈ {0,1}^{Y'∖R_i} : some v–acc path is consistent with φ },

where consistency of a partial path is defined as for full paths (the labels on a start–v path mention only
variables of R_i, those on a v–acc path only variables of Y' ∖ R_i).

(a) P_v × F_v ⊆ g'^{-1}(1): concatenating a start–v path consistent with π and a v–acc path consistent with
φ gives a start–acc path consistent with π ∪ φ. By D(K1,K2) for the partition (R_i, Y' ∖ R_i): if
|F_v| >= K2 then |P_v| <= K1 − 1.

(b) F_start = g'^{-1}(1), so |F_start| = N1(g') >= K2; F_acc ⊆ {0,1}^∅, so |F_acc| <= 1 < K2.

(c) For each x ∈ g'^{-1}(1) fix one start–acc path p_x consistent with x. Let v be the first node on p_x with
|F_v| <= K2 − 1 (it exists by (b), and v ≠ start), let u be the node before v on p_x, and let ε_x be the edge
of p_x from u to v, say in layer i. Then |F_u| >= K2, so |P_u| <= K1 − 1 by (a). The part of p_x up to u shows
x|_{R_{i−1}} ∈ P_u; the part from v shows x|_{Y'∖R_i} ∈ F_v; and if layer i reads y then x(y) is the label of
ε_x. Since Y' = R_{i−1} ⊔ (R_i ∖ R_{i−1}) ⊔ (Y' ∖ R_i) and R_i ∖ R_{i−1} is empty or {y}, the map
x ↦ (x|_{R_{i−1}}, x|_{Y'∖R_i}) is injective on {x : ε_x = ε} for each fixed edge ε, with image in
P_u × F_v. Hence at most (K1 − 1)(K2 − 1) inputs x have ε_x = ε, and

    N1(g') = Σ_ε |{x : ε_x = ε}| <= |P|·(K1 − 1)(K2 − 1). ∎

## 4. Wire graph and the sweep program

Throughout this section C is a circuit in the normal form of Lemma 1.1: inputs x_1..x_N, s >= 1 gates, no
constant nodes, every gate an ancestor of the output gate o, t(o) = 0 and t(g) >= 1 for every gate g ≠ o. An
input is *used* if t(x) >= 1; n_u is the number of used inputs.

**Definition 4.1 (wire graph G(C)).** For every node v with t = t(v) >= 1, list the pins it feeds as
(g_1, π_1), ..., (g_t, π_t) (gate, pin number; if v feeds both pins of a gate, both pins appear). Create t − 1
*copy vertices* c_{v,1}, ..., c_{v,t−1} and the following t·2 − 1 edges, which form the *distributor* T_v:
if t = 1, one edge from [v] to [g_1]; if t >= 2, the *root edge* [v]–c_{v,1}, the chain edges
c_{v,j}–c_{v,j+1} (1 <= j <= t − 2), a leaf edge c_{v,j}–[g_j] for 1 <= j <= t − 2, and two leaf edges
c_{v,t−1}–[g_{t−1}] and c_{v,t−1}–[g_t]. (For t = 1 the single edge is both the root edge and the leaf edge.)
The leaf edge ending at [g_j] is the *pin edge* of pin (g_j, π_j). The vertex set of G(C) is: one gate vertex
[g] per gate, one input vertex [x] per used input, and all copy vertices. All edges are distinct objects
(G(C) is a multigraph: if v feeds both pins of g, two distinct edges end at [g], possibly with the same other
endpoint).

**Lemma 4.2 (counts).** G(C) is a connected loopless multigraph with

    V = 2s + 1 vertices,  E = 3s − n_u + 1 edges,  E − V = s − n_u,

maximum degree 3; input vertices have degree 1, [o] has degree 2, every other gate vertex and every copy
vertex has degree 3.

*Proof.* Loopless: every edge of T_v joins two different vertices ([v] ≠ [g_j] since g_j is fed by v, and
copy vertices are new). Degrees: [x] has only the root edge of T_x; a gate vertex [g] has its two pin edges
and, iff t(g) >= 1, the root edge of T_g; c_{v,j} has its parent edge, and either a chain edge and a leaf edge
or two leaf edges. Counts: the nodes with t >= 1 are the n_u used inputs and the s − 1 gates other than o, and
Σ_v t(v) = 2s (two pins per gate). So there are Σ (t(v) − 1) = 2s − (n_u + s − 1) = s − n_u + 1 copy vertices,
V = s + n_u + (s − n_u + 1) = 2s + 1, and E = Σ (2t(v) − 1) = 4s − (n_u + s − 1) = 3s − n_u + 1. Connected:
every vertex lies in some T_v, which is connected and contains [v]; and for every node v there is a feeding
path v = v_0, v_1, ..., v_a = o, where T_{v_j} contains a path from [v_j] to [v_{j+1}]. ∎

**Definition 4.3 (cuts, cutwidth).** For a loopless or general multigraph H with vertex set of size n_H, an
ordering is a bijection pos : V(H) -> {1, ..., n_H}. For 0 <= i <= n_H the cut E_i is the set of edges with one
endpoint at a position <= i and the other at a position > i (a loop is never in a cut; parallel edges count
separately). The width of the ordering is max_i |E_i|, and cw(H) is the least width over all orderings
(cw = 0 if n_H = 1). Write v_i for the vertex at position i.

**Theorem 4.4 (sweep program).** Let C be in normal form, computing F : {0,1}^N -> {0,1}, and let pos be an
ordering of G = G(C) of width w. There is a program P over {x_1, ..., x_N} computing F with |P| <= 4·V·2^w, in
which every used input is read by exactly one layer and no unused input is read.

*Construction.* V_i = {(i, σ) : σ ∈ {0,1}^{E_i}} (one node for each 0/1 assignment σ to the cut E_i, tagged
with its layer index i, so that the sets V_0, ..., V_V are pairwise disjoint), for 0 <= i <= V; since
E_0 = E_V = ∅, V_0 and V_V have one node each, start = (0, ∅) and acc = (V, ∅), which are distinct since V >= 3.
Below we write σ for the node (i, σ) when its layer i is clear; the tags add no edges. Layer i corresponds to
the vertex v_i. Let δ(v_i) be the set of edges at v_i. Because G is loopless, every edge at v_i has its other
endpoint either before v_i (then it lies in E_{i−1} and not in E_i) or after v_i (then in E_i and not in
E_{i−1}); and an edge in both E_{i−1} and E_i has both endpoints different from v_i. Hence

    E_{i−1} ∪ E_i = (E_{i−1} ∩ E_i) ⊔ δ(v_i).                                       (4.1)

The *local rule* of a vertex is a condition on an assignment β to its edges:
- gate vertex [g] with t(g) >= 1, pin edges p_1, p_2 (of pins 1 and 2) and root edge e_g of T_g:
  β(e_g) = φ_g(β(p_1), β(p_2));
- the output vertex [o]: φ_o(β(p_1), β(p_2)) = 1;
- copy vertex: its three edges have equal values;
- input vertex: no condition.
For σ ∈ V_{i−1} and σ' ∈ V_i that agree on E_{i−1} ∩ E_i, let β = σ ∪ σ' (an assignment to E_{i−1} ∪ E_i).
There is an edge σ -> σ' iff β restricted to δ(v_i) satisfies the local rule of v_i. If v_i = [x_k] is an
input vertex, layer i reads x_k and the edge is labelled β(e), e the unique edge at [x_k]; otherwise layer i is
a guess layer.

*Proof.* Read-once: variable x_k is read only in the layer of [x_k], which exists iff x_k is used.

Size: by (4.1) an edge of layer i is determined by an assignment to (E_{i−1} ∩ E_i) ⊔ δ(v_i) satisfying the
local rule on δ(v_i). The number of rule-satisfying assignments of δ(v_i) is 4 for a gate vertex with t >= 1
(the two pin values are free and determine the root edge), at most 4 for [o], 2 for a copy vertex and 2 for an
input vertex. So layer i has at most 4·2^{|E_{i−1} ∩ E_i|} <= 4·2^w edges, and |P| <= 4V·2^w.

Correctness. Call β : E(G) -> {0,1} *valid for x* if it satisfies the local rules of all non-output vertices
and β(root edge of T_{x_k}) = x_k for every used input x_k. (i) Start–acc paths (σ_0, ..., σ_V) consistent with
x correspond bijectively to assignments β : E(G) -> {0,1} that are valid for x and satisfy the rule of [o]:
given the path, for an edge e = ab with pos(a) < pos(b) the set of i with e ∈ E_i is {pos(a), ..., pos(b) − 1},
nonempty since G is loopless; consecutive σ's agree on common edges, so β(e) = σ_i(e) for any such i is well
defined. Every local rule is checked at the layer of its vertex, and the labels of the read layers are exactly
β of the root edges of the input distributors (the single edge at [x_k] is the root edge of T_{x_k}).
Conversely β gives the path σ_i = β|_{E_i}. (ii) For every x there is exactly one β valid for x, namely
β(e) = val_x(v) for all e ∈ T_v: by induction over the nodes v in the order of C (inputs first), the root
edge of T_v is forced (input: by the label condition; gate g: by its rule, from its pin edges, which belong to
distributors of earlier nodes and are forced to the values of the feeding nodes), and then the copy rules force
every edge of T_v, moving away from the root, to the same value. This β satisfies all rules. (iii) Under this
β the rule of [o] reads φ_o(val_x(fed nodes)) = val_x(o) = 1. Hence the number of consistent start–acc paths is
1 if F(x) = 1 and 0 otherwise. ∎

**Corollary 4.5.** Let C be in normal form computing F, let X = Y ⊔ Z' be a partition of the inputs, ρ an
assignment to Z', and suppose g(c) = F(c ∪ ρ) has D(K1,K2) with K1,K2 >= 2. Let r be the number of variables
of Y unused in C, and assume N1(g) >= 2^r K2. Then

    cw(G(C)) >= log2 N1(g) − r − log2((K1 − 1)(K2 − 1)) − 2 − log2 V,    V = 2s + 1.

*Proof.* Take an ordering of width w = cw(G(C)), build P (Theorem 4.4), restrict it to P_ρ (Lemma 3.1): a
program over Y computing g with |P_ρ| <= 4V·2^w whose unread variables are exactly the r unused variables of
Y. Theorem 3.3 gives 4V·2^w >= N1(g)/(2^r(K1−1)(K2−1)); take log2. ∎

## 5. The kernel: from the wire graph to a cubic multigraph

Throughout this section G is a connected loopless multigraph with maximum degree <= 3, V >= 1 vertices and E
edges, and μ = E − V + 1 (>= 0 since G is connected). By Lemma 4.2 every wire graph is such a G, with
μ = s − n_u + 1.

**Lemma 5.1 (2-core and pendant trees).** Repeatedly delete a vertex of degree <= 1 (in the current graph)
until none is left; call the result G_2 (we fix one run of this process). Let μ >= 1.
Then: (a) G_2 is nonempty, connected, has minimum degree >= 2 and maximum degree <= 3, and
E(G_2) − V(G_2) = E − V; (b) every connected component T of G − V(G_2) is a tree joined to G_2 by exactly one
edge; (c) for every vertex z of G_2 at most one such tree is joined to z.

*Proof.* (a) G has a cycle (μ >= 1); a vertex of a cycle keeps degree >= 2 as long as the cycle is present, so
no cycle vertex is ever deleted, and G_2 is nonempty. While a cycle remains, the current graph has at least two
vertices, so a deleted vertex has degree exactly 1 (degree 0 would mean the current graph is a single vertex,
since deleting a degree-1 vertex keeps the graph connected, by induction). Each deletion removes one vertex and
one edge and keeps connectivity, so E − V is preserved; at the end no vertex has degree <= 1. Degrees only
drop, so the maximum degree stays <= 3. (b) Charge every edge of G with at least one deleted endpoint to its
endpoint that was deleted first; at the moment of its deletion a vertex has at most one remaining edge, so each
deleted vertex is charged at most once. For a component T of G − V(G_2), the edges inside T and between T and
G_2 are all charged to vertices of T, so there are at most |T| of them. T is connected, so it has at least
|T| − 1 inner edges, and since G is connected and G_2 nonempty there is at least one edge from T to G_2. Hence
T has exactly |T| − 1 inner edges (it is a tree) and exactly one edge to G_2. (c) z has degree >= 2 inside G_2
and degree <= 3 in G, so at most one edge leaves z towards G − V(G_2). ∎

**Lemma 5.2 (kernel).** Let μ >= 2 and let D be the number of vertices of degree 3 in G_2. Then D = 2(μ − 1)
>= 2, and there is a connected cubic multigraph K (loops and parallel edges allowed) with V(K) = the set of
degree-3 vertices of G_2, so |V(K)| = D, such that G_2 is obtained from K by subdividing edges: each non-loop
edge of K with ends a, b is replaced by a path from a to b with >= 0 new inner vertices, each loop at a by a
closed path through a with >= 1 new inner vertex, the inner vertices of different edges being distinct, and
V(G_2) consists of V(K) and all inner vertices.

*Proof.* In G_2 every vertex has degree 2 or 3, so 2E(G_2) = 2V(G_2) + D, i.e. D = 2(E(G_2) − V(G_2))
= 2(E − V) = 2(μ − 1) >= 2 (Lemma 5.1(a)). Now suppress degree-2 vertices one at a time. Let H be the current
multigraph (initially G_2), connected, with all degrees in {2,3} and the same D vertices of degree 3. If w has
degree 2 in H, w carries no loop (a loop would be its only edge, making w an isolated vertex of the connected H,
which has D >= 2 other vertices). Let its two edges be wa and wb (a = b is possible). Delete w and these two
edges and add one new edge ab (a loop if a = b). H stays connected (a path through w is rerouted along ab), the
other degrees and E(H) − V(H) are unchanged. After |V(G_2)| − D steps all vertices have degree 3; call the result
K: a connected cubic multigraph on the D degree-3 vertices. Bookkeeping: assign to every edge f of the current H
a path P_f of G_2 between the ends of f (closed if f is a loop), with inner vertices among the deleted vertices.
Initially P_f = f. When wa, wb are replaced by ab, let P_ab be P_wa traversed from a to w followed by P_wb.
By induction the paths P_f partition E(G_2), and their inner vertex sets are disjoint and cover exactly the
deleted vertices. A loop f of K has P_f with at least one inner vertex, since G_2 is loopless. So G_2 arises
from K by replacing each edge f by P_f, which is the claimed subdivision. ∎

**Lemma 5.3 (subdivision costs at most 2).** In the situation of Lemma 5.2, cw(G_2) <= cw(K) + 2.

*Proof.* Take an ordering of K of width c. Build an ordering of G_2: list the vertices of K in their order, and
immediately after each vertex a insert, one block after another, the inner vertices of P_f for every edge f of
K whose "left end" is a (for a non-loop edge, its end earlier in the K-order; for a loop at a, a itself), each
block in the order in which P_f visits them starting from a. Consider a gap of the new ordering, and let a be the
last K-vertex at or before it (the first position is a K-vertex). For a non-loop edge f from a' to b' (a' before
b' in K), P_f visits its vertices in increasing positions, so exactly one of its edges crosses the gap if
a' <= a < b' in the K-order, and none otherwise; the number of such f is the cut of K just after a, at most c.
For a loop at a'' ≠ a, P_f lies entirely on one side of the gap (in the group of a''). For a loop at a with inner
vertices w_1, ..., w_k (edges a w_1, w_1 w_2, ..., w_k a), at most 2 edges cross: if the gap is before its
block, exactly a w_1 and w_k a; if inside the block, one path edge and w_k a; if after, none. Since a has degree
3 in K it carries at most one loop. So every gap is crossed by at most c + 2 edges. ∎

**Lemma 5.4 (trees).** A tree T with maximum degree <= 3 and n_T >= 1 vertices has cw(T) <= 2·log2 n_T.

*Proof.* Induction on n_T; n_T = 1 gives 0. For n_T >= 2 choose a centroid z: every component of T − z has at
most n_T/2 vertices (start anywhere; while the current vertex z has a component of T − z with more than n_T/2
vertices, move to the neighbour z' in it; the component of T − z' containing z then has fewer than n_T/2
vertices, so the walk never steps back, and in a finite tree it stops). z has at most three
components T_1, T_2, T_3 (some possibly empty), each a tree of maximum degree <= 3, each joined to z by one edge.
Order: layout of T_1, then z, then layout of T_2, then layout of T_3. A gap inside the layout of T_1 is crossed
by edges of T_1 and possibly the edge T_1–z: at most cw(T_1) + 1. Inside T_2: edges of T_2, possibly the edge
z–T_2, and the edge z–T_3: at most cw(T_2) + 2. Inside T_3: at most cw(T_3) + 1. The gaps next to z are crossed
by at most 2 edges. So cw(T) <= max(2, max_j cw(T_j) + 2) <= 2·log2(n_T/2) + 2 = 2·log2 n_T (using n_T >= 2 and
the induction hypothesis for the T_j, which have at most n_T/2 vertices). ∎

**Proposition 5.5 (cutwidth transfer).** If μ >= 2 then cw(G) <= cw(K) + 3 + 2·log2 V, with K as in Lemma 5.2
(a connected cubic multigraph on D = 2(μ − 1) vertices). If μ <= 1 then cw(G) <= 3 + 2·log2 V.

*Proof.* Let μ >= 1 and take an optimal ordering of G_2. For every pendant tree T (Lemma 5.1(b)) joined to
z ∈ V(G_2), insert an optimal layout of T (Lemma 5.4) as a block immediately after z; by Lemma 5.1(c) blocks
of different trees follow different vertices. A gap that is neither inside a block nor between a vertex z and
the first vertex of its block is crossed only by G_2-edges (each tree and its joining edge lie on one side,
together with z), at most cw(G_2) of them. A gap inside the block of T, or between z and the first vertex of
that block, is crossed by at most cw(G_2) edges of G_2 (the relative order of the G_2-vertices is unchanged,
so these are the edges of the G_2-cut after z), at most cw(T) <= 2 log2 V edges of T,
and possibly the joining edge: cw(G) <= cw(G_2) + 1 + 2·log2 V. For μ >= 2 combine with Lemma 5.3. For μ = 1,
G_2 has E(G_2) = V(G_2) and minimum degree 2, so it is a single cycle (possibly of length 2, two parallel
edges), whose cyclic order has width 2; so cw(G) <= 3 + 2 log2 V. For μ = 0, G is a tree: Lemma 5.4. ∎

## 6. Parameters, the main inequality and the proof of Theorem 1

**Lemma 6.1 (parameters).** (a) For N >= 16: k >= 2, 4 <= t <= √N < 2t; m0 >= 2, so m >= 1; m is odd and
gcd(m,t) = 1; √N − 4 < m < 2√N; 0 <= ℓ <= 2t + 1. (b) For N >= 256 moreover t >= 16, k <= (1/2)log2 N and
m >= 2k + 3. (c) With r_max = ⌈log2 t⌉ + ⌈log2(t! + 1)⌉ − 1: r_max <= kt and log2((t − 1)·t!) <= kt, and
kt <= (1/2)√N·log2 N.

*Proof.* (a) 4^k <= N < 4^{k+1} gives t <= √N < 2t, and N >= 16 gives k >= 2. The function
τ ↦ (N − τ)/(τ + 1) decreases, so (N − t)/(t + 1) >= (N − √N)/(√N + 1) = √N − 2√N/(√N + 1) > √N − 2. Hence
m0 > √N − 3 >= 1, so m0 >= 2 and m >= m0 − 1 > √N − 4, m >= 1. Also m <= m0 <= (N − t)/(t + 1) < N/t < 2√N.
m is odd by construction, and t is a power of 2, so gcd(m,t) = 1. By the definition of the floor,
0 <= N − t − m0(t + 1) <= t; ℓ = N − t − m(t + 1) equals this number if m = m0 and exceeds it by t + 1 if
m = m0 − 1. (b) N >= 256 = 4^4 gives k >= 4, t >= 16; 4^k <= N gives k <= (1/2)log2 N. For x = √N >= 16,
x − 2 log2 x >= 8 (it is 8 at x = 16 and increasing for x >= 3), so m > √N − 4 >= log2 N + 3 >= 2k + 3.
(c) ⌈log2 t⌉ = k; t! <= t^{t−1}, so t! + 1 <= 2·t! <= 2^{k(t−1)+1} and ⌈log2(t! + 1)⌉ <= k(t − 1) + 1; thus
r_max <= kt. (t − 1)·t! <= t·t^{t−1} = 2^{kt}. Finally k <= (1/2)log2 N and t <= √N. ∎

**Proposition 6.2 (main inequality).** Assume H(γ,h). Let N >= 256 and let C be any circuit of size s
computing L_N. Then

    s >= t·m − r_max − 1
         + [ (t − 1)·m − r_max − log2((t − 1)·t!) − 5 − 3·log2(2s + 1) − h(2s) ] / (2γ).       (6.1)

*Proof.* Let F = L_N (as a function on {0,1}^N), Y the payload variables, ρ* as in §2.4 and g = g_N, so
g(c) = F(c ∪ ρ*). By Lemma 2.7, g has D(K1,K2) with K1 = t >= 2, K2 = t! + 1 >= 2 and N1(g) = e >= 2^{m(t−1)}.

(1) F is neither constant nor a projection x ↦ x_k. Otherwise g would be constant or a projection onto one
payload variable, hence would not depend on a set of at least t·m − 1 payload variables; but by Lemma 3.2
every such set has at most r_max <= kt elements, and t·m − 1 − kt = t(m − k) − 1 >= 16(k + 3) − 1 > 0
(Lemma 6.1(b)).

(2) Apply Lemma 1.1 (N >= 1): C' of size s' <= s computes F, in normal form. Let n_u be its number of used
inputs and r the number of payload variables unused in C'. An unused input influences no node value, so g does
not depend on these r variables, and r <= r_max by Lemma 3.2. Every used payload variable is a used input, so
n_u >= t·m − r.

(3) Lower bound on the cutwidth. N1(g)/2^r >= 2^{m(t−1) − r_max}, and by Lemma 6.1(b),(c)
m(t − 1) − r_max >= (2k + 3)(t − 1) − kt = kt + 3t − 2k − 3 >= k(t − 1) + 1 >= ⌈log2(t! + 1)⌉, using
3t >= k + 4. So N1(g) >= 2^r·K2, and Corollary 4.5 gives, with G = G(C'), V = 2s' + 1 and
Λ = log2 N1(g) − r − log2((t − 1)·t!):

    cw(G) >= Λ − 2 − log2 V.

(4) Upper bound on the cutwidth. By Lemma 4.2, G is connected, loopless, of maximum degree 3, and
μ = E − V + 1 = s' − n_u + 1. If μ >= 2, Proposition 5.5 and H(γ,h) applied to the kernel K (a connected
cubic multigraph on 2(s' − n_u) vertices) give cw(G) <= 2γ(s' − n_u) + h(2(s' − n_u)) + 3 + 2 log2 V. With (3),
and since 2(s' − n_u) <= 2s' <= 2s, h is nondecreasing and V <= 2s + 1,

    s' − n_u >= X/(2γ),    X := Λ − 5 − 3·log2(2s + 1) − h(2s).

If μ <= 1, Proposition 5.5 gives cw(G) <= 3 + 2 log2 V, so by (3) Λ − 5 − 3 log2 V <= 0, hence X <= 0 (as
h >= 0 and V <= 2s + 1); and s' − n_u = μ − 1 >= −1. In both cases s' − n_u >= −1 + X/(2γ).

(5) Therefore s >= s' >= n_u − 1 + X/(2γ) >= t·m − r − 1 + X/(2γ). Finally r <= r_max and
log2 N1(g) >= (t − 1)m only decrease the right-hand side when substituted, which gives (6.1). ∎

**Proof of Theorem 1.** Membership in P is §2.2. Let N >= 256, let C be a circuit of size s computing
L_N, and s_0 = ⌈(1 + 1/(2γ))N⌉. If s >= s_0, then s >= (1 + 1/(2γ))N >= (1 + 1/(2γ))N − R(N). Otherwise
2s + 1 < 2s_0 and 2s < 2s_0, so in (6.1) log2(2s + 1) < log2(2s_0) and h(2s) <= h(2s_0). Substituting
t·m = N − t − m − ℓ and (t − 1)m = N − t − 2m − ℓ into (6.1):

    s >= (1 + 1/(2γ))N − R_exact(N),                                                        (6.2)
    R_exact(N) = t + m + ℓ + r_max + 1
                 + [ t + 2m + ℓ + r_max + log2((t − 1)·t!) + 5 + 3·log2(2s_0) + h(2s_0) ] / (2γ).   (6.3)

By Lemma 6.1: t <= √N, m < 2√N, ℓ <= 2t + 1 <= 2√N + 1, r_max <= (1/2)√N log2 N and
log2((t − 1)t!) <= (1/2)√N log2 N. Hence the first line of (6.3) is at most 5√N + (1/2)√N log2 N + 2 and the
bracket at most 7√N + √N log2 N + 6 + 3 log2(2s_0) + h(2s_0); that is, R_exact(N) <= R(N) as displayed in §0.
Both cases give C_B2(L_N) >= (1 + 1/(2γ))N − R(N).

Limit. √N log2 N / N -> 0; s_0 <= (1 + 1/(2γ))N + 1, so log2(2s_0)/N -> 0; and
h(2s_0)/N = (h(2s_0)/(2s_0))·(2s_0/N) -> 0 because 2s_0 -> ∞, h(D)/D -> 0 and 2s_0/N is bounded. So for every
ε > 0 there is N_ε (depending on ε, γ and h) with R(N) <= εN for all N >= N_ε, and then
C_B2(L_N) >= (1 + 1/(2γ) − ε)N for EVERY integer N >= max(256, N_ε). This is the liminf statement. ∎
