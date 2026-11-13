# A 4.67235·N − O(N/log² N) circuit lower bound: a validated-field family and a cutwidth argument

## Claim

Let L be the single total language defined in §1, A its evaluator and L_N its slice at length N, with
**N denoting the entire input length**.

**Main Theorem**. A runs in polynomial time on every input, so L is in P; L is in
NP with witness bound W(N) = 0 and the fixed verifier V that accepts (x, w) iff w is empty and A(x) = 1. In the
full B2 model, with N the entire input length: for every integer N >= 2^200,

    C_B2(L_N) >= (11459905344586199/2452706089845207)·N − K·N/(log2 N)²,
    K = 287704960015153634328733/8175686966150690000 = 35190.31014…

**Corollary.** Liminf over all integers N of C_B2(L_N)/N >= 11459905344586199/2452706089845207; equivalently,
for every real ε > 0 there is N_ε such that C_B2(L_N) >= (11459905344586199/2452706089845207 − ε)·N for
every integer N >= N_ε.

**Route.** Put

    γ_d = 2452706089845207/2^54 = 0.13615253867…,   c* = 1 + 1/(2γ_d) = 11459905344586199/2452706089845207 = 4.67235164…

We prove that for every integer N >= 256

    C_B2(L_N) >= c*·N − R(N),                                                         (★)

with the explicit remainder R(N) of §6.1, and that R(N) < K·N/(log2 N)² with K = (c* − 1)·9582.5001 + 0.0001
(the value displayed in the Main Theorem) for every N >= 2^200 (§6.3); the Main Theorem follows with
N_0 = 2^200, and the Corollary with
N_ε = 2^max(200, ⌈√(K/ε)⌉) (§6.4). The result is this eventual lower bound: leading coefficient
**c* = 11459905344586199/2452706089845207 (= 4.67235164…), exponent 1** (§6.2), explicit remainder
**K·N/(log2 N)², K = 287704960015153634328733/8175686966150690000 (= 35190.31014…)**, at every integer
N >= N_0 = 2^200.

**Attribution.**
* **Method.** The route circuit -> wire graph -> cutwidth ordering -> read-once nondeterministic program ->
  rectangle edge counting is from S. McGuire, S. Schlesinger, R. Williams, "Explicit functions requiring larger
  than 4.5n size circuits", preprint, November 2026; the authors report a Lean 4 formalization (§8). Their hard
  function is a sumset extractor of Li. Ordering the vertices of a cubic graph by thresholds of a Gaussian field is
  due to that preprint and to S. Gaspers (arXiv:2611.05146). These sources are credited, not used as premises:
  every step is re-proved in `circuit.md`, `cutwidth.md` and `certificate.md`.
* **Cutwidth constant.** The bound cw <= (2452706089845207/2^54)·D + h_d(D) is proved in `cutwidth.md`. Two of its
  ingredients are new here: the comparison of a non-backtracking-walk Gaussian field on any cubic multigraph with
  the same field on the 3-regular tree, for local functionals of the threshold pattern whose formal sum over the
  tree is submodular although the single local terms are not (`cutwidth.md` Theorem 3.3 and Lemma 4.4), and a
  post-processing of the level sets by two local set maps. They reduce the constant to an integral on the tree,
  which is bounded in `certificate.md` with the program `certify.py` (interval
  arithmetic).
* **Norm graphs.** The rectangle property of the hard function rests on a theorem of J. Kollár, L. Rónyai and
  T. Szabó (premise P1), proved in `krs.md` along the lines of their proof.
* **Validated prefix.** Making the field-defining polynomials part of the input, checked by an exact test, is
  due to mooselumph (GitHub), who used it in a 4n lower bound for a certificate-prefix family.
* **This text** is an independent write-up with a different explicit function: the indicator of z^e = 1,
  e = 1 + q + ... + q^{t−1} with q = 2^m, for the payload element z of a field with q^t elements whose two
  defining polynomials are validated input prefixes (the condition defining the norm graphs of Kollár, Rónyai
  and Szabó). The cutwidth bound is proved for all cubic multigraphs with loops and parallel edges, with an
  explicit remainder, so the final remainder is explicit.

**The numerical step.** There is exactly one program, `certify.py` (Python standard library only, its own outward-rounded interval
arithmetic; `math.sqrt` serves only as the start value of two verified square-root loops); it runs in a
few seconds (pure Python). It establishes
`cutwidth.md` Proposition C (sup_t G_d(t) <= γ_d = 2452706089845207/2^54), the only step of the proof that rests on a
computation; its method and error analysis are in `certificate.md` (§6 there), and its output object reports
`certified: true` together with the cover and the largest certified bound. The same program re-checks by
exhaustive enumeration the finite facts (C1) window energy, (C2) tree vector and (C6) global submodularity of
`cutwidth.md` and the rational witnesses (N1)–(N8) of its §7 (C4), all of which are also proved in the text.
Every other numerical fact is proved with rational witnesses (§6.2–§6.3, `cutwidth.md` §7).

## 1. The family: one evaluator on every bit string

### 1.1 Length parameters and input layout

For an integer N >= 16 define

    k  = the largest integer with 4^k <= N,      t = 2^k,
    m0 = ⌊(N − t)/(t + 1)⌋,   m = m0 if m0 is odd, m = m0 − 1 if m0 is even,
    ℓ  = N − t − m − t·m.

Thus t is a power of two, m is odd and gcd(m, t) = 1. An input x = x_1 … x_N is split, in this order, into the
**R-prefix** x_1..x_t, the **Q-prefix** x_{t+1}..x_{t+m}, the **payload** of t·m bits c_{u,v} (0 <= u < m,
0 <= v < t; c_{u,v} is bit number t + m + v·m + u + 1), and ℓ **leftover** bits. So N = t + m + t·m + ℓ exactly.

### 1.2 The evaluator A

On x ∈ {0,1}^N:

1. If N < 16, output 0.
2. Compute k, t, m, ℓ as above. If m < 1, output 0.
3. Let R(W) = W^t + Σ_{v<t} x_{v+1} W^v ∈ F_2[W] and Q(Z) = Z^m + Σ_{u<m} x_{t+u+1} Z^u ∈ F_2[Z].
   If IrrTest(R) or IrrTest(Q) rejects, output 0.
4. Let F = F_2[Z]/(Q) and E = F[W]/(R). Form z = Σ_{v<t} (Σ_{u<m} c_{u,v} Z^u) W^v ∈ E.
5. Let e = Σ_{j=0}^{t−1} 2^{m·j}. Compute z^e in E by square-and-multiply. Output 1 iff z^e = 1.

The leftover bits are never read. **IrrTest(P)**, for a monic P ∈ F_2[X] of degree d >= 1, accepts iff
X^{2^d} ≡ X (mod P) and, for every divisor d' of d with 1 <= d' < d, gcd(P, (X^{2^{d'}} − X) mod P) = 1, where
X^{2^j} mod P is computed by j successive squarings modulo P.

L = {x : A(x) = 1} and L_N = L ∩ {0,1}^N. This defines L_N at **every** length, including N < 16, the guard
m < 1 (which never fires for N >= 16, `circuit.md` Lemma 6.1(a)) and every invalid prefix. The polynomials R and
Q are input bits checked by the evaluator; they are not advice and not the output of a construction algorithm.
When both prefixes pass, E is a field with 2^{tm} elements (`circuit.md` Lemmas 2.2 and 2.4).

## 2. Uniform P and NP with empty witnesses

A runs in O(N^4) bit operations on every input (`circuit.md` §2.2), so L ∈ P. Let V(x, w) accept exactly when w
is the empty string and A(x) = 1, with witness bound W(N) = 0. If x ∈ L, the empty witness is accepted. If
V(x, w) = 1 for some permitted w, then A(x) = 1 and x ∈ L. This proves both directions with one fixed
polynomial-time verifier for all lengths. Witnesses are not circuit inputs.

## 3. Circuit model and coverage

The bound is for the full B2 model (Li–Yang, ECCC TR21-023, 2021-02-20, Sections 1.1, 2.1, 2.4 and 3.3):
deterministic acyclic circuits with one output, two ordered input pins per gate, any of the 16 binary truth
tables per gate (constants, projections and negated projections included), unrestricted fan-out and depth,
repeated pins and shared subcircuits allowed, exact computation on every input of length N, nonuniform circuits.
Every gate is counted once; inputs, wires and output selection cost nothing. The formal model is `circuit.md` §1.

* **All gate types, repeated pins, sharing.** The only gate-dependent step is the local rule
  β(e_g) = φ_g(β(p_1), β(p_2)) of `circuit.md` Theorem 4.4, valid for every φ_g; degenerate gates are counted like
  all others. A gate with both pins fed by one node has two distinct pin edges (`circuit.md` Definition 4.1),
  counted twice in Lemma 4.2; their equal values are forced by the copy rules, not assumed.
* **No substitution into circuits.** The proof never fixes inputs of a circuit. It compiles the whole circuit
  (with its R-, Q-prefix and leftover inputs) into a read-once program and restricts the *program*
  (`circuit.md` Lemma 3.1, Corollary 4.5). Hence constant nodes created by substitutions never arise.
* **Constant nodes.** If the model admits free constant nodes at all, `circuit.md` Lemma 1.1(i) removes them by
  absorbing each constant into the truth table of the gate it feeds; a gate with two constant pins becomes a
  constant-type gate reading x_1 twice. No gate is added, no gate is removed except non-ancestors of the output
  (Lemma 1.1(ii)), and no uncharged basis element is introduced. If the model has no constant nodes this step is
  void.
* **Terminal cases.** L_N is neither constant nor a projection for N >= 256 (`circuit.md` Proposition 6.2(1)),
  so after Lemma 1.1 the output is a gate and every other gate has fan-out >= 1. Inputs of fan-out 0 get no
  vertex and are never read (Theorem 4.4); unused payload variables are counted by r (Proposition 6.2(2)). Wire
  graphs that are trees or unicyclic are handled in Proposition 6.2(4).
* **Every length, invalid prefixes.** A is defined on all strings and (★) holds at every integer N >= 256.
  Every circuit must compute L_N on all inputs, including invalid prefixes; the lower bound uses only the
  restriction of the compiled program to one valid prefix pair (`circuit.md` §2.4, Corollary 4.5), which exists
  at every N >= 16 (`circuit.md` Lemma 2.3).

## 4. Structure of the proof

* `circuit.md` **Theorem 1** (circuit side): if the graph hypothesis H(γ,h) of `circuit.md` §0 holds, then for
  every N >= 256, C_B2(L_N) >= (1 + 1/(2γ))N − R(N) with R as in §6.1. Chain: normal form (Lemma 1.1); the
  restricted payload function has property D(t, t! + 1) and e ones (Lemmas 2.1–2.7, with P1 in Lemma 2.6); edge
  lower bound for read-once programs (Lemmas 3.1–3.2, Theorem 3.3); wire graph and sweep program (Lemma 4.2,
  Theorem 4.4, Corollary 4.5); kernel (Lemmas 5.1–5.4, Proposition 5.5); parameters and the main inequality
  (Lemma 6.1, Proposition 6.2). Theorem 1 is stated and proved for every γ > 0 and every admissible h; here it
  is used with γ_d = 2452706089845207/2^54 and h_d (§6.1).
* `cutwidth.md` **Theorem 1** (graph side): H(γ_d, h_d) holds with γ_d = 2452706089845207/2^54 and h_d as in §6.1.
  Chain: walks, the universal cover and its deck transformations (§1); the non-backtracking-walk field and the
  lifting lemma (§2, Lemmas 2.1–2.3, with tree correlations in closed form and an error bound valid for every
  walk length); Gaussian comparison by interpolation and smoothing, for two fields (Lemma 3.2) and globally on
  the tree (Theorem 3.3); the set maps E, D, the charging inequalities, the window energy f and the global
  submodularity of its formal sum (§4, Lemma 4.4); the tree vector and the reduction of the constant to
  G_d(t) = V − (3/2)P2 + P3/2 (§5); Proposition C, sup_t G_d(t) <= 2452706089845207/2^54, stated in §6 and proved in
  `certificate.md`; ties, threshold grid, concentration and the explicit remainder (§7, with rational
  witnesses (N1)–(N8)).
* `certificate.md`: the proof of `cutwidth.md` Proposition C. Theorem PL (log-concavity of Gaussian
  marginals) and Lemmas 5.9–5.12, with proofs; then §6.1–§6.6 there: what is checked, the arithmetic, the lower
  bound of P4 = Φ − V, the lower bound of P2, the leaf bound with P3 and the tails, and the run of the program `certify.py`.
* `krs.md`: premise P1 (Kollár–Rónyai–Szabó, Combinatorica 16(3) (1996) 399–406, Theorem 3.3; stated in
  `circuit.md` §0 and `krs.md` §0), proved for every field via Theorem A (`krs.md` §0, §3).
* §6 below combines them and does the arithmetic.

## 5. Facts used without proof

* Textbook commutative algebra F1–F6 (Atiyah–Macdonald; Milne) and elementary facts E1–E5: `krs.md` §2.
* Textbook algebra (S1)–(S6): `circuit.md` §0.
* Undergraduate analysis and probability, basic Lebesgue integration (Tonelli, monotone convergence, inner
  regularity, the layer-cake formula), one-dimensional Gaussian integration by parts, Fourier uniqueness on
  L¹(R) and the generating function of the Hermite polynomials: the list in `cutwidth.md` §1.0.
* **One finite computation**: `cutwidth.md` Proposition C (sup over all real t of G_d(t) <= γ_d =
  2452706089845207/2^54) is established by the program `certify.py` (Python standard
  library only, its own outward-rounded interval arithmetic; `math.sqrt` serves only as the start value of
  two verified square-root loops), which anyone can run in a few seconds; its method and
  error analysis are in `certificate.md` (§6 there), and its output object reports `certified: true` together
  with the cover and the largest certified bound. The same program re-checks by exhaustive enumeration the
  finite facts (C1), (C2), (C6) and the rational witnesses of `cutwidth.md` §7 (C4), all of which are also
  proved in the text. The arithmetic model it assumes (IEEE 754 binary64, `cutwidth.md` §1.0) and every
  enclosure it uses are stated and proved in `certificate.md`.

Nothing else is used without proof. The Li–Yang paper fixes the model conventions only. The sources credited in
§8 are not premises. No deterministic construction of irreducible polynomials, no prime number theorem and no
Bertrand postulate is used: the field-defining polynomials are input bits, and their existence (`circuit.md`
Lemma 2.3) is used only inside the lower-bound proof.

## 6. The main theorem and its derivation

### 6.1 Combining `circuit.md` and `cutwidth.md`

`cutwidth.md` Theorem 1 is the hypothesis H(γ,h) of `circuit.md` §0 with γ = γ_d = 2452706089845207/2^54 and

    h_d(D) = (24568891674377769/18014398509481984)·D                         for 1 <= D < 2^40,
    h_d(D) = min{ (24568891674377769/18014398509481984)·D,  958·D/(log2 D − 3)² + 38·D^{8/9} }   for D >= 2^40,

where 24568891674377769/18014398509481984 = 3/2 − γ_d.

`cutwidth.md` Theorem 1 proves cw(K) <= γ_d·D + h_d(D) for every cubic multigraph K on D vertices, connected or
not, and that h_d is nonnegative, nondecreasing on the positive integers and o(D). Both files use the same class
(cubic multigraphs; loops and parallel edges allowed; a loop adds 2 to the degree), the same cut convention (a
loop never crosses a cut, parallel edges count separately) and the same cutwidth (maximum over prefix cuts,
minimum over orderings; `cutwidth.md` §0 and `circuit.md` Definition 4.3). `circuit.md` applies H(γ,h) only to the
kernel K of Lemma 5.2, which is a connected cubic multigraph in exactly this sense, on D = 2(s' − n_u) >= 2
vertices, and evaluates h only at positive integers. So `circuit.md` Theorem 1 applies and gives (★) for every
integer N >= 256 with c* = 1 + 1/(2γ_d) = 11459905344586199/2452706089845207 and

    R(N) = 5√N + (1/2)√N·log2 N + 2
           + (c* − 1)·[ 7√N + √N·log2 N + 6 + 3·log2(2s_0) + h_d(2s_0) ],     s_0 = ⌈c*·N⌉.

(Here 1/(2γ_d) = c* − 1 = 2^53/2452706089845207 = 9007199254740992/2452706089845207.) For N < 256 one may
set R(N) = c*·N; then (★) holds trivially at every
length.

### 6.2 The leading coefficient: c* = 11459905344586199/2452706089845207

c* = 1 + 1/(2·2452706089845207/2^54) = 1 + 2^53/2452706089845207 = 1 + 9007199254740992/2452706089845207 =
11459905344586199/2452706089845207, and this is the leading coefficient of the Main Theorem, with exponent 1. It is positive, and the fraction is reduced: 11459905344586199 = 2452706089845207 + 2^53
(2^53 = 9007199254740992), so gcd(11459905344586199, 2452706089845207) = gcd(2^53, 2452706089845207) = 1,
because 2452706089845207 is odd. Also c* < 5 (5 − c* = 803625104639836/2452706089845207) and
c* − 1 = 2^53/2452706089845207 = 3.67235164… < 3.6723517 (as 3.6723517·2452706089845207 =
9007199378643398.6633019 > 2^53).

### 6.3 The remainder: R(N) < K·N/(log2 N)² for every N >= 2^200

Let N >= 2^200 and L = log2 N >= 200.

* s_0 = ⌈c*·N⌉ = ⌈11459905344586199N/2452706089845207⌉ <= 5N (as (5 − c*)N =
  803625104639836N/2452706089845207 >= 1), so 2s_0 <= 10N and 3·log2(2s_0) <= 3(L + 4).
* h_d is nondecreasing and 10N >= 2^40, so h_d(2s_0) <= h_d(10N) <= 958·10N/(log2(10N) − 3)² + 38·(10N)^{8/9}.
  Here log2(10N) − 3 > L (as 10 > 8), and 10^{8/9} < 7.75 (since 7.75⁹ > 10⁸), 38·7.75 = 294.5; so
  h_d(2s_0) < 9580·N/L² + 294.5·N^{8/9}.
* 294.5·N^{8/9} = 294.5·N·2^{−L/9} <= 2.5·N/L²: the function L²·2^{−L/9} decreases for L > 18/ln 2 (< 26), and
  at L = 200 the inequality 294.5·200²·2^{−200/9} <= 2.5 is equivalent to (294.5·40000/2.5)⁹ <= 2^200, which
  holds ((294.5·40000/2.5)⁹ = 4712000⁹ < 1.15·10⁶⁰ < 1.6·10⁶⁰ < 2^200).
* The remaining terms are tiny: √N = 2^{L/2}, and 7√N + √N·L + 6 + 3(L + 4) <= 9·L·2^{L/2} <= 10⁻⁴·N/L² because
  9L³ <= 10⁻⁴·2^{L/2} at L = 200 (9·8·10⁶ = 7.2·10⁷ <= 10⁻⁴·2^100, as 2^100 > 10^30) and L³·2^{−L/2} decreases
  for L > 6/ln 2. Likewise 5√N + (1/2)√N·L + 2 <= L·2^{L/2} <= 10⁻⁴·N/L².

Therefore the bracket is less than (9580 + 2.5 + 0.0001)·N/L² = 9582.5001·N/L² (strictly, because the bound
on h_d(2s_0) is strict), and as c* − 1 > 0,

    R(N) < [0.0001 + (c* − 1)·9582.5001]·N/L² = K·N/(log2 N)²,
    K := 0.0001 + (2^53/2452706089845207)·(95825001/10000) = 287704960015153634328733/8175686966150690000

(35190.31014 < K < 35190.31015). Hence R(N) < K·N/(log2 N)² for every integer N >= 2^200. K is positive and
the fraction is reduced: with 2452706089845207 = 3·817568696615069 and 95825001 = 3·31941667,
K = (817568696615069 + 2^53·31941667)/(10⁴·817568696615069); the numerator 817568696615069 + 2^53·31941667 =
287704960015153634328733 is odd, is ≡ 3 (mod 5) (as 817568696615069 ≡ 4, 2^53 ≡ 2 and 31941667 ≡ 2), and is
coprime to 817568696615069 because gcd(2^53·31941667, 817568696615069) = gcd(31941667, 817568696615069) = 1
(817568696615069 is odd; Euclid's remainders: 9416509, 3692140, 2032229, 1659911, 372318, 170639, 31040, 15439,
162, 49, 15, 4, 3, 1).

### 6.4 Conclusion

Let N >= N_0 = 2^200 be any integer. By (★), §6.2 and §6.3,

    C_B2(L_N) >= c*·N − R(N) > (11459905344586199/2452706089845207)·N − K·N/(log2 N)²,
    K = 287704960015153634328733/8175686966150690000.

This holds at **every** integer length N >= 2^200, not on a subsequence, for the one fixed language L with its
one verifier and witness bound 0. This is the Main Theorem, with N_0 = 2^200: an
eventual lower bound with leading term (11459905344586199/2452706089845207)·N and the single explicit remainder
term K·N/(log2 N)², K = 287704960015153634328733/8175686966150690000.

Corollaries. Let ε > 0 and N >= N_ε = 2^max(200, ⌈√(K/ε)⌉), any integer, K as in §6.3. Then
(log2 N)² >= K/ε, so K·N/(log2 N)² <= εN and C_B2(L_N) >= (c* − ε)·N. Since ε > 0 is arbitrary,

    liminf over all integers N of C_B2(L_N)/N >= c* = 11459905344586199/2452706089845207,

that is, the constant 11459905344586199/2452706089845207 with exponent 1.

## 7. Bit accounting

* N = t + m + t·m + ℓ exactly. The R- and Q-prefixes (t + m <= 3√N bits) and the leftover (ℓ <= 2√N + 1 bits)
  are real circuit inputs; they are charged twice in the exact remainder (`circuit.md` (6.3)): once in the
  linear term, since they are not payload inputs and do not contribute to n_u, and once in the bracket, since
  they do not contribute to log2 N1. The payload loses m bits of density (N1 = e, not 2^{tm}) and
  O(√N log N) bits for the rectangle parameters (r_max and log2((t − 1)·t!)). The other losses are
  (3·log2(2s_0) + 5 + h_d(2s_0))/(2γ_d), from the program size and the cutwidth remainder. All are o(N); no
  linear loss is hidden.
* No formula, monotone, bounded-depth, XOR-free, multi-output, randomized or average-case statement is used, so
  no transfer is needed. No direct-sum additivity is assumed and no potential is identified with a gate count:
  the bound counts the gates of an arbitrary circuit through the exact vertex and edge counts of its wire graph
  (`circuit.md` Lemma 4.2).

## 8. Sources

* S. McGuire, S. Schlesinger, R. Williams, "Explicit functions requiring larger than 4.5n size circuits",
  preprint, November 2026. The authors' Lean 4 formalization: github.com/SamuelSchlesinger/circuit-lb-4.56n-lean
  (commit b7c27d13c0545dedd78ec2614ca6792df160e8ed, 2026-10-13). Credit for the circuit-to-cutwidth route and the
  Gaussian ordering of cubic graphs; not a premise. The same authors have a computer-assisted cutwidth constant
  of about 0.1383 in this normalisation, i.e. (4.6155 − ε)n (public repository
  github.com/rrwilliams0/circuit-lb-4.6155n); not used here.
* S. Gaspers, arXiv:2611.05146v1 (preprint, November 2026): Gaussian threshold orderings of cubic graphs. Credit;
  not used.
* J. Kollár, L. Rónyai, T. Szabó, "Norm-graphs and bipartite Turán numbers", Combinatorica 16(3) (1996)
  399–406, Theorem 3.3: premise P1, proved in `krs.md`.
* N. Alon, L. Rónyai, T. Szabó, "Norm-graphs: variations and applications", J. Combin. Theory Ser. B 76 (1999)
  280–290: P1 with the indices exchanged (`krs.md` Theorem A).
* M. F. Atiyah, I. G. Macdonald, Introduction to Commutative Algebra, Addison-Wesley, 1969; J. S. Milne, Fields
  and Galois Theory, version 5.10: the textbook facts F1–F6 of `krs.md` §2.
* Li–Yang, ECCC TR21-023, 2021-02-20, Sections 1.1, 2.1, 2.4 and 3.3: the full-B2 conventions. Its
  lower-bound arguments are not used.
* mooselumph (GitHub), a 4n lower bound for a certificate-prefix family: the validated-prefix device. Its family
  and arguments are not used.
* Standard tools re-proved in `cutwidth.md`, credited as such: Gaussian interpolation (Slepian, Kahane) and
  Mehler's formula for the bivariate normal law; in `certificate.md`: the Prékopa–Leindler inequality (Prékopa
  1971/1973, Leindler 1972) and the log-concavity of Gaussian marginals (Theorem PL and its corollary there).
* `certificate.md` with the program `certify.py`: the proof of `cutwidth.md`
  Proposition C.
