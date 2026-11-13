# An explicit function that needs more than 4.67n gates

This repository contains a proof that an explicit Boolean function in P requires circuits of size at least
(4.6723 − o(1))·n over the full binary basis, together with the short program that certifies the one numerical
step of the proof.

Author: Arthur Ostapenko, November 2026.

**Status: not yet peer reviewed.** The proof was found and written with heavy use of AI models (Anthropic Claude
and OpenAI GPT models, directed by the author). It has been checked by several independent AI reviewers and by
exhaustive and interval-arithmetic computations, but no human expert has refereed it and it is not formalised.
Please read it as a claim with a complete written argument, and report any error you find (open an issue).

## The problem

A Boolean circuit computes a function f: {0,1}^n → {0,1} with gates of fan-in two. Here every one of the 16
two-input Boolean functions is allowed as a gate (the basis B2), fan-out is unrestricted, and the size is the
number of gates. Shannon showed in 1949 that almost all functions need about 2^n/n gates. Yet for *explicit*
functions (say, functions in P or NP) nobody can prove more than a linear lower bound. A superpolynomial bound for
a function in NP would give P ≠ NP. What is actually known is a small constant times n:

| year | bound | authors | method |
|---|---|---|---|
| 1984 | 3n − o(n) | Blum | gate elimination |
| 2016 | (3 + 1/86)n − o(n) | Find, Golovnev, Hirsch, Kulikov | gate elimination |
| 2022 | 3.1n − o(n) | Li, Yang | gate elimination |
| 2026 | 4n − O(log n) | Mishra, Santhanam | gate elimination |
| 2026 | (4.5624 − ε)n | McGuire, Schlesinger, Williams | cutwidth of the circuit's wire graph |
| 2026 | (4.6155 − ε)n | McGuire, Schlesinger, Williams | same, with a computer-assisted cutwidth bound (see their repository) |
| 2026 | **(4.6723 − ε)n** | this repository | same route, better cutwidth bound |

So the constant is still far from anything that separates complexity classes. It is, however, the place where
the difficulty of the problem can be measured, and each new technique that moves it is worth understanding.

## The result

**Theorem.** There is an explicit language L in P such that for every input length N ≥ 2^200, every B2 circuit
deciding L on inputs of length N has at least

    c·N − 35190.32·N/(log₂ N)²

gates, where c = 11459905344586199/2452706089845207 = 4.672351…, so for every ε > 0 and every sufficiently large N the size is at least
(4.6723 − ε)·N.

The function is the indicator of "the norm of z equals 1" for an element z of a finite field of characteristic 2,
where the polynomials defining the field are part of the input and are validated by the function itself. It is
defined at every input length.

The bound is asymptotic: the remainder becomes smaller than the main term only for very large N.

## How the proof goes

The route is the one introduced by McGuire, Schlesinger and Williams (November 2026). It does not eliminate
gates. It measures how much information has to cross a cut of the circuit.

1. **Wire graph.** A circuit with s gates and n inputs is turned into a graph of maximum degree 3 whose vertices
   are the points where wires meet. After removing vertices of degree at most 2 one is left with a cubic
   multigraph (the *kernel*) on D = 2(s − n) vertices, up to lower-order terms.
2. **From an ordering to a branching program.** Order the vertices of the kernel so that at every point of the
   order at most w edges cross from the left part to the right part (the *cutwidth* of the ordering). Sweeping
   the circuit in this order gives a read-once nondeterministic branching program for f with about 2^w states
   per layer: it only has to remember the values on the crossing wires.
3. **Hard function.** If the set of ones of f contains no large combinatorial rectangle under any partition of
   the variables, every such program needs 2^(n − o(n)) edges. For the norm indicator this property follows from
   a theorem of Kollár, Rónyai and Szabó on norm graphs (1996).
4. **Arithmetic.** If every cubic multigraph on D vertices has an ordering of cutwidth at most (γ + o(1))·D,
   then steps 1–3 give s ≥ (1 + 1/(2γ))·n − o(n). The trivial value γ = 1/6 gives exactly 4n. McGuire,
   Schlesinger and Williams prove γ ≤ 0.14035, which gives 4.5624n, and with a computer-assisted argument
   γ ≤ 0.13830, which gives 4.6155n.
5. **Cutwidth of cubic graphs — the new part.** We prove γ ≤ 0.13615254.
   - Give every vertex a Gaussian label that is correlated along non-backtracking walks, and order the vertices
     by label. This is the starting point of the earlier work (also Gaspers, 2026).
   - Improve the order locally, twice: first raise each label to the median of its neighbours' labels when that
     is larger, then lower it to the median when that is smaller. Each step removes vertices that sit on the
     wrong side of a cut.
   - Bound the cut at every threshold by a sum of local "window energies". A single window energy is not
     submodular, but the sum over the whole graph is. This needs weight exactly 1/2, and the property already fails
     for 0.51.
   - Global submodularity is enough for a Gaussian comparison argument: among all cubic multigraphs the
     infinite 3-regular tree is the worst case, because every other graph has larger correlations.
   - On the tree the bound becomes an explicit function G(t) of the threshold, a combination of three Gaussian
     probabilities. Its maximum is about 0.1361516, near t = 0.04.
6. **The numerical step.** A short Python program proves G(t) ≤ 0.13615254 for every real t, with interval
   arithmetic that it implements itself.
   - Two of the three probabilities are probabilities that a Gaussian vector lies in a convex set that moves
     linearly with t. Such functions are log-concave in t (Prékopa–Leindler). So lower bounds at the two ends
     of an interval give a lower bound inside it, with a loss of second order in the length of the interval.
   - Each probability is an integral of a function of the form e^(−q)·g with g log-concave. On a box such an
     integral is at least the volume times the geometric mean of the corner values times an explicit factor.
     This is second order and has no error term.
   - The real line is covered by two analytic tails and 114 intervals. Every interval bound is compared with
     the target in exact rational arithmetic.

## What is new here, and what is not

Not ours:
- the route of steps 1–4 (McGuire, Schlesinger, Williams),
- the idea of Gaussian orderings (McGuire, Schlesinger, Williams, and Gaspers),
- the norm-graph theorem (Kollár, Rónyai, Szabó),
- the trick of putting the field-defining polynomials into the input (credited in `proof.md`).

Ours: the cutwidth bound of step 5 — the two-step local improvement, the global submodularity lemma, the
comparison theorem in the form needed for it, and the certificate of step 6 — and a self-contained write-up of
the whole chain for a different explicit function, with an explicit remainder term.

## How it was checked, and what has not been checked

- The comparison theorem and the submodularity lemma were proved independently three times and attacked by
  several reviewers. The submodularity lemma was also verified by exhaustive enumeration (269 million
  configurations on the tree).
- The pointwise inequality "cut ≤ energy" was verified exhaustively on all cubic multigraphs with up to 8
  vertices (322 million cases).
- The numerical step is certified by `certify.py`. `certificate.md` proves, function by function, that its
  output implies the bound, including a full proof of the Prékopa–Leindler theorem. Three other programs,
  written independently with different methods, give the same maximum 0.1361516.
- The program's lower bounds were compared with direct quadrature and with a Monte Carlo simulation from the
  definition (24 million samples). They are below the true values everywhere, by about 10^-6 near the maximum.
- An automated proof reviewer, which runs the program itself in a sandbox and reads all files, accepted this
  version and six weaker earlier versions (constants from 4.5624 to 4.67233).
- **Not done:** review by a human expert and formal verification. The margin of the certificate is small
  (the target is the largest interval bound of the program itself, 0.13615254, against the true maximum
  0.1361516), and the new parts were written
  within one day.

## Repository layout

    proof.md          the function, the main theorem, and how the parts fit together (start here)
    circuit.md        steps 1–4: wire graph, kernel, branching program, edge lower bound
    cutwidth.md       step 5: the cutwidth theorem for cubic multigraphs
    certificate.md    step 6: the Prékopa–Leindler theorem, the lemmas behind the program, its error analysis
    certify.py        the program of step 6 (Python standard library only)
    krs.md            the norm-graph theorem with a complete proof
    earlier/          the first version of step 5 (γ ≤ 0.1375, constant 51/11 ≈ 4.636) with a certificate in C

To run the certificate (about four seconds):

    echo '{}' | python3 certify.py

It prints one JSON object. The fields to look at are `certified` (must be `true`), `cover` (104 base intervals,
119 leaves, contiguous from −5/4 to 2) and `largest_certified_bound` (0.136152539). The target is a binary
fraction, 2452706089845207/2^54, equal to the largest interval bound. If it is lowered, even by one unit in the
last binary digit, the program reports a failed interval.

## Where this could go next

- **Better cutwidth constant.** The exact cut (instead of the energy with weight 1/2) would give γ ≈ 0.1323,
  that is about 4.78n, if the comparison with the tree could be proved for it. Numerically it holds. More rounds
  of local improvement give a little more.
- **Limit of the route.** Random cubic graphs have bisection width at least 0.10329·D (Lichev, Mitsche), so no
  cutwidth bound can take this argument beyond about 5.84n.
- **Beyond wires.** The branching program remembers one bit per crossing wire. Counting the information that
  actually has to cross, rather than the wires, is not limited by the cutwidth of cubic graphs. We do not know how
  to do this yet.
- None of this is superlinear. Any idea that gives a growing constant would be far more interesting than a
  better γ.

## References

- C. E. Shannon, The synthesis of two-terminal switching circuits, Bell System Tech. J. 28 (1949), 59–98.
- N. Blum, A Boolean function requiring 3n network size, Theoret. Comput. Sci. 28 (1984), 337–345.
- M. G. Find, A. Golovnev, E. A. Hirsch, A. S. Kulikov, A better-than-3n lower bound for the circuit complexity
  of an explicit function, FOCS 2016.
- J. Li, T. Yang, 3.1n − o(n) circuit lower bounds for explicit functions, STOC 2022.
- O. S. Mishra, R. Santhanam, An explicit 4n − O(log n) size lower bound against general Boolean circuits,
  ECCC TR26-260, revision 1 (3 November 2026).
- S. McGuire, S. Schlesinger, R. Williams, Explicit functions requiring larger than 4.5n size circuits,
  preprint, November 2026. The (4.6155 − ε)n bound: https://github.com/rrwilliams0/circuit-lb-4.6155n
- S. Gaspers, Path decompositions of sparse graphs via Gaussian sweeps and faster exponential algorithms,
  arXiv:2611.05146 (2026).
- J. Kollár, L. Rónyai, T. Szabó, Norm-graphs and bipartite Turán numbers, Combinatorica 16(3) (1996), 399–406.
- A. Prékopa, On logarithmic concave measures and functions, Acta Sci. Math. (Szeged) 34 (1973), 335–343.
- L. Leindler, On a certain converse of Hölder's inequality II, Acta Sci. Math. (Szeged) 33 (1972), 217–223.
- L. Lichev, D. Mitsche, On the minimum bisection of random 3-regular graphs, Electron. J. Combin. 30(2) (2023),
  P2.40.

## License

Text (`*.md`): CC BY 4.0, see `LICENSE-TEXT`. Code (`certify.py` and the programs in `earlier/`): MIT, see
`LICENSE-CODE`.
