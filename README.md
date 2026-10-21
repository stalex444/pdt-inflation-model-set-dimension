# The least physical dimension of an inflation-symmetric model set

Kernel-checked, in Lean 4 + Mathlib. Fix the integer lattice `ℤ^ι ⊂ ℝ^ι` and an integer matrix
`A`. An `A`-invariant cut-and-project scheme splits `ℝ^ι = E ⊕ H` into `A`-invariant subspaces
with `ℤ^ι ∩ H = 0` and `π_H(ℤ^ι)` dense in `H`; a window `W ⊆ H` gives the model set
`Λ(W) = {π_E γ : γ ∈ ℤ^ι, π_H γ ∈ W}`; and the scheme is admissible if some window gives
`A Λ(W) ⊆ Λ(W)`, inflation symmetry in Meyer's inclusion sense. The entry determines `d(A)`, the
least physical dimension `dim E` of an admissible scheme:

* for every integer `A`, admissibility is power-boundedness of `A` on `H` (1), and density is
  Kronecker's criterion (2);
* for `det A ≠ 0` and `χ_A` squarefree over `ℚ`, the admissible splittings are characterized and
  `d(A) = U(A) + circleCount A`, where `U(A)` counts the eigenvalues of modulus `> 1` and
  `circleCount A` counts `1` for each factor `x ± 1` and `2` for each other cyclotomic factor (3);
* for hyperbolic `A`, any `χ_A`, `d(A) = U(A)`, attained only by the unstable/stable splitting
  `(E^u, E^s)` (4);
* `d(A) = 1` exactly for the Pisot and Salem cases (5), the cyclotomic case gives planes (6), and
  the squarefree hypothesis of (3) cannot be dropped (7);
* model sets are Delone sets with uniformly discrete difference sets (13).

These are then applied to multiplication by `ρ` (`ρ³ = ρ + 1`), `Q` (`Q⁴ = Q + 1`),
`θ = −Q⁻¹ = 1 − Q³` and their products on `ℤ[ρ]`, `ℤ[Q]` and the degree-12 lattice
`ℤ[ρ] ⊗ ℤ[Q]` (8)–(11), with a Salem witness (12). Thirteen compared theorems; every one on the
axioms `propext`, `Classical.choice`, `Quot.sound` alone.

## The compared statements

Namespace `ModelSetDimension`. The exact Lean is in `Challenge.lean`; the definitions it uses are
stated there, between `-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`.

1. `admissibility_criterion` — for every integer `A`: a scheme is admissible if and only if `A` is
   power-bounded on `H`; then the orbit window `W_* = {h ∈ H : ‖Aⁿ h‖ ≤ 1 for all n}` (sup norm)
   is a compact, convex, centrally symmetric window with `A W_* ⊆ W_*` and
   `A Λ(W_*) ⊆ Λ(W_*)`. For each window, `A Λ(W) ⊆ Λ(W)` if and only if `A` maps the lattice
   points `W ∩ π_H(ℤ^ι)` into `W`; for a closed window contained in the closure of its lattice
   points, if and only if `A W ⊆ W`. Admissibility puts every eigenvalue of `A|_H` in the closed
   unit disk, so `U(A) ≤ dim E`.
2. `kronecker_density_criterion` — for complementary `E`, `H`, the projection of `ℤ^ι` to `H`
   along `E` is dense in `H` if and only if every real functional that is integer-valued on
   `ℤ^ι` and vanishes on `E` is zero.
3. `least_physical_dimension_squarefree` — for `det A ≠ 0` and `χ_A` squarefree over `ℚ`:
   (a) every `A`-invariant splitting is `E = ker q_E(A)`, `H = ker q_H(A)` with `χ_A = q_E q_H`
   over `ℝ`, `q_E`, `q_H` the characteristic polynomials of `A|_E`, `A|_H`; (b) it carries an
   admissible scheme if and only if every root of `q_H` lies in the closed unit disk and every
   irreducible factor of `χ_A` over `ℚ` shares a complex root with `q_E`; (c)
   `d(A) = U(A) + circleCount A`; (d) an irreducible factor has all its roots on the unit circle
   if and only if it is cyclotomic.
4. `hyperbolic_case` — for `det A ≠ 0` and no eigenvalue on the unit circle, any `χ_A` (no
   diagonalizability): a scheme is admissible if and only if `E ⊇ E^u(A)`, if and only if
   `H ⊆ E^s(A)`; `(E^u, E^s)` carries an admissible scheme; `d(A) = U(A)`; and every admissible
   scheme with `dim E = U(A)` is `(E^u, E^s)`. Here `E^u` is the set of vectors with a backward
   orbit tending to `0`, `E^s` the set of vectors whose forward orbit tends to `0`.
5. `dimension_one_pisot_or_salem` — for `det A ≠ 0` and `χ_A` squarefree: `d(A) = 1` if and only
   if `χ_A` is irreducible with exactly one root of modulus `> 1`, or `A = ±1` on `ℤ¹`; in the
   irreducible case that root `r` is real, every other root has modulus at most `1` (so `|r|` is
   a Pisot number, a Salem number, or for `#ι = 1` an integer `≥ 2`), and every admissible scheme
   with `dim E = 1` has `E` the `r`-eigenline.
6. `finite_order_case` — for `χ_A` squarefree with all roots on the unit circle: every
   irreducible factor is cyclotomic and `d(A) = Σ_p min(deg p, 2)`; every integer matrix with
   `χ_A = Φ_n`, `n ≥ 3` (multiplication by `ζ_n` on `ℤ[ζ_n]`), has `d = 2`.
7. `squarefree_hypothesis_needed` — on `ℤ²`, `I₂` and `J₂ = [[1, 1], [0, 1]]` both have
   `χ = (x − 1)²`, for which the count of (3) gives `2`; but `d(I₂) = 1` and `d(J₂) = 2`.
8. `sector_rings` — `Cρ`, `Cρ² − 1`, `CQ`, `1 − CQ³` (multiplication by `ρ`, `ρ⁻¹`, `Q`, `θ` on
   `ℤ[ρ]`, `ℤ[Q]` in the power bases) have characteristic polynomials `x³ − x − 1`,
   `x³ + x² − 1`, `x⁴ − x − 1`, `x⁴ − x³ − 1`, are hyperbolic, and have `d = 1, 2, 3, 1`; the one
   expanding eigenvalue of `θ` is real, `θ₄ = −1/q′ ∈ (1.3802, 1.3803)`, `q′` the negative root
   of `x⁴ − x − 1`.
9. `compositum_lattice` — for every integer combination `α = Σ a(i,j) ρ^i Q^j` other than `0`,
   `±1`, the matrix `mulMatrix a = Σ a(i,j) Cρ^i ⊗ CQ^j` is invertible and hyperbolic, so
   `d = U`, attained only by `(E^u, E^s)`; for `ρ`, `θ`, `ρQ`, `Q` (`Cρ ⊗ I₄`, `I₃ ⊗ (I₄ − CQ³)`,
   `Cρ ⊗ CQ`, `I₃ ⊗ CQ`) the values are `4, 3, 5, 9`.
10. `compositum_dilations` — on `ℝ³ ⊗ ℝ⁴` with the pairing of `GramRho ⊗ GramQ`: (a) `ρ` acts
    on `E^u` as the real scalar `r`, `r³ = r + 1`, and the spectral projection `P` onto `E^u`
    along `E^s` carries the quartic sector `e₀ ⊗ ℝ⁴` bijectively onto `E^u`, with the pairing
    equal to that of `GramQ` (multiple exactly `1`); (b) `θ` acts on `E^u` as a real scalar
    `t > 1`, `t⁴ = t³ + 1`, and `P` carries the cubic sector `ℝ³ ⊗ e₀` onto `E^u` with the
    pairing of `GramRho`; `GramQ` has type `(3, 1)` and `GramRho` type `(2, 1)` (Mathlib's
    `sigPos`, `sigNeg`).
11. `quartic_model_set` — for `CQ` on `ℤ⁴`: `(E^u, E^s)` is a scheme with `ℤ⁴ ∩ E = 0`; the
    window `|Σ_j h_j q′^j| ≤ 1/2` is a segment, its model set is
    `{π_E γ : |Σ_j γ_j q′^j| ≤ 1/2}`, and `CQ` maps it into itself; `det(CQ|_E) = −1/q′`; the
    non-real eigenvalues `w` have `|w|² = 1/(Q|q′|) > 1`; and the form of `GramQ` has type
    `(2, 1)` on `E` and `(1, 0)` on `H`. By (8), `3` is the least physical dimension of `CQ`,
    attained only by this scheme.
12. `salem_witness` — the companion matrix of `x⁴ − x³ − x² − x + 1` has that characteristic
    polynomial, is not hyperbolic and has `d = 1`; its Salem root lies in `(1.7220, 1.7221)`, and
    every admissible scheme with `dim E = 1` is on its eigenline.
13. `modelSet_isMeyer` — for every scheme and every window, `Λ(W)` is a `Delone.DeloneSet` in
    `E` and `Λ(W) − Λ(W)` is uniformly discrete.

## What is known, what is cited, what is proved here

* **Known in other formulations; no novelty claimed.** The necessity half of (1) is
  Masáková–Mazáč–Pelantová (MMP, Linear Algebra Appl. 625 (2021)), Prop. 13.2 and Cor. 13.4
  (numbering of arXiv:1909.10753v2; the journal numbering was not checked), for diagonalizable
  maps and generic schemes; Baake–Moody (2001), §1.4, remarked it for similarities. (2) is
  Kronecker's density theorem, in the cut-and-project form of Pleasants (2000), Cor. 2.12 (read
  through MMP, Prop. 3.3(iii); the primary was not opened). (4): for substitutional patterns
  (up to mutual local derivability) with expansive inflation, Harriss–Koivusalo–Walton (HKW,
  arXiv:2512.13659, preprint, v1) prove that the internal space is the contracting subspace (Thm
  3.3); (4) is its analogue for the inclusion notion, and contains, with no diagonalizability, the
  necessity of `H ⊆ E^s` from MMP Cor. 13.4. (5) is the lattice-first, model-set form of Meyer's
  theorem (Meyer 1972; 1995, Thm 6, read through Berthé–Yassawi, arXiv:2404.04116, Thm 2.2); the
  explicit Salem model set on `ℤ^s` is Solomyak (2020), §4(iv), credited there to Akiyama, and
  (12) is an instance. (6): the planar cyclotomic model sets (Huck, arXiv:math/0701141, Def. 11 and
  Rem. 18; Baake–Grimm 2013, §7.3) have physical dimension 2 and internal dimension `φ(n) − 2`;
  `φ(n)` is the least lattice rank for a planar model set with `n`-fold symmetry
  (Baake–Joseph–Schlottmann 1991), the dual quantity, and is not Hiller's bound `ψ(n)` for
  lattices with an order-`n` symmetry. (13) is classical (Meyer 1972; Moody 1997).
* **(11) is not new.** The scheme and model set of (11) are, in substance, instances of MMP
  Thm 13.1 and of HKW §3.4 (codimension-one schemes with interval windows), and the translation
  set of the Thurston dual tiling of the Pisot unit `−1/q′` is a model set of the same kind
  (Kalle–Steiner 2012, Lemma 4.3). The entry gives the instance explicitly and in the kernel.
* **Priority, bounded (literature).** The window criterion and the hyperbolic case are known:
  MMP (Prop. 13.2, Cor. 13.4, for diagonalizable maps and generic schemes) and HKW (Thm 3.3,
  expansive inflations; preprint). The dimension-one case is Meyer's (1972; 1995, Thm 6), and the
  density criterion is Kronecker's, in Pleasants's cut-and-project form (2000, Cor. 2.12). The
  minimal internal dimension for a given physical map, unit-circle spectrum included, is MMP
  Thm 13.7 (diagonalizable maps, generic schemes). For squarefree `χ_A`, hence diagonalizable `A`,
  the count (3) is a short consequence of MMP Lemma 5.1, Prop. 8.1(iii) and Cor. 13.4. We did not
  find the lattice-first least physical dimension, statement (3), stated in the sources listed
  (search completed 2026-10-20). The master's thesis of J. Mazáč, "Delone sets closed under
  affine mappings" (Czech Technical University in Prague, hdl 10467/82624), whose abstract treats
  existence for all linear maps and minimal scheme dimension for diagonalizable maps, physical
  map first, was not read: the repository record has no public full text. This is a search
  result, not a guarantee.
* **Scheme notion.** Aperiodicity (`ℤ^ι ∩ E = 0`) is not required and `H = 0` is admitted. For
  `det A ≠ 0` and squarefree `χ_A`, the line of a factor `x ± 1` and the plane of a factor `Φ₃`,
  `Φ₄` or `Φ₆` lie in `E` in every admissible scheme (3)(b), so the model set is periodic in those
  directions, and under MMP's generic (aperiodic) schemes such a factor makes a scheme impossible.
  The least dimension under aperiodicity is not treated. "Minimal" in Baake–Lenz–Moody (2007) and
  Aujogue (2016) refers to a given point set, a different question.
* **Proved here.** All thirteen statements, from Mathlib, with no Jordan form and no
  diagonalization. Used and not re-proved from Mathlib: Kronecker's theorem on algebraic integers
  with all conjugates on the unit circle (`NumberField.Embeddings.pow_eq_one_of_norm_eq_one`),
  Gelfand's spectral radius formula, Sylvester's law of inertia (D. Loeffler's
  `QuadraticForm.sigPos_of_equiv_weightedSumSquares`), the `ZSpan` floor, Selmer's
  irreducibility of `x^n − x − 1` (`X_pow_sub_X_sub_one_irreducible_rat`) and Mathlib's Delone
  sets (N. Jensen). The rational kernel lemma behind the necessity half of (3)(b), that
  `ker p(A)` contains a nonzero lattice vector for every irreducible rational factor `p` of
  `χ_A` (`InflationDimension.exists_int_mem_ker`, with no squarefree or `det` hypothesis), is
  proved here.
* **Instances at matrix level.** Statements (8)–(11) are about explicit integer matrices and
  explicit Gram matrices. That `mulMatrix a` is multiplication by `α = Σ a(i,j) ρ^i Q^j` on the
  ring of integers `ℤ[ρ] ⊗ ℤ[Q]` of `K = ℚ(ρ, Q)` in the basis `ρ^i Q^j`, and that
  `GramRho ⊗ GramQ` is the Gram matrix of the trace form of `K` in that basis (traces multiply
  across the two linearly disjoint sectors), are theorems of the author's
  stalex444/pdt-hermite-signature-compositum at commit 5aa870e8 (statements (8) and (11) there;
  submitted to the registry, registration pending), cited here and not compared. The degree-12
  field and its circle-freeness (no element other than `±1` has a conjugate on the unit circle,
  statement (17) there) are ported, with credit, into `InflationDimension/Compositum/` and used in
  the proof of (9); the eigenvalues of `mulMatrix a` are the twelve conjugates of `α`, so `U`
  counts the expanding embeddings of `α`. The general slice lemma behind the companion's factor 3
  (the restriction of the trace form of `K` to a sector over all three embeddings of `ℚ(ρ)`) is
  not compared here; (10) uses the one expanding embedding, where the multiple is exactly `1`.
* **The author's registered entries.** PALOMAR-2026-09-04-000004 (chiral Padovan histories) is
  the registered entry this one overlaps most. Its `cubic_record_windows` proves the Meyer
  property of the cubic record window by norm arguments, with no model-set definition; its
  `quartic_record_obstruction` shows that a window on the real expanding place of `ℤ[Q]`,
  observed at the complex place, gives a set that is not uniformly discrete, and its
  `quartic_escaping_coordinate` that the omitted coordinate, at `q′`, is unbounded along the
  units `Q⁻ⁿ`. Statement (4) explains both: every admissible `Q`-invariant scheme on `ℤ⁴` has
  `H ⊆ E^s`, the line of the contracting place `q′`, and (11) builds that scheme, whose model set
  is a Delone set by (13).

## Prior formalizations

As of a search completed 2026-10-20 — Mathlib master and its pull-request index; all 674 Palomar
registry entries; Lean, Coq/Rocq, Isabelle and Agda repositories on GitHub; the full Isabelle AFP
index (1,038 entries); Zenodo; OpenAlex; arXiv — we found no proof-assistant development that
defines a cut-and-project scheme in general dimension (a lattice `Γ ⊂ ℝ^N` with a splitting
`ℝ^N = E ⊕ H` and a window `W ⊂ H`) or a model set `Λ(W)`, that proves a model set to be a Meyer
set (a Delone set whose difference set is uniformly discrete), or that formalizes an inflation of
one. Narrower developments exist: a one-dimensional strip projection of `ℤ²` with period formulas
for rational slope and no finite period for irrational slope (D. Kunert,
github.com/dkunert/cut-and-project, 2026); Bohr₀ sets (PALOMAR-2026-10-18-000015); a
trivial-kernel lemma for one linear map `ℤ⁴ → ℝ³` (Zenodo 10.5281/zenodo.21796509); and the
author's PALOMAR-2026-09-04-000004 and PALOMAR-2026-08-19-000006. Mathlib has Delone sets
(`Mathlib/Analysis/AperiodicOrder/Delone`, N. Jensen), used in (13); the entry does not claim the
first Delone set in Lean. Kronecker's density theorem (2) is not claimed first in any prover; only
Mathlib was checked for it, and Mathlib at the pin has one-dimensional analogues. This is a search
result, not a guarantee.

## Application (cited, not a claim of the entry)

In the author's Pisot Dimensional Theory, `ℚ(ρ)` is the arithmetic of three-dimensional space and
`ℚ(Q)` the arithmetic of four-dimensional spacetime, and their compositum `K`, whose integers are
`ℤ[ρ] ⊗ ℤ[Q]`, is the parent of both (stalex444/pdt-hermite-signature-compositum@5aa870e8,
statements (7), (8)). A model set is the shadow of a lattice cut through a window, a standard
mathematical model of a quasicrystal (Moody 2000). Read through the theory, this entry's theorems
fix how many dimensions each of the theory's inflations needs to be the symmetry of one, and
which ones.

Space inflates the parent through spacetime, and spacetime inflates it through space. On the
parent's lattice the plastic inflation `ρ` needs exactly four physical dimensions, and only one
scheme attains four (9). Those four are a copy of spacetime's: `ρ` has a single expanding
embedding in `ℚ(ρ)`, the real one, and the spectral projection maps the quartic sector onto them,
carrying `ℤ[Q]` with its trace form unchanged, of Lorentzian type `(3, 1)` (10). `ρ` acts on them
as a pure dilation by `ρ ≈ 1.3247`, the same stretch in every direction (10). Symmetrically, the
unit `θ = −Q⁻¹ = 1 − Q³` needs exactly three, and those three are a copy of space's: `ℚ(ρ)`'s real
space with its form of type `(2, 1)` unchanged, dilated by `θ₄ = −1/q′ ≈ 1.3803` (8, 9, 10).
Taken over all three embeddings of `ℚ(ρ)` instead of the one expanding embedding, the form on the
quartic sector is tripled: the factor 3 of the companion's statement (13).

The clock needs one dimension; the ruler needs five. On `ℤ[ρ]` the plastic inflation needs
exactly one: the line, over a two-dimensional window at the complex place (8). The plastic
substitution's control-point sets are regular model sets in this scheme, with Rauzy-fractal
windows in `ℂ` (Baake and Grimm 2020), and in the theory the line is time and its points are the
ticks (PALOMAR-2026-08-19-000006, PALOMAR-2026-10-18-000019). The coupling ruler `ρQ`, which
generates the whole parent (the companion's statement (15); PALOMAR-2026-09-01-000005), needs
exactly five, over a seven-dimensional window (9): one real and two complex expanding places, a
dimension neither sector has.

The parent holds no circle, so every minimal scheme is forced. Off the parent, eigenvalues on the
unit circle change the count: a Salem inflation needs only a line (5, 12), multiplication by a
primitive `n`-th root of unity, `n ≥ 3`, needs exactly a plane, and with squarefree
characteristic polynomial every element of order `n ≥ 3` needs at least one (6). The parent has
none. No element of `K` other than `±1` has a conjugate on the unit circle (the companion's
statement (17)), so every inflation of the parent is hyperbolic, needs exactly as many dimensions
as it has expanding embeddings (a complex place counts twice), and has a unique minimal scheme
(4, 9).

## Layout and build

* `Challenge.lean` — the thirteen statements with placeholder proofs, after the entry's
  definitions (between `-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`). It imports
  Mathlib only.
* `InflationDimension/Defs.lean` — the same definitions, byte for byte; the proof modules are
  built on it.
* `InflationDimension/Admissibility.lean` (1), (2); `Normal.lean` (3)(a)(b) and the rational
  kernel lemma; `Count.lean` (3); `Hyperbolic.lean` (4); `DimOne.lean` (5), (6), (7), (12);
  `Compositum/Tower.lean`, `Compositum/CircleFree.lean` (the degree-12 field and its
  circle-freeness, ported from stalex444/pdt-hermite-signature-compositum@5aa870e8, which ported
  its `ℚ`-level inputs from PALOMAR-2026-09-02-000014); `Instances.lean` (8), (9), (10);
  `ModelSetQ.lean` (11); `Meyer.lean` (13).
* `Solution.lean` — the same statements, each proved by one application of the theorem of the
  same name in namespace `InflationDimension`.
* `comparator.json` — the thirteen compared declarations, in order, and the permitted axioms.
* `DefinitionAudit.lean` — a default build target, Mathlib only, not compared: kernel-checked
  facts about the Mathlib definitions the statements use (the matrix action and the standard
  basis, the projection along a complement, the sup norm, characteristic polynomials and
  determinants in any basis, roots with multiplicity, normalized factors, cyclotomic
  polynomials, the Kronecker product, the matrix quadratic form, Sylvester's law, Delone sets,
  segments, `IsLeast`).
* `MATHLIB_DEFINITIONS.md` — those Mathlib definitions quoted verbatim with permalinks at the
  pinned revision, byte-compared against GitHub when generated.
* `formalization.yaml` — sources, classification and disclosure; `BUILD.txt` — the build and
  axiom record (toolchain, Mathlib revision, build tail, `#print axioms` for every compared
  declaration, file hashes).

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```
lake exe cache get
lake build
```

## References

- Z. Masáková, J. Mazáč, E. Pelantová, "On generalized self-similarities of cut-and-project
  sets", Linear Algebra Appl. 625 (2021), 279–321. doi:10.1016/j.laa.2021.05.010;
  arXiv:1909.10753.
- E. Harriss, H. Koivusalo, J. J. Walton, "When is a cut and project set substitutional?",
  arXiv:2512.13659 (2025), preprint.
- "Designer quasicrystals: cut-and-project sets with pre-assigned properties" (P. A. B.
  Pleasants), in Directions in Mathematical Quasicrystals, CRM Monogr. Ser. 13, AMS (2000),
  95–141. doi:10.1090/crmm/013/04
- L. Kronecker, "Zwei Sätze über Gleichungen mit ganzzahligen Coefficienten", J. reine angew.
  Math. 53 (1857), 173–175. doi:10.1515/crll.1857.53.173
- Y. Meyer, *Algebraic Numbers and Harmonic Analysis*, North-Holland Math. Library 2 (1972).
- Y. Meyer, "Quasicrystals, Diophantine approximation and algebraic numbers", in Beyond
  Quasicrystals, Springer (1995), 3–16. doi:10.1007/978-3-662-03130-8_1
- V. Berthé, R. Yassawi, "Meyer sets, Pisot numbers, and self-similarity in symbolic dynamical
  systems", arXiv:2404.04116 (Thm 2.2 restates Meyer 1995, Thm 6).
- B. Solomyak, "Delone sets and dynamical systems", in Substitution and Tiling Dynamics, Lecture
  Notes in Math. 2273, Springer (2020), 1–32. doi:10.1007/978-3-030-57666-0_1; arXiv:1802.02370.
- C. Huck, "Uniqueness in discrete tomography of planar model sets", arXiv:math/0701141.
- M. Baake, U. Grimm, *Aperiodic Order*, Vol. 1, Cambridge Univ. Press (2013).
  doi:10.1017/CBO9781139025256
- M. Baake, D. Joseph, M. Schlottmann, "The root lattice D₄ and planar quasilattices with
  octagonal and dodecagonal symmetry", Int. J. Mod. Phys. B 5 (1991), 1927–1953.
  doi:10.1142/S0217979291000754
- M. Baake, R. V. Moody, "Self-similarities and invariant densities for model sets", in Algebraic
  Methods in Physics, Springer (2001), 1–15. doi:10.1007/978-1-4613-0119-6_1
- R. V. Moody, "Meyer sets and their duals", in The Mathematics of Long-Range Aperiodic Order,
  NATO ASI Ser. C 489, Kluwer (1997), 403–441. doi:10.1007/978-94-015-8784-6_16
- R. V. Moody, "Model sets: a survey", in From Quasicrystals to More Complex Systems, Springer
  (2000), 145–166. doi:10.1007/978-3-662-04253-3_6; arXiv:math/0002020.
- C. Kalle, W. Steiner, "Beta-expansions, natural extensions and multiple tilings associated with
  Pisot units", Trans. Amer. Math. Soc. 364 (2012), 2281–2318.
  doi:10.1090/S0002-9947-2012-05362-1
- M. Baake, D. Lenz, R. V. Moody, "Characterization of model sets by dynamical systems", Ergodic
  Theory Dynam. Systems 27 (2007), 341–382. doi:10.1017/S0143385706000800
- J.-B. Aujogue, "Optimal embedding of Meyer sets into model sets", Proc. Amer. Math. Soc. 144
  (2016), 1277–1288. doi:10.1090/proc/12790
- A. Hof, "On diffraction by aperiodic structures", Comm. Math. Phys. 169 (1995), 25–43.
  doi:10.1007/BF02101595
- "Generalized model sets and dynamical systems" (M. Schlottmann), in Directions in Mathematical
  Quasicrystals, CRM Monogr. Ser. 13, AMS (2000), 143–159. doi:10.1090/crmm/013/05
- M. Baake, U. Grimm, "Diffraction of a model set with complex windows", J. Phys.: Conf. Ser.
  1458 (2020), 012006. doi:10.1088/1742-6596/1458/1/012006; arXiv:1904.08285.

## Licence

MIT (see `LICENSE`). The verbatim Mathlib excerpts in `MATHLIB_DEFINITIONS.md` are Apache-2.0,
copyright the Mathlib authors.
