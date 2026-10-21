# The least physical dimension of an inflation-symmetric model set

Kernel-checked, in Lean 4 + Mathlib. Fix the integer lattice `ℤ^ι ⊂ ℝ^ι` and an integer matrix
`A`. An `A`-invariant cut-and-project scheme splits `ℝ^ι = E ⊕ H` into `A`-invariant subspaces
with `ℤ^ι ∩ H = 0` and `π_H(ℤ^ι)` dense in `H`; a window `W ⊆ H` gives the model set
`Λ(W) = {π_E γ : γ ∈ ℤ^ι, π_H γ ∈ W}`; and the scheme is admissible if some window gives
`A Λ(W) ⊆ Λ(W)`, inflation symmetry in Meyer's inclusion sense. The entry determines `d(A)`, the
least physical dimension `dim E` of an admissible scheme:

* for every integer `A`, admissibility is power-boundedness of `A` on `H` (1), and density is
  Kronecker's criterion (2);
* for every `A` with `det A ≠ 0`, `d(A)` is the sum over the distinct irreducible factors `p` of
  `χ_A` over `ℚ` of `m_p u_p + c_p (m_p − r₁(p))`, plus `min (deg p, 2)` when every root of `p`
  lies on the unit circle and every Jordan block at the roots of `p` has size one; here `m_p` is
  the multiplicity, `u_p`, `c_p` count the roots of `p` of modulus `> 1` and `= 1`, and `r₁(p)` is
  the number of Jordan blocks of size one at each root of `p`, computed from ranks over `ℚ`. The
  value is an invariant of rational similarity, and for squarefree `χ_A` the admissible splittings
  are characterized and `d(A) = U(A) + circleCount A`, where `U(A)` counts the eigenvalues of
  modulus `> 1` and `circleCount A` counts `1` for each factor `x ± 1` and `2` for each other
  cyclotomic factor, each counted with its multiplicity (3);
* for `det A ≠ 0` and hyperbolic `A`, any `χ_A`, an invariant splitting carries an admissible
  scheme exactly when `E ⊇ E^u`, and `d(A) = U(A)`, attained only by the unstable/stable splitting
  `(E^u, E^s)` (4);
* for `det A ≠ 0`, any `χ_A`, `d(A) = 1` exactly when `χ_A` is irreducible with one root of
  modulus `> 1` (up to sign a Pisot or Salem number) or `A = ±1` (5); for `A` of finite order,
  `d(A) = Σ_p min(deg p, 2)` over the distinct factors, a plane for each `Φ_n` with `n ≥ 3` (6); and
  Jordan blocks on the unit circle count in full while a cyclotomic factor with blocks of size one
  costs a line or a plane whatever its multiplicity (7);
* model sets are Delone sets with uniformly discrete difference sets (13).

These are then applied to multiplication by `ρ` (`ρ³ = ρ + 1`), `ρ⁻¹`, `Q` (`Q⁴ = Q + 1`),
`θ = −Q⁻¹ = 1 − Q³` and `ρQ` on `ℤ[ρ]`, `ℤ[Q]` and the degree-12 lattice `ℤ[ρ] ⊗ ℤ[Q]`
(8)–(11), with a Salem witness (12). Thirteen compared theorems; every one on the
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
3. `least_physical_dimension` — for `det A ≠ 0`, any `χ_A`: (a) `d(A) = dimensionFormula A`, the sum
   over the distinct irreducible factors `p` of `χ_A` over `ℚ` of `m_p u_p + c_p (m_p − r₁(p))`,
   plus `min (deg p, 2)` if every root of `p` lies on the unit circle and `r₁(p) = m_p`, where
   `r₁(p) = (2 dim_ℚ ker p(A) − dim_ℚ ker p(A)²) / deg p`; through the Jordan form (which the
   definitions do not use; this restatement is not formalized) this reads
   `d(A) = Σ_{|λ|>1} a_λ + Σ_{|λ|=1} (a_λ − s_λ) + #{n ≤ 2 : n ∈ 𝒮(A)} + 2·#{n ≥ 3 : n ∈ 𝒮(A)}`,
   `a_λ` the multiplicity, `s_λ` the number of Jordan blocks of size one at `λ`, `𝒮(A)` the set of
   `n` whose primitive `n`-th roots of unity are eigenvalues with all blocks of size one; (b) if
   `P A = B P` for an invertible rational `P`, then `B` has the same value; (c) an irreducible
   factor has all its roots on the unit circle if and only if it is cyclotomic; (d) for `χ_A`
   squarefree over `ℚ`, every `A`-invariant splitting is `E = ker q_E(A)`, `H = ker q_H(A)` with
   `χ_A = q_E q_H` over `ℝ`, `q_E`, `q_H` the characteristic polynomials of `A|_E`, `A|_H`; it
   carries an admissible scheme if and only if every root of `q_H` lies in the closed unit disk and
   every irreducible factor of `χ_A` over `ℚ` shares a complex root with `q_E`; and the value is
   `U(A) + circleCount A`.
4. `hyperbolic_case` — for `det A ≠ 0` and no eigenvalue on the unit circle, any `χ_A` (no
   diagonalizability): a scheme is admissible if and only if `E ⊇ E^u(A)`, if and only if
   `H ⊆ E^s(A)`; an `A`-invariant splitting `E ⊕ H` carries an admissible scheme if and only if
   `E ⊇ E^u(A)`; `(E^u, E^s)` carries an admissible scheme; `d(A) = U(A)`; and every admissible
   scheme with `dim E = U(A)` is `(E^u, E^s)`. Here `E^u` is the set of vectors with a backward
   orbit tending to `0`, `E^s` the set of vectors whose forward orbit tends to `0`.
5. `dimension_one_pisot_or_salem` — for `det A ≠ 0`, any `χ_A`: `d(A) = 1` if and only if `χ_A` is
   irreducible with exactly one root of modulus `> 1`, or `A = ±1` (on `ℤ^ι`, `ι` nonempty, of any
   rank); in the irreducible case that root `r` is real, every other root has modulus at most `1`
   (so `|r|` is a Pisot number, a Salem number, or for `#ι = 1` an integer `≥ 2`), and every
   admissible scheme with `dim E = 1` has `E` the `r`-eigenline.
6. `finite_order_case` — if `A^k = 1` for some `k ≥ 1`: every irreducible factor of `χ_A` is
   cyclotomic and `d(A) = Σ_p min(deg p, 2)` over the distinct factors, whatever the
   multiplicities; the same for `χ_A` squarefree with all roots on the unit circle; every integer
   matrix with `χ_A = Φ_n`, `n ≥ 3` (for example, multiplication by `ζ_n` on `ℤ[ζ_n]`), has
   `d = 2`.
7. `jordan_block_witnesses` — on `ℤ²`, `I₂` and `J₂ = [[1, 1], [0, 1]]` both have `χ = (x − 1)²`,
   for which the squarefree count of (3), with `x − 1` counted twice, gives `2`; but `d(I₂) = 1` and
   `d(J₂) = 2`; and `1 ⊕ J₂(1)` on `ℤ³` and `1 ⊕ J₃(1)` on `ℤ⁴` have `d = 2` and `d = 3` (the block
   of size one costs nothing: the internal line is tilted into the socle of the larger block).
8. `sector_rings` — `Cρ`, `Cρ² − 1`, `CQ`, `1 − CQ³` (multiplication by `ρ`, `ρ⁻¹`, `Q`, `θ` on
   `ℤ[ρ]`, `ℤ[Q]` in the power bases) have characteristic polynomials `x³ − x − 1`,
   `x³ + x² − 1`, `x⁴ − x − 1`, `x⁴ − x³ − 1`, are hyperbolic, and have `d = 1, 2, 3, 1`; the one
   expanding eigenvalue of `θ` is real, `t = −1/q′ ∈ (1.3802, 1.3803)`, `q′` the negative root
   of `x⁴ − x − 1`.
9. `compositum_lattice` — for every integer combination `α = Σ a(i,j) ρ^i Q^j` other than `0`,
   `±1`, the matrix `mulMatrix a = Σ a(i,j) Cρ^i ⊗ CQ^j` is nonsingular (`det ≠ 0`) and
   hyperbolic, so `d = U`, attained only by `(E^u, E^s)`; for `ρ`, `θ`, `ρQ`, `Q` (`Cρ ⊗ I₄`,
   `I₃ ⊗ (I₄ − CQ³)`, `Cρ ⊗ CQ`, `I₃ ⊗ CQ`) the values are `4, 3, 5, 9`.
10. `compositum_dilations` — on `ℝ³ ⊗ ℝ⁴` with the pairing of `GramRho ⊗ GramQ`: (a) `ρ` acts
    on `E^u` as the real scalar `r`, `r³ = r + 1`, and the spectral projection `P` onto `E^u`
    along `E^s` carries the quartic sector `e₀ ⊗ ℝ⁴` bijectively onto `E^u`, with the pairing
    equal to that of `GramQ` (multiple exactly `1`); (b) `θ` acts on `E^u` as a real scalar
    `t > 1`, `t⁴ = t³ + 1`, and `P` carries the cubic sector `ℝ³ ⊗ e₀` onto `E^u` with the
    pairing of `GramRho`; `GramQ` has type `(3, 1)` and `GramRho` type `(2, 1)` (Mathlib's
    `sigPos`, `sigNeg`).
11. `quartic_model_set` — for `CQ` on `ℤ⁴`: `(E^u, E^s)` is a scheme with `ℤ⁴ ∩ E = 0`; the window
    `|Σ_j h_j q′^j| ≤ 1/2` is a segment, its model set is `{π_E γ : |Σ_j γ_j q′^j| ≤ 1/2}`, and `CQ`
    maps it into itself; `det(CQ|_E) = −1/q′`; the non-real eigenvalues `w` have
    `|w|² = 1/(Q|q′|) > 1`; and the form of `GramQ` has type `(2, 1)` on `E` and `(1, 0)` on `H`.
    By (4) and (8), `3` is the least physical dimension of `CQ`, attained only by this scheme.
12. `salem_witness` — the companion matrix of `x⁴ − x³ − x² − x + 1` has that characteristic
    polynomial, is not hyperbolic and has `d = 1`; its Salem root lies in `(1.7220, 1.7221)`, and
    every admissible scheme with `dim E = 1` is on its eigenline.
13. `modelSet_isMeyer` — for every scheme and every window, `Λ(W)` is a `Delone.DeloneSet` in
    `E` and `Λ(W) − Λ(W)` is uniformly discrete.

## What is known, what is cited, what is proved here

* **Known in other formulations; no novelty claimed.** The necessity half of (1) is
  Masáková–Mazáč–Pelantová (MMP, Linear Algebra Appl. 625 (2021)), Prop. 13.2 and Cor. 13.4
  (numbering of arXiv:1909.10753v2; the journal numbering was not checked), for diagonalizable maps
  and generic schemes; Baake–Moody (2001), §1.4, remarked it for similarities. (2) is Kronecker's
  density theorem (Kronecker 1884, not opened), in the cut-and-project form of Pleasants (2000),
  Cor. 2.12 (read through MMP, Prop. 3.3(iii); the primary was not opened). (4): for substitutional
  patterns (up to mutual local derivability) with expansive inflation, Harriss–Koivusalo–Walton
  (HKW, arXiv:2512.13659, preprint, v1) prove that the internal space is the contracting subspace
  (Thm 3.3); (4) is its analogue for the inclusion notion, and contains, with no diagonalizability,
  the necessity of `H ⊆ E^s` from MMP Cor. 13.4. (5), for irreducible `χ_A`, is the lattice-first,
  model-set form of Meyer's theorem (Meyer 1972; 1995, Thm 6, read through Berthé–Yassawi,
  arXiv:2404.04116, Thm 2.2; the Meyer-set inflation case also Lagarias 1999, Thm 4.1, as stated in
  Solomyak 2020, Thm 3(iii)); the explicit Salem model set on `ℤ^s` is Solomyak (2020), §4(iv),
  credited there to Akiyama, and (12) is an instance. (6): the planar cyclotomic model sets (Huck,
  arXiv:math/0701141, Def. 11 and Rem. 18; Baake–Grimm 2013, §7.3) have physical dimension 2 and
  internal dimension `φ(n) − 2`; `φ(n)` is the least lattice rank for a planar model set with
  `n`-fold symmetry (Baake–Joseph–Schlottmann 1991), the dual quantity, and is not Hiller's bound
  `ψ(n)` for lattices with an order-`n` symmetry (Hiller 1985, as cited by MMP §1; not opened). (13)
  is classical (Meyer 1972; Moody 1997).
* **(11) is not new.** The scheme and model set of (11) are, in substance, instances of MMP
  Thm 13.1 and of HKW §3.4 (codimension-one schemes with interval windows), and the translation
  set of the Thurston dual tiling of the Pisot unit `−1/q′` is a model set of the same kind
  (Kalle–Steiner 2012, Lemma 4.3). The entry gives the instance explicitly and in the kernel.
* **Beyond the cited cases.** The entry proves the least physical dimension for every nonsingular
  integer matrix (3), including what lies outside MMP's diagonalizable class: a Jordan block of size
  `≥ 2` at an eigenvalue on the unit circle counts in full (the terms `c_p (m_p − r₁(p))`, which
  vanish for diagonalizable `A`), and at a cyclotomic factor with such a block the blocks of size
  one cost nothing, the internal space being tilted into the socle of the larger blocks; the
  witnesses are `J₂`, `1 ⊕ J₂(1)` and `1 ⊕ J₃(1)` (7). The Jordan-block terms are not confined to
  periodic schemes: for the companion matrix of the square of the Salem polynomial of (12), (3)
  gives `d = 6`, against `d = 2` for two copies of the companion matrix of (12) (the same `χ_A`),
  and in both cases the minimal scheme meets the lattice only in `0` (the values are (3) evaluated
  by hand; this last fact is not formalized). The master's thesis of J. Mazáč, "Delone sets closed
  under affine mappings" (Czech Technical University in Prague, 2019, hdl 10467/82624), whose
  abstract treats, physical map first, the existence of a scheme with a given self-similarity for
  all linear maps and the minimal lattice dimension for diagonalizable maps, was not read: the
  repository record has no public full text. Its treatment of non-diagonalizable maps, existence
  only by its abstract, was not checked against the Jordan-block terms of (3); the later paper of
  MMP states (§14) that its answer covers nonsingular maps diagonalizable over ℂ only. The entry
  also proves the characterization of every admissible splitting for squarefree `χ_A` ((3)(d)),
  non-generic splittings included (its necessity half is the argument of MMP, Lemma 5.1, which uses
  only the injectivity `ℤ^ι ∩ H = 0` and so needs no genericity), and (1) for every integer matrix
  and (4) for every nonsingular hyperbolic integer matrix, with no diagonalizability hypothesis; for
  diagonalizable `A` and generic schemes, the uniqueness of the minimal scheme in (4) and of the
  minimal physical line in (5) is immediate from MMP Cor. 13.4. For `det A ≠ 0` and squarefree `χ_A`
  with a factor `Φ_n`, `n ∉ {1, 2, 3, 4, 6}`, the minimal scheme is not unique, by (3)(d).
* **Priority, bounded (literature).** The necessity halves of the window criterion (1) and of the
  hyperbolic case (4) are MMP Prop. 13.2 and Cor. 13.4 (diagonalizable maps, generic schemes); the
  expansive substitutional analogue of (4) is HKW Thm 3.3 (preprint). The dimension-one case, for
  irreducible `χ_A`, is Meyer's (1972; 1995, Thm 6; for Meyer sets also Lagarias 1999, Thm 4.1), and
  the density criterion is Kronecker's, in Pleasants's cut-and-project form (2000, Cor. 2.12). The
  minimal internal dimension for a given physical map, unit-circle spectrum included, is MMP
  Thm 13.7 (diagonalizable maps, generic schemes). For squarefree `χ_A`, hence diagonalizable `A`,
  the count of (3) also follows from the arguments of MMP, Lemma 5.1, Prop. 8.1(iii) and Cor. 13.4,
  which are stated there for generic (aperiodic) schemes, under which a factor `x ± 1`, `Φ₃`, `Φ₄`
  or `Φ₆` admits no scheme. We did not find the lattice-first least physical dimension,
  statement (3), stated in the sources listed (search completed 2026-10-20). This is a search
  result, not a guarantee.
* **Scheme notion.** Aperiodicity (`ℤ^ι ∩ E = 0`) is not required, `H = 0` is admitted, and `A` need
  not be unimodular: the counts assume `det A ≠ 0` only. The internal space is a real subspace of
  `ℝ^ι`; for `|det A| ≥ 2`, inflation-symmetric model sets with `p`-adic internal spaces
  (Baake–Moody–Schlottmann 1998; Lee–Moody 2001) are outside this notion. For `det A ≠ 0` and
  squarefree `χ_A`, the line of a factor `x ± 1` and the plane of a factor `Φ₃`, `Φ₄` or `Φ₆` lie in
  `E` in every admissible scheme ((3)(d)), so the model set is periodic in those directions, and
  under MMP's generic (aperiodic) schemes such a factor makes a scheme impossible. Likewise, at a
  cyclotomic factor `p` with a Jordan block of size `≥ 2`, `p(A)` kills the `p`-component of `H`
  (power-boundedness), so the nonzero rational subspace `im p(A)` of that component lies in `E`: at
  a root of unity, the Jordan-block terms and the tilt occur only in schemes with `ℤ^ι ∩ E ≠ 0`. The
  least dimension under aperiodicity is not treated. "Minimal" in Baake–Lenz–Moody (2007) and
  Aujogue (2016) refers to a given point set, a different question.
* **Proved here.** All thirteen statements, from Mathlib, with no Jordan form of `A` and no
  diagonalization of `A`. In (3) the lower bound comes from the largest power-bounded invariant
  summand, of dimension `Σ_p (m_p s_p + c_p r₁(p))` with `s_p` the number of roots of `p` inside the
  unit disk (a power-bounded map is semisimple on its unit-circle part), and from the fact that at a
  cyclotomic factor with all Jordan blocks of size one the physical space meets the generalized
  eigenspace in at least `min (deg p, 2)` dimensions; the upper bound replaces, in a largest
  power-bounded summand, the component of each cyclotomic factor by a scheme of the integer matrix
  by which `A` acts on a `ℤ`-basis of the lattice points of that component, a generic line or plane
  at one place of `ℚ(ζ_n)` when all blocks have size one and otherwise an internal space tilted into
  the socle of the larger blocks (generic parameters avoid countably many proper affine subspaces,
  by Haar measure). Used and not re-proved from Mathlib: Kronecker's theorem on algebraic integers
  with all conjugates on the unit circle (`NumberField.Embeddings.pow_eq_one_of_norm_eq_one`),
  Gelfand's spectral radius formula, Sylvester's law of inertia (D. Loeffler's
  `QuadraticForm.sigPos_of_equiv_weightedSumSquares`), the `ZSpan` floor, Selmer's irreducibility of
  `x^n − x − 1` (`X_pow_sub_X_sub_one_irreducible_rat`) and Mathlib's Delone sets (N. Jensen). The
  rational kernel lemma behind the necessity half of (3)(d), that `ker p(A)` contains a nonzero
  lattice vector for every irreducible rational factor `p` of `χ_A`
  (`InflationDimension.exists_int_mem_ker`, with no squarefree or `det` hypothesis), is proved here.
* **Instances at matrix level.** Statements (8)–(11) are about explicit integer matrices and
  explicit Gram matrices. That `Cρ` and `CQ` are multiplication by `ρ` and `Q` in the power bases is
  their definition (companion matrices), so `Cρ^i ⊗ CQ^j` is multiplication by `ρ^i Q^j` in the
  product basis and `mulMatrix a` is multiplication by `α = Σ a(i,j) ρ^i Q^j`. That the `ρ^i Q^j`
  are a `ℤ`-basis of the ring of integers of `K = ℚ(ρ, Q)` is statement (8) of the author's
  registered entry PALOMAR-2026-10-21-000012
  (stalex444/pdt-hermite-signature-compositum@5aa870e98236ba240561b798265c629df8c2d031); that
  `GramRho`, `GramQ` and `GramRho ⊗ GramQ` are the Gram matrices of the trace forms in these bases
  is statements (8), (9) and (19) of the author's registered entry PALOMAR-2026-09-02-000014, in
  which `ℚ(ρ) ⊗ ℚ(Q)` is the field `ℚ(ρ, Q)` (its (23)). These are cited, not compared. The
  degree-12 field and its circle-freeness (no element other than `±1` has a conjugate on the unit
  circle, statement (17) of PALOMAR-2026-10-21-000012) are ported, with credit, into
  `InflationDimension/Compositum/` (namespace `InflationDimension.Compositum`, so no declaration
  name of that entry is declared again) and used in the proof of (9); the eigenvalues of
  `mulMatrix a` are the twelve conjugates of `α`, so `U` counts the expanding embeddings of `α`. The
  general slice lemma behind the factor 3 of PALOMAR-2026-10-21-000012, statement (13) (the
  restriction of the trace form of `K` to a sector over all three embeddings of `ℚ(ρ)`) is not
  compared here; (10) uses the one expanding embedding, where the multiple is exactly `1`.
* **The author's registered entries.** PALOMAR-2026-09-04-000004 (chiral Padovan histories) is
  the registered entry this one overlaps most. Its `cubic_record_windows` proves the Meyer
  property of the cubic record window by norm arguments, with no model-set definition; its
  `quartic_record_obstruction` shows that a window on the real expanding place of `ℤ[Q]`,
  observed at the complex place, gives a set that is not uniformly discrete, and its
  `quartic_escaping_coordinate` that the omitted coordinate, at `q′`, is unbounded along the
  units `Q⁻ⁿ`. Keeping the dropped coordinate at `q′` gives the model set of the `Q`-invariant
  scheme whose window line is the expanding real place; it is a Delone set by (13), but it is not
  `Q`-admissible by (4), since every admissible `Q`-invariant scheme on `ℤ⁴` has `H ⊆ E^s`, the
  line of `q′`. Dropping that coordinate, which is unbounded along `Q⁻ⁿ`
  (`quartic_escaping_coordinate`), is what destroys uniform discreteness. (11) is the admissible
  scheme.

## Prior formalizations

As of a search completed 2026-10-20 — Mathlib master and its pull-request index; all 674 Palomar
registry entries; Lean, Coq/Rocq, Isabelle and Agda repositories on GitHub; the full Isabelle AFP
index (1,038 entries); Zenodo; OpenAlex; arXiv — we found no proof-assistant development that
defines a cut-and-project scheme in general dimension (a lattice `Γ ⊂ ℝ^N` with a splitting
`ℝ^N = E ⊕ H` and a window `W ⊂ H`) or a model set `Λ(W)`, that proves model sets in general (every
scheme and window) to be Meyer sets (Delone sets whose difference sets are uniformly discrete), or
that formalizes an inflation of one. Narrower developments exist: a one-dimensional strip projection
of `ℤ²` with period formulas for rational slope and no finite period for irrational slope
(D. Kunert, github.com/dkunert/cut-and-project, 2026); Bohr₀ sets (PALOMAR-2026-10-18-000015); a
trivial-kernel lemma for one linear map `ℤ⁴ → ℝ³` (J. Reed, Zenodo 10.5281/zenodo.21796509); and the
author's PALOMAR-2026-09-04-000004 (the Meyer property of one cubic window set,
`cubic_record_windows`) and PALOMAR-2026-08-19-000006 (its uncompared module `Settling.lean` at the
registered commit c48eb128: `meyer_separation`, `windowed_separation`). Mathlib has Delone sets
(`Mathlib/Analysis/AperiodicOrder/Delone`, N. Jensen), used in (13); the entry does not claim the
first Delone set in Lean. Kronecker's density theorem (2) is not claimed first in any prover; only
Mathlib was checked for it, and Mathlib at the pin has one-dimensional analogues. This is a search
result, not a guarantee.

## Application (cited, not a claim of the entry)

In the author's Pisot Dimensional Theory, `ℚ(ρ)` is the arithmetic of three-dimensional space and
`ℚ(Q)` the arithmetic of four-dimensional spacetime, and their compositum `K`, whose integers are
`ℤ[ρ] ⊗ ℤ[Q]`, is the parent of both (the author's registered entry PALOMAR-2026-10-21-000012
(stalex444/pdt-hermite-signature-compositum@5aa870e98236ba240561b798265c629df8c2d031), statements
(7), (8)). A model set is the shadow of a lattice cut through a window, a standard mathematical
model of a quasicrystal (Moody 2000). Read through the theory, this entry's theorems fix how many
dimensions each of the theory's inflations needs to be the symmetry of one, and which ones.

Space inflates the parent through spacetime, and spacetime inflates it through space. On the
parent's lattice the plastic inflation `ρ` needs exactly four physical dimensions, and only one
scheme attains four (4, 9). Those four are a copy of spacetime's: `ρ` has a single expanding
embedding in `ℚ(ρ)`, the real one, and the spectral projection maps the quartic sector onto them,
carrying `ℤ[Q]` with its trace form unchanged, of Lorentzian type `(3, 1)` (10). `ρ` acts on them as
a pure dilation by `ρ ≈ 1.3247`, the same stretch in every direction (10). Symmetrically, the unit
`θ = −Q⁻¹ = 1 − Q³` needs exactly three, and those three are a copy of space's: `ℚ(ρ)`'s real space
with its form of type `(2, 1)` unchanged, dilated by `t = −1/q′ ≈ 1.3803` (8, 9, 10). Taken over all
three embeddings of `ℚ(ρ)` instead of the one expanding embedding, the form on the quartic sector is
tripled: the factor 3 of statement (13) of PALOMAR-2026-10-21-000012.

The clock needs one dimension; the ruler needs five. On `ℤ[ρ]` the plastic inflation needs exactly
one: the line, over a two-dimensional window at the complex place (8). The plastic substitution's
control-point sets are regular model sets in this scheme, with Rauzy-fractal windows in `ℂ` (Baake
and Grimm 2020), and in the theory the line is time and its points are the ticks
(PALOMAR-2026-08-19-000006, PALOMAR-2026-10-18-000019). The coupling ruler `ρQ`, which generates the
parent field (`ℚ(ρQ) = K`; statement (15) of PALOMAR-2026-10-21-000012, where `ℤ[ρQ]` has index 53
in the integers; PALOMAR-2026-09-01-000005), needs exactly five, over a seven-dimensional
window (9): one real and two complex expanding places, a dimension neither sector has.

The parent holds no circle, so every minimal scheme is forced. Off the parent, eigenvalues on the
unit circle can change the count: a Salem inflation's circle eigendirections lie in the internal
space and cost nothing, so it still needs only a line (5, 12), but multiplication by a primitive
`n`-th root of unity, `n ≥ 3`, needs exactly a plane, and every element of finite order `n ≥ 3`
needs at least one (6). The parent has none. No element of `K` other than `±1` has a conjugate on
the unit circle (statement (17) of PALOMAR-2026-10-21-000012), so every inflation of the parent by
an element other than `0` and `±1` is hyperbolic, needs exactly as many dimensions as it has
expanding embeddings (a complex place counts twice), and has a unique minimal scheme (4, 9).

## Layout and build

* `Challenge.lean` — the thirteen statements with placeholder proofs, after the entry's
  definitions (between `-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`). It imports
  Mathlib only.
* `InflationDimension/Defs.lean` — the same definitions, byte for byte; the proof modules are
  built on it.
* `InflationDimension/Admissibility.lean` (1), (2); `Normal.lean` (the squarefree normal form and
  characterization in (3)) and the rational kernel lemma; `Count.lean` (the squarefree count in
  (3)); `Hyperbolic.lean` (4); `DimOne.lean` (the squarefree forms of (5), (6), the `ℤ²` examples of
  (7), and (12)); `JordanData.lean` (Jordan data from rational ranks; the largest power-bounded
  invariant summand); `Tilt.lean` (a single cyclotomic factor: the semisimple collapse and the tilt;
  the examples `1 ⊕ J₂(1)`, `1 ⊕ J₃(1)` of (7)); `FormulaA.lean` ((3) for every nonsingular `A`, and
  (5), (6), (7)); `Compositum/Tower.lean`, `Compositum/CircleFree.lean` (the degree-12 field and its
  circle-freeness, ported from the author's registered entry PALOMAR-2026-10-21-000012
  (stalex444/pdt-hermite-signature-compositum@5aa870e98236ba240561b798265c629df8c2d031), which
  ported its `ℚ`-level inputs from PALOMAR-2026-09-02-000014); `Instances.lean` (8), (9), (10);
  `ModelSetQ.lean` (11); `Meyer.lean` (13).
* `Solution.lean` — the same statements, each proved by one application of the theorem of the
  same name in namespace `InflationDimension`.
* `comparator.json` — the thirteen compared declarations, in order, and the permitted axioms.
* `DefinitionAudit.lean` — a default build target, Mathlib only, not compared: kernel-checked
  facts about the Mathlib definitions the statements use (the matrix action and the standard
  basis, the projection along a complement, the sup norm, characteristic polynomials and
  determinants in any basis, roots with multiplicity, normalized factors, cyclotomic
  polynomials, multiplicities in a multiset, the Kronecker product, the matrix quadratic form,
  Sylvester's law, Delone sets, segments, `IsLeast`).
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
  Math. 53 (1857), 173–175. doi:10.1515/crll.1857.53.173 (the root-of-unity theorem, (3))
- L. Kronecker, "Näherungsweise ganzzahlige Auflösung linearer Gleichungen", Sitzungsber. Königl.
  Preuss. Akad. Wiss. Berlin (1884), 1179–1193, continued 1271–1300; JFM 16.0083.02,
  17.0073.01 (the density theorem, (2))
- Y. Meyer, *Algebraic Numbers and Harmonic Analysis*, North-Holland Math. Library 2 (1972).
- Y. Meyer, "Quasicrystals, Diophantine approximation and algebraic numbers", in Beyond
  Quasicrystals, Springer (1995), 3–16. doi:10.1007/978-3-662-03130-8_1
- V. Berthé, R. Yassawi, "Meyer sets, Pisot numbers, and self-similarity in symbolic dynamical
  systems", arXiv:2404.04116 (Thm 2.2 restates Meyer 1995, Thm 6).
- B. Solomyak, "Delone sets and dynamical systems", in Substitution and Tiling Dynamics, Lecture
  Notes in Math. 2273, Springer (2020), 1–32. doi:10.1007/978-3-030-57666-0_1; arXiv:1802.02370.
- J. C. Lagarias, "Geometric models for quasicrystals I. Delone sets of finite type", Discrete
  Comput. Geom. 21 (1999), 161–191. doi:10.1007/PL00009413 (Thm 4.1 as stated in Solomyak 2020,
  Thm 3(iii); not opened)
- C. Huck, "Uniqueness in discrete tomography of planar model sets", arXiv:math/0701141.
- M. Baake, U. Grimm, *Aperiodic Order*, Vol. 1, Cambridge Univ. Press (2013).
  doi:10.1017/CBO9781139025256
- M. Baake, D. Joseph, M. Schlottmann, "The root lattice D₄ and planar quasilattices with
  octagonal and dodecagonal symmetry", Int. J. Mod. Phys. B 5 (1991), 1927–1953.
  doi:10.1142/S0217979291000754
- H. Hiller, "The crystallographic restriction in higher dimensions", Acta Cryst. A 41 (1985),
  541–544. doi:10.1107/S0108767385001180 (as cited by MMP §1; not opened)
- M. Baake, R. V. Moody, "Self-similarities and invariant densities for model sets", in Algebraic
  Methods in Physics, Springer (2001), 1–15. doi:10.1007/978-1-4613-0119-6_1
- M. Baake, R. V. Moody, M. Schlottmann, "Limit-(quasi)periodic point sets as quasicrystals with
  p-adic internal spaces", J. Phys. A: Math. Gen. 31 (1998), 5755–5765.
  doi:10.1088/0305-4470/31/27/006; arXiv:math-ph/9901008.
- J.-Y. Lee, R. V. Moody, "Lattice substitution systems and model sets", Discrete Comput. Geom.
  25 (2001), 173–201. doi:10.1007/s004540010083; arXiv:math/0002019.
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
- D. A. Lind, "The entropies of topological Markov shifts and a related class of algebraic
  integers", Ergodic Theory Dynam. Systems 4 (1984), 283–300. doi:10.1017/S0143385700002443
- R. Kenyon, B. Solomyak, "On the characterization of expansion maps for self-affine tilings",
  Discrete Comput. Geom. 43 (2010), 577–593. doi:10.1007/s00454-009-9199-6
- M. Baake, U. Grimm, "Diffraction of a model set with complex windows", J. Phys.: Conf. Ser.
  1458 (2020), 012006. doi:10.1088/1742-6596/1458/1/012006; arXiv:1904.08285.

## Licence

MIT (see `LICENSE`). The verbatim Mathlib excerpts in `MATHLIB_DEFINITIONS.md` are Apache-2.0,
copyright the Mathlib authors.
