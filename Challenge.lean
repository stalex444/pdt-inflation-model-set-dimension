module
public import Mathlib

@[expose] public section
/-!
# The least physical dimension of an inflation-symmetric model set

Thirteen compared statements, (1)–(13) below. The main theorem is (3): for every integer matrix `A`
with `det A ≠ 0`, `d(A)` is the sum over the distinct irreducible factors `p` of `χ_A` over `ℚ` of
`m_p u_p + c_p (m_p − r₁(p))`, plus `min (deg p, 2)` when every root of `p` lies on the unit circle
and every Jordan block at the roots of `p` has size one (`dimensionFormula A`); the value is an
invariant of rational similarity, and for squarefree `χ_A` every admissible splitting is
characterized and `d(A) = U(A) + #{x ± 1 ∣ χ_A} + 2·#{Φ_n ∣ χ_A, n ≥ 3}`. (4) is the hyperbolic
case, `det A ≠ 0` and any `χ_A`: `d(A) = U(A)`, attained only by `(E^u, E^s)`. (1), (2) and (13) are
the general tools, (5)–(7) corollaries and witnesses of (3), and (8)–(12) the instances:
multiplication by `ρ`, `ρ⁻¹`, `Q`, `θ = −Q⁻¹` and `ρQ` on `ℤ[ρ]`, `ℤ[Q]` and `ℤ[ρ] ⊗ ℤ[Q]`, where
`ρ³ = ρ + 1` and `Q⁴ = Q + 1`, and a Salem witness.

**Setting.** `ι` is a finite type, `ℤ^ι ⊂ ℝ^ι` is the integer lattice (`intLattice`) and an
integer matrix `A` acts on `ℝ^ι` (`act A`). An `A`-invariant cut-and-project scheme
(`InvariantCPS A`) is a splitting `ℝ^ι = E ⊕ H` into `A`-invariant subspaces with
`ℤ^ι ∩ H = 0` and `π_H(ℤ^ι)` dense in `H`, where `π_E`, `π_H` are the projections along the
splitting. A window is a bounded subset of `H` containing a relative ball of `H`, and the model set
of `W` is `Λ(W) = {π_E γ : γ ∈ ℤ^ι, π_H γ ∈ W}`. The scheme is admissible if some window gives
`A Λ(W) ⊆ Λ(W)`. The least physical dimension `d(A)` is the least `dim E` over admissible schemes
(`IsLeast (physDims A) d`); the scheme `(ℝ^ι, 0)` is admissible, so `d(A) ≤ #ι`. `U(A)`
(`unstableCount`) is the number of complex eigenvalues of `A` of modulus `> 1`, with
multiplicity; `E^u(A)` (`unstableSet`) is the set of vectors with a backward orbit tending to `0`
and `E^s(A)` (`stableSet`) the set of vectors whose forward orbit tends to `0`; `A` is hyperbolic
if no eigenvalue has modulus `1`; and `circleCount A` counts `1` for each irreducible factor
`x ± 1` of `χ_A` over `ℚ` and `2` for each other irreducible factor whose roots all lie on the
unit circle, each factor counted with its multiplicity in `χ_A` (Mathlib's `normalizedFactors`).
For an irreducible factor `p` of `χ_A` over `ℚ`, `m_p` (`factorMult`) is its
multiplicity, `u_p` and `c_p` (`expandingRootCount`, `circleRootCount`) are the numbers of its
complex roots of modulus `> 1` and `= 1`, and
`r₁(p) = (2 dim_ℚ ker p(A) − dim_ℚ ker p(A)²) / deg p` (`sizeOneBlocks`), which is the number of
Jordan blocks of size one at each root of `p`; no Jordan form enters the definitions.

**Scope.**
* The minimum is over `A`-invariant schemes on the fixed lattice `ℤ^ι`: the lattice and the map are
  given and the splitting is chosen. "Minimal" in Baake–Lenz–Moody (2007) and Aujogue (2016) refers
  to a given point set, a different question. The physical-map-first dual, the least lattice rank
  for a given physical map with eigenvalues on the unit circle allowed, is Masáková–Mazáč–Pelantová
  (2021), Thm 13.7 (diagonalizable maps, generic schemes); it is cited, not re-proved.
* Inflation symmetry is the inclusion `A Λ ⊆ Λ`, in Meyer's sense, linear and centred at the origin.
  It is not the substitutional notion (up to mutual local derivability) of Harriss–Koivusalo–Walton.
* Aperiodicity (`ℤ^ι ∩ E = 0`) is not required, `H = 0` is admitted, and `A` need not be unimodular:
  the counts assume `det A ≠ 0` only. The internal space is a real subspace of `ℝ^ι`; for
  `|det A| ≥ 2`, inflation-symmetric model sets with `p`-adic internal spaces
  (Baake–Moody–Schlottmann 1998; Lee–Moody 2001) are outside this notion. When `det A ≠ 0` and `χ_A`
  is squarefree, the line of a factor `x ± 1` and the plane of a factor `Φ₃`, `Φ₄` or `Φ₆` lie in
  `E` in every admissible scheme (by (3)(d)), so such a factor excludes an aperiodic scheme; the
  generic schemes of Masáková–Mazáč–Pelantová are aperiodic. Likewise, at a cyclotomic factor `p`
  with a Jordan block of size `≥ 2`, `p(A)` kills the `p`-component of `H` (power-boundedness), so
  the nonzero rational subspace `im p(A)` of that component lies in `E`: at a root of unity, the
  Jordan-block terms and the tilt occur only in schemes with `ℤ^ι ∩ E ≠ 0`. The least dimension
  under aperiodicity is a different problem and is not treated.
* The value is an invariant of the `ℚ`-module `(ℚ^ι, A)` (3), not of an eigenvalue: multiplication
  by `ρ` needs one physical dimension on `ℤ[ρ]` (8) and four on `ℤ[ρ] ⊗ ℤ[Q]` (9).
* The statements are about inflation-symmetric model sets, not tilings. The substitution
  `a ↦ b, b ↦ c, c ↦ d, d ↦ ab` is primitive and its substitution matrix is the companion matrix of
  `x⁴ − x − 1`, so its self-similar tiling of the line has expansion `Q`; a model set inflated by
  `Q` on `ℤ[Q]` needs three physical dimensions (8). Likewise `ρQ ≈ 1.6171` is a Perron number, so
  it is the expansion of a self-similar tiling of the line (Lind 1984; Kenyon–Solomyak 2010), but a
  model set inflated by `ρQ` on `ℤ[ρ] ⊗ ℤ[Q]` needs five physical dimensions (9).

**The compared statements** (namespace `ModelSetDimension`).
1. `admissibility_criterion` — for every integer `A`, a scheme is admissible if and only if `A` is
   power-bounded on `H`; then the orbit window `W_* = {h ∈ H : ‖Aⁿ h‖ ≤ 1 for all n}` is a compact,
   convex, centrally symmetric window with `A W_* ⊆ W_*`. Per window, `A Λ(W) ⊆ Λ(W)` if and only if
   `A` maps the lattice points `W ∩ π_H(ℤ^ι)` into `W` (for a closed window contained in the closure
   of its lattice points, if and only if `A W ⊆ W`). Admissibility puts the eigenvalues of `A|_H` in
   the closed unit disk, so `U(A) ≤ dim E`.
2. `kronecker_density_criterion` — `π_H(ℤ^ι)` is dense in `H` if and only if every real linear
   functional that is integer-valued on `ℤ^ι` and vanishes on `E` is zero.
3. `least_physical_dimension` — for `det A ≠ 0`: (a) `d(A) = dimensionFormula A`; (b) if `P A = B P`
   for an invertible rational matrix `P`, then `B` has the same value; (c) the irreducible factors
   of `χ_A` with all roots on the unit circle are exactly the cyclotomic ones; and (d) for `χ_A`
   squarefree over `ℚ`, every invariant splitting is `E = ker q_E(A)`, `H = ker q_H(A)` with
   `χ_A = q_E q_H`, it carries an admissible scheme if and only if the roots of `q_H` lie in the
   closed unit disk and every irreducible factor of `χ_A` over `ℚ` shares a complex root with `q_E`,
   and `dimensionFormula A = U(A) + circleCount A`.
4. `hyperbolic_case` — for `det A ≠ 0` and `A` hyperbolic, any `χ_A`: a scheme is admissible if and
   only if `E ⊇ E^u`, if and only if `H ⊆ E^s`; an `A`-invariant splitting carries an admissible
   scheme if and only if `E ⊇ E^u`; `(E^u, E^s)` carries an admissible scheme; `d(A) = U(A)`; and
   every admissible scheme with `dim E = U(A)` is `(E^u, E^s)`.
5. `dimension_one_pisot_or_salem` — for `det A ≠ 0`, any `χ_A`: `d(A) = 1` if and only if `χ_A` is
   irreducible with exactly one root of modulus `> 1`, or `A = ±1` (`ι` nonempty); that root `r` is
   real, every other root has modulus at most `1`, and every admissible scheme with `dim E = 1` has
   `E` the `r`-eigenline.
6. `finite_order_case` — if `A^k = 1` for some `k ≥ 1`, the irreducible factors of `χ_A` are
   cyclotomic and `d(A) = Σ_p min(deg p, 2)` over the distinct factors; if `χ_A` is squarefree with
   all roots on the unit circle, the same count holds; every integer matrix with `χ_A = Φ_n`,
   `n ≥ 3`, has `d = 2`.
7. `jordan_block_witnesses` — `I₂` and `[[1, 1], [0, 1]]` both have `χ = (x − 1)²`, for which the
   squarefree count of (3), with `x − 1` counted twice, is `2`; but `d(I₂) = 1`, and `d = 2` for the
   Jordan block; and `1 ⊕ J₂(1)` and `1 ⊕ J₃(1)` have `d = 2` and `d = 3`.
8. `sector_rings` — `Cρ`, `Cρ² − 1`, `CQ` and `1 − CQ³`, multiplication by `ρ`, `ρ⁻¹`, `Q` and
   `θ = −Q⁻¹` on `ℤ[ρ]` and `ℤ[Q]`, have characteristic polynomials `x³ − x − 1`, `x³ + x² − 1`,
   `x⁴ − x − 1`, `x⁴ − x³ − 1`, are hyperbolic and have `d = 1, 2, 3, 1`; the one expanding
   eigenvalue of `θ` is real and lies in `(1.3802, 1.3803)`.
9. `compositum_lattice` — for every `a ≠ 0, ±e₀₀`, `mulMatrix a` (multiplication by
   `Σ a(i,j) ρ^i Q^j` on `ℤ³ ⊗ ℤ⁴`) is nonsingular (`det ≠ 0`) and hyperbolic, with `d = U`; for
   `ρ`, `θ`, `ρQ` and `Q` the values are `4`, `3`, `5`, `9`.
10. `compositum_dilations` — `ρ` (`mulρ`) acts on `E^u` as a real scalar `r`, `r³ = r + 1`, and the
    projection onto `E^u` along `E^s` maps the sector `e₀ ⊗ ℝ⁴` bijectively onto `E^u`, carrying the
    pairing of `GramRho ⊗ GramQ` to that of `GramQ` exactly; the same holds for `θ` (`mulθ`) with a
    scalar `t > 1`, `t⁴ = t³ + 1`, the sector `ℝ³ ⊗ e₀` and `GramRho`; and `GramQ`, `GramRho` have
    types `(3, 1)`, `(2, 1)`.
11. `quartic_model_set` — for `CQ`, `(E^u, E^s)` is a scheme with `ℤ⁴ ∩ E = 0`; with `q′` the
    negative root of `x⁴ − x − 1`, the window `|Σ_j h_j q′^j| ≤ 1/2` is a segment, its model set is
    `{π_E γ : |Σ_j γ_j q′^j| ≤ 1/2}`, and `Q` maps it into itself; `det(Q|_E) = −1/q′`; the non-real
    eigenvalues have modulus squared `1/(Q|q′|) > 1`; and the form of `GramQ` has type `(2, 1)` on
    `E` and `(1, 0)` on `H`.
12. `salem_witness` — the companion matrix of `x⁴ − x³ − x² − x + 1` is not hyperbolic and has
    `d = 1`, attained only on the eigenline of its Salem root, which lies in `(1.7220, 1.7221)`.
13. `modelSet_isMeyer` — for every scheme and every window, `Λ(W)` is a Delone set in `E` (Mathlib's
    `Delone.DeloneSet`) and `Λ(W) − Λ(W)` is uniformly discrete.

**Attributions.** Each statement's docstring names its sources, and the README gives them statement
by statement. The mathematics of (1), (2), (4), (5) for irreducible `χ_A`, and (13), and of (6) for
`χ_A = Φ_n` (the planar cyclotomic model sets), is known in other formulations, and the scheme and
model set of (11) are, in substance, an instance of Masáková–Mazáč–Pelantová (Linear Algebra Appl.
625 (2021) 279–321), Thm 13.1; none of this is claimed as new. Beyond the cited cases, the entry
proves the least physical dimension for every nonsingular integer matrix (3), including what lies
outside the diagonalizable class of Masáková–Mazáč–Pelantová: a Jordan block of size `≥ 2` at an
eigenvalue on the unit circle counts in full (the terms `c_p (m_p − r₁(p))`, which vanish for
diagonalizable `A`), and at a cyclotomic factor with such a block the blocks of size one cost
nothing, the internal space being tilted into the socle of the larger blocks; the witnesses are
`J₂`, `1 ⊕ J₂(1)` and `1 ⊕ J₃(1)` (7). The Jordan-block terms are not confined to periodic schemes:
for the companion matrix of the square of the Salem polynomial of (12), (3) gives `d = 6`, against
`d = 2` for two copies of the companion matrix of (12) (the same `χ_A`), and in both cases the
minimal scheme meets the lattice only in `0` (the values are (3) evaluated by hand; this last fact
is not formalized). The master's thesis of J. Mazáč (Czech Technical University in Prague, 2019, hdl
10467/82624), whose abstract treats, physical map first, the existence of a scheme with a given
self-similarity for all linear maps and the minimal lattice dimension for diagonalizable maps, was
not read: its full text is not public. Its treatment of non-diagonalizable maps, existence only by
its abstract, was not checked against the Jordan-block terms of (3); the later paper of
Masáková–Mazáč–Pelantová states (§14) that its answer covers nonsingular maps diagonalizable over ℂ
only. The entry also proves the characterization of every admissible splitting for squarefree `χ_A`
((3)(d)), non-generic splittings included (its necessity half is the argument of
Masáková–Mazáč–Pelantová, Lemma 5.1, which uses only the injectivity `ℤ^ι ∩ H = 0` and so needs no
genericity), and (1) for every integer matrix and (4) for every nonsingular hyperbolic integer
matrix, with no diagonalizability hypothesis; for diagonalizable `A` and generic schemes, the
uniqueness of the minimal scheme in (4) and of the minimal physical line in (5) is immediate from
Masáková–Mazáč–Pelantová, Cor. 13.4. For `det A ≠ 0` and squarefree `χ_A` with a factor `Φ_n`,
`n ∉ {1, 2, 3, 4, 6}`, the minimal scheme is not unique, by (3)(d). For squarefree `χ_A`, hence
diagonalizable `A`, the count of (3) also follows from the arguments of Masáková–Mazáč–Pelantová,
Lemma 5.1, Prop. 8.1(iii) and Cor. 13.4 (numbering of arXiv:1909.10753v2), which are stated there
for generic (aperiodic) schemes, under which a factor `x ± 1`, `Φ₃`, `Φ₄` or `Φ₆` admits no scheme.
We did not find the least physical dimension for a given lattice map, statement (3), stated in the
sources we read (search completed 2026-10-20); this is a search result, not a guarantee.

**The proofs.** No Jordan form of `A` and no diagonalization of `A` is used: the Jordan data of (3)
are ranks of rational kernels. The lower bound in (3): admissibility is power-boundedness on `H`
(1), the largest power-bounded invariant summand has dimension `Σ_p (m_p s_p + c_p r₁(p))`, `s_p`
the number of roots of `p` inside the unit disk (a power-bounded map is semisimple on its
unit-circle part, and an invariant summand killed by `p(A)` misses `im p(A)`), and at a cyclotomic
factor with all Jordan blocks of size one the physical space meets the generalized eigenspace in at
least `min (deg p, 2)` dimensions. The upper bound: from a largest power-bounded summand, the
component of each cyclotomic factor is replaced by a scheme of the integer matrix by which `A` acts
on a `ℤ`-basis of the lattice points of that component; there the least scheme is a generic line or
plane at one place of `ℚ(ζ_n)` if all Jordan blocks have size one, and otherwise an internal space
tilted into the socle of the larger blocks, with generic parameters avoiding countably many proper
affine subspaces (Haar measure). Such a splitting is admissible once, at every cyclotomic factor, no
lattice vector of `H` and no integer vector orthogonal to `E` is seen, by the rational annihilator
of a lattice vector and Kronecker's theorem for the factors of `χ_A`
(`NumberField.Embeddings.pow_eq_one_of_norm_eq_one`); density is (2). Part (d) of (3) rests on a
rational kernel lemma (for an irreducible rational factor `p` of `χ_A`, `ker p(A)` contains a
nonzero lattice vector) and a Lagrange-interpolation power bound on `H`. The rates in (4) come from
Gelfand's spectral radius formula. The signatures in (10) and (11) are computed by Sylvester's law
of inertia in Mathlib (D. Loeffler's `sigPos`, `sigNeg`). Statements (8)–(11) are about explicit
integer matrices. That `Cρ` and `CQ` are multiplication by `ρ` and `Q` in the power bases is their
definition (companion matrices), so `Cρ^i ⊗ CQ^j` is multiplication by `ρ^i Q^j` in the product
basis. That the `ρ^i Q^j` are a `ℤ`-basis of the ring of integers of `ℚ(ρ, Q)` is statement (8) of
the author's registered entry PALOMAR-2026-10-21-000012
(stalex444/pdt-hermite-signature-compositum@5aa870e98236ba240561b798265c629df8c2d031); that
`GramRho`, `GramQ` and `GramRho ⊗ GramQ` are the Gram matrices of the trace forms in these bases is
statements (8), (9) and (19) of the author's registered entry PALOMAR-2026-09-02-000014, in which
`ℚ(ρ) ⊗ ℚ(Q)` is the field `ℚ(ρ, Q)` (its (23)). These are cited, not compared. The circle-freeness
of `ℚ(ρ, Q)` (statement (17) of PALOMAR-2026-10-21-000012) is ported to this repository
(`InflationDimension/Compositum`) and used in (9). The author's registered entry
PALOMAR-2026-09-04-000004 shows (`quartic_record_obstruction`) that a window on the real expanding
place of `ℤ[Q]`, observed at the complex place, gives a set that is not uniformly discrete. Keeping
the dropped coordinate at `q′` gives the model set of the `Q`-invariant scheme whose window line is
the expanding real place; it is a Delone set by (13), but it is not `Q`-admissible by (4), since
every admissible `Q`-invariant scheme on `ℤ⁴` has `H ⊆ E^s`, the line of `q′`. Dropping that
coordinate, which is unbounded along `Q⁻ⁿ` (`quartic_escaping_coordinate`), is what destroys uniform
discreteness. (11) is the admissible scheme.

**Definitions.** The entry's definitions are stated in this file, between the lines
`-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`; that text is byte for byte the body
of `InflationDimension/Defs.lean`, on which the proof modules are built. This file imports Mathlib
only. The Mathlib definitions the statements use are quoted in `MATHLIB_DEFINITIONS.md`, and
`DefinitionAudit.lean` checks facts about them.

**Not formalized.** The least physical dimension when `det A = 0`; the least dimension under
aperiodicity; and the regularity and pure-point diffraction of the model sets (Hof 1995;
Schlottmann 2000), which are cited only.

**Application (cited, not a claim of the entry).** In the author's Pisot Dimensional Theory, `ℚ(ρ)`
is the arithmetic of three-dimensional space and `ℚ(Q)` the arithmetic of four-dimensional
spacetime, and their compositum `K`, whose integers are `ℤ[ρ] ⊗ ℤ[Q]`, is the parent of both (the
author's registered entry PALOMAR-2026-10-21-000012
(stalex444/pdt-hermite-signature-compositum@5aa870e98236ba240561b798265c629df8c2d031), statements
(7), (8)). A model set is the shadow of a lattice cut through a window, a standard mathematical
model of a quasicrystal (Moody 2000). Read through the theory, this entry's theorems fix how many
dimensions each of the theory's inflations needs to be the symmetry of one, and which ones.

Space inflates the parent through spacetime, and spacetime inflates it through space. On the
parent's lattice the plastic inflation `ρ` needs exactly four physical dimensions, and only one
scheme attains four (9). Those four are a copy of spacetime's: `ρ` has a single expanding embedding
in `ℚ(ρ)`, the real one, and the spectral projection maps the quartic sector onto them, carrying
`ℤ[Q]` with its trace form unchanged, of Lorentzian type `(3, 1)` (10). `ρ` acts on them as a pure
dilation by `ρ ≈ 1.3247`, the same stretch in every direction (10). Symmetrically, the unit
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
-/

-- BEGIN SHARED DEFINITIONS
-- The definitions of this entry that the compared statements use. This block is, byte for byte,
-- the body of `InflationDimension/Defs.lean`, on which the proof modules are built; both files
-- import Mathlib only.

namespace InflationDimension

open Polynomial Filter Topology Module
open scoped Kronecker

noncomputable section

section Scheme

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integer lattice `ℤ^ι ⊂ ℝ^ι`: the `ℤ`-span of the standard basis. -/
def intLattice (ι : Type*) [Fintype ι] [DecidableEq ι] : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))

/-- The real-linear map `v ↦ A v` of an integer matrix `A` on `ℝ^ι`. -/
def act (A : Matrix ι ι ℤ) : Module.End ℝ (ι → ℝ) :=
  Matrix.toLin' (A.map (Int.cast : ℤ → ℝ))

/-- An `A`-invariant cut-and-project scheme on the lattice `ℤ^ι`: a splitting `ℝ^ι = E ⊕ H`
into `A`-invariant subspaces (`E` physical, `H` internal) such that `ℤ^ι ∩ H = 0` (so the
projection to `E` along `H` is injective on the lattice) and the projection of `ℤ^ι` to `H`
along `E` is dense in `H`. Aperiodicity (`ℤ^ι ∩ E = 0`) is not required, and `H = 0` is
allowed. -/
structure InvariantCPS (A : Matrix ι ι ℤ) where
  /-- The physical space. -/
  E : Submodule ℝ (ι → ℝ)
  /-- The internal space. -/
  H : Submodule ℝ (ι → ℝ)
  isCompl : IsCompl E H
  mapsTo_E : ∀ v ∈ E, act A v ∈ E
  mapsTo_H : ∀ v ∈ H, act A v ∈ H
  inj : ∀ γ ∈ intLattice ι, γ ∈ H → γ = 0
  dense : (H : Set (ι → ℝ)) ⊆ closure (H.projection E isCompl.symm '' (intLattice ι : Set (ι → ℝ)))

namespace InvariantCPS

variable {A : Matrix ι ι ℤ} (S : InvariantCPS A)

/-- The projection `π_E` onto the physical space along the internal space. -/
def πE : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := S.E.projection S.H S.isCompl

/-- The projection `π_H` onto the internal space along the physical space. -/
def πH : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := S.H.projection S.E S.isCompl.symm

/-- A window: a bounded subset of `H` containing a relative ball of `H` (nonempty interior in
`H`). -/
def IsWindow (W : Set (ι → ℝ)) : Prop :=
  W ⊆ S.H ∧ Bornology.IsBounded W ∧
    ∃ c ∈ S.H, ∃ r > (0 : ℝ), Metric.ball c r ∩ (S.H : Set (ι → ℝ)) ⊆ W

/-- The model set `Λ(W) = {π_E γ : γ ∈ ℤ^ι, π_H γ ∈ W}`. -/
def modelSet (W : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {x | ∃ γ ∈ intLattice ι, S.πH γ ∈ W ∧ S.πE γ = x}

/-- The scheme is admissible if some window `W` gives a model set with `A Λ(W) ⊆ Λ(W)`. -/
def Admissible : Prop :=
  ∃ W : Set (ι → ℝ), S.IsWindow W ∧ Set.MapsTo (act A) (S.modelSet W) (S.modelSet W)

/-- The orbit window `W_* = {h ∈ H : ‖Aⁿ h‖ ≤ 1 for all n ≥ 0}` (sup norm on `ℝ^ι`). -/
def orbitWindow : Set (ι → ℝ) :=
  {h | h ∈ S.H ∧ ∀ n : ℕ, ‖(act A ^ n) h‖ ≤ 1}

end InvariantCPS

/-- The physical dimensions of the admissible `A`-invariant schemes on `ℤ^ι`. The least
element is the least physical dimension `d(A)`. -/
def physDims (A : Matrix ι ι ℤ) : Set ℕ :=
  {d | ∃ S : InvariantCPS A, S.Admissible ∧ finrank ℝ S.E = d}

end Scheme

section Spectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complex eigenvalues of `A` with multiplicity: the roots of `χ_A` in `ℂ`. -/
def eigenvalues (A : Matrix ι ι ℤ) : Multiset ℂ := (A.charpoly.map (Int.castRingHom ℂ)).roots

/-- `U(A)`: the number of eigenvalues of modulus `> 1`, with multiplicity. -/
def unstableCount (A : Matrix ι ι ℤ) : ℕ :=
  Multiset.card ((eigenvalues A).filter (fun z => 1 < ‖z‖))

/-- `A` is hyperbolic: no eigenvalue lies on the unit circle. -/
def IsHyperbolic (A : Matrix ι ι ℤ) : Prop := ∀ z ∈ eigenvalues A, ‖z‖ ≠ 1

/-- The stable set `E^s(A) = {v : Aⁿ v → 0}`. -/
def stableSet (A : Matrix ι ι ℤ) : Set (ι → ℝ) :=
  {v | Tendsto (fun n : ℕ => (act A ^ n) v) atTop (𝓝 0)}

/-- The unstable set `E^u(A)`: the vectors with a backward orbit tending to `0`. -/
def unstableSet (A : Matrix ι ι ℤ) : Set (ι → ℝ) :=
  {v | ∃ w : ℕ → ι → ℝ, w 0 = v ∧ (∀ n, act A (w (n + 1)) = w n) ∧ Tendsto w atTop (𝓝 0)}

/-- `χ_A` over `ℚ`. -/
def charpolyQ (A : Matrix ι ι ℤ) : ℚ[X] := A.charpoly.map (Int.castRingHom ℚ)

/-- A rational polynomial all of whose complex roots lie on the unit circle. -/
def IsCircleFactor (p : ℚ[X]) : Prop := ∀ z ∈ (p.map (algebraMap ℚ ℂ)).roots, ‖z‖ = 1

open Classical in
/-- The circle term of the count: over the irreducible factors of `χ_A` over `ℚ` whose roots
all lie on the unit circle, each counted with its multiplicity in `χ_A` (the multiset
`normalizedFactors`), `1` for a factor of degree one (`X - 1` or `X + 1`) and `2` for each other
one. -/
def circleCount (A : Matrix ι ι ℤ) : ℕ :=
  (((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).filter IsCircleFactor).map
    (fun p => min p.natDegree 2)).sum

end Spectrum

section JordanData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `m_p`: the multiplicity of the irreducible factor `p` in `χ_A` over `ℚ`. -/
def factorMult (A : Matrix ι ι ℤ) (p : ℚ[X]) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).count p

/-- `dim_ℚ ker p(A)^k` for `A` acting on `ℚ^ι`. -/
def kerRankQ (A : Matrix ι ι ℤ) (p : ℚ[X]) (k : ℕ) : ℕ :=
  finrank ℚ (LinearMap.ker (aeval (Matrix.toLin' (A.map (Int.cast : ℤ → ℚ))) (p ^ k)))

/-- `r₁(p) = (2 dim_ℚ ker p(A) − dim_ℚ ker p(A)²) / deg p`, computed from ranks: the number of
Jordan blocks of size one at each complex root of `p`. -/
def sizeOneBlocks (A : Matrix ι ι ℤ) (p : ℚ[X]) : ℕ :=
  (2 * kerRankQ A p 1 - kerRankQ A p 2) / p.natDegree

/-- `u_p`: the number of complex roots of `p` of modulus `> 1`. -/
def expandingRootCount (p : ℚ[X]) : ℕ :=
  Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖))

/-- `c_p`: the number of complex roots of `p` of modulus `1`. -/
def circleRootCount (p : ℚ[X]) : ℕ :=
  Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ‖z‖ = 1))

open Classical in
/-- The contribution of an irreducible factor `p` of `χ_A` over `ℚ`:
`m_p u_p + c_p (m_p − r₁(p))`, plus `min (deg p, 2)` if every root of `p` lies on the unit circle
and every Jordan block at the roots of `p` has size one (`r₁(p) = m_p`). -/
def factorContribution (A : Matrix ι ι ℤ) (p : ℚ[X]) : ℕ :=
  factorMult A p * expandingRootCount p +
      circleRootCount p * (factorMult A p - sizeOneBlocks A p) +
    if IsCircleFactor p ∧ sizeOneBlocks A p = factorMult A p then min p.natDegree 2 else 0

/-- The sum of the contributions over the distinct irreducible factors of `χ_A` over `ℚ`. -/
def dimensionFormula (A : Matrix ι ι ℤ) : ℕ :=
  ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
    factorContribution A p

end JordanData

section Instances

/-- Multiplication by `ρ` on `ℤ[ρ]` in the basis `1, ρ, ρ²`, where `ρ³ = ρ + 1`: the companion
matrix of `x³ − x − 1`. -/
def Cρ : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

/-- Multiplication by `Q` on `ℤ[Q]` in the basis `1, Q, Q², Q³`, where `Q⁴ = Q + 1`: the
companion matrix of `x⁴ − x − 1`. -/
def CQ : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

/-- The companion matrix of the Salem polynomial `x⁴ − x³ − x² − x + 1`. -/
def CSalem : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 0, -1; 1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1]

/-- The integer matrix `Σ a(i,j) · (Cρ^i ⊗ CQ^j)` on `ℤ³ ⊗ ℤ⁴`, indexed by the pairs `(i,j)`:
multiplication by `Σ a(i,j) ρ^i Q^j` in the product basis `ρ^i Q^j`. -/
def mulMatrix (a : Fin 3 × Fin 4 → ℤ) : Matrix (Fin 3 × Fin 4) (Fin 3 × Fin 4) ℤ :=
  ∑ p : Fin 3 × Fin 4, a p • ((Cρ ^ (p.1 : ℕ)) ⊗ₖ (CQ ^ (p.2 : ℕ)))

/-- `Cρ ⊗ I₄`: multiplication by `ρ` in the product basis. -/
def mulρ : Matrix (Fin 3 × Fin 4) (Fin 3 × Fin 4) ℤ := Cρ ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℤ)

/-- `I₃ ⊗ CQ`: multiplication by `Q` in the product basis. -/
def mulQ : Matrix (Fin 3 × Fin 4) (Fin 3 × Fin 4) ℤ := (1 : Matrix (Fin 3) (Fin 3) ℤ) ⊗ₖ CQ

/-- `I₃ ⊗ (I₄ − CQ³)`: multiplication by `θ = 1 − Q³ = −Q⁻¹` in the product basis. -/
def mulθ : Matrix (Fin 3 × Fin 4) (Fin 3 × Fin 4) ℤ :=
  (1 : Matrix (Fin 3) (Fin 3) ℤ) ⊗ₖ (1 - CQ ^ 3)

/-- `Cρ ⊗ CQ`: multiplication by `ρQ` in the product basis. -/
def mulρQ : Matrix (Fin 3 × Fin 4) (Fin 3 × Fin 4) ℤ := Cρ ⊗ₖ CQ

/-- The Gram matrix `(Tr(ρ^{i+j}))` of the trace form of `ℚ(ρ)` in the basis `1, ρ, ρ²`: the
Hankel matrix of the power sums `3, 0, 2, 3, 2` of the roots of `x³ − x − 1`. -/
def GramRho : Matrix (Fin 3) (Fin 3) ℤ := !![3, 0, 2; 0, 2, 3; 2, 3, 2]

/-- The Gram matrix `(Tr(Q^{i+j}))` of the trace form of `ℚ(Q)` in the basis `1, Q, Q², Q³`:
the Hankel matrix of the power sums `4, 0, 0, 3, 4, 0, 3` of the roots of `x⁴ − x − 1`. -/
def GramQ : Matrix (Fin 4) (Fin 4) ℤ := !![4, 0, 0, 3; 0, 0, 3, 4; 0, 3, 4, 0; 3, 4, 0, 3]

/-- The quadratic form `c ↦ Σ_{i,j} G_{ij} c_i c_j` on `ℝ^n` of an integer Gram matrix `G`. -/
def formOf {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℤ) :
    QuadraticForm ℝ (n → ℝ) :=
  (G.map (Int.cast : ℤ → ℝ)).toQuadraticForm'

/-- The bilinear pairing `(x, y) ↦ xᵀ G y` of an integer Gram matrix `G`. -/
def pairing {n : Type*} [Fintype n] (G : Matrix n n ℤ) (x y : n → ℝ) : ℝ :=
  x ⬝ᵥ Matrix.mulVec (G.map (Int.cast : ℤ → ℝ)) y

/-- The quartic sector `span{ρ⁰ Q^j}` inside `ℝ³ ⊗ ℝ⁴`: `u ↦ e₀ ⊗ u`. -/
def sectorQ (u : Fin 4 → ℝ) : Fin 3 × Fin 4 → ℝ := fun p => if p.1 = 0 then u p.2 else 0

/-- The cubic sector `span{ρ^i Q⁰}` inside `ℝ³ ⊗ ℝ⁴`: `u ↦ u ⊗ e₀`. -/
def sectorRho (u : Fin 3 → ℝ) : Fin 3 × Fin 4 → ℝ := fun p => if p.2 = 0 then u p.1 else 0

end Instances

end

end InflationDimension
-- END SHARED DEFINITIONS

open Polynomial Filter Topology Module QuadraticMap
open scoped Kronecker Pointwise

open InflationDimension

namespace ModelSetDimension

/-- **(1) Admissibility criterion**, for every integer matrix `A`. (a) An `A`-invariant scheme is
admissible if and only if `A` is power-bounded on `H`; then the orbit window
`W_* = {h ∈ H : ‖Aⁿ h‖ ≤ 1 for all n}` is a compact, convex, centrally symmetric window with
`A W_* ⊆ W_*` and `A Λ(W_*) ⊆ Λ(W_*)`. (b) Per window: `A Λ(W) ⊆ Λ(W)` if and only if `A` maps the
lattice points `W ∩ π_H(ℤ^ι)` of the window into `W`; for a closed window contained in the
closure of its lattice points, if and only if `A W ⊆ W`. (c) Every eigenvalue of `A|_H` lies in
the closed unit disk, so `U(A) ≤ dim E`. The necessity half is Masáková–Mazáč–Pelantová (2021),
Prop. 13.2 and Cor. 13.4, there for diagonalizable maps and generic schemes. -/
theorem admissibility_criterion {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (S : InvariantCPS A) :
    (S.Admissible ↔ ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ S.H, ‖(act A ^ n) v‖ ≤ C * ‖v‖) ∧
    ((∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ S.H, ‖(act A ^ n) v‖ ≤ C * ‖v‖) →
      S.IsWindow S.orbitWindow ∧ IsCompact S.orbitWindow ∧ Convex ℝ S.orbitWindow ∧
        (∀ h ∈ S.orbitWindow, -h ∈ S.orbitWindow) ∧
        Set.MapsTo (act A) S.orbitWindow S.orbitWindow ∧
        Set.MapsTo (act A) (S.modelSet S.orbitWindow) (S.modelSet S.orbitWindow)) ∧
    (∀ W : Set (ι → ℝ), Set.MapsTo (act A) (S.modelSet W) (S.modelSet W) ↔
      Set.MapsTo (act A) (W ∩ S.πH '' (intLattice ι : Set (ι → ℝ))) W) ∧
    (∀ W : Set (ι → ℝ), IsClosed W →
      W ⊆ closure (W ∩ S.πH '' (intLattice ι : Set (ι → ℝ))) →
      (Set.MapsTo (act A) (S.modelSet W) (S.modelSet W) ↔ Set.MapsTo (act A) W W)) ∧
    (S.Admissible →
      (∀ z ∈ (((act A).restrict S.mapsTo_H).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1) ∧
        unstableCount A ≤ finrank ℝ S.E) := by
  sorry

/-- **(2) Kronecker's density criterion**, in cut-and-project form: for complementary subspaces
`E`, `H` of `ℝ^ι`, the projection of `ℤ^ι` to `H` along `E` is dense in `H` if and only if every
real linear functional that is integer-valued on `ℤ^ι` and vanishes on `E` is zero. The
cut-and-project form is Pleasants (2000), Cor. 2.12, and Masáková–Mazáč–Pelantová (2021),
Prop. 3.3(iii). -/
theorem kronecker_density_criterion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E H : Submodule ℝ (ι → ℝ)) (hc : IsCompl E H) :
    (H : Set (ι → ℝ)) ⊆ closure (H.projection E hc.symm '' (intLattice ι : Set (ι → ℝ))) ↔
      ∀ f : (ι → ℝ) →ₗ[ℝ] ℝ, (∀ γ ∈ intLattice ι, ∃ n : ℤ, f γ = n) →
        (∀ v ∈ E, f v = 0) → f = 0 := by
  sorry

/-- **(3) The least physical dimension** (`det A ≠ 0`; any `χ_A`; eigenvalues on the unit circle and
Jordan blocks allowed). (a) `d(A) = Σ_p f_p` over the distinct irreducible factors `p` of `χ_A`
over `ℚ` (`dimensionFormula A`), where `f_p = m_p u_p + c_p (m_p − r₁(p))`, plus `min (deg p, 2)`
when every root of `p` lies on the unit circle and `r₁(p) = m_p` (`factorContribution`): every
root of modulus `> 1` counts with its multiplicity, every Jordan block of size `≥ 2` at a root on
the unit circle counts in full, and a cyclotomic factor all of whose Jordan blocks have size one
costs one line (`x ± 1`) or one plane (`Φ_n`, `n ≥ 3`), however large its multiplicity.
Equivalently, through the Jordan form (which the definitions do not use),
`d(A) = Σ_{|λ|>1} a_λ + Σ_{|λ|=1} (a_λ − s_λ) + #{n ≤ 2 : n ∈ 𝒮(A)} + 2·#{n ≥ 3 : n ∈ 𝒮(A)}`,
with `a_λ` the multiplicity of `λ`, `s_λ` the number of Jordan blocks of size one at `λ`, and
`𝒮(A)` the set of `n` whose primitive `n`-th roots of unity are eigenvalues with all Jordan blocks
of size one. (b) The value is an invariant of rational similarity: if `P A = B P` with `P` rational
and invertible, `B` has the same least physical dimension. (c) The irreducible factors whose roots
all lie on the unit circle are exactly the cyclotomic ones (Kronecker). (d) For `χ_A` squarefree
over `ℚ`: every `A`-invariant splitting `ℝ^ι = E ⊕ H` is `E = ker q_E(A)`, `H = ker q_H(A)` with
`χ_A = q_E q_H` over `ℝ`, where `q_E`, `q_H` are the characteristic polynomials of `A|_E`, `A|_H`;
it carries an admissible scheme if and only if every root of `q_H` lies in the closed unit disk and
every irreducible factor of `χ_A` over `ℚ` shares a complex root with `q_E`; and the value is
`U(A) + circleCount A`. For squarefree `χ_A`, hence diagonalizable `A`, this count also follows
from the arguments of Masáková–Mazáč–Pelantová (2021), Lemma 5.1, Prop. 8.1(iii) and Cor. 13.4,
which are stated there for generic (aperiodic) schemes, under which a factor `x ± 1`, `Φ₃`, `Φ₄`
or `Φ₆` admits no scheme. -/
theorem least_physical_dimension {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hdet : A.det ≠ 0) :
    IsLeast (physDims A) (dimensionFormula A) ∧
    (∀ (B : Matrix ι ι ℤ) (P : Matrix ι ι ℚ), IsUnit P.det →
      P * A.map (Int.castRingHom ℚ) = B.map (Int.castRingHom ℚ) * P →
        IsLeast (physDims B) (dimensionFormula A)) ∧
    (∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      IsCircleFactor p ↔ ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ) ∧
    (Squarefree (charpolyQ A) →
      (∀ (E H : Submodule ℝ (ι → ℝ)), IsCompl E H → ∀ (hE : ∀ v ∈ E, act A v ∈ E)
          (hH : ∀ v ∈ H, act A v ∈ H),
        A.charpoly.map (Int.castRingHom ℝ) =
            ((act A).restrict hE).charpoly * ((act A).restrict hH).charpoly ∧
          E = LinearMap.ker (aeval (act A) ((act A).restrict hE).charpoly) ∧
          H = LinearMap.ker (aeval (act A) ((act A).restrict hH).charpoly) ∧
          ((∃ S : InvariantCPS A, S.E = E ∧ S.H = H ∧ S.Admissible) ↔
            (∀ z ∈ (((act A).restrict hH).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1) ∧
              ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
                ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots,
                  aeval z ((act A).restrict hE).charpoly = 0)) ∧
        dimensionFormula A = unstableCount A + circleCount A) := by
  sorry

/-- **(4) The hyperbolic case**, every `χ_A` (`det A ≠ 0`, no eigenvalue on the unit circle). An
`A`-invariant scheme is admissible if and only if `E ⊇ E^u(A)`, if and only if `H ⊆ E^s(A)`, and
an `A`-invariant splitting `ℝ^ι = E ⊕ H` carries an admissible scheme if and only if
`E ⊇ E^u(A)`. `(E^u, E^s)` carries an admissible scheme, `d(A) = U(A)`, and every admissible
scheme with `dim E = U(A)` is `(E^u, E^s)`. No diagonalizability is assumed. For diagonalizable
maps and generic schemes the necessity of `H ⊆ E^s` is Masáková–Mazáč–Pelantová (2021),
Prop. 13.2 and Cor. 13.4; the statement is the inclusion-notion analogue of the expansive case of
Harriss–Koivusalo–Walton (preprint, arXiv:2512.13659), Thm 3.3. -/
theorem hyperbolic_case {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hdet : A.det ≠ 0) (hhyp : IsHyperbolic A) :
    (∀ S : InvariantCPS A, (S.Admissible ↔ unstableSet A ⊆ (S.E : Set (ι → ℝ))) ∧
      (S.Admissible ↔ (S.H : Set (ι → ℝ)) ⊆ stableSet A)) ∧
    (∀ (E H : Submodule ℝ (ι → ℝ)), IsCompl E H → (∀ v ∈ E, act A v ∈ E) →
      (∀ v ∈ H, act A v ∈ H) →
      ((∃ S : InvariantCPS A, S.E = E ∧ S.H = H ∧ S.Admissible) ↔
        unstableSet A ⊆ (E : Set (ι → ℝ)))) ∧
    (∃ S : InvariantCPS A, (S.E : Set (ι → ℝ)) = unstableSet A ∧
      (S.H : Set (ι → ℝ)) = stableSet A ∧ S.Admissible) ∧
    IsLeast (physDims A) (unstableCount A) ∧
    ∀ S : InvariantCPS A, S.Admissible → finrank ℝ S.E = unstableCount A →
      (S.E : Set (ι → ℝ)) = unstableSet A ∧ (S.H : Set (ι → ℝ)) = stableSet A := by
  sorry

/-- **(5) Dimension one: Pisot or Salem** (`det A ≠ 0`, any `χ_A`). `d(A) = 1` if and only if `χ_A`
is irreducible over `ℚ` with exactly one root of modulus `> 1`, or `A = ±1` on a lattice of any
positive rank. In the irreducible case that root `r` is real, every other root has modulus at most
`1` (so `|r|` is a Pisot number, a Salem number, or for `#ι = 1` an integer `≥ 2`), and every
admissible scheme with `dim E = 1` has `E` the `r`-eigenline. For irreducible `χ_A` this is the
lattice-first, model-set form of Meyer's theorem (1972; 1995, Thm 6; the Meyer-set inflation case
also Lagarias 1999, Thm 4.1): existence on the line and the model-set case of necessity, for
`A`-invariant schemes. The Salem case is the model set on `ℤ^s` of Solomyak (2020), §4(iv),
credited there to Akiyama. The clause `A = ±1`, in any rank, is a corollary of (3). -/
theorem dimension_one_pisot_or_salem {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hdet : A.det ≠ 0) :
    (IsLeast (physDims A) 1 ↔
      (Irreducible (charpolyQ A) ∧ unstableCount A = 1) ∨ (Nonempty ι ∧ (A = 1 ∨ A = -1))) ∧
    (Irreducible (charpolyQ A) → unstableCount A = 1 →
      ∃ r : ℝ, 1 < |r| ∧ (r : ℂ) ∈ eigenvalues A ∧ (∀ z ∈ eigenvalues A, z ≠ r → ‖z‖ ≤ 1) ∧
        ∀ S : InvariantCPS A, S.Admissible → finrank ℝ S.E = 1 →
          S.E = LinearMap.ker (act A - r • LinearMap.id)) := by
  sorry

/-- **(6) Finite order: the cyclotomic case.** If `A^k = 1` for some `k ≥ 1`, every irreducible
factor of `χ_A` over `ℚ` is cyclotomic and `d(A)` counts, over the distinct factors, `1` for
`Φ₁ = x − 1` and `Φ₂ = x + 1` and `2` for each `Φ_n`, `n ≥ 3`, whatever the multiplicities; for
example, an integer matrix of order `5` with `χ_A = (x − 1)² Φ₅` has `d = 3`. The same count holds
when `χ_A` is squarefree with all roots on the unit circle. In particular every integer matrix with
characteristic polynomial `Φ_n`, `n ≥ 3` (for example, multiplication by `ζ_n` on `ℤ[ζ_n]`), has
`d = 2`: the physical plane of the classical planar cyclotomic model sets (Huck, arXiv:math/0701141;
Baake–Grimm 2013, §7.3), whose internal dimension is `φ(n) − 2`. -/
theorem finite_order_case {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) :
    (∀ k : ℕ, 0 < k → A ^ k = 1 →
      (∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
        ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ) ∧
      IsLeast (physDims A)
        (∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
          min p.natDegree 2)) ∧
    (Squarefree (charpolyQ A) → (∀ z ∈ eigenvalues A, ‖z‖ = 1) →
      (∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
        ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ) ∧
      IsLeast (physDims A)
        (((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).map
          (fun p => min p.natDegree 2)).sum)) ∧
    ∀ n : ℕ, 3 ≤ n → A.charpoly = cyclotomic n ℤ → IsLeast (physDims A) 2 := by
  sorry

/-- **(7) Jordan blocks on the unit circle.** On `ℤ²`, `I₂` and the Jordan block
`J₂ = [[1, 1], [0, 1]]` both have `χ = (x − 1)²`, for which the squarefree count of (3), with
`x − 1` counted twice, gives `2`; but `d(I₂) = 1` (a cyclotomic factor with Jordan blocks of size
one costs one line, whatever its multiplicity) and `d(J₂) = 2` (a Jordan block of size two counts
in full). On `ℤ³` and `ℤ⁴`, `1 ⊕ J₂(1)` and `1 ⊕ J₃(1)` have `d = 2` and `d = 3`: the block of
size one costs nothing, its internal line being tilted into the socle of the larger block. -/
theorem jordan_block_witnesses :
    (1 : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    unstableCount (1 : Matrix (Fin 2) (Fin 2) ℤ) + circleCount (1 : Matrix (Fin 2) (Fin 2) ℤ) =
      2 ∧
    IsLeast (physDims (1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 ∧
    IsLeast (physDims (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) 2 ∧
    IsLeast (physDims (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ)) 2 ∧
    IsLeast (physDims (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) ℤ)) 3 := by
  sorry

/-- **(8) The sector rings.** On `ℤ[ρ]` (basis `1, ρ, ρ²`) and `ℤ[Q]` (basis `1, Q, Q², Q³`),
multiplication by `ρ`, `ρ⁻¹ = ρ² − 1`, `Q` and `θ = −Q⁻¹ = 1 − Q³` has the stated characteristic
polynomials, is hyperbolic, and needs exactly `1`, `2`, `3`, `1` physical dimensions; by (4) each
minimum is attained only by `(E^u, E^s)`. The one expanding eigenvalue of `θ` is real,
`t = −1/q′ ≈ 1.38028`, where `q′` is the negative real root of `x⁴ − x − 1`. -/
theorem sector_rings :
    Cρ.charpoly = X ^ 3 - X - 1 ∧ (Cρ ^ 2 - 1).charpoly = X ^ 3 + X ^ 2 - 1 ∧
    CQ.charpoly = X ^ 4 - X - 1 ∧ (1 - CQ ^ 3).charpoly = X ^ 4 - X ^ 3 - 1 ∧
    IsHyperbolic Cρ ∧ IsHyperbolic (Cρ ^ 2 - 1) ∧ IsHyperbolic CQ ∧ IsHyperbolic (1 - CQ ^ 3) ∧
    IsLeast (physDims Cρ) 1 ∧ IsLeast (physDims (Cρ ^ 2 - 1)) 2 ∧
    IsLeast (physDims CQ) 3 ∧ IsLeast (physDims (1 - CQ ^ 3)) 1 ∧
    ∀ z ∈ eigenvalues (1 - CQ ^ 3), 1 < ‖z‖ →
      z.im = 0 ∧ (1.3802 : ℝ) < z.re ∧ z.re < 1.3803 := by
  sorry

/-- **(9) The degree-12 lattice `ℤ[ρ] ⊗ ℤ[Q]`.** For every integer combination
`α = Σ a(i,j) ρ^i Q^j` other than `0`, `1`, `−1`, multiplication by `α` in the product basis
(`mulMatrix a`) is nonsingular (`det ≠ 0`) and hyperbolic, so by (4) it needs exactly `U`
physical dimensions, attained only by `(E^u, E^s)`. For `ρ`, `θ`, `ρQ` and `Q` the values are
`4`, `3`, `5`, `9`. -/
theorem compositum_lattice :
    (∀ a : Fin 3 × Fin 4 → ℤ, a ≠ 0 → a ≠ Pi.single (0, 0) 1 → a ≠ -Pi.single (0, 0) 1 →
      (mulMatrix a).det ≠ 0 ∧ IsHyperbolic (mulMatrix a) ∧
        IsLeast (physDims (mulMatrix a)) (unstableCount (mulMatrix a))) ∧
    IsHyperbolic mulρ ∧ IsHyperbolic mulθ ∧ IsHyperbolic mulρQ ∧ IsHyperbolic mulQ ∧
    IsLeast (physDims mulρ) 4 ∧ IsLeast (physDims mulθ) 3 ∧
    IsLeast (physDims mulρQ) 5 ∧ IsLeast (physDims mulQ) 9 := by
  sorry

/-- **(10) The two dilations**, on `ℝ³ ⊗ ℝ⁴` with the pairing of `GramRho ⊗ GramQ`. (a) `ρ`
(`mulρ`) acts on `E^u` as the real scalar `r`, `r³ = r + 1`, and the spectral projection `P`
onto `E^u` along `E^s` carries the quartic sector `e₀ ⊗ ℝ⁴` bijectively onto `E^u`, with the
pairing of `GramRho ⊗ GramQ` equal to that of `GramQ` (multiple exactly `1`); `GramQ` has type
`(3,1)`. (b) `θ = 1 − Q³` (`mulθ`) acts on `E^u` as the real scalar `t > 1`, `t⁴ = t³ + 1`, and
`P` carries the cubic sector `ℝ³ ⊗ e₀` onto `E^u` with the pairing of `GramRho`, of type
`(2,1)`. -/
theorem compositum_dilations :
    (∃ r : ℝ, r ^ 3 = r + 1 ∧ (∀ v ∈ unstableSet mulρ, act mulρ v = r • v) ∧
      ∃ P : (Fin 3 × Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 × Fin 4 → ℝ),
        (∀ v, P v ∈ unstableSet mulρ) ∧ (∀ v ∈ unstableSet mulρ, P v = v) ∧
        (∀ v ∈ stableSet mulρ, P v = 0) ∧
        (∀ v ∈ unstableSet mulρ, ∃! u : Fin 4 → ℝ, P (sectorQ u) = v) ∧
        ∀ u u' : Fin 4 → ℝ,
          pairing (GramRho ⊗ₖ GramQ) (P (sectorQ u)) (P (sectorQ u')) = pairing GramQ u u') ∧
    (∃ t : ℝ, t ^ 4 = t ^ 3 + 1 ∧ 1 < t ∧ (∀ v ∈ unstableSet mulθ, act mulθ v = t • v) ∧
      ∃ P : (Fin 3 × Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 × Fin 4 → ℝ),
        (∀ v, P v ∈ unstableSet mulθ) ∧ (∀ v ∈ unstableSet mulθ, P v = v) ∧
        (∀ v ∈ stableSet mulθ, P v = 0) ∧
        (∀ v ∈ unstableSet mulθ, ∃! u : Fin 3 → ℝ, P (sectorRho u) = v) ∧
        ∀ u u' : Fin 3 → ℝ,
          pairing (GramRho ⊗ₖ GramQ) (P (sectorRho u)) (P (sectorRho u')) =
            pairing GramRho u u') ∧
    sigPos (formOf GramQ) = 3 ∧ sigNeg (formOf GramQ) = 1 ∧
    sigPos (formOf GramRho) = 2 ∧ sigNeg (formOf GramRho) = 1 := by
  sorry

/-- **(11) The three-dimensional model set of `Q`.** On `ℤ[Q]` (`CQ`), `(E^u, E^s)` is a
`Q`-invariant scheme with `ℤ⁴ ∩ E = 0` (aperiodic). With `q′ < 0` the negative real root of
`x⁴ − x − 1` and the internal coordinate `h ↦ Σ_j h_j q′^j`, the window `|·| ≤ 1/2` is a
segment, its model set is `{π_E γ : |Σ_j γ_j q′^j| ≤ 1/2}`, and `Q` maps it into itself. `Q`
multiplies volume on `E` by `−1/q′`, its non-real eigenvalues have modulus squared `1/(Q|q′|)`
and exceed `1` in modulus, and the form of `GramQ` has type `(2,1)` on `E` and `(1,0)` on `H`. By
(8), `3` is the least physical dimension, attained only here. -/
theorem quartic_model_set :
    ∃ Qr q' : ℝ, Qr ^ 4 = Qr + 1 ∧ 1 < Qr ∧ q' ^ 4 = q' + 1 ∧ q' < 0 ∧
    ∃ S : InvariantCPS CQ,
      (S.E : Set (Fin 4 → ℝ)) = unstableSet CQ ∧ (S.H : Set (Fin 4 → ℝ)) = stableSet CQ ∧
      (∀ γ ∈ intLattice (Fin 4), γ ∈ S.E → γ = 0) ∧
      (∀ W : Set (Fin 4 → ℝ), W = {h | h ∈ S.H ∧ |∑ j, h j * q' ^ (j : ℕ)| ≤ 1 / 2} →
        S.IsWindow W ∧ (∃ a b : Fin 4 → ℝ, W = segment ℝ a b) ∧
        S.modelSet W =
          {x | ∃ γ ∈ intLattice (Fin 4), |∑ j, γ j * q' ^ (j : ℕ)| ≤ 1 / 2 ∧ S.πE γ = x} ∧
        Set.MapsTo (act CQ) (S.modelSet W) (S.modelSet W)) ∧
      LinearMap.det ((act CQ).restrict S.mapsTo_E) = -1 / q' ∧
      (∀ z ∈ eigenvalues CQ, z.im ≠ 0 → ‖z‖ ^ 2 = 1 / (Qr * |q'|) ∧ 1 < ‖z‖) ∧
      sigPos ((formOf GramQ).comp S.E.subtype) = 2 ∧
      sigNeg ((formOf GramQ).comp S.E.subtype) = 1 ∧
      sigPos ((formOf GramQ).comp S.H.subtype) = 1 ∧
      sigNeg ((formOf GramQ).comp S.H.subtype) = 0 := by
  sorry

/-- **(12) A Salem witness.** The companion matrix of `x⁴ − x³ − x² − x + 1`, whose expanding root
is the Salem number `≈ 1.7220838`, is not hyperbolic (two eigenvalues lie on the unit circle)
and has `d = 1`, attained only on the eigenline of that root. The model set is that of
Solomyak (2020), §4(iv), credited there to Akiyama. -/
theorem salem_witness :
    CSalem.charpoly = X ^ 4 - X ^ 3 - X ^ 2 - X + 1 ∧ ¬ IsHyperbolic CSalem ∧
    IsLeast (physDims CSalem) 1 ∧
    ∃ r : ℝ, (1.7220 : ℝ) < r ∧ r < 1.7221 ∧ (r : ℂ) ∈ eigenvalues CSalem ∧
      ∀ S : InvariantCPS CSalem, S.Admissible → finrank ℝ S.E = 1 →
        S.E = LinearMap.ker (act CSalem - r • LinearMap.id) := by
  sorry

/-- **(13) Model sets are Meyer sets.** For every scheme and every window, `Λ(W)` is a Delone
set in `E` (Mathlib's `Delone.DeloneSet`) and `Λ(W) − Λ(W)` is uniformly discrete. This is
classical (Meyer 1972; Moody 1997). -/
theorem modelSet_isMeyer {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (S : InvariantCPS A) (W : Set (ι → ℝ)) (hW : S.IsWindow W) :
    (∃ D : Delone.DeloneSet S.E, (D : Set S.E) = Subtype.val ⁻¹' S.modelSet W) ∧
    ∃ r > (0 : ℝ), ∀ x ∈ S.modelSet W - S.modelSet W, ∀ y ∈ S.modelSet W - S.modelSet W,
      x ≠ y → r ≤ dist x y := by
  sorry

end ModelSetDimension
