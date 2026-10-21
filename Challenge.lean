module
public import Mathlib

@[expose] public section
/-!
# The least physical dimension of an inflation-symmetric model set

Thirteen compared statements, (1)–(13) below: seven about every integer matrix ((1)–(6) and
(13)), two examples ((7) and (12)), and four about the integer matrices of multiplication by `ρ`,
`Q` and their products on `ℤ[ρ]`, `ℤ[Q]` and `ℤ[ρ] ⊗ ℤ[Q]` ((8)–(11)), where `ρ³ = ρ + 1` and
`Q⁴ = Q + 1`.

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
unit circle.

**Scope.**
* The minimum is over `A`-invariant schemes on the fixed lattice `ℤ^ι`: the lattice and the map are
  given and the splitting is chosen. "Minimal" in Baake–Lenz–Moody (2007) and Aujogue (2016) refers
  to a given point set, a different question. The physical-map-first dual, the least lattice rank
  for a given physical map with eigenvalues on the unit circle allowed, is Masáková–Mazáč–Pelantová
  (2021), Thm 13.7 (diagonalizable maps, generic schemes); it is cited, not re-proved.
* Inflation symmetry is the inclusion `A Λ ⊆ Λ`, in Meyer's sense, linear and centred at the origin.
  It is not the substitutional notion (up to mutual local derivability) of Harriss–Koivusalo–Walton.
* Aperiodicity (`ℤ^ι ∩ E = 0`) is not required and `H = 0` is admitted. When `det A ≠ 0` and `χ_A`
  is squarefree, the line of a factor `x ± 1` and the plane of a factor `Φ₃`, `Φ₄` or `Φ₆` lie in
  `E` in every admissible scheme (by (3)), so such a factor excludes an aperiodic scheme; the
  generic schemes of Masáková–Mazáč–Pelantová are aperiodic. The least dimension under aperiodicity
  is a different problem and is not treated.
* The value belongs to the `ℚ`-module `(ℚ^ι, A)`, not to an eigenvalue: multiplication by `ρ` needs
  one physical dimension on `ℤ[ρ]` (8) and four on `ℤ[ρ] ⊗ ℤ[Q]` (9).
* The statements are about inflation-symmetric model sets, not tilings. The substitution
  `a ↦ b, b ↦ c, c ↦ d, d ↦ ab` is primitive and its substitution matrix is the companion matrix of
  `x⁴ − x − 1`, so its self-similar tiling of the line has expansion `Q`; a model set inflated by
  `Q` on `ℤ[Q]` needs three physical dimensions (8).

**The compared statements** (namespace `ModelSetDimension`).
1. `admissibility_criterion` — for every integer `A`, a scheme is admissible if and only if `A`
   is power-bounded on `H`; then the orbit window `W_* = {h ∈ H : ‖Aⁿ h‖ ≤ 1 for all n}` is a
   compact, convex, centrally symmetric window with `A W_* ⊆ W_*`. Per window, `A Λ(W) ⊆ Λ(W)`
   if and only if `A` maps the lattice points `W ∩ π_H(ℤ^ι)` into `W` (for a closed window
   contained in the closure of its lattice points, if and only if `A W ⊆ W`). Admissibility puts
   the eigenvalues of `A|_H` in the closed unit disk, so `U(A) ≤ dim E`.
2. `kronecker_density_criterion` — `π_H(ℤ^ι)` is dense in `H` if and only if every real linear
   functional that is integer-valued on `ℤ^ι` and vanishes on `E` is zero.
3. `least_physical_dimension_squarefree` — for `det A ≠ 0` and `χ_A` squarefree over `ℚ`: every
   invariant splitting is `E = ker q_E(A)`, `H = ker q_H(A)` with `χ_A = q_E q_H`; it carries an
   admissible scheme if and only if the roots of `q_H` lie in the closed unit disk and every
   irreducible factor of `χ_A` over `ℚ` shares a complex root with `q_E`;
   `d(A) = U(A) + circleCount A`; and the irreducible factors with all roots on the unit circle
   are exactly the cyclotomic ones.
4. `hyperbolic_case` — for `det A ≠ 0` and `A` hyperbolic, any `χ_A`: a scheme is admissible if
   and only if `E ⊇ E^u`, if and only if `H ⊆ E^s`; `(E^u, E^s)` carries an admissible scheme;
   `d(A) = U(A)`; and every admissible scheme with `dim E = U(A)` is `(E^u, E^s)`.
5. `dimension_one_pisot_or_salem` — for `det A ≠ 0` and `χ_A` squarefree: `d(A) = 1` if and only
   if `χ_A` is irreducible with exactly one root of modulus `> 1`, or `A = ±1` on `ℤ¹`; that
   root `r` is real, every other root has modulus at most `1`, and every admissible scheme with
   `dim E = 1` has `E` the `r`-eigenline.
6. `finite_order_case` — if `χ_A` is squarefree with all roots on the unit circle, its
   irreducible factors are cyclotomic and `d(A) = Σ_p min(deg p, 2)`; every integer matrix with
   `χ_A = Φ_n`, `n ≥ 3`, has `d = 2`.
7. `squarefree_hypothesis_needed` — `I₂` and `[[1, 1], [0, 1]]` both have `χ = (x − 1)²`, for
   which the count of (3) is `2`; but `d(I₂) = 1`, and `d = 2` for the Jordan block.
8. `sector_rings` — `Cρ`, `Cρ² − 1`, `CQ` and `1 − CQ³`, multiplication by `ρ`, `ρ⁻¹`, `Q` and
   `θ = −Q⁻¹` on `ℤ[ρ]` and `ℤ[Q]`, have characteristic polynomials `x³ − x − 1`, `x³ + x² − 1`,
   `x⁴ − x − 1`, `x⁴ − x³ − 1`, are hyperbolic and have `d = 1, 2, 3, 1`; the one expanding
   eigenvalue of `θ` is real and lies in `(1.3802, 1.3803)`.
9. `compositum_lattice` — for every `a ≠ 0, ±e₀₀`, `mulMatrix a` (multiplication by
   `Σ a(i,j) ρ^i Q^j` on `ℤ³ ⊗ ℤ⁴`) is invertible and hyperbolic, with `d = U`; for `ρ`, `θ`,
   `ρQ` and `Q` the values are `4`, `3`, `5`, `9`.
10. `compositum_dilations` — `ρ` (`mulρ`) acts on `E^u` as a real scalar `r`, `r³ = r + 1`, and
    the projection onto `E^u` along `E^s` maps the sector `e₀ ⊗ ℝ⁴` bijectively onto `E^u`,
    carrying the pairing of `GramRho ⊗ GramQ` to that of `GramQ` exactly; the same holds for
    `θ` (`mulθ`) with a scalar `t > 1`, `t⁴ = t³ + 1`, the sector `ℝ³ ⊗ e₀` and `GramRho`; and
    `GramQ`, `GramRho` have types `(3, 1)`, `(2, 1)`.
11. `quartic_model_set` — for `CQ`, `(E^u, E^s)` is a scheme with `ℤ⁴ ∩ E = 0`; with `q′` the
    negative root of `x⁴ − x − 1`, the window `|Σ_j h_j q′^j| ≤ 1/2` is a segment, its model set
    is `{π_E γ : |Σ_j γ_j q′^j| ≤ 1/2}`, and `Q` maps it into itself; `det(Q|_E) = −1/q′`; the
    non-real eigenvalues have modulus squared `1/(Q|q′|) > 1`; and the form of `GramQ` has type
    `(2, 1)` on `E` and `(1, 0)` on `H`.
12. `salem_witness` — the companion matrix of `x⁴ − x³ − x² − x + 1` is not hyperbolic and has
    `d = 1`, attained only on the eigenline of its Salem root, which lies in `(1.7220, 1.7221)`.
13. `modelSet_isMeyer` — for every scheme and every window, `Λ(W)` is a Delone set in `E`
    (Mathlib's `Delone.DeloneSet`) and `Λ(W) − Λ(W)` is uniformly discrete.

**Attributions.** The mathematics of (1), (2), (4), (5), (6) and (13) is known in other
formulations, cited here; (1) and (4) are stated with no diagonalizability hypothesis. The necessity
half of (1) is Masáková–Mazáč–Pelantová (Linear Algebra Appl. 625 (2021) 279–321), Prop. 13.2 and
Cor. 13.4 in the numbering of arXiv:1909.10753v2, for diagonalizable maps and generic schemes. (2)
is Kronecker's density theorem; its cut-and-project form is Pleasants (2000), Cor. 2.12, and
Masáková–Mazáč–Pelantová, Prop. 3.3(iii). (4) is the hyperbolic case on a fixed lattice, with no
diagonalizability; for substitutional patterns with expansive inflation, Harriss–Koivusalo–Walton
(preprint, arXiv:2512.13659), Thm 3.3, show that the internal space is the contracting subspace. (5)
is the lattice-first, model-set form of Meyer's theorem (1972; 1995, Thm 6) that the inflation
factors of Meyer sets are the Pisot and Salem numbers; the Salem model set on `ℤ^s` is Solomyak
(2020), §4(iv), credited there to Akiyama, and (12) is an instance. The planes of (6) are those of
the classical planar cyclotomic model sets (Huck, arXiv:math/0701141, Def. 11; Baake–Grimm 2013,
§7.3), of internal dimension `φ(n) − 2`; `φ(n)`, the least lattice rank for a planar model set with
`n`-fold symmetry (Baake–Joseph–Schlottmann 1991), is the dual quantity. (13) is classical (Meyer
1972; Moody 1997). The scheme and model set of (11) are, in substance, instances of
Masáková–Mazáč–Pelantová, Thm 13.1, and of Harriss–Koivusalo–Walton, §3.4, and the translation set
of the Thurston dual tiling of the Pisot unit `−1/q′` is a model set of the same kind
(Kalle–Steiner, Trans. Amer. Math. Soc. 364 (2012), Lemma 4.3); none of this is claimed as new. For
squarefree `χ_A`, so for diagonalizable `A`, the count of (3) also follows from
Masáková–Mazáč–Pelantová, Lemma 5.1, Prop. 8.1(iii) and Cor. 13.4. We did not find the least
physical dimension for a given lattice map, statement (3), stated in the sources we read (search
completed 2026-10-20); this is a search result, not a guarantee. The master's thesis of J. Mazáč
(Czech Technical University in Prague, hdl 10467/82624), whose abstract treats minimal scheme
dimension for diagonalizable maps, physical map first, was not read: its full text is not public.

**The proofs.** No Jordan form and no diagonalization is used. Necessity in (3) comes from a
rational kernel lemma (for an irreducible rational factor `p` of `χ_A`, `ker p(A)` contains a
nonzero lattice vector) and from (1); sufficiency from (2), a Lagrange-interpolation power bound
on `H` and the orbit window of (1). The count in (3) is a root count over the rational factors of
`χ_A`, and its circle factors are identified by Mathlib's form of Kronecker's theorem
(`NumberField.Embeddings.pow_eq_one_of_norm_eq_one`). The rates in (4) come from Gelfand's
spectral radius formula. The signatures in (10) and (11) are computed by Sylvester's law of
inertia in Mathlib (D. Loeffler's `sigPos`, `sigNeg`). Statements (8)–(11) are about explicit
integer matrices. That `Cρ` and `CQ` are multiplication by `ρ` and `Q` in the power bases is
their definition (companion matrices). That `mulMatrix a` is multiplication by
`Σ a(i,j) ρ^i Q^j` on the ring of integers `ℤ[ρ] ⊗ ℤ[Q]` of `ℚ(ρ, Q)` in the basis `ρ^i Q^j`, and
that `GramRho ⊗ GramQ` is the Gram matrix of its trace form in that basis, are theorems of the
author's stalex444/pdt-hermite-signature-compositum at commit 5aa870e8 (statements (8) and (11)
there), cited and not compared here. The circle-freeness of `ℚ(ρ, Q)` (statement (17) there) is
ported to this repository (`InflationDimension/Compositum`) and used in (9). The author's
registered entry PALOMAR-2026-09-04-000004 shows (`quartic_record_obstruction`) that a window on
the real expanding place of `ℤ[Q]`, observed at the complex place, gives a set that is not
uniformly discrete. Statement (4) accounts for this: every admissible `Q`-invariant scheme on `ℤ⁴`
has `H ⊆ E^s`, the line of the contracting place `q′`, and (11) is that scheme.

**Definitions.** The entry's definitions are stated in this file, between the lines
`-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS`; that text is byte for byte the body
of `InflationDimension/Defs.lean`, on which the proof modules are built. This file imports Mathlib
only. The Mathlib definitions the statements use are quoted in `MATHLIB_DEFINITIONS.md`, and
`DefinitionAudit.lean` checks facts about them.

**Not formalized.** The least physical dimension when `χ_A` is not squarefree and has
eigenvalues on the unit circle; the least dimension under aperiodicity; and the regularity and
pure-point diffraction of the model sets (Hof 1995; Schlottmann 2000), which are cited only.

**Application (cited, not a claim of the entry).** In the author's Pisot Dimensional Theory,
`ℚ(ρ)` is the arithmetic of three-dimensional space and `ℚ(Q)` the arithmetic of
four-dimensional spacetime, and their compositum `K`, whose integers are `ℤ[ρ] ⊗ ℤ[Q]`, is the
parent of both (stalex444/pdt-hermite-signature-compositum@5aa870e8, statements (7), (8)). A
model set is the shadow of a lattice cut through a window, a standard mathematical model of a
quasicrystal (Moody 2000). Read through the theory, this entry's theorems fix how many dimensions
each of the theory's inflations needs to be the symmetry of one, and which ones.

Space inflates the parent through spacetime, and spacetime inflates it through space. On the
parent's lattice the plastic inflation `ρ` needs exactly four physical dimensions, and only one
scheme attains four (9). Those four are a copy of spacetime's: `ρ` has a single expanding embedding
in `ℚ(ρ)`, the real one, and the spectral projection maps the quartic sector onto them, carrying
`ℤ[Q]` with its trace form unchanged, of Lorentzian type `(3, 1)` (10). `ρ` acts on them as a pure
dilation by `ρ ≈ 1.3247`, the same stretch in every direction (10). Symmetrically, the unit
`θ = −Q⁻¹ = 1 − Q³` needs exactly three, and those three are a copy of space's: `ℚ(ρ)`'s real space
with its form of type `(2, 1)` unchanged, dilated by `θ₄ = −1/q′ ≈ 1.3803` (8, 9, 10). Taken over
all three embeddings of `ℚ(ρ)` instead of the one expanding embedding, the form on the quartic
sector is tripled: the factor 3 of the companion's statement (13).

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
all lie on the unit circle, `1` for a factor of degree one (`X - 1` or `X + 1`) and `2` for each
other one. -/
def circleCount (A : Matrix ι ι ℤ) : ℕ :=
  (((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).filter IsCircleFactor).map
    (fun p => min p.natDegree 2)).sum

end Spectrum

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

/-- **(3) The least physical dimension, `χ_A` squarefree over `ℚ`** (`det A ≠ 0`; eigenvalues on
the unit circle allowed). (a) Normal form: every `A`-invariant splitting `ℝ^ι = E ⊕ H` is
`E = ker q_E(A)`, `H = ker q_H(A)` with `χ_A = q_E q_H` over `ℝ`, where `q_E`, `q_H` are the
characteristic polynomials of `A|_E`, `A|_H`. (b) Characterization: the splitting carries an
admissible scheme if and only if every root of `q_H` lies in the closed unit disk and every
irreducible factor of `χ_A` over `ℚ` shares a complex root with `q_E`. (c) Count:
`d(A) = U(A) + circleCount A`, the second term counting `1` for each factor `x ± 1` and `2` for
each other irreducible factor with all roots on the unit circle; those factors are exactly the
cyclotomic ones (Kronecker). For diagonalizable `A` the count also follows from
Masáková–Mazáč–Pelantová (2021), Lemma 5.1, Prop. 8.1(iii) and Cor. 13.4. -/
theorem least_physical_dimension_squarefree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) (hsf : Squarefree (charpolyQ A)) :
    (∀ (E H : Submodule ℝ (ι → ℝ)), IsCompl E H → ∀ (hE : ∀ v ∈ E, act A v ∈ E)
        (hH : ∀ v ∈ H, act A v ∈ H),
      A.charpoly.map (Int.castRingHom ℝ) =
          ((act A).restrict hE).charpoly * ((act A).restrict hH).charpoly ∧
        E = LinearMap.ker (aeval (act A) ((act A).restrict hE).charpoly) ∧
        H = LinearMap.ker (aeval (act A) ((act A).restrict hH).charpoly) ∧
        ((∃ S : InvariantCPS A, S.E = E ∧ S.H = H ∧ S.Admissible) ↔
          (∀ z ∈ (((act A).restrict hH).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1) ∧
            ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
              ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots, aeval z ((act A).restrict hE).charpoly = 0)) ∧
    IsLeast (physDims A) (unstableCount A + circleCount A) ∧
    ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      IsCircleFactor p ↔ ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ := by
  sorry

/-- **(4) The hyperbolic case**, every `χ_A` (`det A ≠ 0`, no eigenvalue on the unit circle). An
`A`-invariant scheme is admissible if and only if `E ⊇ E^u(A)`, if and only if `H ⊆ E^s(A)`.
`(E^u, E^s)` carries an admissible scheme, `d(A) = U(A)`, and every admissible scheme with
`dim E = U(A)` is `(E^u, E^s)`. No diagonalizability is assumed. For diagonalizable maps and
generic schemes the necessity of `H ⊆ E^s` is Masáková–Mazáč–Pelantová (2021), Prop. 13.2 and
Cor. 13.4; the statement is the inclusion-notion analogue of the expansive case of
Harriss–Koivusalo–Walton (preprint, arXiv:2512.13659), Thm 3.3. -/
theorem hyperbolic_case {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hdet : A.det ≠ 0) (hhyp : IsHyperbolic A) :
    (∀ S : InvariantCPS A, (S.Admissible ↔ unstableSet A ⊆ (S.E : Set (ι → ℝ))) ∧
      (S.Admissible ↔ (S.H : Set (ι → ℝ)) ⊆ stableSet A)) ∧
    (∃ S : InvariantCPS A, (S.E : Set (ι → ℝ)) = unstableSet A ∧
      (S.H : Set (ι → ℝ)) = stableSet A ∧ S.Admissible) ∧
    IsLeast (physDims A) (unstableCount A) ∧
    ∀ S : InvariantCPS A, S.Admissible → finrank ℝ S.E = unstableCount A →
      (S.E : Set (ι → ℝ)) = unstableSet A ∧ (S.H : Set (ι → ℝ)) = stableSet A := by
  sorry

/-- **(5) Dimension one: Pisot or Salem** (`det A ≠ 0`, `χ_A` squarefree over `ℚ`). `d(A) = 1` if
and only if `χ_A` is irreducible over `ℚ` with exactly one root of modulus `> 1`, or `A = ±1` on
`ℤ¹`. In the irreducible case that root `r` is real, every other root has modulus at most `1`
(so `|r|` is a Pisot number, a Salem number, or for `#ι = 1` an integer `≥ 2`), and every
admissible scheme with `dim E = 1` has `E` the `r`-eigenline. This is the lattice-first,
model-set form of Meyer's theorem (1972; 1995, Thm 6): existence on the line and the model-set
case of necessity, for `A`-invariant schemes. The Salem case is the model set on `ℤ^s` of
Solomyak (2020), §4(iv), credited there to Akiyama. -/
theorem dimension_one_pisot_or_salem {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hdet : A.det ≠ 0) (hsf : Squarefree (charpolyQ A)) :
    (IsLeast (physDims A) 1 ↔
      (Irreducible (charpolyQ A) ∧ unstableCount A = 1) ∨
        (Fintype.card ι = 1 ∧ (A = 1 ∨ A = -1))) ∧
    (Irreducible (charpolyQ A) → unstableCount A = 1 →
      ∃ r : ℝ, 1 < |r| ∧ (r : ℂ) ∈ eigenvalues A ∧ (∀ z ∈ eigenvalues A, z ≠ r → ‖z‖ ≤ 1) ∧
        ∀ S : InvariantCPS A, S.Admissible → finrank ℝ S.E = 1 →
          S.E = LinearMap.ker (act A - r • LinearMap.id)) := by
  sorry

/-- **(6) Finite order: the cyclotomic case.** If `χ_A` is squarefree over `ℚ` with all roots on
the unit circle, every irreducible factor is cyclotomic and `d(A)` counts `1` for each factor
`Φ₁ = x − 1`, `Φ₂ = x + 1` and `2` for each `Φ_n`, `n ≥ 3`. In particular every integer matrix
with characteristic polynomial `Φ_n`, `n ≥ 3` (multiplication by `ζ_n` on `ℤ[ζ_n]`), has
`d = 2`: the physical plane of the classical planar cyclotomic model sets, whose internal
dimension is `φ(n) − 2`. -/
theorem finite_order_case {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) :
    (Squarefree (charpolyQ A) → (∀ z ∈ eigenvalues A, ‖z‖ = 1) →
      (∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
        ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ) ∧
      IsLeast (physDims A)
        (((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).map
          (fun p => min p.natDegree 2)).sum)) ∧
    ∀ n : ℕ, 3 ≤ n → A.charpoly = cyclotomic n ℤ → IsLeast (physDims A) 2 := by
  sorry

/-- **(7) The squarefree hypothesis of (3) is needed.** On `ℤ²`, `I₂` and the Jordan block
`J₂ = [[1, 1], [0, 1]]` both have `χ = (x − 1)²`, for which the count of (3) gives `2`; but
`d(I₂) = 1` and `d(J₂) = 2`. -/
theorem squarefree_hypothesis_needed :
    (1 : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    unstableCount (1 : Matrix (Fin 2) (Fin 2) ℤ) + circleCount (1 : Matrix (Fin 2) (Fin 2) ℤ) =
      2 ∧
    IsLeast (physDims (1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 ∧
    IsLeast (physDims (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) 2 := by
  sorry

/-- **(8) The sector rings.** On `ℤ[ρ]` (basis `1, ρ, ρ²`) and `ℤ[Q]` (basis `1, Q, Q², Q³`),
multiplication by `ρ`, `ρ⁻¹ = ρ² − 1`, `Q` and `θ = −Q⁻¹ = 1 − Q³` has the stated characteristic
polynomials, is hyperbolic, and needs exactly `1`, `2`, `3`, `1` physical dimensions; by (4) each
minimum is attained only by `(E^u, E^s)`. The one expanding eigenvalue of `θ` is real,
`θ₄ = −1/q′ ≈ 1.38028`, where `q′` is the negative real root of `x⁴ − x − 1`. -/
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
(`mulMatrix a`) is invertible and hyperbolic, so by (4) it needs exactly `U` physical
dimensions, attained only by `(E^u, E^s)`. For `ρ`, `θ`, `ρQ` and `Q` the values are `4`, `3`,
`5`, `9`. -/
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
