module
public import Mathlib

@[expose] public section
/-!
# The least physical dimension of an inflation-symmetric model set

Thirteen compared statements, (1)–(13) below. This opening account is a working draft; it is
rewritten in full before submission.

**Setting.** `ι` is a finite type, `ℤ^ι ⊂ ℝ^ι` is the integer lattice and an integer matrix `A`
acts on `ℝ^ι`. An `A`-invariant cut-and-project scheme (`InvariantCPS A`) is a splitting
`ℝ^ι = E ⊕ H` into `A`-invariant subspaces with `ℤ^ι ∩ H = 0` and `π_H(ℤ^ι)` dense in `H`. A
window is a bounded subset of `H` with nonempty interior in `H`, and the model set is
`Λ(W) = {π_E γ : γ ∈ ℤ^ι, π_H γ ∈ W}`. The scheme is admissible if some window gives
`A Λ(W) ⊆ Λ(W)`: inflation symmetry as inclusion, in Meyer's sense, linear and centred at the
origin. The least physical dimension `d(A)` is the least `dim E` over admissible schemes
(`IsLeast (physDims A) d`); the trivial scheme `(ℝ^ι, 0)` is admissible, so `d(A) ≤ #ι`.

**Scope.** The minimum is over `A`-invariant schemes on the fixed lattice `ℤ^ι`. Aperiodicity
(`ℤ^ι ∩ E = 0`) is not required and `H = 0` is admitted, so rational invariant directions may lie
in `E`; the minimum under aperiodicity is a different problem and is not treated. The value
belongs to the `ℚ`-module `(ℚ^ι, A)`, not to an eigenvalue: multiplication by `ρ` needs one
physical dimension on `ℤ[ρ]` and four on `ℤ[ρ] ⊗ ℤ[Q]`. The statements are about
inflation-symmetric model sets, not tilings.

**The statements.**
1. Admissibility criterion, every integer `A`.
2. Kronecker's density criterion, in cut-and-project form.
3. The least physical dimension when `χ_A` is squarefree over `ℚ` (Formula B).
4. The hyperbolic case, every `χ_A`.
5. Dimension one: Pisot or Salem.
6. Finite order (the cyclotomic case).
7. The squarefree hypothesis of (3) is needed.
8. The sector rings `ℤ[ρ]` and `ℤ[Q]`.
9. The degree-12 lattice `ℤ[ρ] ⊗ ℤ[Q]`.
10. The two dilations.
11. The three-dimensional model set of `Q`.
12. A Salem witness.
13. Model sets are Meyer sets.
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
`dim E = U(A)` is `(E^u, E^s)`. No diagonalizability is assumed. This contains the
fixed-lattice hyperbolic case of Masáková–Mazáč–Pelantová (2021), Thm 13.1, and is the
inclusion-notion analogue of Harriss–Koivusalo–Walton (preprint, arXiv:2512.13659), Thm 3.3. -/
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
set in `E` (Mathlib's `Delone.DeloneSet`) and `Λ(W) − Λ(W)` is uniformly discrete. -/
theorem modelSet_isMeyer {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (S : InvariantCPS A) (W : Set (ι → ℝ)) (hW : S.IsWindow W) :
    (∃ D : Delone.DeloneSet S.E, (D : Set S.E) = Subtype.val ⁻¹' S.modelSet W) ∧
    ∃ r > (0 : ℝ), ∀ x ∈ S.modelSet W - S.modelSet W, ∀ y ∈ S.modelSet W - S.modelSet W,
      x ≠ y → r ≤ dist x y := by
  sorry

end ModelSetDimension
