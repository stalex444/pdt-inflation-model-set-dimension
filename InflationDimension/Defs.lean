module
public import Mathlib

@[expose] public section
/-!
# Shared definitions

The definitions on which the compared statements rest. The block between the
`BEGIN`/`END SHARED DEFINITIONS` markers is copied byte for byte into `Challenge.lean`, so the
Challenge imports Mathlib only and elaborates the same declarations, under the same names, as the
proof modules, which are all built on this file.
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
