module
public import Mathlib
public import InflationDimension.Admissibility
public import InflationDimension.Count
public import InflationDimension.Hyperbolic
public import InflationDimension.DimOne
public import InflationDimension.Instances
public import InflationDimension.ModelSetQ
public import InflationDimension.Meyer

@[expose] public section
/-!
# Solution

The compared statements of `Challenge.lean`, stated identically (the same opens, namespace,
docstrings and statement text), each proved by one application of the theorem of the same name
in namespace `InflationDimension`. The definitions they use are those of
`InflationDimension.Defs`, whose text is the shared block of `Challenge.lean`.
-/

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
        unstableCount A ≤ finrank ℝ S.E) :=
  InflationDimension.admissibility_criterion A S

/-- **(2) Kronecker's density criterion**, in cut-and-project form: for complementary subspaces
`E`, `H` of `ℝ^ι`, the projection of `ℤ^ι` to `H` along `E` is dense in `H` if and only if every
real linear functional that is integer-valued on `ℤ^ι` and vanishes on `E` is zero. The
cut-and-project form is Pleasants (2000), Cor. 2.12, and Masáková–Mazáč–Pelantová (2021),
Prop. 3.3(iii). -/
theorem kronecker_density_criterion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E H : Submodule ℝ (ι → ℝ)) (hc : IsCompl E H) :
    (H : Set (ι → ℝ)) ⊆ closure (H.projection E hc.symm '' (intLattice ι : Set (ι → ℝ))) ↔
      ∀ f : (ι → ℝ) →ₗ[ℝ] ℝ, (∀ γ ∈ intLattice ι, ∃ n : ℤ, f γ = n) →
        (∀ v ∈ E, f v = 0) → f = 0 :=
  InflationDimension.kronecker_density_criterion E H hc

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
      IsCircleFactor p ↔ ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ :=
  InflationDimension.least_physical_dimension_squarefree A hdet hsf

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
      (S.E : Set (ι → ℝ)) = unstableSet A ∧ (S.H : Set (ι → ℝ)) = stableSet A :=
  InflationDimension.hyperbolic_case A hdet hhyp

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
          S.E = LinearMap.ker (act A - r • LinearMap.id)) :=
  InflationDimension.dimension_one_pisot_or_salem A hdet hsf

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
    ∀ n : ℕ, 3 ≤ n → A.charpoly = cyclotomic n ℤ → IsLeast (physDims A) 2 :=
  InflationDimension.finite_order_case A

/-- **(7) The squarefree hypothesis of (3) is needed.** On `ℤ²`, `I₂` and the Jordan block
`J₂ = [[1, 1], [0, 1]]` both have `χ = (x − 1)²`, for which the count of (3) gives `2`; but
`d(I₂) = 1` and `d(J₂) = 2`. -/
theorem squarefree_hypothesis_needed :
    (1 : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    unstableCount (1 : Matrix (Fin 2) (Fin 2) ℤ) + circleCount (1 : Matrix (Fin 2) (Fin 2) ℤ) =
      2 ∧
    IsLeast (physDims (1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 ∧
    IsLeast (physDims (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) 2 :=
  InflationDimension.squarefree_hypothesis_needed

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
      z.im = 0 ∧ (1.3802 : ℝ) < z.re ∧ z.re < 1.3803 :=
  InflationDimension.sector_rings

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
    IsLeast (physDims mulρQ) 5 ∧ IsLeast (physDims mulQ) 9 :=
  InflationDimension.compositum_lattice

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
    sigPos (formOf GramRho) = 2 ∧ sigNeg (formOf GramRho) = 1 :=
  InflationDimension.compositum_dilations

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
      sigNeg ((formOf GramQ).comp S.H.subtype) = 0 :=
  InflationDimension.quartic_model_set

/-- **(12) A Salem witness.** The companion matrix of `x⁴ − x³ − x² − x + 1`, whose expanding root
is the Salem number `≈ 1.7220838`, is not hyperbolic (two eigenvalues lie on the unit circle)
and has `d = 1`, attained only on the eigenline of that root. The model set is that of
Solomyak (2020), §4(iv), credited there to Akiyama. -/
theorem salem_witness :
    CSalem.charpoly = X ^ 4 - X ^ 3 - X ^ 2 - X + 1 ∧ ¬ IsHyperbolic CSalem ∧
    IsLeast (physDims CSalem) 1 ∧
    ∃ r : ℝ, (1.7220 : ℝ) < r ∧ r < 1.7221 ∧ (r : ℂ) ∈ eigenvalues CSalem ∧
      ∀ S : InvariantCPS CSalem, S.Admissible → finrank ℝ S.E = 1 →
        S.E = LinearMap.ker (act CSalem - r • LinearMap.id) :=
  InflationDimension.salem_witness

/-- **(13) Model sets are Meyer sets.** For every scheme and every window, `Λ(W)` is a Delone
set in `E` (Mathlib's `Delone.DeloneSet`) and `Λ(W) − Λ(W)` is uniformly discrete. This is
classical (Meyer 1972; Moody 1997). -/
theorem modelSet_isMeyer {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (S : InvariantCPS A) (W : Set (ι → ℝ)) (hW : S.IsWindow W) :
    (∃ D : Delone.DeloneSet S.E, (D : Set S.E) = Subtype.val ⁻¹' S.modelSet W) ∧
    ∃ r > (0 : ℝ), ∀ x ∈ S.modelSet W - S.modelSet W, ∀ y ∈ S.modelSet W - S.modelSet W,
      x ≠ y → r ≤ dist x y :=
  InflationDimension.modelSet_isMeyer A S W hW

end ModelSetDimension
