module
public import Mathlib
public import InflationDimension.Defs
public import InflationDimension.Admissibility

@[expose] public section
/-!
# The hyperbolic case

Let `A` be an integer matrix with `det A ≠ 0`. A factorization `χ_A = q · r` over `ℝ` into monic
factors, with every complex root of `q` outside the closed unit disk and every complex root of `r`
inside the open unit disk, gives the `A`-invariant splitting `ℝ^ι = ker r(A) ⊕ ker q(A)`, and

* `ker r(A)` is the stable set `E^s(A)` and `ker q(A)` is the unstable set `E^u(A)`;
* `dim ker q(A) = deg q = U(A)`.

When `A` has no eigenvalue on the unit circle such a factorization exists, and then an
`A`-invariant cut-and-project scheme on `ℤ^ι` is admissible if and only if `E ⊇ E^u(A)`, if and
only if `H ⊆ E^s(A)`; the scheme `(E^u, E^s)` is admissible, the least physical dimension is
`U(A)`, and `(E^u, E^s)` is the only admissible scheme with `dim E = U(A)`.

The uniform bounds for `Aⁿ` on `ker r(A)` and for `A⁻ⁿ` on `ker q(A)` come from Gelfand's spectral
radius formula, applied to the complexified matrix of the restriction. No diagonalizability is
used.

Main results, in the namespace `InflationDimension`: `hyperbolic_case` (statement (4)),
`unstableSet_eq_ker` (the spectral description, for any `A` with `det A ≠ 0`),
`exists_hyperbolic_factorization`, `exists_unstable_stable_submodules` and
`isLeast_physDims_of_isHyperbolic`. The supporting lemmas are in `InflationDimension.Hyperbolic`,
organised around the predicate `Hyperbolic.IsHypSplitting`.
-/

namespace InflationDimension

open Polynomial Filter Topology Module Metric

noncomputable section

namespace Hyperbolic

/-! ### Powers of a matrix whose eigenvalues lie in the open unit disk -/

open scoped NNReal ENNReal in
/-- In a complex Banach algebra, the powers of an element of spectral radius `< 1` tend to `0`
(Gelfand's formula). -/
theorem tendsto_pow_of_spectralRadius_lt_one {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
    [CompleteSpace B] (a : B) (h : spectralRadius ℂ a < 1) :
    Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  obtain ⟨r, hr1, hr⟩ : ∃ r : ℝ≥0, spectralRadius ℂ a < r ∧ (r : ℝ≥0∞) < 1 :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hr' : r < 1 := by exact_mod_cast hr
  have hev : ∀ᶠ n : ℕ in atTop, (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) < r :=
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a).eventually
      (gt_mem_nhds hr1)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hr')
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hn' : (‖a ^ n‖₊ : ℝ≥0∞) < (r : ℝ≥0∞) ^ n := by
    have h1 : ((‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) ^ (n : ℝ) < (r : ℝ≥0∞) ^ (n : ℝ) :=
      ENNReal.rpow_lt_rpow hn (by positivity)
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by exact_mod_cast hn0.ne'),
      ENNReal.rpow_one, ENNReal.rpow_natCast] at h1
  have : ‖a ^ n‖₊ < r ^ n := by exact_mod_cast hn'
  exact_mod_cast this.le

/-- Entrywise form for a complex matrix whose characteristic roots lie in the open unit disk. -/
theorem tendsto_pow_entry_of_roots_lt_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℂ) (h : ∀ z ∈ M.charpoly.roots, ‖z‖ < 1) (i j : κ) :
    Tendsto (fun n : ℕ => (M ^ n) i j) atTop (𝓝 0) := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix κ κ ℂ) := FiniteDimensional.complete ℂ _
  have hspec : spectralRadius ℂ M < 1 := by
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · have : Subsingleton (Matrix κ κ ℂ) := inferInstance
      simp [spectralRadius]
    · obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius M
      rw [← hzr]
      have hz' : z ∈ M.charpoly.roots := by
        rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hz
        exact (mem_roots (Matrix.charpoly_monic M).ne_zero).mpr hz
      have := h z hz'
      exact_mod_cast (show ‖z‖₊ < 1 from by exact_mod_cast this)
  have hC := tendsto_pow_of_spectralRadius_lt_one M hspec
  let ev : Matrix κ κ ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun A => A i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hcont : Continuous ev := LinearMap.continuous_of_finiteDimensional ev
  have := (hcont.tendsto 0).comp hC
  simp only [map_zero] at this
  exact this

/-- A real matrix whose complex characteristic roots lie in the open unit disk has powers
tending to `0`. -/
theorem tendsto_pow_of_charpoly_roots_lt_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℝ) (h : ∀ z : ℂ, aeval z M.charpoly = 0 → ‖z‖ < 1) :
    Tendsto (fun n : ℕ => M ^ n) atTop (𝓝 0) := by
  set MC : Matrix κ κ ℂ := M.map (algebraMap ℝ ℂ)
  have hMC : MC.charpoly = M.charpoly.map (algebraMap ℝ ℂ) := Matrix.charpoly_map M _
  have hroots : ∀ z ∈ MC.charpoly.roots, ‖z‖ < 1 := by
    intro z hz
    apply h
    have := (mem_roots'.mp hz).2
    rwa [hMC, IsRoot, eval_map_algebraMap] at this
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  have hE := tendsto_pow_entry_of_roots_lt_one MC hroots i j
  have hpow : ∀ n : ℕ, (MC ^ n) i j = ((M ^ n) i j : ℂ) := fun n => by
    have := congrArg (fun A : Matrix κ κ ℂ => A i j) (map_pow (algebraMap ℝ ℂ).mapMatrix M n)
    simpa [RingHom.mapMatrix_apply, MC] using this.symm
  simp_rw [hpow] at hE
  have := (Complex.continuous_re.tendsto 0).comp hE
  simpa [Function.comp_def] using this

/-! ### Endomorphisms of a finite-dimensional real space -/

section Endo

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem aeval_restrict_apply (f : Module.End ℝ V) {U : Submodule ℝ V} (hU : ∀ v ∈ U, f v ∈ U)
    (p : ℝ[X]) (v : U) : ((aeval (f.restrict hU) p) v : V) = aeval f p (v : V) := by
  induction p using Polynomial.induction_on generalizing v with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    have e1 : (C a * X ^ (n + 1) : ℝ[X]) = C a * X ^ n * X := by ring
    rw [e1, map_mul (aeval (f.restrict hU)) (C a * X ^ n) X, map_mul (aeval f) (C a * X ^ n) X,
      aeval_X, aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

omit [FiniteDimensional ℝ V] in
theorem mapsTo_ker_aeval (f : Module.End ℝ V) (q : ℝ[X]) :
    ∀ v ∈ LinearMap.ker (aeval f q), f v ∈ LinearMap.ker (aeval f q) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have h1 : aeval f (q * X) = aeval f (X * q) := by rw [mul_comm]
  rw [map_mul, map_mul, aeval_X] at h1
  have := congrArg (fun T : Module.End ℝ V => T v) h1
  simp only [Module.End.mul_apply] at this
  rw [this, hv, map_zero]

omit [FiniteDimensional ℝ V] in
theorem aeval_restrict_ker_eq_zero (f : Module.End ℝ V) (q : ℝ[X]) :
    aeval (f.restrict (mapsTo_ker_aeval f q)) q = 0 := by
  ext v
  simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero]
  rw [aeval_restrict_apply]
  exact v.2

/-- Every complex root of `χ_h` is a root of any polynomial annihilating `h`. -/
theorem aeval_eq_zero_of_charpoly_root {U : Type*} [AddCommGroup U] [Module ℝ U]
    [FiniteDimensional ℝ U] (h : Module.End ℝ U) {p : ℝ[X]} (hp : aeval h p = 0) (z : ℂ)
    (hz : aeval z h.charpoly = 0) : aeval z p = 0 := by
  classical
  set b := Module.finBasis ℝ U
  set M := LinearMap.toMatrix b b h with hM
  set MC : Matrix (Fin (finrank ℝ U)) (Fin (finrank ℝ U)) ℂ := M.map (algebraMap ℝ ℂ) with hMC
  have hroot : IsRoot MC.charpoly z := by
    rw [hMC, Matrix.charpoly_map, hM, LinearMap.charpoly_toMatrix, IsRoot, eval_map_algebraMap]
    exact hz
  have hspec : z ∈ spectrum ℂ (Matrix.toLin' MC) := by
    rw [Matrix.spectrum_toLin']
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  obtain ⟨w, hw⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hspec).exists_hasEigenvector
  have hMp : aeval M p = 0 := by
    have hM' : LinearMap.toMatrixAlgEquiv b h = M := by
      ext i j
      rw [LinearMap.toMatrixAlgEquiv_apply, hM, LinearMap.toMatrix_apply]
    rw [← hM']
    have := aeval_algHom_apply ((LinearMap.toMatrixAlgEquiv b).toAlgHom) h p
    erw [this, hp, map_zero]
  have hMCp : aeval MC (p.map (algebraMap ℝ ℂ)) = 0 := by
    rw [aeval_map_algebraMap]
    have h2 : MC = (Algebra.ofId ℝ ℂ).mapMatrix M := rfl
    rw [h2, aeval_algHom_apply, hMp, map_zero]
  have hlin : aeval (Matrix.toLin' MC) (p.map (algebraMap ℝ ℂ)) = 0 := by
    have := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ)
      (n := Fin (finrank ℝ U))).toAlgHom MC (p.map (algebraMap ℝ ℂ))
    have e : Matrix.toLinAlgEquiv' MC = Matrix.toLin' MC := rfl
    erw [e] at this
    erw [this, hMCp, map_zero]
  have hev := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap ℝ ℂ)) hw
  rw [hlin, LinearMap.zero_apply] at hev
  have hne : w ≠ 0 := hw.2
  have : (p.map (algebraMap ℝ ℂ)).eval z = 0 := by
    by_contra hc
    exact hne (smul_eq_zero.mp hev.symm |>.resolve_left hc)
  rwa [eval_map_algebraMap] at this

/-- `χ_f = q · r` with `q`, `r` monic and coprime: `ker q(f) ⊕ ker r(f)` is a splitting and
`dim ker q(f) = deg q`. -/
theorem finrank_ker_aeval_of_coprime (f : Module.End ℝ V) {q r : ℝ[X]} (hq : q.Monic)
    (hr : r.Monic) (hχ : f.charpoly = q * r) (hcop : IsCoprime q r) :
    IsCompl (LinearMap.ker (aeval f q)) (LinearMap.ker (aeval f r)) ∧
      finrank ℝ (LinearMap.ker (aeval f q)) = q.natDegree := by
  set U := LinearMap.ker (aeval f q) with hUdef
  set W := LinearMap.ker (aeval f r) with hWdef
  have hU := mapsTo_ker_aeval f q
  have hW := mapsTo_ker_aeval f r
  have hcompl : IsCompl U W := by
    refine ⟨Polynomial.disjoint_ker_aeval_of_isCoprime f hcop, ?_⟩
    rw [codisjoint_iff, hUdef, hWdef, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop,
      ← hχ, LinearMap.aeval_self_charpoly, LinearMap.ker_zero]
  refine ⟨hcompl, ?_⟩
  set g₁ := (f.restrict hU).charpoly with hg₁
  set g₂ := (f.restrict hW).charpoly with hg₂
  have hsplit : f.charpoly = g₁ * g₂ :=
    PowerBounded.charpoly_eq_mul_of_isCompl f U W hcompl hU hW
  have hq0 : aeval (f.restrict hU) q = 0 := aeval_restrict_ker_eq_zero f q
  have hr0 : aeval (f.restrict hW) r = 0 := aeval_restrict_ker_eq_zero f r
  have hcopC := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ q r).mp hcop
  have hc₁ : IsCoprime g₁ r := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ]
    intro a
    by_cases ha : aeval a g₁ = 0
    · right
      have := aeval_eq_zero_of_charpoly_root _ hq0 a ha
      exact (hcopC a).resolve_left (not_not.mpr this)
    · left; exact ha
  have hc₂ : IsCoprime g₂ q := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ]
    intro a
    by_cases ha : aeval a g₂ = 0
    · right
      have := aeval_eq_zero_of_charpoly_root _ hr0 a ha
      exact fun hqa => ((hcopC a).resolve_left (not_not.mpr hqa)) this
    · left; exact ha
  have hd₁ : g₁ ∣ q := by
    have : g₁ ∣ q * r := by rw [← hχ, hsplit]; exact dvd_mul_right _ _
    exact hc₁.dvd_of_dvd_mul_right this
  have hd₂ : g₂ ∣ r := by
    have : g₂ ∣ r * q := by rw [mul_comm, ← hχ, hsplit]; exact dvd_mul_left _ _
    exact hc₂.dvd_of_dvd_mul_right this
  have hle₁ := Polynomial.natDegree_le_of_dvd hd₁ hq.ne_zero
  have hle₂ := Polynomial.natDegree_le_of_dvd hd₂ hr.ne_zero
  have hsum : g₁.natDegree + g₂.natDegree = q.natDegree + r.natDegree := by
    rw [← (LinearMap.charpoly_monic _).natDegree_mul (LinearMap.charpoly_monic _), ← hsplit, hχ,
      hq.natDegree_mul hr]
  rw [← LinearMap.charpoly_natDegree (f.restrict hU), ← hg₁]
  omega

end Endo

section Normed

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

/-- An endomorphism whose complex characteristic roots lie in the open unit disk has
`‖fⁿ x‖ ≤ c n ‖x‖` with `c n → 0`. -/
theorem exists_bound_tendsto_zero (f : Module.End ℝ U)
    (h : ∀ z : ℂ, aeval z f.charpoly = 0 → ‖z‖ < 1) :
    ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧ (∀ n, 0 ≤ c n) ∧
      ∀ n : ℕ, ∀ x : U, ‖(f ^ n) x‖ ≤ c n * ‖x‖ := by
  classical
  set b := Module.finBasis ℝ U
  set M := LinearMap.toMatrixAlgEquiv b f with hMdef
  have hMc : M = LinearMap.toMatrix b b f := by
    ext i j
    rw [hMdef, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hM : M.charpoly = f.charpoly := by rw [hMc, LinearMap.charpoly_toMatrix]
  have hMt := tendsto_pow_of_charpoly_roots_lt_one M (by rw [hM]; exact h)
  let Φ : Matrix (Fin (finrank ℝ U)) (Fin (finrank ℝ U)) ℝ →ₗ[ℝ] (U →L[ℝ] U) :=
    (LinearMap.toContinuousLinearMap : (U →ₗ[ℝ] U) ≃ₗ[ℝ] (U →L[ℝ] U)).toLinearMap ∘ₗ
      (Matrix.toLinAlgEquiv b).toLinearMap
  have hΦ : Continuous Φ := LinearMap.continuous_of_finiteDimensional Φ
  have hpow : ∀ n : ℕ, ∀ x : U, (f ^ n) x = Φ (M ^ n) x := by
    intro n x
    have : Matrix.toLinAlgEquiv b (M ^ n) = f ^ n := by
      rw [map_pow, hMdef, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
    simp [Φ, this]
  refine ⟨fun n => ‖Φ (M ^ n)‖, ?_, fun n => norm_nonneg _, fun n x => ?_⟩
  · have h1 := (hΦ.tendsto 0).comp hMt
    simpa using h1.norm
  · rw [hpow]
    exact (Φ (M ^ n)).le_opNorm x

/-- If `f g = g f = 1`, a complex characteristic root `z` of `g` is nonzero and `z⁻¹` is a
characteristic root of `f`. -/
theorem charpoly_root_inv (f g : Module.End ℝ U) (hfg : f * g = 1) (hgf : g * f = 1) {z : ℂ}
    (hz : aeval z g.charpoly = 0) : z ≠ 0 ∧ aeval z⁻¹ f.charpoly = 0 := by
  classical
  set b := Module.finBasis ℝ U
  let φ : Module.End ℝ U →ₐ[ℝ] Matrix (Fin (finrank ℝ U)) (Fin (finrank ℝ U)) ℂ :=
    (Algebra.ofId ℝ ℂ).mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toAlgHom
  have hcp : ∀ k : Module.End ℝ U, ∀ w : ℂ, w ∈ spectrum ℂ (φ k) ↔ aeval w k.charpoly = 0 := by
    intro k w
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    have e1 : φ k = (LinearMap.toMatrix b b k).map (algebraMap ℝ ℂ) := by
      ext i j
      simp [φ, AlgHom.mapMatrix_apply, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    rw [e1, Matrix.charpoly_map, LinearMap.charpoly_toMatrix, IsRoot, eval_map_algebraMap]
  let u : (Matrix (Fin (finrank ℝ U)) (Fin (finrank ℝ U)) ℂ)ˣ :=
    ⟨φ f, φ g, by rw [← map_mul, hfg, map_one], by rw [← map_mul, hgf, map_one]⟩
  have hzg : z ∈ spectrum ℂ ((u⁻¹ : (Matrix (Fin (finrank ℝ U)) (Fin (finrank ℝ U)) ℂ)ˣ) :
      Matrix (Fin (finrank ℝ U)) (Fin (finrank ℝ U)) ℂ) := (hcp g z).mpr hz
  rw [← spectrum.map_inv, Set.mem_inv] at hzg
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [inv_zero] at hzg
    exact (spectrum.zero_mem_iff ℂ).mp hzg u.isUnit
  exact ⟨hz0, (hcp f z⁻¹).mp hzg⟩

end Normed

/-! ### The spectral splitting of an integer matrix -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_charpoly_complex (A : Matrix ι ι ℤ) :
    (A.charpoly.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ) =
      A.charpoly.map (Int.castRingHom ℂ) := by
  rw [Polynomial.map_map]
  congr 1

theorem act_injective (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) : Function.Injective (act A) := by
  have h1 : (A.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    have e : (A.map (Int.cast : ℤ → ℝ)).det = ((A.det : ℤ) : ℝ) := by
      rw [show A.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix A from rfl,
        ← RingHom.map_det]
      simp
    rw [e]
    exact_mod_cast hdet
  have h2 : IsUnit (A.map (Int.cast : ℤ → ℝ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h1)
  have h3 : Function.Injective (A.map (Int.cast : ℤ → ℝ)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr h2
  intro x y hxy
  apply h3
  simpa [act, Matrix.toLin'_apply] using hxy

theorem aeval_eq_zero_of_mem_roots {g : ℝ[X]} {z : ℂ} (hz : z ∈ (g.map (algebraMap ℝ ℂ)).roots) :
    aeval z g = 0 := by
  have := (mem_roots'.mp hz).2
  rwa [IsRoot, eval_map_algebraMap] at this

theorem mem_roots_of_aeval_eq_zero {g : ℝ[X]} (hg0 : g ≠ 0) {z : ℂ} (hz : aeval z g = 0) :
    z ∈ (g.map (algebraMap ℝ ℂ)).roots := by
  rw [mem_roots', IsRoot, eval_map_algebraMap]
  exact ⟨(Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hg0, hz⟩

/-- The complex roots of an irreducible real polynomial all have the same modulus. -/
theorem norm_eq_of_irreducible {g : ℝ[X]} (hg : Irreducible g) {z w : ℂ}
    (hz : z ∈ (g.map (algebraMap ℝ ℂ)).roots) (hw : w ∈ (g.map (algebraMap ℝ ℂ)).roots) :
    ‖z‖ = ‖w‖ := by
  classical
  have hg0 : g ≠ 0 := hg.ne_zero
  have hcard : Multiset.card (g.map (algebraMap ℝ ℂ)).roots ≤ g.natDegree := by
    simpa [natDegree_map] using card_roots' (g.map (algebraMap ℝ ℂ))
  have hdeg := hg.natDegree_le_two
  have hzroot := aeval_eq_zero_of_mem_roots hz
  by_cases h1 : g.natDegree ≤ 1
  · have hc1 : Multiset.card (g.map (algebraMap ℝ ℂ)).roots ≤ 1 := hcard.trans h1
    by_contra hn
    have hzw : z ≠ w := fun e => hn (by rw [e])
    have hsub : ({z, w} : Finset ℂ) ⊆ (g.map (algebraMap ℝ ℂ)).roots.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Multiset.mem_toFinset]
      rcases hx with rfl | rfl
      exacts [hz, hw]
    have := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
    rw [Finset.card_pair hzw] at this
    omega
  · have h2 : g.natDegree = 2 := by omega
    have him : z.im ≠ 0 := by
      intro him
      have hzr : z = algebraMap ℝ ℂ z.re := Complex.ext (by simp) (by simp [him])
      have hroot : IsRoot g z.re := by
        rw [hzr, aeval_algebraMap_apply, coe_aeval_eq_eval,
          map_eq_zero_iff _ (algebraMap ℝ ℂ).injective] at hzroot
        exact hzroot
      have := degree_eq_one_of_irreducible_of_root hg hroot
      rw [degree_eq_natDegree hg0, h2] at this
      norm_num at this
    have hc : (starRingEnd ℂ) z ∈ (g.map (algebraMap ℝ ℂ)).roots :=
      mem_roots_of_aeval_eq_zero hg0 (by rw [aeval_conj, hzroot, map_zero])
    have hne : z ≠ (starRingEnd ℂ) z := fun h => him (Complex.conj_eq_iff_im.mp h.symm)
    by_contra hzw
    have hw1 : w ≠ z := fun h => hzw (by rw [h])
    have hw2 : w ≠ (starRingEnd ℂ) z := fun h => hzw (by rw [h, Complex.norm_conj])
    have hsub : ({z, (starRingEnd ℂ) z, w} : Finset ℂ) ⊆
        (g.map (algebraMap ℝ ℂ)).roots.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Multiset.mem_toFinset]
      rcases hx with rfl | rfl | rfl
      exacts [hz, hc, hw]
    have h3 : ({z, (starRingEnd ℂ) z, w} : Finset ℂ).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hw2.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne, hw1.symm⟩
    have := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
    omega

/-- A monic real polynomial with no complex root on the unit circle is `p · q` with `p`, `q`
monic, every root of `p` inside and every root of `q` outside the unit circle. -/
theorem exists_factor_inside_outside (f : ℝ[X]) (hf : f.Monic)
    (hhyp : ∀ z ∈ (f.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≠ 1) :
    ∃ p q : ℝ[X], p.Monic ∧ q.Monic ∧ f = p * q ∧
      (∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, ‖z‖ < 1) ∧
      (∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, 1 < ‖z‖) := by
  classical
  set F := UniqueFactorizationMonoid.normalizedFactors f
  let inside : ℝ[X] → Prop := fun g => ∀ z ∈ (g.map (algebraMap ℝ ℂ)).roots, ‖z‖ < 1
  have hirr : ∀ g ∈ F, Irreducible g := fun g hg =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg
  have hmon : ∀ g ∈ F, g.Monic := fun g hg => by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor g hg]
    exact Polynomial.monic_normalize (hirr g hg).ne_zero
  have hFmon : ∀ s ≤ F, s.prod.Monic := fun s hs => by
    simpa using Polynomial.monic_multiset_prod_of_monic s id
      (fun g hg => hmon g (Multiset.mem_of_le hs hg))
  set p := (F.filter inside).prod
  set q := (F.filter (fun g => ¬ inside g)).prod
  have hp : p.Monic := hFmon _ (Multiset.filter_le _ _)
  have hq : q.Monic := hFmon _ (Multiset.filter_le _ _)
  have hfpq : f = p * q := by
    rw [Multiset.prod_filter_mul_prod_filter_not]
    exact (Polynomial.eq_of_monic_of_associated (hFmon F le_rfl) hf
      (UniqueFactorizationMonoid.prod_normalizedFactors hf.ne_zero)).symm
  have hfactor : ∀ s ≤ F, ∀ z ∈ (s.prod.map (algebraMap ℝ ℂ)).roots,
      ∃ g ∈ s, z ∈ (g.map (algebraMap ℝ ℂ)).roots := by
    intro s hs z hz
    have h0 := aeval_eq_zero_of_mem_roots hz
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at h0
    obtain ⟨g, hg, hgz⟩ := h0
    exact ⟨g, hg, mem_roots_of_aeval_eq_zero (hirr g (Multiset.mem_of_le hs hg)).ne_zero hgz⟩
  refine ⟨p, q, hp, hq, hfpq, ?_, ?_⟩
  · intro z hz
    obtain ⟨g, hg, hzg⟩ := hfactor _ (Multiset.filter_le _ _) z hz
    exact (Multiset.mem_filter.mp hg).2 z hzg
  · intro z hz
    obtain ⟨g, hg, hzg⟩ := hfactor _ (Multiset.filter_le _ _) z hz
    have hgF := (Multiset.mem_filter.mp hg)
    have hnot : ¬ inside g := hgF.2
    simp only [inside, not_forall, not_lt] at hnot
    obtain ⟨w, hw, hw1⟩ := hnot
    have heq := norm_eq_of_irreducible (hirr g hgF.1) hzg hw
    have hne : p.map (algebraMap ℝ ℂ) * q.map (algebraMap ℝ ℂ) ≠ 0 := by
      rw [← Polynomial.map_mul]
      exact (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr (hp.mul hq).ne_zero
    have hzf : z ∈ (f.map (algebraMap ℝ ℂ)).roots := by
      rw [hfpq, Polynomial.map_mul, roots_mul hne, Multiset.mem_add]
      exact Or.inr hz
    exact lt_of_le_of_ne (heq ▸ hw1) (hhyp z hzf).symm

/-- `U(A) = deg q` for a factorization `χ_A = q · r` with the roots of `q` outside and the roots
of `r` inside the unit circle. -/
theorem unstableCount_eq_natDegree (A : Matrix ι ι ℤ) (q r : ℝ[X]) (hq : q.Monic) (hr : r.Monic)
    (hχ : A.charpoly.map (Int.castRingHom ℝ) = q * r)
    (hqroots : ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, 1 < ‖z‖)
    (hrroots : ∀ z ∈ (r.map (algebraMap ℝ ℂ)).roots, ‖z‖ < 1) :
    unstableCount A = q.natDegree := by
  have he : eigenvalues A = (q.map (algebraMap ℝ ℂ)).roots + (r.map (algebraMap ℝ ℂ)).roots := by
    rw [eigenvalues, ← map_charpoly_complex, hχ, Polynomial.map_mul, roots_mul]
    exact ((hq.map _).mul (hr.map _)).ne_zero
  rw [unstableCount, he, Multiset.filter_add, Multiset.card_add,
    Multiset.filter_eq_self.mpr (fun z hz => hqroots z hz),
    Multiset.filter_eq_nil.mpr (fun z hz => not_lt.mpr (hrroots z hz).le), Multiset.card_zero,
    add_zero]
  exact IsAlgClosed.card_roots_map_eq_natDegree_of_injective q (algebraMap ℝ ℂ).injective

/-- A hyperbolic splitting `ℝ^ι = V_s ⊕ V_u` for `A`: complementary `A`-invariant subspaces with
`‖Aⁿ x‖ ≤ c n ‖x‖` on `V_s` and `‖x‖ ≤ c n ‖Aⁿ x‖` on `V_u` for sequences `c n → 0`, every vector
of `V_u` having a backward orbit tending to `0`. -/
structure IsHypSplitting (A : Matrix ι ι ℤ) (Vs Vu : Submodule ℝ (ι → ℝ)) : Prop where
  compl : IsCompl Vs Vu
  mapsTo_s : ∀ x ∈ Vs, act A x ∈ Vs
  mapsTo_u : ∀ x ∈ Vu, act A x ∈ Vu
  contr : ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧ (∀ n, 0 ≤ c n) ∧
    ∀ n : ℕ, ∀ x ∈ Vs, ‖(act A ^ n) x‖ ≤ c n * ‖x‖
  exp : ∃ c : ℕ → ℝ, Tendsto c atTop (𝓝 0) ∧ (∀ n, 0 ≤ c n) ∧
    ∀ n : ℕ, ∀ x ∈ Vu, ‖x‖ ≤ c n * ‖(act A ^ n) x‖
  back : ∀ x ∈ Vu, x ∈ unstableSet A

/-- **The spectral splitting.** For `det A ≠ 0` and `χ_A = q · r` with the roots of `q` outside
and those of `r` inside the unit circle, `(ker r(A), ker q(A))` is a hyperbolic splitting and
`dim ker q(A) = deg q`. -/
theorem isHypSplitting_ker (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) (q r : ℝ[X]) (hq : q.Monic)
    (hr : r.Monic) (hχ : A.charpoly.map (Int.castRingHom ℝ) = q * r)
    (hqroots : ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, 1 < ‖z‖)
    (hrroots : ∀ z ∈ (r.map (algebraMap ℝ ℂ)).roots, ‖z‖ < 1) :
    IsHypSplitting A (LinearMap.ker (aeval (act A) r)) (LinearMap.ker (aeval (act A) q)) ∧
      finrank ℝ (LinearMap.ker (aeval (act A) q)) = q.natDegree := by
  set T := act A with hTdef
  have hcop : IsCoprime q r := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ]
    intro a
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    have h1 := hqroots a (mem_roots_of_aeval_eq_zero hq.ne_zero hcon.1)
    have h2 := hrroots a (mem_roots_of_aeval_eq_zero hr.ne_zero hcon.2)
    linarith
  have hTχ : T.charpoly = q * r := by rw [hTdef, charpoly_act, hχ]
  obtain ⟨hcompl, hdim⟩ := finrank_ker_aeval_of_coprime T hq hr hTχ hcop
  set Vu := LinearMap.ker (aeval T q) with hVu
  set Vs := LinearMap.ker (aeval T r) with hVs
  have hu : ∀ x ∈ Vu, T x ∈ Vu := mapsTo_ker_aeval T q
  have hs : ∀ x ∈ Vs, T x ∈ Vs := mapsTo_ker_aeval T r
  have hTinj : Function.Injective T := act_injective A hdet
  -- contraction on `V_s`
  let fs : Module.End ℝ Vs := T.restrict hs
  have hfs : ∀ z : ℂ, aeval z fs.charpoly = 0 → ‖z‖ < 1 := fun z hz =>
    hrroots z (mem_roots_of_aeval_eq_zero hr.ne_zero
      (aeval_eq_zero_of_charpoly_root fs (aeval_restrict_ker_eq_zero T r) z hz))
  obtain ⟨cs, hcs, hcs0, hcsb⟩ := exists_bound_tendsto_zero fs hfs
  have hpow_s : ∀ n : ℕ, ∀ x : Vs, (((fs ^ n) x : Vs) : ι → ℝ) = (T ^ n) x := by
    intro n x
    rw [Module.End.pow_restrict]
    rfl
  -- the inverse on `V_u`
  let fu : Module.End ℝ Vu := T.restrict hu
  have hfu_inj : Function.Injective fu := by
    intro a b hab
    apply Subtype.ext
    apply hTinj
    exact congrArg Subtype.val hab
  let g : Module.End ℝ Vu := ((LinearEquiv.ofInjectiveEndo fu hfu_inj).symm : Vu →ₗ[ℝ] Vu)
  have hfg : fu * g = 1 := LinearEquiv.ofInjectiveEndo_right_inv fu hfu_inj
  have hgf : g * fu = 1 := LinearEquiv.ofInjectiveEndo_left_inv fu hfu_inj
  have hg : ∀ z : ℂ, aeval z g.charpoly = 0 → ‖z‖ < 1 := by
    intro z hz
    obtain ⟨hz0, hzi⟩ := charpoly_root_inv fu g hfg hgf hz
    have h1 := hqroots z⁻¹ (mem_roots_of_aeval_eq_zero hq.ne_zero
      (aeval_eq_zero_of_charpoly_root fu (aeval_restrict_ker_eq_zero T q) z⁻¹ hzi))
    rw [norm_inv] at h1
    exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mp h1
  obtain ⟨cu, hcu, hcu0, hcub⟩ := exists_bound_tendsto_zero g hg
  have hpow_u : ∀ n : ℕ, ∀ x : Vu, (((fu ^ n) x : Vu) : ι → ℝ) = (T ^ n) x := by
    intro n x
    rw [Module.End.pow_restrict]
    rfl
  have hgf_pow : ∀ n : ℕ, g ^ n * fu ^ n = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc g, hgf, one_mul, ih]
  have hfg_pow : ∀ n : ℕ, fu ^ n * g ^ n = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc fu, hfg, one_mul, ih]
  refine ⟨⟨hcompl.symm, hs, hu, ⟨cs, hcs, hcs0, fun n x hx => ?_⟩,
    ⟨cu, hcu, hcu0, fun n x hx => ?_⟩, fun x hx => ?_⟩, hdim⟩
  · have := hcsb n ⟨x, hx⟩
    simp only [← Submodule.norm_coe, hpow_s] at this
    exact this
  · set y : Vu := ⟨x, hx⟩
    have hy : y = (g ^ n) ((fu ^ n) y) := by
      rw [← Module.End.mul_apply, hgf_pow, Module.End.one_apply]
    have := hcub n ((fu ^ n) y)
    rw [← hy] at this
    simp only [← Submodule.norm_coe, hpow_u] at this
    exact this
  · set y : Vu := ⟨x, hx⟩
    refine ⟨fun n => (((g ^ n) y : Vu) : ι → ℝ), by simp [y], fun n => ?_, ?_⟩
    · have e : T (((g ^ (n + 1)) y : Vu) : ι → ℝ) = ((fu ((g ^ (n + 1)) y) : Vu) : ι → ℝ) := rfl
      rw [e, pow_succ', ← Module.End.mul_apply, ← mul_assoc, hfg, one_mul]
    · refine squeeze_zero_norm (fun n => ?_) (by simpa using hcu.mul_const ‖y‖)
      simp only [Submodule.norm_coe]
      exact hcub n y

theorem tendsto_bound {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n, c n ≤ K := by
  obtain ⟨K, hK⟩ := (Metric.isBounded_range_of_tendsto c hc).exists_norm_le
  refine ⟨max K 0, le_max_right _ _, fun n => ?_⟩
  have := hK (c n) ⟨n, rfl⟩
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

omit [Fintype ι] [DecidableEq ι] in
theorem pow_mapsTo_set (T : Module.End ℝ (ι → ℝ)) {P : Set (ι → ℝ)} (hP : ∀ x ∈ P, T x ∈ P) :
    ∀ n : ℕ, ∀ x ∈ P, (T ^ n) x ∈ P := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ', Module.End.mul_apply]
    exact hP _ (ih x hx)

omit [Fintype ι] [DecidableEq ι] in
/-- Projections along an invariant splitting commute with the map. -/
theorem projection_comm {T : Module.End ℝ (ι → ℝ)} {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H)
    (hTE : ∀ x ∈ E, T x ∈ E) (hTH : ∀ x ∈ H, T x ∈ H) (v : ι → ℝ) :
    E.projection H hc (T v) = T (E.projection H hc v) := by
  have hv := Submodule.projection_add_projection_eq_self hc v
  conv_lhs => rw [← hv]
  rw [map_add, map_add]
  rw [Submodule.projection_apply_of_mem_left hc (hTE _ (Submodule.projection_apply_mem hc v))]
  rw [Submodule.projection_apply_of_mem_right hc
    (hTH _ (Submodule.projection_apply_mem hc.symm v)), add_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem projection_pow_comm {T : Module.End ℝ (ι → ℝ)} {E H : Submodule ℝ (ι → ℝ)}
    (hc : IsCompl E H) (hTE : ∀ x ∈ E, T x ∈ E) (hTH : ∀ x ∈ H, T x ∈ H) (n : ℕ)
    (v : ι → ℝ) : E.projection H hc ((T ^ n) v) = (T ^ n) (E.projection H hc v) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, projection_comm hc hTE hTH, ih]

/-! ### Dynamics of a hyperbolic splitting -/

section Dynamics

variable {A : Matrix ι ι ℤ} {Vs Vu : Submodule ℝ (ι → ℝ)}

/-- A vector with bounded forward orbit lies in `V_s`. -/
theorem IsHypSplitting.mem_s_of_bdd (hyp : IsHypSplitting A Vs Vu) {h : ι → ℝ} {K : ℝ}
    (hK : ∀ n : ℕ, ‖(act A ^ n) h‖ ≤ K) : h ∈ Vs := by
  obtain ⟨cs, hcs, hcs0, hcsb⟩ := hyp.contr
  obtain ⟨cu, hcu, hcu0, hcub⟩ := hyp.exp
  obtain ⟨Ks, hKs0, hKs⟩ := tendsto_bound hcs
  have htop : h ∈ Vs ⊔ Vu := by rw [hyp.compl.sup_eq_top]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp htop
  have hzb : ∀ n : ℕ, ‖(act A ^ n) z‖ ≤ K + Ks * ‖y‖ := by
    intro n
    have : (act A ^ n) z = (act A ^ n) (y + z) - (act A ^ n) y := by rw [map_add]; abel
    rw [this]
    refine (norm_sub_le _ _).trans (add_le_add (hK n) ?_)
    exact (hcsb n y hy).trans (mul_le_mul_of_nonneg_right (hKs n) (norm_nonneg _))
  have hz0 : ‖z‖ ≤ 0 := by
    have hlim : Tendsto (fun n : ℕ => cu n * (K + Ks * ‖y‖)) atTop (𝓝 0) := by
      simpa using hcu.mul_const (K + Ks * ‖y‖)
    refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    exact (hcub n z hz).trans (mul_le_mul_of_nonneg_left (hzb n) (hcu0 n))
  have : z = 0 := norm_le_zero_iff.mp hz0
  rw [this, add_zero]
  exact hy

theorem IsHypSplitting.tendsto_of_mem_s (hyp : IsHypSplitting A Vs Vu) {x : ι → ℝ} (hx : x ∈ Vs) :
    Tendsto (fun n : ℕ => (act A ^ n) x) atTop (𝓝 0) := by
  obtain ⟨cs, hcs, hcs0, hcsb⟩ := hyp.contr
  exact squeeze_zero_norm (fun n => hcsb n x hx) (by simpa using hcs.mul_const ‖x‖)

/-- `E^s(A) = V_s`. -/
theorem IsHypSplitting.stableSet_eq (hyp : IsHypSplitting A Vs Vu) :
    stableSet A = (Vs : Set (ι → ℝ)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨K, hK⟩ := (Metric.isBounded_range_of_tendsto _ hv).exists_norm_le
    exact hyp.mem_s_of_bdd (K := K) (fun n => hK _ ⟨n, rfl⟩)
  · intro hv
    exact hyp.tendsto_of_mem_s hv

/-- For an invariant splitting `E ⊕ H` with `H ⊆ V_s`, every vector with a backward orbit
tending to `0` lies in `E`. -/
theorem IsHypSplitting.unstableSet_subset (hyp : IsHypSplitting A Vs Vu)
    {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H) (hE : ∀ x ∈ E, act A x ∈ E)
    (hH : ∀ x ∈ H, act A x ∈ H) (hHs : H ≤ Vs) : unstableSet A ⊆ (E : Set (ι → ℝ)) := by
  rintro v ⟨w, hw0, hwT, hwt⟩
  obtain ⟨cs, hcs, hcs0, hcsb⟩ := hyp.contr
  set π := H.projection E hc.symm with hπdef
  have hπc : Continuous π := LinearMap.continuous_of_finiteDimensional π
  have hpow : ∀ n : ℕ, (act A ^ n) (w n) = v := by
    intro n
    induction n with
    | zero => simp [hw0]
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hwT, ih]
  have hπv : ∀ n, π v = (act A ^ n) (π (w n)) := by
    intro n
    rw [hπdef, ← projection_pow_comm hc.symm hH hE, hpow]
  have h1 : Tendsto (fun n => π (w n)) atTop (𝓝 0) := by
    have := (hπc.tendsto 0).comp hwt
    rw [map_zero] at this
    exact this
  have hlim : Tendsto (fun n => cs n * ‖π (w n)‖) atTop (𝓝 0) := by
    simpa using hcs.mul (tendsto_norm_zero.comp h1)
  have hle : ‖π v‖ ≤ 0 := by
    refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    rw [hπv n]
    exact hcsb n _ (hHs (Submodule.projection_apply_mem _ _))
  have : π v = 0 := norm_le_zero_iff.mp hle
  exact (Submodule.projection_apply_eq_zero_iff _).mp this

/-- `E^u(A) = V_u`. -/
theorem IsHypSplitting.unstableSet_eq (hyp : IsHypSplitting A Vs Vu) :
    unstableSet A = (Vu : Set (ι → ℝ)) :=
  Set.Subset.antisymm (hyp.unstableSet_subset hyp.compl.symm hyp.mapsTo_u hyp.mapsTo_s le_rfl)
    hyp.back

/-- For an invariant splitting `E ⊕ H` with `V_u ⊆ E`, the forward orbits of `H` tend to `0`. -/
theorem IsHypSplitting.subset_stableSet (hyp : IsHypSplitting A Vs Vu)
    {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H) (hE : ∀ x ∈ E, act A x ∈ E)
    (hH : ∀ x ∈ H, act A x ∈ H) (hu : Vu ≤ E) : (H : Set (ι → ℝ)) ⊆ stableSet A := by
  intro h hh
  have htop : h ∈ Vs ⊔ Vu := by rw [hyp.compl.sup_eq_top]; trivial
  obtain ⟨s, hs, u, hu', rfl⟩ := Submodule.mem_sup.mp htop
  set π := H.projection E hc.symm with hπdef
  have hπc : Continuous π := LinearMap.continuous_of_finiteDimensional π
  have hπ : π (s + u) = π s := by
    rw [map_add, hπdef, Submodule.projection_apply_of_mem_right _ (hu hu'), add_zero]
  have hself : π (s + u) = s + u := Submodule.projection_apply_of_mem_left _ hh
  have heq : ∀ n, (act A ^ n) (s + u) = π ((act A ^ n) s) := by
    intro n
    rw [hπdef, projection_pow_comm hc.symm hH hE, ← hπdef, ← hπ, hself]
  show Tendsto (fun n => (act A ^ n) (s + u)) atTop (𝓝 0)
  simp_rw [heq]
  have := (hπc.tendsto 0).comp (hyp.tendsto_of_mem_s hs)
  rw [map_zero] at this
  exact this

end Dynamics

/-! ### The lattice -/

theorem eq_zero_of_mem_lattice_of_norm_lt_one {v : ι → ℝ} (hv : v ∈ intLattice ι)
    (h : ‖v‖ < 1) : v = 0 := by
  obtain ⟨z, rfl⟩ := mem_intLattice_iff.mp hv
  funext i
  have hi : |(z i : ℝ)| < 1 := by
    have := (norm_le_pi_norm (fun i => (z i : ℝ)) i).trans_lt h
    rwa [Real.norm_eq_abs] at this
  have hz1 : |z i| < 1 := by exact_mod_cast hi
  rw [Pi.zero_apply, Int.abs_lt_one_iff.mp hz1, Int.cast_zero]

section Schemes

variable {A : Matrix ι ι ℤ} {Vs Vu : Submodule ℝ (ι → ℝ)}

/-- A lattice vector of `V_s` is `0`. -/
theorem IsHypSplitting.lattice_inj (hyp : IsHypSplitting A Vs Vu)
    (hinj : Function.Injective (act A)) {γ : ι → ℝ} (hγ : γ ∈ intLattice ι) (hγs : γ ∈ Vs) :
    γ = 0 := by
  obtain ⟨n, hn⟩ := ((hyp.tendsto_of_mem_s hγs).eventually (ball_mem_nhds 0 one_pos)).exists
  have h0 : (act A ^ n) γ = 0 :=
    eq_zero_of_mem_lattice_of_norm_lt_one (act_pow_mem_intLattice A n hγ) (mem_ball_zero_iff.mp hn)
  have hinjn : Function.Injective (act A ^ n) := by
    rw [Module.End.coe_pow]
    exact hinj.iterate n
  exact hinjn (by rw [h0, map_zero])

omit [DecidableEq ι] in
theorem isClosed_lineSpace (C : AddSubgroup (ι → ℝ)) (hC : IsClosed (C : Set (ι → ℝ))) :
    IsClosed (KroneckerDensity.lineSpace C : Set (ι → ℝ)) := by
  have : (KroneckerDensity.lineSpace C : Set (ι → ℝ)) =
      ⋂ t : ℝ, (fun u : ι → ℝ => t • u) ⁻¹' C := by
    ext u
    simp [KroneckerDensity.lineSpace]
  rw [this]
  exact isClosed_iInter fun t => hC.preimage (continuous_const_smul t)

omit [DecidableEq ι] in
/-- A closed subgroup approached by its own points from outside a subspace `L ⊆ C` contains a line
not in `L`. -/
theorem exists_line_of_approach {C : AddSubgroup (ι → ℝ)} (hC : IsClosed (C : Set (ι → ℝ)))
    {L : Submodule ℝ (ι → ℝ)} (hLC : (L : Set (ι → ℝ)) ⊆ C)
    (c : ℕ → ι → ℝ) (hc : ∀ n, c n ∈ C) (hpos : ∀ n, 0 < infDist (c n) L)
    (hlim : Tendsto (fun n => infDist (c n) L) atTop (𝓝 0)) :
    ∃ u : ι → ℝ, u ∉ L ∧ ∀ t : ℝ, t • u ∈ C := by
  have hLne : (L : Set (ι → ℝ)).Nonempty := ⟨0, L.zero_mem⟩
  have hex : ∀ n, ∃ v ∈ (L : Set (ι → ℝ)), dist (c n) v < 2 * infDist (c n) L := by
    intro n
    exact (infDist_lt_iff hLne).mp (by linarith [hpos n])
  choose v hvL hvd using hex
  set x : ℕ → ι → ℝ := fun n => c n - v n with hx
  set d : ℕ → ℝ := fun n => ‖x n‖ with hd
  have hxC : ∀ n, x n ∈ C := fun n => C.sub_mem (hc n) (hLC (hvL n))
  have hdist : ∀ n, d n = dist (c n) (v n) := fun n => (dist_eq_norm _ _).symm
  have hdpos : ∀ n, 0 < d n := by
    intro n
    rw [hdist n]
    exact lt_of_lt_of_le (hpos n) (infDist_le_dist_of_mem (hvL n))
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 2 * infDist (c n) L) atTop (𝓝 0) := by
      simpa using hlim.const_mul 2
    refine squeeze_zero (fun n => (hdpos n).le) (fun n => ?_) h2
    rw [hdist n]
    exact (hvd n).le
  set u : ℕ → ι → ℝ := fun n => (d n)⁻¹ • x n with hu
  have hunorm : ∀ n, ‖u n‖ = 1 := by
    intro n
    rw [hu]
    simp only
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hdpos n)]
    exact inv_mul_cancel₀ (hdpos n).ne'
  have hfar : ∀ n, ∀ w ∈ L, (1 / 2 : ℝ) ≤ ‖u n - w‖ := by
    intro n w hw
    have hmem : v n + d n • w ∈ (L : Set (ι → ℝ)) := L.add_mem (hvL n) (L.smul_mem _ hw)
    have h1 : infDist (c n) L ≤ dist (c n) (v n + d n • w) := infDist_le_dist_of_mem hmem
    have h2 : dist (c n) (v n + d n • w) = d n * ‖u n - w‖ := by
      rw [dist_eq_norm]
      have : c n - (v n + d n • w) = d n • (u n - w) := by
        rw [hu]
        simp only
        rw [smul_sub, smul_smul, mul_inv_cancel₀ (hdpos n).ne', one_smul, hx]
        exact sub_add_eq_sub_sub _ _ _
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (hdpos n)]
    have h3 : d n < 2 * infDist (c n) L := by rw [hdist n]; exact hvd n
    have h4 : d n < 2 * (d n * ‖u n - w‖) := lt_of_lt_of_le h3 (by rw [← h2]; linarith)
    have h5 := hdpos n
    nlinarith
  have hsph : ∀ n, u n ∈ sphere (0 : ι → ℝ) 1 := fun n => by simp [hunorm n]
  obtain ⟨u₀, hu₀, φ, hφ, hconv⟩ := (isCompact_sphere (0 : ι → ℝ) 1).tendsto_subseq hsph
  refine ⟨u₀, ?_, ?_⟩
  · intro hu₀L
    have hclosed : IsClosed {y : ι → ℝ | (1 / 2 : ℝ) ≤ ‖y - u₀‖} :=
      isClosed_le continuous_const (by fun_prop)
    have hlimmem : u₀ ∈ {y : ι → ℝ | (1 / 2 : ℝ) ≤ ‖y - u₀‖} :=
      hclosed.mem_of_tendsto hconv (Eventually.of_forall fun n => hfar (φ n) u₀ hu₀L)
    simp at hlimmem
    norm_num at hlimmem
  · intro t
    set k : ℕ → ℤ := fun n => ⌊t / d (φ n)⌋ with hk
    have hkC : ∀ n, (k n) • x (φ n) ∈ C := fun n => C.zsmul_mem (hxC (φ n)) _
    have hrepr : ∀ n, (k n) • x (φ n) = ((k n : ℝ) * d (φ n)) • u (φ n) := by
      intro n
      rw [hu]
      simp only
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hdpos (φ n)).ne', mul_one,
        ← Int.cast_smul_eq_zsmul ℝ]
    have hdφ : Tendsto (fun n => d (φ n)) atTop (𝓝 0) := hdlim.comp hφ.tendsto_atTop
    have hscal : Tendsto (fun n => (k n : ℝ) * d (φ n)) atTop (𝓝 t) := by
      have hb : ∀ n, |(k n : ℝ) * d (φ n) - t| ≤ d (φ n) := by
        intro n
        have hdp := hdpos (φ n)
        have hfl1 : (k n : ℝ) ≤ t / d (φ n) := Int.floor_le _
        have hfl2 : t / d (φ n) < (k n : ℝ) + 1 := Int.lt_floor_add_one _
        have e1 : (k n : ℝ) * d (φ n) ≤ t := by
          have := mul_le_mul_of_nonneg_right hfl1 hdp.le
          rwa [div_mul_cancel₀ _ hdp.ne'] at this
        have e2 : t < ((k n : ℝ) + 1) * d (φ n) := by
          have := mul_lt_mul_of_pos_right hfl2 hdp
          rwa [div_mul_cancel₀ _ hdp.ne'] at this
        rw [abs_le]
        constructor <;> nlinarith
      have : Tendsto (fun n => (k n : ℝ) * d (φ n) - t) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hb n) hdφ
      simpa using this.add_const t
    have hy : Tendsto (fun n => (k n) • x (φ n)) atTop (𝓝 (t • u₀)) := by
      simp_rw [hrepr]
      exact hscal.smul hconv
    exact hC.mem_of_tendsto hy (Eventually.of_forall hkC)

omit [DecidableEq ι] in
/-- A closed `T`-invariant subgroup on which the iterates of an injective `T` tend to `0`
contains its real span. -/
theorem span_subset_of_contracting {C : AddSubgroup (ι → ℝ)} (hC : IsClosed (C : Set (ι → ℝ)))
    (T : Module.End ℝ (ι → ℝ)) (hT : Function.Injective T) (hTC : ∀ x ∈ C, T x ∈ C)
    (hcontr : ∀ x ∈ C, Tendsto (fun n : ℕ => (T ^ n) x) atTop (𝓝 0)) :
    (Submodule.span ℝ (C : Set (ι → ℝ)) : Set (ι → ℝ)) ⊆ C := by
  set L := KroneckerDensity.lineSpace C with hL
  have hTL : ∀ u ∈ L, T u ∈ L := by
    intro u hu t
    rw [← map_smul]
    exact hTC _ (hu t)
  have hTL' : ∀ y, T y ∈ L → y ∈ L := by
    let Tl : L →ₗ[ℝ] L := T.restrict hTL
    have hinj : Function.Injective Tl := by
      intro a b hab
      apply Subtype.ext
      exact hT (congrArg Subtype.val hab)
    have hsurj : Function.Surjective Tl := LinearMap.injective_iff_surjective.mp hinj
    intro y hy
    obtain ⟨w, hw⟩ := hsurj ⟨T y, hy⟩
    have : T w = T y := congrArg Subtype.val hw
    rw [← hT this]
    exact w.2
  have hCL : (C : Set (ι → ℝ)) ⊆ L := by
    intro c hcC
    by_contra hcL
    have hLcl : IsClosed (L : Set (ι → ℝ)) := isClosed_lineSpace C hC
    have hLne : (L : Set (ι → ℝ)).Nonempty := ⟨0, L.zero_mem⟩
    have hiterC : ∀ n : ℕ, (T ^ n) c ∈ C := fun n => pow_mapsTo_set T hTC n c hcC
    have hiterL : ∀ n : ℕ, (T ^ n) c ∉ L := by
      intro n hn
      apply hcL
      have key : ∀ m : ℕ, ∀ y : ι → ℝ, (T ^ m) y ∈ L → y ∈ L := by
        intro m
        induction m with
        | zero => intro y hy; simpa using hy
        | succ m ih =>
          intro y hy
          rw [pow_succ', Module.End.mul_apply] at hy
          exact ih y (hTL' _ hy)
      exact key n c hn
    have hpos : ∀ n, 0 < infDist ((T ^ n) c) L :=
      fun n => (hLcl.notMem_iff_infDist_pos hLne).mp (hiterL n)
    have hlim : Tendsto (fun n => infDist ((T ^ n) c) L) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => (hpos n).le) (fun n => ?_)
        (tendsto_norm_zero.comp (hcontr c hcC))
      have := infDist_le_dist_of_mem (x := (T ^ n) c) (L.zero_mem : (0 : ι → ℝ) ∈ (L : Set _))
      simpa [dist_zero_right] using this
    obtain ⟨u, huL, hline⟩ :=
      exists_line_of_approach hC (KroneckerDensity.lineSpace_subset C) _ hiterC hpos hlim
    exact huL hline
  have hspan : Submodule.span ℝ (C : Set (ι → ℝ)) ≤ L := Submodule.span_le.mpr hCL
  exact fun x hx => KroneckerDensity.lineSpace_subset C (hspan hx)

/-- The projection of `ℤ^ι` to `V_s` along `V_u` is dense in `V_s`. -/
theorem IsHypSplitting.dense (hyp : IsHypSplitting A Vs Vu) (hinj : Function.Injective (act A)) :
    (Vs : Set (ι → ℝ)) ⊆
      closure (Vs.projection Vu hyp.compl '' (intLattice ι : Set (ι → ℝ))) := by
  set T := act A with hT
  set πs := Vs.projection Vu hyp.compl with hπs
  set G : AddSubgroup (ι → ℝ) :=
    ((intLattice ι).toAddSubgroup.map πs.toAddMonoidHom).topologicalClosure with hG
  have hGcl : IsClosed (G : Set (ι → ℝ)) := AddSubgroup.isClosed_topologicalClosure _
  have hπsT : ∀ v, πs (T v) = T (πs v) := projection_comm hyp.compl hyp.mapsTo_s hyp.mapsTo_u
  have hGsub : (G : Set (ι → ℝ)) ⊆ Vs := by
    apply closure_minimal _ Vs.closed_of_finiteDimensional
    rintro _ ⟨γ, _, rfl⟩
    exact Submodule.projection_apply_mem _ _
  have hTG : ∀ x ∈ G, T x ∈ G := by
    have himg : ∀ x ∈ ((intLattice ι).toAddSubgroup.map πs.toAddMonoidHom : Set (ι → ℝ)),
        T x ∈ G := by
      rintro _ ⟨γ, hγ, rfl⟩
      apply AddSubgroup.le_topologicalClosure
      exact ⟨T γ, act_mem_intLattice A hγ, by simp [hπsT]⟩
    intro x hx
    have hcont : Continuous T := LinearMap.continuous_of_finiteDimensional T
    have := map_mem_closure hcont hx (fun y hy => himg y hy)
    exact hGcl.closure_subset this
  have hspanG : (Vs : Set (ι → ℝ)) ⊆ Submodule.span ℝ (G : Set (ι → ℝ)) := by
    intro h hh
    have hhΓ : h ∈ Submodule.span ℝ (intLattice ι : Set (ι → ℝ)) := by
      rw [span_intLattice]
      trivial
    have hπ : πs h = h := Submodule.projection_apply_of_mem_left _ hh
    rw [← hπ]
    have : Submodule.map πs (Submodule.span ℝ (intLattice ι : Set (ι → ℝ))) ≤
        Submodule.span ℝ (G : Set (ι → ℝ)) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨γ, hγ, rfl⟩
      exact AddSubgroup.le_topologicalClosure _ ⟨γ, hγ, rfl⟩
    exact this ⟨h, hhΓ, rfl⟩
  have hdensity : (Vs : Set (ι → ℝ)) ⊆ G :=
    hspanG.trans (span_subset_of_contracting hGcl T hinj hTG
      (fun x hx => hyp.tendsto_of_mem_s (hGsub hx)))
  intro h hh
  have := hdensity hh
  simpa [hG, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map] using this

/-- An inflation-invariant model set keeps every window orbit in the window. -/
theorem window_orbit (S : InvariantCPS A) {W : Set (ι → ℝ)}
    (hinfl : Set.MapsTo (act A) (S.modelSet W) (S.modelSet W))
    {γ : ι → ℝ} (hγ : γ ∈ intLattice ι) (hW : S.πH γ ∈ W) :
    ∀ n : ℕ, (act A ^ n) (S.πH γ) ∈ W := by
  intro n
  rw [InvariantCPS.πH, ← projection_pow_comm S.isCompl.symm S.mapsTo_H S.mapsTo_E]
  induction n with
  | zero => rw [pow_zero, Module.End.one_apply]; exact hW
  | succ n ih =>
    have hγn : (act A ^ n) γ ∈ intLattice ι := act_pow_mem_intLattice A n hγ
    have hmem : S.πE ((act A ^ n) γ) ∈ S.modelSet W := ⟨(act A ^ n) γ, hγn, ih, rfl⟩
    obtain ⟨γ', hγ', hW', heq⟩ := hinfl hmem
    have hδ : γ' - act A ((act A ^ n) γ) ∈ S.H := by
      rw [← Submodule.projection_apply_eq_zero_iff S.isCompl, map_sub]
      have e1 : S.E.projection S.H S.isCompl γ' = S.πE γ' := rfl
      rw [e1, heq, InvariantCPS.πE, projection_comm S.isCompl S.mapsTo_E S.mapsTo_H, sub_self]
    have hδΓ : γ' - act A ((act A ^ n) γ) ∈ intLattice ι :=
      (intLattice ι).sub_mem hγ' (act_mem_intLattice A hγn)
    have h0 := S.inj _ hδΓ hδ
    have : γ' = act A ((act A ^ n) γ) := sub_eq_zero.mp h0
    rw [pow_succ', Module.End.mul_apply, ← this]
    exact hW'

/-- Density and a relative ball: the window points span the internal space. -/
theorem le_span_window (S : InvariantCPS A) {W : Set (ι → ℝ)} (hW : S.IsWindow W) :
    S.H ≤ Submodule.span ℝ {y | ∃ γ ∈ intLattice ι, S.πH γ = y ∧ y ∈ W} := by
  set P := Submodule.span ℝ {y | ∃ γ ∈ intLattice ι, S.πH γ = y ∧ y ∈ W} with hPdef
  obtain ⟨_, _, c, hcH, r, hr, hball⟩ := hW
  have hPcl : IsClosed (P : Set (ι → ℝ)) := P.closed_of_finiteDimensional
  have hballP : ∀ y ∈ ball c r, y ∈ S.H → y ∈ P := by
    intro y hy hyH
    have hcl : y ∈ closure {y | ∃ γ ∈ intLattice ι, S.πH γ = y ∧ y ∈ W} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hyc : dist y c < r := hy
      have hδ : 0 < min ε (r - dist y c) := lt_min hε (by linarith)
      obtain ⟨b, ⟨γ, hγ, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp (S.dense hyH) _ hδ
      have hd' : dist y (S.πH γ) < min ε (r - dist y c) := hd
      refine ⟨S.πH γ, ⟨γ, hγ, rfl, hball ⟨?_, ?_⟩⟩, ?_⟩
      · rw [mem_ball]
        have hm := min_le_right ε (r - dist y c)
        calc dist (S.πH γ) c ≤ dist (S.πH γ) y + dist y c := dist_triangle _ _ _
          _ < (r - dist y c) + dist y c := by rw [dist_comm]; linarith
          _ = r := by ring
      · exact Submodule.projection_apply_mem _ _
      · exact lt_of_lt_of_le hd' (min_le_left _ _)
    exact closure_minimal Submodule.subset_span hPcl hcl
  have hcP : c ∈ P := hballP c (mem_ball_self hr) hcH
  intro h hh
  by_cases h0 : h = 0
  · rw [h0]; exact P.zero_mem
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr h0
  set t : ℝ := r / (2 * ‖h‖) with ht
  have htpos : 0 < t := div_pos hr (by linarith)
  have hmem : c + t • h ∈ P := by
    apply hballP
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos htpos, ht]
      field_simp
      linarith
    · exact S.H.add_mem hcH (S.H.smul_mem t hh)
  have : t • h ∈ P := by
    have := P.sub_mem hmem hcP
    rwa [add_sub_cancel_left] at this
  have hsmul := P.smul_mem t⁻¹ this
  rwa [smul_smul, inv_mul_cancel₀ htpos.ne', one_smul] at hsmul

/-- **Necessity.** An admissible scheme has `H ⊆ V_s`. -/
theorem IsHypSplitting.internal_le (hyp : IsHypSplitting A Vs Vu) (S : InvariantCPS A)
    (hS : S.Admissible) : S.H ≤ Vs := by
  obtain ⟨W, hW, hinfl⟩ := hS
  obtain ⟨R, hR⟩ := hW.2.1.subset_closedBall 0
  intro h hh
  have hbdd : ∀ x ∈ Submodule.span ℝ {y | ∃ γ ∈ intLattice ι, S.πH γ = y ∧ y ∈ W},
      ∃ K : ℝ, ∀ n : ℕ, ‖(act A ^ n) x‖ ≤ K := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨γ, hγ, rfl, hyW⟩ := hy
      refine ⟨R, fun n => ?_⟩
      have := hR (window_orbit S hinfl hγ hyW n)
      simpa [mem_closedBall, dist_zero_right] using this
    | zero => exact ⟨0, fun n => by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨K₁, h₁⟩ := hy
      obtain ⟨K₂, h₂⟩ := hz
      exact ⟨K₁ + K₂, fun n => by
        rw [map_add]; exact (norm_add_le _ _).trans (add_le_add (h₁ n) (h₂ n))⟩
    | smul a y _ hy =>
      obtain ⟨K, hK⟩ := hy
      exact ⟨‖a‖ * K, fun n => by
        rw [map_smul, norm_smul]; exact mul_le_mul_of_nonneg_left (hK n) (norm_nonneg a)⟩
  obtain ⟨K, hK⟩ := hbdd h (le_span_window S hW hh)
  exact hyp.mem_s_of_bdd hK

/-- **Sufficiency.** A scheme with `H ⊆ V_s` is admissible, with the orbit window. -/
theorem IsHypSplitting.admissible_of_le (hyp : IsHypSplitting A Vs Vu) (S : InvariantCPS A)
    (hHs : S.H ≤ Vs) : S.Admissible := by
  obtain ⟨cs, hcs, hcs0, hcsb⟩ := hyp.contr
  obtain ⟨K, hK0, hK⟩ := tendsto_bound hcs
  refine ⟨S.orbitWindow, ⟨fun v hv => hv.1, ?_, 0, S.H.zero_mem, (K + 1)⁻¹, by positivity, ?_⟩, ?_⟩
  · refine (isBounded_closedBall (x := (0 : ι → ℝ)) (r := 1)).subset (fun v hv => ?_)
    have := hv.2 0
    simpa using this
  · rintro v ⟨hv, hvH⟩
    refine ⟨hvH, fun n => ?_⟩
    rw [mem_ball, dist_zero_right] at hv
    calc ‖(act A ^ n) v‖ ≤ cs n * ‖v‖ := hcsb n v (hHs hvH)
      _ ≤ K * (K + 1)⁻¹ := mul_le_mul (hK n) hv.le (norm_nonneg _) hK0
      _ ≤ 1 := by
          rw [mul_inv_le_iff₀ (by positivity)]
          linarith
  · rintro x ⟨γ, hγ, hγW, rfl⟩
    refine ⟨act A γ, act_mem_intLattice A hγ, ?_, ?_⟩
    · have e : S.πH (act A γ) = act A (S.πH γ) :=
        projection_comm S.isCompl.symm S.mapsTo_H S.mapsTo_E γ
      rw [e]
      refine ⟨S.mapsTo_H _ hγW.1, fun n => ?_⟩
      have := hγW.2 (n + 1)
      rwa [pow_succ, Module.End.mul_apply] at this
    · exact projection_comm S.isCompl S.mapsTo_E S.mapsTo_H γ

end Schemes

end Hyperbolic

open Hyperbolic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The spectral description** (`det A ≠ 0`; no hyperbolicity hypothesis): for `χ_A = q · r`
over `ℝ` with `q`, `r` monic, every root of `q` outside and every root of `r` inside the unit
circle, `E^u(A) = ker q(A)` and `E^s(A) = ker r(A)`. -/
theorem unstableSet_eq_ker (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) (q : ℝ[X]) (r : ℝ[X])
    (hq : q.Monic) (hr : r.Monic) (hχ : A.charpoly.map (Int.castRingHom ℝ) = q * r)
    (hqroots : ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, 1 < ‖z‖)
    (hrroots : ∀ z ∈ (r.map (algebraMap ℝ ℂ)).roots, ‖z‖ < 1) :
    unstableSet A = LinearMap.ker (Polynomial.aeval (act A) q) ∧
      stableSet A = LinearMap.ker (Polynomial.aeval (act A) r) := by
  obtain ⟨hyp, -⟩ := isHypSplitting_ker A hdet q r hq hr hχ hqroots hrroots
  exact ⟨hyp.unstableSet_eq, hyp.stableSet_eq⟩

/-- If no eigenvalue of `A` lies on the unit circle, `χ_A = q · r` over `ℝ` with `q`, `r` monic,
every complex root of `q` outside and every complex root of `r` inside the unit circle (group the
irreducible real factors of `χ_A` by the common modulus of their roots). -/
theorem exists_hyperbolic_factorization (A : Matrix ι ι ℤ) (hhyp : IsHyperbolic A) :
    ∃ q r : ℝ[X], q.Monic ∧ r.Monic ∧ A.charpoly.map (Int.castRingHom ℝ) = q * r ∧
      (∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, 1 < ‖z‖) ∧
      (∀ z ∈ (r.map (algebraMap ℝ ℂ)).roots, ‖z‖ < 1) := by
  have hmon : (A.charpoly.map (Int.castRingHom ℝ)).Monic := (Matrix.charpoly_monic A).map _
  have hh : ∀ z ∈ ((A.charpoly.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ)).roots,
      ‖z‖ ≠ 1 := by
    rw [map_charpoly_complex]
    exact hhyp
  obtain ⟨r, q, hr, hq, hχ, hrroots, hqroots⟩ := exists_factor_inside_outside _ hmon hh
  exact ⟨q, r, hq, hr, by rw [hχ, mul_comm], hqroots, hrroots⟩

/-- `E^u ⊕ E^s` is a hyperbolic splitting into subspaces, with `dim E^u = U(A)`. -/
theorem exists_unstable_stable_submodules (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hhyp : IsHyperbolic A) :
    ∃ Eu Es : Submodule ℝ (ι → ℝ), (Eu : Set (ι → ℝ)) = unstableSet A ∧
      (Es : Set (ι → ℝ)) = stableSet A ∧ IsCompl Eu Es ∧
      Module.finrank ℝ Eu = unstableCount A := by
  obtain ⟨q, r, hq, hr, hχ, hqroots, hrroots⟩ := exists_hyperbolic_factorization A hhyp
  obtain ⟨hyp, hdim⟩ := isHypSplitting_ker A hdet q r hq hr hχ hqroots hrroots
  refine ⟨_, _, hyp.unstableSet_eq.symm, hyp.stableSet_eq.symm, hyp.compl.symm, ?_⟩
  rw [hdim, unstableCount_eq_natDegree A q r hq hr hχ hqroots hrroots]

/-- **(4) The hyperbolic case** (`det A ≠ 0`, no eigenvalue on the unit circle). An `A`-invariant
scheme is admissible if and only if `E ⊇ E^u(A)`, if and only if `H ⊆ E^s(A)`; `(E^u, E^s)`
carries an admissible scheme; the least physical dimension is `U(A)`; and every admissible scheme
with `dim E = U(A)` is `(E^u, E^s)`. No diagonalizability is assumed. -/
theorem hyperbolic_case {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hdet : A.det ≠ 0) (hhyp : IsHyperbolic A) :
    (∀ S : InvariantCPS A, (S.Admissible ↔ unstableSet A ⊆ (S.E : Set (ι → ℝ))) ∧
      (S.Admissible ↔ (S.H : Set (ι → ℝ)) ⊆ stableSet A)) ∧
    (∃ S : InvariantCPS A, (S.E : Set (ι → ℝ)) = unstableSet A ∧
      (S.H : Set (ι → ℝ)) = stableSet A ∧ S.Admissible) ∧
    IsLeast (physDims A) (unstableCount A) ∧
    ∀ S : InvariantCPS A, S.Admissible → finrank ℝ S.E = unstableCount A →
      (S.E : Set (ι → ℝ)) = unstableSet A ∧ (S.H : Set (ι → ℝ)) = stableSet A := by
  obtain ⟨q, r, hq, hr, hχ, hqroots, hrroots⟩ := exists_hyperbolic_factorization A hhyp
  obtain ⟨hyp, hdim⟩ := isHypSplitting_ker A hdet q r hq hr hχ hqroots hrroots
  set Vu := LinearMap.ker (aeval (act A) q) with hVu
  set Vs := LinearMap.ker (aeval (act A) r) with hVs
  have hinj := act_injective A hdet
  have hs : (Vs : Set (ι → ℝ)) = stableSet A := hyp.stableSet_eq.symm
  have hu : (Vu : Set (ι → ℝ)) = unstableSet A := hyp.unstableSet_eq.symm
  have hU : finrank ℝ Vu = unstableCount A := by
    rw [hdim, unstableCount_eq_natDegree A q r hq hr hχ hqroots hrroots]
  have hu_le : ∀ S : InvariantCPS A, S.Admissible → Vu ≤ S.E := fun S hS x hx =>
    hyp.unstableSet_subset S.isCompl S.mapsTo_E S.mapsTo_H (hyp.internal_le S hS) (hyp.back x hx)
  let S0 : InvariantCPS A :=
    { E := Vu
      H := Vs
      isCompl := hyp.compl.symm
      mapsTo_E := hyp.mapsTo_u
      mapsTo_H := hyp.mapsTo_s
      inj := fun γ hγ hγs => hyp.lattice_inj hinj hγ hγs
      dense := hyp.dense hinj }
  have hS0 : S0.Admissible := hyp.admissible_of_le S0 le_rfl
  refine ⟨fun S => ⟨⟨fun hS => ?_, fun h => ?_⟩, ⟨fun hS => ?_, fun h => ?_⟩⟩,
    ⟨S0, hu, hs, hS0⟩, ⟨⟨S0, hS0, hU⟩, ?_⟩, ?_⟩
  · exact hyp.unstableSet_subset S.isCompl S.mapsTo_E S.mapsTo_H (hyp.internal_le S hS)
  · refine hyp.admissible_of_le S ?_
    have hle : Vu ≤ S.E := fun x hx => h (hu ▸ hx)
    have := hyp.subset_stableSet S.isCompl S.mapsTo_E S.mapsTo_H hle
    rw [← hs] at this
    exact this
  · rw [← hs]
    exact hyp.internal_le S hS
  · refine hyp.admissible_of_le S ?_
    rw [← hs] at h
    exact h
  · rintro d ⟨S, hS, rfl⟩
    rw [← hU]
    exact Submodule.finrank_mono (hu_le S hS)
  · intro S hS hdimS
    have hE : S.E = Vu :=
      (Submodule.eq_of_le_of_finrank_eq (hu_le S hS) (by rw [hU, hdimS])).symm
    have hH : S.H = Vs := by
      have h1 := Submodule.finrank_add_eq_of_isCompl S.isCompl
      have h2 := Submodule.finrank_add_eq_of_isCompl hyp.compl
      exact Submodule.eq_of_le_of_finrank_eq (hyp.internal_le S hS) (by omega)
    rw [hE, hH]
    exact ⟨hu, hs⟩

/-- The least physical dimension of a hyperbolic `A` with `det A ≠ 0` is `U(A)`. -/
theorem isLeast_physDims_of_isHyperbolic (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hhyp : IsHyperbolic A) : IsLeast (physDims A) (unstableCount A) :=
  (hyperbolic_case A hdet hhyp).2.2.1

end

end InflationDimension
