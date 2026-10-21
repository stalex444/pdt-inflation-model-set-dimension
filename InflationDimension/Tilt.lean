module
public import Mathlib
public import InflationDimension.Defs
public import InflationDimension.Admissibility
public import InflationDimension.Normal
public import InflationDimension.DimOne

@[expose] public section
/-!
# Cyclotomic components: places, the semisimple collapse, and the tilt

Let `A` be an integer matrix whose characteristic polynomial is a power of one cyclotomic
polynomial `Φ_n`, equivalently `Φ_n(A)` is nilpotent. The least physical dimension of an
admissible `A`-invariant cut-and-project scheme on `ℤ^ι` is computed exactly.

* `isLeast_physDims_of_cyclotomic` (the semisimple collapse): if `Φ_n(A) = 0`, i.e. `A` is
  semisimple with `χ_A = Φ_nʳ`, the value is `δ_n`, `1` for `n ≤ 2` and `2` for `n ≥ 3`, whatever
  `r`; in particular `±1` on `ℤ^ι` needs `1` in every rank (`isLeast_physDims_one`,
  `isLeast_physDims_neg_one`).
* `isLeast_physDims_unipotent`, `isLeast_physDims_neg_unipotent` (`n = 1, 2`) and
  `isLeast_physDims_cyclotomic_tilt` (`n ≥ 3`), the tilt: if `Φ_n(A) ≠ 0`, the value is
  `#ι − (dim ker Φ_n(A) − dim (ker Φ_n(A) ∩ im Φ_n(A)))`. The Jordan blocks of size `≥ 2` count in
  full and the blocks of size one cost nothing: the internal space is tilted into the socle of the
  larger blocks.
* `isLeast_physDims_single_cyclotomic`: both cases in one statement.
* `tilt_physDims`, `tilt₃_physDims`: `1 ⊕ J₂(1)` on `ℤ³` needs `2` and `1 ⊕ J₃(1)` on `ℤ⁴`
  needs `3`, with explicit schemes.

Ingredients. A countable family of proper affine subspaces of a finite-dimensional real space
misses a point (Haar measure: `exists_forall_notMem_affine`, `exists_forall_apply_ne`). The
places of `ℚ(ζ_n)` are complex for `n ≥ 3`: every irreducible real factor of `Φ_n` is quadratic
(`natDegree_eq_two_of_dvd_cyclotomic`). Rational vectors are invisible to real factors of `Φ_n`
of smaller degree (`cyclotomic_dvd_of_annihilator`, from the rational annihilator lemma
`KernelSplit.exists_irreducible_dvd_of_real_annihilator`). Density is Kronecker's criterion
(`dense_of_no_integral_functional`). The lower bound reduces to the unipotent map `Aⁿ`
(`finrank_H_add_le_cyclotomic`). The generic invariant subspaces inside a repeated isotypic
component are `exists_scheme_of_cyclotomic` (a plane `span (e, A e)` at one place of `ℚ(ζ_n)`),
`exists_scheme_of_ker_inf_range` (the unipotent tilt) and `exists_internal_of_cyclotomic` (an
equivariant graph tilted into the socle at one place); the physical space of the tilt at a
complex place is the dot-product orthogonal of the same construction for `Aᵀ`.
-/

namespace InflationDimension

open Polynomial Module
open scoped Matrix

noncomputable section

namespace Tilt

/-! ### Generic points -/

/-- A countable family of proper affine subspaces of a finite-dimensional real normed space
misses some point. -/
theorem exists_forall_notMem_affine {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {α : Type*} [Countable α] (s : α → AffineSubspace ℝ V)
    (hs : ∀ a, s a ≠ ⊤) : ∃ x : V, ∀ a, x ∉ s a := by
  borelize V
  let μ : MeasureTheory.Measure V := MeasureTheory.Measure.addHaar
  have h0 : μ (⋃ a, (s a : Set V)) = 0 :=
    MeasureTheory.measure_iUnion_null
      (fun a => MeasureTheory.Measure.addHaar_affineSubspace μ (s a) (hs a))
  by_contra h
  have hU : (⋃ a, (s a : Set V)) = Set.univ :=
    Set.eq_univ_of_forall (fun x => Set.mem_iUnion.2 (not_forall_not.1 (not_exists.1 h x)))
  rw [hU] at h0
  exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne' h0

/-- A countable family of proper subspaces of a finite-dimensional real normed space misses some
point. -/
theorem exists_forall_notMem {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {α : Type*} [Countable α] (s : α → Submodule ℝ V)
    (hs : ∀ a, s a ≠ ⊤) : ∃ x : V, ∀ a, x ∉ s a := by
  borelize V
  let μ : MeasureTheory.Measure V := MeasureTheory.Measure.addHaar
  have h0 : μ (⋃ a, (s a : Set V)) = 0 :=
    MeasureTheory.measure_iUnion_null
      (fun a => MeasureTheory.Measure.addHaar_submodule μ (s a) (hs a))
  by_contra h
  have hU : (⋃ a, (s a : Set V)) = Set.univ :=
    Set.eq_univ_of_forall (fun x => Set.mem_iUnion.2 (not_forall_not.1 (not_exists.1 h x)))
  rw [hU] at h0
  exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne' h0

/-- The linear functional `x ↦ y ⬝ᵥ x`. -/
def dotL {ι : Type*} [Fintype ι] (y : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun x := y ⬝ᵥ x
  map_add' x z := dotProduct_add y x z
  map_smul' r x := dotProduct_smul r y x

@[simp] theorem dotL_apply {ι : Type*} [Fintype ι] (y x : ι → ℝ) : dotL y x = y ⬝ᵥ x := rfl

theorem ker_dotL_ne_top {ι : Type*} [Fintype ι] {y : ι → ℝ} (hy : y ≠ 0) :
    LinearMap.ker (dotL y) ≠ ⊤ := by
  intro h
  have : y ∈ LinearMap.ker (dotL y) := by rw [h]; exact Submodule.mem_top
  rw [LinearMap.mem_ker, dotL_apply, dotProduct_self_eq_zero] at this
  exact hy this

/-! ### Transport of polynomial identities from `ℤ` -/

section Transport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem aeval_map_int {R : Type*} [CommRing R] (A : Matrix ι ι ℤ) (p : ℤ[X]) :
    aeval (A.map (Int.castRingHom R)) (p.map (Int.castRingHom R)) =
      (aeval A p).map (Int.castRingHom R) := by
  rw [← algebraMap_int_eq, aeval_map_algebraMap]
  exact aeval_algHom_apply ((algebraMap ℤ R).mapMatrix.toIntAlgHom) A p

theorem aeval_act_map {A : Matrix ι ι ℤ} (p : ℤ[X]) :
    aeval (act A) (p.map (Int.castRingHom ℝ)) =
      Matrix.toLin' ((aeval A p).map (Int.castRingHom ℝ)) := by
  rw [← aeval_map_int]
  exact aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℝ) (n := ι)).toAlgHom
    (A.map (Int.castRingHom ℝ)) (p.map (Int.castRingHom ℝ))

theorem aeval_act_eq_zero {A : Matrix ι ι ℤ} {p : ℤ[X]} (hp : aeval A p = 0) :
    aeval (act A) (p.map (Int.castRingHom ℝ)) = 0 := by
  rw [aeval_act_map, hp, Matrix.map_zero _ (map_zero (Int.castRingHom ℝ)), map_zero]

end Transport

/-! ### The tilt `1 ⊕ J₂(1)` on `ℤ³` -/

section TiltTwo

/-- `1 ⊕ J₂(1)`: `A e₀ = e₀`, `A e₁ = e₁`, `A e₂ = e₁ + e₂`. -/
abbrev tiltMat : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

@[simp] theorem act_apply_zero (v : Fin 3 → ℝ) : act tiltMat v 0 = v 0 := by
  simp [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] theorem act_apply_one (v : Fin 3 → ℝ) : act tiltMat v 1 = v 1 + v 2 := by
  simp [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[simp] theorem act_apply_two (v : Fin 3 → ℝ) : act tiltMat v 2 = v 2 := by
  simp [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mem_intLattice_three {v : Fin 3 → ℝ} :
    v ∈ intLattice (Fin 3) ↔ ∀ i, ∃ n : ℤ, (n : ℝ) = v i := by
  unfold intLattice
  rw [Basis.mem_span_iff_repr_mem ℤ (Pi.basisFun ℝ (Fin 3)) v]
  simp [Pi.basisFun_repr, Set.mem_range]

/-- The internal direction `e₀ + √2 e₁`. -/
def h₀ : Fin 3 → ℝ := ![1, √2, 0]

theorem h₀_ne_zero : h₀ ≠ 0 := fun h => by
  have := congrFun h 0
  simp [h₀] at this

theorem act_h₀ : act tiltMat h₀ = h₀ := by
  ext i; fin_cases i <;> simp [h₀]

/-- The internal line `ℝ (e₀ + √2 e₁)`. -/
def Htilt : Submodule ℝ (Fin 3 → ℝ) := ℝ ∙ h₀

/-- The physical plane `span (e₁, √3 e₀ + e₂) = {v | v₀ = √3 v₂}`. -/
def Etilt : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | v 0 = √3 * v 2}
  add_mem' := by
    intro a b ha hb
    change a 0 = √3 * a 2 at ha
    change b 0 = √3 * b 2 at hb
    change a 0 + b 0 = √3 * (a 2 + b 2)
    rw [ha, hb]; ring
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    change v 0 = √3 * v 2 at hv
    change c * v 0 = √3 * (c * v 2)
    rw [hv]; ring

theorem mem_Etilt {v : Fin 3 → ℝ} : v ∈ Etilt ↔ v 0 = √3 * v 2 := Iff.rfl

theorem mem_Htilt {v : Fin 3 → ℝ} : v ∈ Htilt ↔ ∃ a : ℝ, a • h₀ = v :=
  Submodule.mem_span_singleton

theorem decomp (v : Fin 3 → ℝ) :
    (v 0 - √3 * v 2) • h₀ ∈ Htilt ∧ v - (v 0 - √3 * v 2) • h₀ ∈ Etilt := by
  refine ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self h₀), ?_⟩
  rw [mem_Etilt]
  simp [h₀]

theorem isCompl_tilt : IsCompl Etilt Htilt := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hE hH
    obtain ⟨a, rfl⟩ := mem_Htilt.1 hH
    rw [mem_Etilt] at hE
    have ha : a = 0 := by simpa [h₀] using hE
    simp [ha]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [Submodule.mem_sup]
    exact ⟨_, (decomp v).2, _, (decomp v).1, sub_add_cancel v _⟩

theorem mapsTo_E_tilt : ∀ v ∈ Etilt, act tiltMat v ∈ Etilt := by
  intro v hv
  rw [mem_Etilt] at hv ⊢
  simp [hv]

theorem mapsTo_H_tilt : ∀ v ∈ Htilt, act tiltMat v ∈ Htilt := by
  intro v hv
  obtain ⟨a, rfl⟩ := mem_Htilt.1 hv
  rw [map_smul, act_h₀]
  exact hv

theorem inj_tilt : ∀ γ ∈ intLattice (Fin 3), γ ∈ Htilt → γ = 0 := by
  intro γ hγ hH
  obtain ⟨a, rfl⟩ := mem_Htilt.1 hH
  obtain ⟨m, hm⟩ := (mem_intLattice_three.1 hγ) 0
  obtain ⟨n, hn⟩ := (mem_intLattice_three.1 hγ) 1
  have hm' : (m : ℝ) = a := by simpa [h₀] using hm
  have hn' : (n : ℝ) = a * √2 := by simpa [h₀] using hn
  by_cases h : m = 0
  · rw [← hm', h, Int.cast_zero, zero_smul]
  · rw [← hm'] at hn'
    exact absurd hn'.symm ((irrational_sqrt_two.intCast_mul h).ne_int n)

theorem projH_eq (v : Fin 3 → ℝ) :
    Htilt.projection Etilt isCompl_tilt.symm v = (v 0 - √3 * v 2) • h₀ := by
  calc Htilt.projection Etilt isCompl_tilt.symm v
      = Htilt.projection Etilt isCompl_tilt.symm
          ((v - (v 0 - √3 * v 2) • h₀) + (v 0 - √3 * v 2) • h₀) := by rw [sub_add_cancel]
    _ = (v 0 - √3 * v 2) • h₀ := by
      rw [map_add, Submodule.projection_apply_of_mem_left _ (decomp v).1,
        (Submodule.projection_apply_eq_zero_iff _).2 (decomp v).2, zero_add]

theorem projE_eq (v : Fin 3 → ℝ) :
    Etilt.projection Htilt isCompl_tilt v = v - (v 0 - √3 * v 2) • h₀ := by
  calc Etilt.projection Htilt isCompl_tilt v
      = Etilt.projection Htilt isCompl_tilt
          ((v - (v 0 - √3 * v 2) • h₀) + (v 0 - √3 * v 2) • h₀) := by rw [sub_add_cancel]
    _ = v - (v 0 - √3 * v 2) • h₀ := by
      rw [map_add, Submodule.projection_apply_of_mem_left _ (decomp v).2,
        (Submodule.projection_apply_eq_zero_iff _).2 (decomp v).1, add_zero]

theorem dense_tilt : (Htilt : Set (Fin 3 → ℝ)) ⊆
    closure (Htilt.projection Etilt isCompl_tilt.symm ''
      (intLattice (Fin 3) : Set (Fin 3 → ℝ))) := by
  have hG : Dense (AddSubgroup.closure {√3, (1 : ℝ)} : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff, div_one]
    simpa using Nat.prime_three.irrational_sqrt
  have hφc : Continuous (fun t : ℝ => t • h₀) := continuous_id.smul continuous_const
  have hsub : (fun t : ℝ => t • h₀) '' (AddSubgroup.closure {√3, (1 : ℝ)} : Set ℝ) ⊆
      Htilt.projection Etilt isCompl_tilt.symm '' (intLattice (Fin 3) : Set (Fin 3 → ℝ)) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 ht
    refine ⟨![(n : ℝ), 0, -(m : ℝ)], ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_intLattice_three]
      intro i
      fin_cases i
      · exact ⟨n, by simp⟩
      · exact ⟨0, by simp⟩
      · exact ⟨-m, by simp⟩
    · rw [projH_eq]
      congr 1
      simp [zsmul_eq_mul]
      ring1
  intro x hx
  obtain ⟨a, rfl⟩ := mem_Htilt.1 hx
  exact closure_mono hsub (image_closure_subset_closure_image hφc ⟨a, hG a, rfl⟩)

/-- The tilted scheme: `E = span (e₁, √3 e₀ + e₂)`, `H = ℝ (e₀ + √2 e₁)`. -/
def tiltScheme : InvariantCPS tiltMat where
  E := Etilt
  H := Htilt
  isCompl := isCompl_tilt
  mapsTo_E := mapsTo_E_tilt
  mapsTo_H := mapsTo_H_tilt
  inj := inj_tilt
  dense := dense_tilt

theorem tiltScheme_πH (v : Fin 3 → ℝ) : tiltScheme.πH v = (v 0 - √3 * v 2) • h₀ := projH_eq v

theorem tiltScheme_πE (v : Fin 3 → ℝ) :
    tiltScheme.πE v = v - (v 0 - √3 * v 2) • h₀ := projE_eq v

theorem tiltScheme_admissible : tiltScheme.Admissible := by
  refine ⟨Metric.ball 0 1 ∩ (Htilt : Set (Fin 3 → ℝ)),
    ⟨Set.inter_subset_right, Metric.isBounded_ball.subset Set.inter_subset_left,
      0, Htilt.zero_mem, 1, one_pos, subset_rfl⟩, ?_⟩
  rintro x ⟨γ, hγ, hW, rfl⟩
  refine ⟨act tiltMat γ, act_mem_intLattice tiltMat hγ, ?_, ?_⟩
  · rw [tiltScheme_πH, act_apply_zero, act_apply_two, ← tiltScheme_πH]
    exact hW
  · rw [tiltScheme_πE, tiltScheme_πE, map_sub, map_smul, act_h₀, act_apply_zero, act_apply_two]

theorem finrank_E_tilt : finrank ℝ tiltScheme.E = 2 := by
  have h := Submodule.finrank_add_eq_of_isCompl isCompl_tilt
  have hH : finrank ℝ Htilt = 1 := finrank_span_singleton h₀_ne_zero
  rw [Module.finrank_fin_fun] at h
  show finrank ℝ Etilt = 2
  omega

theorem e₁_not_mem (S : InvariantCPS tiltMat) : Pi.basisFun ℝ (Fin 3) 1 ∉ S.H := fun h => by
  have h1 := congrFun (S.inj _ (Submodule.subset_span ⟨1, rfl⟩) h) 1
  simp at h1

theorem finrank_H_le_one (S : InvariantCPS tiltMat) : finrank ℝ S.H ≤ 1 := by
  have hsub : ∀ v ∈ S.H, act tiltMat v - v ∈ S.H := fun v hv =>
    S.H.sub_mem (S.mapsTo_H v hv) hv
  have h2 : ∀ v ∈ S.H, v 2 = 0 := by
    intro v hv
    by_contra h2
    apply e₁_not_mem S
    have he : Pi.basisFun ℝ (Fin 3) 1 = (v 2)⁻¹ • (act tiltMat v - v) := by
      ext i; fin_cases i <;> simp [h2]
    rw [he]
    exact S.H.smul_mem _ (hsub v hv)
  let φ : S.H →ₗ[ℝ] ℝ := (LinearMap.proj 0).comp S.H.subtype
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 ?_
    rintro ⟨v, hv⟩ h0
    have h0' : v 0 = 0 := h0
    have h2' := h2 v hv
    by_cases h1 : v 1 = 0
    · apply Subtype.ext
      ext i; fin_cases i <;> simp [h0', h1, h2']
    · exfalso
      apply e₁_not_mem S
      have he : Pi.basisFun ℝ (Fin 3) 1 = (v 1)⁻¹ • v := by
        ext i; fin_cases i <;> simp [h0', h1, h2']
      rw [he]
      exact S.H.smul_mem _ hv
  have := LinearMap.finrank_le_finrank_of_injective hφ
  simpa using this

/-- The tilt `1 ⊕ J₂(1)` on `ℤ³`: least physical dimension `2`, not `3`. -/
theorem tilt_physDims :
    IsLeast (physDims (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ)) 2 := by
  refine ⟨⟨tiltScheme, tiltScheme_admissible, finrank_E_tilt⟩, ?_⟩
  rintro d ⟨S, -, rfl⟩
  have h := Submodule.finrank_add_eq_of_isCompl S.isCompl
  rw [Module.finrank_fin_fun] at h
  have := finrank_H_le_one S
  omega

end TiltTwo

/-! ### The tilt `1 ⊕ J₃(1)` on `ℤ⁴` -/

section TiltThree

/-- `1 ⊕ J₃(1)`: `A e₀ = e₀`, `A e₁ = e₁`, `A e₂ = e₁ + e₂`, `A e₃ = e₂ + e₃`. -/
abbrev tiltMat₃ : Matrix (Fin 4) (Fin 4) ℤ := !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1]

@[simp] theorem act₃_apply_zero (v : Fin 4 → ℝ) : act tiltMat₃ v 0 = v 0 := by
  simp [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem act₃_apply_one (v : Fin 4 → ℝ) : act tiltMat₃ v 1 = v 1 + v 2 := by
  simp [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem act₃_apply_two (v : Fin 4 → ℝ) : act tiltMat₃ v 2 = v 2 + v 3 := by
  simp [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem act₃_apply_three (v : Fin 4 → ℝ) : act tiltMat₃ v 3 = v 3 := by
  simp [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem mem_intLattice_four {v : Fin 4 → ℝ} :
    v ∈ intLattice (Fin 4) ↔ ∀ i, ∃ n : ℤ, (n : ℝ) = v i := by
  unfold intLattice
  rw [Basis.mem_span_iff_repr_mem ℤ (Pi.basisFun ℝ (Fin 4)) v]
  simp [Pi.basisFun_repr, Set.mem_range]

/-- The internal direction `e₀ + √2 e₁`. -/
def k₀ : Fin 4 → ℝ := ![1, √2, 0, 0]

theorem k₀_ne_zero : k₀ ≠ 0 := fun h => by
  have := congrFun h 0
  simp [k₀] at this

theorem act_k₀ : act tiltMat₃ k₀ = k₀ := by
  ext i; fin_cases i <;> simp [k₀]

/-- The internal line `ℝ (e₀ + √2 e₁)`. -/
def Htilt₃ : Submodule ℝ (Fin 4 → ℝ) := ℝ ∙ k₀

/-- The physical space `span (e₁, e₂, √3 e₀ + e₃) = {v | v₀ = √3 v₃}`. -/
def Etilt₃ : Submodule ℝ (Fin 4 → ℝ) where
  carrier := {v | v 0 = √3 * v 3}
  add_mem' := by
    intro a b ha hb
    change a 0 = √3 * a 3 at ha
    change b 0 = √3 * b 3 at hb
    change a 0 + b 0 = √3 * (a 3 + b 3)
    rw [ha, hb]; ring
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    change v 0 = √3 * v 3 at hv
    change c * v 0 = √3 * (c * v 3)
    rw [hv]; ring

theorem mem_Etilt₃ {v : Fin 4 → ℝ} : v ∈ Etilt₃ ↔ v 0 = √3 * v 3 := Iff.rfl

theorem mem_Htilt₃ {v : Fin 4 → ℝ} : v ∈ Htilt₃ ↔ ∃ a : ℝ, a • k₀ = v :=
  Submodule.mem_span_singleton

theorem decomp₃ (v : Fin 4 → ℝ) :
    (v 0 - √3 * v 3) • k₀ ∈ Htilt₃ ∧ v - (v 0 - √3 * v 3) • k₀ ∈ Etilt₃ := by
  refine ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self k₀), ?_⟩
  rw [mem_Etilt₃]
  simp [k₀]

theorem isCompl_tilt₃ : IsCompl Etilt₃ Htilt₃ := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hE hH
    obtain ⟨a, rfl⟩ := mem_Htilt₃.1 hH
    rw [mem_Etilt₃] at hE
    have ha : a = 0 := by simpa [k₀] using hE
    simp [ha]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [Submodule.mem_sup]
    exact ⟨_, (decomp₃ v).2, _, (decomp₃ v).1, sub_add_cancel v _⟩

theorem mapsTo_E_tilt₃ : ∀ v ∈ Etilt₃, act tiltMat₃ v ∈ Etilt₃ := by
  intro v hv
  rw [mem_Etilt₃] at hv ⊢
  simp [hv]

theorem mapsTo_H_tilt₃ : ∀ v ∈ Htilt₃, act tiltMat₃ v ∈ Htilt₃ := by
  intro v hv
  obtain ⟨a, rfl⟩ := mem_Htilt₃.1 hv
  rw [map_smul, act_k₀]
  exact hv

theorem inj_tilt₃ : ∀ γ ∈ intLattice (Fin 4), γ ∈ Htilt₃ → γ = 0 := by
  intro γ hγ hH
  obtain ⟨a, rfl⟩ := mem_Htilt₃.1 hH
  obtain ⟨m, hm⟩ := (mem_intLattice_four.1 hγ) 0
  obtain ⟨n, hn⟩ := (mem_intLattice_four.1 hγ) 1
  have hm' : (m : ℝ) = a := by simpa [k₀] using hm
  have hn' : (n : ℝ) = a * √2 := by simpa [k₀] using hn
  by_cases h : m = 0
  · rw [← hm', h, Int.cast_zero, zero_smul]
  · rw [← hm'] at hn'
    exact absurd hn'.symm ((irrational_sqrt_two.intCast_mul h).ne_int n)

theorem projH₃_eq (v : Fin 4 → ℝ) :
    Htilt₃.projection Etilt₃ isCompl_tilt₃.symm v = (v 0 - √3 * v 3) • k₀ := by
  calc Htilt₃.projection Etilt₃ isCompl_tilt₃.symm v
      = Htilt₃.projection Etilt₃ isCompl_tilt₃.symm
          ((v - (v 0 - √3 * v 3) • k₀) + (v 0 - √3 * v 3) • k₀) := by rw [sub_add_cancel]
    _ = (v 0 - √3 * v 3) • k₀ := by
      rw [map_add, Submodule.projection_apply_of_mem_left _ (decomp₃ v).1,
        (Submodule.projection_apply_eq_zero_iff _).2 (decomp₃ v).2, zero_add]

theorem projE₃_eq (v : Fin 4 → ℝ) :
    Etilt₃.projection Htilt₃ isCompl_tilt₃ v = v - (v 0 - √3 * v 3) • k₀ := by
  calc Etilt₃.projection Htilt₃ isCompl_tilt₃ v
      = Etilt₃.projection Htilt₃ isCompl_tilt₃
          ((v - (v 0 - √3 * v 3) • k₀) + (v 0 - √3 * v 3) • k₀) := by rw [sub_add_cancel]
    _ = v - (v 0 - √3 * v 3) • k₀ := by
      rw [map_add, Submodule.projection_apply_of_mem_left _ (decomp₃ v).2,
        (Submodule.projection_apply_eq_zero_iff _).2 (decomp₃ v).1, add_zero]

theorem dense_tilt₃ : (Htilt₃ : Set (Fin 4 → ℝ)) ⊆
    closure (Htilt₃.projection Etilt₃ isCompl_tilt₃.symm ''
      (intLattice (Fin 4) : Set (Fin 4 → ℝ))) := by
  have hG : Dense (AddSubgroup.closure {√3, (1 : ℝ)} : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff, div_one]
    simpa using Nat.prime_three.irrational_sqrt
  have hφc : Continuous (fun t : ℝ => t • k₀) := continuous_id.smul continuous_const
  have hsub : (fun t : ℝ => t • k₀) '' (AddSubgroup.closure {√3, (1 : ℝ)} : Set ℝ) ⊆
      Htilt₃.projection Etilt₃ isCompl_tilt₃.symm '' (intLattice (Fin 4) : Set (Fin 4 → ℝ)) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 ht
    refine ⟨![(n : ℝ), 0, 0, -(m : ℝ)], ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_intLattice_four]
      intro i
      fin_cases i
      · exact ⟨n, by simp⟩
      · exact ⟨0, by simp⟩
      · exact ⟨0, by simp⟩
      · exact ⟨-m, by simp⟩
    · rw [projH₃_eq]
      congr 1
      simp [zsmul_eq_mul]
      ring1
  intro x hx
  obtain ⟨a, rfl⟩ := mem_Htilt₃.1 hx
  exact closure_mono hsub (image_closure_subset_closure_image hφc ⟨a, hG a, rfl⟩)

/-- The tilted scheme: `E = span (e₁, e₂, √3 e₀ + e₃)`, `H = ℝ (e₀ + √2 e₁)`. -/
def tiltScheme₃ : InvariantCPS tiltMat₃ where
  E := Etilt₃
  H := Htilt₃
  isCompl := isCompl_tilt₃
  mapsTo_E := mapsTo_E_tilt₃
  mapsTo_H := mapsTo_H_tilt₃
  inj := inj_tilt₃
  dense := dense_tilt₃

theorem tiltScheme₃_πH (v : Fin 4 → ℝ) : tiltScheme₃.πH v = (v 0 - √3 * v 3) • k₀ :=
  projH₃_eq v

theorem tiltScheme₃_πE (v : Fin 4 → ℝ) :
    tiltScheme₃.πE v = v - (v 0 - √3 * v 3) • k₀ := projE₃_eq v

theorem tiltScheme₃_admissible : tiltScheme₃.Admissible := by
  refine ⟨Metric.ball 0 1 ∩ (Htilt₃ : Set (Fin 4 → ℝ)),
    ⟨Set.inter_subset_right, Metric.isBounded_ball.subset Set.inter_subset_left,
      0, Htilt₃.zero_mem, 1, one_pos, subset_rfl⟩, ?_⟩
  rintro x ⟨γ, hγ, hW, rfl⟩
  refine ⟨act tiltMat₃ γ, act_mem_intLattice tiltMat₃ hγ, ?_, ?_⟩
  · rw [tiltScheme₃_πH, act₃_apply_zero, act₃_apply_three, ← tiltScheme₃_πH]
    exact hW
  · rw [tiltScheme₃_πE, tiltScheme₃_πE, map_sub, map_smul, act_k₀, act₃_apply_zero,
      act₃_apply_three]

theorem finrank_E_tilt₃ : finrank ℝ tiltScheme₃.E = 3 := by
  have h := Submodule.finrank_add_eq_of_isCompl isCompl_tilt₃
  have hH : finrank ℝ Htilt₃ = 1 := finrank_span_singleton k₀_ne_zero
  rw [Module.finrank_fin_fun] at h
  show finrank ℝ Etilt₃ = 3
  omega

theorem e₁_not_mem₃ (S : InvariantCPS tiltMat₃) : Pi.basisFun ℝ (Fin 4) 1 ∉ S.H := fun h => by
  have h1 := congrFun (S.inj _ (Submodule.subset_span ⟨1, rfl⟩) h) 1
  simp at h1

theorem finrank_H_le_one₃ (S : InvariantCPS tiltMat₃) : finrank ℝ S.H ≤ 1 := by
  have hsub : ∀ v ∈ S.H, act tiltMat₃ v - v ∈ S.H := fun v hv =>
    S.H.sub_mem (S.mapsTo_H v hv) hv
  have h3 : ∀ v ∈ S.H, v 3 = 0 := by
    intro v hv
    by_contra h3
    apply e₁_not_mem₃ S
    have hw := hsub _ (hsub v hv)
    have he : Pi.basisFun ℝ (Fin 4) 1 =
        (v 3)⁻¹ • (act tiltMat₃ (act tiltMat₃ v - v) - (act tiltMat₃ v - v)) := by
      ext i; fin_cases i <;> simp [h3]
    rw [he]
    exact S.H.smul_mem _ hw
  have h2 : ∀ v ∈ S.H, v 2 = 0 := by
    intro v hv
    by_contra h2
    apply e₁_not_mem₃ S
    have he : Pi.basisFun ℝ (Fin 4) 1 = (v 2)⁻¹ • (act tiltMat₃ v - v) := by
      ext i; fin_cases i <;> simp [h2, h3 v hv]
    rw [he]
    exact S.H.smul_mem _ (hsub v hv)
  let φ : S.H →ₗ[ℝ] ℝ := (LinearMap.proj 0).comp S.H.subtype
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 ?_
    rintro ⟨v, hv⟩ h0
    have h0' : v 0 = 0 := h0
    have h2' := h2 v hv
    have h3' := h3 v hv
    by_cases h1 : v 1 = 0
    · apply Subtype.ext
      ext i; fin_cases i <;> simp [h0', h1, h2', h3']
    · exfalso
      apply e₁_not_mem₃ S
      have he : Pi.basisFun ℝ (Fin 4) 1 = (v 1)⁻¹ • v := by
        ext i; fin_cases i <;> simp [h0', h1, h2', h3']
      rw [he]
      exact S.H.smul_mem _ hv
  have := LinearMap.finrank_le_finrank_of_injective hφ
  simpa using this

/-- The tilt `1 ⊕ J₃(1)` on `ℤ⁴`: least physical dimension `3`, not `4`. -/
theorem tilt₃_physDims :
    IsLeast (physDims (!![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) ℤ)) 3 := by
  refine ⟨⟨tiltScheme₃, tiltScheme₃_admissible, finrank_E_tilt₃⟩, ?_⟩
  rintro d ⟨S, -, rfl⟩
  have h := Submodule.finrank_add_eq_of_isCompl S.isCompl
  rw [Module.finrank_fin_fun] at h
  have := finrank_H_le_one₃ S
  omega

end TiltThree

/-! ### Semisimple cyclotomic matrices: `Φ_n(A) = 0` -/

section Cyclotomic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem aeval_transpose_rat (M : Matrix ι ι ℚ) (f : ℚ[X]) : aeval Mᵀ f = (aeval M f)ᵀ := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.transpose_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_smul, Matrix.transpose_pow]

/-- **Rational annihilators when `Φ_n(B)` is nilpotent.** If `Φ_n(B)` is nilpotent for a rational
matrix `B` (all eigenvalues primitive `n`-th roots of unity), then every real polynomial `f` with
`f(B) γ = 0` at a nonzero rational vector `γ` is divisible by `Φ_n` in `ℝ[X]`. -/
theorem cyclotomic_dvd_of_annihilator {B : Matrix ι ι ℚ} {n : ℕ} (hn : 0 < n)
    (hB : IsNilpotent (aeval B (cyclotomic n ℚ))) {γ : ι → ℚ} (hγ : γ ≠ 0) {f : ℝ[X]}
    (hf : aeval (B.map (algebraMap ℚ ℝ)) f *ᵥ (algebraMap ℚ ℝ ∘ γ) = 0) :
    cyclotomic n ℝ ∣ f := by
  obtain ⟨p, hp, hpχ, hpf⟩ := KernelSplit.exists_irreducible_dvd_of_real_annihilator B hγ f hf
  have hdeg : p.degree ≠ 0 := fun h =>
    hp.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p hdeg
  set BC : Matrix ι ι ℂ := B.map (algebraMap ℚ ℂ) with hBC
  have hroot : IsRoot BC.charpoly z := by
    rw [hBC, Matrix.charpoly_map, IsRoot, eval_map_algebraMap]
    obtain ⟨g, hg⟩ := hpχ
    rw [hg, map_mul, hz, zero_mul]
  have hspec : z ∈ spectrum ℂ (Matrix.toLin' BC) := by
    rw [Matrix.spectrum_toLin']
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  obtain ⟨w, hw⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hspec).exists_hasEigenvector
  obtain ⟨k, hk⟩ := hB
  have hΦC : aeval (Matrix.toLin' BC) (cyclotomic n ℂ ^ k) = 0 := by
    have h1 : aeval BC (cyclotomic n ℂ ^ k) = 0 := by
      rw [map_pow, hBC, ← map_cyclotomic n (algebraMap ℚ ℂ), KernelSplit.aeval_map_matrix,
        ← Matrix.map_pow, hk, Matrix.map_zero _ (map_zero _)]
    have h2 := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)).toAlgHom BC
      (cyclotomic n ℂ ^ k)
    rw [h1, map_zero] at h2
    exact h2
  have hzΦ : aeval z (cyclotomic n ℚ) = 0 := by
    have h3 := Module.End.aeval_apply_of_hasEigenvector (p := cyclotomic n ℂ ^ k) hw
    rw [hΦC, LinearMap.zero_apply] at h3
    have h4 : (cyclotomic n ℂ).eval z = 0 := by
      by_contra hne
      exact hw.2 ((smul_eq_zero.mp h3.symm).resolve_left (by
        rw [eval_pow]; exact pow_ne_zero _ hne))
    rw [← map_cyclotomic n (algebraMap ℚ ℂ), eval_map_algebraMap] at h4
    exact h4
  have hmin : cyclotomic n ℚ = minpoly ℚ z :=
    minpoly.eq_of_irreducible_of_monic (cyclotomic.irreducible_rat hn) hzΦ (cyclotomic.monic n ℚ)
  have hdvd : cyclotomic n ℚ ∣ p := by rw [hmin]; exact minpoly.dvd ℚ z hz
  rw [← map_cyclotomic n (algebraMap ℚ ℝ)]
  exact (Polynomial.map_dvd _ hdvd).trans hpf

theorem aeval_ratMatrix_cyclotomic {A : Matrix ι ι ℤ} {n : ℕ}
    (hA : aeval A (cyclotomic n ℤ) = 0) :
    aeval (A.map (Int.castRingHom ℚ)) (cyclotomic n ℚ) = 0 := by
  rw [← map_cyclotomic n (Int.castRingHom ℚ), aeval_map_int, hA, Matrix.map_zero _ (map_zero _)]

theorem isNilpotent_ratMatrix_cyclotomic {A : Matrix ι ι ℤ} {n : ℕ}
    (hA : IsNilpotent (aeval A (cyclotomic n ℤ))) :
    IsNilpotent (aeval (A.map (Int.castRingHom ℚ)) (cyclotomic n ℚ)) := by
  obtain ⟨k, hk⟩ := hA
  refine ⟨k, ?_⟩
  rw [← map_cyclotomic n (Int.castRingHom ℚ), aeval_map_int, ← Matrix.map_pow, hk,
    Matrix.map_zero _ (map_zero _)]

theorem aeval_act_cyclotomic {A : Matrix ι ι ℤ} {n : ℕ} (hA : aeval A (cyclotomic n ℤ) = 0) :
    aeval (act A) (cyclotomic n ℝ) = 0 := by
  rw [← map_cyclotomic n (Int.castRingHom ℝ)]
  exact aeval_act_eq_zero hA

/-- **No lattice vector in a small kernel.** If `Φ_n(A)` is nilpotent, a real polynomial `f ≠ 0`
of degree `< φ(n)` kills no nonzero vector of `ℤ^ι`. -/
theorem lattice_eq_zero_of_aeval {A : Matrix ι ι ℤ} {n : ℕ} (hn : 0 < n)
    (hA : IsNilpotent (aeval A (cyclotomic n ℤ))) {f : ℝ[X]} (hf0 : f ≠ 0)
    (hdeg : f.natDegree < (cyclotomic n ℝ).natDegree) {γ : ι → ℝ} (hγ : γ ∈ intLattice ι)
    (h : aeval (act A) f γ = 0) : γ = 0 := by
  obtain ⟨k, rfl⟩ := mem_intLattice_iff.mp hγ
  by_contra hγ0
  set AQ : Matrix ι ι ℚ := A.map (Int.castRingHom ℚ) with hAQ
  set γQ : ι → ℚ := fun i => (k i : ℚ) with hγQ
  have hγeq : (fun i => (k i : ℝ)) = algebraMap ℚ ℝ ∘ γQ := by funext i; simp [γQ]
  have hγQ0 : γQ ≠ 0 := by
    intro h0; apply hγ0; rw [hγeq, h0]; funext i; simp
  have hann : aeval (AQ.map (algebraMap ℚ ℝ)) f *ᵥ (algebraMap ℚ ℝ ∘ γQ) = 0 := by
    rw [← hγeq, hAQ, ← KernelSplit.aeval_act]; exact h
  have hdvd := cyclotomic_dvd_of_annihilator hn (isNilpotent_ratMatrix_cyclotomic hA) hγQ0 hann
  exact absurd (natDegree_le_of_dvd hdvd hf0) (not_le.mpr hdeg)

/-- **No integral functional vanishes on a small image.** If `Φ_n(A)` is nilpotent and `f ≠ 0`
is a real polynomial of degree `< φ(n)`, then for every nonzero `c ∈ ℤ^ι` some `x` has
`c ⬝ f(A) x ≠ 0`. -/
theorem exists_dot_ne_zero {A : Matrix ι ι ℤ} {n : ℕ} (hn : 0 < n)
    (hA : IsNilpotent (aeval A (cyclotomic n ℤ))) {f : ℝ[X]} (hf0 : f ≠ 0)
    (hdeg : f.natDegree < (cyclotomic n ℝ).natDegree) {c : ι → ℤ} (hc : c ≠ 0) :
    ∃ x : ι → ℝ, (fun i => (c i : ℝ)) ⬝ᵥ aeval (act A) f x ≠ 0 := by
  by_contra h
  push Not at h
  set AQ : Matrix ι ι ℚ := A.map (Int.castRingHom ℚ) with hAQ
  set cQ : ι → ℚ := fun i => (c i : ℚ) with hcQ
  have hceq : (fun i => (c i : ℝ)) = algebraMap ℚ ℝ ∘ cQ := by funext i; simp [cQ]
  have hcQ0 : cQ ≠ 0 := by
    intro h0; apply hc; funext i; have := congrFun h0 i; simpa [cQ] using this
  set M : Matrix ι ι ℝ := aeval (AQ.map (algebraMap ℚ ℝ)) f with hM
  have hB : IsNilpotent (aeval AQᵀ (cyclotomic n ℚ)) := by
    obtain ⟨k, hk⟩ := isNilpotent_ratMatrix_cyclotomic hA
    refine ⟨k, ?_⟩
    rw [aeval_transpose_rat, ← Matrix.transpose_pow, hAQ, hk, Matrix.transpose_zero]
  have hT : aeval ((AQᵀ).map (algebraMap ℚ ℝ)) f *ᵥ (algebraMap ℚ ℝ ∘ cQ) = 0 := by
    rw [Matrix.transpose_map, KernelSplit.aeval_transpose_matrix, ← hM, Matrix.mulVec_transpose]
    funext j
    have := h (Pi.single j 1)
    rw [KernelSplit.aeval_act, ← hAQ, ← hM, hceq, Matrix.dotProduct_mulVec,
      dotProduct_single_one] at this
    simpa using this
  have hdvd := cyclotomic_dvd_of_annihilator hn hB hcQ0 hT
  exact absurd (natDegree_le_of_dvd hdvd hf0) (not_le.mpr hdeg)

/-- An integral functional is the dot product with an integer vector. -/
theorem exists_int_of_integral {f : (ι → ℝ) →ₗ[ℝ] ℝ}
    (hf : ∀ γ ∈ intLattice ι, ∃ n : ℤ, f γ = n) :
    ∃ c : ι → ℤ, ∀ v, f v = (fun i => (c i : ℝ)) ⬝ᵥ v := by
  have hsingle : ∀ i, (Pi.single i (1 : ℝ) : ι → ℝ) ∈ intLattice ι := fun i =>
    Submodule.subset_span ⟨i, by simp [Pi.basisFun_apply]⟩
  choose c hc using fun i => hf _ (hsingle i)
  refine ⟨c, fun v => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ f v, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hk' : f (fun j => if i = j then (1 : ℝ) else 0) = c i := by
    rw [← hc i]; congr 1; funext j; simp [Pi.single_apply, eq_comm]
  rw [hk', smul_eq_mul, mul_comm]

/-- **No invariant line.** If `Φ_n(A) = 0` with `n ≥ 3`, no `A`-invariant real subspace has
dimension one: `A` has no real eigenvalue. -/
theorem finrank_ne_one_of_invariant {A : Matrix ι ι ℤ} {n : ℕ} (hn : 2 < n)
    (hA : aeval (act A) (cyclotomic n ℝ) = 0) {U : Submodule ℝ (ι → ℝ)}
    (hU : ∀ v ∈ U, act A v ∈ U) : finrank ℝ U ≠ 1 := by
  intro h1
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨c, hc⟩ := hv ⟨act A v, hU v v.2⟩
  have hvne : (v : ι → ℝ) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have heig : (act A).HasEigenvector c (v : ι → ℝ) := by
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, hvne⟩
    have := congrArg Subtype.val hc
    simpa using this.symm
  have h3 := Module.End.aeval_apply_of_hasEigenvector (p := cyclotomic n ℝ) heig
  rw [hA, LinearMap.zero_apply] at h3
  have h4 := (smul_eq_zero.mp h3.symm).resolve_right hvne
  exact (cyclotomic_pos hn c).ne' h4

/-- The lower bound: for `Φ_n(A) = 0`, `n ≥ 3`, every scheme has `dim E ≥ 2`. -/
theorem two_le_finrank_E_of_cyclotomic [Nonempty ι] {A : Matrix ι ι ℤ} {n : ℕ} (hn : 2 < n)
    (hA : aeval A (cyclotomic n ℤ) = 0) (S : InvariantCPS A) : 2 ≤ finrank ℝ S.E := by
  have h1 := DimOne.one_le_finrank_E S
  have h2 := finrank_ne_one_of_invariant hn (aeval_act_cyclotomic hA) S.mapsTo_E
  omega

theorem act_pow_eq_one {A : Matrix ι ι ℤ} {n : ℕ} (hA : aeval (act A) (cyclotomic n ℝ) = 0) :
    act A ^ n = 1 := by
  obtain ⟨r, hr⟩ := cyclotomic.dvd_X_pow_sub_one n ℝ
  have h : aeval (act A) (X ^ n - 1 : ℝ[X]) = 0 := by rw [hr, map_mul, hA, zero_mul]
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h
  exact h

/-- A map of finite order is power-bounded. -/
theorem powerBounded_of_pow_eq_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {f : Module.End ℝ V} {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1) :
    ∃ C : ℝ, ∀ k : ℕ, ∀ v : V, ‖(f ^ k) v‖ ≤ C * ‖v‖ := by
  refine ⟨∑ j ∈ Finset.range n, ‖LinearMap.toContinuousLinearMap (f ^ j)‖, fun k v => ?_⟩
  have hk : f ^ k = f ^ (k % n) := by
    conv_lhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, hf, one_pow, one_mul]
  rw [hk]
  calc ‖(f ^ (k % n)) v‖ = ‖LinearMap.toContinuousLinearMap (f ^ (k % n)) v‖ := rfl
    _ ≤ ‖LinearMap.toContinuousLinearMap (f ^ (k % n))‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (∑ j ∈ Finset.range n, ‖LinearMap.toContinuousLinearMap (f ^ j)‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        exact Finset.single_le_sum (f := fun j => ‖LinearMap.toContinuousLinearMap (f ^ j)‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.2 (Nat.mod_lt k hn))

/-- **The places of `ℚ(ζ_n)` are complex for `n ≥ 3`.** Every irreducible real factor of `Φ_n`
has degree two. -/
theorem natDegree_eq_two_of_dvd_cyclotomic {n : ℕ} (hn : 2 < n) {q : ℝ[X]} (hq : Irreducible q)
    (hqΦ : q ∣ cyclotomic n ℝ) : q.natDegree = 2 := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hle : q.natDegree ≤ 2 := hq.natDegree_le_two
  have hne1 : q.natDegree ≠ 1 := by
    intro h1
    have hd : q.degree = 1 := by rw [degree_eq_natDegree hq0, h1, Nat.cast_one]
    obtain ⟨t, ht⟩ := exists_root_of_degree_eq_one hd
    obtain ⟨r, hr⟩ := hqΦ
    have := cyclotomic_pos hn t
    rw [hr, eval_mul, ht.eq_zero, zero_mul] at this
    exact lt_irrefl _ this
  have hne0 : q.natDegree ≠ 0 := by
    intro h0
    apply hq.not_isUnit
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hq0, h0, Nat.cast_zero]
  omega

/-- A real quadratic factor `q` of `Φ_n` (`n ≥ 3`), with cofactor `g` coprime to it. -/
theorem exists_quadratic_factor {n : ℕ} (hn : 2 < n) :
    ∃ q g : ℝ[X], q.Monic ∧ q.natDegree = 2 ∧ cyclotomic n ℝ = q * g ∧ IsCoprime q g ∧
      g ≠ 0 ∧ g.natDegree < (cyclotomic n ℝ).natDegree := by
  classical
  have hΦ0 : cyclotomic n ℝ ≠ 0 := (cyclotomic.monic n ℝ).ne_zero
  have hdegΦ : 0 < (cyclotomic n ℝ).natDegree := by
    rw [natDegree_cyclotomic]; exact Nat.totient_pos.mpr (by omega)
  have hnu : ¬ IsUnit (cyclotomic n ℝ) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hΦ0]
    exact_mod_cast hdegΦ.ne'
  obtain ⟨q₀, hq₀, hq₀Φ⟩ := WfDvdMonoid.exists_irreducible_factor hnu hΦ0
  have hq₀0 : q₀ ≠ 0 := hq₀.ne_zero
  have hqmon : (normalize q₀).Monic := Polynomial.monic_normalize hq₀0
  have hqirr : Irreducible (normalize q₀) := (associated_normalize q₀).irreducible hq₀
  have hqΦ : normalize q₀ ∣ cyclotomic n ℝ := (associated_normalize q₀).symm.dvd.trans hq₀Φ
  have hq2 := natDegree_eq_two_of_dvd_cyclotomic hn hqirr hqΦ
  obtain ⟨g, hg⟩ := hqΦ
  have hg0 : g ≠ 0 := by rintro rfl; rw [mul_zero] at hg; exact hΦ0 hg
  have : NeZero (n : ℝ) := ⟨by exact_mod_cast (show n ≠ 0 by omega)⟩
  refine ⟨normalize q₀, g, hqmon, hq2, hg, ?_, hg0, ?_⟩
  · have hsep := separable_cyclotomic n ℝ
    rw [hg] at hsep
    exact hsep.isCoprime
  · rw [hg, natDegree_mul hqmon.ne_zero hg0]; omega

theorem quadratic_eq {q : ℝ[X]} (hqmon : q.Monic) (hq2 : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  apply Polynomial.ext
  intro k
  rcases k with _ | _ | _ | k
  · simp
  · simp
  · have h := hqmon.coeff_natDegree
    rw [hq2] at h
    simp [h]
  · show q.coeff (k + 3) = (X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0)).coeff (k + 3)
    rw [coeff_eq_zero_of_natDegree_lt (show q.natDegree < k + 3 by omega)]
    simp

theorem aeval_quadratic_apply {V : Type*} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V)
    {q : ℝ[X]} (hqmon : q.Monic) (hq2 : q.natDegree = 2) (v : V) :
    aeval T q v = T (T v) + q.coeff 1 • T v + q.coeff 0 • v := by
  conv_lhs => rw [quadratic_eq hqmon hq2]
  simp only [map_add, map_mul, aeval_X, aeval_C, LinearMap.add_apply,
    Module.End.mul_apply, Module.algebraMap_end_apply, pow_two]

/-- **The semisimple collapse, `n ≥ 3`: a generic invariant plane.** If `Φ_n(A) = 0` with
`n ≥ 3`, there is an admissible `A`-invariant scheme with `dim E = 2`. The plane is
`E = span (e, A e)` for a generic `e` in the kernel of a real quadratic factor `q` of `Φ_n` (one
place of `ℚ(ζ_n)`), and `H` is cut out by a generic functional `θ ∘ g(A)` and its translate by
`A`, where `Φ_n = q g`. -/
theorem exists_scheme_of_cyclotomic [Nonempty ι] {A : Matrix ι ι ℤ} {n : ℕ} (hn : 2 < n)
    (hA : aeval A (cyclotomic n ℤ) = 0) :
    ∃ S : InvariantCPS A, S.Admissible ∧ finrank ℝ S.E = 2 := by
  have hn0 : 0 < n := by omega
  have hAR := aeval_act_cyclotomic hA
  have hAnil : IsNilpotent (aeval A (cyclotomic n ℤ)) := ⟨1, by rw [pow_one]; exact hA⟩
  obtain ⟨q, g, hqmon, hq2, hΦ, hcop, hg0, hgdeg⟩ := exists_quadratic_factor hn
  set T := act A with hT
  set G := aeval T g with hG
  have hqgT : aeval T q * aeval T g = 0 := by rw [← map_mul, ← hΦ]; exact hAR
  have hgqT : aeval T g * aeval T q = 0 := by rw [← map_mul, mul_comm, ← hΦ]; exact hAR
  have hqg : ∀ v, aeval T q (G v) = 0 := fun v => by
    rw [hG, ← Module.End.mul_apply, hqgT, LinearMap.zero_apply]
  have hgq : ∀ v, G (aeval T q v) = 0 := fun v => by
    rw [hG, ← Module.End.mul_apply, hgqT, LinearMap.zero_apply]
  set a := q.coeff 1 with ha
  set b := q.coeff 0 with hb
  have hqT : ∀ v, aeval T q v = T (T v) + a • T v + b • v := aeval_quadratic_apply T hqmon hq2
  -- the generic point `x`, `e = g(A) x`
  have hbadx : ∀ c : {c : ι → ℤ // c ≠ 0},
      LinearMap.ker (dotL (fun i => (c.1 i : ℝ)) ∘ₗ G) ≠ ⊤ := by
    intro c hc
    obtain ⟨x, hx⟩ := exists_dot_ne_zero hn0 hAnil hg0 hgdeg c.2
    apply hx
    have hmem : x ∈ LinearMap.ker (dotL (fun i => (c.1 i : ℝ)) ∘ₗ G) := by
      rw [hc]; exact Submodule.mem_top
    simpa using hmem
  obtain ⟨x, hxgen⟩ := exists_forall_notMem _ hbadx
  have hx : ∀ c : ι → ℤ, c ≠ 0 → (fun i => (c i : ℝ)) ⬝ᵥ G x ≠ 0 := by
    intro c hc h0
    exact hxgen ⟨c, hc⟩ (by simpa [LinearMap.mem_ker] using h0)
  set e := G x with he
  have he0 : e ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    intro h0
    apply hx (Pi.single i 1) (by
      intro h1; have := congrFun h1 i; simp at this)
    rw [h0, dotProduct_zero]
  have hqe : aeval T q e = 0 := hqg x
  have hGe : G e ≠ 0 := by
    obtain ⟨u, w, huw⟩ := hcop
    intro h0
    apply he0
    have h1 : aeval T (u * q + w * g) e = e := by rw [huw, map_one, Module.End.one_apply]
    rw [map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, hqe, ← hG, h0, map_zero, map_zero, zero_add] at h1
    exact h1.symm
  -- the generic functional `θ`
  let ys : Option {m : ι → ℤ // m ≠ 0} → (ι → ℝ) := fun o => match o with
    | none => G e
    | some m => G (fun i => (m.1 i : ℝ))
  have hys : ∀ o, ys o ≠ 0 := by
    rintro (_ | m)
    · exact hGe
    · intro h0
      have h1 := lattice_eq_zero_of_aeval hn0 hAnil hg0 hgdeg
        (mem_intLattice_iff.mpr ⟨m.1, rfl⟩) h0
      apply m.2
      funext i
      have := congrFun h1 i
      simpa using this
  obtain ⟨θ, hθ⟩ := exists_forall_notMem (fun o => LinearMap.ker (dotL (ys o)))
    (fun o => ker_dotL_ne_top (hys o))
  have hθe : θ ⬝ᵥ G e ≠ 0 := by
    intro h0; apply hθ none; rw [LinearMap.mem_ker, dotL_apply, dotProduct_comm]; exact h0
  have hθm : ∀ m : ι → ℤ, m ≠ 0 → θ ⬝ᵥ G (fun i => (m i : ℝ)) ≠ 0 := by
    intro m hm h0
    apply hθ (some ⟨m, hm⟩)
    rw [LinearMap.mem_ker, dotL_apply, dotProduct_comm]
    exact h0
  -- the subspaces
  set φ : (ι → ℝ) →ₗ[ℝ] ℝ := dotL θ ∘ₗ G with hφ
  have hφq : ∀ v, φ (T (T v)) + a * φ (T v) + b * φ v = 0 := by
    intro v
    have h0 : φ (aeval T q v) = 0 := by
      rw [hφ, LinearMap.comp_apply, hgq, map_zero]
    rw [hqT, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h0
    exact h0
  set L : ℝ × ℝ →ₗ[ℝ] (ι → ℝ) :=
    (LinearMap.toSpanSingleton ℝ _ e).coprod (LinearMap.toSpanSingleton ℝ _ (T e)) with hL
  have hLapp : ∀ s t : ℝ, L (s, t) = s • e + t • T e := fun s t => by
    simp [hL]
  set E : Submodule ℝ (ι → ℝ) := LinearMap.range L with hE
  set H : Submodule ℝ (ι → ℝ) := LinearMap.ker φ ⊓ LinearMap.ker (φ ∘ₗ T) with hH
  have heE : e ∈ E := LinearMap.mem_range.mpr ⟨(1, 0), by rw [hLapp]; simp⟩
  have heH : e ∉ H := by
    intro h
    apply hθe
    have := (Submodule.mem_inf.mp h).1
    rw [LinearMap.mem_ker, hφ, LinearMap.comp_apply, dotL_apply] at this
    exact this
  have hTTe : T (T e) = (-b) • e + (-a) • T e := by
    have h0 := hqT e
    rw [hqe] at h0
    calc T (T e) = (T (T e) + a • T e + b • e) + ((-b) • e + (-a) • T e) := by module
      _ = (-b) • e + (-a) • T e := by rw [← h0, zero_add]
  have hEinv : ∀ v ∈ E, T v ∈ E := by
    intro v hv
    obtain ⟨⟨s, t⟩, rfl⟩ := LinearMap.mem_range.mp hv
    refine LinearMap.mem_range.mpr ⟨(t * -b, s + t * -a), ?_⟩
    rw [hLapp, hLapp, map_add, map_smul, map_smul, hTTe]
    module
  have hHinv : ∀ v ∈ H, T v ∈ H := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    rw [LinearMap.mem_ker] at hv1
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hv2
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker]; exact hv2
    · rw [LinearMap.mem_ker, LinearMap.comp_apply]
      have := hφq v
      rw [hv1, hv2] at this
      linarith
  -- dimensions
  have hEle : finrank ℝ E ≤ 2 := by
    have := LinearMap.finrank_range_le L
    rw [Module.finrank_prod, Module.finrank_self, ← hE] at this
    omega
  have hE1 : finrank ℝ E ≠ 1 := finrank_ne_one_of_invariant hn hAR hEinv
  have hE0 : finrank ℝ E ≠ 0 := by
    intro h0
    have := Submodule.finrank_eq_zero.mp h0
    apply he0
    have h' : e ∈ (⊥ : Submodule ℝ (ι → ℝ)) := this ▸ heE
    exact (Submodule.mem_bot ℝ).mp h'
  have hE2 : finrank ℝ E = 2 := by omega
  have hHge : Fintype.card ι ≤ finrank ℝ H + 2 := by
    have hk : H = LinearMap.ker (φ.prod (φ ∘ₗ T)) := by rw [LinearMap.ker_prod]
    have hrn := LinearMap.finrank_range_add_finrank_ker (φ.prod (φ ∘ₗ T))
    have hr := Submodule.finrank_le (LinearMap.range (φ.prod (φ ∘ₗ T)))
    rw [Module.finrank_prod, Module.finrank_self] at hr
    rw [Module.finrank_fintype_fun_eq_card] at hrn
    rw [hk]
    omega
  have hdisj : Disjoint E H := by
    have hinv : ∀ v ∈ E ⊓ H, T v ∈ E ⊓ H := fun v hv =>
      Submodule.mem_inf.mpr ⟨hEinv v (Submodule.mem_inf.mp hv).1,
        hHinv v (Submodule.mem_inf.mp hv).2⟩
    have hlt : E ⊓ H < E := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro heq
      apply heH
      have : e ∈ E ⊓ H := by rw [heq]; exact heE
      exact (Submodule.mem_inf.mp this).2
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := finrank_ne_one_of_invariant hn hAR hinv
    have h3 : finrank ℝ ↥(E ⊓ H) = 0 := by omega
    rw [disjoint_iff]
    exact Submodule.finrank_eq_zero.mp h3
  have hcompl : IsCompl E H := by
    refine (Submodule.isCompl_iff_disjoint E H ?_).mpr hdisj
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  -- the lattice and density conditions
  have hinj : ∀ γ ∈ intLattice ι, γ ∈ H → γ = 0 := by
    intro γ hγ hγH
    obtain ⟨m, rfl⟩ := mem_intLattice_iff.mp hγ
    have h1 := (Submodule.mem_inf.mp hγH).1
    rw [LinearMap.mem_ker, hφ, LinearMap.comp_apply, dotL_apply] at h1
    by_cases hm : m = 0
    · funext i; simp [hm]
    · exact absurd h1 (hθm m hm)
  have hdense := dense_of_no_integral_functional hcompl (by
    intro f hf hfE
    obtain ⟨c, hc⟩ := exists_int_of_integral hf
    have h1 : (fun i => (c i : ℝ)) ⬝ᵥ e = 0 := by rw [← hc]; exact hfE e heE
    have hc0 : c = 0 := by
      by_contra hc0
      exact hx c hc0 h1
    apply LinearMap.ext
    intro v
    rw [hc v, hc0]
    simp [dotProduct])
  let S : InvariantCPS A :=
    { E := E, H := H, isCompl := hcompl, mapsTo_E := hEinv, mapsTo_H := hHinv, inj := hinj,
      dense := hdense }
  refine ⟨S, ?_, hE2⟩
  obtain ⟨C, hC⟩ := powerBounded_of_pow_eq_one (f := act A) hn0 (act_pow_eq_one hAR)
  exact (admissible_iff_powerBounded S).mpr ⟨C, fun k v _ => hC k v⟩

/-- **The semisimple collapse, `n ≤ 2`: a generic line.** If `A` acts as a scalar `s` with
`|s| = 1` (`A = ±1`), there is an admissible `A`-invariant scheme with `dim E = 1`. -/
theorem exists_scheme_of_scalar [Nonempty ι] {A : Matrix ι ι ℤ} {s : ℝ} (hs1 : s * s = 1)
    (hs : ∀ v, act A v = s • v) :
    ∃ S : InvariantCPS A, S.Admissible ∧ finrank ℝ S.E = 1 := by
  have hbadx : ∀ c : {c : ι → ℤ // c ≠ 0}, LinearMap.ker (dotL (fun i => (c.1 i : ℝ))) ≠ ⊤ := by
    intro c
    refine ker_dotL_ne_top ?_
    intro h0
    apply c.2
    funext i
    have := congrFun h0 i
    simpa using this
  obtain ⟨x, hxgen⟩ := exists_forall_notMem _ hbadx
  have hx : ∀ c : ι → ℤ, c ≠ 0 → (fun i => (c i : ℝ)) ⬝ᵥ x ≠ 0 := by
    intro c hc h0
    exact hxgen ⟨c, hc⟩ (by simpa [LinearMap.mem_ker] using h0)
  have hx0 : x ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    intro h0
    apply hx (Pi.single i 1) (by
      intro h1; have := congrFun h1 i; simp at this)
    rw [h0, dotProduct_zero]
  let ys : Option {m : ι → ℤ // m ≠ 0} → (ι → ℝ) := fun o => match o with
    | none => x
    | some m => fun i => (m.1 i : ℝ)
  have hys : ∀ o, ys o ≠ 0 := by
    rintro (_ | m)
    · exact hx0
    · intro h0
      apply m.2
      funext i
      have := congrFun h0 i
      simpa [ys] using this
  obtain ⟨θ, hθ⟩ := exists_forall_notMem (fun o => LinearMap.ker (dotL (ys o)))
    (fun o => ker_dotL_ne_top (hys o))
  have hθx : θ ⬝ᵥ x ≠ 0 := by
    intro h0; apply hθ none; rw [LinearMap.mem_ker, dotL_apply, dotProduct_comm]; exact h0
  have hθm : ∀ m : ι → ℤ, m ≠ 0 → θ ⬝ᵥ (fun i => (m i : ℝ)) ≠ 0 := by
    intro m hm h0
    apply hθ (some ⟨m, hm⟩)
    rw [LinearMap.mem_ker, dotL_apply, dotProduct_comm]
    exact h0
  set E : Submodule ℝ (ι → ℝ) := ℝ ∙ x with hE
  set H : Submodule ℝ (ι → ℝ) := LinearMap.ker (dotL θ) with hH
  have hE1 : finrank ℝ E = 1 := finrank_span_singleton hx0
  have hHge : Fintype.card ι ≤ finrank ℝ H + 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (dotL θ)
    have hr := Submodule.finrank_le (LinearMap.range (dotL θ))
    rw [Module.finrank_self] at hr
    rw [Module.finrank_fintype_fun_eq_card] at hrn
    rw [hH]
    omega
  have hdisj : Disjoint E H := by
    rw [Submodule.disjoint_def]
    intro v hvE hvH
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hvE
    rw [LinearMap.mem_ker, dotL_apply, dotProduct_smul, smul_eq_mul] at hvH
    rw [(mul_eq_zero.mp hvH).resolve_right hθx, zero_smul]
  have hcompl : IsCompl E H := by
    refine (Submodule.isCompl_iff_disjoint E H ?_).mpr hdisj
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  have hinv : ∀ (U : Submodule ℝ (ι → ℝ)), ∀ v ∈ U, act A v ∈ U := fun U v hv => by
    rw [hs]; exact U.smul_mem s hv
  have hinj : ∀ γ ∈ intLattice ι, γ ∈ H → γ = 0 := by
    intro γ hγ hγH
    obtain ⟨m, rfl⟩ := mem_intLattice_iff.mp hγ
    rw [LinearMap.mem_ker, dotL_apply] at hγH
    by_cases hm : m = 0
    · funext i; simp [hm]
    · exact absurd hγH (hθm m hm)
  have hdense := dense_of_no_integral_functional hcompl (by
    intro f hf hfE
    obtain ⟨c, hc⟩ := exists_int_of_integral hf
    have h1 : (fun i => (c i : ℝ)) ⬝ᵥ x = 0 := by
      rw [← hc]; exact hfE x (Submodule.mem_span_singleton_self x)
    have hc0 : c = 0 := by
      by_contra hc0
      exact hx c hc0 h1
    apply LinearMap.ext
    intro v
    rw [hc v, hc0]
    simp [dotProduct])
  let S : InvariantCPS A :=
    { E := E, H := H, isCompl := hcompl, mapsTo_E := hinv E, mapsTo_H := hinv H, inj := hinj,
      dense := hdense }
  refine ⟨S, ?_, hE1⟩
  have hpow : act A ^ 2 = 1 := by
    apply LinearMap.ext
    intro v
    rw [pow_two, Module.End.mul_apply, hs, hs, smul_smul, hs1, one_smul, Module.End.one_apply]
  obtain ⟨C, hC⟩ := powerBounded_of_pow_eq_one (f := act A) two_pos hpow
  exact (admissible_iff_powerBounded S).mpr ⟨C, fun k v _ => hC k v⟩

/-- **The semisimple collapse.** If `Φ_n(A) = 0`, i.e. `A` is semisimple with characteristic
polynomial a power `Φ_n^r` of a single cyclotomic polynomial, then the least physical dimension
is `δ_n`: `1` for `n ≤ 2` (`A = ±1`) and `2` for `n ≥ 3`, whatever the multiplicity `r`. -/
theorem isLeast_physDims_of_cyclotomic [Nonempty ι] (A : Matrix ι ι ℤ) (n : ℕ)
    (hA : aeval A (cyclotomic n ℤ) = 0) :
    IsLeast (physDims A) (if n ≤ 2 then 1 else 2) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [cyclotomic_zero, map_one] at hA
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrFun (congrFun hA i) i
    simp at this
  split_ifs with hn
  · have hs : ∃ s : ℝ, s * s = 1 ∧ ∀ v, act A v = s • v := by
      have h := aeval_act_cyclotomic hA
      have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      interval_cases n
      · refine ⟨1, one_mul 1, fun v => ?_⟩
        rw [cyclotomic_one, map_sub, aeval_X, map_one, sub_eq_zero] at h
        simp [h]
      · refine ⟨-1, by norm_num, fun v => ?_⟩
        rw [cyclotomic_two, map_add, aeval_X, map_one, add_eq_zero_iff_eq_neg] at h
        simp [h]
    obtain ⟨s, hs1, hs⟩ := hs
    obtain ⟨S, hS, hSE⟩ := exists_scheme_of_scalar hs1 hs
    refine ⟨⟨S, hS, hSE⟩, ?_⟩
    rintro d ⟨S', -, rfl⟩
    exact DimOne.one_le_finrank_E S'
  · push Not at hn
    obtain ⟨S, hS, hSE⟩ := exists_scheme_of_cyclotomic hn hA
    refine ⟨⟨S, hS, hSE⟩, ?_⟩
    rintro d ⟨S', -, rfl⟩
    exact two_le_finrank_E_of_cyclotomic hn hA S'

/-- The identity on `ℤ^ι` (`ι` nonempty) has least physical dimension `1`, for every rank. -/
theorem isLeast_physDims_one [Nonempty ι] : IsLeast (physDims (1 : Matrix ι ι ℤ)) 1 := by
  have h := isLeast_physDims_of_cyclotomic (1 : Matrix ι ι ℤ) 1 (by rw [cyclotomic_one]; simp)
  simpa using h

/-- `−1` on `ℤ^ι` (`ι` nonempty) has least physical dimension `1`, for every rank. -/
theorem isLeast_physDims_neg_one [Nonempty ι] : IsLeast (physDims (-1 : Matrix ι ι ℤ)) 1 := by
  have h := isLeast_physDims_of_cyclotomic (-1 : Matrix ι ι ℤ) 2 (by rw [cyclotomic_two]; simp)
  simpa using h

end Cyclotomic

/-! ### Unipotent matrices: the tilt in general -/

section Unipotent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A countable family of nonzero linear functionals avoids prescribed values at some point. -/
theorem exists_forall_apply_ne {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {α : Type*} [Countable α] (L : α → V →ₗ[ℝ] ℝ) (c : α → ℝ)
    (hL : ∀ a, L a ≠ 0) : ∃ x : V, ∀ a, L a x ≠ c a := by
  have hy : ∀ a, ∃ y, L a y = 1 := by
    intro a
    obtain ⟨y, hy⟩ : ∃ y, L a y ≠ 0 := by
      by_contra h
      push Not at h
      exact hL a (LinearMap.ext h)
    exact ⟨(L a y)⁻¹ • y, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  choose y hy using hy
  let s : α → AffineSubspace ℝ V := fun a =>
    AffineSubspace.mk' (c a • y a) (LinearMap.ker (L a))
  have hmem : ∀ a x, x ∈ s a ↔ L a x = c a := by
    intro a x
    show x ∈ AffineSubspace.mk' (c a • y a) (LinearMap.ker (L a)) ↔ _
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, map_smul, hy,
      smul_eq_mul, mul_one, sub_eq_zero]
  have hs : ∀ a, s a ≠ ⊤ := by
    intro a htop
    have h1 : (c a + 1) • y a ∈ s a := by rw [htop]; simp
    rw [hmem, map_smul, hy, smul_eq_mul, mul_one] at h1
    linarith
  obtain ⟨x, hx⟩ := exists_forall_notMem_affine s hs
  exact ⟨x, fun a h => hx a ((hmem a x).mpr h)⟩

/-- For a nilpotent `f` and `f v ≠ 0`, some `w = f^j v` has `f w ≠ 0` and `f (f w) = 0`. -/
theorem exists_pow_apply_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℝ V]
    {f : Module.End ℝ V} (hf : IsNilpotent f) {v : V} (hv : f v ≠ 0) :
    ∃ j : ℕ, f ((f ^ j) v) ≠ 0 ∧ f (f ((f ^ j) v)) = 0 := by
  classical
  obtain ⟨p, hp⟩ := hf
  have hex : ∃ m, (f ^ m) v = 0 := ⟨p, by rw [hp, LinearMap.zero_apply]⟩
  have hm0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_zero, Module.End.one_apply] at this
    exact hv (by rw [this, map_zero])
  have hm1 : Nat.find hex ≠ 1 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_one] at this
    exact hv this
  refine ⟨Nat.find hex - 2, ?_, ?_⟩
  · have h := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rwa [show Nat.find hex - 1 = (Nat.find hex - 2) + 1 by omega, pow_succ',
      Module.End.mul_apply] at h
  · have h := Nat.find_spec hex
    rwa [show Nat.find hex = (Nat.find hex - 2) + 1 + 1 by omega, pow_succ', pow_succ',
      Module.End.mul_apply, Module.End.mul_apply] at h

/-- **A power-bounded unipotent map is the identity.** If `f − 1` is nilpotent and `f` is
power-bounded on an invariant subspace `H`, then `f = 1` on `H`. -/
theorem sub_one_apply_eq_zero_of_bdd {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Module.End ℝ V} (hnil : IsNilpotent (f - 1)) {H : Submodule ℝ V}
    (hH : ∀ v ∈ H, f v ∈ H) {C : ℝ} (hC : ∀ m : ℕ, ∀ v ∈ H, ‖(f ^ m) v‖ ≤ C * ‖v‖) :
    ∀ v ∈ H, (f - 1) v = 0 := by
  intro v hv
  by_contra hne
  obtain ⟨j, hj1, hj2⟩ := exists_pow_apply_of_isNilpotent hnil hne
  set N := f - 1 with hN
  have hNapp : ∀ u, N u = f u - u := fun u => by
    rw [hN, LinearMap.sub_apply, Module.End.one_apply]
  have hNH : ∀ u ∈ H, N u ∈ H := fun u hu => by rw [hNapp]; exact H.sub_mem (hH u hu) hu
  have hpowH : ∀ k : ℕ, ∀ u ∈ H, (N ^ k) u ∈ H := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      rw [pow_succ', Module.End.mul_apply]
      exact hNH _ (ih u hu)
  set w := (N ^ j) v with hw
  have hwH : w ∈ H := hpowH j v hv
  have hf : ∀ u, f u = u + N u := fun u => by rw [hNapp]; abel
  have horbit : ∀ m : ℕ, (f ^ m) w = w + (m : ℝ) • N w := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, hf w, hf (N w), hj2, add_zero]
      push_cast
      module
  have hbound : ∀ m : ℕ, (m : ℝ) * ‖N w‖ ≤ (C + 1) * ‖w‖ := by
    intro m
    have h1 := hC m w hwH
    rw [horbit] at h1
    have h2 : ‖(m : ℝ) • N w‖ ≤ ‖w + (m : ℝ) • N w‖ + ‖w‖ := by
      calc ‖(m : ℝ) • N w‖ = ‖(w + (m : ℝ) • N w) - w‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖w + (m : ℝ) • N w‖ + ‖w‖ := norm_sub_le _ _
    rw [norm_smul, Real.norm_natCast] at h2
    linarith
  have hpos : 0 < ‖N w‖ := norm_pos_iff.mpr hj1
  obtain ⟨m, hm⟩ := exists_nat_gt ((C + 1) * ‖w‖ / ‖N w‖)
  have := hbound m
  rw [div_lt_iff₀ hpos] at hm
  linarith

theorem pow_apply_mem_of_mapsTo {V : Type*} [AddCommGroup V] [Module ℝ V] (f : Module.End ℝ V)
    {U : Submodule ℝ V} (hU : ∀ v ∈ U, f v ∈ U) (k : ℕ) : ∀ v ∈ U, (f ^ k) v ∈ U := by
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih =>
    intro v hv
    rw [pow_succ', Module.End.mul_apply]
    exact hU _ (ih v hv)

/-- **Lower bound, abstract form.** Let `f − 1` be nilpotent and `V = E ⊕ H` with both summands
`f`-invariant and `f` power-bounded on `H`. Then `H ⊆ ker (f − 1)`, `H` misses `im (f − 1)`, and
`dim H + dim (ker (f − 1) ∩ im (f − 1)) ≤ dim ker (f − 1)`. -/
theorem finrank_add_le_of_unipotent {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {f : Module.End ℝ V} (hnil : IsNilpotent (f - 1))
    {E H : Submodule ℝ V} (hc : IsCompl E H) (hE : ∀ v ∈ E, f v ∈ E) (hH : ∀ v ∈ H, f v ∈ H)
    {C : ℝ} (hC : ∀ m : ℕ, ∀ v ∈ H, ‖(f ^ m) v‖ ≤ C * ‖v‖) :
    finrank ℝ H + finrank ℝ ↥(LinearMap.ker (f - 1) ⊓ LinearMap.range (f - 1)) ≤
      finrank ℝ ↥(LinearMap.ker (f - 1)) := by
  set N := f - 1 with hN
  have hHK : H ≤ LinearMap.ker N := fun v hv =>
    LinearMap.mem_ker.mpr (sub_one_apply_eq_zero_of_bdd hnil hH hC v hv)
  have hNapp : ∀ u, N u = f u - u := fun u => by
    rw [hN, LinearMap.sub_apply, Module.End.one_apply]
  have hNE : ∀ v ∈ E, N v ∈ E := fun v hv => by
    rw [hNapp]; exact E.sub_mem (hE v hv) hv
  have hdisj : H ⊓ (LinearMap.ker N ⊓ LinearMap.range N) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvH, hv2⟩ := Submodule.mem_inf.mp hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp (Submodule.mem_inf.mp hv2).2
    have hu : u ∈ H ⊔ E := by rw [hc.symm.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨h, hh, e, he, rfl⟩ := Submodule.mem_sup.mp hu
    have hNh : N h = 0 := LinearMap.mem_ker.mp (hHK hh)
    rw [map_add, hNh, zero_add] at hvH ⊢
    exact (Submodule.mem_bot ℝ).mpr
      ((Submodule.disjoint_def.mp hc.disjoint) _ (hNE e he) hvH)
  have key := Submodule.finrank_sup_add_finrank_inf_eq H
    (LinearMap.ker N ⊓ LinearMap.range N)
  rw [hdisj, finrank_bot, add_zero] at key
  have hmono := Submodule.finrank_mono (sup_le hHK (inf_le_left :
    LinearMap.ker N ⊓ LinearMap.range N ≤ LinearMap.ker N))
  omega

/-- **Lower bound for unipotent `A`.** For an admissible scheme,
`dim H + dim (ker (A − 1) ∩ im (A − 1)) ≤ dim ker (A − 1)`. -/
theorem finrank_H_add_le {A : Matrix ι ι ℤ} (hnil : IsNilpotent (act A - 1)) (S : InvariantCPS A)
    (hS : S.Admissible) :
    finrank ℝ S.H + finrank ℝ ↥(LinearMap.ker (act A - 1) ⊓ LinearMap.range (act A - 1)) ≤
      finrank ℝ ↥(LinearMap.ker (act A - 1)) := by
  obtain ⟨C, hC⟩ := (admissible_iff_powerBounded S).mp hS
  exact finrank_add_le_of_unipotent hnil S.isCompl S.mapsTo_E S.mapsTo_H hC

/-- **The tilt, construction.** If `ker (A − 1)` meets `im (A − 1)` (no other hypothesis on the
integer matrix `A`), there is an admissible scheme with
`dim H = dim ker (A − 1) − dim (ker (A − 1) ∩ im (A − 1))`:
`H` is the graph over a complement `K'` of the socle `ker ∩ im` in `ker (A − 1)` of a generic
map into the socle (the size-one blocks tilted into the socle of the larger ones), and
`E = im (A − 1) ⊕` the graph over a complement `Q` of `ker + im` of a generic map into
`ker (A − 1)`. -/
theorem exists_scheme_of_ker_inf_range {A : Matrix ι ι ℤ}
    (hS0 : LinearMap.ker (act A - 1) ⊓ LinearMap.range (act A - 1) ≠ ⊥) :
    ∃ S : InvariantCPS A, S.Admissible ∧
      finrank ℝ S.H + finrank ℝ ↥(LinearMap.ker (act A - 1) ⊓ LinearMap.range (act A - 1)) =
        finrank ℝ ↥(LinearMap.ker (act A - 1)) := by
  classical
  set N := act A - 1 with hN
  set K := LinearMap.ker N with hK
  set R := LinearMap.range N with hR
  set Sd := K ⊓ R with hSd
  obtain ⟨C₁, hC₁⟩ := exists_isCompl Sd
  obtain ⟨Q, hQ⟩ := exists_isCompl (K ⊔ R)
  set K' := K ⊓ C₁ with hK'
  set PS := Sd.projection C₁ hC₁ with hPS
  have hNapp : ∀ v, N v = act A v - v := fun v => by
    rw [hN, LinearMap.sub_apply, Module.End.one_apply]
  have hKfix : ∀ v ∈ K, act A v = v := fun v hv => by
    have h1 := hNapp v
    rw [LinearMap.mem_ker.mp hv] at h1
    exact (sub_eq_zero.mp h1.symm)
  obtain ⟨s₀, hs₀, hs₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨j₀, hj₀'⟩ := Function.ne_iff.mp hs₀0
  have hj₀ : s₀ j₀ ≠ 0 := by simpa using hj₀'
  have hs₀K : s₀ ∈ K := (Submodule.mem_inf.mp hs₀).1
  have hs₀R : s₀ ∈ R := (Submodule.mem_inf.mp hs₀).2
  have hSdC : ∀ v, v ∈ Sd → v ∈ C₁ → v = 0 := fun v h1 h2 =>
    (Submodule.disjoint_def.mp hC₁.disjoint) v h1 h2
  have hK'K : ∀ a ∈ K', a ∈ K := fun a ha => (Submodule.mem_inf.mp ha).1
  have hK'C : ∀ a ∈ K', a ∈ C₁ := fun a ha => (Submodule.mem_inf.mp ha).2
  have hKRQ : ∀ v, v ∈ K ⊔ R → v ∈ Q → v = 0 := fun v h1 h2 =>
    (Submodule.disjoint_def.mp hQ.disjoint) v h1 h2
  have hKdec : Sd ⊔ K' = K := by
    rw [hK', inf_comm K C₁, ← sup_inf_assoc_of_le C₁ (inf_le_left : Sd ≤ K), hC₁.sup_eq_top,
      top_inf_eq]
  have hdimK' : finrank ℝ K' + finrank ℝ Sd = finrank ℝ K := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Sd K'
    have hbot : Sd ⊓ K' = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      exact (Submodule.mem_bot ℝ).mpr
        (hSdC v (Submodule.mem_inf.mp hv).1 (hK'C v (Submodule.mem_inf.mp hv).2))
    rw [hbot, finrank_bot, add_zero, hKdec] at h
    omega
  -- the generic tilt `μ` of the internal space
  let aγ : (ι → ℝ) → (ι → ℝ) := fun v => v - PS v
  have hbadμ : ∀ m : {m : ι → ℤ // aγ (fun i => (m i : ℝ)) ≠ 0},
      dotL (aγ (fun i => (m.1 i : ℝ))) ≠ 0 := by
    intro m h0
    have h1 := LinearMap.congr_fun h0 (aγ (fun i => (m.1 i : ℝ)))
    rw [dotL_apply, LinearMap.zero_apply, dotProduct_self_eq_zero] at h1
    exact m.2 h1
  obtain ⟨μ, hμ⟩ := exists_forall_apply_ne _
    (fun m : {m : ι → ℤ // aγ (fun i => (m i : ℝ)) ≠ 0} =>
      (PS (fun i => (m.1 i : ℝ))) j₀ / s₀ j₀) hbadμ
  set gH : ↥K' →ₗ[ℝ] (ι → ℝ) :=
    K'.subtype + (LinearMap.toSpanSingleton ℝ _ s₀) ∘ₗ (dotL μ) ∘ₗ K'.subtype with hgH
  have hgH_apply : ∀ a : ↥K', gH a = (a : ι → ℝ) + (μ ⬝ᵥ (a : ι → ℝ)) • s₀ := fun a => by
    simp [hgH]
  set H := LinearMap.range gH with hH
  -- the physical space: `im (A − 1)` plus a generic graph over `Q`
  have hQ0 : Q ≠ ⊥ := by
    intro hQbot
    apply hS0
    have h1 : K ⊔ R = ⊤ := by
      have := hQ.sup_eq_top
      rwa [hQbot, sup_bot_eq] at this
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq K R
    have h3 := LinearMap.finrank_range_add_finrank_ker N
    rw [← hR, ← hK] at h3
    rw [h1, finrank_top] at h2
    have h4 : finrank ℝ ↥(K ⊓ R) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h4
  obtain ⟨q₀, hq₀, hq₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  set ν₀ : ι → ℝ := (q₀ ⬝ᵥ q₀)⁻¹ • q₀ with hν₀
  have hνq : ν₀ ⬝ᵥ q₀ = 1 := by
    rw [hν₀, smul_dotProduct, smul_eq_mul,
      inv_mul_cancel₀ (by rwa [Ne, dotProduct_self_eq_zero])]
  have hbadκ : ∀ c : {c : ι → ℤ // ∃ k ∈ K, (fun i => (c i : ℝ)) ⬝ᵥ k ≠ 0},
      dotL (fun i => (c.1 i : ℝ)) ∘ₗ K.subtype ≠ 0 := by
    intro c h0
    obtain ⟨k, hk, hck⟩ := c.2
    apply hck
    have h1 := LinearMap.congr_fun h0 ⟨k, hk⟩
    simpa using h1
  obtain ⟨κ, hκ⟩ := exists_forall_apply_ne (V := ↥K) _
    (fun c : {c : ι → ℤ // ∃ k ∈ K, (fun i => (c i : ℝ)) ⬝ᵥ k ≠ 0} =>
      -((fun i => (c.1 i : ℝ)) ⬝ᵥ q₀)) hbadκ
  set gE : ↥Q →ₗ[ℝ] (ι → ℝ) :=
    Q.subtype + (LinearMap.toSpanSingleton ℝ _ (κ : ι → ℝ)) ∘ₗ (dotL ν₀) ∘ₗ Q.subtype with hgE
  have hgE_apply : ∀ q : ↥Q,
      gE q = (q : ι → ℝ) + (ν₀ ⬝ᵥ (q : ι → ℝ)) • (κ : ι → ℝ) := fun q => by
    simp [hgE]
  set E := R ⊔ LinearMap.range gE with hE
  have hRE : R ≤ E := le_sup_left
  have hgEmem : ∀ q : ↥Q, gE q ∈ E := fun q =>
    Submodule.mem_sup_right (LinearMap.mem_range_self gE q)
  have hHK : ∀ v ∈ H, v ∈ K := by
    intro v hv
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hv
    rw [hgH_apply]
    exact K.add_mem (hK'K _ a.2) (K.smul_mem _ hs₀K)
  -- complementarity
  have hdisj : Disjoint E H := by
    rw [Submodule.disjoint_def]
    intro v hvE hvH
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hvH
    obtain ⟨r, hr, w, hw, hrw⟩ := Submodule.mem_sup.mp hvE
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp hw
    rw [hgE_apply, hgH_apply] at hrw
    have hq : (q : ι → ℝ) = 0 := by
      apply hKRQ _ _ q.2
      have h1 : (q : ι → ℝ) = ((a : ι → ℝ) + (μ ⬝ᵥ (a : ι → ℝ)) • s₀ -
          (ν₀ ⬝ᵥ (q : ι → ℝ)) • (κ : ι → ℝ)) - r := by
        rw [← hrw]; abel
      rw [h1]
      refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.mem_sup_right hr)
      · exact Submodule.mem_sup_left (K.add_mem (hK'K _ a.2) (K.smul_mem _ hs₀K))
      · exact Submodule.mem_sup_left (K.smul_mem _ κ.2)
    rw [hq, dotProduct_zero, zero_smul, add_zero, add_zero] at hrw
    have haR : (a : ι → ℝ) ∈ R := by
      have h1 : (a : ι → ℝ) = r - (μ ⬝ᵥ (a : ι → ℝ)) • s₀ := by rw [hrw]; abel
      rw [h1]
      exact R.sub_mem hr (R.smul_mem _ hs₀R)
    have ha0 : (a : ι → ℝ) = 0 :=
      hSdC _ (Submodule.mem_inf.mpr ⟨hK'K _ a.2, haR⟩) (hK'C _ a.2)
    rw [hgH_apply, ha0, dotProduct_zero, zero_smul, add_zero]
  have hgHinj : Function.Injective gH := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, hgH_apply] at ha
    have hmem : (a : ι → ℝ) ∈ Sd := by
      have h1 : (a : ι → ℝ) = -((μ ⬝ᵥ (a : ι → ℝ)) • s₀) := eq_neg_of_add_eq_zero_left ha
      rw [h1]
      exact Sd.neg_mem (Sd.smul_mem _ hs₀)
    exact (Submodule.mem_bot ℝ).mpr (Subtype.ext (hSdC _ hmem (hK'C _ a.2)))
  have hgEinj : Function.Injective gE := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    rw [LinearMap.mem_ker, hgE_apply] at hq
    have hmem : (q : ι → ℝ) ∈ K ⊔ R := by
      have h1 : (q : ι → ℝ) = -((ν₀ ⬝ᵥ (q : ι → ℝ)) • (κ : ι → ℝ)) :=
        eq_neg_of_add_eq_zero_left hq
      rw [h1]
      exact Submodule.mem_sup_left (K.neg_mem (K.smul_mem _ κ.2))
    exact (Submodule.mem_bot ℝ).mpr (Subtype.ext (hKRQ _ hmem q.2))
  have hRgE : R ⊓ LinearMap.range gE = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwR, hw2⟩ := Submodule.mem_inf.mp hw
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp hw2
    rw [hgE_apply] at hwR
    have hmem : (q : ι → ℝ) ∈ K ⊔ R := by
      have h1 : (q : ι → ℝ) = ((q : ι → ℝ) + (ν₀ ⬝ᵥ (q : ι → ℝ)) • (κ : ι → ℝ)) -
          (ν₀ ⬝ᵥ (q : ι → ℝ)) • (κ : ι → ℝ) := by abel
      rw [h1]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hwR)
        (Submodule.mem_sup_left (K.smul_mem _ κ.2))
    have hq0 := hKRQ _ hmem q.2
    rw [Submodule.mem_bot, hgE_apply, hq0, dotProduct_zero, zero_smul, add_zero]
  have hdimH : finrank ℝ H = finrank ℝ K' := LinearMap.finrank_range_of_inj hgHinj
  have hdimE : finrank ℝ E = finrank ℝ R + finrank ℝ Q := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq R (LinearMap.range gE)
    rw [hRgE, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hgEinj] at h
    rw [hE]
    exact h
  have hdimQ : finrank ℝ ↥(K ⊔ R) + finrank ℝ Q = Fintype.card ι := by
    rw [Submodule.finrank_add_eq_of_isCompl hQ, Module.finrank_fintype_fun_eq_card]
  have hKR := Submodule.finrank_sup_add_finrank_inf_eq K R
  rw [← hSd] at hKR
  have hcompl : IsCompl E H := by
    refine (Submodule.isCompl_iff_disjoint E H ?_).mpr hdisj
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  -- the lattice misses `H`
  have hinj : ∀ γ ∈ intLattice ι, γ ∈ H → γ = 0 := by
    intro γ hγ hγH
    obtain ⟨m, rfl⟩ := mem_intLattice_iff.mp hγ
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hγH
    rw [hgH_apply] at ha
    have hPa : PS (a : ι → ℝ) = 0 :=
      (Submodule.projection_apply_eq_zero_iff hC₁).mpr (hK'C _ a.2)
    have hPs : PS s₀ = s₀ := Submodule.projection_apply_of_mem_left hC₁ hs₀
    have hPγ : PS (fun i => (m i : ℝ)) = (μ ⬝ᵥ (a : ι → ℝ)) • s₀ := by
      rw [← ha, map_add, map_smul, hPa, hPs, zero_add]
    have haγ : aγ (fun i => (m i : ℝ)) = (a : ι → ℝ) := by
      show (fun i => (m i : ℝ)) - PS (fun i => (m i : ℝ)) = a
      rw [hPγ, ← ha, add_sub_cancel_right]
    by_cases ha0 : (a : ι → ℝ) = 0
    · rw [← ha, ha0, dotProduct_zero, zero_smul, add_zero]
    · exfalso
      apply hμ ⟨m, by rw [haγ]; exact ha0⟩
      show aγ (fun i => (m i : ℝ)) ⬝ᵥ μ = PS (fun i => (m i : ℝ)) j₀ / s₀ j₀
      rw [haγ, hPγ, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hj₀, mul_one,
        dotProduct_comm]
  -- the projection of the lattice is dense in `H`
  have hdense := dense_of_no_integral_functional hcompl (by
    intro f hf hfE
    obtain ⟨c, hc⟩ := exists_int_of_integral hf
    set cR : ι → ℝ := fun i => (c i : ℝ) with hcR
    have hvan : ∀ v ∈ E, cR ⬝ᵥ v = 0 := fun v hv => by rw [← hc]; exact hfE v hv
    have hc0 : cR = 0 := by
      by_contra hc0
      by_cases hKc : ∃ k ∈ K, cR ⬝ᵥ k ≠ 0
      · have h1 := hκ ⟨c, hKc⟩
        have h2 := hvan _ (hgEmem ⟨q₀, hq₀⟩)
        rw [hgE_apply] at h2
        simp only [hνq, one_smul, dotProduct_add] at h2
        apply h1
        show cR ⬝ᵥ (κ : ι → ℝ) = -(cR ⬝ᵥ q₀)
        linarith
      · push Not at hKc
        have hRc : ∀ r ∈ R, cR ⬝ᵥ r = 0 := fun r hr => hvan r (hRE hr)
        have hQc : ∃ q ∈ Q, cR ⬝ᵥ q ≠ 0 := by
          by_contra hQc
          push Not at hQc
          apply hc0
          funext i
          have hall : ∀ v, cR ⬝ᵥ v = 0 := by
            intro v
            have hv : v ∈ (K ⊔ R) ⊔ Q := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
            obtain ⟨y, hy, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
            obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.mp hy
            rw [dotProduct_add, dotProduct_add, hKc k hk, hRc r hr, hQc q hq]
            simp
          have h3 := hall (Pi.single i 1)
          rw [dotProduct_single_one] at h3
          exact h3
        obtain ⟨q₁, hq₁, hcq₁⟩ := hQc
        apply hcq₁
        have h2 := hvan _ (hgEmem ⟨q₁, hq₁⟩)
        rw [hgE_apply, dotProduct_add, dotProduct_smul, hKc _ κ.2, smul_zero, add_zero] at h2
        exact h2
    apply LinearMap.ext
    intro v
    rw [hc v]
    show cR ⬝ᵥ v = 0
    rw [hc0, zero_dotProduct])
  -- invariance and admissibility
  have hEinv : ∀ v ∈ E, act A v ∈ E := by
    intro v hv
    have h1 : act A v = v + N v := by rw [hNapp]; abel
    rw [h1]
    exact E.add_mem hv (hRE (LinearMap.mem_range_self N v))
  have hHinv : ∀ v ∈ H, act A v ∈ H := fun v hv => by rw [hKfix v (hHK v hv)]; exact hv
  let S : InvariantCPS A :=
    { E := E, H := H, isCompl := hcompl, mapsTo_E := hEinv, mapsTo_H := hHinv, inj := hinj,
      dense := hdense }
  refine ⟨S, ?_, ?_⟩
  · refine (admissible_iff_powerBounded S).mpr ⟨1, fun k v hv => ?_⟩
    have hpow : (act A ^ k) v = v := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, hKfix v (hHK v hv)]
    rw [hpow, one_mul]
  · show finrank ℝ H + finrank ℝ Sd = finrank ℝ K
    omega

/-- `act` as a ring homomorphism. -/
def actHom : Matrix ι ι ℤ →+* Module.End ℝ (ι → ℝ) :=
  (Matrix.toLinAlgEquiv' (R := ℝ) (n := ι)).toRingEquiv.toRingHom.comp
    (Int.castRingHom ℝ).mapMatrix

theorem actHom_apply (A : Matrix ι ι ℤ) : actHom A = act A := rfl

theorem eq_one_of_act_eq_one {A : Matrix ι ι ℤ} (h : act A = 1) : A = 1 := by
  have h1 : A.map (Int.cast : ℤ → ℝ) = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    exact h
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply] at h2 ⊢ <;> exact_mod_cast h2

theorem ker_inf_range_ne_bot {A : Matrix ι ι ℤ} (hnil : IsNilpotent (act A - 1)) (hA : A ≠ 1) :
    LinearMap.ker (act A - 1) ⊓ LinearMap.range (act A - 1) ≠ ⊥ := by
  have hN0 : act A - 1 ≠ 0 := fun h => hA (eq_one_of_act_eq_one (sub_eq_zero.mp h))
  obtain ⟨v, hv⟩ : ∃ v, (act A - 1) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hN0 (LinearMap.ext h)
  obtain ⟨j, hj1, hj2⟩ := exists_pow_apply_of_isNilpotent hnil hv
  intro hbot
  apply hj1
  have hmem : (act A - 1) (((act A - 1) ^ j) v) ∈
      LinearMap.ker (act A - 1) ⊓ LinearMap.range (act A - 1) :=
    Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hj2, LinearMap.mem_range_self _ _⟩
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℝ).mp hmem

/-- **The tilt.** For a unipotent integer matrix `A ≠ 1` (`A − 1` nilpotent), the least physical
dimension is `#ι − (dim ker (A − 1) − dim (ker (A − 1) ∩ im (A − 1)))`. The subtracted number is
the number of Jordan blocks of size one, so the value is the total size of the Jordan blocks of
size `≥ 2`: the size-one blocks cost nothing once a larger block is present. -/
theorem isLeast_physDims_unipotent (A : Matrix ι ι ℤ) (hnil : IsNilpotent (A - 1)) (hA : A ≠ 1) :
    IsLeast (physDims A) (Fintype.card ι - (finrank ℝ ↥(LinearMap.ker (act A - 1)) -
      finrank ℝ ↥(LinearMap.ker (act A - 1) ⊓ LinearMap.range (act A - 1)))) := by
  have hnil' : IsNilpotent (act A - 1) := by
    rw [← actHom_apply, ← map_one actHom, ← map_sub]
    exact hnil.map actHom
  obtain ⟨S, hS, hSdim⟩ := exists_scheme_of_ker_inf_range (ker_inf_range_ne_bot hnil' hA)
  have hcard : ∀ S' : InvariantCPS A, finrank ℝ S'.E + finrank ℝ S'.H = Fintype.card ι :=
    fun S' => by
      rw [Submodule.finrank_add_eq_of_isCompl S'.isCompl, Module.finrank_fintype_fun_eq_card]
  refine ⟨⟨S, hS, ?_⟩, ?_⟩
  · have := hcard S
    omega
  · rintro d ⟨S', hS', rfl⟩
    have h1 := finrank_H_add_le hnil' S' hS'
    have := hcard S'
    omega

/-- `act` turns `−A` into `−act A`. -/
theorem act_neg (A : Matrix ι ι ℤ) : act (-A) = -act A := by
  rw [← actHom_apply, map_neg, actHom_apply]

theorem pow_neg_apply {V : Type*} [AddCommGroup V] [Module ℝ V] (f : Module.End ℝ V) (m : ℕ)
    (v : V) : ((-f) ^ m) v = (-1 : ℝ) ^ m • (f ^ m) v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LinearMap.neg_apply, map_smul, pow_succ' f,
      Module.End.mul_apply, pow_succ, mul_neg_one, neg_smul]

/-- An `A`-invariant scheme is a `(−A)`-invariant scheme. -/
def negScheme {A : Matrix ι ι ℤ} (S : InvariantCPS A) : InvariantCPS (-A) where
  E := S.E
  H := S.H
  isCompl := S.isCompl
  mapsTo_E := fun v hv => by
    rw [act_neg, LinearMap.neg_apply]; exact S.E.neg_mem (S.mapsTo_E v hv)
  mapsTo_H := fun v hv => by
    rw [act_neg, LinearMap.neg_apply]; exact S.H.neg_mem (S.mapsTo_H v hv)
  inj := S.inj
  dense := S.dense

theorem negScheme_admissible {A : Matrix ι ι ℤ} (S : InvariantCPS A) (hS : S.Admissible) :
    (negScheme S).Admissible := by
  obtain ⟨C, hC⟩ := (admissible_iff_powerBounded S).mp hS
  refine (admissible_iff_powerBounded (negScheme S)).mpr ⟨C, fun m v hv => ?_⟩
  rw [act_neg, pow_neg_apply, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hC m v hv

theorem physDims_subset_neg (A : Matrix ι ι ℤ) : physDims A ⊆ physDims (-A) := by
  rintro d ⟨S, hS, rfl⟩
  exact ⟨negScheme S, negScheme_admissible S hS, rfl⟩

/-- `A` and `−A` have the same physical dimensions. -/
theorem physDims_neg (A : Matrix ι ι ℤ) : physDims (-A) = physDims A := by
  apply le_antisymm
  · have h := physDims_subset_neg (-A)
    rwa [neg_neg] at h
  · exact physDims_subset_neg A

/-- **The tilt at `−1`.** For an integer matrix `A ≠ −1` with `A + 1` nilpotent, the least
physical dimension is `#ι − (dim ker (A + 1) − dim (ker (A + 1) ∩ im (A + 1)))`. -/
theorem isLeast_physDims_neg_unipotent (A : Matrix ι ι ℤ) (hnil : IsNilpotent (A + 1))
    (hA : A ≠ -1) :
    IsLeast (physDims A) (Fintype.card ι - (finrank ℝ ↥(LinearMap.ker (act A + 1)) -
      finrank ℝ ↥(LinearMap.ker (act A + 1) ⊓ LinearMap.range (act A + 1)))) := by
  have h := isLeast_physDims_unipotent (-A)
    (by rw [show -A - 1 = -(A + 1) by abel]; exact hnil.neg)
    (fun h1 => hA (by rw [← neg_neg A, h1]))
  rw [physDims_neg, show act (-A) - 1 = -(act A + 1) by rw [act_neg]; abel,
    LinearMap.ker_neg, LinearMap.range_neg] at h
  exact h

/-! ### A single cyclotomic factor with Jordan blocks: `Φ_n(A)` nilpotent -/

theorem isNilpotent_aeval_act {A : Matrix ι ι ℤ} {n : ℕ}
    (hnil : IsNilpotent (aeval A (cyclotomic n ℤ))) :
    IsNilpotent (aeval (act A) (cyclotomic n ℝ)) := by
  rw [← map_cyclotomic n (Int.castRingHom ℝ), aeval_act_map]
  exact hnil.map actHom

/-- **Reduction to the unipotent map `Aⁿ`.** If `Φ_n(A)` is nilpotent, then `Aⁿ − 1` is
nilpotent with the same kernel and image as `Φ_n(A)`. -/
theorem pow_sub_one_of_cyclotomic {V : Type*} [AddCommGroup V] [Module ℝ V]
    {T : Module.End ℝ V} {n : ℕ} (hn : 0 < n) (hnil : IsNilpotent (aeval T (cyclotomic n ℝ))) :
    IsNilpotent (T ^ n - 1) ∧
      LinearMap.ker (T ^ n - 1) = LinearMap.ker (aeval T (cyclotomic n ℝ)) ∧
      LinearMap.range (T ^ n - 1) = LinearMap.range (aeval T (cyclotomic n ℝ)) := by
  set P := aeval T (cyclotomic n ℝ) with hP
  obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one n ℝ
  have hsep : (X ^ n - C (1 : ℝ)).Separable :=
    separable_X_pow_sub_C 1 (by exact_mod_cast hn.ne') one_ne_zero
  rw [C_1, hh] at hsep
  have hcop : IsCoprime (cyclotomic n ℝ) h := hsep.isCoprime
  obtain ⟨k, hk⟩ := hnil
  obtain ⟨u, w, huw⟩ := hcop.pow_left (m := k)
  set Hh := aeval T h with hHh
  have hinvL : aeval T w * Hh = 1 := by
    have h1 := congrArg (aeval T) huw
    rw [map_add, map_mul, map_mul, map_pow, ← hP, hk, mul_zero, zero_add, map_one] at h1
    exact h1
  have hcwH : Commute (aeval T w) Hh := (Commute.all w h).map (aeval T)
  have hcPH : Commute P Hh := (Commute.all (cyclotomic n ℝ) h).map (aeval T)
  have hinvR : Hh * aeval T w = 1 := by rw [← hcwH.eq]; exact hinvL
  have hf : T ^ n - 1 = P * Hh := by
    have h1 := congrArg (aeval T) hh
    rw [map_sub, map_pow, aeval_X, map_one, map_mul] at h1
    exact h1
  have hHker : LinearMap.ker Hh = ⊥ := LinearMap.ker_eq_bot_of_inverse hinvL
  have hHrange : LinearMap.range Hh = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨aeval T w y, by rw [← Module.End.mul_apply, hinvR, Module.End.one_apply]⟩
  refine ⟨⟨k, by rw [hf, hcPH.mul_pow, hk, zero_mul]⟩, ?_, ?_⟩
  · rw [hf, hcPH.eq, Module.End.mul_eq_comp, LinearMap.ker_comp_of_ker_eq_bot _ hHker]
  · rw [hf, Module.End.mul_eq_comp, LinearMap.range_comp_of_range_eq_top _ hHrange]

/-- **Lower bound for a single cyclotomic factor.** If `Φ_n(A)` is nilpotent (`χ_A = Φ_nᵐ`),
every admissible scheme has
`dim H + dim (ker Φ_n(A) ∩ im Φ_n(A)) ≤ dim ker Φ_n(A)`. -/
theorem finrank_H_add_le_cyclotomic {A : Matrix ι ι ℤ} {n : ℕ} (hn : 0 < n)
    (hnil : IsNilpotent (aeval A (cyclotomic n ℤ))) (S : InvariantCPS A) (hS : S.Admissible) :
    finrank ℝ S.H + finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ)) ⊓
        LinearMap.range (aeval (act A) (cyclotomic n ℝ))) ≤
      finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ))) := by
  obtain ⟨hnil', hker, hrange⟩ := pow_sub_one_of_cyclotomic hn (isNilpotent_aeval_act hnil)
  obtain ⟨C, hC⟩ := (admissible_iff_powerBounded S).mp hS
  have key := finrank_add_le_of_unipotent hnil' S.isCompl
    (pow_apply_mem_of_mapsTo _ S.mapsTo_E n) (pow_apply_mem_of_mapsTo _ S.mapsTo_H n) (C := C)
    (fun m v hv => by rw [← pow_mul]; exact hC (n * m) v hv)
  rw [hker, hrange] at key
  exact key

/-- The lower bound for a single cyclotomic factor: if `Φ_n(A)` is nilpotent, every
admissible scheme has `dim E ≥ #ι − (dim ker Φ_n(A) − dim (ker Φ_n(A) ∩ im Φ_n(A)))`, i.e.
`dim E ≥ φ(n) · (total size of the Jordan blocks of size ≥ 2)`. -/
theorem le_physDims_cyclotomic {A : Matrix ι ι ℤ} {n : ℕ} (hn : 0 < n)
    (hnil : IsNilpotent (aeval A (cyclotomic n ℤ))) :
    ∀ d ∈ physDims A, Fintype.card ι -
      (finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ))) -
        finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ)) ⊓
          LinearMap.range (aeval (act A) (cyclotomic n ℝ)))) ≤ d := by
  rintro d ⟨S, hS, rfl⟩
  have h1 := finrank_H_add_le_cyclotomic hn hnil S hS
  have h2 := Submodule.finrank_add_eq_of_isCompl S.isCompl
  rw [Module.finrank_fintype_fun_eq_card] at h2
  omega

/-- **Blocks of size `≥ 2` count in full.** If `Φ_n(A)` is nilpotent and every Jordan block has
size `≥ 2` (`ker Φ_n(A) ⊆ im Φ_n(A)`), only the trivial scheme is admissible up to dimension:
the least physical dimension is `#ι`. -/
theorem isLeast_physDims_of_ker_le_range {A : Matrix ι ι ℤ} {n : ℕ} (hn : 0 < n)
    (hnil : IsNilpotent (aeval A (cyclotomic n ℤ)))
    (hle : LinearMap.ker (aeval (act A) (cyclotomic n ℝ)) ≤
      LinearMap.range (aeval (act A) (cyclotomic n ℝ))) :
    IsLeast (physDims A) (Fintype.card ι) := by
  refine ⟨⟨InvariantCPS.trivial A, InvariantCPS.trivial_admissible A, ?_⟩, ?_⟩
  · show finrank ℝ (⊤ : Submodule ℝ (ι → ℝ)) = _
    rw [finrank_top, Module.finrank_fintype_fun_eq_card]
  · intro d hd
    have h := le_physDims_cyclotomic hn hnil d hd
    rw [inf_eq_left.mpr hle, Nat.sub_self, Nat.sub_zero] at h
    exact h

end Unipotent

/-! ### The tilt at a complex place: `Φ_n(A)` nilpotent, `n ≥ 3` -/

section CyclotomicTilt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem aeval_act_cyclotomic_eq (A : Matrix ι ι ℤ) (n : ℕ) :
    aeval (act A) (cyclotomic n ℝ) = act (aeval A (cyclotomic n ℤ)) := by
  rw [← map_cyclotomic n (Int.castRingHom ℝ), aeval_act_map]
  rfl

theorem aeval_comm_apply {V : Type*} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V)
    (p : ℝ[X]) (v : V) : aeval T p (T v) = T (aeval T p v) := by
  have h : Commute (aeval T p) T := by
    have := (Commute.all p X).map (aeval T)
    rwa [aeval_X] at this
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply]

theorem aeval_comm_aeval_apply {V : Type*} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V)
    (p r : ℝ[X]) (v : V) : aeval T p (aeval T r v) = aeval T r (aeval T p v) := by
  rw [← Module.End.mul_apply, ((Commute.all p r).map (aeval T)).eq, Module.End.mul_apply]

theorem pow_apply_eq_self_of_cyclotomic {V : Type*} [AddCommGroup V] [Module ℝ V]
    {T : Module.End ℝ V} {n : ℕ} {v : V} (hv : aeval T (cyclotomic n ℝ) v = 0) :
    (T ^ n) v = v := by
  obtain ⟨r, hr⟩ := cyclotomic.dvd_X_pow_sub_one n ℝ
  have h : aeval T (X ^ n - 1 : ℝ[X]) v = 0 := by
    rw [hr, mul_comm, map_mul, Module.End.mul_apply, hv, map_zero]
  rw [map_sub, map_pow, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero] at h
  exact h

/-- No real eigenvector is killed by `Φ_n(T)`, `n ≥ 3`. -/
theorem eq_zero_of_eigen_cyclotomic {V : Type*} [AddCommGroup V] [Module ℝ V]
    {T : Module.End ℝ V} {n : ℕ} (hn : 2 < n) {x : V} (hx : aeval T (cyclotomic n ℝ) x = 0)
    {c : ℝ} (hTx : T x = c • x) : x = 0 := by
  by_contra hx0
  have heig : T.HasEigenvector c x := by
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨hTx, hx0⟩
  have h3 := Module.End.aeval_apply_of_hasEigenvector (p := cyclotomic n ℝ) heig
  rw [hx] at h3
  have h4 := (smul_eq_zero.mp h3.symm).resolve_right hx0
  exact (cyclotomic_pos hn c).ne' h4

/-- The average `(1/n) Σ_{j<n} T^{n-j} P T^j` of `P` over the group generated by `T`. -/
def avgProj {V : Type*} [AddCommGroup V] [Module ℝ V] (T P : Module.End ℝ V) (n : ℕ) :
    Module.End ℝ V :=
  (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, T ^ (n - j) * P * T ^ j

theorem avgProj_apply {V : Type*} [AddCommGroup V] [Module ℝ V] (T P : Module.End ℝ V) (n : ℕ)
    (v : V) :
    avgProj T P n v = (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, (T ^ (n - j)) (P ((T ^ j) v)) := by
  simp [avgProj, LinearMap.sum_apply, Module.End.mul_apply]

/-- **An invariant complement by averaging.** If `Tⁿ = 1` on `K ⊇ S`, `S` is `T`-invariant and
`P` is a projection onto `S`, the average of `P` is a projection onto `S` commuting with `T` on
`K`. -/
theorem avgProj_spec {V : Type*} [AddCommGroup V] [Module ℝ V] {T P : Module.End ℝ V} {n : ℕ}
    (hn : 0 < n) {S K : Submodule ℝ V} (hSK : S ≤ K) (hS : ∀ v ∈ S, T v ∈ S)
    (hKn : ∀ v ∈ K, (T ^ n) v = v) (hP : ∀ v, P v ∈ S) (hPS : ∀ v ∈ S, P v = v) :
    (∀ v, avgProj T P n v ∈ S) ∧ (∀ v ∈ S, avgProj T P n v = v) ∧
      (∀ v ∈ K, avgProj T P n (T v) = T (avgProj T P n v)) := by
  refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [avgProj_apply]
    exact S.smul_mem _ (S.sum_mem fun j _ => pow_apply_mem_of_mapsTo T hS _ _ (hP _))
  · rw [avgProj_apply]
    have hterm : ∀ j ∈ Finset.range n, (T ^ (n - j)) (P ((T ^ j) v)) = v := by
      intro j hj
      rw [hPS _ (pow_apply_mem_of_mapsTo T hS j v hv), ← Module.End.mul_apply, ← pow_add,
        Nat.sub_add_cancel (Finset.mem_range.mp hj).le, hKn v (hSK hv)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
      one_smul]
  · set g : ℕ → V := fun k => (T ^ (n + 1 - k)) (P ((T ^ k) v)) with hg
    have hPv : P v ∈ K := hSK (hP v)
    have h0n : g 0 = g n := by
      simp only [hg, Nat.sub_zero, pow_zero, Module.End.one_apply, Nat.add_sub_cancel_left,
        pow_one]
      rw [hKn v hv, pow_succ', Module.End.mul_apply, hKn _ hPv]
    have key : ∑ j ∈ Finset.range n, g (j + 1) = ∑ j ∈ Finset.range n, g j := by
      have h1 := Finset.sum_range_succ' g n
      have h2 := Finset.sum_range_succ g n
      rw [h1, h0n] at h2
      exact add_right_cancel h2
    rw [avgProj_apply, avgProj_apply, map_smul, map_sum]
    congr 1
    calc ∑ j ∈ Finset.range n, (T ^ (n - j)) (P ((T ^ j) (T v)))
        = ∑ j ∈ Finset.range n, g (j + 1) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hg]
          rw [show n + 1 - (j + 1) = n - j by omega, ← Module.End.mul_apply (T ^ j) T,
            ← pow_succ]
      _ = ∑ j ∈ Finset.range n, g j := key
      _ = ∑ j ∈ Finset.range n, T ((T ^ (n - j)) (P ((T ^ j) v))) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjn := Finset.mem_range.mp hj
          simp only [hg]
          rw [← Module.End.mul_apply T, ← pow_succ', show n - j + 1 = n + 1 - j by omega]

theorem eq_zero_of_act_eq_zero {M : Matrix ι ι ℤ} (h : act M = 0) : M = 0 := by
  have h1 : M.map (Int.cast : ℤ → ℝ) = 0 := by
    apply Matrix.toLin'.injective
    rw [map_zero]
    exact h
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply, Int.cast_eq_zero] at h2
  simpa using h2

/-- **The tilt at a complex place: the internal space.** Let `n ≥ 3` and `Φ_n(A)` nilpotent and
nonzero. There is an `A`-invariant subspace `H ⊆ ker Φ_n(A)` meeting neither `im Φ_n(A)` nor
`ℤ^ι` (except in `0`), with `dim H + dim (ker Φ_n(A) ∩ im Φ_n(A)) = dim ker Φ_n(A)`. It is the
graph, over an invariant complement of the socle `ker ∩ im` in `ker Φ_n(A)`, of a generic
`A`-equivariant map into the socle supported at one place of `ℚ(ζ_n)`. -/
theorem exists_internal_of_cyclotomic {A : Matrix ι ι ℤ} {n : ℕ} (hn : 2 < n)
    (hnil : IsNilpotent (aeval A (cyclotomic n ℤ))) (hne : aeval A (cyclotomic n ℤ) ≠ 0) :
    ∃ H : Submodule ℝ (ι → ℝ),
      H ≤ LinearMap.ker (aeval (act A) (cyclotomic n ℝ)) ∧
      Disjoint H (LinearMap.range (aeval (act A) (cyclotomic n ℝ))) ∧
      finrank ℝ H + finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ)) ⊓
          LinearMap.range (aeval (act A) (cyclotomic n ℝ))) =
        finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ))) ∧
      (∀ v ∈ H, act A v ∈ H) ∧ (∀ γ ∈ intLattice ι, γ ∈ H → γ = 0) := by
  classical
  have hn0 : 0 < n := by omega
  set T := act A with hT
  set P := aeval T (cyclotomic n ℝ) with hP
  have hPact : P = act (aeval A (cyclotomic n ℤ)) := aeval_act_cyclotomic_eq A n
  have hPnil : IsNilpotent P := isNilpotent_aeval_act hnil
  set K := LinearMap.ker P with hK
  set R := LinearMap.range P with hR
  set Sd := K ⊓ R with hSd
  have hcommP : ∀ (p : ℝ[X]) (v : ι → ℝ), P (aeval T p v) = aeval T p (P v) := fun p v =>
    aeval_comm_aeval_apply T _ p v
  have hpK : ∀ (p : ℝ[X]), ∀ v ∈ K, aeval T p v ∈ K := fun p v hv => by
    rw [LinearMap.mem_ker, hcommP, LinearMap.mem_ker.mp hv, map_zero]
  have hpR : ∀ (p : ℝ[X]), ∀ v ∈ R, aeval T p v ∈ R := fun p v hv => by
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
    exact ⟨aeval T p u, hcommP p u⟩
  have hpSd : ∀ (p : ℝ[X]), ∀ v ∈ Sd, aeval T p v ∈ Sd := fun p v hv =>
    Submodule.mem_inf.mpr ⟨hpK p v (Submodule.mem_inf.mp hv).1, hpR p v (Submodule.mem_inf.mp hv).2⟩
  have hTX : ∀ v, T v = aeval T (X : ℝ[X]) v := fun v => by rw [aeval_X]
  have hKinv : ∀ v ∈ K, T v ∈ K := fun v hv => by rw [hTX]; exact hpK X v hv
  have hSdinv : ∀ v ∈ Sd, T v ∈ Sd := fun v hv => by rw [hTX]; exact hpSd X v hv
  have hKn : ∀ v ∈ K, (T ^ n) v = v := fun v hv =>
    pow_apply_eq_self_of_cyclotomic (LinearMap.mem_ker.mp hv)
  -- a nonzero integer vector in the socle
  obtain ⟨s₀, hs₀lat, hs₀Sd, hs₀0⟩ : ∃ s₀ ∈ intLattice ι, s₀ ∈ Sd ∧ s₀ ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, P (Pi.single i 1) ≠ 0 := by
      by_contra h
      push Not at h
      apply hne
      apply eq_zero_of_act_eq_zero
      rw [← hPact]
      apply (Pi.basisFun ℝ ι).ext
      intro i
      rw [Pi.basisFun_apply, LinearMap.zero_apply]
      exact h i
    obtain ⟨j, hj1, hj2⟩ := exists_pow_apply_of_isNilpotent hPnil hi
    refine ⟨P ((P ^ j) (Pi.single i 1)), ?_, ?_, hj1⟩
    · rw [hPact]
      exact act_mem_intLattice _ (act_pow_mem_intLattice _ j
        (Submodule.subset_span ⟨i, by simp [Pi.basisFun_apply]⟩))
    · exact Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hj2, LinearMap.mem_range_self _ _⟩
  have hs₀K : s₀ ∈ K := (Submodule.mem_inf.mp hs₀Sd).1
  -- one place: a real quadratic factor `q` of `Φ_n`, and the projection to its component
  obtain ⟨q, g, hqmon, hq2, hΦ, hcop, hg0, hgdeg⟩ := exists_quadratic_factor hn
  obtain ⟨u, w, huw⟩ := hcop
  set πq := aeval T (w * g) with hπq
  have hqg : ∀ v ∈ K, aeval T q (πq v) = 0 := by
    intro v hv
    have h1 : aeval T q (πq v) = aeval T w (P v) := by
      rw [hπq, ← Module.End.mul_apply, ← map_mul, show q * (w * g) = w * (q * g) by ring, ← hΦ,
        map_mul, Module.End.mul_apply]
    rw [h1, LinearMap.mem_ker.mp hv, map_zero]
  have hgsplit : ∀ v ∈ K, v - πq v ∈ LinearMap.ker (aeval T g) := by
    intro v hv
    have h0 := congrArg (fun p => aeval T p v) huw
    simp only [map_add, LinearMap.add_apply, map_one, Module.End.one_apply] at h0
    have h1 : v - πq v = aeval T (u * q) v := (eq_sub_of_add_eq h0).symm
    rw [LinearMap.mem_ker, h1, ← Module.End.mul_apply, ← map_mul,
      show g * (u * q) = u * (q * g) by ring, ← hΦ, map_mul, Module.End.mul_apply,
      LinearMap.mem_ker.mp hv, map_zero]
  have hπT : ∀ v, πq (T v) = T (πq v) := fun v => aeval_comm_apply T _ v
  set s₁ := πq s₀ with hs₁
  have hs₁Sd : s₁ ∈ Sd := hpSd _ s₀ hs₀Sd
  have hqs₁ : aeval T q s₁ = 0 := hqg s₀ hs₀K
  have hs₁0 : s₁ ≠ 0 := by
    intro h0
    apply hs₀0
    have h1 := hgsplit s₀ hs₀K
    rw [show πq s₀ = 0 from h0, sub_zero] at h1
    exact lattice_eq_zero_of_aeval hn0 hnil hg0 hgdeg hs₀lat (LinearMap.mem_ker.mp h1)
  obtain ⟨j₀, hj₀'⟩ := Function.ne_iff.mp hs₁0
  have hj₀ : s₁ j₀ ≠ 0 := by simpa using hj₀'
  set b := q.coeff 1 with hb
  set c := q.coeff 0 with hc
  have hqT : ∀ v, aeval T q v = T (T v) + b • T v + c • v := aeval_quadratic_apply T hqmon hq2
  have hTT : ∀ x, aeval T q x = 0 → T (T x) = -(b • T x) - c • x := by
    intro x hx
    have h1 := hqT x
    rw [hx] at h1
    calc T (T x) = (T (T x) + b • T x + c • x) + (-(b • T x) - c • x) := by module
      _ = -(b • T x) - c • x := by rw [← h1, zero_add]
  set u₁ := T s₁ + b • s₁ with hu₁
  have hu₁Sd : u₁ ∈ Sd := Sd.add_mem (hSdinv _ hs₁Sd) (Sd.smul_mem _ hs₁Sd)
  have hTu₁ : T u₁ = -(c • s₁) := by
    rw [hu₁, map_add, map_smul, hTT s₁ hqs₁]
    module
  -- an invariant complement of the socle in `ker Φ_n(A)`
  obtain ⟨C₁, hC₁⟩ := exists_isCompl Sd
  set av := avgProj T (Sd.projection C₁ hC₁) n with hav
  obtain ⟨hav1, hav2, hav3⟩ := avgProj_spec hn0 (inf_le_left : Sd ≤ K) hSdinv hKn
    (fun v => Submodule.projection_apply_mem hC₁ v)
    (fun v hv => Submodule.projection_apply_of_mem_left hC₁ hv)
  set K' := K ⊓ LinearMap.ker av with hK'
  have hK'K : ∀ a ∈ K', a ∈ K := fun a ha => (Submodule.mem_inf.mp ha).1
  have hK'av : ∀ a ∈ K', av a = 0 := fun a ha =>
    LinearMap.mem_ker.mp (Submodule.mem_inf.mp ha).2
  have hK'Sd : ∀ a ∈ K', a ∈ Sd → a = 0 := fun a ha hs => by
    rw [← hav2 a hs, hK'av a ha]
  have hK'inv : ∀ a ∈ K', T a ∈ K' := fun a ha =>
    Submodule.mem_inf.mpr ⟨hKinv a (hK'K a ha),
      LinearMap.mem_ker.mpr (by rw [hav3 a (hK'K a ha), hK'av a ha, map_zero])⟩
  have hdimK' : finrank ℝ K' + finrank ℝ Sd = finrank ℝ K := by
    have hsup : K' ⊔ Sd = K := by
      apply le_antisymm (sup_le inf_le_left inf_le_left)
      intro v hv
      rw [Submodule.mem_sup]
      refine ⟨v - av v, Submodule.mem_inf.mpr ⟨K.sub_mem hv ((inf_le_left : Sd ≤ K) (hav1 v)),
        LinearMap.mem_ker.mpr ?_⟩, av v, hav1 v, sub_add_cancel v _⟩
      rw [map_sub, hav2 _ (hav1 v), sub_self]
    have hinf : K' ⊓ Sd = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      exact (Submodule.mem_bot ℝ).mpr
        (hK'Sd v (Submodule.mem_inf.mp hv).1 (Submodule.mem_inf.mp hv).2)
    have h := Submodule.finrank_sup_add_finrank_inf_eq K' Sd
    rw [hsup, hinf, finrank_bot, add_zero] at h
    omega
  -- the generic tilt
  let xγ : (ι → ℤ) → (ι → ℝ) := fun m => πq ((fun i => (m i : ℝ)) - av (fun i => (m i : ℝ)))
  let yγ : (ι → ℤ) → (ι → ℝ) := fun m => (u₁ j₀) • xγ m + (s₁ j₀) • T (xγ m)
  have hbad : ∀ m : {m : ι → ℤ // (fun i => (m i : ℝ)) ∈ K ∧ xγ m ≠ 0},
      dotL (yγ m.1) ≠ 0 := by
    intro m h0
    have hy : yγ m.1 = 0 := by
      have h1 := LinearMap.congr_fun h0 (yγ m.1)
      rwa [dotL_apply, LinearMap.zero_apply, dotProduct_self_eq_zero] at h1
    have hxK : xγ m.1 ∈ K := hpK _ _ (K.sub_mem m.2.1 ((inf_le_left : Sd ≤ K) (hav1 _)))
    have hh' : (s₁ j₀) • T (xγ m.1) = -((u₁ j₀) • xγ m.1) := eq_neg_of_add_eq_zero_right hy
    have hTx : T (xγ m.1) = (-((s₁ j₀)⁻¹ * u₁ j₀)) • xγ m.1 := by
      rw [neg_smul, ← smul_smul, ← smul_neg, ← hh', inv_smul_smul₀ hj₀]
    exact m.2.2 (eq_zero_of_eigen_cyclotomic hn (LinearMap.mem_ker.mp hxK) hTx)
  obtain ⟨θ, hθ⟩ := exists_forall_apply_ne _
    (fun m : {m : ι → ℤ // (fun i => (m i : ℝ)) ∈ K ∧ xγ m ≠ 0} =>
      av (fun i => (m.1 i : ℝ)) j₀) hbad
  set φL : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    (LinearMap.toSpanSingleton ℝ _ u₁) ∘ₗ (dotL θ) ∘ₗ πq +
      (LinearMap.toSpanSingleton ℝ _ s₁) ∘ₗ (dotL θ) ∘ₗ T ∘ₗ πq with hφL
  have hφ : ∀ v, φL v = (θ ⬝ᵥ πq v) • u₁ + (θ ⬝ᵥ T (πq v)) • s₁ := fun v => by
    simp [hφL]
  have hφSd : ∀ v, φL v ∈ Sd := fun v => by
    rw [hφ]; exact Sd.add_mem (Sd.smul_mem _ hu₁Sd) (Sd.smul_mem _ hs₁Sd)
  have hφT : ∀ v ∈ K, φL (T v) = T (φL v) := by
    intro v hv
    rw [hφ, hφ, hπT, map_add, map_smul, map_smul, hTT _ (hqg v hv), hTu₁, hu₁,
      dotProduct_sub, dotProduct_neg, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    module
  set gH : ↥K' →ₗ[ℝ] (ι → ℝ) := K'.subtype + φL ∘ₗ K'.subtype with hgH
  have hgH_apply : ∀ a : ↥K', gH a = (a : ι → ℝ) + φL a := fun a => by simp [hgH]
  set H := LinearMap.range gH with hH
  have hHK : ∀ v ∈ H, v ∈ K := by
    intro v hv
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hv
    rw [hgH_apply]
    exact K.add_mem (hK'K _ a.2) ((inf_le_left : Sd ≤ K) (hφSd _))
  have hgHinj : Function.Injective gH := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, hgH_apply] at ha
    have hmem : (a : ι → ℝ) ∈ Sd := by
      rw [eq_neg_of_add_eq_zero_left ha]
      exact Sd.neg_mem (hφSd _)
    exact (Submodule.mem_bot ℝ).mpr (Subtype.ext (hK'Sd _ a.2 hmem))
  refine ⟨H, fun v hv => hHK v hv, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hvH hvR
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hvH
    rw [hgH_apply] at hvR ⊢
    have haR : (a : ι → ℝ) ∈ R := by
      have h1 : (a : ι → ℝ) = ((a : ι → ℝ) + φL a) - φL a := by abel
      rw [h1]
      exact R.sub_mem hvR ((inf_le_right : Sd ≤ R) (hφSd _))
    have ha0 := hK'Sd _ a.2 (Submodule.mem_inf.mpr ⟨hK'K _ a.2, haR⟩)
    rw [ha0, map_zero, add_zero]
  · rw [LinearMap.finrank_range_of_inj hgHinj]
    exact hdimK'
  · intro v hv
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hv
    refine LinearMap.mem_range.mpr ⟨⟨T a, hK'inv _ a.2⟩, ?_⟩
    rw [hgH_apply, hgH_apply, map_add, hφT _ (hK'K _ a.2)]
  · intro γ hγ hγH
    obtain ⟨m, rfl⟩ := mem_intLattice_iff.mp hγ
    have hγK := hHK _ hγH
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hγH
    rw [hgH_apply] at ha
    have havγ : av (fun i => (m i : ℝ)) = φL a := by
      rw [← ha, map_add, hK'av _ a.2, zero_add, hav2 _ (hφSd _)]
    have haγ : (a : ι → ℝ) = (fun i => (m i : ℝ)) - av (fun i => (m i : ℝ)) := by
      rw [havγ, ← ha, add_sub_cancel_right]
    by_cases hx : xγ m = 0
    · have hπa : πq (a : ι → ℝ) = 0 := by rw [haγ]; exact hx
      have hφa : φL a = 0 := by rw [hφ, hπa, map_zero, dotProduct_zero, zero_smul, zero_smul,
        add_zero]
      have hγa : (fun i => (m i : ℝ)) = a := by rw [← ha, hφa, add_zero]
      have hπγ : πq (fun i => (m i : ℝ)) = 0 := by rw [hγa]; exact hπa
      have h1 := hgsplit _ hγK
      rw [hπγ, sub_zero] at h1
      exact lattice_eq_zero_of_aeval hn0 hnil hg0 hgdeg hγ (LinearMap.mem_ker.mp h1)
    · exfalso
      apply hθ ⟨m, hγK, hx⟩
      show yγ m ⬝ᵥ θ = av (fun i => (m i : ℝ)) j₀
      have hπa : πq (a : ι → ℝ) = xγ m := by rw [haγ]
      rw [havγ, hφ, hπa]
      simp only [yγ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_dotProduct, smul_dotProduct]
      rw [dotProduct_comm (xγ m) θ, dotProduct_comm (T (xγ m)) θ]
      ring

end CyclotomicTilt

/-! ### Duality and the physical space of the tilt -/

section TiltDuality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dot-product orthogonal `{v | ∀ u ∈ U, u ⬝ᵥ v = 0}` of a subspace of `ℝ^ι`. -/
def dotOrth (U : Submodule ℝ (ι → ℝ)) : Submodule ℝ (ι → ℝ) where
  carrier := {v | ∀ u ∈ U, u ⬝ᵥ v = 0}
  add_mem' := fun {a b} ha hb u hu => by rw [dotProduct_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => dotProduct_zero u
  smul_mem' := fun r v hv u hu => by rw [dotProduct_smul, hv u hu, smul_zero]

omit [DecidableEq ι] in
theorem mem_dotOrth {U : Submodule ℝ (ι → ℝ)} {v : ι → ℝ} :
    v ∈ dotOrth U ↔ ∀ u ∈ U, u ⬝ᵥ v = 0 := Iff.rfl

theorem toDual_eq_dotL (v : ι → ℝ) : (Pi.basisFun ℝ ι).toDual v = dotL v := by
  apply (Pi.basisFun ℝ ι).ext
  intro i
  rw [Basis.toDual_apply_left, Pi.basisFun_repr, Pi.basisFun_apply, dotL_apply,
    dotProduct_single_one]

theorem finrank_dotOrth (U : Submodule ℝ (ι → ℝ)) :
    finrank ℝ (dotOrth U) + finrank ℝ U = Fintype.card ι := by
  have hc : dotOrth U = U.dualAnnihilator.comap
      ((Pi.basisFun ℝ ι).toDualEquiv : (ι → ℝ) →ₗ[ℝ] Module.Dual ℝ (ι → ℝ)) := by
    ext v
    rw [mem_dotOrth, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    simp only [LinearEquiv.coe_coe, Basis.toDualEquiv_apply, toDual_eq_dotL, dotL_apply]
    constructor
    · intro h u hu
      rw [dotProduct_comm]
      exact h u hu
    · intro h u hu
      rw [dotProduct_comm]
      exact h u hu
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  rw [hc, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  rw [Module.finrank_fintype_fun_eq_card] at h1
  omega

omit [DecidableEq ι] in
theorem le_dotOrth_dotOrth (U : Submodule ℝ (ι → ℝ)) : U ≤ dotOrth (dotOrth U) := by
  intro v hv w hw
  rw [dotProduct_comm]
  exact hw v hv

theorem dotOrth_dotOrth (U : Submodule ℝ (ι → ℝ)) : dotOrth (dotOrth U) = U := by
  refine (Submodule.eq_of_le_of_finrank_eq (le_dotOrth_dotOrth U) ?_).symm
  have h1 := finrank_dotOrth U
  have h2 := finrank_dotOrth (dotOrth U)
  omega

omit [DecidableEq ι] in
theorem dotOrth_inf (U W : Submodule ℝ (ι → ℝ)) :
    dotOrth U ⊓ dotOrth W = dotOrth (U ⊔ W) := by
  ext v
  rw [Submodule.mem_inf, mem_dotOrth, mem_dotOrth, mem_dotOrth]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [add_dotProduct, h1 y hy, h2 z hz, add_zero]
  · intro h
    exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
      fun u hu => h u (Submodule.mem_sup_right hu)⟩

theorem act_transpose_dot (M : Matrix ι ι ℤ) (θ v : ι → ℝ) :
    act Mᵀ θ ⬝ᵥ v = θ ⬝ᵥ act M v := by
  rw [act, act, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.transpose_map,
    Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

theorem aeval_transpose_int (M : Matrix ι ι ℤ) (f : ℤ[X]) : aeval Mᵀ f = (aeval M f)ᵀ := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.transpose_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_smul, Matrix.transpose_pow]

/-- A map that is the identity after `n` steps on a subspace is power-bounded there. -/
theorem powerBounded_of_pow_apply_eq_self {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {f : Module.End ℝ V} {n : ℕ} (hn : 0 < n) {U : Submodule ℝ V}
    (hf : ∀ v ∈ U, (f ^ n) v = v) :
    ∃ C : ℝ, ∀ k : ℕ, ∀ v ∈ U, ‖(f ^ k) v‖ ≤ C * ‖v‖ := by
  refine ⟨∑ j ∈ Finset.range n, ‖LinearMap.toContinuousLinearMap (f ^ j)‖, fun k v hv => ?_⟩
  have hiter : ∀ q : ℕ, ((f ^ n) ^ q) v = v := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [pow_succ, Module.End.mul_apply, hf v hv, ih]
  have hk : (f ^ k) v = (f ^ (k % n)) v := by
    conv_lhs => rw [← Nat.div_add_mod k n, add_comm, pow_add, pow_mul, Module.End.mul_apply,
      hiter]
  rw [hk]
  calc ‖(f ^ (k % n)) v‖ = ‖LinearMap.toContinuousLinearMap (f ^ (k % n)) v‖ := rfl
    _ ≤ ‖LinearMap.toContinuousLinearMap (f ^ (k % n))‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (∑ j ∈ Finset.range n, ‖LinearMap.toContinuousLinearMap (f ^ j)‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        exact Finset.single_le_sum (f := fun j => ‖LinearMap.toContinuousLinearMap (f ^ j)‖)
          (fun j _ => norm_nonneg _) (Finset.mem_range.2 (Nat.mod_lt k hn))

/-- **The tilt at a complex place.** Let `n ≥ 3` and `Φ_n(A)` nilpotent and nonzero (`χ_A = Φ_nᵐ`
with at least one Jordan block of size `≥ 2`). The least physical dimension is
`#ι − (dim ker Φ_n(A) − dim (ker Φ_n(A) ∩ im Φ_n(A)))`: `φ(n)` times the total size of the Jordan
blocks of size `≥ 2` at each primitive `n`-th root of unity; the blocks of size one cost nothing.
The internal space is the tilted graph of `exists_internal_of_cyclotomic`; the physical space is
the dot-product orthogonal of the same construction for `Aᵀ`. -/
theorem isLeast_physDims_cyclotomic_tilt {A : Matrix ι ι ℤ} {n : ℕ} (hn : 2 < n)
    (hnil : IsNilpotent (aeval A (cyclotomic n ℤ))) (hne : aeval A (cyclotomic n ℤ) ≠ 0) :
    IsLeast (physDims A) (Fintype.card ι -
      (finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ))) -
        finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ)) ⊓
          LinearMap.range (aeval (act A) (cyclotomic n ℝ))))) := by
  classical
  have hn0 : 0 < n := by omega
  refine ⟨?_, le_physDims_cyclotomic hn0 hnil⟩
  have hnilT : IsNilpotent (aeval Aᵀ (cyclotomic n ℤ)) := by
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [aeval_transpose_int, ← Matrix.transpose_pow, hk, Matrix.transpose_zero]⟩
  have hneT : aeval Aᵀ (cyclotomic n ℤ) ≠ 0 := by
    rw [aeval_transpose_int]
    intro h
    apply hne
    rw [← Matrix.transpose_transpose (aeval A (cyclotomic n ℤ)), h, Matrix.transpose_zero]
  obtain ⟨H, hHK, hHR, hHdim, hHinv, hHlat⟩ := exists_internal_of_cyclotomic hn hnil hne
  obtain ⟨F, hFK, hFR, hFdim, hFinv, hFlat⟩ := exists_internal_of_cyclotomic hn hnilT hneT
  set T := act A with hT
  set P := aeval T (cyclotomic n ℝ) with hP
  set PT := aeval (act Aᵀ) (cyclotomic n ℝ) with hPT
  have hPeq : P = act (aeval A (cyclotomic n ℤ)) := aeval_act_cyclotomic_eq A n
  have hPTeq : PT = act (aeval A (cyclotomic n ℤ))ᵀ := by
    rw [hPT, aeval_act_cyclotomic_eq, aeval_transpose_int]
  have hdotP : ∀ θ v, PT θ ⬝ᵥ v = θ ⬝ᵥ P v := fun θ v => by
    rw [hPTeq, hPeq]; exact act_transpose_dot _ θ v
  have hdotT : ∀ θ v, act Aᵀ θ ⬝ᵥ v = θ ⬝ᵥ T v := fun θ v => act_transpose_dot A θ v
  set K := LinearMap.ker P with hK
  set R := LinearMap.range P with hR
  set KT := LinearMap.ker PT with hKT
  set RT := LinearMap.range PT with hRT
  have hKT_eq : KT = dotOrth R := by
    ext θ
    rw [LinearMap.mem_ker, mem_dotOrth]
    constructor
    · intro h u hu
      obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hu
      rw [dotProduct_comm, ← hdotP, h, zero_dotProduct]
    · intro h
      funext i
      have h1 := h (P (Pi.single i 1)) (LinearMap.mem_range_self _ _)
      rw [dotProduct_comm, ← hdotP, dotProduct_single_one] at h1
      simpa using h1
  have hdimR : finrank ℝ K + finrank ℝ R = Fintype.card ι := by
    have h1 := LinearMap.finrank_range_add_finrank_ker P
    rw [Module.finrank_fintype_fun_eq_card, ← hK, ← hR] at h1
    omega
  have hdimKT : finrank ℝ KT + finrank ℝ R = Fintype.card ι := by
    rw [hKT_eq]; exact finrank_dotOrth R
  have hRT_eq : RT = dotOrth K := by
    apply Submodule.eq_of_le_of_finrank_eq
    · intro θ hθ u hu
      obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hθ
      rw [dotProduct_comm, hdotP, LinearMap.mem_ker.mp hu, dotProduct_zero]
    · have h1 := LinearMap.finrank_range_add_finrank_ker PT
      rw [Module.finrank_fintype_fun_eq_card, ← hKT, ← hRT] at h1
      have h2 := finrank_dotOrth K
      omega
  have hdimSdT : finrank ℝ ↥(KT ⊓ RT) + finrank ℝ ↥(K ⊔ R) = Fintype.card ι := by
    rw [hKT_eq, hRT_eq, inf_comm, dotOrth_inf]
    exact finrank_dotOrth _
  have hKR := Submodule.finrank_sup_add_finrank_inf_eq K R
  -- the physical space
  set E := dotOrth F with hE
  have hdimE : finrank ℝ E + finrank ℝ F = Fintype.card ι := finrank_dotOrth F
  have hEinv : ∀ v ∈ E, T v ∈ E := by
    intro v hv f hf
    rw [← hdotT]
    exact hv _ (hFinv f hf)
  have hFsup : F ⊔ (KT ⊓ RT) = KT := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hFK inf_le_left)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq F (KT ⊓ RT)
    have h2 : F ⊓ (KT ⊓ RT) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      exact (Submodule.mem_bot ℝ).mpr ((Submodule.disjoint_def.mp hFR) v
        (Submodule.mem_inf.mp hv).1 (Submodule.mem_inf.mp (Submodule.mem_inf.mp hv).2).2)
    rw [h2, finrank_bot, add_zero] at h1
    omega
  have hEK : ∀ v ∈ E, v ∈ K → v ∈ R := by
    intro v hvE hvK
    have h1 : v ∈ dotOrth KT := by
      intro θ hθ
      rw [← hFsup] at hθ
      obtain ⟨f, hf, s, hs, rfl⟩ := Submodule.mem_sup.mp hθ
      obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp (Submodule.mem_inf.mp hs).2
      rw [add_dotProduct, hvE f hf, hdotP, LinearMap.mem_ker.mp hvK, dotProduct_zero, add_zero]
    rw [hKT_eq, dotOrth_dotOrth] at h1
    exact h1
  have hdisj : Disjoint E H := by
    rw [Submodule.disjoint_def]
    intro v hvE hvH
    exact (Submodule.disjoint_def.mp hHR) v hvH (hEK v hvE (hHK hvH))
  have hcompl : IsCompl E H := by
    refine (Submodule.isCompl_iff_disjoint E H ?_).mpr hdisj
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  have hdense := dense_of_no_integral_functional hcompl (by
    intro f hf hfE
    obtain ⟨c, hc⟩ := exists_int_of_integral hf
    have hcF : (fun i => (c i : ℝ)) ∈ F := by
      rw [← dotOrth_dotOrth F]
      intro v hv
      rw [dotProduct_comm, ← hc]
      exact hfE v hv
    have hc0 := hFlat _ (mem_intLattice_iff.mpr ⟨c, rfl⟩) hcF
    apply LinearMap.ext
    intro v
    rw [hc v, hc0, zero_dotProduct, LinearMap.zero_apply])
  let S : InvariantCPS A :=
    { E := E, H := H, isCompl := hcompl, mapsTo_E := hEinv, mapsTo_H := hHinv, inj := hHlat,
      dense := hdense }
  refine ⟨S, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := powerBounded_of_pow_apply_eq_self (f := act A) hn0 (U := H)
      (fun v hv => pow_apply_eq_self_of_cyclotomic (LinearMap.mem_ker.mp (hHK hv)))
    exact (admissible_iff_powerBounded S).mpr ⟨C, hC⟩
  · show finrank ℝ E = _
    have h3 := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [Module.finrank_fintype_fun_eq_card] at h3
    omega

/-- **The least physical dimension for a single cyclotomic factor.** Let `Φ_n(A)` be nilpotent
(`χ_A = Φ_nᵐ`, all eigenvalues primitive `n`-th roots of unity) and `ι` nonempty. If `A` is
semisimple (`Φ_n(A) = 0`) the least physical dimension is `δ_n` (`1` for `n ≤ 2`, `2` for `n ≥ 3`);
otherwise it is `#ι − (dim ker Φ_n(A) − dim (ker Φ_n(A) ∩ im Φ_n(A)))`, i.e. `φ(n)` times the
total size of the Jordan blocks of size `≥ 2` at each primitive `n`-th root of unity. -/
theorem isLeast_physDims_single_cyclotomic [Nonempty ι] (A : Matrix ι ι ℤ) {n : ℕ} (hn : 0 < n)
    (hnil : IsNilpotent (aeval A (cyclotomic n ℤ))) :
    IsLeast (physDims A)
      (if aeval A (cyclotomic n ℤ) = 0 then (if n ≤ 2 then 1 else 2) else
        Fintype.card ι - (finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ))) -
          finrank ℝ ↥(LinearMap.ker (aeval (act A) (cyclotomic n ℝ)) ⊓
            LinearMap.range (aeval (act A) (cyclotomic n ℝ))))) := by
  by_cases h0 : aeval A (cyclotomic n ℤ) = 0
  · simp only [h0, ↓reduceIte]
    exact isLeast_physDims_of_cyclotomic A n h0
  · simp only [h0, ↓reduceIte]
    rcases (show n = 1 ∨ n = 2 ∨ 2 < n by omega) with rfl | rfl | h3
    · have hA : aeval A (cyclotomic 1 ℤ) = A - 1 := by
        rw [cyclotomic_one, map_sub, aeval_X, map_one]
      have hP : aeval (act A) (cyclotomic 1 ℝ) = act A - 1 := by
        rw [cyclotomic_one, map_sub, aeval_X, map_one]
      rw [hA] at hnil h0
      rw [hP]
      exact isLeast_physDims_unipotent A hnil (fun h => h0 (by rw [h, sub_self]))
    · have hA : aeval A (cyclotomic 2 ℤ) = A + 1 := by
        rw [cyclotomic_two, map_add, aeval_X, map_one]
      have hP : aeval (act A) (cyclotomic 2 ℝ) = act A + 1 := by
        rw [cyclotomic_two, map_add, aeval_X, map_one]
      rw [hA] at hnil h0
      rw [hP]
      exact isLeast_physDims_neg_unipotent A hnil (fun h => h0 (by rw [h, neg_add_cancel]))
    · exact isLeast_physDims_cyclotomic_tilt h3 hnil h0

end TiltDuality

/-! ### The semisimple penalty, componentwise, for an arbitrary integer matrix -/

section ComponentBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An invariant splitting `V = E ⊕ H` restricts to the kernel of any endomorphism `f` preserving
both summands: `ker f = (E ∩ ker f) ⊕ (H ∩ ker f)`. -/
theorem sup_inf_ker_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {E H : Submodule ℝ V}
    (hc : IsCompl E H) {f : Module.End ℝ V} (hE : ∀ v ∈ E, f v ∈ E) (hH : ∀ v ∈ H, f v ∈ H) :
    (E ⊓ LinearMap.ker f) ⊔ (H ⊓ LinearMap.ker f) = LinearMap.ker f := by
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  intro v hv
  have hv' : v ∈ E ⊔ H := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨e, he, h, hh, rfl⟩ := Submodule.mem_sup.mp hv'
  have h0 : f e + f h = 0 := by rw [← map_add]; exact LinearMap.mem_ker.mp hv
  have hfe : f e = 0 := by
    have hfe' : f e = -f h := eq_neg_of_add_eq_zero_left h0
    exact (Submodule.disjoint_def.mp hc.disjoint) _ (hE e he)
      (by rw [hfe']; exact H.neg_mem (hH h hh))
  have hfh : f h = 0 := by rw [hfe, zero_add] at h0; exact h0
  exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨he, LinearMap.mem_ker.mpr hfe⟩)
    (Submodule.mem_inf.mpr ⟨hh, LinearMap.mem_ker.mpr hfh⟩)

theorem aeval_apply_mem_of_mapsTo {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Module.End ℝ V) {U : Submodule ℝ V} (hU : ∀ v ∈ U, f v ∈ U) (p : ℝ[X]) :
    ∀ v ∈ U, aeval f p v ∈ U := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact U.add_mem (hp v hv) (hq v hv)
  | monomial k a =>
    intro v hv
    rw [Polynomial.aeval_monomial, Module.End.mul_apply]
    simp only [Module.algebraMap_end_apply]
    exact U.smul_mem a (pow_apply_mem_of_mapsTo f hU k v hv)

/-- **The semisimple penalty, componentwise.** Let `A` be any integer matrix with `Φ_n ∣ χ_A`.
For every `A`-invariant scheme, the physical space meets the generalized `Φ_n`-component
`ker Φ_n(A)^{#ι}` in dimension `≥ 1`, and in dimension `≥ 2` when `n ≥ 3`. -/
theorem le_finrank_E_inf_component {A : Matrix ι ι ℤ} {n : ℕ} (hn : 0 < n)
    (hdvd : cyclotomic n ℚ ∣ charpolyQ A) (S : InvariantCPS A) :
    1 ≤ finrank ℝ ↥(S.E ⊓ LinearMap.ker (aeval (act A) (cyclotomic n ℝ ^ Fintype.card ι))) ∧
      (2 < n → 2 ≤ finrank ℝ
        ↥(S.E ⊓ LinearMap.ker (aeval (act A) (cyclotomic n ℝ ^ Fintype.card ι)))) := by
  set f := aeval (act A) (cyclotomic n ℝ ^ Fintype.card ι) with hf
  obtain ⟨γ, hγlat, hγ0, hγ⟩ := exists_int_mem_ker A (cyclotomic.irreducible_rat hn) hdvd
  rw [map_cyclotomic] at hγ
  obtain ⟨i, -⟩ := Function.ne_iff.mp hγ0
  have : Nonempty ι := ⟨i⟩
  have hN : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hγV : γ ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, hf, map_pow]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hN
    rw [hk, pow_succ, Module.End.mul_apply, hγ, map_zero]
  have hEf : ∀ v ∈ S.E, f v ∈ S.E := fun v hv =>
    aeval_apply_mem_of_mapsTo (act A) S.mapsTo_E _ v hv
  have hHf : ∀ v ∈ S.H, f v ∈ S.H := fun v hv =>
    aeval_apply_mem_of_mapsTo (act A) S.mapsTo_H _ v hv
  have hsplit := sup_inf_ker_eq S.isCompl hEf hHf
  have hne : S.E ⊓ LinearMap.ker f ≠ ⊥ := by
    intro hbot
    rw [hbot, bot_sup_eq] at hsplit
    have hmem : γ ∈ S.H ⊓ LinearMap.ker f := by rw [hsplit]; exact hγV
    exact hγ0 (S.inj γ hγlat (Submodule.mem_inf.mp hmem).1)
  have hpos : 1 ≤ finrank ℝ ↥(S.E ⊓ LinearMap.ker f) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hne (Submodule.finrank_eq_zero.mp h0)
  refine ⟨hpos, fun hn3 => ?_⟩
  have hne1 : finrank ℝ ↥(S.E ⊓ LinearMap.ker f) ≠ 1 := by
    intro h1
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
    have hvE := (Submodule.mem_inf.mp v.2).1
    have hvK := LinearMap.mem_ker.mp (Submodule.mem_inf.mp v.2).2
    have hinv : act A (v : ι → ℝ) ∈ S.E ⊓ LinearMap.ker f := by
      refine Submodule.mem_inf.mpr ⟨S.mapsTo_E _ hvE, LinearMap.mem_ker.mpr ?_⟩
      have h5 : f (act A (v : ι → ℝ)) = act A (f v) := aeval_comm_apply _ _ _
      rw [h5, hvK, map_zero]
    obtain ⟨c, hc⟩ := hv ⟨act A v, hinv⟩
    have hTv : act A (v : ι → ℝ) = c • (v : ι → ℝ) := by
      have h2 := congrArg Subtype.val hc
      simpa using h2.symm
    have hvne : (v : ι → ℝ) ≠ 0 := fun h => hv0 (Subtype.ext h)
    have heig : (act A).HasEigenvector c (v : ι → ℝ) := by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
      exact ⟨hTv, hvne⟩
    have h3 : f v = (cyclotomic n ℝ ^ Fintype.card ι).eval c • (v : ι → ℝ) :=
      Module.End.aeval_apply_of_hasEigenvector (p := cyclotomic n ℝ ^ Fintype.card ι) heig
    rw [hvK] at h3
    have h4 := (smul_eq_zero.mp h3.symm).resolve_right hvne
    rw [eval_pow] at h4
    exact (cyclotomic_pos hn3 c).ne' (pow_eq_zero_iff'.mp h4).1
  omega

end ComponentBounds

end Tilt

end

end InflationDimension
