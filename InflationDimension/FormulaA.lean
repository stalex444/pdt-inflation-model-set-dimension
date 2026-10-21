module
public import Mathlib
public import InflationDimension.JordanData
public import InflationDimension.Tilt

@[expose] public section
/-!
# The least physical dimension for every nonsingular integer matrix

Let `A` be an integer matrix with `det A ≠ 0`. The least physical dimension of an admissible
`A`-invariant cut-and-project scheme on `ℤ^ι` is `dimensionFormula A`, the sum over the distinct
irreducible factors `p` of `χ_A` over `ℚ` of `m_p u_p + c_p (m_p − r₁(p)) + δ_p`, where `m_p` is the
multiplicity, `u_p` and `c_p` count the roots of `p` of modulus `> 1` and `= 1`, `r₁(p)` is the
number of Jordan blocks of size one at each root of `p` (defined by ranks), and
`δ_p = min (deg p, 2)` when every root of `p` lies on the unit circle and `r₁(p) = m_p`, else `0`
(`FormulaA.isLeast_physDims_dimensionFormula`).

* **Lower bound** (`FormulaA.lower_aux`). An admissible scheme has `A` power-bounded on `H`, so
  `dim H` is at most the largest dimension `P` of a power-bounded invariant summand
  (`JordanData.isGreatest_powerBounded_summand`). At a cyclotomic factor with all Jordan blocks of
  size one, the physical space meets the generalized component in at least `δ_p` dimensions
  (`Tilt.le_finrank_E_inf_component`); absorbing such components into the internal space one at a
  time keeps a power-bounded summand, so `dim H + Σ_p δ_p ≤ P`.
* **Upper bound** (`FormulaA.upper_aux`). Start from a largest power-bounded summand and replace,
  one circle factor `p` at a time, its component `ker p(A)ᴺ` of a Fitting decomposition by the
  transport of a least scheme of the integer matrix by which `A` acts on a `ℤ`-basis of
  `ℤ^ι ∩ ker p(A)ᴺ` (`FormulaA.exists_transport`, `FormulaA.exists_component`); that matrix has
  `Φ_n` nilpotent, so its least scheme is the semisimple collapse or the tilt
  (`Tilt.isLeast_physDims_single_cyclotomic`).
* **Admissibility** (`FormulaA.exists_scheme_of_circle`). A splitting with `A` power-bounded on `H`
  carries an admissible scheme once, at every circle factor `p`, no nonzero lattice vector of `H` is
  killed by `p(A)` and no nonzero integer vector is orthogonal to `E` and to `im p(A)`: the rational
  annihilator of a lattice vector (`FormulaA.exists_annihilator`) and Kronecker's theorem for the
  factors of `χ_A` reduce every obstruction to a circle factor.
* **Corollaries.** The value is an invariant of rational similarity
  (`FormulaA.dimensionFormula_eq_of_conj`); it is `1` exactly for irreducible `χ_A` with one root of
  modulus `> 1` and for `A = ±1` (`FormulaA.dimensionFormula_eq_one`); and for `A^k = 1` it is
  `Σ_p min (deg p, 2)` (`FormulaA.finite_order_formula`).

The compared statements (3), (5), (6) and (7) are at the end of the file.
-/

namespace InflationDimension

open Polynomial Module
open scoped Matrix

noncomputable section

namespace FormulaA

open JordanData

/-! ### Invariant subspaces and Fitting decompositions -/

section Fitting

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An invariant splitting restricts to the image of any endomorphism preserving both
summands. -/
theorem sup_inf_range_eq {E H : Submodule ℝ V} (hc : IsCompl E H) {f : Module.End ℝ V}
    (hE : ∀ v ∈ E, f v ∈ E) (hH : ∀ v ∈ H, f v ∈ H) :
    (E ⊓ LinearMap.range f) ⊔ (H ⊓ LinearMap.range f) = LinearMap.range f := by
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  rintro _ ⟨w, rfl⟩
  have hw : w ∈ E ⊔ H := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨e, he, h, hh, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨hE e he, LinearMap.mem_range_self f e⟩)
    (Submodule.mem_inf.mpr ⟨hH h hh, LinearMap.mem_range_self f h⟩)

/-- An endomorphism injective on an invariant subspace of finite dimension maps it onto
itself. -/
theorem exists_preimage_of_disjoint [FiniteDimensional ℝ V] {T : Module.End ℝ V}
    {U : Submodule ℝ V} (hU : ∀ v ∈ U, T v ∈ U) (hd : Disjoint U (LinearMap.ker T)) :
    ∀ y ∈ U, ∃ w ∈ U, T w = y := by
  have hinj : Function.Injective (T.restrict hU) := by
    intro a b hab
    apply Subtype.ext
    have h0 : T ((a : V) - b) = 0 := by
      have h1 := congrArg Subtype.val hab
      rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply] at h1
      rw [map_sub, h1, sub_self]
    exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hd) _ (U.sub_mem a.2 b.2)
      (LinearMap.mem_ker.mpr h0))
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨w, hw⟩ := hsurj ⟨y, hy⟩
  refine ⟨w, w.2, ?_⟩
  have h1 := congrArg Subtype.val hw
  rwa [LinearMap.coe_restrict_apply] at h1

/-- An invariant subspace splits along a Fitting decomposition `ker Tᴺ ⊕ im Tᴺ`. -/
theorem sup_inf_fitting [FiniteDimensional ℝ V] {T : Module.End ℝ V} {N : ℕ}
    (hc : IsCompl (LinearMap.ker (T ^ N)) (LinearMap.range (T ^ N))) {U : Submodule ℝ V}
    (hU : ∀ v ∈ U, T v ∈ U) :
    (U ⊓ LinearMap.ker (T ^ N)) ⊔ (U ⊓ LinearMap.range (T ^ N)) = U := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro v hv
  have hUN : ∀ v ∈ U, (T ^ N) v ∈ U := fun v hv =>
    PowerBounded.coe_restrict_pow_apply T hU N ⟨v, hv⟩ ▸ ((T.restrict hU ^ N) ⟨v, hv⟩).2
  set U' := U ⊓ LinearMap.range (T ^ N) with hU'
  have hU'inv : ∀ v ∈ U', (T ^ N) v ∈ U' := fun v hv =>
    Submodule.mem_inf.mpr ⟨hUN v (Submodule.mem_inf.mp hv).1, LinearMap.mem_range_self _ v⟩
  have hd : Disjoint U' (LinearMap.ker (T ^ N)) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    exact (Submodule.disjoint_def.mp hc.disjoint) x hx2 (Submodule.mem_inf.mp hx1).2
  have hv' : v ∈ LinearMap.ker (T ^ N) ⊔ LinearMap.range (T ^ N) := by
    rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.mp hv'
  have hy : (T ^ N) (k + r) ∈ U' :=
    Submodule.mem_inf.mpr ⟨hUN _ hv, LinearMap.mem_range_self _ _⟩
  obtain ⟨w, hwU, hw⟩ := exists_preimage_of_disjoint hU'inv hd _ hy
  have hrw : r - w = 0 := by
    refine (Submodule.disjoint_def.mp hc.disjoint) _ ?_
      (Submodule.sub_mem _ hr (Submodule.mem_inf.mp hwU).2)
    rw [LinearMap.mem_ker, map_sub, hw, map_add, LinearMap.mem_ker.mp hk, zero_add, sub_self]
  have hrU : r ∈ U := by
    rw [sub_eq_zero.mp hrw]; exact (Submodule.mem_inf.mp hwU).1
  have hkU : k ∈ U := by
    have := U.sub_mem hv hrU
    rwa [add_sub_cancel_right] at this
  exact Submodule.add_mem_sup (Submodule.mem_inf.mpr ⟨hkU, hk⟩)
    (Submodule.mem_inf.mpr ⟨hrU, hr⟩)

/-- A Fitting decomposition for an exponent at least the dimension. -/
theorem exists_fitting [FiniteDimensional ℝ V] (T : Module.End ℝ V) :
    ∃ N : ℕ, finrank ℝ V ≤ N ∧
      IsCompl (LinearMap.ker (T ^ N)) (LinearMap.range (T ^ N)) ∧
      LinearMap.ker (T ^ N) = LinearMap.ker (T ^ finrank ℝ V) := by
  obtain ⟨N, hN⟩ := (T.eventually_isCompl_ker_pow_range_pow.and
    (Filter.eventually_ge_atTop (finrank ℝ V))).exists
  exact ⟨N, hN.2, hN.1, Module.End.ker_pow_eq_ker_pow_finrank_of_le hN.2⟩

/-- Replacing one component of an invariant splitting: if `V = K ⊕ R`, `V = E ⊕ H` with
`R = (E ∩ R) ⊕ (H ∩ R)`, and `K = E' ⊕ H'`, then `V = ((E ∩ R) ⊕ E') ⊕ ((H ∩ R) ⊕ H')`. -/
theorem isCompl_replace {K R E H Ec Hc : Submodule ℝ V} (hKR : IsCompl K R)
    (hEH : IsCompl E H) (hR : (E ⊓ R) ⊔ (H ⊓ R) = R) (hEc : Ec ≤ K) (hHc : Hc ≤ K)
    (hcK : Ec ⊔ Hc = K) (hdc : Disjoint Ec Hc) :
    IsCompl ((E ⊓ R) ⊔ Ec) ((H ⊓ R) ⊔ Hc) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨c, hc, d, hd, hcd⟩ := Submodule.mem_sup.mp hx2
    have hac : a - c = d - b := by
      rw [sub_eq_sub_iff_add_eq_add, ← hcd]; abel
    have h1 : a - c = 0 := (Submodule.disjoint_def.mp hKR.disjoint) _
      (by rw [hac]; exact K.sub_mem (hHc hd) (hEc hb))
      (R.sub_mem (Submodule.mem_inf.mp ha).2 (Submodule.mem_inf.mp hc).2)
    have hac' : a = c := sub_eq_zero.mp h1
    have ha0 : a = 0 := (Submodule.disjoint_def.mp hEH.disjoint) a (Submodule.mem_inf.mp ha).1
      (by rw [hac']; exact (Submodule.mem_inf.mp hc).1)
    have hbd : d - b = 0 := by rw [← hac, h1]
    have hb0 : b = 0 := (Submodule.disjoint_def.mp hdc) b hb
      (by rw [← sub_eq_zero.mp hbd]; exact hd)
    rw [ha0, hb0, add_zero]
  · rw [codisjoint_iff, sup_sup_sup_comm, hR, hcK, sup_comm, hKR.sup_eq_top]

theorem finrank_sup_of_le {K R X Y : Submodule ℝ V} [FiniteDimensional ℝ V]
    (hKR : IsCompl K R) (hX : X ≤ R) (hY : Y ≤ K) :
    finrank ℝ ↥(X ⊔ Y) = finrank ℝ X + finrank ℝ Y := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
  have hbot : X ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.mem_bot ℝ).mpr ((Submodule.disjoint_def.mp hKR.disjoint) v
      (hY (Submodule.mem_inf.mp hv).2) (hX (Submodule.mem_inf.mp hv).1))
  rw [hbot, finrank_bot, add_zero] at h
  exact h

theorem mem_right_of_mem_sup {K R X Y : Submodule ℝ V} (hKR : IsCompl K R) (hX : X ≤ R)
    (hY : Y ≤ K) {v : V} (hv : v ∈ X ⊔ Y) (hvK : v ∈ K) : v ∈ Y := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  have hx0 : x = 0 := (Submodule.disjoint_def.mp hKR.disjoint) x
    (by have := K.sub_mem hvK (hY hy); rwa [add_sub_cancel_right] at this) (hX hx)
  rw [hx0, zero_add]; exact hy

theorem mem_left_of_mem_sup {K R X Y : Submodule ℝ V} (hKR : IsCompl K R) (hX : X ≤ R)
    (hY : Y ≤ K) {v : V} (hv : v ∈ X ⊔ Y) (hvR : v ∈ R) : v ∈ X := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  have hy0 : y = 0 := (Submodule.disjoint_def.mp hKR.disjoint) y (hY hy)
    (by have := R.sub_mem hvR (hX hx); rwa [add_sub_cancel_left] at this)
  rw [hy0, add_zero]; exact hx

end Fitting

/-! ### Admissibility from the cyclotomic kernels -/

section Criterion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open KernelSplit in
/-- **The rational annihilator.** A nonzero rational vector `γ` has a monic annihilating
polynomial `g ∣ χ_B` over `ℚ` that divides every rational, and every real, polynomial `f` with
`f(B) γ = 0`. -/
theorem exists_annihilator (B : Matrix ι ι ℚ) {γ : ι → ℚ} (hγ : γ ≠ 0) :
    ∃ g : ℚ[X], g.Monic ∧ 0 < g.natDegree ∧ g ∣ B.charpoly ∧ aeval B g *ᵥ γ = 0 ∧
      (∀ h : ℚ[X], aeval B h *ᵥ γ = 0 → g ∣ h) ∧
      ∀ f : ℝ[X], aeval (B.map (algebraMap ℚ ℝ)) f *ᵥ (algebraMap ℚ ℝ ∘ γ) = 0 →
        g.map (algebraMap ℚ ℝ) ∣ f := by
  classical
  set φ := algebraMap ℚ ℝ with hφ
  set I := annIdeal B γ with hI
  set g₀ := Submodule.IsPrincipal.generator I with hg₀
  have hdvd₀ : ∀ h ∈ I, g₀ ∣ h := by
    intro h hh
    rw [← Ideal.span_singleton_generator I, Ideal.mem_span_singleton] at hh
    exact hh
  have hχ : B.charpoly ∈ I := by
    rw [hI, mem_annIdeal, Matrix.aeval_self_charpoly, Matrix.zero_mulVec]
  have hg₀0 : g₀ ≠ 0 := by
    intro h0
    have := hdvd₀ _ hχ
    rw [h0, zero_dvd_iff] at this
    exact (Matrix.charpoly_monic B).ne_zero this
  set g := normalize g₀ with hg
  have hgmon : g.Monic := Polynomial.monic_normalize hg₀0
  have hgI : g ∈ I := by
    have hmem : g₀ ∈ I := Submodule.IsPrincipal.generator_mem I
    rw [hg, normalize_apply]
    exact I.mul_mem_right _ hmem
  have hdvd : ∀ h ∈ I, g ∣ h := fun h hh =>
    ((associated_normalize g₀).symm.dvd).trans (hdvd₀ h hh)
  have hg1 : g ≠ 1 := by
    intro h1
    have : aeval B g *ᵥ γ = 0 := hgI
    rw [h1, map_one, Matrix.one_mulVec] at this
    exact hγ this
  refine ⟨g, hgmon, ?_, hdvd _ hχ, hgI, fun h hh => hdvd h hh, fun f hf => ?_⟩
  · by_contra h0
    push Not at h0
    exact hg1 ((Polynomial.Monic.natDegree_eq_zero hgmon).mp (by omega))
  set d := g.natDegree with hd
  set u : Fin d → ι → ℚ := fun k => (B ^ (k : ℕ)) *ᵥ γ with hu
  have hindQ : LinearIndependent ℚ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set h : ℚ[X] := ∑ k : Fin d, monomial (k : ℕ) (c k) with hh
    have hhI : h ∈ I := by
      rw [hI, mem_annIdeal, hh, map_sum, Matrix.sum_mulVec]
      simp only [aeval_monomial]
      have : ∀ k : Fin d, (algebraMap ℚ (Matrix ι ι ℚ) (c k) * B ^ (k : ℕ)) *ᵥ γ
          = c k • u k := by
        intro k
        rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul, Matrix.smul_mulVec]
      simp only [this]
      exact hc
    have hcoeff : ∀ k : Fin d, h.coeff k = c k := by
      intro k
      rw [hh, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        rw [Polynomial.coeff_monomial]
        exact ite_eq_right_iff.mpr (fun hjk => absurd (Fin.ext hjk) hj)
      · simp
    have hdeg : h.natDegree < d ∨ h = 0 := by
      by_cases h0 : h = 0
      · exact Or.inr h0
      left
      have hle : h.natDegree ≤ d - 1 := by
        rw [hh]
        refine (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_)
        intro k _
        refine (Polynomial.natDegree_monomial_le _).trans ?_
        omega
      have hdpos : 0 < d := by
        by_contra hd0
        push Not at hd0
        apply h0
        rw [hh]
        have : d = 0 := by omega
        have hempty : IsEmpty (Fin d) := by rw [this]; infer_instance
        exact Finset.sum_of_isEmpty _
      omega
    have h0 : h = 0 := by
      rcases hdeg with hlt | h0
      · by_contra hne
        have := Polynomial.natDegree_le_of_dvd (hdvd h hhI) hne
        omega
      · exact h0
    intro k
    rw [← hcoeff k, h0, Polynomial.coeff_zero]
  have hindR : LinearIndependent ℝ (fun k : Fin d => φ ∘ u k) :=
    linearIndependent_algebraMap_comp_iff.mpr hindQ
  set Bℝ := B.map φ with hBℝ
  set γℝ := φ ∘ γ with hγℝ
  have hpow : ∀ k : ℕ, φ ∘ ((B ^ k) *ᵥ γ) = (Bℝ ^ k) *ᵥ γℝ := by
    intro k
    rw [cast_mulVec, hBℝ, Matrix.map_pow]
  have hgR : aeval Bℝ (g.map φ) *ᵥ γℝ = 0 := by
    rw [hBℝ, aeval_map_matrix, hγℝ, ← cast_mulVec]
    have : aeval B g *ᵥ γ = 0 := hgI
    rw [this]
    funext i; simp
  have hgmonR : (g.map φ).Monic := hgmon.map φ
  set r := f %ₘ g.map φ with hr
  have hrann : aeval Bℝ r *ᵥ γℝ = 0 := by
    have hsplit := Polynomial.modByMonic_add_div f (g.map φ)
    have hr' : r = f - g.map φ * (f /ₘ g.map φ) := by rw [hr]; exact eq_sub_of_add_eq hsplit
    rw [hr', mul_comm (g.map φ) (f /ₘ g.map φ), map_sub, Matrix.sub_mulVec, hf, map_mul,
      ← Matrix.mulVec_mulVec, hgR, Matrix.mulVec_zero, sub_zero]
  have hgmapdeg : (g.map φ).natDegree = d := by
    rw [hd]; exact Polynomial.natDegree_map φ
  have hrdeg : r.natDegree < d ∨ r = 0 := by
    by_cases hr0 : r = 0
    · exact Or.inr hr0
    left
    have hg1R : g.map φ ≠ 1 := by
      intro h1
      apply hg1
      have : (g.map φ).natDegree = 0 := by rw [h1]; simp
      rw [hgmapdeg] at this
      exact (Polynomial.Monic.natDegree_eq_zero hgmon).mp this
    have := Polynomial.natDegree_modByMonic_lt f hgmonR hg1R
    rw [hgmapdeg] at this
    exact this
  have hr0 : r = 0 := by
    rcases hrdeg with hlt | h0
    · have hexp : aeval Bℝ r *ᵥ γℝ = ∑ k : Fin d, r.coeff k • (φ ∘ u k) := by
        rw [Polynomial.aeval_eq_sum_range' hlt, Matrix.sum_mulVec]
        rw [← Fin.sum_univ_eq_sum_range (fun k => (r.coeff k • Bℝ ^ k) *ᵥ γℝ) d]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Matrix.smul_mulVec, hu]
        simp only
        rw [hpow]
      rw [hexp] at hrann
      have hc := (Fintype.linearIndependent_iff.mp hindR) (fun k => r.coeff k) hrann
      ext n
      rw [Polynomial.coeff_zero]
      by_cases hn : n < d
      · exact hc ⟨n, hn⟩
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    · exact h0
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hgmonR).mp hr0

/-- Clearing denominators. -/
theorem exists_int_smul (v : ι → ℚ) : ∃ N : ℕ, N ≠ 0 ∧ ∃ n : ι → ℤ, ∀ i, (n i : ℚ) = N * v i := by
  refine ⟨∏ i, (v i).den, ?_, fun i => (v i).num * ((∏ j ∈ Finset.univ.erase i, (v j).den : ℕ) :
    ℤ), fun i => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    exact fun i _ => (v i).den_nz
  · have hprod : (v i).den * ∏ j ∈ Finset.univ.erase i, (v j).den = ∏ j, (v j).den :=
      Finset.mul_prod_erase Finset.univ (fun j => (v j).den) (Finset.mem_univ i)
    rw [← hprod, Nat.cast_mul, mul_comm ((v i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
    push_cast
    ring

/-- The eigenvalues of a power-bounded restriction lie in the closed unit disk. -/
theorem roots_le_one_of_powerBoundedOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f : Module.End ℝ V) {H : Submodule ℝ V} (hH : ∀ v ∈ H, f v ∈ H)
    (hpb : PowerBoundedOn f H) (z : ℂ) (hz : aeval z (f.restrict hH).charpoly = 0) :
    ‖z‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := hpb
  have hC' : ∀ (n : ℕ) (x : H), ‖(f.restrict hH ^ n) x‖ ≤ C * ‖x‖ := by
    intro n x
    have := hC n x x.2
    rw [← PowerBounded.coe_restrict_pow_apply f hH n x] at this
    exact this
  obtain ⟨K, hK⟩ := PowerBounded.entries_bounded_of_powerBounded _ hC'
  have hdisk := PowerBounded.norm_le_one_of_pow_bounded _ K hK
  rw [LinearMap.charpoly_toMatrix] at hdisk
  apply hdisk
  rw [Polynomial.mem_roots ((LinearMap.charpoly_monic _).map _).ne_zero, IsRoot,
    eval_map_algebraMap]
  exact hz

theorem aeval_charpoly_restrict_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (f : Module.End ℝ V) {H : Submodule ℝ V} (hH : ∀ v ∈ H, f v ∈ H)
    {v : V} (hv : v ∈ H) : aeval f (f.restrict hH).charpoly v = 0 := by
  have h := KernelSplit.aeval_restrict_apply f hH (f.restrict hH).charpoly ⟨v, hv⟩
  rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at h
  exact h.symm.trans rfl

/-- A lattice vector killed by a real polynomial with all roots in the closed disk gives, inside
any invariant subspace containing it, a nonzero lattice vector killed by a circle factor. -/
theorem exists_circle_vector (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) {U : Submodule ℝ (ι → ℝ)}
    (hU : ∀ v ∈ U, act A v ∈ U) {q : ℝ[X]} (hq : ∀ z : ℂ, aeval z q = 0 → ‖z‖ ≤ 1)
    {γ : ι → ℝ} (hγ : γ ∈ intLattice ι) (hγU : γ ∈ U) (hγ0 : γ ≠ 0)
    (hqγ : aeval (act A) q γ = 0) :
    ∃ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A), IsCircleFactor p ∧
      ∃ γ' ∈ intLattice ι, γ' ∈ U ∧ γ' ≠ 0 ∧ aeval (act A) (p.map (algebraMap ℚ ℝ)) γ' = 0 := by
  classical
  obtain ⟨m, rfl⟩ := mem_intLattice_iff.mp hγ
  set γQ : ι → ℚ := fun i => (m i : ℚ) with hγQ
  have hγeq : (fun i => (m i : ℝ)) = algebraMap ℚ ℝ ∘ γQ := by funext i; simp [γQ]
  have hγQ0 : γQ ≠ 0 := by
    intro h; apply hγ0; rw [hγeq, h]; funext i; simp
  set AQ : Matrix ι ι ℚ := A.map (Int.castRingHom ℚ) with hAQ
  have hχQ : AQ.charpoly = charpolyQ A := by rw [hAQ, Matrix.charpoly_map]; rfl
  have hreal : ∀ (f : ℝ[X]) (w : ι → ℚ), aeval (act A) f (algebraMap ℚ ℝ ∘ w) =
      aeval (AQ.map (algebraMap ℚ ℝ)) f *ᵥ (algebraMap ℚ ℝ ∘ w) := fun f w =>
    KernelSplit.aeval_act A f _
  obtain ⟨g, hgmon, hgdeg, hgχ, hgγ, hgminQ, hgmin⟩ := exists_annihilator AQ hγQ0
  have hgq : g.map (algebraMap ℚ ℝ) ∣ q := hgmin q (by rw [← hreal, ← hγeq]; exact hqγ)
  have hgdisk : ∀ z : ℂ, aeval z g = 0 → ‖z‖ ≤ 1 := by
    intro z hz
    apply hq
    obtain ⟨r, hr⟩ := hgq
    rw [hr, map_mul, aeval_map_algebraMap, hz, zero_mul]
  have hgu : ¬ IsUnit g := fun hu => by
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨p₀, hp₀, hp₀g⟩ := WfDvdMonoid.exists_irreducible_factor hgu hgmon.ne_zero
  have hχ0 : charpolyQ A ≠ 0 := (Matrix.charpoly_monic A).map _ |>.ne_zero
  obtain ⟨p, hpmem, hassoc⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
    hχ0 hp₀ (hp₀g.trans (hχQ ▸ hgχ))
  have hpg : p ∣ g := hassoc.symm.dvd.trans hp₀g
  have hpirr : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hpmem
  have hpmon : p.Monic := Count.monic_of_mem A hpmem
  have hpcirc : IsCircleFactor p := by
    have h0 : A.charpoly.coeff 0 ≠ 0 := by
      intro h0
      apply hdet
      rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
    refine Count.norm_eq_one_of_forall_le_one hpirr hpmon (Matrix.charpoly_monic A) h0
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpmem) ?_
    intro z hz
    apply hgdisk
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hpirr.ne_zero), IsRoot,
      eval_map_algebraMap] at hz
    obtain ⟨s, hs⟩ := hpg
    rw [hs, map_mul, hz, zero_mul]
  obtain ⟨s, hs⟩ := hpg
  set γ'Q : ι → ℚ := aeval AQ s *ᵥ γQ with hγ'Q
  have hγ'Q0 : γ'Q ≠ 0 := by
    intro h0
    have hgs := hgminQ s h0
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      exact hgmon.ne_zero hs
    have h1 := Polynomial.natDegree_le_of_dvd hgs hs0
    have h2 : g.natDegree = p.natDegree + s.natDegree := by
      rw [hs]; exact Polynomial.natDegree_mul hpirr.ne_zero hs0
    have h3 := Irreducible.natDegree_pos hpirr
    omega
  have hpγ' : aeval AQ p *ᵥ γ'Q = 0 := by
    rw [hγ'Q, Matrix.mulVec_mulVec, ← map_mul, ← hs]
    exact hgγ
  obtain ⟨N, hN0, n, hn⟩ := exists_int_smul γ'Q
  refine ⟨p, hpmem, hpcirc, fun i => (n i : ℝ), mem_intLattice_iff.mpr ⟨n, rfl⟩, ?_, ?_, ?_⟩
  · have hreal' : (fun i => (n i : ℝ)) = (N : ℝ) • aeval (act A) (s.map (algebraMap ℚ ℝ))
        (fun i => (m i : ℝ)) := by
      rw [hγeq, hreal, KernelSplit.aeval_map_matrix, ← KernelSplit.cast_mulVec, ← hγ'Q]
      funext i
      simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
      have h2 : ((n i : ℚ) : ℝ) = ((N * γ'Q i : ℚ) : ℝ) := by rw [hn i]
      rw [show (algebraMap ℚ ℝ) (γ'Q i) = ((γ'Q i : ℚ) : ℝ) from rfl]
      exact_mod_cast h2
    rw [hreal']
    exact U.smul_mem _ (Tilt.aeval_apply_mem_of_mapsTo (act A) hU _ _ hγU)
  · intro h0
    apply hγ'Q0
    funext i
    have h1 : (n i : ℝ) = 0 := congrFun h0 i
    have h2 : (n i : ℚ) = 0 := by exact_mod_cast h1
    rw [hn i] at h2
    simpa [hN0] using h2
  · have hcast : (fun i => (n i : ℝ)) = algebraMap ℚ ℝ ∘ ((N : ℚ) • γ'Q) := by
      funext i
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hn i]
      simp
    rw [hcast, hreal, KernelSplit.aeval_map_matrix, ← KernelSplit.cast_mulVec,
      Matrix.mulVec_smul, hpγ', smul_zero]
    funext i; simp


theorem dot_aeval_transpose (A : Matrix ι ι ℤ) (q : ℝ[X]) (c v : ι → ℝ) :
    aeval (act Aᵀ) q c ⬝ᵥ v = c ⬝ᵥ aeval (act A) q v := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, add_dotProduct,
      dotProduct_add, hp, hq]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, smul_dotProduct, dotProduct_smul]
    congr 1
    induction k generalizing c with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, Tilt.act_transpose_dot, pow_succ',
        Module.End.mul_apply]

/-- **Admissibility from the circle factors.** Let `det A ≠ 0` and let `ℝ^ι = E ⊕ H` be an
`A`-invariant splitting with `A` power-bounded on `H`. If, for every irreducible factor `p` of
`χ_A` over `ℚ` with all roots on the unit circle, no nonzero lattice vector of `H` is killed by
`p(A)` and no nonzero integer vector is orthogonal to both `E` and `im p(A)`, the splitting
carries an admissible scheme. -/
theorem exists_scheme_of_circle (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H) (hE : ∀ v ∈ E, act A v ∈ E)
    (hH : ∀ v ∈ H, act A v ∈ H) (hpb : PowerBoundedOn (act A) H)
    (ha : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A), IsCircleFactor p →
      ∀ γ ∈ intLattice ι, γ ∈ H → aeval (act A) (p.map (algebraMap ℚ ℝ)) γ = 0 → γ = 0)
    (hb : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A), IsCircleFactor p →
      ∀ c : ι → ℤ, (∀ e ∈ E, (fun i => (c i : ℝ)) ⬝ᵥ e = 0) →
        (∀ v, (fun i => (c i : ℝ)) ⬝ᵥ aeval (act A) (p.map (algebraMap ℚ ℝ)) v = 0) → c = 0) :
    ∃ S : InvariantCPS A, S.E = E ∧ S.H = H ∧ S.Admissible := by
  classical
  set gH := ((act A).restrict hH).charpoly with hgH
  have hroots : ∀ z : ℂ, aeval z gH = 0 → ‖z‖ ≤ 1 :=
    roots_le_one_of_powerBoundedOn (act A) hH hpb
  have hinj : ∀ γ ∈ intLattice ι, γ ∈ H → γ = 0 := by
    intro γ hγ hγH
    by_contra hγ0
    obtain ⟨p, hp, hpc, γ', hγ', hγ'H, hγ'0, hpγ'⟩ := exists_circle_vector A hdet hH hroots hγ
      hγH hγ0 (aeval_charpoly_restrict_apply (act A) hH hγH)
    exact hγ'0 (ha p hp hpc γ' hγ' hγ'H hpγ')
  have hnoint : ∀ c : ι → ℤ, (∀ e ∈ E, (fun i => (c i : ℝ)) ⬝ᵥ e = 0) → c = 0 := by
    intro c hcE
    by_contra hc0
    set cR : ι → ℝ := fun i => (c i : ℝ) with hcR
    have hcR0 : cR ≠ 0 := fun h => hc0 (funext fun i => by
      have h1 : ((c i : ℤ) : ℝ) = 0 := congrFun h i
      exact_mod_cast h1)
    have hkill : aeval (act Aᵀ) gH cR = 0 := by
      ext j
      rw [Pi.zero_apply, ← dotProduct_single_one (aeval (act Aᵀ) gH cR) j, dot_aeval_transpose]
      apply hcE
      have hv : (Pi.single j 1 : ι → ℝ) ∈ E ⊔ H := by
        rw [hc.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨e, he, h, hh, hsum⟩ := Submodule.mem_sup.mp hv
      rw [← hsum, map_add, aeval_charpoly_restrict_apply (act A) hH hh, add_zero]
      exact Tilt.aeval_apply_mem_of_mapsTo (act A) hE _ _ he
    have hUinv : ∀ v ∈ Tilt.dotOrth E, act Aᵀ v ∈ Tilt.dotOrth E := by
      intro v hv u hu
      rw [dotProduct_comm, Tilt.act_transpose_dot, dotProduct_comm]
      exact hv _ (hE u hu)
    have hcU : cR ∈ Tilt.dotOrth E := fun u hu => by rw [dotProduct_comm]; exact hcE u hu
    have hdetT : Aᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
    obtain ⟨p, hp, hpc, γ', hγ', hγ'U, hγ'0, hpγ'⟩ := exists_circle_vector Aᵀ hdetT hUinv hroots
      (mem_intLattice_iff.mpr ⟨c, rfl⟩) hcU hcR0 hkill
    have hχT : charpolyQ Aᵀ = charpolyQ A := by
      rw [charpolyQ, charpolyQ, Matrix.charpoly_transpose]
    rw [hχT] at hp
    obtain ⟨c', rfl⟩ := mem_intLattice_iff.mp hγ'
    have hc' := hb p hp hpc c' (fun e he => by rw [dotProduct_comm]; exact hγ'U e he)
      (fun v => by rw [← dot_aeval_transpose, hpγ', zero_dotProduct])
    apply hγ'0
    rw [hc']; funext i; simp
  have hdense := dense_of_no_integral_functional hc (by
    intro f hf hfE
    obtain ⟨c, hcf⟩ := Tilt.exists_int_of_integral hf
    have hc0 := hnoint c (fun e he => by rw [← hcf]; exact hfE e he)
    apply LinearMap.ext
    intro v
    rw [hcf v, hc0]
    simp)
  refine ⟨⟨E, H, hc, hE, hH, hinj, hdense⟩, rfl, rfl, ?_⟩
  exact (admissible_iff_powerBounded _).mpr hpb

end Criterion

/-! ### Transport to a primary component -/

section Transport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem intCast_mulVec (M : Matrix ι ι ℤ) (m : ι → ℤ) :
    (fun i => ((M *ᵥ m) i : ℝ)) = act M (fun i => (m i : ℝ)) := by
  funext i
  rw [act, Matrix.toLin'_apply]
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) M m i)

omit [Fintype ι] [DecidableEq ι] in
theorem intCast_injective {m m' : ι → ℤ} (h : (fun i => (m i : ℝ)) = fun i => (m' i : ℝ)) :
    m = m' := funext fun i => by exact_mod_cast congrFun h i

/-- **Transport.** Let `M` be an integer matrix commuting with `A`. The lattice `ℤ^ι ∩ ker M`
has a `ℤ`-basis `b₁, …, b_k`; in it `A` acts by an integer matrix `B`, and `x ↦ Σ x_j b_j` is an
injective map `L : ℝ^k → ℝ^ι` onto `ker M` intertwining `B` with `A`, mapping `ℤ^k` onto
`ℤ^ι ∩ ker M`. -/
theorem exists_transport (A M : Matrix ι ι ℤ) (hAM : A * M = M * A) :
    ∃ (k : ℕ) (B : Matrix (Fin k) (Fin k) ℤ) (L : (Fin k → ℝ) →ₗ[ℝ] (ι → ℝ)),
      Function.Injective L ∧ LinearMap.range L = LinearMap.ker (act M) ∧
      (∀ x, act A (L x) = L (act B x)) ∧
      (∀ x ∈ intLattice (Fin k), L x ∈ intLattice ι) ∧
      (∀ γ ∈ intLattice ι, γ ∈ LinearMap.ker (act M) → ∃ x ∈ intLattice (Fin k), L x = γ) := by
  classical
  set Γ : Submodule ℤ (ι → ℤ) := LinearMap.ker (Matrix.mulVecLin M) with hΓ
  obtain ⟨k, bb⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) Γ
  set b : Fin k → ι → ℤ := fun j => (bb j : ι → ℤ) with hb
  set bR : Fin k → ι → ℝ := fun j i => (b j i : ℝ) with hbR
  have hbΓ : ∀ j, M *ᵥ b j = 0 := fun j => (bb j).2
  have hAb : ∀ j, M *ᵥ (A *ᵥ b j) = 0 := by
    intro j
    rw [Matrix.mulVec_mulVec, ← hAM, ← Matrix.mulVec_mulVec, hbΓ, Matrix.mulVec_zero]
  set B : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun i j => bb.repr ⟨A *ᵥ b j, hAb j⟩ i with hB
  have hAbsum : ∀ j, A *ᵥ b j = ∑ i, B i j • b i := by
    intro j
    have h2 : ((⟨A *ᵥ b j, hAb j⟩ : Γ) : ι → ℤ) = ∑ i, B i j • b i := by
      conv_lhs => rw [← bb.sum_repr ⟨A *ᵥ b j, hAb j⟩]
      rw [Submodule.coe_sum]
      rfl
    exact h2
  set L : (Fin k → ℝ) →ₗ[ℝ] (ι → ℝ) := Fintype.linearCombination ℝ bR with hL
  have hLapp : ∀ x, L x = ∑ j, x j • bR j := fun x => Fintype.linearCombination_apply ℝ bR x
  -- linear independence
  have hindZ : LinearIndependent ℤ b :=
    bb.linearIndependent.map' Γ.subtype (Submodule.ker_subtype _)
  set castQ : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) :=
    { toFun := fun m i => (m i : ℚ), map_add' := fun _ _ => by funext i; simp,
      map_smul' := fun _ _ => by funext i; simp } with hcastQ
  have hcastQinj : LinearMap.ker castQ = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [LinearMap.mem_ker] at hm
    exact (Submodule.mem_bot ℤ).mpr (funext fun i => by
      have h1 : ((m i : ℤ) : ℚ) = 0 := congrFun hm i
      exact_mod_cast h1)
  set bQ : Fin k → ι → ℚ := fun j => castQ (b j) with hbQ
  have hindZQ : LinearIndependent ℤ bQ := hindZ.map' castQ hcastQinj
  have hindQ : LinearIndependent ℚ bQ := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hindZQ
  have hindR : LinearIndependent ℝ (fun j => algebraMap ℚ ℝ ∘ bQ j) :=
    linearIndependent_algebraMap_comp_iff.mpr hindQ
  have hbReq : ∀ j, bR j = algebraMap ℚ ℝ ∘ bQ j := by
    intro j; funext i; simp [bR, bQ, castQ]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, hLapp] at hx
    have hx' : ∑ j, x j • (algebraMap ℚ ℝ ∘ bQ j) = 0 := by
      rw [← hx]; refine Finset.sum_congr rfl (fun j _ => ?_); rw [hbReq]
    have := (Fintype.linearIndependent_iff.mp hindR) x hx'
    exact (Submodule.mem_bot ℝ).mpr (funext this)
  -- the intertwining
  have hactb : ∀ j, act A (bR j) = ∑ i, (B i j : ℝ) • bR i := by
    intro j
    have h1 : act A (bR j) = fun i => ((A *ᵥ b j) i : ℝ) := (intCast_mulVec A (b j)).symm
    rw [h1, hAbsum j]
    funext i
    simp [Finset.sum_apply, bR]
  have hinter : ∀ x, act A (L x) = L (act B x) := by
    intro x
    rw [hLapp, hLapp, map_sum]
    simp only [map_smul, hactb, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_smul]
    congr 1
    rw [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [mul_comm]
  -- the lattice
  have hLlat : ∀ x ∈ intLattice (Fin k), L x ∈ intLattice ι := by
    intro x hx
    obtain ⟨c, rfl⟩ := mem_intLattice_iff.mp hx
    rw [mem_intLattice_iff]
    refine ⟨∑ j, c j • b j, ?_⟩
    rw [hLapp]
    funext i
    simp [Finset.sum_apply, bR]
  have hLsurj : ∀ γ ∈ intLattice ι, γ ∈ LinearMap.ker (act M) →
      ∃ x ∈ intLattice (Fin k), L x = γ := by
    intro γ hγ hγM
    obtain ⟨m, rfl⟩ := mem_intLattice_iff.mp hγ
    have hm : M *ᵥ m = 0 := by
      apply intCast_injective
      rw [intCast_mulVec, LinearMap.mem_ker.mp hγM]
      funext i; simp
    have hmΓ : m ∈ Γ := by
      show Matrix.mulVecLin M m = 0
      rw [Matrix.mulVecLin_apply]; exact hm
    set c := bb.repr ⟨m, hmΓ⟩ with hc
    refine ⟨fun j => (c j : ℝ), mem_intLattice_iff.mpr ⟨c, rfl⟩, ?_⟩
    have h := congrArg Subtype.val (bb.sum_repr ⟨m, hmΓ⟩)
    rw [Submodule.coe_sum] at h
    rw [hLapp]
    funext i
    have h3 := congrFun h i
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h3
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bR, b]
    rw [← h3]
    push_cast
    rfl
  -- the range
  have hLM : ∀ x, act M (L x) = 0 := by
    intro x
    rw [hLapp, map_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [map_smul]
    have : act M (bR j) = 0 := by
      rw [show bR j = fun i => (b j i : ℝ) from rfl, ← intCast_mulVec, hbΓ]
      funext i; simp
    rw [this, smul_zero]
  have hrange_le : LinearMap.range L ≤ LinearMap.ker (act M) := by
    rintro _ ⟨x, rfl⟩; exact hLM x
  have hspan : LinearMap.ker (Matrix.toLin' (M.map (Int.castRingHom ℚ))) ≤
      Submodule.span ℚ (Set.range bQ) := by
    intro v hv
    obtain ⟨N, hN0, n, hn⟩ := exists_int_smul v
    have hnM : M *ᵥ n = 0 := by
      funext i
      have h1 : ((M *ᵥ n) i : ℚ) = (N : ℚ) * ((M.map (Int.castRingHom ℚ)) *ᵥ v) i := by
        rw [show ((M *ᵥ n) i : ℚ) = ((M.map (Int.castRingHom ℚ)) *ᵥ (fun j => (n j : ℚ))) i
          from (RingHom.map_mulVec (Int.castRingHom ℚ) M n i)]
        rw [show (fun j => (n j : ℚ)) = (N : ℚ) • v from funext fun j => by
          rw [hn j]; simp, Matrix.mulVec_smul]
        simp
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hv
      rw [hv] at h1
      simp only [Pi.zero_apply, mul_zero] at h1
      exact_mod_cast h1
    have hnΓ : n ∈ Γ := by
      show Matrix.mulVecLin M n = 0
      rw [Matrix.mulVecLin_apply]; exact hnM
    have h := congrArg Subtype.val (bb.sum_repr ⟨n, hnΓ⟩)
    rw [Submodule.coe_sum] at h
    have hv' : v = ∑ j, ((bb.repr ⟨n, hnΓ⟩ j : ℚ) / N) • bQ j := by
      funext i
      have h3 := congrFun h i
      simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] at h3
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bQ, castQ, LinearMap.coe_mk,
        AddHom.coe_mk]
      have h4 : (n i : ℚ) = ∑ j, ((bb.repr ⟨n, hnΓ⟩ j : ℚ) * (b j i : ℚ)) := by
        rw [← h3]; push_cast; rfl
      have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
      rw [hn i] at h4
      have hvi : v i = (∑ j, ((bb.repr ⟨n, hnΓ⟩ j : ℚ) * (b j i : ℚ))) / N := by
        rw [← h4]; field_simp
      rw [hvi, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hv']
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, rfl⟩))
  have hdimQ : finrank ℚ (LinearMap.ker (Matrix.toLin' (M.map (Int.castRingHom ℚ)))) ≤ k := by
    refine (Submodule.finrank_mono hspan).trans ?_
    exact (finrank_span_le_card (Set.range bQ)).trans (by
      rw [Set.toFinset_range]; exact Finset.card_image_le.trans (by simp))
  have hdimR : finrank ℝ (LinearMap.ker (act M)) =
      finrank ℚ (LinearMap.ker (Matrix.toLin' (M.map (Int.castRingHom ℚ)))) := by
    have h := JordanData.finrank_ker_map_real (M.map (Int.castRingHom ℚ))
    have hM : (M.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) = M.map (Int.cast : ℤ → ℝ) := by
      ext i j; simp
    rw [← h, hM]; rfl
  have hrange_dim : finrank ℝ (LinearMap.range L) = k := by
    rw [LinearMap.finrank_range_of_inj hLinj, Module.finrank_fin_fun]
  have hmono := Submodule.finrank_mono hrange_le
  have hrange : LinearMap.range L = LinearMap.ker (act M) :=
    Submodule.eq_of_le_of_finrank_eq hrange_le (by omega)
  exact ⟨k, B, L, hLinj, hrange, hinter, hLlat, hLsurj⟩

end Transport

/-! ### Schemes of a primary component -/

section Components

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem L_pow {k : ℕ} {A : Matrix ι ι ℤ} {B : Matrix (Fin k) (Fin k) ℤ}
    {L : (Fin k → ℝ) →ₗ[ℝ] (ι → ℝ)} (hL : ∀ x, act A (L x) = L (act B x)) (m : ℕ) (x) :
    (act A ^ m) (L x) = L ((act B ^ m) x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, hL, ih, ← Module.End.mul_apply, ← pow_succ]

theorem L_aeval {k : ℕ} {A : Matrix ι ι ℤ} {B : Matrix (Fin k) (Fin k) ℤ}
    {L : (Fin k → ℝ) →ₗ[ℝ] (ι → ℝ)} (hL : ∀ x, act A (L x) = L (act B x)) (q : ℝ[X]) (x) :
    aeval (act A) q (L x) = L (aeval (act B) q x) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq,
      map_add]
  | monomial m a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, L_pow hL]

theorem finrank_ker_transport {k : ℕ} {A : Matrix ι ι ℤ} {B : Matrix (Fin k) (Fin k) ℤ}
    {L : (Fin k → ℝ) →ₗ[ℝ] (ι → ℝ)} (hLinj : Function.Injective L)
    (hL : ∀ x, act A (L x) = L (act B x)) {q : ℝ[X]}
    (hq : LinearMap.ker (aeval (act A) q) ≤ LinearMap.range L) :
    finrank ℝ (LinearMap.ker (aeval (act B) q)) = finrank ℝ (LinearMap.ker (aeval (act A) q)) := by
  have hmap : (LinearMap.ker (aeval (act B) q)).map L = LinearMap.ker (aeval (act A) q) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [LinearMap.mem_ker, L_aeval hL, LinearMap.mem_ker.mp hx, map_zero]
    · intro hy
      obtain ⟨x, rfl⟩ := hq hy
      refine ⟨x, ?_, rfl⟩
      show x ∈ LinearMap.ker (aeval (act B) q)
      rw [LinearMap.mem_ker]
      apply hLinj
      rw [← L_aeval hL, map_zero]
      exact hy
  rw [← hmap]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L hLinj _)

theorem PowerBoundedOn.mono' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Module.End ℝ V} {U W : Submodule ℝ V} (h : PowerBoundedOn f W) (hUW : U ≤ W) :
    PowerBoundedOn f U := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun n v hv => hC n v (hUW hv)⟩

theorem powerBoundedOn_sup {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f : Module.End ℝ V) {U W : Submodule ℝ V}
    (hU : PowerBoundedOn f U) (hW : PowerBoundedOn f W) : PowerBoundedOn f (U ⊔ W) := by
  apply powerBoundedOn_of_bounded
  intro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨C, hC⟩ := hU
  obtain ⟨C', hC'⟩ := hW
  exact ⟨C * ‖u‖ + C' * ‖w‖, fun n => by
    rw [map_add]; exact (norm_add_le _ _).trans (add_le_add (hC n u hu) (hC' n w hw))⟩

/-- A scheme for `B` transports to a splitting of `range L`. -/
theorem transport_scheme {k : ℕ} {A : Matrix ι ι ℤ} {B : Matrix (Fin k) (Fin k) ℤ}
    {L : (Fin k → ℝ) →ₗ[ℝ] (ι → ℝ)} (hLinj : Function.Injective L)
    (hL : ∀ x, act A (L x) = L (act B x))
    (hLlat : ∀ x ∈ intLattice (Fin k), L x ∈ intLattice ι)
    (hLsurj : ∀ γ ∈ intLattice ι, γ ∈ LinearMap.range L → ∃ x ∈ intLattice (Fin k), L x = γ)
    (S : InvariantCPS B) (hS : S.Admissible) :
    S.E.map L ⊔ S.H.map L = LinearMap.range L ∧ Disjoint (S.E.map L) (S.H.map L) ∧
      (∀ v ∈ S.E.map L, act A v ∈ S.E.map L) ∧ (∀ v ∈ S.H.map L, act A v ∈ S.H.map L) ∧
      PowerBoundedOn (act A) (S.H.map L) ∧
      (∀ γ ∈ intLattice ι, γ ∈ S.H.map L → γ = 0) ∧
      (∀ c : ι → ℤ, (∀ e ∈ S.E.map L, (fun i => (c i : ℝ)) ⬝ᵥ e = 0) →
        ∀ v ∈ LinearMap.range L, (fun i => (c i : ℝ)) ⬝ᵥ v = 0) ∧
      finrank ℝ (S.H.map L) = finrank ℝ S.H := by
  refine ⟨?_, Submodule.disjoint_map hLinj S.isCompl.disjoint, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Submodule.map_sup, S.isCompl.sup_eq_top, Submodule.map_top]
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨act B x, S.mapsTo_E x hx, (hL x).symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨act B x, S.mapsTo_H x hx, (hL x).symm⟩
  · obtain ⟨C, hC⟩ := (admissible_iff_powerBounded S).mp hS
    apply powerBoundedOn_of_bounded
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨‖LinearMap.toContinuousLinearMap L‖ * (C * ‖x‖), fun n => ?_⟩
    rw [L_pow hL]
    calc ‖L ((act B ^ n) x)‖ = ‖LinearMap.toContinuousLinearMap L ((act B ^ n) x)‖ := rfl
      _ ≤ ‖LinearMap.toContinuousLinearMap L‖ * ‖(act B ^ n) x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖LinearMap.toContinuousLinearMap L‖ * (C * ‖x‖) :=
          mul_le_mul_of_nonneg_left (hC n x hx) (norm_nonneg _)
  · rintro γ hγ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hLsurj _ hγ ⟨y, rfl⟩
    have : x = y := hLinj hxy
    subst this
    rw [S.inj x hx hy, map_zero]
  · intro c hcE
    set f : (Fin k → ℝ) →ₗ[ℝ] ℝ := Tilt.dotL (fun i => (c i : ℝ)) ∘ₗ L with hf
    have hint : ∀ γ ∈ intLattice (Fin k), ∃ n : ℤ, f γ = n := by
      intro γ hγ
      obtain ⟨m, hm⟩ := mem_intLattice_iff.mp (hLlat γ hγ)
      refine ⟨c ⬝ᵥ m, ?_⟩
      rw [hf, LinearMap.comp_apply, Tilt.dotL_apply, hm, dotProduct, dotProduct]
      push_cast
      rfl
    have hvan : ∀ v ∈ S.E, f v = 0 := fun v hv => hcE _ ⟨v, hv, rfl⟩
    have hf0 := (kronecker_density_criterion S.E S.H S.isCompl).mp S.dense f hint hvan
    rintro _ ⟨x, rfl⟩
    have := LinearMap.congr_fun hf0 x
    simpa [hf] using this
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L hLinj _)).symm

theorem ker_le_range_of_coprime {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : Module.End ℝ V) {a b : ℝ[X]} (h : IsCoprime a b) :
    LinearMap.ker (aeval f a) ≤ LinearMap.range (aeval f b) := by
  intro y hy
  have hinv : ∀ v ∈ LinearMap.ker (aeval f a), aeval f b v ∈ LinearMap.ker (aeval f a) := by
    intro v hv
    rw [LinearMap.mem_ker, Tilt.aeval_comm_aeval_apply, LinearMap.mem_ker.mp hv, map_zero]
  obtain ⟨w, -, hw⟩ := exists_preimage_of_disjoint hinv
    (Polynomial.disjoint_ker_aeval_of_isCoprime f h) y hy
  exact ⟨w, hw⟩

theorem isCoprime_of_mem {A : Matrix ι ι ℤ} {p q : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A))
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) (hpq : p ≠ q) :
    IsCoprime (p.map (algebraMap ℚ ℝ)) (q.map (algebraMap ℚ ℝ)) := by
  have hpi := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hqi := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
  have hcop : IsCoprime p q := by
    rw [hpi.coprime_iff_not_dvd]
    intro hdvd
    exact hpq (Polynomial.eq_of_monic_of_associated (Count.monic_of_mem A hp)
      (Count.monic_of_mem A hq) (hpi.associated_of_dvd hqi hdvd))
  exact hcop.map (Polynomial.mapRingHom (algebraMap ℚ ℝ))

theorem min_totient_two {n : ℕ} (hn : 0 < n) :
    min n.totient 2 = if n ≤ 2 then 1 else 2 := by
  split_ifs with h
  · interval_cases n <;> simp
  · have h1 := Nat.totient_even (by omega : 2 < n)
    have h2 := Nat.totient_pos.mpr hn
    obtain ⟨r, hr⟩ := h1
    omega

open Classical in
/-- The semisimple-cyclotomic term: `δ_p = min (deg p, 2)` if `p` has all its roots on the unit
circle (so `p = Φ_n`) and all Jordan blocks at its roots have size one (`r₁(p) = m_p`); else
`0`. -/
def defect (A : Matrix ι ι ℤ) (p : ℚ[X]) : ℕ :=
  if IsCircleFactor p ∧ singleBlocks A p = mult A p then min p.natDegree 2 else 0

theorem singleBlocks_eq_mult_iff_real (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) :
    singleBlocks A p = mult A p ↔
      LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ) ^ 2)) =
        LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ))) := by
  rw [singleBlocks_eq_mult_iff A hp]
  have hle : LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ))) ≤
      LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ) ^ 2)) := by
    intro v hv
    rw [LinearMap.mem_ker, pow_two, map_mul, Module.End.mul_apply, LinearMap.mem_ker.mp hv,
      map_zero]
  have hleQ := ker_le_ker_pow A p (by norm_num : 1 ≤ 2)
  have h1 := finrank_ker_real_pow A p 1
  have h2 := finrank_ker_real_pow A p 2
  rw [pow_one] at h1
  have hk1 : kerRank A p 1 = finrank ℚ (LinearMap.ker (aeval (actQ A) p)) := by
    rw [kerRank, pow_one]
  have hk2 : kerRank A p 2 = finrank ℚ (LinearMap.ker (aeval (actQ A) (p ^ 2))) := rfl
  constructor
  · intro h
    symm
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [h1, h2, hk1, hk2, h]
  · intro h
    symm
    refine Submodule.eq_of_le_of_finrank_eq (by simpa using hleQ) ?_
    rw [← hk1, ← hk2, ← h1, ← h2, h]

end Components

/-! ### One circle factor at a time -/

section Assembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No nonzero lattice vector of `H` is killed by `p(A)`. -/
def CondH (A : Matrix ι ι ℤ) (H : Submodule ℝ (ι → ℝ)) (p : ℚ[X]) : Prop :=
  ∀ γ ∈ intLattice ι, γ ∈ H → aeval (act A) (p.map (algebraMap ℚ ℝ)) γ = 0 → γ = 0

/-- No nonzero integer vector is orthogonal to `E` and to `im p(A)`. -/
def CondE (A : Matrix ι ι ℤ) (E : Submodule ℝ (ι → ℝ)) (p : ℚ[X]) : Prop :=
  ∀ c : ι → ℤ, (∀ e ∈ E, (fun i => (c i : ℝ)) ⬝ᵥ e = 0) →
    (∀ v, (fun i => (c i : ℝ)) ⬝ᵥ aeval (act A) (p.map (algebraMap ℚ ℝ)) v = 0) → c = 0

theorem eq_zero_of_dot_eq_zero {c : ι → ℤ} (h : ∀ v, (fun i => (c i : ℝ)) ⬝ᵥ v = 0) : c = 0 := by
  funext i
  have h1 := h (Pi.single i 1)
  rw [dotProduct_single_one] at h1
  exact_mod_cast h1

theorem act_zero' {κ : Type*} [Fintype κ] [DecidableEq κ] : act (0 : Matrix κ κ ℤ) = 0 :=
  map_zero Tilt.actHom

theorem pow_apply_eq_zero_of {V : Type*} [AddCommGroup V] [Module ℝ V] {T : Module.End ℝ V}
    {N : ℕ} (hN : 1 ≤ N) {v : V} (hv : T v = 0) : (T ^ N) v = 0 := by
  rw [show N = (N - 1) + 1 by omega, pow_succ, Module.End.mul_apply, hv, map_zero]

theorem range_pow_le {V : Type*} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) {N : ℕ}
    (hN : 1 ≤ N) : LinearMap.range (T ^ N) ≤ LinearMap.range T := by
  rintro _ ⟨w, rfl⟩
  refine ⟨(T ^ (N - 1)) w, ?_⟩
  rw [← Module.End.mul_apply, ← pow_succ', show N - 1 + 1 = N by omega]

/-- **The component of a circle factor.** For a circle factor `p = Φ_n` of `χ_A`, a Fitting
decomposition `ℝ^ι = ker p(A)ᴺ ⊕ im p(A)ᴺ`, and an `A`-invariant splitting `E_p ⊕ H_p` of
`ker p(A)ᴺ` transported from the least scheme of the integer matrix of `A` on
`ℤ^ι ∩ ker p(A)ᴺ`: `A` is power-bounded on `H_p`, `H_p` holds no nonzero lattice vector, no
nonzero integer vector orthogonal to `E_p` sees `ker p(A)ᴺ`, and
`dim H_p + δ_p = dim ker p(A) − dim (ker p(A) ∩ im p(A))`. -/
theorem exists_component (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A))
    (hpc : IsCircleFactor p) :
    ∃ N : ℕ, 1 ≤ N ∧
      IsCompl (LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ)) ^ N))
        (LinearMap.range (aeval (act A) (p.map (algebraMap ℚ ℝ)) ^ N)) ∧
      (∀ U : Submodule ℝ (ι → ℝ), (∀ v ∈ U, act A v ∈ U) → PowerBoundedOn (act A) U →
        U ≤ LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ)) ^ N) →
          ∀ v ∈ U, aeval (act A) (p.map (algebraMap ℚ ℝ)) v = 0) ∧
      ∃ Ec Hc : Submodule ℝ (ι → ℝ),
        Ec ⊔ Hc = LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ)) ^ N) ∧
        Disjoint Ec Hc ∧ (∀ v ∈ Ec, act A v ∈ Ec) ∧ (∀ v ∈ Hc, act A v ∈ Hc) ∧
        PowerBoundedOn (act A) Hc ∧ (∀ γ ∈ intLattice ι, γ ∈ Hc → γ = 0) ∧
        (∀ c : ι → ℤ, (∀ e ∈ Ec, (fun i => (c i : ℝ)) ⬝ᵥ e = 0) →
          ∀ v ∈ LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ)) ^ N),
            (fun i => (c i : ℝ)) ⬝ᵥ v = 0) ∧
        finrank ℝ Hc + defect A p = socleCount (act A) (p.map (algebraMap ℚ ℝ)) := by
  obtain ⟨n, hn, rfl⟩ := (isCircleFactor_iff_cyclotomic A hp).mp hpc
  have hpR : (cyclotomic n ℚ).map (algebraMap ℚ ℝ) = cyclotomic n ℝ := map_cyclotomic n _
  have hss_iff := singleBlocks_eq_mult_iff_real A hp
  have hdef : defect A (cyclotomic n ℚ) =
      if singleBlocks A (cyclotomic n ℚ) = mult A (cyclotomic n ℚ) then
        (if n ≤ 2 then 1 else 2) else 0 := by
    rw [defect, natDegree_cyclotomic, min_totient_two hn]
    by_cases h : singleBlocks A (cyclotomic n ℚ) = mult A (cyclotomic n ℚ)
    · rw [ite_eq_left ⟨hpc, h⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right h]
  rw [hdef]
  rw [hpR] at hss_iff ⊢
  obtain ⟨N, hNle, hfit, hkerN⟩ := exists_fitting (aeval (act A) (cyclotomic n ℝ))
  rw [Module.finrank_fintype_fun_eq_card] at hNle hkerN
  obtain ⟨γ₀, -, hγ₀0, hTγ₀⟩ := exists_int_mem_ker A (cyclotomic.irreducible_rat hn)
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
  rw [hpR] at hTγ₀
  have hne : Nonempty ι := by
    obtain ⟨i, -⟩ := Function.ne_iff.mp hγ₀0; exact ⟨i⟩
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hN1 : 1 ≤ N := le_trans hcard hNle
  set T := aeval (act A) (cyclotomic n ℝ) with hT
  set M : Matrix ι ι ℤ := aeval A (cyclotomic n ℤ ^ Fintype.card ι) with hM
  have hactM : act M = T ^ Fintype.card ι := by
    have h := Tilt.aeval_act_map (A := A) (cyclotomic n ℤ ^ Fintype.card ι)
    rw [Polynomial.map_pow, map_cyclotomic, map_pow] at h
    rw [hT, h]; rfl
  have hAM : A * M = M * A := by
    have h := (Commute.all X (cyclotomic n ℤ ^ Fintype.card ι)).map (aeval A)
    rw [aeval_X] at h
    exact h.eq
  obtain ⟨k, B, L, hLinj, hrange, hinter, hLlat, hLsurj⟩ := exists_transport A M hAM
  have hK : LinearMap.range L = LinearMap.ker (T ^ N) := by rw [hrange, hactM, hkerN]
  have hγ₀N : γ₀ ∈ LinearMap.ker (T ^ N) := pow_apply_eq_zero_of hN1 hTγ₀
  have hk : Nonempty (Fin k) := by
    obtain ⟨x, hx⟩ : γ₀ ∈ LinearMap.range L := hK ▸ hγ₀N
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      exfalso; apply hγ₀0
      rw [← hx, Subsingleton.elim x 0, map_zero]
    · exact ⟨⟨0, hpos⟩⟩
  have hBzero : aeval (act B) (cyclotomic n ℝ ^ Fintype.card ι) = 0 := by
    apply LinearMap.ext
    intro x
    apply hLinj
    rw [← L_aeval hinter, LinearMap.zero_apply, map_zero, map_pow]
    have h1 : L x ∈ LinearMap.ker (T ^ N) := hK ▸ LinearMap.mem_range_self L x
    rw [hkerN] at h1
    exact h1
  have hnil : IsNilpotent (aeval B (cyclotomic n ℤ)) := by
    refine ⟨Fintype.card ι, Tilt.eq_zero_of_act_eq_zero ?_⟩
    rw [← Tilt.actHom_apply, map_pow, Tilt.actHom_apply, ← Tilt.aeval_act_cyclotomic_eq,
      ← map_pow, hBzero]
  have hBL := Tilt.isLeast_physDims_single_cyclotomic B hn hnil
  obtain ⟨S, hSadm, hSdim⟩ := hBL.1
  have hLsurj' : ∀ γ ∈ intLattice ι, γ ∈ LinearMap.range L →
      ∃ x ∈ intLattice (Fin k), L x = γ := fun γ hγ hγL => hLsurj γ hγ (hrange ▸ hγL)
  obtain ⟨hsup, hdisj, hEc, hHc, hpbc, hlatc, hdualc, hdimc⟩ :=
    transport_scheme hLinj hinter hLlat hLsurj' S hSadm
  -- kernels of powers of `Φ_n(A)` lie in `ker Φ_n(A)ᴺ`
  have hkerle : ∀ j, LinearMap.ker (aeval (act A) (cyclotomic n ℝ ^ j)) ≤ LinearMap.range L := by
    intro j
    rw [hK, hkerN, map_pow]
    have := Module.End.ker_pow_le_ker_pow_finrank T j
    rwa [Module.finrank_fintype_fun_eq_card] at this
  have hsoc : socleCount (act B) (cyclotomic n ℝ) = socleCount (act A) (cyclotomic n ℝ) := by
    rw [socleCount_eq, socleCount_eq, finrank_ker_transport hLinj hinter (by simpa using hkerle 1),
      finrank_ker_transport hLinj hinter (hkerle 2)]
  have hss : aeval B (cyclotomic n ℤ) = 0 ↔
      singleBlocks A (cyclotomic n ℚ) = mult A (cyclotomic n ℚ) := by
    rw [hss_iff]
    constructor
    · intro h0
      have hB0 : aeval (act B) (cyclotomic n ℝ) = 0 := by
        rw [Tilt.aeval_act_cyclotomic_eq, h0, act_zero']
      apply le_antisymm
      · intro y hy
        obtain ⟨x, rfl⟩ := hkerle 2 hy
        rw [LinearMap.mem_ker, L_aeval hinter, hB0, LinearMap.zero_apply, map_zero]
      · intro v hv
        rw [LinearMap.mem_ker, pow_two, map_mul, Module.End.mul_apply, LinearMap.mem_ker.mp hv,
          map_zero]
    · intro h
      apply Tilt.eq_zero_of_act_eq_zero
      rw [← Tilt.aeval_act_cyclotomic_eq]
      apply LinearMap.ext
      intro x
      apply hLinj
      rw [← L_aeval hinter, LinearMap.zero_apply, map_zero]
      have h1 : LinearMap.ker (T ^ 1) = LinearMap.ker (T ^ Nat.succ 1) := by
        rw [pow_one, Nat.succ_eq_add_one, ← map_pow, h]
      have h2 := Module.End.ker_pow_constant h1 (Fintype.card ι - 1)
      rw [pow_one, show 1 + (Fintype.card ι - 1) = Fintype.card ι by omega] at h2
      have h3 : L x ∈ LinearMap.ker (T ^ N) := hK ▸ LinearMap.mem_range_self L x
      rw [hkerN, ← h2] at h3
      exact h3
  have hSk : finrank ℝ S.E + finrank ℝ S.H = k := by
    rw [Submodule.finrank_add_eq_of_isCompl S.isCompl, Module.finrank_fin_fun]
  have hsock : socleCount (act B) (cyclotomic n ℝ) ≤ k := by
    rw [socleCount]
    have := Submodule.finrank_le (LinearMap.ker (aeval (act B) (cyclotomic n ℝ)))
    rw [Module.finrank_fin_fun] at this
    omega
  refine ⟨N, hN1, hfit, ?_, S.E.map L, S.H.map L, hsup.trans hK, hdisj, hEc, hHc, hpbc,
    hlatc, fun c hc v hv => hdualc c hc v (hK ▸ hv), ?_⟩
  · intro U hU hpbU hUK
    have hS : ∀ z ∈ primitiveRoots n ℂ, ‖z‖ = 1 := fun z hz =>
      ((mem_primitiveRoots hn).mp hz).norm'_eq_one hn.ne'
    have hc : (cyclotomic n ℝ).map (algebraMap ℝ ℂ) = Lagrange.nodal (primitiveRoots n ℂ) id := by
      rw [map_cyclotomic, cyclotomic_eq_prod_X_sub_primitiveRoots
        (Complex.isPrimitiveRoot_exp n hn.ne')]
      rfl
    refine aeval_eq_zero_of_powerBoundedOn (act A) hU hpbU hS hc (N := N) (dvd_refl _) ?_
    intro v hv
    rw [map_pow]
    exact hUK hv
  · rw [hdimc, ← hsoc]
    by_cases h0 : aeval B (cyclotomic n ℤ) = 0
    · have hss' := hss.mp h0
      rw [ite_eq_left hss']
      rw [ite_eq_left h0] at hSdim
      have hB0 : aeval (act B) (cyclotomic n ℝ) = 0 := by
        rw [Tilt.aeval_act_cyclotomic_eq, h0, act_zero']
      have hsocB : socleCount (act B) (cyclotomic n ℝ) = k := by
        rw [socleCount, hB0, LinearMap.ker_zero, LinearMap.range_zero, inf_bot_eq, finrank_bot,
          finrank_top, Module.finrank_fin_fun, Nat.sub_zero]
      rw [hsocB]
      split_ifs at hSdim ⊢ <;> omega
    · rw [ite_eq_right (fun h => h0 (hss.mpr h))]
      rw [ite_eq_right h0] at hSdim
      have : socleCount (act B) (cyclotomic n ℝ) = finrank ℝ ↥(LinearMap.ker
          (aeval (act B) (cyclotomic n ℝ))) - finrank ℝ ↥(LinearMap.ker
          (aeval (act B) (cyclotomic n ℝ)) ⊓ LinearMap.range (aeval (act B) (cyclotomic n ℝ))) :=
        rfl
      rw [Fintype.card_fin, ← this] at hSdim
      omega


/-- **A semisimple circle component.** If `δ_p ≠ 0` (`p = Φ_n` with all Jordan blocks of size
one), then `ker p(A)ᴺ = ker p(A)^{#ι}` is power-bounded and every scheme's physical space meets it
in dimension at least `δ_p`. -/
theorem exists_component_ss (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) (hd : defect A p ≠ 0) :
    ∃ N : ℕ, 1 ≤ N ∧
      IsCompl (LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ)) ^ N))
        (LinearMap.range (aeval (act A) (p.map (algebraMap ℚ ℝ)) ^ N)) ∧
      LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ)) ^ N) =
        LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ) ^ Fintype.card ι)) ∧
      PowerBoundedOn (act A) (LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ)) ^ N)) ∧
      ∀ S : InvariantCPS A, defect A p ≤
        finrank ℝ ↥(S.E ⊓
          LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ) ^ Fintype.card ι))) := by
  have hpcs : IsCircleFactor p ∧ singleBlocks A p = mult A p := by
    by_contra h
    exact hd (by rw [defect, ite_eq_right h])
  obtain ⟨hpc, hss⟩ := hpcs
  have hdef : defect A p = min p.natDegree 2 := by rw [defect, ite_eq_left ⟨hpc, hss⟩]
  obtain ⟨n, hn, rfl⟩ := (isCircleFactor_iff_cyclotomic A hp).mp hpc
  have hpR : (cyclotomic n ℚ).map (algebraMap ℚ ℝ) = cyclotomic n ℝ := map_cyclotomic n _
  have hker2 := (singleBlocks_eq_mult_iff_real A hp).mp hss
  rw [natDegree_cyclotomic, min_totient_two hn] at hdef
  rw [hdef]
  rw [hpR] at hker2 ⊢
  set T := aeval (act A) (cyclotomic n ℝ) with hT
  obtain ⟨N, hNle, hfit, hkerN⟩ := exists_fitting T
  rw [Module.finrank_fintype_fun_eq_card] at hNle hkerN
  obtain ⟨γ₀, -, hγ₀0, -⟩ := exists_int_mem_ker A (cyclotomic.irreducible_rat hn)
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
  have hne : Nonempty ι := by
    obtain ⟨i, -⟩ := Function.ne_iff.mp hγ₀0; exact ⟨i⟩
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hN1 : 1 ≤ N := le_trans hcard hNle
  have hkerT : LinearMap.ker (T ^ N) = LinearMap.ker T := by
    have h1 : LinearMap.ker (T ^ 1) = LinearMap.ker (T ^ Nat.succ 1) := by
      rw [pow_one, Nat.succ_eq_add_one, ← map_pow, hker2]
    have h2 := Module.End.ker_pow_constant h1 (N - 1)
    rw [pow_one, show 1 + (N - 1) = N by omega] at h2
    exact h2.symm
  refine ⟨N, hN1, hfit, by rw [hkerN, map_pow], ?_, fun S => ?_⟩
  · rw [hkerT]
    exact Tilt.powerBounded_of_pow_apply_eq_self hn (fun v hv =>
      Tilt.pow_apply_eq_self_of_cyclotomic (LinearMap.mem_ker.mp hv))
  · have h := Tilt.le_finrank_E_inf_component hn
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp) S
    split_ifs with h2
    · exact h.1
    · exact h.2 (by omega)

omit [Fintype ι] [DecidableEq ι] in
theorem inv_sup {f : Module.End ℝ (ι → ℝ)} {U W : Submodule ℝ (ι → ℝ)}
    (hU : ∀ v ∈ U, f v ∈ U) (hW : ∀ v ∈ W, f v ∈ W) : ∀ v ∈ U ⊔ W, f v ∈ U ⊔ W := by
  intro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact Submodule.add_mem_sup (hU u hu) (hW w hw)

omit [Fintype ι] [DecidableEq ι] in
theorem inv_inf {f : Module.End ℝ (ι → ℝ)} {U W : Submodule ℝ (ι → ℝ)}
    (hU : ∀ v ∈ U, f v ∈ U) (hW : ∀ v ∈ W, f v ∈ W) : ∀ v ∈ U ⊓ W, f v ∈ U ⊓ W :=
  fun v hv => Submodule.mem_inf.mpr ⟨hU v (Submodule.mem_inf.mp hv).1,
    hW v (Submodule.mem_inf.mp hv).2⟩

theorem inv_aeval_pow (A : Matrix ι ι ℤ) {U : Submodule ℝ (ι → ℝ)}
    (hU : ∀ v ∈ U, act A v ∈ U) (q : ℝ[X]) (N : ℕ) : ∀ v ∈ U, (aeval (act A) q ^ N) v ∈ U := by
  intro v hv
  rw [← map_pow]
  exact Tilt.aeval_apply_mem_of_mapsTo (act A) hU _ v hv

theorem inv_ker_pow (A : Matrix ι ι ℤ) (q : ℝ[X]) (N : ℕ) :
    ∀ v ∈ LinearMap.ker (aeval (act A) q ^ N), act A v ∈ LinearMap.ker (aeval (act A) q ^ N) := by
  rw [← map_pow]; exact mapsTo_ker (act A) (q ^ N)

theorem inv_range_pow (A : Matrix ι ι ℤ) (q : ℝ[X]) (N : ℕ) :
    ∀ v ∈ LinearMap.range (aeval (act A) q ^ N),
      act A v ∈ LinearMap.range (aeval (act A) q ^ N) := by
  rw [← map_pow]; exact mapsTo_range (act A) (q ^ N)

/-- **The upper step**: replace the component of one more circle factor. -/
theorem upper_step (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) (hpc : IsCircleFactor p)
    (T : Finset ℚ[X]) (hpT : p ∉ T)
    (hT : ∀ q ∈ T, q ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A))
    {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H) (hE : ∀ v ∈ E, act A v ∈ E)
    (hH : ∀ v ∈ H, act A v ∈ H) (hpb : PowerBoundedOn (act A) H)
    (hcond : ∀ q ∈ T, CondH A H q ∧ CondE A E q) :
    ∃ E' H' : Submodule ℝ (ι → ℝ), IsCompl E' H' ∧ (∀ v ∈ E', act A v ∈ E') ∧
      (∀ v ∈ H', act A v ∈ H') ∧ PowerBoundedOn (act A) H' ∧
      (∀ q, (q = p ∨ q ∈ T) → CondH A H' q ∧ CondE A E' q) ∧
      finrank ℝ H ≤ finrank ℝ H' + defect A p := by
  obtain ⟨N, hN1, hfit, hkill, Ec, Hc, hsup, hdisj, hEc, hHc, hpbc, hlatc, hdualc, hdimc⟩ :=
    exists_component A hp hpc
  set Tp := aeval (act A) (p.map (algebraMap ℚ ℝ)) with hTp
  set K := LinearMap.ker (Tp ^ N) with hK
  set R := LinearMap.range (Tp ^ N) with hR
  have hEcK : Ec ≤ K := hsup ▸ le_sup_left
  have hHcK : Hc ≤ K := hsup ▸ le_sup_right
  have hET : ∀ v ∈ E, Tp v ∈ E := Tilt.aeval_apply_mem_of_mapsTo (act A) hE _
  have hHT : ∀ v ∈ H, Tp v ∈ H := Tilt.aeval_apply_mem_of_mapsTo (act A) hH _
  have hRsplit : (E ⊓ R) ⊔ (H ⊓ R) = R :=
    sup_inf_range_eq hc (inv_aeval_pow A hE _ N) (inv_aeval_pow A hH _ N)
  have hEsplit : (E ⊓ K) ⊔ (E ⊓ R) = E := sup_inf_fitting hfit hET
  have hHsplit : (H ⊓ K) ⊔ (H ⊓ R) = H := sup_inf_fitting hfit hHT
  have hKinv : ∀ v ∈ K, act A v ∈ K := inv_ker_pow A _ N
  have hRinv : ∀ v ∈ R, act A v ∈ R := inv_range_pow A _ N
  have hcompl := isCompl_replace hfit hc hRsplit hEcK hHcK hsup hdisj
  -- the circle factors of `T`
  have hcop : ∀ q ∈ T, IsCoprime (q.map (algebraMap ℚ ℝ)) (p.map (algebraMap ℚ ℝ)) := by
    intro q hq
    exact isCoprime_of_mem (hT q hq) hp (fun h => hpT (h ▸ hq))
  refine ⟨(E ⊓ R) ⊔ Ec, (H ⊓ R) ⊔ Hc, hcompl, inv_sup (inv_inf hE hRinv) hEc,
    inv_sup (inv_inf hH hRinv) hHc,
    powerBoundedOn_sup _ (PowerBoundedOn.mono' hpb inf_le_left) hpbc, ?_, ?_⟩
  · rintro q (rfl | hq)
    · constructor
      · intro γ hγ hγH hγT
        have hγK : γ ∈ K := pow_apply_eq_zero_of hN1 hγT
        exact hlatc γ hγ (mem_right_of_mem_sup hfit inf_le_right hHcK hγH hγK)
      · intro c hcE hcT
        apply eq_zero_of_dot_eq_zero
        intro v
        have hv : v ∈ K ⊔ R := by rw [hfit.sup_eq_top]; exact Submodule.mem_top
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
        rw [dotProduct_add, hdualc c (fun e he => hcE e (Submodule.mem_sup_right he)) a ha]
        obtain ⟨w, rfl⟩ := range_pow_le Tp hN1 hb
        rw [hcT w, add_zero]
    · obtain ⟨hcH, hcE⟩ := hcond q hq
      have hqR : LinearMap.ker (aeval (act A) (q.map (algebraMap ℚ ℝ))) ≤ R := by
        rw [hR, ← map_pow]
        exact ker_le_range_of_coprime (act A) ((hcop q hq).pow_right)
      have hKq : K ≤ LinearMap.range (aeval (act A) (q.map (algebraMap ℚ ℝ))) := by
        rw [hK, ← map_pow]
        exact ker_le_range_of_coprime (act A) ((hcop q hq).symm.pow_left)
      constructor
      · intro γ hγ hγH hγq
        have hγR : γ ∈ R := hqR hγq
        exact hcH γ hγ (Submodule.mem_inf.mp
          (mem_left_of_mem_sup hfit inf_le_right hHcK hγH hγR)).1 hγq
      · intro c hcE' hcq
        apply hcE c _ hcq
        intro e he
        rw [← hEsplit] at he
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp he
        rw [dotProduct_add, hcE' b (Submodule.mem_sup_left hb)]
        obtain ⟨w, hw⟩ := hKq (Submodule.mem_inf.mp ha).2
        rw [← hw, hcq w, add_zero]
  · -- dimensions
    have hHK_inv : ∀ v ∈ H ⊓ K, act A v ∈ H ⊓ K := inv_inf hH hKinv
    have hkill' := hkill (H ⊓ K) hHK_inv (PowerBoundedOn.mono' hpb inf_le_left) inf_le_right
    have hcomp : IsCompl (H ⊓ K) (E ⊔ (H ⊓ R)) := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx1 hx2
        obtain ⟨e, he, h, hh, rfl⟩ := Submodule.mem_sup.mp hx2
        have hxH := (Submodule.mem_inf.mp hx1).1
        have he0 : e = 0 := (Submodule.disjoint_def.mp hc.disjoint) e he
          (by have := H.sub_mem hxH (Submodule.mem_inf.mp hh).1; rwa [add_sub_cancel_right] at this)
        rw [he0, zero_add] at hx1 ⊢
        exact (Submodule.disjoint_def.mp hfit.disjoint) h (Submodule.mem_inf.mp hx1).2
          (Submodule.mem_inf.mp hh).2
      · rw [codisjoint_iff, ← sup_assoc, sup_comm (H ⊓ K) E, sup_assoc, hHsplit, hc.sup_eq_top]
    have hsb := (socle_bound (act A) (p.map (algebraMap ℚ ℝ)) hcomp
      (inv_sup hE (inv_inf hH hRinv)) hkill').2
    have h1 : finrank ℝ H = finrank ℝ ↥(H ⊓ R) + finrank ℝ ↥(H ⊓ K) := by
      conv_lhs => rw [← hHsplit, sup_comm]
      exact finrank_sup_of_le hfit inf_le_right inf_le_right
    have h2 : finrank ℝ ↥((H ⊓ R) ⊔ Hc) = finrank ℝ ↥(H ⊓ R) + finrank ℝ Hc :=
      finrank_sup_of_le hfit inf_le_right hHcK
    rw [socleCount] at hdimc
    omega

/-- **The lower step**: absorb the component of one more semisimple circle factor into the
internal space. -/
theorem lower_step (A : Matrix ι ι ℤ) (S : InvariantCPS A) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A))
    (T : Finset ℚ[X]) (hpT : p ∉ T)
    {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H) (hE : ∀ v ∈ E, act A v ∈ E)
    (hH : ∀ v ∈ H, act A v ∈ H) (hpb : PowerBoundedOn (act A) H)
    (hagree : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A), q ∉ T →
      E ⊓ LinearMap.ker (aeval (act A) (q.map (algebraMap ℚ ℝ) ^ Fintype.card ι)) =
        S.E ⊓ LinearMap.ker (aeval (act A) (q.map (algebraMap ℚ ℝ) ^ Fintype.card ι))) :
    ∃ E' H' : Submodule ℝ (ι → ℝ), IsCompl E' H' ∧ (∀ v ∈ E', act A v ∈ E') ∧
      (∀ v ∈ H', act A v ∈ H') ∧ PowerBoundedOn (act A) H' ∧
      (∀ q ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A), q ≠ p → q ∉ T →
        E' ⊓ LinearMap.ker (aeval (act A) (q.map (algebraMap ℚ ℝ) ^ Fintype.card ι)) =
          S.E ⊓ LinearMap.ker (aeval (act A) (q.map (algebraMap ℚ ℝ) ^ Fintype.card ι))) ∧
      finrank ℝ H + defect A p ≤ finrank ℝ H' := by
  by_cases hd : defect A p = 0
  · exact ⟨E, H, hc, hE, hH, hpb, fun q hq _ hqT => hagree q hq hqT, by omega⟩
  obtain ⟨N, hN1, hfit, hKc, hpbK, hlow⟩ := exists_component_ss A hp hd
  set Tp := aeval (act A) (p.map (algebraMap ℚ ℝ)) with hTp
  set K := LinearMap.ker (Tp ^ N) with hK
  set R := LinearMap.range (Tp ^ N) with hR
  have hET : ∀ v ∈ E, Tp v ∈ E := Tilt.aeval_apply_mem_of_mapsTo (act A) hE _
  have hHT : ∀ v ∈ H, Tp v ∈ H := Tilt.aeval_apply_mem_of_mapsTo (act A) hH _
  have hRsplit : (E ⊓ R) ⊔ (H ⊓ R) = R :=
    sup_inf_range_eq hc (inv_aeval_pow A hE _ N) (inv_aeval_pow A hH _ N)
  have hHsplit : (H ⊓ K) ⊔ (H ⊓ R) = H := sup_inf_fitting hfit hHT
  have hKinv : ∀ v ∈ K, act A v ∈ K := inv_ker_pow A _ N
  have hRinv : ∀ v ∈ R, act A v ∈ R := inv_range_pow A _ N
  have hcompl := isCompl_replace hfit hc hRsplit (bot_le : (⊥ : Submodule ℝ (ι → ℝ)) ≤ K) le_rfl
    (bot_sup_eq K) disjoint_bot_left
  rw [sup_bot_eq] at hcompl
  refine ⟨E ⊓ R, (H ⊓ R) ⊔ K, hcompl, inv_inf hE hRinv, inv_sup (inv_inf hH hRinv) hKinv,
    powerBoundedOn_sup _ (PowerBoundedOn.mono' hpb inf_le_left) hpbK, ?_, ?_⟩
  · intro q hq hqp hqT
    have hle : LinearMap.ker (aeval (act A) (q.map (algebraMap ℚ ℝ) ^ Fintype.card ι)) ≤ R := by
      rw [hR, ← map_pow]
      exact ker_le_range_of_coprime (act A)
        ((isCoprime_of_mem hq hp hqp).pow_left.pow_right)
    rw [inf_assoc, inf_eq_right.mpr hle]
    exact hagree q hq hqT
  · have hEKsplit := Tilt.sup_inf_ker_eq hc (f := Tp ^ N)
      (inv_aeval_pow A hE (p.map (algebraMap ℚ ℝ)) N)
      (inv_aeval_pow A hH (p.map (algebraMap ℚ ℝ)) N)
    rw [← hK] at hEKsplit
    have hdisjEK : (E ⊓ K) ⊓ (H ⊓ K) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      exact (Submodule.mem_bot ℝ).mpr ((Submodule.disjoint_def.mp hc.disjoint) v
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hv).1).1
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hv).2).1)
    have h0 := Submodule.finrank_sup_add_finrank_inf_eq (E ⊓ K) (H ⊓ K)
    rw [hdisjEK, finrank_bot, add_zero, hEKsplit] at h0
    have h1 : finrank ℝ H = finrank ℝ ↥(H ⊓ R) + finrank ℝ ↥(H ⊓ K) := by
      conv_lhs => rw [← hHsplit, sup_comm]
      exact finrank_sup_of_le hfit inf_le_right inf_le_right
    have h2 : finrank ℝ ↥((H ⊓ R) ⊔ K) = finrank ℝ ↥(H ⊓ R) + finrank ℝ K :=
      finrank_sup_of_le hfit inf_le_right le_rfl
    have h3 : defect A p ≤ finrank ℝ ↥(E ⊓ K) := by
      have h4 := hagree p hp hpT
      rw [← hKc] at h4
      rw [h4]
      have := hlow S
      rwa [← hKc] at this
    omega

theorem upper_aux (A : Matrix ι ι ℤ) (D : DiskSplit (act A).charpoly) (T : Finset ℚ[X]) :
    (∀ q ∈ T, q ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A) ∧
      IsCircleFactor q) →
    ∃ E H : Submodule ℝ (ι → ℝ), IsCompl E H ∧ (∀ v ∈ E, act A v ∈ E) ∧
      (∀ v ∈ H, act A v ∈ H) ∧ PowerBoundedOn (act A) H ∧
      (∀ q ∈ T, CondH A H q ∧ CondE A E q) ∧
      D.qs.natDegree + socleCount (act A) D.c ≤ finrank ℝ H + ∑ q ∈ T, defect A q := by
  induction T using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨H, E, hc, hH, hE, hpb, hdim⟩ := exists_powerBounded_summand (act A) D
    exact ⟨E, H, hc.symm, hE, hH, hpb, by simp, by simp [hdim]⟩
  | insert p T hpT ih =>
    intro hT
    obtain ⟨E, H, hc, hE, hH, hpb, hcond, hdim⟩ :=
      ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    obtain ⟨hp, hpc⟩ := hT p (Finset.mem_insert_self p T)
    obtain ⟨E', H', hc', hE', hH', hpb', hcond', hdim'⟩ := upper_step A hp hpc T hpT
      (fun q hq => (hT q (Finset.mem_insert_of_mem hq)).1) hc hE hH hpb hcond
    refine ⟨E', H', hc', hE', hH', hpb', fun q hq => hcond' q (Finset.mem_insert.mp hq), ?_⟩
    rw [Finset.sum_insert hpT]
    omega

theorem lower_aux (A : Matrix ι ι ℤ) (S : InvariantCPS A) (hS : S.Admissible) (T : Finset ℚ[X]) :
    (∀ q ∈ T, q ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) →
    ∃ E H : Submodule ℝ (ι → ℝ), IsCompl E H ∧ (∀ v ∈ E, act A v ∈ E) ∧
      (∀ v ∈ H, act A v ∈ H) ∧ PowerBoundedOn (act A) H ∧
      (∀ q ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A), q ∉ T →
        E ⊓ LinearMap.ker (aeval (act A) (q.map (algebraMap ℚ ℝ) ^ Fintype.card ι)) =
          S.E ⊓ LinearMap.ker (aeval (act A) (q.map (algebraMap ℚ ℝ) ^ Fintype.card ι))) ∧
      finrank ℝ S.H + ∑ q ∈ T, defect A q ≤ finrank ℝ H := by
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨S.E, S.H, S.isCompl, S.mapsTo_E, S.mapsTo_H, (admissible_iff_powerBounded S).mp hS,
      fun _ _ _ => rfl, by simp⟩
  | insert p T hpT ih =>
    intro hT
    obtain ⟨E, H, hc, hE, hH, hpb, hagree, hdim⟩ :=
      ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    obtain ⟨E', H', hc', hE', hH', hpb', hagree', hdim'⟩ :=
      lower_step A S (hT p (Finset.mem_insert_self p T)) T hpT hc hE hH hpb hagree
    refine ⟨E', H', hc', hE', hH', hpb', fun q hq hqT => ?_, ?_⟩
    · rw [Finset.mem_insert, not_or] at hqT
      exact hagree' q hq hqT.1 hqT.2
    · rw [Finset.sum_insert hpT]
      omega

end Assembly


/-! ### The least physical dimension -/

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isLeast_of_diskSplit (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (D : DiskSplit (act A).charpoly) :
    IsLeast (physDims A) (Fintype.card ι - (D.qs.natDegree + socleCount (act A) D.c) +
      ∑ q ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        defect A q) := by
  classical
  set F := (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset with hF
  set P := D.qs.natDegree + socleCount (act A) D.c with hP
  have hPle : P ≤ Fintype.card ι := by
    obtain ⟨H, E, -, -, -, -, hdim⟩ := exists_powerBounded_summand (act A) D
    rw [hP, ← hdim]
    have := Submodule.finrank_le H
    rwa [Module.finrank_fintype_fun_eq_card] at this
  set Fc := F.filter IsCircleFactor with hFc
  have hsum : ∑ q ∈ Fc, defect A q = ∑ q ∈ F, defect A q := by
    rw [hFc, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    split_ifs with h
    · rfl
    · rw [defect, ite_eq_right (fun h' => h h'.1)]
  have hlow : ∀ S : InvariantCPS A, S.Admissible →
      Fintype.card ι - P + ∑ q ∈ F, defect A q ≤ finrank ℝ S.E := by
    intro S hS
    obtain ⟨E, H, hc, hE, hH, hpb, -, hdim⟩ :=
      lower_aux A S hS F (fun q hq => Multiset.mem_toFinset.mp hq)
    have hle := finrank_le_of_powerBoundedOn (act A) D hc.symm hH hE hpb
    have hSdim : finrank ℝ S.E + finrank ℝ S.H = Fintype.card ι := by
      rw [Submodule.finrank_add_eq_of_isCompl S.isCompl, Module.finrank_fintype_fun_eq_card]
    omega
  have hmemFc : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      IsCircleFactor q → q ∈ Fc := fun q hq hqc => by
    rw [hFc, Finset.mem_filter, Multiset.mem_toFinset]; exact ⟨hq, hqc⟩
  obtain ⟨E, H, hc, hE, hH, hpb, hcond, hdim⟩ := upper_aux A D Fc (fun q hq => by
    rw [hFc, Finset.mem_filter, Multiset.mem_toFinset] at hq; exact hq)
  obtain ⟨S, hSE, hSH, hSadm⟩ := exists_scheme_of_circle A hdet hc hE hH hpb
    (fun p hp hpc => (hcond p (hmemFc p hp hpc)).1)
    (fun p hp hpc => (hcond p (hmemFc p hp hpc)).2)
  refine ⟨⟨S, hSadm, ?_⟩, fun d ⟨S', hS', hd⟩ => hd ▸ hlow S' hS'⟩
  have h1 := hlow S hSadm
  have hEH : finrank ℝ E + finrank ℝ H = Fintype.card ι := by
    rw [Submodule.finrank_add_eq_of_isCompl hc, Module.finrank_fintype_fun_eq_card]
  rw [hSE] at h1 ⊢
  rw [hsum] at hdim
  omega

theorem card_sub_eq_sum (A : Matrix ι ι ℤ) (D : DiskSplit (act A).charpoly) :
    Fintype.card ι - (D.qs.natDegree + socleCount (act A) D.c) =
      ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        (mult A p * expandingRoots p + circleRoots p * (mult A p - singleBlocks A p)) := by
  have hP : D.qs.natDegree + socleCount (act A) D.c =
      ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        (mult A p * insideRoots p + circleRoots p * singleBlocks A p) :=
    (isGreatest_powerBounded_summand (act A) D).unique (largest_powerBounded_summand_factors A)
  rw [hP, card_eq_sum_mult_natDegree A]
  have hterm : ∀ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
      mult A p * p.natDegree = (mult A p * insideRoots p + circleRoots p * singleBlocks A p) +
        (mult A p * expandingRoots p + circleRoots p * (mult A p - singleBlocks A p)) := by
    intro p hp
    have hle := singleBlocks_le_mult A (Multiset.mem_toFinset.mp hp)
    rw [← insideRoots_add_circleRoots_add_expandingRoots p]
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
    rw [ht, Nat.add_sub_cancel_left]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Nat.add_sub_cancel_left]

/-- **The least physical dimension, every nonsingular integer matrix.** -/
theorem isLeast_physDims_dimensionFormula (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) :
    IsLeast (physDims A) (dimensionFormula A) := by
  obtain ⟨D⟩ := exists_diskSplit (act A).charpoly (LinearMap.charpoly_monic _)
  have h := isLeast_of_diskSplit A hdet D
  rw [card_sub_eq_sum A D, ← Finset.sum_add_distrib] at h
  have heq : dimensionFormula A =
      ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        ((mult A p * expandingRoots p + circleRoots p * (mult A p - singleBlocks A p)) +
          defect A p) := rfl
  rw [heq]
  exact h

end Main


/-! ### Rational similarity -/

section Similarity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pow_conj {A B P : Matrix ι ι ℚ} (h : P * A = B * P) (k : ℕ) : P * A ^ k = B ^ k * P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', ← mul_assoc, h, mul_assoc, ih, ← mul_assoc]

theorem aeval_conj {A B P : Matrix ι ι ℚ} (h : P * A = B * P) (q : ℚ[X]) :
    P * aeval A q = aeval B q * P := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc,
      pow_conj h k, ← mul_assoc]

theorem finrank_ker_toLin' (M : Matrix ι ι ℚ) :
    finrank ℚ (LinearMap.ker (Matrix.toLin' M)) = Fintype.card ι - M.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  rw [Module.finrank_fintype_fun_eq_card] at h
  have : M.rank = finrank ℚ (LinearMap.range (Matrix.toLin' M)) := by
    rw [Matrix.rank, Matrix.toLin'_apply']
  omega

theorem kerRankQ_eq (A : Matrix ι ι ℤ) (p : ℚ[X]) (k : ℕ) :
    kerRankQ A p k = Fintype.card ι - (aeval (A.map (Int.castRingHom ℚ)) (p ^ k)).rank := by
  rw [kerRankQ, ← finrank_ker_toLin', show Matrix.toLin' (A.map (Int.cast : ℤ → ℚ)) = actQ A
    from rfl, aeval_actQ A (p ^ k)]

/-- **Rational similarity.** If `P A = B P` for an invertible rational matrix `P`, the Jordan data
of `A` and `B` agree, so the formula takes the same value. -/
theorem dimensionFormula_eq_of_conj {A B : Matrix ι ι ℤ} {P : Matrix ι ι ℚ} (hP : IsUnit P.det)
    (h : P * A.map (Int.castRingHom ℚ) = B.map (Int.castRingHom ℚ) * P) :
    charpolyQ B = charpolyQ A ∧ B.det = A.det ∧ dimensionFormula B = dimensionFormula A := by
  have hB : B.map (Int.castRingHom ℚ) = P * A.map (Int.castRingHom ℚ) * P⁻¹ := by
    rw [h, mul_assoc, Matrix.mul_nonsing_inv P hP, mul_one]
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
  have hχ : charpolyQ B = charpolyQ A := by
    have h1 := Matrix.charpoly_units_conj hu.unit (A.map (Int.castRingHom ℚ))
    simp only [IsUnit.unit_spec] at h1
    rw [← hB, Matrix.charpoly_map, Matrix.charpoly_map] at h1
    exact h1
  have hdet : B.det = A.det := by
    have h1 : (B.map (Int.castRingHom ℚ)).det = (A.map (Int.castRingHom ℚ)).det := by
      rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff,
        Matrix.charpoly_map, Matrix.charpoly_map]
      have := congrArg (fun f => f.coeff 0) hχ
      simp only [charpolyQ] at this
      rw [this]
    have e1 := RingHom.map_det (Int.castRingHom ℚ) B
    have e2 := RingHom.map_det (Int.castRingHom ℚ) A
    rw [RingHom.mapMatrix_apply] at e1 e2
    rw [← e1, ← e2] at h1
    exact (Int.castRingHom ℚ).injective_int h1
  have hker : ∀ p k, kerRankQ B p k = kerRankQ A p k := by
    intro p k
    rw [kerRankQ_eq, kerRankQ_eq, hB]
    have h2 : aeval (P * A.map (Int.castRingHom ℚ) * P⁻¹) (p ^ k) =
        P * aeval (A.map (Int.castRingHom ℚ)) (p ^ k) * P⁻¹ := by
      have h3 := aeval_conj (A := A.map (Int.castRingHom ℚ))
        (B := P * A.map (Int.castRingHom ℚ) * P⁻¹) (P := P) (by
          rw [mul_assoc (P * _), Matrix.nonsing_inv_mul P hP, mul_one]) (p ^ k)
      rw [h3, Matrix.mul_assoc (aeval (P * A.map (Int.castRingHom ℚ) * P⁻¹) (p ^ k)) P P⁻¹,
        Matrix.mul_nonsing_inv P hP, Matrix.mul_one]
    rw [h2, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by
      rw [Matrix.det_nonsing_inv]; exact hP.ringInverse),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP]
  refine ⟨hχ, hdet, ?_⟩
  unfold dimensionFormula factorContribution factorMult sizeOneBlocks
  rw [hχ]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [hker p 1, hker p 2]

end Similarity

/-! ### Finite order -/

section FiniteOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem root_pow_eq_one (A : Matrix ι ι ℤ) {k : ℕ} (hAk : A ^ k = 1) {p : ℚ[X]}
    (hp : p ∣ charpolyQ A) {z : ℂ} (hz : aeval z p = 0) : z ^ k = 1 := by
  set AC : Matrix ι ι ℂ := A.map (Int.castRingHom ℂ) with hAC
  have hroot : IsRoot AC.charpoly z := by
    rw [hAC, Matrix.charpoly_map, IsRoot]
    obtain ⟨g, hg⟩ := hp
    have h1 : (A.charpoly.map (Int.castRingHom ℂ)) = (charpolyQ A).map (algebraMap ℚ ℂ) := by
      rw [charpolyQ, Polynomial.map_map]; congr 1
    rw [h1, eval_map_algebraMap, hg, map_mul, hz, zero_mul]
  have hspec : z ∈ spectrum ℂ (Matrix.toLin' AC) := by
    rw [Matrix.spectrum_toLin']
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  obtain ⟨w, hw⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hspec).exists_hasEigenvector
  have hpow : (Matrix.toLin' AC) ^ k = 1 := by
    have e := map_pow (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)) AC k
    have e1 : ∀ M : Matrix ι ι ℂ, Matrix.toLinAlgEquiv' M = Matrix.toLin' M := fun M => rfl
    rw [e1, e1] at e
    rw [← e, hAC, ← Matrix.map_pow, hAk, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.toLin'_one]
    rfl
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := (X ^ k - 1 : ℂ[X])) hw
  rw [map_sub, map_pow, aeval_X, map_one, hpow, sub_self, LinearMap.zero_apply] at h1
  have h2 := (smul_eq_zero.mp h1.symm).resolve_right hw.2
  simp only [eval_sub, eval_pow, eval_X, eval_one] at h2
  exact sub_eq_zero.mp h2

/-- **Finite order.** If `A^k = 1`, every irreducible factor of `χ_A` over `ℚ` is cyclotomic,
every Jordan block has size one, and the formula counts `min (deg p, 2)` per distinct factor. -/
theorem finite_order_formula (A : Matrix ι ι ℤ) {k : ℕ} (hk : 0 < k) (hAk : A ^ k = 1) :
    (∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ) ∧
    A.det ≠ 0 ∧
    dimensionFormula A = ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
      min p.natDegree 2 := by
  have hcirc : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      IsCircleFactor p := by
    intro p hp z hz
    have hpi := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
    have hz' : aeval z p = 0 := by
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero hpi.ne_zero), IsRoot,
        eval_map_algebraMap] at hz
      exact hz
    exact Complex.norm_eq_one_of_pow_eq_one (root_pow_eq_one A hAk
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp) hz') hk.ne'
  have hdet : A.det ≠ 0 := by
    intro h0
    have h1 : (A ^ k).det = 1 := by rw [hAk, Matrix.det_one]
    rw [Matrix.det_pow, h0, zero_pow hk.ne'] at h1
    exact zero_ne_one h1
  refine ⟨fun p hp => (isCircleFactor_iff_cyclotomic A hp).mp (hcirc p hp), hdet, ?_⟩
  unfold dimensionFormula
  refine Finset.sum_congr rfl (fun p hpF => ?_)
  have hp := Multiset.mem_toFinset.mp hpF
  have hpi := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hpm := Count.monic_of_mem A hp
  -- every Jordan block at the roots of `p` has size one
  have hss : singleBlocks A p = mult A p := by
    rw [singleBlocks_eq_mult_iff_real A hp]
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p (fun h =>
      hpi.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h))
    have hzk := root_pow_eq_one A hAk (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp) hz
    have hdvdQ : p ∣ X ^ k - 1 := by
      rw [minpoly.eq_of_irreducible_of_monic hpi hz hpm]
      apply minpoly.dvd
      simp [hzk]
    obtain ⟨s, hs⟩ := hdvdQ
    have hsepR : ((X ^ k - 1 : ℚ[X]).map (algebraMap ℚ ℝ)).Separable := by
      rw [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
      exact separable_X_pow_sub_C (1 : ℝ) (by exact_mod_cast hk.ne') one_ne_zero |>.of_dvd
        (by simp)
    rw [hs, Polynomial.map_mul] at hsepR
    have hcop := hsepR.isCoprime
    have hkill : aeval (act A) ((X ^ k - 1 : ℚ[X]).map (algebraMap ℚ ℝ)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one, map_sub, map_pow,
        aeval_X, map_one, ← Tilt.actHom_apply, ← map_pow, hAk, map_one, sub_self]
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hw1 : aeval (act A) (p.map (algebraMap ℚ ℝ)) (aeval (act A) (p.map (algebraMap ℚ ℝ)) v)
          = 0 := by rw [← Module.End.mul_apply, ← map_mul, ← pow_two]; exact hv
      have hw2 : aeval (act A) (s.map (algebraMap ℚ ℝ)) (aeval (act A) (p.map (algebraMap ℚ ℝ)) v)
          = 0 := by
        rw [← Module.End.mul_apply, ← map_mul, ← Polynomial.map_mul, mul_comm, ← hs, hkill,
          LinearMap.zero_apply]
      exact (Submodule.disjoint_def.mp (Polynomial.disjoint_ker_aeval_of_isCoprime (act A) hcop))
        _ (LinearMap.mem_ker.mpr hw1) (LinearMap.mem_ker.mpr hw2)
    · intro v hv
      rw [LinearMap.mem_ker, pow_two, map_mul, Module.End.mul_apply, LinearMap.mem_ker.mp hv,
        map_zero]
  have hexp : expandingRootCount p = 0 := by
    rw [expandingRootCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro z hz
    rw [hcirc p hp z hz]; exact lt_irrefl 1
  have hss' : sizeOneBlocks A p = factorMult A p := hss
  unfold factorContribution
  rw [hexp, hss', Nat.sub_self, mul_zero, mul_zero, zero_add, ite_eq_left ⟨hcirc p hp, rfl⟩,
    zero_add]

end FiniteOrder


/-! ### Dimension one -/

section DimensionOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem counts_of_circle {p : ℚ[X]} (hpc : IsCircleFactor p) :
    circleRootCount p = p.natDegree ∧ expandingRootCount p = 0 := by
  have hall : (p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ‖z‖ = 1) =
      (p.map (algebraMap ℚ ℂ)).roots := Multiset.filter_eq_self.mpr (fun z hz => hpc z hz)
  refine ⟨?_, ?_⟩
  · rw [circleRootCount, hall]
    exact IsAlgClosed.card_roots_map_eq_natDegree_of_injective _ (algebraMap ℚ ℂ).injective
  · rw [expandingRootCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro z hz; rw [hpc z hz]; exact lt_irrefl 1

open Classical in
theorem one_le_factorContribution (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) :
    1 ≤ factorContribution A p := by
  have hpi := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hdeg := Irreducible.natDegree_pos hpi
  have hm := one_le_mult A hp
  have hle := singleBlocks_le_mult A hp
  unfold factorContribution
  change 1 ≤ mult A p * expandingRootCount p + circleRootCount p * (mult A p - singleBlocks A p) +
    (if IsCircleFactor p ∧ singleBlocks A p = mult A p then min p.natDegree 2 else 0)
  by_cases hpc : IsCircleFactor p
  · by_cases hss : singleBlocks A p = mult A p
    · rw [ite_eq_left ⟨hpc, hss⟩]
      have : 1 ≤ min p.natDegree 2 := le_min hdeg (by norm_num)
      omega
    · rw [ite_eq_right (fun h => hss h.2), (counts_of_circle hpc).1]
      have h1 : 1 ≤ mult A p - singleBlocks A p := by omega
      have h2 : 1 ≤ p.natDegree * (mult A p - singleBlocks A p) := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
      omega
  · obtain ⟨z, hz, hz1⟩ := exists_expanding_root A hdet hp hpc
    have hu : 1 ≤ expandingRootCount p := by
      rw [expandingRootCount, Nat.one_le_iff_ne_zero, Ne, Multiset.card_eq_zero]
      intro h0
      have : z ∈ (p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖) :=
        Multiset.mem_filter.mpr ⟨hz, hz1⟩
      rw [h0] at this
      exact Multiset.notMem_zero _ this
    have : 1 ≤ mult A p * expandingRootCount p := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    omega

open Classical in
/-- **Dimension one.** If the formula equals `1`, then `χ_A` is irreducible over `ℚ` with exactly
one root of modulus `> 1`, or `A = ±1`. -/
theorem dimensionFormula_eq_one (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (h1 : dimensionFormula A = 1) :
    (Irreducible (charpolyQ A) ∧ unstableCount A = 1) ∨ (Nonempty ι ∧ (A = 1 ∨ A = -1)) := by
  set nf := UniqueFactorizationMonoid.normalizedFactors (charpolyQ A) with hnf
  set F := nf.toFinset with hF
  have hge : F.card ≤ dimensionFormula A := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun p hp => one_le_factorContribution A hdet
      (Multiset.mem_toFinset.mp hp))
  have hFne : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [dimensionFormula, ← hnf, ← hF, h0, Finset.sum_empty] at h1
    exact zero_ne_one h1
  obtain ⟨p, hFp⟩ := Finset.card_eq_one.mp (show F.card = 1 by have := hFne.card_pos; omega)
  have hpF : p ∈ F := by rw [hFp]; exact Finset.mem_singleton_self p
  have hp : p ∈ nf := Multiset.mem_toFinset.mp hpF
  have hfp : factorContribution A p = 1 := by
    rw [dimensionFormula, ← hnf, ← hF, hFp, Finset.sum_singleton] at h1
    exact h1
  have hpi := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hdeg := Irreducible.natDegree_pos hpi
  have hm := one_le_mult A hp
  have hle := singleBlocks_le_mult A hp
  -- `χ_A = p ^ m`
  have hall : ∀ q ∈ nf, q = p := fun q hq => by
    have : q ∈ F := Multiset.mem_toFinset.mpr hq
    rw [hFp] at this; exact Finset.mem_singleton.mp this
  have hrep : nf = Multiset.replicate (mult A p) p := by
    rw [Multiset.eq_replicate]
    refine ⟨?_, hall⟩
    rw [mult, ← hnf, Multiset.count_eq_card.mpr (fun q hq => (hall q hq).symm)]
  have hχ : charpolyQ A = p ^ mult A p := by
    rw [← DimOne.prod_normalizedFactors A, ← hnf, hrep, Multiset.prod_replicate]
  have hcard : Fintype.card ι = mult A p * p.natDegree := by
    rw [card_eq_sum_mult_natDegree A, ← hnf, ← hF, hFp, Finset.sum_singleton]
  unfold factorContribution at hfp
  change mult A p * expandingRootCount p + circleRootCount p * (mult A p - singleBlocks A p) +
    (if IsCircleFactor p ∧ singleBlocks A p = mult A p then min p.natDegree 2 else 0) = 1 at hfp
  by_cases hpc : IsCircleFactor p
  · obtain ⟨hc, hu⟩ := counts_of_circle hpc
    rw [hc, hu, mul_zero, zero_add] at hfp
    by_cases hss : singleBlocks A p = mult A p
    · -- `p = x ∓ 1` and `A = ±1`
      rw [ite_eq_left ⟨hpc, hss⟩, hss, Nat.sub_self, mul_zero, zero_add] at hfp
      have hdeg1 : p.natDegree = 1 := by
        have : min p.natDegree 2 = 1 := hfp
        omega
      obtain ⟨n, hn, hpn⟩ := (isCircleFactor_iff_cyclotomic A hp).mp hpc
      have htot : n.totient = 1 := by rw [← natDegree_cyclotomic n ℚ, ← hpn, hdeg1]
      have hn12 : n = 1 ∨ n = 2 := by
        rcases Nat.totient_eq_one_iff.mp htot with h | h <;> simp [h]
      have hker := (singleBlocks_eq_mult_iff_real A hp).mp hss
      set T := aeval (act A) (p.map (algebraMap ℚ ℝ)) with hT
      have hTpow : T ^ mult A p = 0 := by
        rw [hT, ← map_pow, ← Polynomial.map_pow, ← hχ]
        have h := LinearMap.aeval_self_charpoly (act A)
        rwa [charpoly_act, ← KernelSplit.charpolyQ_map_real] at h
      have hT0 : T = 0 := by
        have h1' : LinearMap.ker (T ^ 1) = LinearMap.ker (T ^ Nat.succ 1) := by
          rw [pow_one, Nat.succ_eq_add_one, hT, ← map_pow, hker]
        have h2 := Module.End.ker_pow_constant h1' (mult A p - 1)
        rw [pow_one, show 1 + (mult A p - 1) = mult A p by omega, hTpow, LinearMap.ker_zero] at h2
        exact LinearMap.ker_eq_top.mp h2
      obtain ⟨γ, -, hγ0, -⟩ := exists_int_mem_ker A hpi
        (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
      obtain ⟨i, -⟩ := Function.ne_iff.mp hγ0
      refine Or.inr ⟨⟨i⟩, ?_⟩
      rcases hn12 with rfl | rfl
      · left
        apply Tilt.eq_one_of_act_eq_one
        rw [hpn, cyclotomic_one, Polynomial.map_sub, map_X, Polynomial.map_one, map_sub, aeval_X,
          map_one] at hT
        exact sub_eq_zero.mp (hT ▸ hT0)
      · right
        have h2 : act A + 1 = 0 := by
          rw [hpn, cyclotomic_two, Polynomial.map_add, map_X, Polynomial.map_one, map_add, aeval_X,
            map_one] at hT
          exact hT ▸ hT0
        have h3 : act (-A) = 1 := by
          rw [Tilt.act_neg, eq_neg_of_add_eq_zero_left h2, neg_neg]
        have := Tilt.eq_one_of_act_eq_one h3
        rw [← neg_neg A, this]
    · -- a Jordan block of size `≥ 2` forces at least two dimensions
      exfalso
      rw [ite_eq_right (fun h => hss h.2), add_zero] at hfp
      obtain ⟨hr1, hr2⟩ := natDegree_mul_singleBlocks A hpi (Count.monic_of_mem A hp)
      have hk2 := kerRank_two A p
      have hk2le : kerRank A p 2 ≤ Fintype.card ι := by
        have := Submodule.finrank_le (LinearMap.ker (aeval (actQ A) (p ^ 2)))
        rwa [Module.finrank_fintype_fun_eq_card] at this
      have hne : kerRank A p 2 ≠ kerRank A p 1 := by
        intro heq
        apply hss
        rw [singleBlocks_eq_mult_iff A hp]
        refine (Submodule.eq_of_le_of_finrank_eq (ker_le_ker_pow A p (by norm_num)) ?_).symm
        rw [show kerRank A p 1 = finrank ℚ (LinearMap.ker (aeval (actQ A) p)) by
          rw [kerRank, pow_one]] at heq
        exact heq.symm
      have hmul : p.natDegree * (mult A p - singleBlocks A p) =
          p.natDegree * mult A p - p.natDegree * singleBlocks A p := Nat.mul_sub _ _ _
      have hle' : p.natDegree * singleBlocks A p ≤ p.natDegree * mult A p :=
        Nat.mul_le_mul_left _ hle
      rw [mul_comm (mult A p)] at hcard
      have hxk : finrank ℚ ↥(LinearMap.ker (aeval (actQ A) p) ⊓ LinearMap.range (aeval (actQ A) p))
          ≤ kerRank A p 1 := by
        rw [kerRank, pow_one]; exact Submodule.finrank_mono inf_le_left
      omega
  · -- one factor with an expanding root
    rw [ite_eq_right (fun h => hpc h.1), add_zero] at hfp
    obtain ⟨z, hz, hz1⟩ := exists_expanding_root A hdet hp hpc
    have hu : 1 ≤ expandingRootCount p := by
      rw [expandingRootCount, Nat.one_le_iff_ne_zero, Ne, Multiset.card_eq_zero]
      intro h0
      have : z ∈ (p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖) :=
        Multiset.mem_filter.mpr ⟨hz, hz1⟩
      rw [h0] at this
      exact Multiset.notMem_zero _ this
    have hmu : mult A p * expandingRootCount p ≤ 1 := by omega
    have hm1 : mult A p = 1 := by
      by_contra hne
      have : 2 * 1 ≤ mult A p * expandingRootCount p := Nat.mul_le_mul (by omega) hu
      omega
    have hu1 : expandingRootCount p = 1 := by rw [hm1, one_mul] at hmu; omega
    left
    refine ⟨by rw [hχ, hm1, pow_one]; exact hpi, ?_⟩
    rw [unstableCount_eq_sum A, ← hnf, ← hF, hFp, Finset.sum_singleton]
    exact show mult A p * expandingRootCount p = 1 by rw [hm1, hu1]

end DimensionOne

end FormulaA

/-! ### The compared statements -/

section Exports

open FormulaA

/-- **(3) The least physical dimension** (`det A ≠ 0`, any `χ_A`). (a) `d(A) = dimensionFormula A`.
(b) The value is an invariant of rational similarity. (c) The circle factors are the cyclotomic
ones (Kronecker). (d) For squarefree `χ_A`: the normal form and the characterization of the
admissible splittings, and `dimensionFormula A = U(A) + circleCount A`. -/
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
  have hA := isLeast_physDims_dimensionFormula A hdet
  refine ⟨hA, fun B P hP h => ?_, fun p hp => isCircleFactor_iff_cyclotomic A hp,
    fun hsf => ?_⟩
  · obtain ⟨-, hdetB, hform⟩ := dimensionFormula_eq_of_conj hP h
    rw [← hform]
    exact isLeast_physDims_dimensionFormula B (hdetB ▸ hdet)
  · obtain ⟨h1, h2, -⟩ := least_physical_dimension_squarefree A hdet hsf
    exact ⟨h1, hA.unique h2⟩

/-- **(5) Dimension one: Pisot or Salem** (`det A ≠ 0`, any `χ_A`). -/
theorem dimension_one_pisot_or_salem {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hdet : A.det ≠ 0) :
    (IsLeast (physDims A) 1 ↔
      (Irreducible (charpolyQ A) ∧ unstableCount A = 1) ∨ (Nonempty ι ∧ (A = 1 ∨ A = -1))) ∧
    (Irreducible (charpolyQ A) → unstableCount A = 1 →
      ∃ r : ℝ, 1 < |r| ∧ (r : ℂ) ∈ eigenvalues A ∧ (∀ z ∈ eigenvalues A, z ≠ r → ‖z‖ ≤ 1) ∧
        ∀ S : InvariantCPS A, S.Admissible → finrank ℝ S.E = 1 →
          S.E = LinearMap.ker (act A - r • LinearMap.id)) := by
  refine ⟨⟨fun h1 => dimensionFormula_eq_one A hdet
    (isLeast_physDims_dimensionFormula A hdet |>.unique h1), ?_⟩, fun hirr hU =>
      (dimension_one_pisot_or_salem_squarefree A hdet hirr.squarefree).2 hirr hU⟩
  rintro (⟨hirr, hU⟩ | ⟨hne, rfl | rfl⟩)
  · exact (dimension_one_pisot_or_salem_squarefree A hdet hirr.squarefree).1.mpr
      (Or.inl ⟨hirr, hU⟩)
  · exact Tilt.isLeast_physDims_one
  · exact Tilt.isLeast_physDims_neg_one

/-- **(6) Finite order.** -/
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
  refine ⟨fun k hk hAk => ?_, (finite_order_case_squarefree A).1,
    (finite_order_case_squarefree A).2⟩
  obtain ⟨hcyc, hdet, hform⟩ := finite_order_formula A hk hAk
  refine ⟨hcyc, ?_⟩
  rw [← hform]
  exact isLeast_physDims_dimensionFormula A hdet

/-- **(7) Jordan blocks on the unit circle.** -/
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
  obtain ⟨h1, h2, h3, h4, h5⟩ := squarefree_hypothesis_needed
  exact ⟨h1, h2, h3, h4, h5, Tilt.tilt_physDims, Tilt.tilt₃_physDims⟩

end Exports

end

end InflationDimension
