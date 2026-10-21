module
public import Mathlib
public import InflationDimension.Admissibility

@[expose] public section
/-!
# Normal form and characterization of invariant splittings, `χ_A` squarefree

Let `A` be an integer matrix whose characteristic polynomial `χ_A` is squarefree over `ℚ`.

* `normal_form`: every `A`-invariant splitting `ℝ^ι = E ⊕ H` is the kernel splitting
  `E = ker q_E(A)`, `H = ker q_H(A)` of the factorization `χ_A = q_E q_H` over `ℝ`, where `q_E`,
  `q_H` are the characteristic polynomials of `A|_E`, `A|_H`.
* `exists_admissible_iff`: the splitting carries an admissible scheme if and only if every root
  of `q_H` lies in the closed unit disk and every irreducible factor of `χ_A` over `ℚ` shares a
  complex root with `q_E`.
* `exists_int_mem_ker`: for every irreducible factor `p` of `χ_A` over `ℚ` (no squarefree
  hypothesis), the lattice `ℤ^ι` meets `ker p(A)` in a nonzero vector: `p(A)` is singular over
  `ℂ` at an eigenvector for a root of `p`, hence singular over `ℚ`, and a rational kernel vector
  is scaled to an integer one.

Necessity of the shared-root condition: a factor `p` sharing no root with `q_E` divides `q_H`,
so the integer vector of `ker p(A)` lies in `H`. Sufficiency: injectivity from the rational
annihilator lemma, density from Kronecker's criterion, and admissibility from the
power-boundedness of `A` on `H`.

The supporting lemmas, in the namespace `InflationDimension.KernelSplit`, are: the dimension lemma
(`finrank_ker_aeval_of_coprime`: for `χ_f = q r` with `q`, `r` monic and coprime, the kernels of
`q(f)` and `r(f)` are complementary and `dim ker q(f) = deg q`), the rational annihilator lemma
(`exists_irreducible_dvd_of_real_annihilator`), injectivity and the absence of integral
functionals for the kernel splitting under the shared-root condition, and power-boundedness on
the kernel of a polynomial with distinct roots in the closed unit disk (Lagrange interpolation of
`z ↦ zⁿ` on the roots).
-/

namespace InflationDimension

open Polynomial Module
open scoped Matrix

noncomputable section

namespace KernelSplit

section General

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

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

theorem mapsTo_ker_aeval (f : Module.End ℝ V) (q : ℝ[X]) :
    ∀ v ∈ LinearMap.ker (aeval f q), f v ∈ LinearMap.ker (aeval f q) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have h1 : aeval f (q * X) = aeval f (X * q) := by rw [mul_comm]
  rw [map_mul, map_mul, aeval_X] at h1
  have := congrArg (fun T : Module.End ℝ V => T v) h1
  simp only [Module.End.mul_apply] at this
  rw [this, hv, map_zero]

/-- Every complex root of `χ_h` is a root of every polynomial annihilating `h`. -/
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

/-- **The dimension lemma.** If `χ_f = q r` with `q`, `r` monic and coprime over `ℝ`, then
`ker q(f)` and `ker r(f)` are complementary and `dim ker q(f) = deg q`. -/
theorem finrank_ker_aeval_of_coprime [FiniteDimensional ℝ V] (f : Module.End ℝ V) {q r : ℝ[X]}
    (hq : q.Monic) (hr : r.Monic) (hχ : f.charpoly = q * r) (hcop : IsCoprime q r) :
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
  have hsplit : f.charpoly = g₁ * g₂ := PowerBounded.charpoly_eq_mul_of_isCompl f U W hcompl hU hW
  have hq0 : aeval (f.restrict hU) q = 0 := by
    ext v
    simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [aeval_restrict_apply]
    exact v.2
  have hr0 : aeval (f.restrict hW) r = 0 := by
    ext v
    simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [aeval_restrict_apply]
    exact v.2
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

end General

section Power

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The coefficients of `Xⁿ mod ∏_{z ∈ s} (X - z)` stay bounded in `n` when the distinct nodes
`s` lie in the closed unit disk. -/
theorem coeff_X_pow_modByMonic_nodal_bounded (s : Finset ℂ) (hs : ∀ z ∈ s, ‖z‖ ≤ 1) (k : ℕ) :
    ∃ K : ℝ, ∀ n : ℕ, ‖((X ^ n : ℂ[X]) %ₘ Lagrange.nodal s id).coeff k‖ ≤ K := by
  classical
  refine ⟨∑ i ∈ s, ‖(Lagrange.basis s id i).coeff k‖, fun n => ?_⟩
  have hmon : (Lagrange.nodal s (id : ℂ → ℂ)).Monic := Lagrange.nodal_monic
  have hinj : Set.InjOn (id : ℂ → ℂ) s := Set.injOn_id _
  set f := (X ^ n : ℂ[X]) %ₘ Lagrange.nodal s id with hf
  have hdeg : f.degree < s.card := by
    have := Polynomial.degree_modByMonic_lt (X ^ n : ℂ[X]) hmon
    rwa [Lagrange.degree_nodal] at this
  have heval : ∀ i ∈ s, f.eval (id i) = i ^ n := by
    intro i hi
    have hsplit := Polynomial.modByMonic_add_div (X ^ n : ℂ[X]) (Lagrange.nodal s (id : ℂ → ℂ))
    have := congrArg (Polynomial.eval i) hsplit
    have hz : eval i (Lagrange.nodal s (id : ℂ → ℂ)) = 0 :=
      Lagrange.eval_nodal_at_node (v := id) hi
    rw [eval_add, eval_mul, hz, zero_mul, add_zero, eval_pow, eval_X] at this
    simpa [hf] using this
  have hint := Lagrange.eq_interpolate_of_eval_eq (r := fun i => i ^ n) hinj hdeg heval
  rw [hint, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [Polynomial.coeff_C_mul, norm_mul, norm_pow]
  have h1 : ‖i‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (hs i hi)
  calc ‖i‖ ^ n * ‖(Lagrange.basis s id i).coeff k‖
      ≤ 1 * ‖(Lagrange.basis s id i).coeff k‖ := by gcongr
    _ = ‖(Lagrange.basis s id i).coeff k‖ := one_mul _

/-- **Power-boundedness on `ker q(f)`** for a real monic `q` whose complex roots are distinct
and lie in the closed unit disk: one constant `C` with `‖fⁿ v‖ ≤ C ‖v‖` for all `n` and all
`v ∈ ker q(f)`. -/
theorem powerBounded_of_nodal (f : Module.End ℝ V) {q : ℝ[X]} (hq : q.Monic) (s : Finset ℂ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ 1) (hqs : q.map (algebraMap ℝ ℂ) = Lagrange.nodal s id) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ LinearMap.ker (aeval f q), ‖(f ^ n) v‖ ≤ C * ‖v‖ := by
  classical
  choose K hK using coeff_X_pow_modByMonic_nodal_bounded s hs
  set m := q.natDegree with hm
  set B : ℕ → ℝ := fun k => ‖LinearMap.toContinuousLinearMap (f ^ k)‖ with hB
  refine ⟨∑ k ∈ Finset.range m, K k * B k, fun n v hv => ?_⟩
  rw [LinearMap.mem_ker] at hv
  by_cases hq1 : q = 1
  · rw [hq1, map_one, Module.End.one_apply] at hv
    simp [hv]
  set r := (X ^ n : ℝ[X]) %ₘ q with hr
  -- `fⁿ v = r(f) v`
  have hfn : (f ^ n) v = aeval f r v := by
    have hsplit := Polynomial.modByMonic_add_div (X ^ n : ℝ[X]) q
    have h2 : aeval f (X ^ n : ℝ[X]) v = aeval f r v + aeval f (q * ((X ^ n) /ₘ q)) v := by
      conv_lhs => rw [← hsplit]
      rw [map_add, LinearMap.add_apply]
    rw [mul_comm, map_mul, Module.End.mul_apply, hv, map_zero, add_zero] at h2
    rw [← h2, map_pow, aeval_X]
  -- coefficients of `r` are those of the complex remainder
  have hrc : ∀ k, ‖r.coeff k‖ ≤ K k := by
    intro k
    have hmap : r.map (algebraMap ℝ ℂ) = (X ^ n : ℂ[X]) %ₘ Lagrange.nodal s id := by
      rw [hr, Polynomial.map_modByMonic _ hq, hqs, Polynomial.map_pow, Polynomial.map_X]
    have := hK k n
    rw [← hmap, Polynomial.coeff_map] at this
    simpa using this
  have hK0 : ∀ k, 0 ≤ K k := fun k => (norm_nonneg _).trans (hK k 0)
  have hBv : ∀ k, ‖(f ^ k) v‖ ≤ B k * ‖v‖ := by
    intro k
    have := (LinearMap.toContinuousLinearMap (f ^ k)).le_opNorm v
    simpa [hB] using this
  have hlt : r.natDegree < m := Polynomial.natDegree_modByMonic_lt _ hq hq1
  rw [hfn, Polynomial.aeval_eq_sum_range' hlt, LinearMap.sum_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul (hrc k) (hBv k) (norm_nonneg _) (hK0 k)

end Power

section Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem charpolyQ_map_real (A : Matrix ι ι ℤ) :
    (charpolyQ A).map (algebraMap ℚ ℝ) = A.charpoly.map (Int.castRingHom ℝ) := by
  rw [charpolyQ, Polynomial.map_map,
    RingHom.ext_int ((algebraMap ℚ ℝ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℝ)]

theorem separable_charpoly_real (A : Matrix ι ι ℤ) (hsf : Squarefree (charpolyQ A)) :
    (A.charpoly.map (Int.castRingHom ℝ)).Separable := by
  have hsep : (charpolyQ A).Separable := PerfectField.separable_iff_squarefree.mpr hsf
  rw [← charpolyQ_map_real]
  exact hsep.map

/-- casting commutes with polynomial evaluation in a matrix -/
theorem aeval_map_matrix (K : Type*) [Field K] [Algebra ℚ K] (A : Matrix ι ι ℚ) (g : ℚ[X]) :
    aeval (A.map (algebraMap ℚ K)) (g.map (algebraMap ℚ K)) =
      (aeval A g).map (algebraMap ℚ K) := by
  rw [aeval_map_algebraMap]
  have h : A.map (algebraMap ℚ K) = (Algebra.ofId ℚ K).mapMatrix A := rfl
  rw [h, aeval_algHom_apply]
  rfl

omit [DecidableEq ι] in
theorem cast_mulVec (M : Matrix ι ι ℚ) (v : ι → ℚ) :
    algebraMap ℚ ℝ ∘ (M *ᵥ v) = M.map (algebraMap ℚ ℝ) *ᵥ (algebraMap ℚ ℝ ∘ v) := by
  funext i
  exact RingHom.map_mulVec (algebraMap ℚ ℝ) M v i

theorem aeval_act (A : Matrix ι ι ℤ) (f : ℝ[X]) (v : ι → ℝ) :
    aeval (act A) f v =
      aeval ((A.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)) f *ᵥ v := by
  have hA : A.map (Int.cast : ℤ → ℝ) = (A.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ) := by
    ext i j; simp
  have h := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℝ) (n := ι)).toAlgHom
    (A.map (Int.cast : ℤ → ℝ)) f
  have e : ∀ M : Matrix ι ι ℝ, Matrix.toLinAlgEquiv' M = Matrix.toLin' M := fun M => rfl
  show aeval (Matrix.toLin' (A.map (Int.cast : ℤ → ℝ))) f v = _
  erw [e] at h
  erw [h, e, Matrix.toLin'_apply, hA]

/-- the annihilator ideal of a vector under a matrix -/
def annIdeal (A : Matrix ι ι ℚ) (γ : ι → ℚ) : Ideal ℚ[X] where
  carrier := {g | aeval A g *ᵥ γ = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add, Matrix.add_mulVec] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c g hg
    simp only [smul_eq_mul, Set.mem_ofPred_eq, map_mul] at *
    rw [← Matrix.mulVec_mulVec, hg, Matrix.mulVec_zero]

theorem mem_annIdeal {A : Matrix ι ι ℚ} {γ : ι → ℚ} {g : ℚ[X]} :
    g ∈ annIdeal A γ ↔ aeval A g *ᵥ γ = 0 := Iff.rfl

/-- **The rational annihilator lemma.** For a rational matrix `A`, a nonzero rational vector
`γ` and a real polynomial `f` with `f(A) γ = 0`, some irreducible factor `p` of `χ_A` over `ℚ`
divides `f` in `ℝ[X]`. -/
theorem exists_irreducible_dvd_of_real_annihilator (A : Matrix ι ι ℚ) {γ : ι → ℚ} (hγ : γ ≠ 0)
    (f : ℝ[X])
    (hf : aeval (A.map (algebraMap ℚ ℝ)) f *ᵥ (algebraMap ℚ ℝ ∘ γ) = 0) :
    ∃ p : ℚ[X], Irreducible p ∧ p ∣ A.charpoly ∧ p.map (algebraMap ℚ ℝ) ∣ f := by
  classical
  set φ := algebraMap ℚ ℝ with hφ
  set I := annIdeal A γ with hI
  set g₀ := Submodule.IsPrincipal.generator I with hg₀
  have hdvd₀ : ∀ h ∈ I, g₀ ∣ h := by
    intro h hh
    rw [← Ideal.span_singleton_generator I, Ideal.mem_span_singleton] at hh
    exact hh
  have hχ : A.charpoly ∈ I := by
    rw [hI, mem_annIdeal, Matrix.aeval_self_charpoly, Matrix.zero_mulVec]
  have hg₀0 : g₀ ≠ 0 := by
    intro h0
    have := hdvd₀ _ hχ
    rw [h0, zero_dvd_iff] at this
    exact (Matrix.charpoly_monic A).ne_zero this
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
    have : aeval A g *ᵥ γ = 0 := hgI
    rw [h1, map_one, Matrix.one_mulVec] at this
    exact hγ this
  have hgu : ¬ IsUnit g := by
    intro hu
    exact hg1 (hgmon.eq_one_of_isUnit hu)
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor hgu hgmon.ne_zero
  refine ⟨p, hp, hpg.trans (hdvd _ hχ), ?_⟩
  suffices hmain : g.map φ ∣ f from (Polynomial.map_dvd φ hpg).trans hmain
  set d := g.natDegree with hd
  set u : Fin d → ι → ℚ := fun k => (A ^ (k : ℕ)) *ᵥ γ with hu
  have hindQ : LinearIndependent ℚ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set h : ℚ[X] := ∑ k : Fin d, monomial (k : ℕ) (c k) with hh
    have hhI : h ∈ I := by
      rw [hI, mem_annIdeal, hh, map_sum, Matrix.sum_mulVec]
      simp only [aeval_monomial]
      have : ∀ k : Fin d, (algebraMap ℚ (Matrix ι ι ℚ) (c k) * A ^ (k : ℕ)) *ᵥ γ
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
  set Aℝ := A.map φ with hAℝ
  set γℝ := φ ∘ γ with hγℝ
  have hpow : ∀ k : ℕ, φ ∘ ((A ^ k) *ᵥ γ) = (Aℝ ^ k) *ᵥ γℝ := by
    intro k
    rw [cast_mulVec, hAℝ, Matrix.map_pow]
  have hgR : aeval Aℝ (g.map φ) *ᵥ γℝ = 0 := by
    rw [hAℝ, aeval_map_matrix, hγℝ, ← cast_mulVec]
    have : aeval A g *ᵥ γ = 0 := hgI
    rw [this]
    funext i; simp
  have hgmonR : (g.map φ).Monic := hgmon.map φ
  set r := f %ₘ g.map φ with hr
  have hrann : aeval Aℝ r *ᵥ γℝ = 0 := by
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
    · have hexp : aeval Aℝ r *ᵥ γℝ = ∑ k : Fin d, r.coeff k • (φ ∘ u k) := by
        rw [Polynomial.aeval_eq_sum_range' hlt, Matrix.sum_mulVec]
        rw [← Fin.sum_univ_eq_sum_range (fun k => (r.coeff k • Aℝ ^ k) *ᵥ γℝ) d]
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

/-- If `χ_A` is squarefree over `ℚ`, `χ_A = q_E q_H` over `ℝ`, and every irreducible factor of
`χ_A` over `ℚ` shares a complex root with `q_E`, then no irreducible rational factor of `χ_A`
divides `q_H`. -/
theorem false_of_irreducible_dvd (A : Matrix ι ι ℤ) (hsf : Squarefree (charpolyQ A))
    {qE qH : ℝ[X]} (hχ : A.charpoly.map (Int.castRingHom ℝ) = qE * qH)
    (hb : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ∃ z : ℂ, aeval z p = 0 ∧ aeval z qE = 0)
    {p : ℚ[X]} (hp : Irreducible p) (hpχ : p ∣ charpolyQ A)
    (hpH : p.map (algebraMap ℚ ℝ) ∣ qH) : False := by
  classical
  obtain ⟨p', hp'mem, hassoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hsf.ne_zero hp hpχ
  obtain ⟨z, hzp', hzE⟩ := hb p' hp'mem
  have hzp : aeval z p = 0 := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu, map_mul] at hzp'
    have hunit : IsUnit (aeval z (u : ℚ[X])) := u.isUnit.map (aeval z)
    exact (mul_eq_zero.mp hzp').resolve_right hunit.ne_zero
  have hzH : aeval z qH = 0 := by
    obtain ⟨r, hr⟩ := hpH
    rw [hr, map_mul, aeval_map_algebraMap, hzp, zero_mul]
  have hsep : (charpolyQ A).Separable := PerfectField.separable_iff_squarefree.mpr hsf
  have hsqC := (hsep.map (f := algebraMap ℚ ℂ)).squarefree
  have heq : (charpolyQ A).map (algebraMap ℚ ℂ) = (qE * qH).map (algebraMap ℝ ℂ) := by
    rw [← hχ, Polynomial.map_map, charpolyQ, Polynomial.map_map,
      RingHom.ext_int ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ))
        ((algebraMap ℝ ℂ).comp (Int.castRingHom ℝ))]
  have hdvd : (X - C z) * (X - C z) ∣ (qE * qH).map (algebraMap ℝ ℂ) := by
    rw [Polynomial.map_mul]
    refine mul_dvd_mul (dvd_iff_isRoot.mpr ?_) (dvd_iff_isRoot.mpr ?_)
    · rw [IsRoot, eval_map_algebraMap]; exact hzE
    · rw [IsRoot, eval_map_algebraMap]; exact hzH
  rw [← heq] at hdvd
  exact (Polynomial.not_isUnit_X_sub_C z) (hsqC _ hdvd)

/-- **Injectivity for the kernel splitting.** Under the shared-root condition, no nonzero
lattice vector lies in `ker q_H(A)`. -/
theorem inj_of_shared_roots (A : Matrix ι ι ℤ) (hsf : Squarefree (charpolyQ A))
    {qE qH : ℝ[X]} (hχ : A.charpoly.map (Int.castRingHom ℝ) = qE * qH)
    (hb : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ∃ z : ℂ, aeval z p = 0 ∧ aeval z qE = 0) :
    ∀ γ ∈ intLattice ι, aeval (act A) qH γ = 0 → γ = 0 := by
  classical
  intro γ hγ hqH
  by_contra hγ0
  obtain ⟨k, hk⟩ : ∃ k : ι → ℤ, ∀ i, (k i : ℝ) = γ i := by
    obtain ⟨k, rfl⟩ := mem_intLattice_iff.mp hγ
    exact ⟨k, fun i => rfl⟩
  set AQ : Matrix ι ι ℚ := A.map (Int.castRingHom ℚ) with hAQ
  set γQ : ι → ℚ := fun i => (k i : ℚ) with hγQ
  have hγeq : γ = algebraMap ℚ ℝ ∘ γQ := by
    funext i; simp [γQ, ← hk i]
  have hγQ0 : γQ ≠ 0 := by
    intro h
    apply hγ0
    rw [hγeq, h]
    funext i; simp
  have hann : aeval (AQ.map (algebraMap ℚ ℝ)) qH *ᵥ (algebraMap ℚ ℝ ∘ γQ) = 0 := by
    rw [← hγeq, hAQ, ← aeval_act]
    exact hqH
  obtain ⟨p, hp, hpχ, hpH⟩ := exists_irreducible_dvd_of_real_annihilator AQ hγQ0 qH hann
  have hχQ : AQ.charpoly = charpolyQ A := by
    rw [hAQ, Matrix.charpoly_map]; rfl
  rw [hχQ] at hpχ
  exact false_of_irreducible_dvd A hsf hχ hb hp hpχ hpH

theorem aeval_transpose_matrix (M : Matrix ι ι ℝ) (f : ℝ[X]) : aeval Mᵀ f = (aeval M f)ᵀ := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.transpose_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_smul, Matrix.transpose_pow]

/-- **No integral functional for the kernel splitting.** Under the shared-root condition, no
nonzero real functional that is integer-valued on `ℤ^ι` vanishes on `ker q_E(A)`. -/
theorem noIntegralFunctional_of_shared_roots (A : Matrix ι ι ℤ) (hsf : Squarefree (charpolyQ A))
    {qE qH : ℝ[X]} (hχ : A.charpoly.map (Int.castRingHom ℝ) = qE * qH)
    (hb : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ∃ z : ℂ, aeval z p = 0 ∧ aeval z qE = 0) :
    ∀ ξ : (ι → ℝ) →ₗ[ℝ] ℝ, (∀ γ ∈ intLattice ι, ∃ z : ℤ, ξ γ = z) →
      (∀ e ∈ LinearMap.ker (aeval (act A) qE), ξ e = 0) → ξ = 0 := by
  classical
  intro ξ hint hvan
  by_contra hξ0
  have hsingle : ∀ i, (Pi.single i (1 : ℝ) : ι → ℝ) ∈ intLattice ι := fun i =>
    Submodule.subset_span ⟨i, by simp [Pi.basisFun_apply]⟩
  choose k hk using fun i => hint _ (hsingle i)
  set cQ : ι → ℚ := fun i => (k i : ℚ) with hcQ
  have hξ : ∀ v, ξ v = (algebraMap ℚ ℝ ∘ cQ) ⬝ᵥ v := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ ξ v, dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hk' : ξ (fun j => if i = j then (1 : ℝ) else 0) = k i := by
      rw [← hk i]
      congr 1
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [hk', smul_eq_mul, mul_comm]
    simp [cQ]
  have hcQ0 : cQ ≠ 0 := by
    intro h
    apply hξ0
    apply LinearMap.ext
    intro v
    rw [hξ, h]
    simp
  set AQ : Matrix ι ι ℚ := A.map (Int.castRingHom ℚ) with hAQ
  set M : Matrix ι ι ℝ := aeval (AQ.map (algebraMap ℚ ℝ)) qH with hM
  have hCH : aeval (act A) (A.charpoly.map (Int.castRingHom ℝ)) = 0 := by
    have h := LinearMap.aeval_self_charpoly (act A)
    rwa [charpoly_act] at h
  have hrange : ∀ v, ξ (M *ᵥ v) = 0 := by
    intro v
    apply hvan
    rw [LinearMap.mem_ker, hM, hAQ, ← aeval_act]
    have h1 : aeval (act A) qE (aeval (act A) qH v) = aeval (act A) (qE * qH) v := by
      rw [map_mul]; rfl
    rw [h1, ← hχ, hCH, LinearMap.zero_apply]
  have hT : aeval ((AQᵀ).map (algebraMap ℚ ℝ)) qH *ᵥ (algebraMap ℚ ℝ ∘ cQ) = 0 := by
    rw [Matrix.transpose_map, aeval_transpose_matrix, ← hM, Matrix.mulVec_transpose]
    funext j
    have := hrange (Pi.single j 1)
    rw [hξ, Matrix.dotProduct_mulVec, dotProduct_single_one] at this
    simpa using this
  obtain ⟨p, hp, hpχ, hpH⟩ := exists_irreducible_dvd_of_real_annihilator AQᵀ hcQ0 qH hT
  have hχQ : AQᵀ.charpoly = charpolyQ A := by
    rw [Matrix.charpoly_transpose, hAQ, Matrix.charpoly_map]; rfl
  rw [hχQ] at hpχ
  exact false_of_irreducible_dvd A hsf hχ hb hp hpχ hpH

end Lattice

end KernelSplit

section Exports

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open KernelSplit

/-- **Normal form** (statement (3)(a)). If `χ_A` is squarefree over `ℚ`, every `A`-invariant
splitting `ℝ^ι = E ⊕ H` satisfies `χ_A = q_E q_H` over `ℝ` and `E = ker q_E(A)`,
`H = ker q_H(A)`, where `q_E`, `q_H` are the characteristic polynomials of `A|_E`, `A|_H`. -/
theorem normal_form (A : Matrix ι ι ℤ) (hsf : Squarefree (charpolyQ A))
    {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H) (hE : ∀ v ∈ E, act A v ∈ E)
    (hH : ∀ v ∈ H, act A v ∈ H) :
    A.charpoly.map (Int.castRingHom ℝ) =
        ((act A).restrict hE).charpoly * ((act A).restrict hH).charpoly ∧
      E = LinearMap.ker (Polynomial.aeval (act A) ((act A).restrict hE).charpoly) ∧
      H = LinearMap.ker (Polynomial.aeval (act A) ((act A).restrict hH).charpoly) := by
  have hχ := charpoly_restrict_mul A hc hE hH
  refine ⟨hχ, ?_⟩
  set qE := ((act A).restrict hE).charpoly with hqE
  set qH := ((act A).restrict hH).charpoly with hqH
  have hcop : IsCoprime qE qH := by
    have hsep := separable_charpoly_real A hsf
    rw [hχ] at hsep
    exact hsep.isCoprime
  have hχ' : (act A).charpoly = qE * qH := by rw [charpoly_act]; exact hχ
  have hχ'' : (act A).charpoly = qH * qE := by rw [hχ', mul_comm]
  obtain ⟨-, hdimE⟩ := finrank_ker_aeval_of_coprime (act A) (LinearMap.charpoly_monic _)
    (LinearMap.charpoly_monic _) hχ' hcop
  obtain ⟨-, hdimH⟩ := finrank_ker_aeval_of_coprime (act A) (LinearMap.charpoly_monic _)
    (LinearMap.charpoly_monic _) hχ'' hcop.symm
  have hle : ∀ {U : Submodule ℝ (ι → ℝ)} (hU : ∀ v ∈ U, act A v ∈ U),
      U ≤ LinearMap.ker (aeval (act A) ((act A).restrict hU).charpoly) := by
    intro U hU v hv
    rw [LinearMap.mem_ker]
    have h0 : aeval ((act A).restrict hU) ((act A).restrict hU).charpoly = 0 :=
      LinearMap.aeval_self_charpoly _
    have := aeval_restrict_apply (act A) hU ((act A).restrict hU).charpoly ⟨v, hv⟩
    rw [h0] at this
    simpa using this.symm
  refine ⟨Submodule.eq_of_le_of_finrank_eq (hle hE) ?_,
    Submodule.eq_of_le_of_finrank_eq (hle hH) ?_⟩
  · rw [hdimE, LinearMap.charpoly_natDegree]
  · rw [hdimH, LinearMap.charpoly_natDegree]

/-- **The lattice meets `ker p(A)`.** For every irreducible factor `p` of `χ_A` over `ℚ`, some
nonzero vector of `ℤ^ι` is killed by `p(A)`. -/
theorem exists_int_mem_ker (A : Matrix ι ι ℤ) {p : ℚ[X]} (hp : Irreducible p)
    (hpχ : p ∣ charpolyQ A) :
    ∃ γ ∈ intLattice ι, γ ≠ 0 ∧ Polynomial.aeval (act A) (p.map (algebraMap ℚ ℝ)) γ = 0 := by
  classical
  set AQ : Matrix ι ι ℚ := A.map (Int.castRingHom ℚ) with hAQ
  have hχQ : AQ.charpoly = charpolyQ A := by
    rw [hAQ, Matrix.charpoly_map]; rfl
  -- a complex root `z` of `p` is an eigenvalue of `A`
  have hdeg : p.degree ≠ 0 := fun h =>
    hp.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p hdeg
  set AC : Matrix ι ι ℂ := AQ.map (algebraMap ℚ ℂ) with hAC
  have hroot : IsRoot AC.charpoly z := by
    rw [hAC, Matrix.charpoly_map, IsRoot, eval_map_algebraMap, hχQ]
    obtain ⟨g, hg⟩ := hpχ
    rw [hg, map_mul, hz, zero_mul]
  have hspec : z ∈ spectrum ℂ (Matrix.toLin' AC) := by
    rw [Matrix.spectrum_toLin']
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  obtain ⟨w, hw⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hspec).exists_hasEigenvector
  -- so `p(A)` is singular over `ℂ`, hence over `ℚ`
  have hpw : aeval (Matrix.toLin' AC) (p.map (algebraMap ℚ ℂ)) w = 0 := by
    rw [Module.End.aeval_apply_of_hasEigenvector hw, eval_map_algebraMap, hz, zero_smul]
  have hMw : aeval AC (p.map (algebraMap ℚ ℂ)) *ᵥ w = 0 := by
    have h := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)).toAlgHom AC
      (p.map (algebraMap ℚ ℂ))
    have h2 : (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)).toAlgHom
        (aeval AC (p.map (algebraMap ℚ ℂ))) w = 0 := by
      rw [← h]; exact hpw
    exact h2
  have hdetC : (aeval AC (p.map (algebraMap ℚ ℂ))).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw.2, hMw⟩
  have hdetQ : (aeval AQ p).det = 0 := by
    rw [hAC, aeval_map_matrix, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdetC
    exact (FaithfulSMul.algebraMap_injective ℚ ℂ) (by rw [hdetC, map_zero])
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetQ
  -- clear denominators
  set N : ℕ := ∏ i, (v i).den with hN
  have hN0 : (N : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero, hN, Finset.prod_ne_zero_iff]
    exact fun i _ => (v i).den_nz
  set n : ι → ℤ := fun i => (v i).num * ((∏ j ∈ Finset.univ.erase i, (v j).den : ℕ) : ℤ) with hn
  have hnv : ∀ i, (n i : ℚ) = (N : ℚ) * v i := by
    intro i
    have hprod : (v i).den * ∏ j ∈ Finset.univ.erase i, (v j).den = N :=
      Finset.mul_prod_erase Finset.univ (fun j => (v j).den) (Finset.mem_univ i)
    rw [← hprod, Nat.cast_mul, mul_comm ((v i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
    simp only [hn]
    push_cast
    ring
  refine ⟨fun i => (n i : ℝ), mem_intLattice_iff.mpr ⟨n, rfl⟩, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    intro h0
    have h1 : (n i : ℝ) = 0 := congrFun h0 i
    have h2 : (n i : ℚ) = 0 := by exact_mod_cast h1
    rw [hnv] at h2
    exact hi (by simpa [hN0] using h2)
  · have hγ : (fun i => (n i : ℝ)) = algebraMap ℚ ℝ ∘ ((N : ℚ) • v) := by
      funext i
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hnv i]
      simp
    rw [aeval_act, ← hAQ, aeval_map_matrix, hγ, ← cast_mulVec, Matrix.mulVec_smul, hv,
      smul_zero]
    funext i
    simp


/-- Necessity of the disk condition in (3)(b), from the disk condition for admissible
schemes. -/
theorem KernelSplit.disk_of_exists (A : Matrix ι ι ℤ) {E H : Submodule ℝ (ι → ℝ)}
    (hH : ∀ v ∈ H, act A v ∈ H)
    (hroots : ∀ S : InvariantCPS A, S.Admissible →
      ∀ z ∈ (((act A).restrict S.mapsTo_H).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1)
    (h : ∃ S : InvariantCPS A, S.E = E ∧ S.H = H ∧ S.Admissible) :
    ∀ z ∈ (((act A).restrict hH).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1 := by
  obtain ⟨S, -, hSH, hS⟩ := h
  subst hSH
  exact hroots S hS

/-- Necessity of the shared-root condition in (3)(b): if an irreducible factor `p` of `χ_A`
over `ℚ` shared no root with `q_E`, then `p ∣ q_H` over `ℝ`, and the nonzero lattice vector of
`ker p(A) ⊆ ker q_H(A) = H` would contradict `ℤ^ι ∩ H = 0`. -/
theorem KernelSplit.shared_root_of_exists (A : Matrix ι ι ℤ) (hsf : Squarefree (charpolyQ A))
    {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H) (hE : ∀ v ∈ E, act A v ∈ E)
    (hH : ∀ v ∈ H, act A v ∈ H) (h : ∃ S : InvariantCPS A, S.E = E ∧ S.H = H) :
    ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots,
        Polynomial.aeval z ((act A).restrict hE).charpoly = 0 := by
  classical
  obtain ⟨S, -, hSH⟩ := h
  obtain ⟨hχ, -, hHker⟩ := normal_form A hsf hc hE hH
  intro p hp
  have hirr : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hpdvd : p ∣ charpolyQ A := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp
  by_contra hno
  push Not at hno
  have hcop : IsCoprime (p.map (algebraMap ℚ ℝ)) ((act A).restrict hE).charpoly := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ]
    intro a
    by_cases ha : aeval a (p.map (algebraMap ℚ ℝ)) = 0
    · right
      apply hno a
      rw [aeval_map_algebraMap] at ha
      rw [mem_roots', IsRoot, eval_map_algebraMap]
      exact ⟨Polynomial.map_ne_zero hirr.ne_zero, ha⟩
    · left; exact ha
  have hdvdχ : p.map (algebraMap ℚ ℝ) ∣
      ((act A).restrict hE).charpoly * ((act A).restrict hH).charpoly := by
    rw [← hχ, ← charpolyQ_map_real]
    exact Polynomial.map_dvd _ hpdvd
  have hdvdH := hcop.dvd_of_dvd_mul_left hdvdχ
  obtain ⟨γ, hγ, hγ0, hpγ⟩ := exists_int_mem_ker A hirr hpdvd
  apply hγ0
  apply S.inj γ hγ
  rw [hSH, hHker, LinearMap.mem_ker]
  obtain ⟨g, hg⟩ := hdvdH
  rw [hg, mul_comm, map_mul, Module.End.mul_apply, hpγ, map_zero]

/-- Sufficiency in (3)(b), given Kronecker's criterion (no integral functional vanishing on `E`
implies density) and the admissibility of power-bounded schemes. -/
theorem KernelSplit.exists_of_conditions (A : Matrix ι ι ℤ) (hsf : Squarefree (charpolyQ A))
    {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H) (hE : ∀ v ∈ E, act A v ∈ E)
    (hH : ∀ v ∈ H, act A v ∈ H)
    (hdense : (∀ f : (ι → ℝ) →ₗ[ℝ] ℝ, (∀ γ ∈ intLattice ι, ∃ n : ℤ, f γ = n) →
        (∀ v ∈ E, f v = 0) → f = 0) →
      (H : Set (ι → ℝ)) ⊆ closure (H.projection E hc.symm '' (intLattice ι : Set (ι → ℝ))))
    (hadm : ∀ S : InvariantCPS A,
      (∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ S.H, ‖(act A ^ n) v‖ ≤ C * ‖v‖) → S.Admissible)
    (hdisk : ∀ z ∈ (((act A).restrict hH).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1)
    (hshare : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots,
        Polynomial.aeval z ((act A).restrict hE).charpoly = 0) :
    ∃ S : InvariantCPS A, S.E = E ∧ S.H = H ∧ S.Admissible := by
  classical
  obtain ⟨hχ, hEker, hHker⟩ := normal_form A hsf hc hE hH
  have hb : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ∃ z : ℂ, aeval z p = 0 ∧ aeval z ((act A).restrict hE).charpoly = 0 := by
    intro p hp
    obtain ⟨z, hz, hzE⟩ := hshare p hp
    refine ⟨z, ?_, hzE⟩
    have := (mem_roots'.mp hz).2
    rwa [IsRoot, eval_map_algebraMap] at this
  have hinj : ∀ γ ∈ intLattice ι, γ ∈ H → γ = 0 := by
    intro γ hγ hγH
    rw [hHker, LinearMap.mem_ker] at hγH
    exact inj_of_shared_roots A hsf hχ hb γ hγ hγH
  have hden := hdense (by
    intro f hf hfE
    refine noIntegralFunctional_of_shared_roots A hsf hχ hb f hf ?_
    intro e he
    rw [← hEker] at he
    exact hfE e he)
  refine ⟨⟨E, H, hc, hE, hH, hinj, hden⟩, rfl, rfl, hadm _ ?_⟩
  show ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ H, ‖(act A ^ n) v‖ ≤ C * ‖v‖
  set qH := ((act A).restrict hH).charpoly with hqH
  have hsepH : qH.Separable := by
    have hsep := separable_charpoly_real A hsf
    rw [hχ] at hsep
    exact hsep.of_mul_right
  have hnd : (qH.map (algebraMap ℝ ℂ)).roots.Nodup := Polynomial.nodup_roots hsepH.map
  set s := (qH.map (algebraMap ℝ ℂ)).roots.toFinset with hs
  have hs1 : ∀ z ∈ s, ‖z‖ ≤ 1 := fun z hz => hdisk z (Multiset.mem_toFinset.mp hz)
  have hqs : qH.map (algebraMap ℝ ℂ) = Lagrange.nodal s id := by
    rw [Lagrange.nodal_eq, Finset.prod_eq_multiset_prod, hs, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnd]
    exact (IsAlgClosed.splits _).eq_prod_roots_of_monic ((LinearMap.charpoly_monic _).map _)
  obtain ⟨C, hC⟩ := powerBounded_of_nodal (act A) (LinearMap.charpoly_monic _) s hs1 hqs
  refine ⟨C, fun n v hv => hC n v ?_⟩
  rw [hHker] at hv
  exact hv


/-- **Characterization** (statement (3)(b)). If `χ_A` is squarefree over `ℚ`, an `A`-invariant
splitting `ℝ^ι = E ⊕ H` carries an admissible scheme if and only if every root of `q_H` lies in
the closed unit disk and every irreducible factor of `χ_A` over `ℚ` shares a complex root with
`q_E`. (`det A ≠ 0` is not used.) -/
theorem exists_admissible_iff (A : Matrix ι ι ℤ) (_hdet : A.det ≠ 0)
    (hsf : Squarefree (charpolyQ A)) {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H)
    (hE : ∀ v ∈ E, act A v ∈ E) (hH : ∀ v ∈ H, act A v ∈ H) :
    (∃ S : InvariantCPS A, S.E = E ∧ S.H = H ∧ S.Admissible) ↔
      (∀ z ∈ (((act A).restrict hH).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1) ∧
        ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
          ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots,
            Polynomial.aeval z ((act A).restrict hE).charpoly = 0 := by
  constructor
  · intro h
    refine ⟨KernelSplit.disk_of_exists A hH (fun S hS => roots_restrict_H_le_one S hS) h, ?_⟩
    obtain ⟨S, hSE, hSH, -⟩ := h
    exact KernelSplit.shared_root_of_exists A hsf hc hE hH ⟨S, hSE, hSH⟩
  · rintro ⟨hdisk, hshare⟩
    exact KernelSplit.exists_of_conditions A hsf hc hE hH (dense_of_no_integral_functional hc)
      (fun S h => (admissible_iff_powerBounded S).mpr h) hdisk hshare

end Exports

end

end InflationDimension
