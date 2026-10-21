module
public import Mathlib
public import InflationDimension.Normal

@[expose] public section
/-!
# The count for a squarefree characteristic polynomial

Let `A` be an integer matrix with `det A ≠ 0` whose characteristic polynomial `χ_A` is
squarefree over `ℚ`. The least physical dimension of an admissible `A`-invariant
cut-and-project scheme on `ℤ^ι` is

  `U(A) + Σ_{p circle factor} min(deg p, 2)`,

where `U(A)` is the number of eigenvalues of modulus `> 1` and the circle factors are the
irreducible rational factors of `χ_A` with all roots on the unit circle. By Kronecker's theorem
the circle factors are exactly the cyclotomic factors.

The lower bound is a count of roots: an admissible scheme puts every expanding root into
`χ_{A|E}`, and meets every rational factor of `χ_A`; a circle factor of degree `≥ 2` has no real
root, so it contributes a pair of conjugate roots. The bound is attained by the real factor
`q_E = (the part of χ_A with roots outside the closed disk) · Π_{circle p} minpoly_ℝ(z_p)`, one
root `z_p` of each circle factor `p`.
-/

namespace InflationDimension

open Polynomial Module ComplexConjugate UniqueFactorizationMonoid

noncomputable section

namespace Count

/-! ### Polynomial facts -/

/-- Kronecker's theorem, polynomial form: a monic `ℚ`-irreducible factor of a monic integer
polynomial whose complex roots all have modulus `1` is a cyclotomic polynomial. -/
theorem eq_cyclotomic_of_circle {p : ℚ[X]} (hp : Irreducible p) (hmon : p.Monic)
    {f : ℤ[X]} (hf : f.Monic) (hpf : p ∣ f.map (Int.castRingHom ℚ))
    (hcirc : ∀ z ∈ (p.map (algebraMap ℚ ℂ)).roots, ‖z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ := by
  have : Fact (Irreducible p) := ⟨hp⟩
  set x : AdjoinRoot p := AdjoinRoot.root p with hx
  have hpx : aeval x p = 0 := by
    rw [aeval_def]
    have hring : algebraMap ℚ (AdjoinRoot p) = AdjoinRoot.of p := RingHom.ext_rat _ _
    rw [hring, hx]
    exact AdjoinRoot.eval₂_root p
  have hxi : IsIntegral ℤ x := by
    obtain ⟨g, hg⟩ := hpf
    have h0 : aeval x (f.map (Int.castRingHom ℚ)) = 0 := by rw [hg, map_mul, hpx, zero_mul]
    rw [← algebraMap_int_eq, aeval_map_algebraMap] at h0
    exact ⟨f, hf, by rwa [aeval_def] at h0⟩
  have hnorm : ∀ φ : AdjoinRoot p →+* ℂ, ‖φ x‖ = 1 := by
    intro φ
    apply hcirc
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hmon.ne_zero), IsRoot, eval_map_algebraMap]
    have := aeval_algHom_apply φ.toRatAlgHom x p
    rw [hpx, map_zero] at this
    simpa using this
  obtain ⟨n, hn, hxn⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_eq_one (AdjoinRoot p) ℂ hxi hnorm
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hxn⟩
  have hprim : IsPrimitiveRoot x (orderOf x) := IsPrimitiveRoot.orderOf x
  have hpos : 0 < orderOf x := orderOf_pos_iff.mpr hfin
  refine ⟨orderOf x, hpos, ?_⟩
  rw [cyclotomic_eq_minpoly_rat hprim hpos]
  exact minpoly.eq_of_irreducible_of_monic hp hpx hmon

theorem norm_prod_le_one (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ ≤ 1) : ‖s.prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have ha := hs a (Multiset.mem_cons_self a s)
    have hs' := ih (fun z hz => hs z (Multiset.mem_cons_of_mem hz))
    calc ‖a‖ * ‖s.prod‖ ≤ 1 * 1 :=
          mul_le_mul ha hs' (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem norm_prod_lt_one (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ ≤ 1) {w : ℂ} (hw : w ∈ s)
    (hw1 : ‖w‖ < 1) : ‖s.prod‖ < 1 := by
  induction s using Multiset.induction_on with
  | empty => simp at hw
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have ha := hs a (Multiset.mem_cons_self a s)
    have hall : ∀ z ∈ s, ‖z‖ ≤ 1 := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rcases Multiset.mem_cons.mp hw with rfl | hws
    · calc ‖w‖ * ‖s.prod‖ ≤ ‖w‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_prod_le_one s hall) (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hw1
    · have := ih hall hws
      calc ‖a‖ * ‖s.prod‖ ≤ 1 * ‖s.prod‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact this

/-- A `ℚ`-irreducible factor of a monic integer polynomial `f` with `f(0) ≠ 0` whose complex
roots all lie in the closed unit disk has all its roots on the unit circle. -/
theorem norm_eq_one_of_forall_le_one {p : ℚ[X]} (hp : Irreducible p) (hmon : p.Monic)
    {f : ℤ[X]} (hf : f.Monic) (hf0 : f.coeff 0 ≠ 0) (hpf : p ∣ f.map (Int.castRingHom ℚ))
    (hdisk : ∀ z ∈ (p.map (algebraMap ℚ ℂ)).roots, ‖z‖ ≤ 1) :
    ∀ z ∈ (p.map (algebraMap ℚ ℂ)).roots, ‖z‖ = 1 := by
  have : Fact (Irreducible p) := ⟨hp⟩
  set x : AdjoinRoot p := AdjoinRoot.root p with hx
  have hpx : aeval x p = 0 := by
    rw [aeval_def]
    have hring : algebraMap ℚ (AdjoinRoot p) = AdjoinRoot.of p := RingHom.ext_rat _ _
    rw [hring, hx]
    exact AdjoinRoot.eval₂_root p
  have hxi : IsIntegral ℤ x := by
    obtain ⟨g, hg⟩ := hpf
    have h0 : aeval x (f.map (Int.castRingHom ℚ)) = 0 := by rw [hg, map_mul, hpx, zero_mul]
    rw [← algebraMap_int_eq, aeval_map_algebraMap] at h0
    exact ⟨f, hf, by rwa [aeval_def] at h0⟩
  have hmin : p = minpoly ℚ x := minpoly.eq_of_irreducible_of_monic hp hpx hmon
  have hZ : minpoly ℚ x = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hxi
  set c : ℤ := (minpoly ℤ x).coeff 0 with hc
  have hp0 : p.coeff 0 = (c : ℚ) := by
    rw [hmin, hZ, coeff_map]; rfl
  have hc0 : c ≠ 0 := by
    intro h0
    have hX : X ∣ p := by rw [X_dvd_iff, hp0, h0, Int.cast_zero]
    have hXf : X ∣ f.map (Int.castRingHom ℚ) := hX.trans hpf
    rw [X_dvd_iff, coeff_map] at hXf
    exact hf0 (by simpa using hXf)
  have hc1 : (1 : ℝ) ≤ |(c : ℝ)| := by
    have : (1 : ℤ) ≤ |c| := Int.one_le_abs hc0
    exact_mod_cast this
  set P := p.map (algebraMap ℚ ℂ) with hP
  have hPmon : P.Monic := hmon.map _
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hvieta := hsplit.coeff_zero_eq_prod_roots_of_monic hPmon
  have hnormc : ‖P.coeff 0‖ = |(c : ℝ)| := by
    rw [hP, coeff_map, hp0]
    simp
  have hprod : 1 ≤ ‖P.roots.prod‖ := by
    rw [hvieta, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hnormc
    rw [hnormc]; exact hc1
  intro z hz
  by_contra hne
  have hlt : ‖z‖ < 1 := lt_of_le_of_ne (hdisk z hz) hne
  have := norm_prod_lt_one P.roots hdisk hz hlt
  linarith

theorem mem_roots_map_iff {K L : Type*} [Field K] [Field L] [Algebra K L] {p : K[X]} (hp : p ≠ 0)
    {z : L} : z ∈ (p.map (algebraMap K L)).roots ↔ aeval z p = 0 := by
  rw [mem_roots_map hp, aeval_def]

/-- Two monic irreducible rational polynomials with a common complex root are equal. -/
theorem eq_of_common_root {p p' : ℚ[X]} (hp : Irreducible p) (hpm : p.Monic)
    (hp' : Irreducible p') (hpm' : p'.Monic) {z : ℂ} (hz : aeval z p = 0)
    (hz' : aeval z p' = 0) : p = p' :=
  (minpoly.eq_of_irreducible_of_monic hp hz hpm).trans
    (minpoly.eq_of_irreducible_of_monic hp' hz' hpm').symm

/-- An irreducible real polynomial has all its complex roots on one circle. -/
theorem norm_eq_of_irreducible {g : ℝ[X]} (hg : Irreducible g) {z w : ℂ}
    (hz : z ∈ (g.map (algebraMap ℝ ℂ)).roots) (hw : w ∈ (g.map (algebraMap ℝ ℂ)).roots) :
    ‖z‖ = ‖w‖ := by
  classical
  have hg0 : g ≠ 0 := hg.ne_zero
  have hcard : Multiset.card (g.map (algebraMap ℝ ℂ)).roots ≤ g.natDegree := by
    simpa [natDegree_map] using card_roots' (g.map (algebraMap ℝ ℂ))
  have hdeg := hg.natDegree_le_two
  have hzroot : aeval z g = 0 := (mem_roots_map_iff hg0).mp hz
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
    have hc : conj z ∈ (g.map (algebraMap ℝ ℂ)).roots :=
      (mem_roots_map_iff hg0).mpr (by rw [aeval_conj, hzroot, map_zero])
    have hne : z ≠ conj z := fun h => him (Complex.conj_eq_iff_im.mp h.symm)
    by_contra hzw
    have hw1 : w ≠ z := fun h => hzw (by rw [h])
    have hw2 : w ≠ conj z := fun h => hzw (by rw [h, Complex.norm_conj])
    have hsub : ({z, conj z, w} : Finset ℂ) ⊆ (g.map (algebraMap ℝ ℂ)).roots.toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Multiset.mem_toFinset]
      rcases hx with rfl | rfl | rfl
      exacts [hz, hc, hw]
    have h3 : ({z, conj z, w} : Finset ℂ).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hw2.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne, hw1.symm⟩
    have := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
    omega

/-- A monic real polynomial is the product of a monic factor with all complex roots in the
closed unit disk and a monic factor with all complex roots outside it. -/
theorem exists_split_disk (f : ℝ[X]) (hf : f.Monic) :
    ∃ p q : ℝ[X], p.Monic ∧ q.Monic ∧ f = p * q ∧
      (∀ z ∈ (p.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1) ∧
      (∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, 1 < ‖z‖) := by
  classical
  set F := normalizedFactors f
  let inside : ℝ[X] → Prop := fun g => ∀ z ∈ (g.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1
  have hirr : ∀ g ∈ F, Irreducible g := fun g hg => irreducible_of_normalized_factor g hg
  have hmon : ∀ g ∈ F, g.Monic := fun g hg => by
    rw [← normalize_normalized_factor g hg]
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
      (prod_normalizedFactors hf.ne_zero)).symm
  have hfactor : ∀ s ≤ F, ∀ z ∈ (s.prod.map (algebraMap ℝ ℂ)).roots,
      ∃ g ∈ s, z ∈ (g.map (algebraMap ℝ ℂ)).roots := by
    intro s hs z hz
    have h0 : aeval z s.prod = 0 := (mem_roots_map_iff (hFmon s hs).ne_zero).mp hz
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at h0
    obtain ⟨g, hg, hgz⟩ := h0
    exact ⟨g, hg, (mem_roots_map_iff (hirr g (Multiset.mem_of_le hs hg)).ne_zero).mpr hgz⟩
  refine ⟨p, q, hp, hq, hfpq, ?_, ?_⟩
  · intro z hz
    obtain ⟨g, hg, hzg⟩ := hfactor _ (Multiset.filter_le _ _) z hz
    exact (Multiset.mem_filter.mp hg).2 z hzg
  · intro z hz
    obtain ⟨g, hg, hzg⟩ := hfactor _ (Multiset.filter_le _ _) z hz
    have hgF := Multiset.mem_filter.mp hg
    have hnot : ¬ inside g := hgF.2
    simp only [inside, not_forall, not_le] at hnot
    obtain ⟨w, hw, hw1⟩ := hnot
    rw [norm_eq_of_irreducible (hirr g hgF.1) hzg hw]
    exact hw1

/-! ### Linear algebra: kernels of complementary factors -/

section Kernels

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- If `χ_f = q · r` with `q, r` monic and coprime, then `ker q(f) ⊕ ker r(f)` is an
`f`-invariant splitting and the characteristic polynomials of `f` on the two kernels are `q` and
`r`. -/
theorem charpoly_restrict_ker [FiniteDimensional ℝ V] (f : Module.End ℝ V) {q r : ℝ[X]}
    (hq : q.Monic) (hr : r.Monic) (hχ : f.charpoly = q * r) (hcop : IsCoprime q r) :
    IsCompl (LinearMap.ker (aeval f q)) (LinearMap.ker (aeval f r)) ∧
      (f.restrict (KernelSplit.mapsTo_ker_aeval f q)).charpoly = q ∧
      (f.restrict (KernelSplit.mapsTo_ker_aeval f r)).charpoly = r := by
  set U := LinearMap.ker (aeval f q) with hUdef
  set W := LinearMap.ker (aeval f r) with hWdef
  have hU := KernelSplit.mapsTo_ker_aeval f q
  have hW := KernelSplit.mapsTo_ker_aeval f r
  have hcompl : IsCompl U W := by
    refine ⟨Polynomial.disjoint_ker_aeval_of_isCoprime f hcop, ?_⟩
    rw [codisjoint_iff, hUdef, hWdef, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop,
      ← hχ, LinearMap.aeval_self_charpoly, LinearMap.ker_zero]
  refine ⟨hcompl, ?_⟩
  set g₁ := (f.restrict hU).charpoly with hg₁
  set g₂ := (f.restrict hW).charpoly with hg₂
  have hsplit : f.charpoly = g₁ * g₂ :=
    PowerBounded.charpoly_eq_mul_of_isCompl f U W hcompl hU hW
  have hq0 : aeval (f.restrict hU) q = 0 := by
    ext v
    simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [KernelSplit.aeval_restrict_apply]
    exact v.2
  have hr0 : aeval (f.restrict hW) r = 0 := by
    ext v
    simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero]
    rw [KernelSplit.aeval_restrict_apply]
    exact v.2
  have hcopC := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ q r).mp hcop
  have hc₁ : IsCoprime g₁ r := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ]
    intro a
    by_cases ha : aeval a g₁ = 0
    · right
      have := KernelSplit.aeval_eq_zero_of_charpoly_root _ hq0 a ha
      exact (hcopC a).resolve_left (not_not.mpr this)
    · left; exact ha
  have hc₂ : IsCoprime g₂ q := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ]
    intro a
    by_cases ha : aeval a g₂ = 0
    · right
      have := KernelSplit.aeval_eq_zero_of_charpoly_root _ hr0 a ha
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
  have hm₁ : g₁.Monic := LinearMap.charpoly_monic _
  have hm₂ : g₂.Monic := LinearMap.charpoly_monic _
  have e₁ : q = g₁ := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm₁ hq hd₁ (by omega)
  have e₂ : r = g₂ := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm₂ hr hd₂ (by omega)
  exact ⟨e₁.symm, e₂.symm⟩

end Kernels

/-! ### The rational factors of `χ_A` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_map_filter_eq {α : Type*} (s : Multiset α) (P : α → Prop) [DecidablePred P]
    (g : α → ℕ) :
    ((s.filter P).map g).sum = (s.map (fun a => if P a then g a else 0)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.filter_cons, Multiset.map_add, Multiset.sum_add, ih, Multiset.map_cons,
      Multiset.sum_cons]
    split_ifs <;> simp

variable (A : Matrix ι ι ℤ)

theorem charpolyQ_monic : (charpolyQ A).Monic := (Matrix.charpoly_monic A).map _

theorem charpolyQ_ne_zero : charpolyQ A ≠ 0 := (charpolyQ_monic A).ne_zero

theorem monic_of_mem {p : ℚ[X]} (hp : p ∈ normalizedFactors (charpolyQ A)) : p.Monic := by
  rw [← normalize_normalized_factor p hp]
  exact Polynomial.monic_normalize (irreducible_of_normalized_factor p hp).ne_zero

theorem prod_normalizedFactors_eq : (normalizedFactors (charpolyQ A)).prod = charpolyQ A :=
  Polynomial.eq_of_monic_of_associated
    (by simpa using Polynomial.monic_multiset_prod_of_monic _ id (fun p hp => monic_of_mem A hp))
    (charpolyQ_monic A) (prod_normalizedFactors (charpolyQ_ne_zero A))

theorem map_charpoly_eq (K : Type*) [Field K] [CharZero K] :
    A.charpoly.map (Int.castRingHom K) = (charpolyQ A).map (algebraMap ℚ K) := by
  rw [charpolyQ, Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

theorem eigenvalues_eq_bind : eigenvalues A =
    (normalizedFactors (charpolyQ A)).bind (fun p => (p.map (algebraMap ℚ ℂ)).roots) := by
  have h : (charpolyQ A).map (algebraMap ℚ ℂ) =
      ((normalizedFactors (charpolyQ A)).map (Polynomial.map (algebraMap ℚ ℂ))).prod := by
    rw [← Polynomial.map_multiset_prod, prod_normalizedFactors_eq]
  rw [eigenvalues, map_charpoly_eq, h, roots_multiset_prod, Multiset.bind_map]
  intro h0
  obtain ⟨p, hp, hp0⟩ := Multiset.mem_map.mp h0
  exact (Polynomial.map_ne_zero (monic_of_mem A hp).ne_zero) hp0

variable {A}

theorem separable_charpolyQ (hsf : Squarefree (charpolyQ A)) : (charpolyQ A).Separable :=
  PerfectField.separable_iff_squarefree.mpr hsf

theorem nodup_eigenvalues (hsf : Squarefree (charpolyQ A)) : (eigenvalues A).Nodup := by
  rw [eigenvalues, map_charpoly_eq]
  exact nodup_roots (separable_charpolyQ hsf).map

theorem nodup_normalizedFactors (hsf : Squarefree (charpolyQ A)) :
    (normalizedFactors (charpolyQ A)).Nodup :=
  (squarefree_iff_nodup_normalizedFactors (charpolyQ_ne_zero A)).mp hsf

/-! ### The lower bound -/

/-- **The root count.** If `χ_A = q_E q_H` over `ℝ`, every complex root of `q_H` lies in the
closed unit disk and every irreducible rational factor of `χ_A` shares a root with `q_E`, then
`deg q_E ≥ U(A) + circleCount A`. -/
theorem count_le_natDegree (hsf : Squarefree (charpolyQ A)) {qE qH : ℝ[X]}
    (hχ : A.charpoly.map (Int.castRingHom ℝ) = qE * qH)
    (ha : ∀ z ∈ (qH.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1)
    (hb : ∀ p ∈ normalizedFactors (charpolyQ A),
      ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots, aeval z qE = 0) :
    unstableCount A + circleCount A ≤ qE.natDegree := by
  classical
  set F := normalizedFactors (charpolyQ A)
  set RE := (qE.map (algebraMap ℝ ℂ)).roots
  set RH := (qH.map (algebraMap ℝ ℂ)).roots
  have hχC : A.charpoly.map (Int.castRingHom ℂ) =
      qE.map (algebraMap ℝ ℂ) * qH.map (algebraMap ℝ ℂ) := by
    rw [← Polynomial.map_mul, ← hχ, Polynomial.map_map]
    congr 1
  have hne : qE.map (algebraMap ℝ ℂ) * qH.map (algebraMap ℝ ℂ) ≠ 0 := by
    rw [← hχC]; exact ((Matrix.charpoly_monic A).map _).ne_zero
  have hqE0 : qE ≠ 0 := by
    intro h; apply hne; rw [h, Polynomial.map_zero, zero_mul]
  have hroots : eigenvalues A = RE + RH := by
    rw [eigenvalues, hχC, roots_mul hne]
  have hnd := nodup_eigenvalues hsf
  have hREnd : RE.Nodup := Multiset.nodup_of_le (Multiset.le_add_right RE RH) (hroots ▸ hnd)
  set T : ℚ[X] → Multiset ℂ := fun p => RE.filter (fun z => aeval z p = 0)
  have hTbind : (F.bind T).Nodup := by
    rw [Multiset.nodup_bind]
    refine ⟨fun p _ => hREnd.filter _, ?_⟩
    refine Multiset.Nodup.pairwise ?_ (nodup_normalizedFactors hsf)
    intro p hp p' hp' hpp'
    rw [Function.onFun, Multiset.disjoint_left]
    intro z hz hz'
    exact hpp' (eq_of_common_root (irreducible_of_normalized_factor p hp) (monic_of_mem A hp)
      (irreducible_of_normalized_factor p' hp') (monic_of_mem A hp')
      (Multiset.mem_filter.mp hz).2 (Multiset.mem_filter.mp hz').2)
  have hTle : F.bind T ≤ RE := by
    rw [Multiset.le_iff_subset hTbind]
    intro z hz
    obtain ⟨p, _, hzp⟩ := Multiset.mem_bind.mp hz
    exact (Multiset.mem_filter.mp hzp).1
  have hcardT : (F.map (fun p => Multiset.card (T p))).sum ≤ Multiset.card RE := by
    have h1 := Multiset.card_le_card hTle
    rw [Multiset.card_bind] at h1
    exact h1
  have hper : ∀ p ∈ F,
      Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖)) +
        (if IsCircleFactor p then min p.natDegree 2 else 0) ≤ Multiset.card (T p) := by
    intro p hp
    have hirr := irreducible_of_normalized_factor p hp
    have hp0 : p ≠ 0 := (monic_of_mem A hp).ne_zero
    have hle : (p.map (algebraMap ℚ ℂ)).roots ≤ eigenvalues A := by
      rw [eigenvalues_eq_bind]
      exact Multiset.le_bind (normalizedFactors (charpolyQ A))
        (f := fun p => (p.map (algebraMap ℚ ℂ)).roots) hp
    by_cases hc : IsCircleFactor p
    · simp only [hc, ↓reduceIte]
      have h0 : (p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖) = 0 :=
        Multiset.filter_eq_nil.mpr (fun z hz => by rw [hc z hz]; exact lt_irrefl 1)
      rw [h0, Multiset.card_zero, zero_add]
      obtain ⟨z, hz, hzE⟩ := hb p hp
      have hzp : aeval z p = 0 := (mem_roots_map_iff hp0).mp hz
      have hzT : z ∈ T p := Multiset.mem_filter.mpr ⟨(mem_roots_map_iff hqE0).mpr hzE, hzp⟩
      by_cases hdeg : p.natDegree ≤ 1
      · have : 0 < Multiset.card (T p) := Multiset.card_pos_iff_exists_mem.mpr ⟨z, hzT⟩
        omega
      · have hz1 : ‖z‖ = 1 := hc z hz
        have him : z.im ≠ 0 := by
          intro him
          have hre : |z.re| = 1 := (Complex.abs_re_eq_norm.mpr him).trans hz1
          have hrat : ∃ r : ℚ, z = algebraMap ℚ ℂ r := by
            rcases (abs_eq zero_le_one).mp hre with h | h
            · exact ⟨1, Complex.ext (by simp [h]) (by simp [him])⟩
            · exact ⟨-1, Complex.ext (by simp [h]) (by simp [him])⟩
          obtain ⟨r, rfl⟩ := hrat
          rw [aeval_algebraMap_apply, coe_aeval_eq_eval,
            map_eq_zero_iff _ (algebraMap ℚ ℂ).injective] at hzp
          have h1 : p.natDegree = 1 :=
            natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hirr hzp)
          omega
        have hconj : ∀ q : ℝ[X], aeval z q = 0 → aeval (conj z) q = 0 := by
          intro q hq; rw [aeval_conj, hq, map_zero]
        have hpR : aeval z (p.map (algebraMap ℚ ℝ)) = 0 := by
          rw [aeval_map_algebraMap]; exact hzp
        have hczp : aeval (conj z) p = 0 := by
          have := hconj _ hpR
          rwa [aeval_map_algebraMap] at this
        have hczT : conj z ∈ T p :=
          Multiset.mem_filter.mpr ⟨(mem_roots_map_iff hqE0).mpr (hconj _ hzE), hczp⟩
        have hne : z ≠ conj z := fun h => him (Complex.conj_eq_iff_im.mp h.symm)
        have hpairnd : (z ::ₘ {conj z} : Multiset ℂ).Nodup :=
          Multiset.nodup_cons.mpr ⟨by simpa using hne, Multiset.nodup_singleton _⟩
        have hpair : (z ::ₘ {conj z} : Multiset ℂ) ≤ T p := by
          rw [Multiset.le_iff_subset hpairnd]
          intro w hw
          rcases Multiset.mem_cons.mp hw with rfl | hw
          · exact hzT
          · rw [Multiset.mem_singleton.mp hw]; exact hczT
        have := Multiset.card_le_card hpair
        rw [Multiset.card_cons, Multiset.card_singleton] at this
        omega
    · simp only [hc, ↓reduceIte, add_zero]
      have hnd' : ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖)).Nodup :=
        (Multiset.nodup_of_le hle hnd).filter _
      apply Multiset.card_le_card
      rw [Multiset.le_iff_subset hnd']
      intro z hz
      obtain ⟨hzr, hz1⟩ := Multiset.mem_filter.mp hz
      refine Multiset.mem_filter.mpr ⟨?_, (mem_roots_map_iff hp0).mp hzr⟩
      have hzE : z ∈ eigenvalues A := Multiset.mem_of_le hle hzr
      rw [hroots, Multiset.mem_add] at hzE
      rcases hzE with h | h
      · exact h
      · exact absurd (ha z h) (not_le.mpr hz1)
  have hU : unstableCount A = (F.map (fun p =>
      Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖)))).sum := by
    rw [unstableCount, eigenvalues_eq_bind, Multiset.filter_bind, Multiset.card_bind]
    rfl
  have hcc : circleCount A =
      (F.map (fun p => if IsCircleFactor p then min p.natDegree 2 else 0)).sum := by
    rw [circleCount]
    exact sum_map_filter_eq _ _ _
  calc unstableCount A + circleCount A
      = (F.map (fun p =>
          Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖)) +
            (if IsCircleFactor p then min p.natDegree 2 else 0))).sum := by
        rw [hU, hcc, Multiset.sum_map_add]
    _ ≤ (F.map (fun p => Multiset.card (T p))).sum := Multiset.sum_map_le_sum_map _ _ hper
    _ ≤ Multiset.card RE := hcardT
    _ ≤ (qE.map (algebraMap ℝ ℂ)).natDegree := card_roots' _
    _ = qE.natDegree := natDegree_map _

end Count

/-! ### Kronecker's theorem and expanding roots -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Kronecker's theorem for the factors of `χ_A`.** An irreducible rational factor of the
characteristic polynomial of an integer matrix has all its complex roots on the unit circle if and
only if it is a cyclotomic polynomial. -/
theorem isCircleFactor_iff_cyclotomic (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) :
    IsCircleFactor p ↔ ∃ n : ℕ, 0 < n ∧ p = Polynomial.cyclotomic n ℚ := by
  constructor
  · intro hc
    exact Count.eq_cyclotomic_of_circle (irreducible_of_normalized_factor p hp)
      (Count.monic_of_mem A hp) (Matrix.charpoly_monic A) (dvd_of_mem_normalizedFactors hp) hc
  · rintro ⟨n, hn, rfl⟩ z hz
    rw [map_cyclotomic] at hz
    have : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
    exact (isRoot_cyclotomic_iff.mp (mem_roots'.mp hz).2).norm'_eq_one hn.ne'

/-- Every irreducible rational factor of `χ_A` that is not a circle factor has a root of modulus
`> 1` (`det A ≠ 0`). -/
theorem exists_expanding_root (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A))
    (hc : ¬ IsCircleFactor p) :
    ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots, 1 < ‖z‖ := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  apply hc
  have h0 : A.charpoly.coeff 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  exact Count.norm_eq_one_of_forall_le_one (irreducible_of_normalized_factor p hp)
    (Count.monic_of_mem A hp) (Matrix.charpoly_monic A) h0 (dvd_of_mem_normalizedFactors hp) h

namespace Count

/-- **The real factor attaining the count.** For `det A ≠ 0` there is a monic real factorization
`χ_A = q_E q_H` with all roots of `q_H` in the closed unit disk, every irreducible rational factor
of `χ_A` sharing a root with `q_E`, and `deg q_E ≤ U(A) + circleCount A`. Here `q_E` is the part
of `χ_A` with roots outside the closed disk times, for each circle factor `p`, the real minimal
polynomial of one root of `p`. -/
theorem exists_split_count (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) :
    ∃ qE qH : ℝ[X], qE.Monic ∧ qH.Monic ∧ A.charpoly.map (Int.castRingHom ℝ) = qE * qH ∧
      (∀ z ∈ (qH.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1) ∧
      (∀ p ∈ normalizedFactors (charpolyQ A),
        ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots, aeval z qE = 0) ∧
      qE.natDegree ≤ unstableCount A + circleCount A := by
  classical
  set F := normalizedFactors (charpolyQ A)
  set Fc := F.filter IsCircleFactor
  set Fn := F.filter (fun p => ¬ IsCircleFactor p)
  have hex : ∀ p : ℚ[X], ∃ w : ℂ, p ∈ F → aeval w p = 0 := by
    intro p
    by_cases hp : p ∈ F
    · have hdeg : (p.map (algebraMap ℚ ℂ)).degree ≠ 0 := by
        rw [degree_map]
        exact (natDegree_pos_iff_degree_pos.mp
          (irreducible_of_normalized_factor p hp).natDegree_pos).ne'
      obtain ⟨w, hw⟩ := IsAlgClosed.exists_root _ hdeg
      exact ⟨w, fun _ => by rwa [IsRoot, eval_map_algebraMap] at hw⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose z hz using hex
  obtain ⟨g, hgmon, hgdeg, hgz, hgdvd⟩ : ∃ g : ℚ[X] → ℝ[X], (∀ p, (g p).Monic) ∧
      (∀ p, (g p).natDegree ≤ 2) ∧ (∀ p, aeval (z p) (g p) = 0) ∧
      ∀ p ∈ F, g p ∣ p.map (algebraMap ℚ ℝ) :=
    ⟨fun p => minpoly ℝ (z p), fun p => minpoly.monic (Algebra.IsIntegral.isIntegral _),
      fun p => (minpoly.natDegree_le _).trans_eq Complex.finrank_real_complex,
      fun p => minpoly.aeval ℝ _,
      fun p hp => minpoly.dvd ℝ _ (by rw [aeval_map_algebraMap]; exact hz p hp)⟩
  have hex2 : ∀ p : ℚ[X], ∃ k : ℝ[X], p ∈ F → p.map (algebraMap ℚ ℝ) = g p * k := by
    intro p
    by_cases hp : p ∈ F
    · obtain ⟨k, hk⟩ := hgdvd p hp
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose h hh using hex2
  have hhmon : ∀ p ∈ F, (h p).Monic := fun p hp =>
    (hgmon p).of_mul_monic_left (hh p hp ▸ (monic_of_mem A hp).map _)
  have hNmon : (Fn.map (Polynomial.map (algebraMap ℚ ℝ))).prod.Monic :=
    monic_multiset_prod_of_monic _ _
      (fun p hp => (monic_of_mem A (Multiset.mem_of_mem_filter hp)).map _)
  obtain ⟨Nle, Ngt, hle_mon, hgt_mon, hN, hle, hgt⟩ := exists_split_disk _ hNmon
  have hprod : A.charpoly.map (Int.castRingHom ℝ) =
      (Fc.map (Polynomial.map (algebraMap ℚ ℝ))).prod *
        (Fn.map (Polynomial.map (algebraMap ℚ ℝ))).prod := by
    have e2 : charpolyQ A = Fc.prod * Fn.prod :=
      ((Multiset.prod_filter_mul_prod_filter_not _).trans (prod_normalizedFactors_eq A)).symm
    rw [map_charpoly_eq A ℝ, e2, Polynomial.map_mul, Polynomial.map_multiset_prod,
      Polynomial.map_multiset_prod]
  have hFcprod : (Fc.map (Polynomial.map (algebraMap ℚ ℝ))).prod =
      (Fc.map g).prod * (Fc.map h).prod := by
    rw [← Multiset.prod_map_mul]
    exact congrArg _ (Multiset.map_congr rfl (fun p hp => hh p (Multiset.mem_of_mem_filter hp)))
  have hGmon : (Fc.map g).prod.Monic := monic_multiset_prod_of_monic _ _ (fun p _ => hgmon p)
  have hHmon : (Fc.map h).prod.Monic :=
    monic_multiset_prod_of_monic _ _ (fun p hp => hhmon p (Multiset.mem_of_mem_filter hp))
  have hχ : A.charpoly.map (Int.castRingHom ℝ) =
      (Ngt * (Fc.map g).prod) * (Nle * (Fc.map h).prod) := by
    rw [hprod, hFcprod, hN]; ring
  refine ⟨Ngt * (Fc.map g).prod, Nle * (Fc.map h).prod, hgt_mon.mul hGmon, hle_mon.mul hHmon,
    hχ, ?_, ?_, ?_⟩
  · intro w hw
    have hw0 : aeval w (Nle * (Fc.map h).prod) = 0 :=
      (mem_roots_map_iff (hle_mon.mul hHmon).ne_zero).mp hw
    rw [map_mul, mul_eq_zero] at hw0
    rcases hw0 with hw0 | hw0
    · exact hle w ((mem_roots_map_iff hle_mon.ne_zero).mpr hw0)
    · rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at hw0
      obtain ⟨p, hp, hpw⟩ := Multiset.mem_map.mp hw0
      have hpF := Multiset.mem_of_mem_filter hp
      have hc : IsCircleFactor p := (Multiset.mem_filter.mp hp).2
      have hwp : aeval w (p.map (algebraMap ℚ ℝ)) = 0 := by
        rw [hh p hpF, map_mul, show aeval w (h p) = 0 from hpw, mul_zero]
      rw [aeval_map_algebraMap] at hwp
      exact (hc w ((mem_roots_map_iff (monic_of_mem A hpF).ne_zero).mpr hwp)).le
  · intro p hp
    have hp0 := (monic_of_mem A hp).ne_zero
    by_cases hc : IsCircleFactor p
    · refine ⟨z p, (mem_roots_map_iff hp0).mpr (hz p hp), ?_⟩
      have hpc : p ∈ Fc := Multiset.mem_filter.mpr ⟨hp, hc⟩
      obtain ⟨k, hk⟩ :=
        (Multiset.dvd_prod (Multiset.mem_map_of_mem g hpc)).trans (dvd_mul_left _ Ngt)
      rw [hk, map_mul, hgz p, zero_mul]
    · obtain ⟨w, hw, hw1⟩ := exists_expanding_root A hdet hp hc
      refine ⟨w, hw, ?_⟩
      have hwp : aeval w (p.map (algebraMap ℚ ℝ)) = 0 := by
        rw [aeval_map_algebraMap]; exact (mem_roots_map_iff hp0).mp hw
      have hpn : p ∈ Fn := Multiset.mem_filter.mpr ⟨hp, hc⟩
      obtain ⟨k, hk⟩ : p.map (algebraMap ℚ ℝ) ∣ Nle * Ngt :=
        hN ▸ Multiset.dvd_prod (Multiset.mem_map_of_mem _ hpn)
      have hw0 : aeval w (Nle * Ngt) = 0 := by rw [hk, map_mul, hwp, zero_mul]
      rw [map_mul, mul_eq_zero] at hw0
      rcases hw0 with h0 | h0
      · exact absurd (hle w ((mem_roots_map_iff hle_mon.ne_zero).mpr h0)) (not_le.mpr hw1)
      · rw [map_mul, h0, zero_mul]
  · have h1 : Ngt.natDegree ≤ unstableCount A := by
      have hdvd : Ngt ∣ A.charpoly.map (Int.castRingHom ℝ) := by
        rw [hprod, hN]; exact dvd_mul_of_dvd_right (dvd_mul_left Ngt Nle) _
      have hdvdC : Ngt.map (algebraMap ℝ ℂ) ∣ A.charpoly.map (Int.castRingHom ℂ) := by
        have := Polynomial.map_dvd (algebraMap ℝ ℂ) hdvd
        rwa [Polynomial.map_map, show (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) =
          Int.castRingHom ℂ from RingHom.ext_int _ _] at this
      have hle' : (Ngt.map (algebraMap ℝ ℂ)).roots ≤
          (eigenvalues A).filter (fun z => 1 < ‖z‖) :=
        Multiset.le_filter.mpr
          ⟨roots.le_of_dvd ((Matrix.charpoly_monic A).map _).ne_zero hdvdC, hgt⟩
      rw [← natDegree_map (algebraMap ℝ ℂ), ← IsAlgClosed.card_roots_eq_natDegree]
      exact Multiset.card_le_card hle'
    have h2 : ((Fc.map g).map natDegree).sum ≤ circleCount A := by
      rw [circleCount, Multiset.map_map]
      apply Multiset.sum_map_le_sum_map
      intro p hp
      have hpF := Multiset.mem_of_mem_filter hp
      refine le_min ?_ (hgdeg p)
      calc (g p).natDegree ≤ (p.map (algebraMap ℚ ℝ)).natDegree :=
            natDegree_le_of_dvd (hgdvd p hpF)
              (Polynomial.map_ne_zero (monic_of_mem A hpF).ne_zero)
        _ = p.natDegree := natDegree_map _
    rw [hgt_mon.natDegree_mul hGmon, natDegree_multiset_prod_of_monic _ (fun f hf => by
      obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hf; exact hgmon p)]
    omega

/-- The lower bound for one scheme, from the factorization `χ_A = q_E q_H` and the two
conditions on `q_E = χ_{A|E}`, `q_H = χ_{A|H}`: `dim E ≥ U(A) + circleCount A`. -/
theorem count_le_finrank_of (A : Matrix ι ι ℤ) (hsf : Squarefree (charpolyQ A))
    (S : InvariantCPS A)
    (hχ : A.charpoly.map (Int.castRingHom ℝ) =
      ((act A).restrict S.mapsTo_E).charpoly * ((act A).restrict S.mapsTo_H).charpoly)
    (ha : ∀ z ∈ (((act A).restrict S.mapsTo_H).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1)
    (hb : ∀ p ∈ normalizedFactors (charpolyQ A), ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots,
      aeval z ((act A).restrict S.mapsTo_E).charpoly = 0) :
    unstableCount A + circleCount A ≤ finrank ℝ S.E := by
  rw [← LinearMap.charpoly_natDegree ((act A).restrict S.mapsTo_E)]
  exact count_le_natDegree hsf hχ ha hb

/-- Attainment: given that the two conditions on a squarefree invariant splitting produce an
admissible scheme, some admissible scheme has `dim E ≤ U(A) + circleCount A`. -/
theorem exists_scheme_of (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) (hsf : Squarefree (charpolyQ A))
    (hsuff : ∀ {E H : Submodule ℝ (ι → ℝ)} (_ : IsCompl E H) (hE : ∀ v ∈ E, act A v ∈ E)
      (hH : ∀ v ∈ H, act A v ∈ H),
      (∀ z ∈ (((act A).restrict hH).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1) →
      (∀ p ∈ normalizedFactors (charpolyQ A), ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots,
        aeval z ((act A).restrict hE).charpoly = 0) →
      ∃ S : InvariantCPS A, S.E = E ∧ S.H = H ∧ S.Admissible) :
    ∃ S : InvariantCPS A, S.Admissible ∧ finrank ℝ S.E ≤ unstableCount A + circleCount A := by
  obtain ⟨qE, qH, hqE, hqH, hχ, ha, hb, hdeg⟩ := exists_split_count A hdet
  have hcop : IsCoprime qE qH := by
    apply Polynomial.Separable.isCoprime
    rw [← hχ, map_charpoly_eq A ℝ]
    exact (separable_charpolyQ hsf).map
  have hχ' : (act A).charpoly = qE * qH := by rw [charpoly_act A, hχ]
  obtain ⟨hcompl, hcE, hcH⟩ := charpoly_restrict_ker (act A) hqE hqH hχ' hcop
  obtain ⟨S, hSE, -, hS⟩ := hsuff hcompl (KernelSplit.mapsTo_ker_aeval _ qE)
    (KernelSplit.mapsTo_ker_aeval _ qH) (by rw [hcH]; exact ha) (by rw [hcE]; exact hb)
  refine ⟨S, hS, ?_⟩
  rw [hSE, ← LinearMap.charpoly_natDegree
    ((act A).restrict (KernelSplit.mapsTo_ker_aeval _ qE)), hcE]
  exact hdeg

/-- The least element, from the lower bound for every admissible scheme and the sufficiency of
the two conditions. -/
theorem isLeast_of (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0) (hsf : Squarefree (charpolyQ A))
    (hlow : ∀ S : InvariantCPS A, S.Admissible →
      unstableCount A + circleCount A ≤ finrank ℝ S.E)
    (hsuff : ∀ {E H : Submodule ℝ (ι → ℝ)} (_ : IsCompl E H) (hE : ∀ v ∈ E, act A v ∈ E)
      (hH : ∀ v ∈ H, act A v ∈ H),
      (∀ z ∈ (((act A).restrict hH).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1) →
      (∀ p ∈ normalizedFactors (charpolyQ A), ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots,
        aeval z ((act A).restrict hE).charpoly = 0) →
      ∃ S : InvariantCPS A, S.E = E ∧ S.H = H ∧ S.Admissible) :
    IsLeast (physDims A) (unstableCount A + circleCount A) := by
  obtain ⟨S, hS, hle⟩ := exists_scheme_of A hdet hsf hsuff
  refine ⟨⟨S, hS, le_antisymm hle (hlow S hS)⟩, ?_⟩
  rintro d ⟨S', hS', rfl⟩
  exact hlow S' hS'

end Count

/-! ### The count -/

/-- **The lower bound.** Every admissible `A`-invariant scheme has physical dimension at least
`U(A) + circleCount A` (`det A ≠ 0`, `χ_A` squarefree over `ℚ`). -/
theorem unstableCount_add_circleCount_le (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hsf : Squarefree (charpolyQ A)) (S : InvariantCPS A) (hS : S.Admissible) :
    unstableCount A + circleCount A ≤ Module.finrank ℝ S.E := by
  have hnf := normal_form A hsf S.isCompl S.mapsTo_E S.mapsTo_H
  have hab := (exists_admissible_iff A hdet hsf S.isCompl S.mapsTo_E S.mapsTo_H).mp
    ⟨S, rfl, rfl, hS⟩
  exact Count.count_le_finrank_of A hsf S hnf.1 hab.1 hab.2

/-- **The least physical dimension** for `det A ≠ 0` and `χ_A` squarefree over `ℚ`:
`d(A) = U(A) + circleCount A`. -/
theorem isLeast_physDims_squarefree (A : Matrix ι ι ℤ) (hdet : A.det ≠ 0)
    (hsf : Squarefree (charpolyQ A)) :
    IsLeast (physDims A) (unstableCount A + circleCount A) :=
  Count.isLeast_of A hdet hsf (unstableCount_add_circleCount_le A hdet hsf)
    (fun hc hE hH ha hb => (exists_admissible_iff A hdet hsf hc hE hH).mpr ⟨ha, hb⟩)

/-- **(3) Squarefree `χ_A`.** Normal form of an invariant splitting, the characterization of the
admissible ones, the least physical dimension `U(A) + Σ_{circle p} min(deg p, 2)`, and Kronecker's
identification of the circle factors as cyclotomic polynomials. -/
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
  refine ⟨fun E H hc hE hH => ?_, isLeast_physDims_squarefree A hdet hsf,
    fun p hp => isCircleFactor_iff_cyclotomic A hp⟩
  have hnf := normal_form A hsf hc hE hH
  exact ⟨hnf.1, hnf.2.1, hnf.2.2, exists_admissible_iff A hdet hsf hc hE hH⟩

end

end InflationDimension
