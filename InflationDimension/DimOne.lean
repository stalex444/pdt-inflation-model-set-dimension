module
public import Mathlib
public import InflationDimension.Count

@[expose] public section
/-!
# Dimension one, finite order, and two examples on small lattices

Statements (5), (6), (7) and (12): the least physical dimension is `1` exactly in the
Pisot–Salem case (or for `A = ±1` on `ℤ¹`); in the finite-order case it counts `1` for each
factor `x ± 1` and `2` for each other cyclotomic factor; on `ℤ²` the identity and the Jordan
matrix `[[1, 1], [0, 1]]` share `χ = (x − 1)²` but have least physical dimensions `1` and `2`; and
the companion matrix of `x⁴ − x³ − x² − x + 1` is a non-hyperbolic example with least physical
dimension `1`.

The general statements (5) and (6) are corollaries of the count of statement (3)
(`isLeast_physDims_squarefree`), of the expanding-root and Kronecker lemmas, of the normal form,
and of the disk condition of statement (1).
-/

namespace InflationDimension

open Polynomial Filter Topology Module QuadraticMap
open scoped Kronecker Pointwise

noncomputable section

namespace DimOne

section Factors

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem charpolyQ_monic (A : Matrix ι ι ℤ) : (charpolyQ A).Monic :=
  (Matrix.charpoly_monic A).map _

theorem charpolyQ_ne_zero (A : Matrix ι ι ℤ) : charpolyQ A ≠ 0 :=
  (charpolyQ_monic A).ne_zero

theorem natDegree_charpolyQ (A : Matrix ι ι ℤ) :
    (charpolyQ A).natDegree = Fintype.card ι := by
  rw [charpolyQ, (Matrix.charpoly_monic A).natDegree_map, Matrix.charpoly_natDegree_eq_dim]

theorem charpoly_map_complex (A : Matrix ι ι ℤ) :
    A.charpoly.map (Int.castRingHom ℂ) = (charpolyQ A).map (algebraMap ℚ ℂ) := by
  rw [charpolyQ, Polynomial.map_map]
  congr 1

theorem charpoly_map_complex_real (A : Matrix ι ι ℤ) :
    A.charpoly.map (Int.castRingHom ℂ) =
      (A.charpoly.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ) := by
  rw [Polynomial.map_map]
  congr 1

theorem eigenvalues_eq (A : Matrix ι ι ℤ) :
    eigenvalues A = ((charpolyQ A).map (algebraMap ℚ ℂ)).roots := by
  rw [eigenvalues, charpoly_map_complex]

theorem mem_normalizedFactors {A : Matrix ι ι ℤ} {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) :
    Irreducible p ∧ p.Monic ∧ p ∣ charpolyQ A :=
  (Polynomial.mem_normalizedFactors_iff (charpolyQ_ne_zero A)).mp hp

theorem prod_normalizedFactors (A : Matrix ι ι ℤ) :
    (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).prod = charpolyQ A := by
  refine Polynomial.eq_of_monic_of_associated ?_ (charpolyQ_monic A)
    (UniqueFactorizationMonoid.prod_normalizedFactors (charpolyQ_ne_zero A))
  have := Polynomial.monic_multiset_prod_of_monic
    (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) id
    (fun p hp => (mem_normalizedFactors hp).2.1)
  simpa using this

theorem eigenvalues_eq_bind (A : Matrix ι ι ℤ) :
    eigenvalues A = (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).bind
      (fun p => (p.map (algebraMap ℚ ℂ)).roots) := by
  conv_lhs => rw [eigenvalues_eq, ← prod_normalizedFactors A]
  rw [Polynomial.map_multiset_prod, Polynomial.roots_multiset_prod, Multiset.bind_map]
  intro h
  obtain ⟨p, hp, hp0⟩ := Multiset.mem_map.mp h
  exact ((mem_normalizedFactors hp).2.1.map (algebraMap ℚ ℂ)).ne_zero hp0

theorem unstableCount_eq_sum (A : Matrix ι ι ℤ) :
    unstableCount A = ((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).map
      (fun p => Multiset.card
        (((p.map (algebraMap ℚ ℂ)).roots).filter (fun z => 1 < ‖z‖)))).sum := by
  rw [unstableCount, eigenvalues_eq_bind, Multiset.filter_bind, Multiset.card_bind]
  rfl

/-- The complex conjugate of an eigenvalue is an eigenvalue. -/
theorem conj_mem_eigenvalues {A : Matrix ι ι ℤ} {z : ℂ} (hz : z ∈ eigenvalues A) :
    starRingEnd ℂ z ∈ eigenvalues A := by
  have hne : A.charpoly.map (Int.castRingHom ℂ) ≠ 0 :=
    ((Matrix.charpoly_monic A).map _).ne_zero
  rw [eigenvalues, mem_roots hne, IsRoot.def, eval_map] at hz ⊢
  have h := congrArg (starRingEnd ℂ) hz
  rw [hom_eval₂, map_zero] at h
  rwa [show (starRingEnd ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ from
    RingHom.ext_int _ _] at h

open Classical in
/-- The number of irreducible factors is at most `U(A) + circleCount A`, when every factor that
is not a circle factor has a root of modulus `> 1`. -/
theorem card_le_unstableCount_add_circleCount {A : Matrix ι ι ℤ}
    (hexp : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ¬ IsCircleFactor p → ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots, 1 < ‖z‖) :
    Multiset.card (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) ≤
      unstableCount A + circleCount A := by
  have hU := unstableCount_eq_sum A
  set N := UniqueFactorizationMonoid.normalizedFactors (charpolyQ A) with hN
  set g : ℚ[X] → ℕ := fun p => Multiset.card
    (((p.map (algebraMap ℚ ℂ)).roots).filter (fun z => 1 < ‖z‖)) with hg
  have hsplit : (N.map g).sum = ((N.filter IsCircleFactor).map g).sum +
      ((N.filter (fun p => ¬ IsCircleFactor p)).map g).sum := by
    rw [← Multiset.sum_add, ← Multiset.map_add, Multiset.filter_add_not]
  have h1 : Multiset.card (N.filter (fun p => ¬ IsCircleFactor p)) ≤
      ((N.filter (fun p => ¬ IsCircleFactor p)).map g).sum := by
    have hle : ∀ p ∈ N.filter (fun p => ¬ IsCircleFactor p), (fun _ => 1) p ≤ g p := by
      intro p hp
      rw [Multiset.mem_filter] at hp
      obtain ⟨z, hz, hz1⟩ := hexp p hp.1 hp.2
      exact Nat.succ_le_of_lt
        (Multiset.card_pos_iff_exists_mem.mpr ⟨z, Multiset.mem_filter.mpr ⟨hz, hz1⟩⟩)
    calc Multiset.card (N.filter (fun p => ¬ IsCircleFactor p))
        = ((N.filter (fun p => ¬ IsCircleFactor p)).map (fun _ => 1)).sum := by simp
      _ ≤ _ := Multiset.sum_map_le_sum_map _ _ hle
  have h2 : Multiset.card (N.filter IsCircleFactor) ≤ circleCount A := by
    have hle : ∀ p ∈ N.filter IsCircleFactor, (fun _ => 1) p ≤ min p.natDegree 2 := by
      intro p hp
      have hirr := (mem_normalizedFactors (Multiset.mem_filter.mp hp).1).1
      have := Irreducible.natDegree_pos hirr
      simp only
      omega
    calc Multiset.card (N.filter IsCircleFactor)
        = ((N.filter IsCircleFactor).map (fun _ => 1)).sum := by simp
      _ ≤ _ := Multiset.sum_map_le_sum_map _ _ hle
  have h3 : Multiset.card N = Multiset.card (N.filter IsCircleFactor) +
      Multiset.card (N.filter (fun p => ¬ IsCircleFactor p)) := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  rw [hU, hsplit, h3]
  omega

theorem charpoly_eq_of_card_eq_one {A : Matrix ι ι ℤ} (hcard : Fintype.card ι = 1) :
    A.charpoly = X - C A.det := by
  have hm := Matrix.charpoly_monic A
  have hd : A.charpoly.natDegree = 1 := by rw [Matrix.charpoly_natDegree_eq_dim, hcard]
  rw [hm.eq_X_add_C hd]
  have h := Matrix.det_eq_sign_charpoly_coeff A
  rw [hcard, pow_one, neg_one_mul] at h
  rw [h, map_neg, sub_neg_eq_add]

theorem eigenvalues_of_card_eq_one {A : Matrix ι ι ℤ} (hcard : Fintype.card ι = 1) :
    eigenvalues A = {((A.det : ℤ) : ℂ)} := by
  rw [eigenvalues, charpoly_eq_of_card_eq_one hcard, Polynomial.map_sub, map_X, Polynomial.map_C,
    eq_intCast, roots_X_sub_C]

theorem eq_one_or_neg_one {A : Matrix ι ι ℤ} (hcard : Fintype.card ι = 1) (hdet : A.det ≠ 0)
    (hU : unstableCount A = 0) : A = 1 ∨ A = -1 := by
  have hd : A.det = 1 ∨ A.det = -1 := by
    rw [unstableCount, eigenvalues_of_card_eq_one hcard, Multiset.filter_singleton] at hU
    split_ifs at hU with hn
    · simp at hU
    · rw [Complex.norm_intCast] at hn
      have h1 : |A.det| ≤ 1 := by
        have : |(A.det : ℝ)| ≤ 1 := not_lt.mp hn
        exact_mod_cast this
      rw [abs_le] at h1
      omega
  have : Unique ι := (Fintype.card_eq_one_iff_nonempty_unique.mp hcard).some
  have hA : ∀ i j, A i j = A.det := by
    intro i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default, Matrix.det_unique]
  rcases hd with h | h
  · left
    ext i j
    rw [hA, h, Subsingleton.elim i j]
    simp
  · right
    ext i j
    rw [hA, h, Subsingleton.elim i j]
    simp

theorem det_eq_one_or_neg_one {A : Matrix ι ι ℤ} (hcard : Fintype.card ι = 1)
    (hA : A = 1 ∨ A = -1) : A.det = 1 ∨ A.det = -1 := by
  rcases hA with rfl | rfl
  · left; simp
  · right; rw [Matrix.det_neg, hcard]; simp

theorem det_ne_zero_of_circle {A : Matrix ι ι ℤ} (h : ∀ z ∈ eigenvalues A, ‖z‖ = 1) :
    A.det ≠ 0 := by
  intro h0
  have hc : A.charpoly.coeff 0 = 0 := by
    have := Matrix.det_eq_sign_charpoly_coeff A
    rw [h0] at this
    rcases neg_one_pow_eq_or ℤ (Fintype.card ι) with h1 | h1 <;> rw [h1] at this <;> linarith
  have hroot : (0 : ℂ) ∈ eigenvalues A := by
    rw [eigenvalues, mem_roots ((Matrix.charpoly_monic A).map _).ne_zero, IsRoot.def,
      ← coeff_zero_eq_eval_zero, coeff_map, hc, map_zero]
  have := h 0 hroot
  simp at this

end Factors

/-! ### Statement (5), from the count -/

section DimensionOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
theorem dimension_one_iff_of {A : Matrix ι ι ℤ} (hdet : A.det ≠ 0)
    (hcount : IsLeast (physDims A) (unstableCount A + circleCount A))
    (hexp : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ¬ IsCircleFactor p → ∃ z ∈ (p.map (algebraMap ℚ ℂ)).roots, 1 < ‖z‖) :
    IsLeast (physDims A) 1 ↔
      (Irreducible (charpolyQ A) ∧ unstableCount A = 1) ∨
        (Fintype.card ι = 1 ∧ (A = 1 ∨ A = -1)) := by
  constructor
  · intro h1
    have hsum : unstableCount A + circleCount A = 1 := hcount.unique h1
    have hle := card_le_unstableCount_add_circleCount hexp
    have hU' := unstableCount_eq_sum A
    set N := UniqueFactorizationMonoid.normalizedFactors (charpolyQ A) with hN
    have hNne : N ≠ 0 := by
      intro h0
      have hU0 : unstableCount A = 0 := by rw [hU', h0]; simp
      have hc0 : circleCount A = 0 := by
        unfold circleCount
        rw [← hN, h0]
        simp
      omega
    have hcard : Multiset.card N = 1 := by
      have := Multiset.card_pos.mpr hNne
      omega
    obtain ⟨p, hp⟩ := Multiset.card_eq_one.mp hcard
    have hpmem : p ∈ N := by rw [hp]; exact Multiset.mem_singleton_self p
    have hχ : charpolyQ A = p := by
      rw [← prod_normalizedFactors A, ← hN, hp, Multiset.prod_singleton]
    have hirr : Irreducible (charpolyQ A) := hχ ▸ (mem_normalizedFactors hpmem).1
    by_cases hc : IsCircleFactor p
    · right
      have hU : unstableCount A = 0 := by
        rw [hU', hp]
        simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.card_eq_zero]
        rw [Multiset.filter_eq_nil]
        intro z hz
        rw [hc z hz]
        exact lt_irrefl 1
      have hcc : circleCount A = min p.natDegree 2 := by
        unfold circleCount
        rw [← hN, hp, Multiset.filter_singleton, ite_eq_left hc]
        simp
      have hdeg : p.natDegree = 1 := by
        have := Irreducible.natDegree_pos (mem_normalizedFactors hpmem).1
        omega
      have hcardι : Fintype.card ι = 1 := by
        rw [← natDegree_charpolyQ, hχ, hdeg]
      exact ⟨hcardι, eq_one_or_neg_one hcardι hdet hU⟩
    · left
      have hcc : circleCount A = 0 := by
        unfold circleCount
        rw [← hN, hp, Multiset.filter_singleton, ite_eq_right hc]
        simp
      exact ⟨hirr, by omega⟩
  · rintro (⟨hirr, hU⟩ | ⟨hcard, hA⟩)
    · have hN : UniqueFactorizationMonoid.normalizedFactors (charpolyQ A) = {charpolyQ A} := by
        rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr,
          (charpolyQ_monic A).normalize_eq_self]
      have hc : ¬ IsCircleFactor (charpolyQ A) := by
        intro hc
        have : unstableCount A = 0 := by
          rw [unstableCount, eigenvalues_eq, Multiset.card_eq_zero, Multiset.filter_eq_nil]
          intro z hz
          rw [hc z hz]
          exact lt_irrefl 1
        omega
      have hcc : circleCount A = 0 := by
        unfold circleCount
        rw [hN, Multiset.filter_singleton, ite_eq_right hc]
        simp
      have h := hcount
      rwa [hU, hcc] at h
    · have hd := det_eq_one_or_neg_one hcard hA
      have hU : unstableCount A = 0 := by
        rw [unstableCount, eigenvalues_of_card_eq_one hcard]
        rcases hd with h | h <;> simp [h, Multiset.filter_singleton]
      have hχ : charpolyQ A = X - C ((A.det : ℤ) : ℚ) := by
        rw [charpolyQ, charpoly_eq_of_card_eq_one hcard]
        simp
      have hirr : Irreducible (charpolyQ A) := by
        rw [hχ]
        exact irreducible_X_sub_C _
      have hN : UniqueFactorizationMonoid.normalizedFactors (charpolyQ A) = {charpolyQ A} := by
        rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr,
          (charpolyQ_monic A).normalize_eq_self]
      have hc : IsCircleFactor (charpolyQ A) := by
        intro z hz
        rw [hχ, Polynomial.map_sub, map_X, Polynomial.map_C, roots_X_sub_C,
          Multiset.mem_singleton] at hz
        rcases hd with h | h <;> rw [hz, h] <;> simp
      have hcc : circleCount A = 1 := by
        unfold circleCount
        rw [hN, Multiset.filter_singleton, ite_eq_left hc]
        simp [natDegree_charpolyQ, hcard]
      have h := hcount
      rwa [hU, hcc] at h

theorem eigenline_of {A : Matrix ι ι ℤ} (hU : unstableCount A = 1)
    (hnf : ∀ (E H : Submodule ℝ (ι → ℝ)), IsCompl E H → ∀ (hE : ∀ v ∈ E, act A v ∈ E)
      (hH : ∀ v ∈ H, act A v ∈ H),
      A.charpoly.map (Int.castRingHom ℝ) =
          ((act A).restrict hE).charpoly * ((act A).restrict hH).charpoly ∧
        E = LinearMap.ker (aeval (act A) ((act A).restrict hE).charpoly))
    (hdisk : ∀ S : InvariantCPS A, S.Admissible →
      ∀ z ∈ (((act A).restrict S.mapsTo_H).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1) :
    ∃ r : ℝ, 1 < |r| ∧ (r : ℂ) ∈ eigenvalues A ∧ (∀ z ∈ eigenvalues A, z ≠ r → ‖z‖ ≤ 1) ∧
      ∀ S : InvariantCPS A, S.Admissible → finrank ℝ S.E = 1 →
        S.E = LinearMap.ker (act A - r • LinearMap.id) := by
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.mp hU
  have hzmem : z ∈ (eigenvalues A).filter (fun z => 1 < ‖z‖) := by
    rw [hz]; exact Multiset.mem_singleton_self z
  rw [Multiset.mem_filter] at hzmem
  have hconj : starRingEnd ℂ z = z := by
    have hc : starRingEnd ℂ z ∈ (eigenvalues A).filter (fun z => 1 < ‖z‖) :=
      Multiset.mem_filter.mpr ⟨conj_mem_eigenvalues hzmem.1, by
        rw [Complex.norm_conj]; exact hzmem.2⟩
    rw [hz] at hc
    exact Multiset.mem_singleton.mp hc
  have hzr : ((z.re : ℝ) : ℂ) = z := Complex.conj_eq_iff_re.mp hconj
  have hr1 : 1 < |z.re| := by
    have := hzmem.2
    rwa [← hzr, Complex.norm_real, Real.norm_eq_abs] at this
  refine ⟨z.re, hr1, by rw [hzr]; exact hzmem.1, ?_, ?_⟩
  · intro w hw hne
    by_contra hlt
    have hw' : w ∈ (eigenvalues A).filter (fun z => 1 < ‖z‖) :=
      Multiset.mem_filter.mpr ⟨hw, not_le.mp hlt⟩
    rw [hz, Multiset.mem_singleton] at hw'
    exact hne (hw'.trans hzr.symm)
  · intro S hS hdim
    obtain ⟨hχ, hE⟩ := hnf S.E S.H S.isCompl S.mapsTo_E S.mapsTo_H
    set qE := ((act A).restrict S.mapsTo_E).charpoly with hqEdef
    set qH := ((act A).restrict S.mapsTo_H).charpoly with hqHdef
    have hqEm : qE.Monic := LinearMap.charpoly_monic _
    have hqHm : qH.Monic := LinearMap.charpoly_monic _
    have hqEd : qE.natDegree = 1 := by rw [hqEdef, LinearMap.charpoly_natDegree, hdim]
    have hqE : qE = X + C (qE.coeff 0) := hqEm.eq_X_add_C hqEd
    have hcast : ∀ (p : ℝ[X]) (t : ℝ),
        (p.map (algebraMap ℝ ℂ)).eval (t : ℂ) = ((p.eval t : ℝ) : ℂ) := by
      intro p t
      rw [eval_map, ← Complex.coe_algebraMap, eval₂_at_apply]
    have hχr : (A.charpoly.map (Int.castRingHom ℝ)).eval z.re = 0 := by
      have h1 : ((z.re : ℝ) : ℂ) ∈ eigenvalues A := by rw [hzr]; exact hzmem.1
      rw [eigenvalues, charpoly_map_complex_real, mem_roots ((((Matrix.charpoly_monic
        A).map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ)).ne_zero), IsRoot.def, hcast] at h1
      exact_mod_cast h1
    have hHr : qH.eval z.re ≠ 0 := by
      intro h0
      have hmem : ((z.re : ℝ) : ℂ) ∈ (qH.map (algebraMap ℝ ℂ)).roots := by
        rw [mem_roots (hqHm.map _).ne_zero, IsRoot.def, hcast, h0, Complex.ofReal_zero]
      have := hdisk S hS _ hmem
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have hEr : qE.eval z.re = 0 := by
      rw [hχ, eval_mul] at hχr
      exact (mul_eq_zero.mp hχr).resolve_right hHr
    have hcoef : qE.coeff 0 = -z.re := by
      rw [hqE, eval_add, eval_X, eval_C] at hEr
      linarith
    rw [hE]
    congr 1
    rw [hqE, map_add, aeval_X, aeval_C, hcoef, Algebra.algebraMap_eq_smul_one, neg_smul,
      ← sub_eq_add_neg]
    rfl

end DimensionOne

/-! ### Statement (6), from the count -/

section FiniteOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
theorem finite_order_of {A : Matrix ι ι ℤ}
    (hcount : A.det ≠ 0 → Squarefree (charpolyQ A) →
      IsLeast (physDims A) (unstableCount A + circleCount A))
    (hcyc : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      IsCircleFactor p ↔ ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ)
    (hsf : Squarefree (charpolyQ A)) (h : ∀ z ∈ eigenvalues A, ‖z‖ = 1) :
    (∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
        ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ) ∧
      IsLeast (physDims A)
        (((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).map
          (fun p => min p.natDegree 2)).sum) := by
  have hcirc : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      IsCircleFactor p := by
    intro p hp z hz
    apply h
    rw [eigenvalues_eq_bind]
    exact Multiset.mem_bind.mpr ⟨p, hp, hz⟩
  refine ⟨fun p hp => (hcyc p hp).mp (hcirc p hp), ?_⟩
  have hU : unstableCount A = 0 := by
    rw [unstableCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro z hz
    rw [h z hz]
    exact lt_irrefl 1
  have hc : circleCount A = ((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).map
      (fun p => min p.natDegree 2)).sum := by
    unfold circleCount
    rw [Multiset.filter_eq_self.mpr hcirc]
  have h2 := hcount (det_ne_zero_of_circle h) hsf
  rwa [hU, hc, zero_add] at h2

theorem cyclotomic_of {A : Matrix ι ι ℤ}
    (hcount : A.det ≠ 0 → Squarefree (charpolyQ A) →
      IsLeast (physDims A) (unstableCount A + circleCount A))
    (hcyc : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      IsCircleFactor p ↔ ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ)
    {n : ℕ} (hn : 3 ≤ n) (hχ : A.charpoly = cyclotomic n ℤ) : IsLeast (physDims A) 2 := by
  have hQ : charpolyQ A = cyclotomic n ℚ := by rw [charpolyQ, hχ, map_cyclotomic]
  have hirr : Irreducible (charpolyQ A) := hQ ▸ cyclotomic.irreducible_rat (by omega)
  have hall : ∀ z ∈ eigenvalues A, ‖z‖ = 1 := by
    intro z hz
    rw [eigenvalues, hχ, map_cyclotomic] at hz
    have : NeZero (n : ℂ) := ⟨by exact_mod_cast (show n ≠ 0 by omega)⟩
    exact (isRoot_cyclotomic_iff.mp (isRoot_of_mem_roots hz)).norm'_eq_one (by omega)
  obtain ⟨-, h2⟩ := finite_order_of hcount hcyc hirr.squarefree hall
  have hN : UniqueFactorizationMonoid.normalizedFactors (charpolyQ A) = {cyclotomic n ℚ} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr, hQ,
      (cyclotomic.monic n ℚ).normalize_eq_self]
  rw [hN] at h2
  have htot : 2 ≤ n.totient := by
    have h0 : 0 < n.totient := Nat.totient_pos.mpr (by omega)
    have h1 : n.totient ≠ 1 := by
      rw [Ne, Nat.totient_eq_one_iff]
      omega
    omega
  simpa [natDegree_cyclotomic, htot] using h2

end FiniteOrder

/-! ### The Salem quartic -/

section Salem

theorem charpoly_CSalem : CSalem.charpoly = X ^ 4 - X ^ 3 - X ^ 2 - X + 1 := by
  have hsa : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := by decide
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, CSalem, Matrix.charmatrix_apply,
    Matrix.submatrix_apply, Matrix.diagonal_apply, hsa]
  ring

theorem salemZ_irreducible : Irreducible (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℤ[X]) := by
  have hm : (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℤ[X]).Monic := by monicity!
  have hnd : (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℤ[X]).natDegree = 4 := by compute_degree!
  rw [hm.irreducible_iff_natDegree', hnd]
  refine ⟨fun h => by simp [h] at hnd, ?_⟩
  intro f g hf hg hfg hdeg
  have hfg' : f.natDegree + g.natDegree = 4 := by rw [← hf.natDegree_mul hg, hfg, hnd]
  simp only [Finset.mem_Ioc] at hdeg
  have hg12 : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
  rcases hg12 with hg1 | hg2
  · obtain ⟨c, hc⟩ : ∃ c, g.coeff 0 = c := ⟨_, rfl⟩
    have hgX := hg.eq_X_add_C hg1
    rw [hc] at hgX
    have hroot := congrArg (eval (-c)) hfg
    rw [eval_mul, hgX] at hroot
    simp only [eval_add, eval_X, eval_C, neg_add_cancel, mul_zero, eval_sub, eval_pow,
      eval_one] at hroot
    have hunit : (-c) * (-(-c) ^ 3 + (-c) ^ 2 + (-c) + 1) = 1 := by
      linear_combination hroot
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h | h <;> rw [h] at hroot <;>
      norm_num at hroot
  · have hf2 : f.natDegree = 2 := by omega
    have hfe : f = X ^ 2 + C (f.coeff 1) * X + C (f.coeff 0) := by
      conv_lhs => rw [hf.as_sum, hf2]
      simp [Finset.sum_range_succ]
      ring
    have hge : g = X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
      conv_lhs => rw [hg.as_sum, hg2]
      simp [Finset.sum_range_succ]
      ring
    have hprod : f * g = X ^ 4 + C (f.coeff 1 + g.coeff 1) * X ^ 3 +
        C (f.coeff 0 + g.coeff 0 + f.coeff 1 * g.coeff 1) * X ^ 2 +
        C (f.coeff 1 * g.coeff 0 + f.coeff 0 * g.coeff 1) * X + C (f.coeff 0 * g.coeff 0) := by
      conv_lhs => rw [hfe, hge]
      simp only [map_add, map_mul]
      ring
    rw [hprod] at hfg
    have e0 := congrArg (coeff · 0) hfg
    have e1 := congrArg (coeff · 1) hfg
    have e2 := congrArg (coeff · 2) hfg
    have e3 := congrArg (coeff · 3) hfg
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one]
      at e0 e1 e2 e3
    norm_num at e0 e1 e2 e3
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' e0 with ⟨hd, hb⟩ | ⟨hd, hb⟩
    · rw [hd, hb] at e2
      have hpar : g.coeff 1 * (g.coeff 1 + 1) = 3 := by
        linear_combination -e2 + g.coeff 1 * e3
      have hev := Int.even_mul_succ_self (g.coeff 1)
      rw [hpar, Int.even_iff] at hev
      norm_num at hev
    · rw [hd, hb] at e1
      omega

theorem irreducible_charpolyQ_CSalem : Irreducible (charpolyQ CSalem) := by
  have hm : (X ^ 4 - X ^ 3 - X ^ 2 - X + 1 : ℤ[X]).Monic := by monicity!
  have h := (hm.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp salemZ_irreducible
  rw [charpolyQ, charpoly_CSalem]
  rwa [algebraMap_int_eq] at h

theorem exists_salem_root :
    ∃ r : ℝ, 1.7220 < r ∧ r < 1.7221 ∧ r ^ 4 - r ^ 3 - r ^ 2 - r + 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 4 - x ^ 3 - x ^ 2 - x + 1)
      (Set.Icc 1.7220 1.7221) := by fun_prop
  have h := intermediate_value_Ioo (by norm_num : (1.7220 : ℝ) ≤ 1.7221) hcont
  have h0 : (0 : ℝ) ∈ Set.Ioo ((fun x : ℝ => x ^ 4 - x ^ 3 - x ^ 2 - x + 1) 1.7220)
      ((fun x : ℝ => x ^ 4 - x ^ 3 - x ^ 2 - x + 1) 1.7221) := by
    simp only [Set.mem_Ioo]
    norm_num
  obtain ⟨r, ⟨h1, h2⟩, hr⟩ := h h0
  exact ⟨r, h1, h2, hr⟩

theorem eigenvalues_CSalem :
    ∃ r : ℝ, 1.7220 < r ∧ r < 1.7221 ∧ ∃ z : ℂ, ‖z‖ = 1 ∧
      eigenvalues CSalem = {(r : ℂ), ((r⁻¹ : ℝ) : ℂ), z, starRingEnd ℂ z} := by
  obtain ⟨r, h1, h2, hr⟩ := exists_salem_root
  have hrpos : 0 < r := by linarith
  have hr0 : r ≠ 0 := hrpos.ne'
  obtain ⟨y₁, hy₁⟩ : ∃ y : ℝ, y = r + r⁻¹ := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y : ℝ, y = 1 - y₁ := ⟨_, rfl⟩
  have hy1pos : 0 < y₁ := by rw [hy₁]; positivity
  have hq1 : y₁ ^ 2 - y₁ - 3 = 0 := by
    have : y₁ ^ 2 - y₁ - 3 = (r ^ 4 - r ^ 3 - r ^ 2 - r + 1) / r ^ 2 := by
      rw [hy₁]
      field_simp
      ring
    rw [this, hr, zero_div]
  obtain ⟨w, hw2⟩ : ∃ w : ℝ, w ^ 2 = y₁ := ⟨Real.sqrt y₁, Real.sq_sqrt hy1pos.le⟩
  obtain ⟨z, hzre, hzim⟩ : ∃ z : ℂ, z.re = y₂ / 2 ∧ z.im = w / 2 := ⟨⟨y₂ / 2, w / 2⟩, rfl, rfl⟩
  have hzn2 : Complex.normSq z = 1 := by
    rw [Complex.normSq_apply, hzre, hzim, hy₂]
    linear_combination (1 / 4 : ℝ) * hw2 + (1 / 4 : ℝ) * hq1
  have hzn : ‖z‖ = 1 := by rw [Complex.norm_def, hzn2, Real.sqrt_one]
  have hsum1 : ((r : ℝ) : ℂ) + ((r⁻¹ : ℝ) : ℂ) = (y₁ : ℂ) := by
    rw [hy₁]; push_cast; ring
  have hprod1 : ((r : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hr0, Complex.ofReal_one]
  have hsum2 : z + starRingEnd ℂ z = (y₂ : ℂ) := by
    rw [Complex.add_conj, hzre]; push_cast; ring
  have hprod2 : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, hzn2, Complex.ofReal_one]
  have hab : (y₁ : ℂ) + (y₂ : ℂ) = 1 := by
    rw [hy₂]; push_cast; ring
  have hab2 : (y₁ : ℂ) * (y₂ : ℂ) = -3 := by
    have : y₁ * y₂ = -3 := by rw [hy₂]; linear_combination -hq1
    rw [← Complex.ofReal_mul, this]; push_cast; ring
  have hpoly : CSalem.charpoly.map (Int.castRingHom ℂ) =
      (X - C ((r : ℝ) : ℂ)) * ((X - C ((r⁻¹ : ℝ) : ℂ)) *
        ((X - C z) * (X - C (starRingEnd ℂ z)))) := by
    have key : ∀ u v : ℂ, (X - C u) * (X - C v) = X ^ 2 - C (u + v) * X + C (u * v) := by
      intro u v; simp only [map_add, map_mul]; ring
    have e1 := key ((r : ℝ) : ℂ) ((r⁻¹ : ℝ) : ℂ)
    have e2 := key z (starRingEnd ℂ z)
    rw [hsum1, hprod1, map_one] at e1
    rw [hsum2, hprod2, map_one] at e2
    have k1 : C (y₁ : ℂ) + C (y₂ : ℂ) = (1 : ℂ[X]) := by rw [← map_add, hab, map_one]
    have k2 : C (y₁ : ℂ) * C (y₂ : ℂ) = (-3 : ℂ[X]) := by rw [← map_mul, hab2, map_neg, map_ofNat]
    rw [charpoly_CSalem, ← mul_assoc, e1, e2]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X,
      Polynomial.map_one]
    linear_combination (X ^ 3 + X) * k1 - X ^ 2 * k2
  have hm : (({((r : ℝ) : ℂ), ((r⁻¹ : ℝ) : ℂ), z, starRingEnd ℂ z} : Multiset ℂ).map
      (fun a => X - C a)).prod = (X - C ((r : ℝ) : ℂ)) * ((X - C ((r⁻¹ : ℝ) : ℂ)) *
        ((X - C z) * (X - C (starRingEnd ℂ z)))) := by
    simp [Multiset.insert_eq_cons]
  refine ⟨r, h1, h2, z, hzn, ?_⟩
  rw [eigenvalues, hpoly, ← hm, Polynomial.roots_multiset_prod_X_sub_C]

/-- The Salem quartic: one root in `(1.7220, 1.7221)`, of modulus `> 1`; one eigenvalue on the
unit circle; `U = 1`. -/
theorem salem_spectrum :
    ∃ r : ℝ, 1.7220 < r ∧ r < 1.7221 ∧ (r : ℂ) ∈ eigenvalues CSalem ∧
      unstableCount CSalem = 1 ∧ ¬ IsHyperbolic CSalem := by
  obtain ⟨r, h1, h2, z, hz, he⟩ := eigenvalues_CSalem
  have hrpos : 0 < r := by linarith
  have hA : 1 < ‖((r : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hrpos.le]; linarith
  have hB : ¬ 1 < ‖((r⁻¹ : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hrpos.le), not_lt]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hC : ¬ 1 < ‖z‖ := by rw [hz]; exact lt_irrefl 1
  have hD : ¬ 1 < ‖starRingEnd ℂ z‖ := by rw [Complex.norm_conj, hz]; exact lt_irrefl 1
  refine ⟨r, h1, h2, by rw [he]; simp, ?_, ?_⟩
  · rw [unstableCount, he]
    simp only [Multiset.insert_eq_cons]
    rw [Multiset.filter_cons_of_pos (p := fun z : ℂ => 1 < ‖z‖) _ hA,
      Multiset.filter_cons_of_neg (p := fun z : ℂ => 1 < ‖z‖) _ hB,
      Multiset.filter_cons_of_neg (p := fun z : ℂ => 1 < ‖z‖) _ hC,
      Multiset.filter_singleton, ite_eq_right hD]
    simp
  · intro hh
    exact hh z (by rw [he]; simp) hz

theorem det_CSalem : CSalem.det = 1 := by
  rw [Matrix.det_eq_sign_charpoly_coeff, charpoly_CSalem]
  simp

end Salem

/-! ### Statement (7): the identity and the Jordan matrix on `ℤ²` -/

section Plane

theorem one_le_finrank_E {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℤ} (S : InvariantCPS A) : 1 ≤ finrank ℝ S.E := by
  by_contra h
  have h0 : finrank ℝ S.E = 0 := by omega
  have hE : S.E = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hH : S.H = ⊤ := by
    have := S.isCompl.sup_eq_top
    rwa [hE, bot_sup_eq] at this
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hmem : Pi.basisFun ℝ ι i ∈ intLattice ι := Submodule.subset_span ⟨i, rfl⟩
  have h1 := congrFun (S.inj _ hmem (by rw [hH]; exact Submodule.mem_top)) i
  simp at h1

theorem charpoly_one_two : (1 : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 := by
  rw [Matrix.charpoly_one, Fintype.card_fin]

theorem charpoly_jordan :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp
  ring

theorem unstableCount_one_two : unstableCount (1 : Matrix (Fin 2) (Fin 2) ℤ) = 0 := by
  have he : eigenvalues (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 ::ₘ {1} := by
    rw [eigenvalues, charpoly_one_two, Polynomial.map_pow, Polynomial.map_sub, map_X,
      Polynomial.map_one, ← C_1, roots_pow, roots_X_sub_C, two_nsmul, Multiset.singleton_add]
  have hn : ¬ (1 : ℝ) < ‖(1 : ℂ)‖ := by rw [norm_one]; exact lt_irrefl 1
  rw [unstableCount, he, Multiset.filter_cons_of_neg (p := fun z : ℂ => 1 < ‖z‖) _ hn,
    Multiset.filter_singleton, ite_eq_right hn]
  rfl

open Classical in
theorem circleCount_one_two : circleCount (1 : Matrix (Fin 2) (Fin 2) ℤ) = 2 := by
  have hχ : charpolyQ (1 : Matrix (Fin 2) (Fin 2) ℤ) = (X - C 1) ^ 2 := by
    rw [charpolyQ, charpoly_one_two]
    simp
  have hN : UniqueFactorizationMonoid.normalizedFactors
      (charpolyQ (1 : Matrix (Fin 2) (Fin 2) ℤ)) = (X - C 1) ::ₘ {X - C 1} := by
    rw [hχ, UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C 1),
      (monic_X_sub_C (1 : ℚ)).normalize_eq_self, two_nsmul, Multiset.singleton_add]
  have hc : IsCircleFactor (X - C (1 : ℚ)) := by
    intro z hz
    rw [Polynomial.map_sub, map_X, Polynomial.map_C, roots_X_sub_C, Multiset.mem_singleton] at hz
    rw [hz, map_one, norm_one]
  unfold circleCount
  rw [hN, Multiset.filter_cons_of_pos (p := IsCircleFactor) _ hc, Multiset.filter_singleton,
    ite_eq_left hc, Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
    Multiset.sum_singleton, natDegree_X_sub_C]
  rfl

/-- On `ℤ²`, every scheme of the Jordan matrix has `H = 0`. -/
theorem jordan_finrank (S : InvariantCPS (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) :
    finrank ℝ S.E = 2 := by
  have hact : ∀ v : Fin 2 → ℝ,
      act (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) v = ![v 0 + v 1, v 1] := by
    intro v
    ext i
    fin_cases i <;> simp [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have he₀ : (Pi.single 0 1 : Fin 2 → ℝ) ∈ intLattice (Fin 2) :=
    Submodule.subset_span ⟨0, by simp⟩
  have hH : S.H = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hne
    have he : (Pi.single 0 1 : Fin 2 → ℝ) ∈ S.H := by
      by_cases h1 : v 1 = 0
      · have h0 : v 0 ≠ 0 := by
          intro h0
          apply hne
          ext i
          fin_cases i <;> simp [h0, h1]
        have : (Pi.single 0 1 : Fin 2 → ℝ) = (v 0)⁻¹ • v := by
          ext i
          fin_cases i <;> simp [h1, h0]
        rw [this]
        exact S.H.smul_mem _ hv
      · have hw : act (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) v - v ∈ S.H :=
          S.H.sub_mem (S.mapsTo_H v hv) hv
        have : (Pi.single 0 1 : Fin 2 → ℝ) =
            (v 1)⁻¹ • (act (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) v - v) := by
          ext i
          fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail, hact, h1]
        rw [this]
        exact S.H.smul_mem _ hw
    have h := congrFun (S.inj _ he₀ he) 0
    simp at h
  have hsum := Submodule.finrank_add_eq_of_isCompl S.isCompl
  rw [hH, finrank_bot, add_zero, Module.finrank_fin_fun] at hsum
  exact hsum

/-- The scheme `E = ℝ(1, √2)`, `H = ℝ(1, −√2)` for the identity on `ℤ²`. -/
theorem one_mem_physDims_one_of
    (hdense : ∀ (E H : Submodule ℝ (Fin 2 → ℝ)) (hc : IsCompl E H),
      (∀ f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ, (∀ γ ∈ intLattice (Fin 2), ∃ n : ℤ, f γ = n) →
        (∀ v ∈ E, f v = 0) → f = 0) →
      (H : Set (Fin 2 → ℝ)) ⊆
        closure (H.projection E hc.symm '' (intLattice (Fin 2) : Set (Fin 2 → ℝ))))
    (hlat : ∀ {v : Fin 2 → ℝ}, v ∈ intLattice (Fin 2) ↔ ∃ n : Fin 2 → ℤ, v = fun i => (n i : ℝ)) :
    1 ∈ physDims (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hs : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hs0 : Real.sqrt 2 ≠ 0 := hs.ne_zero
  set s : ℝ := Real.sqrt 2 with hsdef
  set u : Fin 2 → ℝ := ![1, s] with hudef
  set u' : Fin 2 → ℝ := ![1, -s] with hu'def
  have hc : IsCompl (ℝ ∙ u) (ℝ ∙ u') := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hvE hvH
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvE
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hvH
      have h0 := congrFun hb 0
      have h1 := congrFun hb 1
      simp only [hudef, hu'def, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one] at h0 h1
      have ha : a * s = 0 := by linear_combination (-1 / 2 : ℝ) * h1 - (s / 2) * h0
      rw [(mul_eq_zero.mp ha).resolve_right hs0, zero_smul]
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro v
      rw [Submodule.mem_sup]
      refine ⟨((v 0 + v 1 / s) / 2) • u, Submodule.mem_span_singleton.mpr ⟨_, rfl⟩,
        ((v 0 - v 1 / s) / 2) • u', Submodule.mem_span_singleton.mpr ⟨_, rfl⟩, ?_⟩
      ext i
      fin_cases i
      · simp [hudef, hu'def]
        ring
      · simp [hudef, hu'def]
        field_simp
        ring
  have hinj : ∀ γ ∈ intLattice (Fin 2), γ ∈ (ℝ ∙ u') → γ = 0 := by
    intro γ hγ hγH
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hγH
    obtain ⟨n, hn⟩ := hlat.mp hγ
    have h0 := congrFun hn 0
    have h1 := congrFun hn 1
    simp only [hu'def, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one] at h0 h1
    have hb : b = 0 := by
      by_contra hb0
      have hn0 : n 0 ≠ 0 := by
        intro h
        apply hb0
        rw [h0, h, Int.cast_zero]
      have : s * (n 0 : ℝ) = -(n 1 : ℝ) := by rw [← h0, ← h1]; ring
      exact (hs.mul_intCast hn0).ne_int (-(n 1)) (by push_cast; linarith)
    rw [hb, zero_smul]
  have hdn := hdense (ℝ ∙ u) (ℝ ∙ u') hc (by
    intro f hf hfE
    obtain ⟨m, hm⟩ := hf (Pi.single 0 1) (Submodule.subset_span ⟨0, by simp⟩)
    obtain ⟨n, hn⟩ := hf (Pi.single 1 1) (Submodule.subset_span ⟨1, by simp⟩)
    have hu : u = Pi.single 0 1 + s • Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp [hudef]
    have hfu : f u = 0 := hfE u (Submodule.mem_span_singleton_self u)
    rw [hu, map_add, map_smul, hm, hn, smul_eq_mul] at hfu
    have hn0 : n = 0 := by
      by_contra hn0
      have : s * (n : ℝ) = -(m : ℝ) := by linarith
      exact (hs.mul_intCast hn0).ne_int (-m) (by push_cast; linarith)
    have hm0 : m = 0 := by
      rw [hn0, Int.cast_zero, mul_zero, add_zero] at hfu
      exact_mod_cast hfu
    apply (Pi.basisFun ℝ (Fin 2)).ext
    intro i
    fin_cases i
    · simp [hm, hm0]
    · simp [hn, hn0])
  have hact1 : act (1 : Matrix (Fin 2) (Fin 2) ℤ) = LinearMap.id := by
    simp [act]
  let S : InvariantCPS (1 : Matrix (Fin 2) (Fin 2) ℤ) :=
    { E := ℝ ∙ u, H := ℝ ∙ u', isCompl := hc,
      mapsTo_E := fun v hv => by rw [hact1]; exact hv,
      mapsTo_H := fun v hv => by rw [hact1]; exact hv,
      inj := hinj, dense := hdn }
  refine ⟨S, ⟨Metric.closedBall 0 1 ∩ ((ℝ ∙ u' : Submodule ℝ (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)),
    ⟨Set.inter_subset_right, Metric.isBounded_closedBall.subset Set.inter_subset_left,
      0, Submodule.zero_mem _, 1, one_pos,
      Set.inter_subset_inter_left _ Metric.ball_subset_closedBall⟩, ?_⟩, ?_⟩
  · intro x hx
    rw [hact1]
    exact hx
  · refine finrank_span_singleton ?_
    intro h
    have := congrFun h 0
    simp [hudef] at this

theorem squarefree_hypothesis_needed_of (hI : 1 ∈ physDims (1 : Matrix (Fin 2) (Fin 2) ℤ))
    (hJ : 2 ∈ physDims (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) :
    (1 : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    unstableCount (1 : Matrix (Fin 2) (Fin 2) ℤ) + circleCount (1 : Matrix (Fin 2) (Fin 2) ℤ) =
      2 ∧
    IsLeast (physDims (1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 ∧
    IsLeast (physDims (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) 2 := by
  refine ⟨charpoly_one_two, charpoly_jordan, by rw [unstableCount_one_two, circleCount_one_two],
    ⟨hI, ?_⟩, ⟨hJ, ?_⟩⟩
  · rintro d ⟨S, -, rfl⟩
    exact one_le_finrank_E S
  · rintro d ⟨S, -, rfl⟩
    exact (jordan_finrank S).symm.le

end Plane

end DimOne

/-! ### The compared statements -/

/-- **(5)** `d(A) = 1` if and only if `χ_A` is irreducible with exactly one root of modulus `> 1`,
or `A = ±1` on `ℤ¹`; in the irreducible case that root is real, all other roots lie in the closed
unit disk, and every admissible scheme with `dim E = 1` has `E` the eigenline of that root. -/
theorem dimension_one_pisot_or_salem {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (hdet : A.det ≠ 0) (hsf : Squarefree (charpolyQ A)) :
    (IsLeast (physDims A) 1 ↔
      (Irreducible (charpolyQ A) ∧ unstableCount A = 1) ∨
        (Fintype.card ι = 1 ∧ (A = 1 ∨ A = -1))) ∧
    (Irreducible (charpolyQ A) → unstableCount A = 1 →
      ∃ r : ℝ, 1 < |r| ∧ (r : ℂ) ∈ eigenvalues A ∧ (∀ z ∈ eigenvalues A, z ≠ r → ‖z‖ ≤ 1) ∧
        ∀ S : InvariantCPS A, S.Admissible → finrank ℝ S.E = 1 →
          S.E = LinearMap.ker (act A - r • LinearMap.id)) :=
  ⟨DimOne.dimension_one_iff_of hdet (isLeast_physDims_squarefree A hdet hsf)
      (fun _ hp hc => exists_expanding_root A hdet hp hc),
    fun _ hU => DimOne.eigenline_of hU
      (fun _ _ hc hE hH => ⟨(normal_form A hsf hc hE hH).1, (normal_form A hsf hc hE hH).2.1⟩)
      (fun S hS => roots_restrict_H_le_one S hS)⟩

/-- **(6)** All roots on the unit circle: the factors are cyclotomic and `d(A)` counts `1` for a
factor of degree one and `2` for each other factor; `χ_A = Φ_n`, `n ≥ 3`, gives `d(A) = 2`. -/
theorem finite_order_case {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) :
    (Squarefree (charpolyQ A) → (∀ z ∈ eigenvalues A, ‖z‖ = 1) →
      (∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
        ∃ n : ℕ, 0 < n ∧ p = cyclotomic n ℚ) ∧
      IsLeast (physDims A)
        (((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).map
          (fun p => min p.natDegree 2)).sum)) ∧
    ∀ n : ℕ, 3 ≤ n → A.charpoly = cyclotomic n ℤ → IsLeast (physDims A) 2 :=
  ⟨fun hsf h => DimOne.finite_order_of
      (fun hdet hsf' => isLeast_physDims_squarefree A hdet hsf')
      (fun _ hp => isCircleFactor_iff_cyclotomic A hp) hsf h,
    fun _ hn hχ => DimOne.cyclotomic_of
      (fun hdet hsf' => isLeast_physDims_squarefree A hdet hsf')
      (fun _ hp => isCircleFactor_iff_cyclotomic A hp) hn hχ⟩

/-- **(7)** On `ℤ²`, `I₂` and `[[1, 1], [0, 1]]` share `χ = (x − 1)²`, for which the count of (3)
gives `2`, but their least physical dimensions are `1` and `2`. -/
theorem squarefree_hypothesis_needed :
    (1 : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).charpoly = (X - 1) ^ 2 ∧
    unstableCount (1 : Matrix (Fin 2) (Fin 2) ℤ) + circleCount (1 : Matrix (Fin 2) (Fin 2) ℤ) =
      2 ∧
    IsLeast (physDims (1 : Matrix (Fin 2) (Fin 2) ℤ)) 1 ∧
    IsLeast (physDims (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) 2 :=
  DimOne.squarefree_hypothesis_needed_of
    (DimOne.one_mem_physDims_one_of (fun _ _ hc h => dense_of_no_integral_functional hc h)
      mem_intLattice_iff)
    ⟨InvariantCPS.trivial _, InvariantCPS.trivial_admissible _, by
      show finrank ℝ (⊤ : Submodule ℝ (Fin 2 → ℝ)) = 2
      simp⟩

/-- **(12)** The companion matrix of `x⁴ − x³ − x² − x + 1`: not hyperbolic, `d = 1`, attained only
on the eigenline of the root in `(1.7220, 1.7221)`. -/
theorem salem_witness :
    CSalem.charpoly = X ^ 4 - X ^ 3 - X ^ 2 - X + 1 ∧ ¬ IsHyperbolic CSalem ∧
    IsLeast (physDims CSalem) 1 ∧
    ∃ r : ℝ, (1.7220 : ℝ) < r ∧ r < 1.7221 ∧ (r : ℂ) ∈ eigenvalues CSalem ∧
      ∀ S : InvariantCPS CSalem, S.Admissible → finrank ℝ S.E = 1 →
        S.E = LinearMap.ker (act CSalem - r • LinearMap.id) := by
  obtain ⟨r, h1, h2, hrmem, hU, hnh⟩ := DimOne.salem_spectrum
  have hdet : CSalem.det ≠ 0 := by rw [DimOne.det_CSalem]; exact one_ne_zero
  have hirr := DimOne.irreducible_charpolyQ_CSalem
  obtain ⟨h5a, h5b⟩ := dimension_one_pisot_or_salem CSalem hdet hirr.squarefree
  refine ⟨DimOne.charpoly_CSalem, hnh, h5a.mpr (Or.inl ⟨hirr, hU⟩), r, h1, h2, hrmem, ?_⟩
  obtain ⟨r', -, -, hr'le, hr'E⟩ := h5b hirr hU
  have hrr : r = r' := by
    by_contra hne
    have h := hr'le (r : ℂ) hrmem (by exact_mod_cast hne)
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h
    linarith
  rw [hrr]
  exact hr'E

end

end InflationDimension
