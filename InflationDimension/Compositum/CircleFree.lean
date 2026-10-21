module
public import Mathlib

@[expose] public section
/-!
# Circle-freeness of a degree-12 field containing roots of `x³ − x − 1` and `x⁴ − x − 1`

Ported from the author's registered entry PALOMAR-2026-10-21-000012
(stalex444/pdt-hermite-signature-compositum@5aa870e98236ba240561b798265c629df8c2d031),
`HermiteCompositum/Extras.lean` (the discriminant transport lemmas `discr_eq_index_sq_mul_discr`,
`discr_map_of_monic`, `discr_minpoly_eq_discr_powerBasis`, `discr_int_eq_discr_rat`,
`discr_pow_eq_discr_minpoly`, and the declarations from `monic_natDegree_two_eq` through
`circle_free`) and `HermiteCompositum/Defs.lean` (the definition `RootRigid`); changes: only these
declarations are kept (the ruler-polynomial and Mahler-measure material is omitted), the section
headers no longer carry that entry's statement numbers, `RootRigid` is defined here, and the
declarations are in the namespace `InflationDimension.Compositum`, so that no declaration name of
that entry is declared again. Proofs and statements are unchanged.

For a number field `L` with `[L : ℚ] = 12` containing a root `ρ` of `x³ − x − 1` and a root `Q`
of `x⁴ − x − 1`: every intermediate field is `⊥`, `ℚ⟮ρ⟯`, `ℚ⟮Q⟯` or `⊤` (`subfield_lattice`); no
irreducible polynomial over `ℚ` has two distinct roots in `L` (`rootRigid_of_roots`); hence the
only elements with a complex embedding of modulus `1` are `±1` (`circle_free`).
-/

open Polynomial Module Matrix

namespace InflationDimension.Compositum

set_option linter.unusedSimpArgs false

/-- **Root-rigidity**: no irreducible polynomial over `ℚ` has two distinct roots in `L`
(in particular, every subfield of `L` has trivial automorphism group over `ℚ`). -/
def RootRigid (L : Type*) [Field L] [Algebra ℚ L] : Prop :=
  ∀ α β : L, minpoly ℚ α = minpoly ℚ β → α = β


/-- discr of a linearly independent family = (index of its span)² · discr of a basis. -/
theorem discr_eq_index_sq_mul_discr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Type*} [CommRing B] (b : Basis ι ℤ B) (v : ι → B) (hv : LinearIndependent ℤ v) :
    Algebra.discr ℤ v =
      ((Submodule.span ℤ (Set.range v)).toAddSubgroup.index : ℤ) ^ 2 * Algebra.discr ℤ b := by
  obtain ⟨bN, hbN⟩ : ∃ bN : Basis ι ℤ (Submodule.span ℤ (Set.range v)).toAddSubgroup,
      ∀ i, (bN i : B) = v i :=
    ⟨Basis.span hv, fun i => Basis.coe_span_apply hv i⟩
  have hidx := AddSubgroup.index_eq_natAbs_det b (Submodule.span ℤ (Set.range v)).toAddSubgroup bN
  have hv' : v = b ᵥ* ((b.toMatrix v).map (algebraMap ℤ B)) := (b.toMatrix_map_vecMul v).symm
  rw [hidx, Int.natCast_natAbs, sq_abs, Basis.det_apply]
  conv_lhs => rw [hv']
  rw [Algebra.discr_of_matrix_vecMul]
  congr 3
  ext i j
  simp [Basis.toMatrix_apply, hbN]

/-! ### The link: discriminant of the minimal polynomial = discriminant of the power basis -/

/-- `Polynomial.discr` commutes with `Polynomial.map` for monic polynomials of positive degree. -/
theorem discr_map_of_monic {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (φ : R →+* S) {f : R[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  have hdeg' : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hdeg
  have hmap : 0 < (f.map φ).degree := by
    rw [degree_eq_natDegree (hf.map φ).ne_zero, hf.natDegree_map φ]
    exact_mod_cast hdeg
  have h1 := resultant_deriv hdeg'
  have h2 := resultant_deriv hmap
  rw [hf.leadingCoeff, mul_one] at h1
  rw [(hf.map φ).leadingCoeff, mul_one, hf.natDegree_map φ, derivative_map, resultant_map_map,
    h1] at h2
  -- h2 : φ ((-1) ^ e * f.discr) = (-1) ^ e * (f.map φ).discr
  rw [map_mul, map_pow, map_neg, map_one] at h2
  have hsq : ((-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
      ((-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc (f.map φ).discr
      = ((-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2)) * (f.map φ).discr := by
        rw [hsq, one_mul]
    _ = (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          ((-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * (f.map φ).discr) := by ring
    _ = (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          ((-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * φ f.discr) := by rw [← h2]
    _ = φ f.discr := by rw [← mul_assoc, hsq, one_mul]

/-- **The discriminant of the minimal polynomial of a power-basis generator equals the
discriminant of the power basis.** -/
theorem discr_minpoly_eq_discr_powerBasis {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (pb : PowerBasis K L) :
    (minpoly K pb.gen).discr = Algebra.discr K pb.basis := by
  classical
  set f := minpoly K pb.gen with hf
  have hint : IsIntegral K pb.gen := pb.isIntegral_gen
  have hmon : f.Monic := minpoly.monic hint
  have hn : f.natDegree = pb.dim := pb.natDegree_minpoly
  have hpos : 0 < f.degree := minpoly.degree_pos hint
  rw [Algebra.discr_powerBasis_eq_norm, pb.finrank]
  have hres := resultant_deriv hpos
  rw [hmon.leadingCoeff, mul_one] at hres
  -- the key identity: the resultant of `f` and `f'` is the norm of `f'(θ)`
  have key : resultant f f.derivative f.natDegree (f.natDegree - 1) =
      Algebra.norm K (aeval pb.gen f.derivative) := by
    let E := AlgebraicClosure L
    apply (algebraMap K E).injective
    rw [← resultant_map_map, Algebra.norm_eq_prod_embeddings]
    have hg : (f.derivative.map (algebraMap K E)).natDegree ≤ f.natDegree - 1 :=
      natDegree_map_le.trans (natDegree_derivative_le f)
    have hprod := resultant_eq_prod_eval (f.map (algebraMap K E))
      (f.derivative.map (algebraMap K E)) (f.natDegree - 1) hg (IsAlgClosed.splits _)
    rw [natDegree_map, (hmon.map _).leadingCoeff, one_pow, one_mul] at hprod
    rw [hprod]
    simp_rw [← aeval_algHom_apply, ← eval_map_algebraMap]
    have hnodup : (f.aroots E).Nodup :=
      nodup_roots (Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
    set g : E → E := fun y => (f.derivative.map (algebraMap K E)).eval y with hg_def
    calc ((f.map (algebraMap K E)).roots.map g).prod
        = ((f.aroots E).map g).prod := rfl
      _ = ∏ y ∈ (f.aroots E).toFinset, g y := by
          rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]
      _ = ∏ y : {y // y ∈ f.aroots E}, g y :=
          Finset.prod_subtype _ (fun y => Multiset.mem_toFinset) g
      _ = ∏ σ : L →ₐ[K] E, g (σ pb.gen) :=
          (Fintype.prod_equiv pb.liftEquiv' _ _ (fun σ => rfl)).symm
  rw [key] at hres
  have hsq : ((-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
      ((-1 : K) ^ (f.natDegree * (f.natDegree - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [hn] at hres hsq
  calc f.discr
      = ((-1 : K) ^ (pb.dim * (pb.dim - 1) / 2) * (-1 : K) ^ (pb.dim * (pb.dim - 1) / 2)) *
          f.discr := by rw [hsq, one_mul]
    _ = (-1 : K) ^ (pb.dim * (pb.dim - 1) / 2) *
          ((-1 : K) ^ (pb.dim * (pb.dim - 1) / 2) * f.discr) := by ring
    _ = (-1 : K) ^ (pb.dim * (pb.dim - 1) / 2) * Algebra.norm K (aeval pb.gen f.derivative) := by
          rw [hres]

/-! ### Transfer `ℤ → ℚ` and the power family of a generator -/

/-- The `ℤ`-discriminant of a family in `𝓞 L`, cast to `ℚ`, is the `ℚ`-discriminant of the
family in `L`. -/
theorem discr_int_eq_discr_rat {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ι → NumberField.RingOfIntegers L) :
    (Algebra.discr ℤ v : ℚ) =
      Algebra.discr ℚ (fun i => algebraMap (NumberField.RingOfIntegers L) L (v i)) := by
  rw [Algebra.discr_def, Algebra.discr_def, ← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply]
  have h := Algebra.trace_localization ℤ (nonZeroDivisors ℤ) (Rₘ := ℚ) (Sₘ := L) (v i * v j)
  rw [map_mul] at h
  exact h.symm

/-- For `θ ∈ L` of degree `[L : ℚ]`, the `ℚ`-discriminant of the power family `θ^i` is the
discriminant of its minimal polynomial. -/
theorem discr_pow_eq_discr_minpoly {L : Type*} [Field L] [NumberField L] (θ : L) (n : ℕ)
    (hrank : Module.finrank ℚ L = n) (hdeg : (minpoly ℚ θ).natDegree = n) :
    Algebra.discr ℚ (fun i : Fin n => θ ^ (i : ℕ)) = (minpoly ℚ θ).discr := by
  have hint : IsIntegral ℚ θ := Algebra.IsIntegral.isIntegral θ
  let pb₀ := Algebra.adjoin.powerBasis hint
  have hdim₀ : pb₀.dim = n := by
    simpa [pb₀, Algebra.adjoin.powerBasis] using hdeg
  have htop : Algebra.adjoin ℚ {θ} = ⊤ := by
    apply Subalgebra.toSubmodule_injective
    rw [Algebra.top_toSubmodule]
    apply Submodule.eq_top_of_finrank_eq
    rw [Subalgebra.finrank_toSubmodule, pb₀.finrank, hdim₀, hrank]
  let e : Algebra.adjoin ℚ {θ} ≃ₐ[ℚ] L :=
    (Subalgebra.equivOfEq _ _ htop).trans Subalgebra.topEquiv
  let pb := pb₀.map e
  have hgen : pb.gen = θ := by
    simp [pb, pb₀, e, Algebra.adjoin.powerBasis_gen]
  have hdim : pb.dim = n := hdim₀
  have h1 := discr_minpoly_eq_discr_powerBasis pb
  rw [hgen] at h1
  rw [h1, ← Algebra.discr_reindex ℚ pb.basis (finCongr hdim)]
  congr 1
  funext i
  simp [PowerBasis.coe_basis, hgen]

open IntermediateField

/-! ### No quadratic subfield -/

/-- A monic polynomial of `natDegree 2` is `X² + c₁ X + c₀`. -/
theorem monic_natDegree_two_eq {F : Type*} [Field F] {p : F[X]} (hm : p.Monic)
    (hd : p.natDegree = 2) : p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext n
  simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · have := hm.coeff_natDegree
    rw [hd] at this
    simp [this]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- If `X⁴ − X − 1` splits into two monic quadratics `(X² + aX + b)(X² + cX + d)` over a field,
then `a²` is a root of the resolvent cubic `y³ + 4y − 1`. -/
theorem quartic_factor_resolvent {F : Type*} [Field F] (a b c d : F)
    (h : (X ^ 2 + C a * X + C b) * (X ^ 2 + C c * X + C d) = (X ^ 4 - X - 1 : F[X])) :
    (a ^ 2) ^ 3 + 4 * a ^ 2 - 1 = 0 := by
  have h' : (X ^ 4 + C (a + c) * X ^ 3 + C (b + d + a * c) * X ^ 2 + C (a * d + b * c) * X
      + C (b * d) : F[X]) = X ^ 4 - X - 1 := by
    rw [← h]; simp only [map_add, map_mul]; ring
  have e3 := congrArg (fun p : F[X] => p.coeff 3) h'
  have e2 := congrArg (fun p : F[X] => p.coeff 2) h'
  have e1 := congrArg (fun p : F[X] => p.coeff 1) h'
  have e0 := congrArg (fun p : F[X] => p.coeff 0) h'
  simp only [coeff_add, coeff_sub, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_X_pow,
    coeff_X, coeff_one] at e3 e2 e1 e0
  norm_num at e3 e2 e1 e0
  have hc : c = -a := by linear_combination e3
  subst hc
  linear_combination (-(a ^ 2) * (b + d + a ^ 2)) * e2 + (a * (d - b) - 1) * e1
    + (4 * a ^ 2) * e0

/-- The resolvent cubic of `X⁴ − X − 1`: `X³ + 4X − 1`. -/
noncomputable def resolventCubic : ℚ[X] := X ^ 3 + 4 * X - 1

theorem resolventCubic_natDegree : resolventCubic.natDegree = 3 := by
  unfold resolventCubic; compute_degree!

theorem resolventCubic_monic : resolventCubic.Monic := by
  unfold resolventCubic; monicity!

/-- `X³ + 4X − 1` is irreducible over `ℚ` (rational root theorem: an integer root divides 1). -/
theorem resolventCubic_irreducible : Irreducible resolventCubic := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [resolventCubic_natDegree]; decide
  · intro x hx
    have hx' : x ^ 3 + 4 * x - 1 = 0 := by simpa [resolventCubic] using hx
    have hint : aeval x (X ^ 3 + 4 * X - 1 : ℤ[X]) = 0 := by
      simp only [map_sub, map_add, map_mul, map_pow, aeval_X, map_ofNat, map_one]
      exact hx'
    obtain ⟨r, hr, hdvd⟩ := exists_integer_of_is_root_of_monic (by monicity!) hint
    have h1 : r ∣ 1 := by
      have : (X ^ 3 + 4 * X - 1 : ℤ[X]).coeff 0 = -1 := by
        simp [coeff_X_pow, coeff_X, coeff_one]
      rw [this] at hdvd
      exact (dvd_neg).mp hdvd
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one h1) with rfl | rfl <;>
      · rw [hr] at hx'; norm_num at hx'

theorem X_pow_four_sub_X_sub_one_irreducible : Irreducible (X ^ 4 - X - 1 : ℚ[X]) :=
  X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

theorem X_pow_four_sub_X_sub_one_natDegree {F : Type*} [Field F] :
    (X ^ 4 - X - 1 : F[X]).natDegree = 4 := by compute_degree!

theorem X_pow_four_sub_X_sub_one_monic {F : Type*} [Field F] :
    (X ^ 4 - X - 1 : F[X]).Monic := by monicity!

/-- A root of `x⁴ − x − 1` in any `ℚ`-algebra field has minimal polynomial `X⁴ − X − 1`. -/
theorem minpoly_quartic_root {L : Type*} [Field L] [Algebra ℚ L] (x : L)
    (hx : x ^ 4 - x - 1 = 0) : minpoly ℚ x = X ^ 4 - X - 1 := by
  symm
  apply minpoly.eq_of_irreducible_of_monic X_pow_four_sub_X_sub_one_irreducible
  · simp [hx]
  · monicity!

theorem isIntegral_quartic_root {L : Type*} [Field L] [Algebra ℚ L] (x : L)
    (hx : x ^ 4 - x - 1 = 0) : IsIntegral ℚ x :=
  ⟨X ^ 4 - X - 1, by monicity!, by simp [hx]⟩

theorem finrank_adjoin_quartic_root {L : Type*} [Field L] [Algebra ℚ L] (x : L)
    (hx : x ^ 4 - x - 1 = 0) : finrank ℚ ℚ⟮x⟯ = 4 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_quartic_root x hx), minpoly_quartic_root x hx]
  compute_degree!

/-- A root of the resolvent cubic `y³ + 4y − 1` has minimal polynomial `resolventCubic`. -/
theorem minpoly_resolvent_root {L : Type*} [Field L] [Algebra ℚ L] (y : L)
    (hy : y ^ 3 + 4 * y - 1 = 0) : minpoly ℚ y = resolventCubic := by
  symm
  apply minpoly.eq_of_irreducible_of_monic resolventCubic_irreducible
  · simp [resolventCubic, hy, map_ofNat]
  · exact resolventCubic_monic

theorem isIntegral_resolvent_root {L : Type*} [Field L] [Algebra ℚ L] (y : L)
    (hy : y ^ 3 + 4 * y - 1 = 0) : IsIntegral ℚ y :=
  ⟨X ^ 3 + 4 * X - 1, by monicity!, by simp [hy]⟩

theorem finrank_adjoin_resolvent_root {L : Type*} [Field L] [Algebra ℚ L] (y : L)
    (hy : y ^ 3 + 4 * y - 1 = 0) : finrank ℚ ℚ⟮y⟯ = 3 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_resolvent_root y hy), minpoly_resolvent_root y hy,
    resolventCubic_natDegree]

/-- **No quadratic subfield.** A field `L` of degree 12 over `ℚ` containing a root `Q` of
`x⁴ − x − 1` has no subfield of degree 2. (The root `ρ` of `x³ − x − 1` is not needed.) -/
theorem no_quadratic_subfield {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (Q : L) (hQ : Q ^ 4 - Q - 1 = 0) (F : IntermediateField ℚ L) : finrank ℚ F ≠ 2 := by
  intro hF
  have htower : finrank ℚ F * finrank F L = finrank ℚ L := Module.finrank_mul_finrank ℚ F L
  have hFL : finrank F L = 6 := by rw [hF, hL] at htower; omega
  have hintF : IsIntegral F Q := Algebra.IsIntegral.isIntegral Q
  have hpdvd : minpoly F Q ∣ (X ^ 4 - X - 1 : F[X]) := minpoly.dvd F Q (by simp [hQ])
  have hdeg_le : (minpoly F Q).natDegree ≤ 4 := by
    have := natDegree_le_of_dvd hpdvd X_pow_four_sub_X_sub_one_monic.ne_zero
    rwa [X_pow_four_sub_X_sub_one_natDegree] at this
  have hdvd6 : (minpoly F Q).natDegree ∣ 6 := by
    have h := IntermediateField.finrank_dvd_of_le_right (le_top : F⟮Q⟯ ≤ ⊤)
    rwa [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hintF, hFL] at h
  have hpos : 0 < (minpoly F Q).natDegree := minpoly.natDegree_pos hintF
  -- a subfield generated by a root of the quartic or the resolvent cubic cannot sit inside `F`
  have hnoQ : ∀ x : L, x ^ 4 - x - 1 = 0 → x ∈ F → False := by
    intro x hx hxF
    have h4 := IntermediateField.finrank_dvd_of_le_right (IntermediateField.adjoin_simple_le_iff.mpr hxF)
    rw [finrank_adjoin_quartic_root x hx, hF] at h4
    norm_num at h4
  have hnoY : ∀ y : L, y ^ 3 + 4 * y - 1 = 0 → y ∈ F → False := by
    intro y hy hyF
    have h3 := IntermediateField.finrank_dvd_of_le_right (IntermediateField.adjoin_simple_le_iff.mpr hyF)
    rw [finrank_adjoin_resolvent_root y hy, hF] at h3
    norm_num at h3
  obtain ⟨d, hd⟩ : ∃ d, (minpoly F Q).natDegree = d := ⟨_, rfl⟩
  rw [hd] at hdeg_le hdvd6 hpos
  have hd6 : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  interval_cases d
  · -- degree 1: `Q ∈ F`
    obtain ⟨y, hy⟩ := minpoly.natDegree_eq_one_iff.mp hd
    exact hnoQ Q hQ (hy ▸ y.2)
  · -- degree 2: the quadratic factorization, hence a root of the resolvent cubic in `F`
    obtain ⟨q, hq⟩ := hpdvd
    have hqm : q.Monic := (minpoly.monic hintF).of_mul_monic_left (hq ▸ X_pow_four_sub_X_sub_one_monic)
    have hqd : q.natDegree = 2 := by
      have := Polynomial.Monic.natDegree_mul (minpoly.monic hintF) hqm
      rw [← hq, X_pow_four_sub_X_sub_one_natDegree, hd] at this
      omega
    have hres := quartic_factor_resolvent ((minpoly F Q).coeff 1) ((minpoly F Q).coeff 0)
      (q.coeff 1) (q.coeff 0)
      (by rw [← monic_natDegree_two_eq (minpoly.monic hintF) hd, ← monic_natDegree_two_eq hqm hqd]
          exact hq.symm)
    set a : F := (minpoly F Q).coeff 1
    refine hnoY ((a : L) ^ 2) ?_ (pow_mem a.2 2)
    have : (((a ^ 2) ^ 3 + 4 * a ^ 2 - 1 : F) : L) = 0 := by rw [hres]; simp
    push_cast at this
    exact this
  · -- degree 3: a linear cofactor, hence a root of the quartic in `F`
    obtain ⟨q, hq⟩ := hpdvd
    have hqm : q.Monic := (minpoly.monic hintF).of_mul_monic_left (hq ▸ X_pow_four_sub_X_sub_one_monic)
    have hqd : q.natDegree = 1 := by
      have := Polynomial.Monic.natDegree_mul (minpoly.monic hintF) hqm
      rw [← hq, X_pow_four_sub_X_sub_one_natDegree, hd] at this
      omega
    obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one (by rw [degree_eq_natDegree hqm.ne_zero, hqd]; rfl)
    have hr' : (X ^ 4 - X - 1 : F[X]).IsRoot r := hr.dvd (Dvd.intro_left _ hq.symm)
    have hr4 : r ^ 4 - r - 1 = 0 := by simpa using hr'
    refine hnoQ (r : L) ?_ r.2
    have : ((r ^ 4 - r - 1 : F) : L) = 0 := by rw [hr4]; simp
    push_cast at this
    exact this
  · -- degree 4 does not divide 6
    norm_num at hdvd6

/-! ### Circle-free, conditional on root-rigidity -/

/-- If a complex embedding sends `α` to the unit circle then `α⁻¹` is a conjugate of `α`. -/
theorem minpoly_inv_eq_of_norm_eq_one {L : Type*} [Field L] [NumberField L]
    (σ : L →+* ℂ) (α : L) (hα : ‖σ α‖ = 1) : minpoly ℚ α⁻¹ = minpoly ℚ α := by
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  symm
  apply minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) _ (minpoly.monic hint)
  apply σ.injective
  rw [map_zero, ← RingHom.toRatAlgHom_apply, ← aeval_algHom_apply, RingHom.toRatAlgHom_apply,
    map_inv₀, Complex.inv_eq_conj hα]
  have h1 : aeval (σ α) (minpoly ℚ α) = 0 := by
    rw [← RingHom.toRatAlgHom_apply, aeval_algHom_apply, minpoly.aeval, map_zero]
  have h2 : aeval ((starRingEnd ℂ) (σ α)) (minpoly ℚ α) =
      (starRingEnd ℂ).toRatAlgHom (aeval (σ α) (minpoly ℚ α)) := by
    rw [← aeval_algHom_apply, RingHom.toRatAlgHom_apply]
  rw [h2, h1, map_zero]

/-- **Circle-free.** In a root-rigid number field, the only elements with a complex embedding
of modulus `1` are `±1`. In particular such a field contains no Salem number. -/
theorem circle_free_of_rootRigid {L : Type*} [Field L] [NumberField L] (hrig : RootRigid L)
    (α : L) (σ : L →+* ℂ) (hα : ‖σ α‖ = 1) : α = 1 ∨ α = -1 := by
  have hα0 : α ≠ 0 := by rintro rfl; simp at hα
  have h := hrig α⁻¹ α (minpoly_inv_eq_of_norm_eq_one σ α hα)
  have : α * α = 1 := by
    nth_rewrite 2 [← h]
    exact mul_inv_cancel₀ hα0
  exact mul_self_eq_one_iff.mp this


/-! ### The field discriminant divides every integral power-family discriminant -/

/-- For `θ ∈ 𝓞 K` with `n = [K : ℚ]`, the field discriminant divides the `ℚ`-discriminant of
`1, θ, …, θⁿ⁻¹` whenever the latter is the integer `a`. -/
theorem discr_dvd_discr_pow {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (hK : finrank ℚ K = n) (θ : NumberField.RingOfIntegers K) (a : ℤ)
    (ha : Algebra.discr ℚ
      (fun i : Fin n => (algebraMap (NumberField.RingOfIntegers K) K θ) ^ (i : ℕ)) = a) :
    NumberField.discr K ∣ a := by
  classical
  have hZ : Algebra.discr ℤ (fun i : Fin n => θ ^ (i : ℕ)) = a := by
    apply Int.cast_injective (α := ℚ)
    rw [discr_int_eq_discr_rat]
    simp only [map_pow]
    exact ha
  by_cases hlin : LinearIndependent ℤ (fun i : Fin n => θ ^ (i : ℕ))
  · have hcard :
        Fintype.card (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) = n := by
      rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, hK]
    let b : Basis (Fin n) ℤ (NumberField.RingOfIntegers K) :=
      (NumberField.RingOfIntegers.basis K).reindex (Fintype.equivFinOfCardEq hcard)
    have h := discr_eq_index_sq_mul_discr b _ hlin
    rw [hZ, NumberField.discr_eq_discr K b] at h
    exact Dvd.intro_left _ h.symm
  · have := Algebra.discr_zero_of_not_linearIndependent (A := ℤ) hlin
    rw [hZ] at this
    rw [this]
    exact dvd_zero _

/-! ### The two cubic discriminants -/

theorem discr_cubic_int : (X ^ 3 - X - 1 : ℤ[X]).discr = -23 := by
  rw [discr_of_degree_eq_three (by compute_degree!)]
  simp [coeff_X_pow, coeff_X, coeff_one]

theorem discr_resolvent_int : (X ^ 3 + 4 * X - 1 : ℤ[X]).discr = -283 := by
  rw [discr_of_degree_eq_three (by compute_degree!)]
  simp [coeff_X_pow, coeff_X, coeff_one]

theorem discr_cubic_rat : (X ^ 3 - X - 1 : ℚ[X]).discr = -23 := by
  have hmap : (X ^ 3 - X - 1 : ℤ[X]).map (Int.castRingHom ℚ) = X ^ 3 - X - 1 := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  have hdeg : 0 < (X ^ 3 - X - 1 : ℤ[X]).natDegree := by
    rw [show (X ^ 3 - X - 1 : ℤ[X]).natDegree = 3 by compute_degree!]; norm_num
  rw [← hmap, discr_map_of_monic _ (by monicity!) hdeg, discr_cubic_int]
  simp

theorem resolventCubic_discr : resolventCubic.discr = -283 := by
  have hmap : (X ^ 3 + 4 * X - 1 : ℤ[X]).map (Int.castRingHom ℚ) = resolventCubic := by
    unfold resolventCubic
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]
  have hdeg : 0 < (X ^ 3 + 4 * X - 1 : ℤ[X]).natDegree := by
    rw [show (X ^ 3 + 4 * X - 1 : ℤ[X]).natDegree = 3 by compute_degree!]; norm_num
  rw [← hmap, discr_map_of_monic _ (by monicity!) hdeg, discr_resolvent_int]
  simp

theorem X_pow_three_sub_X_sub_one_irreducible : Irreducible (X ^ 3 - X - 1 : ℚ[X]) :=
  X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

theorem minpoly_cubic_root {L : Type*} [Field L] [Algebra ℚ L] (x : L)
    (hx : x ^ 3 - x - 1 = 0) : minpoly ℚ x = X ^ 3 - X - 1 := by
  symm
  apply minpoly.eq_of_irreducible_of_monic X_pow_three_sub_X_sub_one_irreducible
  · simp [hx]
  · monicity!

theorem isIntegral_cubic_root {L : Type*} [Field L] [Algebra ℚ L] (x : L)
    (hx : x ^ 3 - x - 1 = 0) : IsIntegral ℚ x :=
  ⟨X ^ 3 - X - 1, by monicity!, by simp [hx]⟩

theorem finrank_adjoin_cubic_root {L : Type*} [Field L] [Algebra ℚ L] (x : L)
    (hx : x ^ 3 - x - 1 = 0) : finrank ℚ ℚ⟮x⟯ = 3 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_cubic_root x hx), minpoly_cubic_root x hx]
  compute_degree!

/-- **Discriminant distinction.** A cubic number field cannot contain both a root of `x³ − x − 1`
and a root of `x³ + 4x − 1`: the power bases have discriminants `−23` and `−283`, both multiples of
`discr K`, forcing `|discr K| = 1`, against Hermite–Minkowski. -/
theorem no_cubic_field_with_both_roots {K : Type*} [Field K] [NumberField K]
    (hK : finrank ℚ K = 3) (ρ y : K) (hρ : ρ ^ 3 - ρ - 1 = 0) (hy : y ^ 3 + 4 * y - 1 = 0) :
    False := by
  have hρint : IsIntegral ℤ ρ := ⟨X ^ 3 - X - 1, by monicity!, by simp [hρ]⟩
  have hyint : IsIntegral ℤ y := ⟨X ^ 3 + 4 * X - 1, by monicity!, by simp [hy]⟩
  have hminρ : minpoly ℚ ρ = X ^ 3 - X - 1 := minpoly_cubic_root ρ hρ
  have hminy : minpoly ℚ y = resolventCubic := minpoly_resolvent_root y hy
  have h1 : NumberField.discr K ∣ -23 := by
    apply discr_dvd_discr_pow hK ⟨ρ, hρint⟩
    have e : algebraMap (NumberField.RingOfIntegers K) K ⟨ρ, hρint⟩ = ρ := rfl
    rw [e, discr_pow_eq_discr_minpoly ρ 3 hK (by rw [hminρ]; compute_degree!), hminρ,
      discr_cubic_rat]
    simp
  have h2 : NumberField.discr K ∣ -283 := by
    apply discr_dvd_discr_pow hK ⟨y, hyint⟩
    have e : algebraMap (NumberField.RingOfIntegers K) K ⟨y, hyint⟩ = y := rfl
    rw [e, discr_pow_eq_discr_minpoly y 3 hK (by rw [hminy, resolventCubic_natDegree]), hminy,
      resolventCubic_discr]
    simp
  have h3 : NumberField.discr K ∣ 1 := by
    have : (1 : ℤ) = (-10) * (-283) + 123 * (-23) := by norm_num
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)
  have habs := NumberField.abs_discr_gt_two (K := K) (by rw [hK]; norm_num)
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one h3) with h | h <;> rw [h] at habs <;> norm_num at habs

/-! ### Roots in subfields from degree data -/

/-- If a monic `p` divides a monic `g` with `g.natDegree = p.natDegree + 1`, then `g` has a root. -/
theorem exists_isRoot_of_dvd_natDegree_succ {F : Type*} [Field F] {p g : F[X]} (hp : p.Monic)
    (hg : g.Monic) (hdvd : p ∣ g) (hdeg : g.natDegree = p.natDegree + 1) : ∃ r : F, g.IsRoot r := by
  obtain ⟨q, hq⟩ := hdvd
  have hqm : q.Monic := hp.of_mul_monic_left (hq ▸ hg)
  have hqd : q.natDegree = 1 := by
    have := Polynomial.Monic.natDegree_mul hp hqm
    rw [← hq] at this; omega
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one
    (by rw [degree_eq_natDegree hqm.ne_zero, hqd]; rfl)
  exact ⟨r, hr.dvd (Dvd.intro_left _ hq.symm)⟩

/-- If `x ∈ L` is a root of a monic cubic `g ∈ ℚ[X]` and has degree `≤ 2` over an intermediate
field `K`, then `g` has a root in `K`. -/
theorem exists_root_mem_of_natDegree_le_two {L : Type*} [Field L] [NumberField L]
    (K : IntermediateField ℚ L) {g : ℚ[X]} (hg : g.Monic) (hg3 : g.natDegree = 3) (x : L)
    (hx : aeval x g = 0) (hdeg : (minpoly K x).natDegree ≤ 2) :
    ∃ r : L, aeval r g = 0 ∧ r ∈ K := by
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hdvd : minpoly K x ∣ g.map (algebraMap ℚ K) := minpoly.dvd K x (by rwa [aeval_map_algebraMap])
  have hpos := minpoly.natDegree_pos hint
  rcases Nat.lt_or_ge (minpoly K x).natDegree 2 with h | h
  · have h1 : (minpoly K x).natDegree = 1 := by omega
    obtain ⟨y, hy⟩ := minpoly.natDegree_eq_one_iff.mp h1
    exact ⟨x, hx, hy ▸ y.2⟩
  · have h2 : (minpoly K x).natDegree = 2 := by omega
    obtain ⟨r, hr⟩ := exists_isRoot_of_dvd_natDegree_succ (minpoly.monic hint) (hg.map _) hdvd
      (by rw [hg.natDegree_map, hg3, h2])
    refine ⟨r, ?_, r.2⟩
    have hr' : aeval r g = 0 := by rwa [IsRoot, eval_map_algebraMap] at hr
    have : aeval ((algebraMap K L) r) g = 0 := by rw [aeval_algebraMap_apply, hr', map_zero]
    exact this

/-- Degree-2 minimal polynomial of `Q` over a subfield `F` ⇒ the resolvent cubic has a root in `F`. -/
theorem exists_resolvent_root_mem {L : Type*} [Field L] [NumberField L] (Q : L)
    (hQ : Q ^ 4 - Q - 1 = 0) (F : IntermediateField ℚ L) (hd : (minpoly F Q).natDegree = 2) :
    ∃ y : L, y ^ 3 + 4 * y - 1 = 0 ∧ y ∈ F := by
  have hintF : IsIntegral F Q := Algebra.IsIntegral.isIntegral Q
  obtain ⟨q, hq⟩ : minpoly F Q ∣ (X ^ 4 - X - 1 : F[X]) := minpoly.dvd F Q (by simp [hQ])
  have hqm : q.Monic := (minpoly.monic hintF).of_mul_monic_left (hq ▸ X_pow_four_sub_X_sub_one_monic)
  have hqd : q.natDegree = 2 := by
    have := Polynomial.Monic.natDegree_mul (minpoly.monic hintF) hqm
    rw [← hq, X_pow_four_sub_X_sub_one_natDegree, hd] at this
    omega
  have hres := quartic_factor_resolvent ((minpoly F Q).coeff 1) ((minpoly F Q).coeff 0)
    (q.coeff 1) (q.coeff 0)
    (by rw [← monic_natDegree_two_eq (minpoly.monic hintF) hd, ← monic_natDegree_two_eq hqm hqd]
        exact hq.symm)
  set a : F := (minpoly F Q).coeff 1
  refine ⟨(a : L) ^ 2, ?_, pow_mem a.2 2⟩
  have : (((a ^ 2) ^ 3 + 4 * a ^ 2 - 1 : F) : L) = 0 := by rw [hres]; simp
  push_cast at this
  exact this

/-! ### No root of the resolvent cubic; no sextic subfield; at most one quartic root -/

/-- **No resolvent root.** A degree-12 field containing a root `ρ` of `x³ − x − 1` contains no
root of `x³ + 4x − 1`: such a root would have degree `1` or `2` over `ℚ(ρ)` (its degree divides
`[L : ℚ(ρ)] = 4` and is at most `3`), hence `x³ + 4x − 1` would have a root in the cubic field
`ℚ(ρ)`, against the discriminant distinction. -/
theorem no_resolvent_root {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (ρ : L) (hρ : ρ ^ 3 - ρ - 1 = 0) (y : L) (hy : y ^ 3 + 4 * y - 1 = 0) : False := by
  set K : IntermediateField ℚ L := ℚ⟮ρ⟯ with hKdef
  have hK3 : finrank ℚ K = 3 := finrank_adjoin_cubic_root ρ hρ
  have htower : finrank ℚ K * finrank K L = finrank ℚ L := Module.finrank_mul_finrank ℚ K L
  have hKL : finrank K L = 4 := by rw [hK3, hL] at htower; omega
  have hint : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hdvd4 : (minpoly K y).natDegree ∣ 4 := by
    have h := IntermediateField.finrank_dvd_of_le_right (le_top : K⟮y⟯ ≤ ⊤)
    rwa [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, hKL] at h
  have hle3 : (minpoly K y).natDegree ≤ 3 := by
    have hd : minpoly K y ∣ resolventCubic.map (algebraMap ℚ K) :=
      minpoly.dvd K y (by rw [aeval_map_algebraMap]; simp [resolventCubic, hy, map_ofNat])
    have := natDegree_le_of_dvd hd (resolventCubic_monic.map _).ne_zero
    rwa [resolventCubic_monic.natDegree_map, resolventCubic_natDegree] at this
  have hle2 : (minpoly K y).natDegree ≤ 2 := by
    have h4 := Nat.le_of_dvd (by norm_num) hdvd4
    obtain ⟨d, hd⟩ : ∃ d, (minpoly K y).natDegree = d := ⟨_, rfl⟩
    rw [hd] at hdvd4 hle3 h4 ⊢
    interval_cases d <;> simp_all
  obtain ⟨y', hy', hy'K⟩ := exists_root_mem_of_natDegree_le_two K resolventCubic_monic
    resolventCubic_natDegree y (by simp [resolventCubic, hy, map_ofNat]) hle2
  have hy'3 : y' ^ 3 + 4 * y' - 1 = 0 := by simpa [resolventCubic, map_ofNat] using hy'
  refine no_cubic_field_with_both_roots hK3 ⟨ρ, mem_adjoin_simple_self ℚ ρ⟩ ⟨y', hy'K⟩ ?_ ?_
  · apply Subtype.ext; push_cast; exact hρ
  · apply Subtype.ext; push_cast; exact hy'3

/-- **No sextic subfield.** -/
theorem no_sextic_subfield {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (ρ Q : L) (hρ : ρ ^ 3 - ρ - 1 = 0) (hQ : Q ^ 4 - Q - 1 = 0) (F : IntermediateField ℚ L) :
    finrank ℚ F ≠ 6 := by
  intro hF
  have htower : finrank ℚ F * finrank F L = finrank ℚ L := Module.finrank_mul_finrank ℚ F L
  have hFL : finrank F L = 2 := by rw [hF, hL] at htower; omega
  have hdivF : ∀ x : L, (minpoly F x).natDegree ∣ 2 := by
    intro x
    have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
    have h := IntermediateField.finrank_dvd_of_le_right (le_top : F⟮x⟯ ≤ ⊤)
    rwa [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, hFL] at h
  have hQpos := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := F) Q)
  have hQle := Nat.le_of_dvd (by norm_num) (hdivF Q)
  rcases Nat.lt_or_ge (minpoly F Q).natDegree 2 with h | h
  · -- `Q ∈ F`; together with a root of the cubic in `F` this gives a degree-12 subfield of `F`
    have h1 : (minpoly F Q).natDegree = 1 := by omega
    obtain ⟨y, hy⟩ := minpoly.natDegree_eq_one_iff.mp h1
    have hQF : Q ∈ F := hy ▸ y.2
    obtain ⟨r, hr, hrF⟩ := exists_root_mem_of_natDegree_le_two F (g := X ^ 3 - X - 1)
      (by monicity!) (by compute_degree!) ρ (by simp [hρ])
      (Nat.le_of_dvd (by norm_num) (hdivF ρ))
    have hr3 : r ^ 3 - r - 1 = 0 := by simpa using hr
    have hdisj : ℚ⟮r⟯.LinearDisjoint ℚ⟮Q⟯ := IntermediateField.LinearDisjoint.of_finrank_coprime
      (by rw [finrank_adjoin_cubic_root r hr3, finrank_adjoin_quartic_root Q hQ]; decide)
    have hsup := IntermediateField.finrank_dvd_of_le_right
      (sup_le (adjoin_simple_le_iff.mpr hrF) (adjoin_simple_le_iff.mpr hQF) : ℚ⟮r⟯ ⊔ ℚ⟮Q⟯ ≤ F)
    rw [hdisj.finrank_sup, finrank_adjoin_cubic_root r hr3, finrank_adjoin_quartic_root Q hQ,
      hF] at hsup
    norm_num at hsup
  · have h2 : (minpoly F Q).natDegree = 2 := by omega
    obtain ⟨y, hy3, -⟩ := exists_resolvent_root_mem Q hQ F h2
    exact no_resolvent_root hL ρ hρ y hy3

/-- **At most one root of `x⁴ − x − 1`.** Two distinct roots `Q ≠ Q'` in `L` would give the
factorization `(X − Q)(X − Q') · (monic quadratic)`, hence a root `(Q + Q')²` of the resolvent
cubic in `L`. -/
theorem quartic_root_unique {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (ρ : L) (hρ : ρ ^ 3 - ρ - 1 = 0) (Q Q' : L) (hQ : Q ^ 4 - Q - 1 = 0)
    (hQ' : Q' ^ 4 - Q' - 1 = 0) : Q = Q' := by
  by_contra hne
  have h1 : (X - C Q) ∣ (X ^ 4 - X - 1 : L[X]) := by
    rw [dvd_iff_isRoot]; simp [hQ]
  have h2 : (X - C Q') ∣ (X ^ 4 - X - 1 : L[X]) := by
    rw [dvd_iff_isRoot]; simp [hQ']
  have hcop : IsCoprime (X - C Q) (X - C Q' : L[X]) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hne).isUnit
  obtain ⟨q, hq⟩ := hcop.mul_dvd h1 h2
  have hpm : ((X - C Q) * (X - C Q') : L[X]).Monic := (monic_X_sub_C Q).mul (monic_X_sub_C Q')
  have hqm : q.Monic := hpm.of_mul_monic_left (hq ▸ X_pow_four_sub_X_sub_one_monic)
  have hpd : ((X - C Q) * (X - C Q') : L[X]).natDegree = 2 := by
    rw [Polynomial.Monic.natDegree_mul (monic_X_sub_C Q) (monic_X_sub_C Q'), natDegree_X_sub_C,
      natDegree_X_sub_C]
  have hqd : q.natDegree = 2 := by
    have := Polynomial.Monic.natDegree_mul hpm hqm
    rw [← hq, X_pow_four_sub_X_sub_one_natDegree, hpd] at this
    omega
  have hfac : (X ^ 2 + C (-(Q + Q')) * X + C (Q * Q')) * (X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0))
      = (X ^ 4 - X - 1 : L[X]) := by
    rw [← monic_natDegree_two_eq hqm hqd, hq]
    congr 1
    simp only [map_neg, map_add, map_mul]
    ring
  have hres := quartic_factor_resolvent _ _ _ _ hfac
  exact no_resolvent_root hL ρ hρ _ hres

/-! ### Uniqueness of the cubic root -/

/-- **At most one root of `x³ − x − 1`.** Two distinct roots `r ≠ r'` in `L` give the third root
`s = −r − r'` and the discriminant square root `δ = (r − r')(r − s)(r' − s)` with `δ² = −23`, so
`ℚ(δ)` would be a quadratic subfield. -/
theorem cubic_root_unique {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (Q : L) (hQ : Q ^ 4 - Q - 1 = 0) (r r' : L) (hr : r ^ 3 - r - 1 = 0)
    (hr' : r' ^ 3 - r' - 1 = 0) : r = r' := by
  by_contra hne
  have hsym : r ^ 2 + r * r' + r' ^ 2 = 1 := by
    have h : (r - r') * (r ^ 2 + r * r' + r' ^ 2 - 1) = 0 := by linear_combination hr - hr'
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · linear_combination h
  set δ : L := (r - r') * (r - (-r - r')) * (r' - (-r - r')) with hδ
  have hδ2 : δ ^ 2 = -23 := by
    rw [hδ]
    linear_combination (-27 * r ^ 3 + 27 * r - 27) * hr
      + (31 * r ^ 4 - 19 * r ^ 3 * r' - 15 * r ^ 2 * r' ^ 2 - 23 * r ^ 2 + 8 * r * r' ^ 3
          + 4 * r * r' + 4 * r' ^ 4 + 4 * r' ^ 2 + 4) * hsym
  have hirr : Irreducible (X ^ 2 + 23 : ℚ[X]) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [show (X ^ 2 + 23 : ℚ[X]).natDegree = 2 by compute_degree!]; decide
    · intro x hx
      have hx' : x ^ 2 + 23 = 0 := by simpa using hx
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ δ = X ^ 2 + 23 := by
    symm
    apply minpoly.eq_of_irreducible_of_monic hirr
    · simp only [map_add, map_pow, aeval_X, map_ofNat, hδ2]; norm_num
    · monicity!
  have hfin : finrank ℚ ℚ⟮δ⟯ = 2 := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral δ), hmin]
    compute_degree!
  exact no_quadratic_subfield hL Q hQ ℚ⟮δ⟯ hfin

/-! ### The cubic and quartic subfields are unique; the lattice -/

/-- A subfield of degree `3` is `ℚ(ρ)`. -/
theorem cubic_subfield_eq {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (ρ Q : L) (hρ : ρ ^ 3 - ρ - 1 = 0) (hQ : Q ^ 4 - Q - 1 = 0) (F : IntermediateField ℚ L)
    (hF : finrank ℚ F = 3) : F = ℚ⟮ρ⟯ := by
  have htower : finrank ℚ F * finrank F L = finrank ℚ L := Module.finrank_mul_finrank ℚ F L
  have hFL : finrank F L = 4 := by rw [hF, hL] at htower; omega
  have hint : IsIntegral F ρ := Algebra.IsIntegral.isIntegral ρ
  have hdvd4 : (minpoly F ρ).natDegree ∣ 4 := by
    have h := IntermediateField.finrank_dvd_of_le_right (le_top : F⟮ρ⟯ ≤ ⊤)
    rwa [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, hFL] at h
  have hle3 : (minpoly F ρ).natDegree ≤ 3 := by
    have hd : minpoly F ρ ∣ (X ^ 3 - X - 1 : F[X]) := minpoly.dvd F ρ (by simp [hρ])
    have hm : (X ^ 3 - X - 1 : F[X]).Monic := by monicity!
    have := natDegree_le_of_dvd hd hm.ne_zero
    rwa [show (X ^ 3 - X - 1 : F[X]).natDegree = 3 by compute_degree!] at this
  have hle2 : (minpoly F ρ).natDegree ≤ 2 := by
    have h4 := Nat.le_of_dvd (by norm_num) hdvd4
    obtain ⟨d, hd⟩ : ∃ d, (minpoly F ρ).natDegree = d := ⟨_, rfl⟩
    rw [hd] at hdvd4 hle3 h4 ⊢
    interval_cases d <;> simp_all
  obtain ⟨r, hr, hrF⟩ := exists_root_mem_of_natDegree_le_two F (g := X ^ 3 - X - 1)
    (by monicity!) (by compute_degree!) ρ (by simp [hρ]) hle2
  have hr3 : r ^ 3 - r - 1 = 0 := by simpa using hr
  have hrρ : r = ρ := cubic_root_unique hL Q hQ r ρ hr3 hρ
  rw [hrρ] at hrF
  symm
  exact IntermediateField.eq_of_le_of_finrank_eq (adjoin_simple_le_iff.mpr hrF)
    (by rw [finrank_adjoin_cubic_root ρ hρ, hF])

/-- A subfield of degree `4` is `ℚ(Q)`. -/
theorem quartic_subfield_eq {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (ρ Q : L) (hρ : ρ ^ 3 - ρ - 1 = 0) (hQ : Q ^ 4 - Q - 1 = 0) (F : IntermediateField ℚ L)
    (hF : finrank ℚ F = 4) : F = ℚ⟮Q⟯ := by
  have htower : finrank ℚ F * finrank F L = finrank ℚ L := Module.finrank_mul_finrank ℚ F L
  have hFL : finrank F L = 3 := by rw [hF, hL] at htower; omega
  have hint : IsIntegral F Q := Algebra.IsIntegral.isIntegral Q
  have hdvd3 : (minpoly F Q).natDegree ∣ 3 := by
    have h := IntermediateField.finrank_dvd_of_le_right (le_top : F⟮Q⟯ ≤ ⊤)
    rwa [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, hFL] at h
  have hpdvd : minpoly F Q ∣ (X ^ 4 - X - 1 : F[X]) := minpoly.dvd F Q (by simp [hQ])
  have hQF : Q ∈ F := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
    · obtain ⟨y, hy⟩ := minpoly.natDegree_eq_one_iff.mp h1
      exact hy ▸ y.2
    · obtain ⟨r, hr⟩ := exists_isRoot_of_dvd_natDegree_succ (minpoly.monic hint)
        X_pow_four_sub_X_sub_one_monic hpdvd (by rw [X_pow_four_sub_X_sub_one_natDegree, h3])
      have hr4 : r ^ 4 - r - 1 = 0 := by simpa using hr
      have hr4' : (r : L) ^ 4 - (r : L) - 1 = 0 := by
        have : ((r ^ 4 - r - 1 : F) : L) = 0 := by rw [hr4]; simp
        push_cast at this
        exact this
      have hrQ : (r : L) = Q := quartic_root_unique hL ρ hρ (r : L) Q hr4' hQ
      rw [← hrQ]; exact r.2
  symm
  exact IntermediateField.eq_of_le_of_finrank_eq (adjoin_simple_le_iff.mpr hQF)
    (by rw [finrank_adjoin_quartic_root Q hQ, hF])

/-- **The subfield lattice.** A degree-12 number field containing a root `ρ` of `x³ − x − 1` and a
root `Q` of `x⁴ − x − 1` has exactly the subfields `ℚ`, `ℚ(ρ)`, `ℚ(Q)`, `L`. -/
theorem subfield_lattice {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (ρ Q : L) (hρ : ρ ^ 3 - ρ - 1 = 0) (hQ : Q ^ 4 - Q - 1 = 0) (F : IntermediateField ℚ L) :
    F = ⊥ ∨ F = ℚ⟮ρ⟯ ∨ F = ℚ⟮Q⟯ ∨ F = ⊤ := by
  have hdvd : finrank ℚ F ∣ 12 := by
    have h := IntermediateField.finrank_dvd_of_le_right (le_top : F ≤ ⊤)
    rwa [IntermediateField.finrank_top', hL] at h
  have hpos : 0 < finrank ℚ F := Module.finrank_pos
  have h12 : finrank ℚ F ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨d, hd⟩ : ∃ d, finrank ℚ F = d := ⟨_, rfl⟩
  rw [hd] at hdvd hpos h12
  have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 ∨ d = 12 := by
    interval_cases d <;> omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (IntermediateField.finrank_eq_one_iff.mp hd)
  · exact absurd hd (no_quadratic_subfield hL Q hQ F)
  · exact Or.inr (Or.inl (cubic_subfield_eq hL ρ Q hρ hQ F hd))
  · exact Or.inr (Or.inr (Or.inl (quartic_subfield_eq hL ρ Q hρ hQ F hd)))
  · exact absurd hd (no_sextic_subfield hL ρ Q hρ hQ F)
  · exact Or.inr (Or.inr (Or.inr (IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [hd, IntermediateField.finrank_top', hL]))))

/-! ### Root-rigidity of the degree-12 field; circle-free -/

/-- Any two `ℚ`-algebra maps from a subfield of `L` into `L` coincide (every subfield has a
trivial automorphism group, in the strong "no second root in `L`" form). -/
theorem algHom_eq {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (ρ Q : L) (hρ : ρ ^ 3 - ρ - 1 = 0) (hQ : Q ^ 4 - Q - 1 = 0) (F : IntermediateField ℚ L)
    (φ₁ φ₂ : F →ₐ[ℚ] L) : φ₁ = φ₂ := by
  have hcub : ∀ (φ : F →ₐ[ℚ] L) (x : F), (x : L) ^ 3 - (x : L) - 1 = 0 → φ x = ρ := by
    intro φ x hx
    have hx' : x ^ 3 - x - 1 = 0 := by apply Subtype.ext; push_cast; exact hx
    have h3 : (φ x) ^ 3 - φ x - 1 = 0 := by
      have := congrArg φ hx'; simpa using this
    exact cubic_root_unique hL Q hQ _ _ h3 hρ
  have hquar : ∀ (φ : F →ₐ[ℚ] L) (x : F), (x : L) ^ 4 - (x : L) - 1 = 0 → φ x = Q := by
    intro φ x hx
    have hx' : x ^ 4 - x - 1 = 0 := by apply Subtype.ext; push_cast; exact hx
    have h4 : (φ x) ^ 4 - φ x - 1 = 0 := by
      have := congrArg φ hx'; simpa using this
    exact quartic_root_unique hL ρ hρ _ _ h4 hQ
  rcases subfield_lattice hL ρ Q hρ hQ F with rfl | rfl | rfl | rfl
  · -- `⊥`: every element is rational
    ext x
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
    have hx : x = algebraMap ℚ (⊥ : IntermediateField ℚ L) q := Subtype.ext hq.symm
    rw [hx, φ₁.commutes, φ₂.commutes]
  · -- `ℚ(ρ)`: determined by the image of `ρ`, a cubic root, hence `ρ`
    apply (IntermediateField.adjoin.powerBasis (isIntegral_cubic_root ρ hρ)).algHom_ext
    rw [IntermediateField.adjoin.powerBasis_gen]
    rw [hcub φ₁ _ (by rw [AdjoinSimple.coe_gen]; exact hρ),
      hcub φ₂ _ (by rw [AdjoinSimple.coe_gen]; exact hρ)]
  · -- `ℚ(Q)`
    apply (IntermediateField.adjoin.powerBasis (isIntegral_quartic_root Q hQ)).algHom_ext
    rw [IntermediateField.adjoin.powerBasis_gen]
    rw [hquar φ₁ _ (by rw [AdjoinSimple.coe_gen]; exact hQ),
      hquar φ₂ _ (by rw [AdjoinSimple.coe_gen]; exact hQ)]
  · -- `⊤`: generated by `ρ` and `Q`
    have hdisj : ℚ⟮ρ⟯.LinearDisjoint ℚ⟮Q⟯ := IntermediateField.LinearDisjoint.of_finrank_coprime
      (by rw [finrank_adjoin_cubic_root ρ hρ, finrank_adjoin_quartic_root Q hQ]; decide)
    have hsup : ℚ⟮ρ⟯ ⊔ ℚ⟮Q⟯ = ⊤ := by
      apply IntermediateField.eq_of_le_of_finrank_eq le_top
      rw [hdisj.finrank_sup, finrank_adjoin_cubic_root ρ hρ, finrank_adjoin_quartic_root Q hQ,
        IntermediateField.finrank_top', hL]
    have hadj : IntermediateField.adjoin ℚ ({ρ, Q} : Set L) = ⊤ := by
      rw [Set.insert_eq, IntermediateField.adjoin_union, hsup]
    have hadj' : Algebra.adjoin ℚ ({ρ, Q} : Set L) = ⊤ := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hadj, IntermediateField.top_toSubalgebra]
    have hcoe : ∀ y : L, ((IntermediateField.topEquiv.symm y : (⊤ : IntermediateField ℚ L)) : L) = y :=
      fun y => rfl
    let ψ₁ : L →ₐ[ℚ] L := φ₁.comp IntermediateField.topEquiv.symm.toAlgHom
    let ψ₂ : L →ₐ[ℚ] L := φ₂.comp IntermediateField.topEquiv.symm.toAlgHom
    have hψ : ψ₁ = ψ₂ := by
      apply AlgHom.ext_of_adjoin_eq_top hadj'
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · show φ₁ (IntermediateField.topEquiv.symm x) = φ₂ (IntermediateField.topEquiv.symm x)
        rw [hcub φ₁ _ (by rw [hcoe]; exact hρ), hcub φ₂ _ (by rw [hcoe]; exact hρ)]
      · show φ₁ (IntermediateField.topEquiv.symm x) = φ₂ (IntermediateField.topEquiv.symm x)
        rw [hquar φ₁ _ (by rw [hcoe]; exact hQ), hquar φ₂ _ (by rw [hcoe]; exact hQ)]
    ext x
    have hx : (IntermediateField.topEquiv.symm (x : L) : (⊤ : IntermediateField ℚ L)) = x :=
      Subtype.ext (hcoe x)
    have := AlgHom.congr_fun hψ (x : L)
    simp only [ψ₁, ψ₂, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at this
    rwa [hx] at this

/-- **Root-rigidity.** No irreducible polynomial over `ℚ` has two distinct roots in `L`. -/
theorem rootRigid_of_roots {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (ρ Q : L) (hρ : ρ ^ 3 - ρ - 1 = 0) (hQ : Q ^ 4 - Q - 1 = 0) : RootRigid L := by
  intro α β hmin
  have hα : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  have hne : minpoly ℚ α ≠ 0 := minpoly.ne_zero hα
  have hαmem : α ∈ (minpoly ℚ α).aroots L := mem_aroots.mpr ⟨hne, minpoly.aeval ℚ α⟩
  have hβmem : β ∈ (minpoly ℚ α).aroots L :=
    mem_aroots.mpr ⟨hne, by rw [hmin]; exact minpoly.aeval ℚ β⟩
  let e := IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := L) hα
  have h := algHom_eq hL ρ Q hρ hQ ℚ⟮α⟯ (e.symm ⟨α, hαmem⟩) (e.symm ⟨β, hβmem⟩)
  have h' := e.symm.injective h
  exact Subtype.ext_iff.mp h'

/-- **Circle-free.** In a degree-12 number field containing roots of `x³ − x − 1` and
`x⁴ − x − 1`, the only elements with a complex embedding of modulus `1` are `±1`; in particular
the field contains no Salem number and no root of unity other than `±1`. -/
theorem circle_free {L : Type*} [Field L] [NumberField L] (hL : finrank ℚ L = 12)
    (ρ Q : L) (hρ : ρ ^ 3 - ρ - 1 = 0) (hQ : Q ^ 4 - Q - 1 = 0)
    (α : L) (σ : L →+* ℂ) (hα : ‖σ α‖ = 1) : α = 1 ∨ α = -1 :=
  circle_free_of_rootRigid (rootRigid_of_roots hL ρ Q hρ hQ) α σ hα


end InflationDimension.Compositum
