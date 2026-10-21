module
public import Mathlib
public import InflationDimension.Defs

@[expose] public section
/-!
# Admissibility of an invariant cut-and-project scheme, and Kronecker's density criterion

For an integer matrix `A` and an `A`-invariant cut-and-project scheme `ℝ^ι = E ⊕ H` on the
lattice `ℤ^ι`:

* `InvariantCPS.mapsTo_modelSet_iff`: `A Λ(W) ⊆ Λ(W)` if and only if `A` maps the lattice points
  `W ∩ π_H(ℤ^ι)` of the window into `W` (any `W`).
* `admissible_iff_powerBounded`: the scheme is admissible if and only if `A` is power-bounded on
  `H`; then the orbit window `W_*` is a compact, convex, centrally symmetric window with
  `A W_* ⊆ W_*` and `A Λ(W_*) ⊆ Λ(W_*)` (`InvariantCPS.orbitWindow_spec`).
* `roots_restrict_H_le_one`, `unstableCount_le_finrank`: on an admissible scheme every eigenvalue
  of `A|_H` lies in the closed unit disk, so the number `U(A)` of eigenvalues of modulus `> 1` is
  at most `dim E`.
* `kronecker_density_criterion`: the projection of `ℤ^ι` to `H` along `E` is dense in `H` if and
  only if every real functional that is integer-valued on `ℤ^ι` and vanishes on `E` is zero
  (Pleasants (2000), Cor. 2.12).

The two compared statements `admissibility_criterion` and `kronecker_density_criterion` are
proved at the end of the file. General facts about a finite-dimensional real space (the
characteristic polynomial of a direct sum, eigenvalues of a power-bounded map) are in the
namespace `InflationDimension.PowerBounded`; Kronecker's criterion for a `ℤ`-submodule `Γ`
spanning the space (`Γ + E` dense if and only if no nonzero functional is integral on `Γ` and
vanishes on `E`) is in `InflationDimension.KroneckerDensity`.
-/

namespace InflationDimension

open Polynomial Filter Topology Module

noncomputable section

/-! ### Linear algebra on a finite-dimensional real space -/

namespace PowerBounded

/-- The characteristic polynomial of an endomorphism preserving both summands of a direct sum
`V = E ⊕ H` is the product of the characteristic polynomials of the two restrictions. -/
theorem charpoly_eq_mul_of_isCompl {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (f : Module.End ℝ V) (E H : Submodule ℝ V) (h : IsCompl E H)
    (hE : ∀ v ∈ E, f v ∈ E) (hH : ∀ v ∈ H, f v ∈ H) :
    f.charpoly = (f.restrict hE).charpoly * (f.restrict hH).charpoly := by
  let e := Submodule.prodEquivOfIsCompl E H h
  have hf : e.conj ((f.restrict hE).prodMap (f.restrict hH)) = f := by
    ext v
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
    simp [e, LinearEquiv.conj_apply, Submodule.coe_prodEquivOfIsCompl', map_add]
  exact (congrArg LinearMap.charpoly hf.symm).trans
    ((LinearEquiv.charpoly_conj e _).trans (LinearMap.charpoly_prodMap _ _))

open Matrix in
/-- A real square matrix whose powers have uniformly bounded entries has all its complex
eigenvalues in the closed unit disk. -/
theorem norm_le_one_of_pow_bounded {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (C : ℝ) (hC : ∀ (k : ℕ) (i j : n), |(M ^ k) i j| ≤ C) :
    ∀ z ∈ (M.charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1 := by
  intro z hz
  set MC : Matrix n n ℂ := M.map (algebraMap ℝ ℂ)
  have hroot : IsRoot MC.charpoly z := by
    rw [Matrix.charpoly_map]
    exact (mem_roots'.mp hz).2
  have hspec : z ∈ spectrum ℂ (Matrix.toLin' MC) := by
    rw [Matrix.spectrum_toLin']
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hspec).exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hvec : MC *ᵥ v = z • v := by
    have := Module.End.mem_eigenspace_iff.mp hv.1
    simpa [Matrix.toLin'_apply] using this
  have hpowvec : ∀ k : ℕ, (MC ^ k) *ᵥ v = z ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hvec, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  obtain ⟨l, hl⟩ : ∃ l, v l ≠ 0 := by
    by_contra! hall
    exact hv0 (funext hall)
  have hpowent : ∀ (k : ℕ) (i j : n), (MC ^ k) i j = ((M ^ k) i j : ℂ) := fun k i j => by
    have := congrArg (fun B : Matrix n n ℂ => B i j) (map_pow (algebraMap ℝ ℂ).mapMatrix M k)
    simpa [RingHom.mapMatrix_apply, MC] using this.symm
  set D : ℝ := ∑ j, C * ‖v j‖
  have hbound : ∀ k : ℕ, ‖z‖ ^ k * ‖v l‖ ≤ D := by
    intro k
    have h1 : ((MC ^ k) *ᵥ v) l = z ^ k * v l := by rw [hpowvec k]; simp
    calc ‖z‖ ^ k * ‖v l‖ = ‖((MC ^ k) *ᵥ v) l‖ := by rw [h1, norm_mul, norm_pow]
      _ = ‖∑ j, (MC ^ k) l j * v j‖ := by rw [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, ‖(MC ^ k) l j * v j‖ := norm_sum_le _ _
      _ ≤ ∑ j, C * ‖v j‖ := by
        gcongr with j
        rw [norm_mul, hpowent, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hC k l j) (norm_nonneg _)
  by_contra! hz1
  have hvl : 0 < ‖v l‖ := norm_pos_iff.mpr hl
  have htend : Tendsto (fun k : ℕ => ‖z‖ ^ k * ‖v l‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hz1).atTop_mul_const hvl
  obtain ⟨k, hk⟩ := (htend.eventually_gt_atTop D).exists
  exact absurd hk (not_lt.mpr (hbound k))

/-- If an endomorphism of a finite-dimensional real normed space is power-bounded, the entries of
the powers of its matrix in a fixed basis are uniformly bounded. -/
theorem entries_bounded_of_powerBounded {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f : Module.End ℝ V) {C : ℝ}
    (hC : ∀ (n : ℕ) (v : V), ‖(f ^ n) v‖ ≤ C * ‖v‖) :
    ∃ K : ℝ, ∀ (n : ℕ) (i j : Fin (finrank ℝ V)),
      |(LinearMap.toMatrix (Module.finBasis ℝ V) (Module.finBasis ℝ V) f ^ n) i j| ≤ K := by
  set b := Module.finBasis ℝ V
  set T : V →L[ℝ] (Fin (finrank ℝ V) → ℝ) :=
    LinearMap.toContinuousLinearMap b.equivFun.toLinearMap
  set B : ℝ := ∑ j, ‖b j‖
  refine ⟨‖T‖ * (max C 0 * B), fun n i j => ?_⟩
  rw [LinearMap.toMatrix_pow, LinearMap.toMatrix_apply]
  have hT : |b.repr ((f ^ n) (b j)) i| ≤ ‖T ((f ^ n) (b j))‖ := by
    have := norm_le_pi_norm (T ((f ^ n) (b j))) i
    simpa [T, Real.norm_eq_abs] using this
  refine hT.trans ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)))
  have hB : ‖b j‖ ≤ B :=
    Finset.single_le_sum (f := fun j => ‖b j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  calc ‖(f ^ n) (b j)‖ ≤ C * ‖b j‖ := hC n (b j)
    _ ≤ max C 0 * ‖b j‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max C 0 * B := mul_le_mul_of_nonneg_left hB (le_max_right _ _)

/-- The powers of a restriction are the restrictions of the powers. -/
theorem coe_restrict_pow_apply {V : Type*} [AddCommGroup V] [Module ℝ V] (f : Module.End ℝ V)
    {p : Submodule ℝ V} (h : ∀ v ∈ p, f v ∈ p) (n : ℕ) (x : p) :
    (((f.restrict h) ^ n) x : V) = (f ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, LinearMap.coe_restrict_apply, pow_succ,
      Module.End.mul_apply]

end PowerBounded

/-! ### Kronecker's density criterion in a finite-dimensional real space -/

namespace KroneckerDensity

/-- A closed subgroup of a finite-dimensional real normed space containing no line is
discrete. -/
theorem discreteTopology_of_isClosed_of_no_line
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (G : AddSubgroup F) (hG : IsClosed (G : Set F))
    (hline : ∀ v : F, (∀ t : ℝ, t • v ∈ G) → v = 0) : DiscreteTopology G := by
  have key : ∃ ε > 0, ∀ g ∈ G, ‖g‖ < ε → g = 0 := by
    by_contra! h
    choose g hgG hgn hg0 using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
    have hgpos : ∀ n, 0 < ‖g n‖ := fun n => norm_pos_iff.mpr (hg0 n)
    set u : ℕ → F := fun n => ‖g n‖⁻¹ • g n with hu_def
    have hu : ∀ n, u n ∈ Metric.sphere (0 : F) 1 := by
      intro n
      simp only [u, mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (hgpos n).ne'
    obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_sphere (0 : F) 1).tendsto_subseq hu
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    apply hw0
    apply hline
    intro t
    have hr : Tendsto (fun n => ‖g (φ n)‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      refine (hgn (φ n)).le.trans ?_
      have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
      gcongr
    have hconv : Tendsto (fun n => (⌊t / ‖g (φ n)‖⌋ : ℤ) • g (φ n)) atTop (𝓝 (t • w)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : ∀ n, ‖(⌊t / ‖g (φ n)‖⌋ : ℤ) • g (φ n) - t • w‖
          ≤ ‖g (φ n)‖ + |t| * ‖u (φ n) - w‖ := by
        intro n
        set r := ‖g (φ n)‖ with hr_def
        have hrpos : 0 < r := hgpos (φ n)
        have hsplit : (⌊t / r⌋ : ℤ) • g (φ n) - t • w
            = ((⌊t / r⌋ : ℝ) - t / r) • g (φ n) + t • (u (φ n) - w) := by
          simp only [u, smul_sub, sub_smul, smul_smul, ← hr_def, Int.cast_smul_eq_zsmul]
          field_simp
          abel
        rw [hsplit]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        gcongr
        calc |(⌊t / r⌋ : ℝ) - t / r| * r ≤ 1 * r := by
              gcongr
              rw [abs_sub_comm, Int.self_sub_floor, Int.abs_fract]
              exact (Int.fract_lt_one _).le
          _ = r := one_mul r
      refine squeeze_zero (fun n => norm_nonneg _) hb ?_
      have h2 : Tendsto (fun n => ‖u (φ n) - w‖) atTop (𝓝 0) :=
        (tendsto_iff_norm_sub_tendsto_zero).mp hlim
      simpa using hr.add (h2.const_mul |t|)
    exact hG.mem_of_tendsto hconv (Eventually.of_forall fun n => G.zsmul_mem (hgG _) _)
  obtain ⟨ε, hε, hiso⟩ := key
  apply discreteTopology_of_isOpen_singleton_zero
  have : ({0} : Set G) = Subtype.val ⁻¹' Metric.ball (0 : F) ε := by
    ext ⟨x, hx⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage, mem_ball_zero_iff]
    constructor
    · intro h
      have : x = 0 := congrArg Subtype.val h
      simp [this, hε]
    · intro h
      exact Subtype.ext (hiso x hx h)
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The subspace of the vectors spanning a line contained in the subgroup `C`. -/
def lineSpace (C : AddSubgroup V) : Submodule ℝ V where
  carrier := {u | ∀ t : ℝ, t • u ∈ C}
  add_mem' := by
    intro a b ha hb t
    rw [smul_add]; exact C.add_mem (ha t) (hb t)
  zero_mem' := by intro t; simp [C.zero_mem]
  smul_mem' := by
    intro r a ha t
    rw [smul_smul]; exact ha (t * r)

theorem lineSpace_subset (C : AddSubgroup V) : (lineSpace C : Set V) ⊆ C := by
  intro u hu; simpa using hu 1

variable [FiniteDimensional ℝ V]

/-- Kronecker's criterion, sufficiency: if no nonzero real functional is integer-valued on `Γ`
and vanishes on `E`, then `Γ + E` is dense. `Γ` need not be discrete. -/
theorem dense_sup_of_no_integral_functional (Γ : Submodule ℤ V)
    (hΓ : Submodule.span ℝ (Γ : Set V) = ⊤) (E : Submodule ℝ V)
    (hrat : ∀ ξ : V →ₗ[ℝ] ℝ, (∀ γ ∈ Γ, ∃ z : ℤ, ξ γ = z) → (∀ e ∈ E, ξ e = 0) → ξ = 0) :
    Dense ((Γ.toAddSubgroup ⊔ E.toAddSubgroup : AddSubgroup V) : Set V) := by
  set G : AddSubgroup V := Γ.toAddSubgroup ⊔ E.toAddSubgroup with hGdef
  set C : AddSubgroup V := G.topologicalClosure with hCdef
  have hCcl : IsClosed (C : Set V) := G.isClosed_topologicalClosure
  set L := lineSpace C with hLdef
  have hGC : G ≤ C := G.le_topologicalClosure
  have hΓC : ∀ γ ∈ Γ, γ ∈ C := fun γ hγ => hGC (AddSubgroup.mem_sup_left (by exact hγ))
  have hEL : E ≤ L := by
    intro e he t
    exact hGC (AddSubgroup.mem_sup_right (by exact E.smul_mem t he))
  suffices hL : L = ⊤ by
    rw [dense_iff_closure_eq, ← AddSubgroup.topologicalClosure_coe]
    apply Set.eq_univ_of_forall
    intro v
    exact lineSpace_subset C (by rw [← hLdef, hL]; trivial)
  by_contra hLne
  obtain ⟨L', hc⟩ := Submodule.exists_isCompl L
  set π : V →ₗ[ℝ] L' := L'.projectionOnto L hc.symm with hπ
  set D : AddSubgroup L' := C.comap L'.subtype.toAddMonoidHom with hD
  have hDcl : IsClosed (D : Set L') := hCcl.preimage continuous_subtype_val
  have hDline : ∀ x : L', (∀ t : ℝ, t • x ∈ D) → x = 0 := by
    intro x hx
    have hxL : (x : V) ∈ L := fun t => by simpa [hD] using hx t
    have hmem : (x : V) ∈ L ⊓ L' := ⟨hxL, x.2⟩
    rw [hc.inf_eq_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hDdisc : DiscreteTopology D := discreteTopology_of_isClosed_of_no_line D hDcl hDline
  set M : Submodule ℤ L' := Γ.map (π.restrictScalars ℤ) with hM
  have hMD : (M : Set L') ⊆ (D : Set L') := by
    rintro _ ⟨γ, hγ, rfl⟩
    show ((π γ : L') : V) ∈ C
    have hsplit := Submodule.projection_add_projection_eq_self hc γ
    have hcoe : ((π γ : L') : V) = L'.projection L hc.symm γ :=
      Submodule.coe_projectionOnto_apply hc.symm γ
    have hLpart : L.projection L' hc γ ∈ C :=
      lineSpace_subset C (Submodule.projection_apply_mem hc γ)
    have : ((π γ : L') : V) = γ - L.projection L' hc γ := by
      rw [hcoe]; exact (eq_sub_of_add_eq' hsplit)
    rw [this]
    exact C.sub_mem (hΓC γ hγ) hLpart
  have hMdisc : DiscreteTopology M := DiscreteTopology.of_subset hDdisc hMD
  have hMlat : IsZLattice ℝ M := by
    refine ⟨?_⟩
    have hset : (M : Set L') = π '' (Γ : Set V) := by
      simp [hM, Submodule.map_coe, LinearMap.coe_restrictScalars]
    rw [hset, Submodule.span_image, hΓ, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.projectionOnto_surjective hc.symm)
  set b := Module.Free.chooseBasis ℤ M with hb
  set B : Basis (Module.Free.ChooseBasisIndex ℤ M) ℝ L' := b.ofZLatticeBasis ℝ M with hB
  have hL'ne : L' ≠ ⊥ := by
    intro h
    apply hLne
    rw [h] at hc
    exact eq_top_of_isCompl_bot hc
  have : Nontrivial L' := Submodule.nontrivial_iff_ne_bot.mpr hL'ne
  have : Nonempty (Module.Free.ChooseBasisIndex ℤ M) := B.index_nonempty
  set i := Classical.arbitrary (Module.Free.ChooseBasisIndex ℤ M)
  set ξ : V →ₗ[ℝ] ℝ := (B.coord i) ∘ₗ π with hξ
  have hint : ∀ γ ∈ Γ, ∃ z : ℤ, ξ γ = z := by
    intro γ hγ
    let x : M := ⟨π γ, ⟨γ, hγ, rfl⟩⟩
    refine ⟨b.repr x i, ?_⟩
    have := b.ofZLatticeBasis_repr_apply ℝ M x i
    simpa [hξ, hB, x] using this
  have hvan : ∀ e ∈ E, ξ e = 0 := by
    intro e he
    have : π e = 0 := Submodule.projectionOnto_apply_of_mem_right hc.symm (hEL he)
    simp [hξ, this]
  have hne : ξ ≠ 0 := by
    intro h0
    have h1 : ξ ((B i : L') : V) = 1 := by
      have : π ((B i : L') : V) = B i := Submodule.projectionOnto_apply_left hc.symm (B i)
      simp [hξ, this]
    rw [h0] at h1
    simp at h1
  exact hne (hrat ξ hint hvan)

/-- Kronecker's criterion, necessity: if `Γ + E` is dense, a real functional that is
integer-valued on `Γ` and vanishes on `E` is zero. -/
theorem no_integral_functional_of_dense_sup (Γ : Submodule ℤ V) (E : Submodule ℝ V)
    (hd : Dense ((Γ.toAddSubgroup ⊔ E.toAddSubgroup : AddSubgroup V) : Set V)) :
    ∀ ξ : V →ₗ[ℝ] ℝ, (∀ γ ∈ Γ, ∃ z : ℤ, ξ γ = z) → (∀ e ∈ E, ξ e = 0) → ξ = 0 := by
  intro ξ hint hvan
  by_contra hne
  have hξc : Continuous ξ := LinearMap.continuous_of_finiteDimensional ξ
  set Z : Set V := ξ ⁻¹' Set.range ((↑) : ℤ → ℝ) with hZ
  have hZcl : IsClosed Z := Int.isClosedEmbedding_coe_real.isClosed_range.preimage hξc
  have hGZ : ((Γ.toAddSubgroup ⊔ E.toAddSubgroup : AddSubgroup V) : Set V) ⊆ Z := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hg
    obtain ⟨k, hk⟩ := hint y hy
    refine ⟨k, ?_⟩
    rw [map_add, hvan z hz, add_zero, hk]
  have hall : Z = Set.univ := by
    have := hZcl.closure_subset_iff.mpr hGZ
    rw [hd.closure_eq] at this
    exact Set.eq_univ_of_univ_subset this
  obtain ⟨v, hv⟩ : ∃ v, ξ v ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext h)
  have hmem : ((2 * ξ v)⁻¹ • v) ∈ Z := by rw [hall]; trivial
  obtain ⟨k, hk⟩ := hmem
  have hval : ξ ((2 * ξ v)⁻¹ • v) = 1 / 2 := by
    rw [map_smul, smul_eq_mul]; field_simp
  rw [hval] at hk
  have h0 : (0 : ℝ) < k := by rw [hk]; norm_num
  have h1 : (k : ℝ) < 1 := by rw [hk]; norm_num
  have h0' : (0 : ℤ) < k := by exact_mod_cast h0
  have h1' : k < (1 : ℤ) := by exact_mod_cast h1
  omega

omit [FiniteDimensional ℝ V] in
/-- If the projection of `Γ` to a complement `H` of `E` along `E` is dense in `H`, then `Γ + E`
is dense. -/
theorem dense_sup_of_dense_projection (Γ : Submodule ℤ V) {E H : Submodule ℝ V}
    (hc : IsCompl E H)
    (hd : (H : Set V) ⊆ closure (H.projection E hc.symm '' (Γ : Set V))) :
    Dense ((Γ.toAddSubgroup ⊔ E.toAddSubgroup : AddSubgroup V) : Set V) := by
  intro x
  set P : V →ₗ[ℝ] V := H.projection E hc.symm with hP
  set PE : V →ₗ[ℝ] V := E.projection H hc with hPE
  have hcont : Continuous fun y : V => y + PE x := continuous_id.add continuous_const
  have hmaps : Set.MapsTo (fun y : V => y + PE x) (P '' (Γ : Set V))
      ((Γ.toAddSubgroup ⊔ E.toAddSubgroup : AddSubgroup V) : Set V) := by
    rintro _ ⟨γ, hγ, rfl⟩
    have hsplit : PE γ + P γ = γ := Submodule.projection_add_projection_eq_self hc γ
    have hE : PE x - PE γ ∈ E :=
      E.sub_mem (Submodule.projection_apply_mem hc x) (Submodule.projection_apply_mem hc γ)
    refine AddSubgroup.mem_sup.mpr ⟨γ, hγ, PE x - PE γ, hE, ?_⟩
    show γ + (PE x - PE γ) = P γ + PE x
    rw [eq_sub_of_add_eq' hsplit]
    abel
  have hx : P x + PE x = x := by
    rw [add_comm]; exact Submodule.projection_add_projection_eq_self hc x
  have hmem : P x ∈ closure (P '' (Γ : Set V)) := hd (Submodule.projection_apply_mem hc.symm x)
  have := map_mem_closure hcont hmem hmaps
  convert this using 1
  exact hx.symm

end KroneckerDensity

open PowerBounded KroneckerDensity

/-! ### The lattice `ℤ^ι` and the action of `A` -/

section Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_intLattice_iff {v : ι → ℝ} :
    v ∈ intLattice ι ↔ ∃ n : ι → ℤ, v = fun i => (n i : ℝ) := by
  rw [intLattice, (Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ]
  simp only [Pi.basisFun_repr, Set.mem_range, algebraMap_int_eq, eq_intCast]
  constructor
  · intro h
    choose n hn using h
    exact ⟨n, funext fun i => (hn i).symm⟩
  · rintro ⟨n, rfl⟩ i
    exact ⟨n i, rfl⟩

theorem span_intLattice : Submodule.span ℝ (intLattice ι : Set (ι → ℝ)) = ⊤ := by
  rw [intLattice, Submodule.span_span_of_tower, (Pi.basisFun ℝ ι).span_eq]

theorem act_mem_intLattice (A : Matrix ι ι ℤ) {γ : ι → ℝ} (hγ : γ ∈ intLattice ι) :
    act A γ ∈ intLattice ι := by
  obtain ⟨n, rfl⟩ := mem_intLattice_iff.mp hγ
  refine mem_intLattice_iff.mpr ⟨A.mulVec n, ?_⟩
  funext i
  simp [act, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

theorem act_pow_mem_intLattice (A : Matrix ι ι ℤ) (n : ℕ) {γ : ι → ℝ}
    (hγ : γ ∈ intLattice ι) : (act A ^ n) γ ∈ intLattice ι := by
  induction n with
  | zero => simpa using hγ
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact act_mem_intLattice A ih

theorem charpoly_act (A : Matrix ι ι ℤ) :
    (act A).charpoly = A.charpoly.map (Int.castRingHom ℝ) := by
  rw [act, Matrix.charpoly_toLin']
  exact Matrix.charpoly_map A (Int.castRingHom ℝ)

theorem charpoly_restrict_mul (A : Matrix ι ι ℤ) {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H)
    (hE : ∀ v ∈ E, act A v ∈ E) (hH : ∀ v ∈ H, act A v ∈ H) :
    A.charpoly.map (Int.castRingHom ℝ) =
      ((act A).restrict hE).charpoly * ((act A).restrict hH).charpoly :=
  (charpoly_act A).symm.trans (charpoly_eq_mul_of_isCompl (act A) E H hc hE hH)

/-- `U(A)` counted on the real-linear map `act A`. -/
theorem unstableCount_eq_card (A : Matrix ι ι ℤ) :
    unstableCount A = Multiset.card
      (((act A).charpoly.map (algebraMap ℝ ℂ)).roots.filter (fun z => 1 < ‖z‖)) := by
  have h2 : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ :=
    RingHom.ext_int _ _
  rw [unstableCount, eigenvalues, charpoly_act, Polynomial.map_map, h2]

namespace InvariantCPS

variable {A : Matrix ι ι ℤ} (S : InvariantCPS A)

theorem πE_act (v : ι → ℝ) : S.πE (act A v) = act A (S.πE v) := by
  have hv := Submodule.projection_add_projection_eq_self S.isCompl v
  have he := Submodule.projection_apply_mem S.isCompl v
  have hk := Submodule.projection_apply_mem S.isCompl.symm v
  have h1 : act A v = act A (S.E.projection S.H S.isCompl v) +
      act A (S.H.projection S.E S.isCompl.symm v) := by
    rw [← map_add, hv]
  show S.E.projection S.H S.isCompl (act A v) = act A (S.E.projection S.H S.isCompl v)
  rw [h1, map_add, Submodule.projection_apply_of_mem_left S.isCompl (S.mapsTo_E _ he),
    Submodule.projection_apply_of_mem_right S.isCompl (S.mapsTo_H _ hk), add_zero]

theorem πH_act (v : ι → ℝ) : S.πH (act A v) = act A (S.πH v) := by
  have hv := Submodule.projection_add_projection_eq_self S.isCompl v
  have he := Submodule.projection_apply_mem S.isCompl v
  have hk := Submodule.projection_apply_mem S.isCompl.symm v
  have h1 : act A v = act A (S.E.projection S.H S.isCompl v) +
      act A (S.H.projection S.E S.isCompl.symm v) := by
    rw [← map_add, hv]
  show S.H.projection S.E S.isCompl.symm (act A v) =
    act A (S.H.projection S.E S.isCompl.symm v)
  rw [h1, map_add, Submodule.projection_apply_of_mem_right S.isCompl.symm (S.mapsTo_E _ he),
    Submodule.projection_apply_of_mem_left S.isCompl.symm (S.mapsTo_H _ hk), zero_add]

theorem πH_mem (v : ι → ℝ) : S.πH v ∈ S.H := Submodule.projection_apply_mem _ _

theorem πE_mem (v : ι → ℝ) : S.πE v ∈ S.E := Submodule.projection_apply_mem _ _

/-- **Per-window criterion.** `A Λ(W) ⊆ Λ(W)` if and only if `A` maps the lattice points
`W ∩ π_H(ℤ^ι)` of the window into `W`. -/
theorem mapsTo_modelSet_iff (W : Set (ι → ℝ)) :
    Set.MapsTo (act A) (S.modelSet W) (S.modelSet W) ↔
      Set.MapsTo (act A) (W ∩ S.πH '' (intLattice ι : Set (ι → ℝ))) W := by
  constructor
  · rintro h _ ⟨hw, γ, hγ, rfl⟩
    have hx : S.πE γ ∈ S.modelSet W := ⟨γ, hγ, hw, rfl⟩
    obtain ⟨γ', hγ', hW', heq⟩ := h hx
    have hAγ := act_mem_intLattice A hγ
    have hd : γ' - act A γ ∈ S.H := by
      have : S.πE (γ' - act A γ) = 0 := by rw [map_sub, heq, S.πE_act, sub_self]
      exact (Submodule.projection_apply_eq_zero_iff S.isCompl).mp this
    have h0 := S.inj _ ((intLattice ι).sub_mem hγ' hAγ) hd
    rw [sub_eq_zero] at h0
    rw [← S.πH_act, ← h0]
    exact hW'
  · rintro h _ ⟨γ, hγ, hW, rfl⟩
    refine ⟨act A γ, act_mem_intLattice A hγ, ?_, S.πE_act γ⟩
    rw [S.πH_act]
    exact h ⟨hW, γ, hγ, rfl⟩

/-- Lattice points of an invariant window stay in the window under all powers of `A`. -/
theorem pow_mem_of_mapsTo {W : Set (ι → ℝ)}
    (h : Set.MapsTo (act A) (W ∩ S.πH '' (intLattice ι : Set (ι → ℝ))) W) (n : ℕ) :
    ∀ γ ∈ intLattice ι, S.πH γ ∈ W → (act A ^ n) (S.πH γ) ∈ W := by
  induction n with
  | zero => intro γ _ hW; simpa using hW
  | succ n ih =>
    intro γ hγ hW
    rw [pow_succ, Module.End.mul_apply, ← S.πH_act]
    refine ih _ (act_mem_intLattice A hγ) ?_
    rw [S.πH_act]
    exact h ⟨hW, γ, hγ, rfl⟩

/-- **Admissible ⇒ power-bounded on `H`.** -/
theorem powerBounded_of_admissible (hS : S.Admissible) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ S.H, ‖(act A ^ n) v‖ ≤ C * ‖v‖ := by
  obtain ⟨W, ⟨hWH, hWb, c, hcH, r, hr, hball⟩, hmaps⟩ := hS
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hWb
  have hlat := (S.mapsTo_modelSet_iff W).mp hmaps
  have hballM : ∀ n : ℕ, ∀ h ∈ S.H, dist h c < r → ‖(act A ^ n) h‖ ≤ M := by
    intro n h hh hd
    have hcl : h ∈ closure (Metric.ball c r ∩ S.πH '' (intLattice ι : Set (ι → ℝ))) :=
      Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball.mpr hd, S.dense hh⟩
    have hcont : Continuous (act A ^ n) := LinearMap.continuous_of_finiteDimensional _
    have hmap : Set.MapsTo (act A ^ n)
        (Metric.ball c r ∩ S.πH '' (intLattice ι : Set (ι → ℝ))) (Metric.closedBall 0 M) := by
      rintro _ ⟨hb, γ, hγ, rfl⟩
      have hγW : S.πH γ ∈ W := hball ⟨hb, S.πH_mem γ⟩
      rw [mem_closedBall_zero_iff]
      exact hM _ (S.pow_mem_of_mapsTo hlat n γ hγ hγW)
    have := map_mem_closure hcont hcl hmap
    rw [Metric.isClosed_closedBall.closure_eq, mem_closedBall_zero_iff] at this
    exact this
  refine ⟨4 * M / r, fun n v hv => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set t : ℝ := r / (2 * ‖v‖) with ht
  have htpos : 0 < t := by positivity
  have hc' : ‖(act A ^ n) c‖ ≤ M := hballM n c hcH (by simpa using hr)
  have htv : t * ‖v‖ = r / 2 := by
    rw [ht, div_mul_eq_mul_div, mul_div_mul_right r 2 hvpos.ne']
  have hct : ‖(act A ^ n) (c + t • v)‖ ≤ M := by
    refine hballM n _ (S.H.add_mem hcH (S.H.smul_mem t hv)) ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le, htv]
    linarith
  have hsplit : (act A ^ n) v = t⁻¹ • ((act A ^ n) (c + t • v) - (act A ^ n) c) := by
    rw [map_add, map_smul, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
  rw [hsplit, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le)]
  calc t⁻¹ * ‖(act A ^ n) (c + t • v) - (act A ^ n) c‖ ≤ t⁻¹ * (M + M) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hct hc'))
          (inv_nonneg.mpr htpos.le)
    _ = 4 * M / r * ‖v‖ := by rw [ht, inv_div]; ring

/-- **Power-bounded ⇒ the orbit window is a compact, convex, symmetric, invariant window whose
model set is invariant.** -/
theorem orbitWindow_spec (h : ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ S.H, ‖(act A ^ n) v‖ ≤ C * ‖v‖) :
    S.IsWindow S.orbitWindow ∧ IsCompact S.orbitWindow ∧ Convex ℝ S.orbitWindow ∧
      (∀ h ∈ S.orbitWindow, -h ∈ S.orbitWindow) ∧
      Set.MapsTo (act A) S.orbitWindow S.orbitWindow ∧
      Set.MapsTo (act A) (S.modelSet S.orbitWindow) (S.modelSet S.orbitWindow) := by
  obtain ⟨C, hC⟩ := h
  have hC1 : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsubH : S.orbitWindow ⊆ S.H := fun h hh => hh.1
  have hnorm : ∀ h ∈ S.orbitWindow, ‖h‖ ≤ 1 := fun h hh => by simpa using hh.2 0
  have hbdd : Bornology.IsBounded S.orbitWindow :=
    (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := 1)).subset
      fun h hh => mem_closedBall_zero_iff.mpr (hnorm h hh)
  have hmaps : Set.MapsTo (act A) S.orbitWindow S.orbitWindow := by
    intro h hh
    refine ⟨S.mapsTo_H h hh.1, fun n => ?_⟩
    have := hh.2 (n + 1)
    rwa [pow_succ, Module.End.mul_apply] at this
  refine ⟨⟨hsubH, hbdd, 0, S.H.zero_mem, 1 / max C 1, one_div_pos.mpr hC1, ?_⟩, ?_, ?_, ?_,
    hmaps, ?_⟩
  · rintro h ⟨hb, hH⟩
    refine ⟨hH, fun n => ?_⟩
    rw [Metric.mem_ball, dist_zero_right] at hb
    calc ‖(act A ^ n) h‖ ≤ C * ‖h‖ := hC n h hH
      _ ≤ max C 1 * ‖h‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max C 1 * (1 / max C 1) := mul_le_mul_of_nonneg_left hb.le hC1.le
      _ = 1 := mul_one_div_cancel hC1.ne'
  · apply Metric.isCompact_of_isClosed_isBounded _ hbdd
    have : S.orbitWindow = (S.H : Set (ι → ℝ)) ∩ ⋂ n : ℕ, {h | ‖(act A ^ n) h‖ ≤ 1} := by
      ext h
      simp [orbitWindow]
    rw [this]
    refine (Submodule.closed_of_finiteDimensional S.H).inter (isClosed_iInter fun n => ?_)
    exact isClosed_le (LinearMap.continuous_of_finiteDimensional _).norm continuous_const
  · intro x hx y hy a b ha hb hab
    refine ⟨S.H.add_mem (S.H.smul_mem a hx.1) (S.H.smul_mem b hy.1), fun n => ?_⟩
    rw [map_add, map_smul, map_smul]
    calc ‖a • (act A ^ n) x + b • (act A ^ n) y‖
        ≤ ‖a • (act A ^ n) x‖ + ‖b • (act A ^ n) y‖ := norm_add_le _ _
      _ = a * ‖(act A ^ n) x‖ + b * ‖(act A ^ n) y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2 n) ha)
            (mul_le_mul_of_nonneg_left (hy.2 n) hb)
      _ = 1 := by rw [mul_one, mul_one, hab]
  · intro h hh
    refine ⟨S.H.neg_mem hh.1, fun n => ?_⟩
    rw [map_neg, norm_neg]
    exact hh.2 n
  · exact (S.mapsTo_modelSet_iff _).mpr (hmaps.mono_left Set.inter_subset_left)

/-- Power-bounded on `H` ⇒ every eigenvalue of `A|_H` lies in the closed unit disk. -/
theorem roots_le_one_of_powerBounded
    (h : ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ S.H, ‖(act A ^ n) v‖ ≤ C * ‖v‖) :
    ∀ z ∈ (((act A).restrict S.mapsTo_H).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := h
  have hC' : ∀ (n : ℕ) (x : S.H), ‖((act A).restrict S.mapsTo_H ^ n) x‖ ≤ C * ‖x‖ := by
    intro n x
    have := hC n x x.2
    rw [← coe_restrict_pow_apply (act A) S.mapsTo_H n x] at this
    exact this
  obtain ⟨K, hK⟩ := entries_bounded_of_powerBounded _ hC'
  have hdisk := norm_le_one_of_pow_bounded _ K hK
  rwa [LinearMap.charpoly_toMatrix] at hdisk

/-- The trivial scheme `(ℝ^ι, 0)`, admissible with the window `{0}`. -/
def trivial (A : Matrix ι ι ℤ) : InvariantCPS A where
  E := ⊤
  H := ⊥
  isCompl := isCompl_top_bot
  mapsTo_E := fun _ _ => Submodule.mem_top
  mapsTo_H := fun v hv => by
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  inj := fun _ _ hγ => (Submodule.mem_bot ℝ).mp hγ
  dense := by
    intro x hx
    have hx0 : x = 0 := (Submodule.mem_bot ℝ).mp hx
    subst hx0
    exact subset_closure ⟨0, (intLattice ι).zero_mem, map_zero _⟩

theorem trivial_admissible (A : Matrix ι ι ℤ) : (InvariantCPS.trivial A).Admissible := by
  refine ⟨{0}, ⟨?_, Bornology.isBounded_singleton, 0, Submodule.zero_mem _, 1, one_pos, ?_⟩, ?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact Submodule.zero_mem _
  · rintro x ⟨_, hx⟩
    exact (Submodule.mem_bot ℝ).mp hx
  · refine ((InvariantCPS.trivial A).mapsTo_modelSet_iff _).mpr ?_
    rintro x ⟨hx, _⟩
    rw [Set.mem_singleton_iff.mp hx, map_zero]
    rfl

end InvariantCPS

theorem physDims_nonempty (A : Matrix ι ι ℤ) : (physDims A).Nonempty :=
  ⟨_, InvariantCPS.trivial A, InvariantCPS.trivial_admissible A, rfl⟩

/-- **Admissibility criterion.** An `A`-invariant scheme is admissible if and only if `A` is
power-bounded on `H`. -/
theorem admissible_iff_powerBounded {A : Matrix ι ι ℤ} (S : InvariantCPS A) :
    S.Admissible ↔ ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ S.H, ‖(act A ^ n) v‖ ≤ C * ‖v‖ :=
  ⟨S.powerBounded_of_admissible, fun h => ⟨_, (S.orbitWindow_spec h).1,
    (S.orbitWindow_spec h).2.2.2.2.2⟩⟩

theorem admissible_of_powerBounded {A : Matrix ι ι ℤ} (S : InvariantCPS A)
    (h : ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ S.H, ‖(act A ^ n) v‖ ≤ C * ‖v‖) :
    S.IsWindow S.orbitWindow ∧
      Set.MapsTo (act A) (S.modelSet S.orbitWindow) (S.modelSet S.orbitWindow) :=
  ⟨(S.orbitWindow_spec h).1, (S.orbitWindow_spec h).2.2.2.2.2⟩

theorem roots_restrict_H_le_one {A : Matrix ι ι ℤ} (S : InvariantCPS A) (hS : S.Admissible) :
    ∀ z ∈ (((act A).restrict S.mapsTo_H).charpoly.map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ 1 :=
  S.roots_le_one_of_powerBounded (S.powerBounded_of_admissible hS)

theorem unstableCount_le_finrank {A : Matrix ι ι ℤ} (S : InvariantCPS A) (hS : S.Admissible) :
    unstableCount A ≤ Module.finrank ℝ S.E := by
  classical
  have hdisk := roots_restrict_H_le_one S hS
  rw [unstableCount_eq_card, charpoly_eq_mul_of_isCompl (act A) S.E S.H S.isCompl S.mapsTo_E
    S.mapsTo_H, Polynomial.map_mul,
    roots_mul (((LinearMap.charpoly_monic _).map _).mul
      ((LinearMap.charpoly_monic _).map _)).ne_zero,
    Multiset.filter_add, Multiset.card_add]
  have hH0 : ((((act A).restrict S.mapsTo_H).charpoly.map (algebraMap ℝ ℂ)).roots.filter
      (fun z => 1 < ‖z‖)) = 0 :=
    Multiset.filter_eq_nil.mpr fun z hz => not_lt.mpr (hdisk z hz)
  rw [hH0, Multiset.card_zero, add_zero]
  calc Multiset.card ((((act A).restrict S.mapsTo_E).charpoly.map (algebraMap ℝ ℂ)).roots.filter
          (fun z => 1 < ‖z‖))
      ≤ Multiset.card (((act A).restrict S.mapsTo_E).charpoly.map (algebraMap ℝ ℂ)).roots :=
        Multiset.card_le_card (Multiset.filter_le _ _)
    _ ≤ (((act A).restrict S.mapsTo_E).charpoly.map (algebraMap ℝ ℂ)).natDegree :=
        card_roots' _
    _ = Module.finrank ℝ S.E := by
      rw [natDegree_map, LinearMap.charpoly_natDegree]

/-- Kronecker's criterion, sufficiency, in cut-and-project form. -/
theorem dense_of_no_integral_functional {E H : Submodule ℝ (ι → ℝ)} (hc : IsCompl E H)
    (h : ∀ f : (ι → ℝ) →ₗ[ℝ] ℝ, (∀ γ ∈ intLattice ι, ∃ n : ℤ, f γ = n) →
      (∀ v ∈ E, f v = 0) → f = 0) :
    (H : Set (ι → ℝ)) ⊆ closure (H.projection E hc.symm '' (intLattice ι : Set (ι → ℝ))) := by
  intro x hx
  have hd := dense_sup_of_no_integral_functional (intLattice ι) span_intLattice E h
  set P : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := H.projection E hc.symm with hP
  have hPc : Continuous P := LinearMap.continuous_of_finiteDimensional P
  have hPx : P x = x := Submodule.projection_apply_of_mem_left _ hx
  have hmaps : Set.MapsTo P ((intLattice ι).toAddSubgroup ⊔ E.toAddSubgroup : AddSubgroup _)
      (P '' (intLattice ι : Set (ι → ℝ))) := by
    intro g hg
    obtain ⟨γ, hγ, e, he, rfl⟩ := AddSubgroup.mem_sup.mp hg
    refine ⟨γ, hγ, ?_⟩
    have hPe : P e = 0 := Submodule.projection_apply_of_mem_right _ (by exact he)
    rw [map_add, hPe, add_zero]
  have := map_mem_closure hPc (hd x) hmaps
  rwa [hPx] at this

end Lattice

/-! ### The compared statements -/

/-- **(1) Admissibility criterion.** -/
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
  refine ⟨admissible_iff_powerBounded S, S.orbitWindow_spec, S.mapsTo_modelSet_iff,
    fun W hWc hWd => ?_, fun hS => ⟨roots_restrict_H_le_one S hS, unstableCount_le_finrank S hS⟩⟩
  rw [S.mapsTo_modelSet_iff]
  constructor
  · intro h w hw
    have hcont : Continuous (act A) := LinearMap.continuous_of_finiteDimensional _
    have := map_mem_closure hcont (hWd hw) h
    rwa [hWc.closure_eq] at this
  · intro h
    exact h.mono_left Set.inter_subset_left

/-- **(2) Kronecker's density criterion**, cut-and-project form. -/
theorem kronecker_density_criterion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E H : Submodule ℝ (ι → ℝ)) (hc : IsCompl E H) :
    (H : Set (ι → ℝ)) ⊆ closure (H.projection E hc.symm '' (intLattice ι : Set (ι → ℝ))) ↔
      ∀ f : (ι → ℝ) →ₗ[ℝ] ℝ, (∀ γ ∈ intLattice ι, ∃ n : ℤ, f γ = n) →
        (∀ v ∈ E, f v = 0) → f = 0 :=
  ⟨fun h => no_integral_functional_of_dense_sup (intLattice ι) E
      (dense_sup_of_dense_projection (intLattice ι) hc h),
    dense_of_no_integral_functional hc⟩

end

end InflationDimension
