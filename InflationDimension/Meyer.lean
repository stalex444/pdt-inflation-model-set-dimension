module
public import Mathlib
public import InflationDimension.Defs

@[expose] public section
/-!
# Model sets are Meyer sets

For an `A`-invariant cut-and-project scheme on `ℤ^ι` and a window `W` (a bounded subset of the
internal space `H` containing a relative ball of `H`), the model set `Λ(W)` is a Delone set in the
physical space `E` and `Λ(W) − Λ(W)` is uniformly discrete: `Λ(W)` is a Meyer set.

* Uniform discreteness: a difference of two points of `Λ(W) − Λ(W)` is `π_E δ` for a lattice
  point `δ` with `π_H δ` bounded. Only finitely many lattice points have both projections
  bounded, so the positive values of `‖π_E δ‖` below `1` have a positive minimum.
* Relative density: round `x + c` (`x ∈ E`, `c` the centre of the relative ball in the window) to
  a lattice point, then correct its internal coordinate by one of finitely many lattice points
  whose internal projections cover a compact piece of `H` by balls of the window's radius.
-/

namespace InflationDimension

open Metric
open scoped Pointwise NNReal

noncomputable section

namespace Meyer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A linear endomorphism of `ℝ^ι` is bounded. -/
theorem exists_bound (f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : ∃ C, 0 < C ∧ ∀ v, ‖f v‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC, h⟩ := (LinearMap.toContinuousLinearMap f).bound
  exact ⟨C, hC, fun v => by simpa using h v⟩

/-- A finite set of points at which a real function is positive carries a positive lower bound
of the function. -/
theorem exists_pos_le_of_finite {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) : ∃ r > 0, ∀ a ∈ s, r ≤ f a := by
  classical
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a t ha ih =>
    obtain ⟨r, hr, h⟩ := ih (Set.toFinite _)
      (fun b hb => hf b (by simp only [Finset.coe_insert]; exact Set.mem_insert_of_mem _ hb))
    have hfa : 0 < f a := hf a (by simp)
    refine ⟨min (f a) r, lt_min hfa hr, fun b hb => ?_⟩
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hb
    rcases hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (h b hb)

variable {A : Matrix ι ι ℤ} (S : InvariantCPS A)

theorem πE_add_πH (v : ι → ℝ) : S.πE v + S.πH v = v :=
  Submodule.projection_add_projection_eq_self S.isCompl v

theorem πE_mem (v : ι → ℝ) : S.πE v ∈ S.E := Submodule.projection_apply_mem _ v

theorem πH_mem (v : ι → ℝ) : S.πH v ∈ S.H := Submodule.projection_apply_mem _ v

theorem πE_of_mem_E {v : ι → ℝ} (hv : v ∈ S.E) : S.πE v = v :=
  Submodule.projection_apply_of_mem_left _ hv

theorem πE_of_mem_H {v : ι → ℝ} (hv : v ∈ S.H) : S.πE v = 0 :=
  Submodule.projection_apply_of_mem_right _ hv

theorem πH_of_mem_H {v : ι → ℝ} (hv : v ∈ S.H) : S.πH v = v :=
  Submodule.projection_apply_of_mem_left _ hv

theorem πH_of_mem_E {v : ι → ℝ} (hv : v ∈ S.E) : S.πH v = 0 :=
  Submodule.projection_apply_of_mem_right _ hv

/-- Lattice points with bounded internal projection have physical projections bounded away
from `0`, unless the physical projection vanishes. -/
theorem exists_sep (R : ℝ) : ∃ r > 0, ∀ δ ∈ intLattice ι, ‖S.πH δ‖ ≤ R → S.πE δ ≠ 0 →
    r ≤ ‖S.πE δ‖ := by
  classical
  set F : Set (ι → ℝ) :=
    (closedBall 0 (1 + R) ∩ (intLattice ι : Set (ι → ℝ))) ∩ {δ | S.πE δ ≠ 0}
  have hF : F.Finite :=
    (ZSpan.setFinite_inter (Pi.basisFun ℝ ι) isBounded_closedBall).subset Set.inter_subset_left
  obtain ⟨r, hr, h⟩ :=
    exists_pos_le_of_finite hF (fun δ => ‖S.πE δ‖) (fun δ hδ => norm_pos_iff.2 hδ.2)
  refine ⟨min r 1, lt_min hr one_pos, fun δ hδ hH hE => ?_⟩
  by_cases h1 : ‖S.πE δ‖ ≤ 1
  · have hmem : δ ∈ F := by
      refine ⟨⟨?_, hδ⟩, hE⟩
      rw [mem_closedBall, dist_zero_right]
      calc ‖δ‖ = ‖S.πE δ + S.πH δ‖ := by rw [πE_add_πH]
        _ ≤ ‖S.πE δ‖ + ‖S.πH δ‖ := norm_add_le _ _
        _ ≤ 1 + R := add_le_add h1 hH
    exact (min_le_left _ _).trans (h δ hmem)
  · exact (min_le_right _ _).trans (le_of_lt (not_le.1 h1))

/-- A point of `Λ(W) − Λ(W)` is the physical projection of a lattice point whose internal
projection has norm at most twice a bound for `W`. -/
theorem mem_sub_modelSet {W : Set (ι → ℝ)} {R : ℝ} (hR : ∀ w ∈ W, ‖w‖ ≤ R) {x : ι → ℝ}
    (hx : x ∈ S.modelSet W - S.modelSet W) :
    ∃ γ ∈ intLattice ι, ‖S.πH γ‖ ≤ 2 * R ∧ S.πE γ = x := by
  rw [Set.mem_sub] at hx
  obtain ⟨_, ⟨γ₁, h₁, hW₁, rfl⟩, _, ⟨γ₂, h₂, hW₂, rfl⟩, rfl⟩ := hx
  refine ⟨γ₁ - γ₂, sub_mem h₁ h₂, ?_, map_sub _ _ _⟩
  rw [map_sub]
  calc ‖S.πH γ₁ - S.πH γ₂‖ ≤ ‖S.πH γ₁‖ + ‖S.πH γ₂‖ := norm_sub_le _ _
    _ ≤ R + R := add_le_add (hR _ hW₁) (hR _ hW₂)
    _ = 2 * R := by ring

/-- Relative density: every point of `E` lies within a fixed distance of `Λ(W)`. -/
theorem exists_cover {W : Set (ι → ℝ)} (hW : S.IsWindow W) :
    ∃ C > (0 : ℝ), ∀ x ∈ S.E, ∃ γ ∈ intLattice ι, S.πH γ ∈ W ∧ ‖x - S.πE γ‖ ≤ C := by
  obtain ⟨_, _, c, hcH, r₀, hr₀, hball⟩ := hW
  set b := Pi.basisFun ℝ ι
  obtain ⟨CE, hCE, hπE⟩ := exists_bound S.πE
  obtain ⟨CH, hCH, hπH⟩ := exists_bound S.πH
  set R₀ : ℝ := ∑ i, ‖b i‖
  have hR₀0 : 0 ≤ R₀ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  set K₁ : Set (ι → ℝ) := closedBall 0 (CH * R₀) ∩ (S.H : Set (ι → ℝ))
  have hK₁ : IsCompact K₁ :=
    (isCompact_closedBall 0 _).inter_right (Submodule.closed_of_finiteDimensional S.H)
  have hcov : K₁ ⊆ ⋃ δ : intLattice ι, ball (S.πH δ) r₀ := by
    rintro h ⟨_, hh⟩
    obtain ⟨_, ⟨δ, hδ, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 (S.dense hh) r₀ hr₀
    exact Set.mem_iUnion.2 ⟨⟨δ, hδ⟩, by rw [mem_ball]; exact hd⟩
  obtain ⟨t, ht⟩ :=
    hK₁.elim_finite_subcover (fun δ : intLattice ι => ball (S.πH δ) r₀) (fun _ => isOpen_ball) hcov
  set M : ℝ := ∑ δ ∈ t, ‖S.πE (δ : ι → ℝ)‖
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : ∀ δ ∈ t, ‖S.πE (δ : ι → ℝ)‖ ≤ M := fun δ hδ =>
    Finset.single_le_sum (f := fun δ : intLattice ι => ‖S.πE (δ : ι → ℝ)‖)
      (fun _ _ => norm_nonneg _) hδ
  refine ⟨CE * R₀ + M + 1, by positivity, fun x hx => ?_⟩
  set v := x + c
  set γ₀ : ι → ℝ := (ZSpan.floor b v : ι → ℝ)
  have hγ₀ : γ₀ ∈ intLattice ι := (ZSpan.floor b v).2
  have hv : ‖γ₀ - v‖ ≤ R₀ := by
    rw [norm_sub_rev, ← ZSpan.fract_apply]
    exact ZSpan.norm_fract_le b v
  have hπHv : S.πH v = c := by
    rw [map_add, πH_of_mem_E S hx, πH_of_mem_H S hcH, zero_add]
  have hπEv : S.πE v = x := by
    rw [map_add, πE_of_mem_E S hx, πE_of_mem_H S hcH, add_zero]
  set h := S.πH γ₀ - c
  have hhK : h ∈ K₁ := by
    refine ⟨?_, sub_mem (πH_mem S γ₀) hcH⟩
    rw [mem_closedBall, dist_zero_right]
    have : h = S.πH (γ₀ - v) := by rw [map_sub, hπHv]
    rw [this]
    exact (hπH _).trans (mul_le_mul_of_nonneg_left hv hCH.le)
  obtain ⟨δ, hδt, hδ⟩ := Set.mem_iUnion₂.1 (ht hhK)
  rw [mem_ball] at hδ
  refine ⟨γ₀ - δ, sub_mem hγ₀ δ.2, hball ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, map_sub, dist_eq_norm]
    have : S.πH γ₀ - S.πH δ - c = h - S.πH δ := by simp only [h]; abel
    rw [this, ← dist_eq_norm]
    exact hδ
  · rw [map_sub]
    exact sub_mem (πH_mem S γ₀) (πH_mem S δ)
  · have : x - S.πE (γ₀ - δ) = -S.πE (γ₀ - v) + S.πE δ := by
      rw [map_sub, map_sub, hπEv]; abel
    rw [this]
    calc ‖-S.πE (γ₀ - v) + S.πE δ‖ ≤ ‖-S.πE (γ₀ - v)‖ + ‖S.πE δ‖ := norm_add_le _ _
      _ = ‖S.πE (γ₀ - v)‖ + ‖S.πE δ‖ := by rw [norm_neg]
      _ ≤ CE * R₀ + M := add_le_add ((hπE _).trans (mul_le_mul_of_nonneg_left hv hCE.le))
          (hM δ hδt)
      _ ≤ CE * R₀ + M + 1 := by linarith

end Meyer

open Meyer in
/-- **Model sets are Meyer sets.** For every `A`-invariant scheme on `ℤ^ι` and every window `W`,
`Λ(W)` is a Delone set in `E` and `Λ(W) − Λ(W)` is uniformly discrete. This is the classical
fact that model sets are Meyer sets (Y. Meyer, *Algebraic Numbers and Harmonic Analysis*, 1972;
R. V. Moody, "Meyer sets and their duals", 1997). -/
theorem modelSet_isMeyer {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ)
    (S : InvariantCPS A) (W : Set (ι → ℝ)) (hW : S.IsWindow W) :
    (∃ D : Delone.DeloneSet S.E, (D : Set S.E) = Subtype.val ⁻¹' S.modelSet W) ∧
    ∃ r > (0 : ℝ), ∀ x ∈ S.modelSet W - S.modelSet W, ∀ y ∈ S.modelSet W - S.modelSet W,
      x ≠ y → r ≤ dist x y := by
  obtain ⟨C, hC, hcover⟩ := exists_cover S hW
  obtain ⟨_, hWb, c, hcH, r₀, hr₀, hball⟩ := hW
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hWb
  have hR0 : 0 ≤ R := (norm_nonneg c).trans (hR c (hball ⟨mem_ball_self hr₀, hcH⟩))
  obtain ⟨r, hr, hsep⟩ := exists_sep S (4 * R)
  refine ⟨⟨{ carrier := Subtype.val ⁻¹' S.modelSet W
             packingRadius := Real.toNNReal (r / 2)
             packingRadius_pos := Real.toNNReal_pos.2 (half_pos hr)
             isSeparated_packingRadius := ?_
             coveringRadius := Real.toNNReal C
             coveringRadius_pos := Real.toNNReal_pos.2 hC
             isCover_coveringRadius := ?_ }, rfl⟩, r, hr, ?_⟩
  · intro x hx y hy hne
    have hne' : (x : ι → ℝ) ≠ y := fun h => hne (Subtype.ext h)
    obtain ⟨γ, hγ, hγH, hγE⟩ := mem_sub_modelSet S hR (Set.sub_mem_sub hx hy)
    have key := hsep γ hγ (by linarith) (by rw [hγE]; exact sub_ne_zero.2 hne')
    rw [hγE, ← dist_eq_norm, ← Subtype.dist_eq] at key
    rw [edist_dist]
    change ENNReal.ofReal (r / 2) < _
    rw [ENNReal.ofReal_lt_ofReal_iff (dist_pos.2 hne)]
    exact (half_lt_self hr).trans_le key
  · rw [isCover_iff_subset_iUnion_closedBall]
    intro x _
    obtain ⟨γ, hγ, hγW, hγx⟩ := hcover x x.2
    refine Set.mem_iUnion₂.2 ⟨⟨S.πE γ, πE_mem S γ⟩, ⟨γ, hγ, hγW, rfl⟩, ?_⟩
    rw [mem_closedBall, Subtype.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC.le]
    exact hγx
  · intro x hx y hy hxy
    obtain ⟨γ, hγ, hγH, rfl⟩ := mem_sub_modelSet S hR hx
    obtain ⟨γ', hγ', hγ'H, rfl⟩ := mem_sub_modelSet S hR hy
    have hH : ‖S.πH (γ - γ')‖ ≤ 4 * R := by
      rw [map_sub]
      calc ‖S.πH γ - S.πH γ'‖ ≤ ‖S.πH γ‖ + ‖S.πH γ'‖ := norm_sub_le _ _
        _ ≤ 2 * R + 2 * R := add_le_add hγH hγ'H
        _ = 4 * R := by ring
    have key := hsep (γ - γ') (sub_mem hγ hγ') hH (by rw [map_sub]; exact sub_ne_zero.2 hxy)
    rwa [map_sub, ← dist_eq_norm] at key

end

end InflationDimension
