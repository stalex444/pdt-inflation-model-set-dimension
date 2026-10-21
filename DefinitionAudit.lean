module
public import Mathlib

@[expose] public section
/-!
# Audit of the imported definitions

The compared statements in `Challenge.lean` rest on definitions imported from Mathlib (pinned
revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`): the matrix action `Matrix.toLin'`, the
standard basis `Pi.basisFun` and `Submodule.span`, the projection `Submodule.projection` along a
complement, the sup norm on `ι → ℝ`, `Matrix.charpoly` and `LinearMap.charpoly`, `Matrix.det` and
`LinearMap.det`, `Polynomial.roots`, `UniqueFactorizationMonoid.normalizedFactors`,
`Polynomial.cyclotomic`, `Squarefree`, the Kronecker product `⊗ₖ` (`Matrix.kroneckerMap`),
`Matrix.toQuadraticForm'`, `dotProduct` and `Matrix.mulVec`, the signature `sigPos`/`sigNeg`,
`Delone.DeloneSet`, `segment`, `IsLeast`, `IsCompl` and the pointwise difference of sets. Their
pinned source text is quoted verbatim, with permalinks, in `MATHLIB_DEFINITIONS.md`. This file
imports Mathlib only and is not part of the compared set. It records, as kernel-checked theorems,
the facts about those definitions that the informal account relies on, so that the
correspondence can be audited from this repository alone:

* `toLin'_apply`, `toLin'_single` — `Matrix.toLin' M v = M *ᵥ v`, and the image of the `j`-th
  standard basis vector is the `j`-th column: the entry's `act A` is the usual action of the
  integer matrix `A` on column vectors.
* `mem_span_basisFun_iff` — the `ℤ`-span of the standard basis of `ℝ^ι` is the set of vectors
  with integer coordinates: the entry's `intLattice ι` is `ℤ^ι`.
* `norm_le_iff` — the norm on `ℝ^ι` is the sup norm (the orbit window of statement 1).
* `projection_add_projection`, `projection_mem`, `projection_of_mem`, `projection_of_mem_compl` —
  `E.projection H h` is the projection onto `E` along `H`: `x = π_E x + π_H x`, `π_E x ∈ E`, `π_E`
  fixes `E` and kills `H`.
* `isCompl_iff` — `IsCompl E H` means `E ∩ H = 0` and `E + H` is everything.
* `charpoly_eq_det`, `charpoly_fin_two`, `charpoly_map` — `χ_M = det(X·1 − M)` (the usual sign
  convention: monic); on `2 × 2` matrices `χ = X² − (a + d)X + (ad − bc)`; and the characteristic
  polynomial of the complexified integer matrix is the complexified integer characteristic
  polynomial, so the entry's `eigenvalues A` are the complex eigenvalues of `A`.
* `charpoly_toMatrix`, `det_toMatrix` — `LinearMap.charpoly` and `LinearMap.det` are those of the
  matrix in any basis (the restrictions `A|_E`, `A|_H` in statements 1, 3 and 11).
* `roots_X_sub_C_sq` — `Polynomial.roots` counts multiplicity (`unstableCount` counts eigenvalues
  with multiplicity).
* `irreducible_of_mem_normalizedFactors`, `monic_of_mem_normalizedFactors`,
  `prod_normalizedFactors` — the normalized factors of a nonzero rational polynomial are its monic
  irreducible factors with multiplicity, and their product is the polynomial up to a unit
  (`circleCount`, and the factor conditions of statements 3, 5 and 6).
* `cyclotomic_one`, `cyclotomic_two` — `Φ₁ = X − 1` and `Φ₂ = X + 1` (statement 6).
* `squarefree_iff` — the definition of `Squarefree` (`Iff.rfl`).
* `kronecker_apply` — `(A ⊗ₖ B)_{(i,k),(j,l)} = A_{ij} B_{kl}` (`mulMatrix`, `mulρ`, ... and
  `GramRho ⊗ₖ GramQ`).
* `toQuadraticForm'_apply`, `dotProduct_mulVec` — `Matrix.toQuadraticForm' M` is
  `c ↦ Σ_{i,j} M_{ij} c_i c_j`, and `x ⬝ᵥ (M *ᵥ y) = Σ_{i,j} x_i M_{ij} y_j` (`formOf`, `pairing`).
* `sigNeg_eq_sigPos_neg`, `sigPos_eq_card_pos_weights`, `sigNeg_eq_card_neg_weights`,
  `sigPos_x_sq_sub_y_sq`, `sigNeg_x_sq_sub_y_sq` — the sign convention, Sylvester's law (the
  counts of positive and negative weights of any diagonalization) and non-vacuity.
* `deloneSet_separated`, `deloneSet_cover` — a `Delone.DeloneSet` is uniformly discrete (distinct
  points at distance more than the packing radius) and relatively dense (every point within the
  covering radius of the set), the two halves of statement 13.
* `segment_eq_image` — `segment ℝ a b` is the closed segment `{a + t (b − a) : t ∈ [0, 1]}`
  (statement 11).
* `isLeast_iff` (`Iff.rfl`) — `IsLeast s a`: `a ∈ s` and `a ≤ b` for every `b ∈ s` (the least
  physical dimension).
* `mem_sub` — `x ∈ s − t` iff `x = a − b` with `a ∈ s`, `b ∈ t` (statement 13).

Each theorem is `rfl`/`Iff.rfl` (the docstring says so), a restatement of the named Mathlib
theorem, or a short derivation from Mathlib theorems; none uses anything from this entry.
-/

namespace DefinitionAudit

open Polynomial Module

/-- `Matrix.toLin' M` is `v ↦ M *ᵥ v` (Mathlib's `Matrix.toLin'_apply`, restated). -/
theorem toLin'_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    Matrix.toLin' M v = M.mulVec v :=
  Matrix.toLin'_apply M v

/-- The action of an integer matrix on the `j`-th standard basis vector is its `j`-th column. -/
theorem toLin'_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) (j : ι) :
    Matrix.toLin' (A.map (Int.cast : ℤ → ℝ)) (Pi.single j 1) = fun i => (A i j : ℝ) := by
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

/-- The `ℤ`-span of the standard basis of `ℝ^ι` is the set of vectors with integer coordinates. -/
theorem mem_span_basisFun_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    v ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ ∀ i, ∃ n : ℤ, v i = n := by
  rw [(Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ]
  simp only [Pi.basisFun_repr, Set.mem_range, algebraMap_int_eq, eq_intCast]
  exact forall_congr' fun i => ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩

/-- The norm on `ℝ^ι` is the sup norm (Mathlib's `pi_norm_le_iff_of_nonneg`, restated). -/
theorem norm_le_iff {ι : Type*} [Fintype ι] (v : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ‖v‖ ≤ r ↔ ∀ i, |v i| ≤ r := by
  rw [pi_norm_le_iff_of_nonneg hr]
  simp only [Real.norm_eq_abs]

/-- `π_E x + π_H x = x` (Mathlib's `Submodule.projection_add_projection_eq_self`). -/
theorem projection_add_projection {V : Type*} [AddCommGroup V] [Module ℝ V]
    {E H : Submodule ℝ V} (h : IsCompl E H) (x : V) :
    E.projection H h x + H.projection E h.symm x = x :=
  Submodule.projection_add_projection_eq_self h x

/-- `π_E x ∈ E` (Mathlib's `Submodule.projection_apply_mem`). -/
theorem projection_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    {E H : Submodule ℝ V} (h : IsCompl E H) (x : V) : E.projection H h x ∈ E :=
  Submodule.projection_apply_mem h x

/-- `π_E` fixes `E` (Mathlib's `Submodule.projection_apply_of_mem_left`). -/
theorem projection_of_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    {E H : Submodule ℝ V} (h : IsCompl E H) {x : V} (hx : x ∈ E) : E.projection H h x = x :=
  Submodule.projection_apply_of_mem_left h hx

/-- `π_E` kills the complement `H`. -/
theorem projection_of_mem_compl {V : Type*} [AddCommGroup V] [Module ℝ V]
    {E H : Submodule ℝ V} (h : IsCompl E H) {x : V} (hx : x ∈ H) : E.projection H h x = 0 := by
  have h1 := Submodule.projection_add_projection_eq_self h x
  rw [Submodule.projection_apply_of_mem_left h.symm hx] at h1
  simpa using h1

/-- `IsCompl E H` means `E ⊓ H = ⊥` and `E ⊔ H = ⊤`. -/
theorem isCompl_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (E H : Submodule ℝ V) :
    IsCompl E H ↔ E ⊓ H = ⊥ ∧ E ⊔ H = ⊤ := by
  rw [_root_.isCompl_iff, disjoint_iff, codisjoint_iff]

/-- `χ_M = det(X·1 − M)`, by definition (`rfl`). -/
theorem charpoly_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) :
    M.charpoly = M.charmatrix.det := rfl

/-- On `2 × 2` matrices, `χ = X² − (a + d) X + (ad − bc)` (Mathlib's `Matrix.charpoly_fin_two`):
the characteristic polynomial is monic, with the usual sign. -/
theorem charpoly_fin_two (a b c d : ℤ) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ).charpoly =
      X ^ 2 - C (a + d) * X + C (a * d - b * c) := by
  rw [Matrix.charpoly_fin_two]
  simp

/-- The characteristic polynomial commutes with a change of coefficient ring (Mathlib's
`Matrix.charpoly_map`): the roots of `χ_A` mapped to `ℂ` are the complex eigenvalues of `A`. -/
theorem charpoly_map {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℤ) :
    (A.map (Int.castRingHom ℂ)).charpoly = A.charpoly.map (Int.castRingHom ℂ) :=
  Matrix.charpoly_map A (Int.castRingHom ℂ)

/-- `LinearMap.charpoly f` is the characteristic polynomial of the matrix of `f` in any basis
(Mathlib's `LinearMap.charpoly_toMatrix`). -/
theorem charpoly_toMatrix {V ι : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι] [DecidableEq ι] (f : V →ₗ[ℝ] V) (b : Basis ι ℝ V) :
    (LinearMap.toMatrix b b f).charpoly = f.charpoly :=
  LinearMap.charpoly_toMatrix f b

/-- `LinearMap.det f` is the determinant of the matrix of `f` in any basis (Mathlib's
`LinearMap.det_toMatrix`). -/
theorem det_toMatrix {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ V) (f : V →ₗ[ℝ] V) : (LinearMap.toMatrix b b f).det = LinearMap.det f :=
  LinearMap.det_toMatrix b f

/-- `Polynomial.roots` counts multiplicity: the root multiset of `(X − 1)²` is `{1, 1}`. -/
theorem roots_X_sub_C_sq : ((X - C (1 : ℂ)) ^ 2).roots = {1, 1} := by
  rw [roots_pow, roots_X_sub_C]
  rfl

/-- The normalized factors are irreducible (Mathlib's
`UniqueFactorizationMonoid.irreducible_of_normalized_factor`). -/
theorem irreducible_of_mem_normalizedFactors {f p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors f) : Irreducible p :=
  UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp

/-- The normalized factors of a rational polynomial are monic. -/
theorem monic_of_mem_normalizedFactors {f p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors f) : p.Monic := by
  classical
  have h0 : p ≠ 0 := (irreducible_of_mem_normalizedFactors hp).ne_zero
  rw [← UniqueFactorizationMonoid.normalize_normalized_factor p hp]
  exact Polynomial.monic_normalize h0

/-- The product of the normalized factors of a nonzero polynomial is the polynomial, up to a unit
(Mathlib's `UniqueFactorizationMonoid.prod_normalizedFactors`). -/
theorem prod_normalizedFactors {f : ℚ[X]} (hf : f ≠ 0) :
    Associated (UniqueFactorizationMonoid.normalizedFactors f).prod f :=
  UniqueFactorizationMonoid.prod_normalizedFactors hf

/-- `Φ₁ = X − 1` (Mathlib's `Polynomial.cyclotomic_one`). -/
theorem cyclotomic_one : cyclotomic 1 ℚ = X - 1 := Polynomial.cyclotomic_one ℚ

/-- `Φ₂ = X + 1` (Mathlib's `Polynomial.cyclotomic_two`). -/
theorem cyclotomic_two : cyclotomic 2 ℚ = X + 1 := Polynomial.cyclotomic_two ℚ

/-- `Squarefree r`: every `x` with `x * x ∣ r` is a unit (`Iff.rfl`). -/
theorem squarefree_iff {R : Type*} [Monoid R] (r : R) :
    Squarefree r ↔ ∀ x : R, x * x ∣ r → IsUnit x := Iff.rfl

open scoped Kronecker in
/-- The Kronecker product: `(A ⊗ₖ B)_{(i,k),(j,l)} = A_{ij} B_{kl}` (`rfl`). -/
theorem kronecker_apply {l m n p : Type*} (A : Matrix l m ℤ) (B : Matrix n p ℤ) (i : l) (j : m)
    (k : n) (r : p) : (A ⊗ₖ B) (i, k) (j, r) = A i j * B k r := rfl

/-- `Matrix.toQuadraticForm' M` is `c ↦ Σ_i Σ_j M_{ij} c_i c_j`; a short derivation from the
definitions of `toQuadraticForm'`, `toQuadraticMap` and `Matrix.toLinearMap₂'`. -/
theorem toQuadraticForm'_apply {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (c : n → ℝ) : M.toQuadraticForm' c = ∑ i, ∑ j, M i j * c i * c j := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `x ⬝ᵥ (M *ᵥ y) = Σ_i Σ_j x_i M_{ij} y_j`. -/
theorem dotProduct_mulVec {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x y : n → ℝ) :
    x ⬝ᵥ M.mulVec y = ∑ i, ∑ j, x i * M i j * y j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The sign convention: `sigNeg Q = sigPos (-Q)` (Mathlib's `sigPos_neg`, restated). -/
theorem sigNeg_eq_sigPos_neg {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) : sigNeg Q = sigPos (-Q) := sigPos_neg.symm

/-- Sylvester's law of inertia, uniqueness half (Mathlib's
`QuadraticForm.sigPos_of_equiv_weightedSumSquares`, restated over `ℝ`): `sigPos` is the number of
positive weights in ANY diagonalization. -/
theorem sigPos_eq_card_pos_weights {M ι : Type*} [AddCommGroup M] [Module ℝ M] [Fintype ι]
    {Q : QuadraticForm ℝ M} {w : ι → ℝ}
    (hQ : QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w)) :
    sigPos Q = {i | 0 < w i}.ncard :=
  QuadraticForm.sigPos_of_equiv_weightedSumSquares hQ

/-- The same for `sigNeg`, which counts the negative weights (Mathlib's
`QuadraticForm.sigNeg_of_equiv_weightedSumSquares`, restated). -/
theorem sigNeg_eq_card_neg_weights {M ι : Type*} [AddCommGroup M] [Module ℝ M] [Fintype ι]
    {Q : QuadraticForm ℝ M} {w : ι → ℝ}
    (hQ : QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w)) :
    sigNeg Q = {i | w i < 0}.ncard :=
  QuadraticForm.sigNeg_of_equiv_weightedSumSquares hQ

/-- Non-vacuity: the form `x² − y²` on `ℝ²` has `sigPos = 1`. -/
theorem sigPos_x_sq_sub_y_sq :
    sigPos (QuadraticMap.weightedSumSquares ℝ ![(1 : ℝ), -1]) = 1 := by
  rw [QuadraticForm.sigPos_weightedSumSquares]
  have : {i : Fin 2 | 0 < (![(1 : ℝ), -1] : Fin 2 → ℝ) i} = {0} := by
    ext i; fin_cases i <;> simp
  rw [this, Set.ncard_singleton]

/-- Non-vacuity: the form `x² − y²` on `ℝ²` has `sigNeg = 1`. -/
theorem sigNeg_x_sq_sub_y_sq :
    sigNeg (QuadraticMap.weightedSumSquares ℝ ![(1 : ℝ), -1]) = 1 := by
  rw [QuadraticForm.sigNeg_weightedSumSquares]
  have : {i : Fin 2 | (![(1 : ℝ), -1] : Fin 2 → ℝ) i < 0} = {1} := by
    ext i; fin_cases i <;> simp
  rw [this, Set.ncard_singleton]

/-- A Delone set is uniformly discrete: distinct points are farther apart than the packing radius
(Mathlib's `Delone.DeloneSet.packingRadius_lt_dist_of_mem_ne`). -/
theorem deloneSet_separated {X : Type*} [MetricSpace X] (D : Delone.DeloneSet X) {x y : X}
    (hx : x ∈ (D : Set X)) (hy : y ∈ (D : Set X)) (hne : x ≠ y) :
    (D.packingRadius : ℝ) < dist x y :=
  D.packingRadius_lt_dist_of_mem_ne hx hy hne

/-- A Delone set is relatively dense: every point lies within the covering radius of the set
(Mathlib's `Delone.DeloneSet.exists_dist_le_coveringRadius`). -/
theorem deloneSet_cover {X : Type*} [MetricSpace X] (D : Delone.DeloneSet X) (x : X) :
    ∃ y ∈ (D : Set X), dist x y ≤ D.coveringRadius :=
  D.exists_dist_le_coveringRadius x

/-- `segment ℝ a b = {a + t (b − a) : t ∈ [0, 1]}` (Mathlib's `segment_eq_image'`). -/
theorem segment_eq_image {n : Type*} (a b : n → ℝ) :
    segment ℝ a b = (fun t : ℝ => a + t • (b - a)) '' Set.Icc 0 1 :=
  segment_eq_image' ℝ a b

/-- `IsLeast s a`: `a ∈ s` and `a` is a lower bound of `s` (`Iff.rfl`). -/
theorem isLeast_iff (s : Set ℕ) (a : ℕ) : IsLeast s a ↔ a ∈ s ∧ ∀ b ∈ s, a ≤ b := Iff.rfl

open scoped Pointwise in
/-- The pointwise difference of sets (Mathlib's `Set.mem_sub`). -/
theorem mem_sub {n : Type*} (s t : Set (n → ℝ)) (x : n → ℝ) :
    x ∈ s - t ↔ ∃ a ∈ s, ∃ b ∈ t, a - b = x := Set.mem_sub

end DefinitionAudit
