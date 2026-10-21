module
public import Mathlib
public import InflationDimension.Hyperbolic
public import InflationDimension.Compositum.Tower
public import InflationDimension.Compositum.CircleFree

@[expose] public section
/-!
# The instances: the sector rings and the degree-12 lattice `ℤ[ρ] ⊗ ℤ[Q]`

Statements (8), (9), (10) of `Challenge.lean`, at the level of explicit integer matrices.

* The roots. `ρ ≈ 1.32472`, `Q ≈ 1.22074` and `q′ ≈ −0.72449` are located in rational boxes by
  the intermediate value theorem; the non-real roots are written down from the real quadratic
  factors (`x³ − x − 1 = (x − ρ)(x² + ρx + ρ² − 1)`,
  `x⁴ − x − 1 = (x − Q)(x − q′)(x² + sx + s² − Qq′)`, `s = Q + q′`), so `|z|² = ρ² − 1` and
  `|w|² = s² − Qq′`. Every modulus comparison is a polynomial inequality on the boxes.
* The spectra. The Vandermonde matrices `V₃`, `V₄` of the roots intertwine `Cρ`, `CQ` with the
  diagonal matrices of the roots (`(1, z, z²)` is a left eigenvector of `Cρ` for `z`), and
  `V₃ ⊗ V₄` intertwines every `mulMatrix a` with the diagonal matrix of the values
  `α(z, w) = Σ a(i,j) z^i w^j` (`V12_mulMatrix`). The eigenvalues, `U`, the determinants and
  hyperbolicity are read off from these.
* (9), general part: for each pair of roots `(z, w)` there is a ring map `L → ℂ` from the field
  `L = ℚ(ρ)[Y]/(Y⁴ − Y − 1)` sending `ρ ↦ z`, `Q ↦ w`, so `α(z, w)` is a conjugate of
  `β = Σ a(i,j) ρ^i Q^j ∈ L`. The field `L` is circle-free (an element with a conjugate on the unit
  circle is `±1`; ported from the author's registered entry PALOMAR-2026-10-21-000012,
  stalex444/pdt-hermite-signature-compositum@5aa870e8, see
  `InflationDimension.Compositum.CircleFree`), and `β = c ∈ ℤ` forces `a = c · e₀₀` because
  `V₃ ⊗ V₄` is invertible.
* (10): the spectral projections are `Π ⊗ I₄` and `I₃ ⊗ Π′` with `Π = v ℓᵀ/(ℓ·v)` built from the
  right and left eigenvectors for the expanding eigenvalue; vectors with a backward orbit tending
  to `0` are killed by the left eigenvectors of the contracting eigenvalues, and those with a
  forward orbit tending to `0` by the expanding one. The multiple `1` is the identity
  `vᵀ G v = (ℓ·v)²`, a polynomial identity modulo the minimal polynomial. The signatures come
  from explicit triangular congruences to `diag(3, 2, −23/6)` and `diag(4, 4, −9/4, 283/36)` and
  Sylvester's law of inertia (`QuadraticForm.sigPos_of_equiv_weightedSumSquares`).
-/

open Polynomial Matrix
open scoped Kronecker

namespace InflationDimension

namespace Inst

noncomputable section

/-! ### Real roots in rational boxes -/

theorem exists_rho_box : ∃ r : ℝ, 13247 / 10000 < r ∧ r < 13248 / 10000 ∧ r ^ 3 = r + 1 := by
  have hc : ContinuousOn (fun t : ℝ => t ^ 3 - t - 1)
      (Set.Icc (13247 / 10000) (13248 / 10000)) := by fun_prop
  have h := intermediate_value_Ioo (by norm_num : (13247 / 10000 : ℝ) ≤ 13248 / 10000) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 3 - t - 1) (13247 / 10000))
      ((fun t : ℝ => t ^ 3 - t - 1) (13248 / 10000)) := by
    constructor <;> norm_num
  obtain ⟨r, hr, hr0⟩ := h h0
  exact ⟨r, hr.1, hr.2, by simp only at hr0; linarith⟩

theorem exists_Q_box : ∃ q : ℝ, 12207 / 10000 < q ∧ q < 12208 / 10000 ∧ q ^ 4 = q + 1 := by
  have hc : ContinuousOn (fun t : ℝ => t ^ 4 - t - 1)
      (Set.Icc (12207 / 10000) (12208 / 10000)) := by fun_prop
  have h := intermediate_value_Ioo (by norm_num : (12207 / 10000 : ℝ) ≤ 12208 / 10000) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 4 - t - 1) (12207 / 10000))
      ((fun t : ℝ => t ^ 4 - t - 1) (12208 / 10000)) := by
    constructor <;> norm_num
  obtain ⟨q, hq, hq0⟩ := h h0
  exact ⟨q, hq.1, hq.2, by simp only at hq0; linarith⟩

theorem exists_q_box : ∃ q : ℝ, -72450 / 100000 < q ∧ q < -72449 / 100000 ∧ q ^ 4 = q + 1 := by
  have hc : ContinuousOn (fun t : ℝ => t ^ 4 - t - 1)
      (Set.Icc (-72450 / 100000) (-72449 / 100000)) := by fun_prop
  have h := intermediate_value_Ioo' (by norm_num : (-72450 / 100000 : ℝ) ≤ -72449 / 100000) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 4 - t - 1) (-72449 / 100000))
      ((fun t : ℝ => t ^ 4 - t - 1) (-72450 / 100000)) := by
    constructor <;> norm_num
  obtain ⟨q, hq, hq0⟩ := h h0
  exact ⟨q, hq.1, hq.2, by simp only at hq0; linarith⟩

/-- The real root `ρ ≈ 1.32472` of `x³ − x − 1`. -/
def rhoR : ℝ := Classical.choose exists_rho_box
/-- The real root `Q ≈ 1.22074` of `x⁴ − x − 1` greater than `1`. -/
def QR : ℝ := Classical.choose exists_Q_box
/-- The negative real root `q′ ≈ −0.72449` of `x⁴ − x − 1`. -/
def qN : ℝ := Classical.choose exists_q_box

theorem rhoR_lo : 13247 / 10000 < rhoR := (Classical.choose_spec exists_rho_box).1
theorem rhoR_hi : rhoR < 13248 / 10000 := (Classical.choose_spec exists_rho_box).2.1
theorem rhoR_eq : rhoR ^ 3 = rhoR + 1 := (Classical.choose_spec exists_rho_box).2.2
theorem QR_lo : 12207 / 10000 < QR := (Classical.choose_spec exists_Q_box).1
theorem QR_hi : QR < 12208 / 10000 := (Classical.choose_spec exists_Q_box).2.1
theorem QR_eq : QR ^ 4 = QR + 1 := (Classical.choose_spec exists_Q_box).2.2
theorem qN_lo : -72450 / 100000 < qN := (Classical.choose_spec exists_q_box).1
theorem qN_hi : qN < -72449 / 100000 := (Classical.choose_spec exists_q_box).2.1
theorem qN_eq : qN ^ 4 = qN + 1 := (Classical.choose_spec exists_q_box).2.2

/-! ### The non-real roots -/

/-- The root in the upper half plane of `x² + b x + c` (when `b² < 4c`). -/
def upperRoot (b c : ℝ) : ℂ := ⟨-b / 2, Real.sqrt (4 * c - b ^ 2) / 2⟩

theorem upperRoot_im_pos {b c : ℝ} (h : b ^ 2 < 4 * c) : 0 < (upperRoot b c).im := by
  have := Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 4 * c - b ^ 2)
  simp only [upperRoot]
  linarith

theorem upperRoot_add_star (b c : ℝ) : upperRoot b c + star (upperRoot b c) = -b := by
  apply Complex.ext <;> simp [upperRoot]

theorem upperRoot_mul_star {b c : ℝ} (h : b ^ 2 < 4 * c) :
    upperRoot b c * star (upperRoot b c) = c := by
  have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 4 * c - b ^ 2)
  apply Complex.ext <;> simp [upperRoot, Complex.mul_re, Complex.mul_im]
  · nlinarith
  · ring

theorem upperRoot_normSq {b c : ℝ} (h : b ^ 2 < 4 * c) : ‖upperRoot b c‖ ^ 2 = c := by
  have h1 := upperRoot_mul_star h
  rw [show star (upperRoot b c) = (starRingEnd ℂ) (upperRoot b c) from rfl,
    Complex.mul_conj'] at h1
  exact_mod_cast h1

theorem upperRoot_quad {b c : ℝ} (h : b ^ 2 < 4 * c) :
    upperRoot b c ^ 2 + b * upperRoot b c + c = 0 := by
  linear_combination upperRoot b c * upperRoot_add_star b c - upperRoot_mul_star h

/-- The complex root `z` of `x³ − x − 1` in the upper half plane (`|z|² = ρ² − 1 = 1/ρ`). -/
def zC : ℂ := upperRoot rhoR (rhoR ^ 2 - 1)
/-- The complex root `w` of `x⁴ − x − 1` in the upper half plane (`|w|² = −1/(Q q′)`). -/
def wC : ℂ := upperRoot (QR + qN) ((QR + qN) ^ 2 - QR * qN)

theorem zC_disc : rhoR ^ 2 < 4 * (rhoR ^ 2 - 1) := by nlinarith [rhoR_lo, rhoR_hi]

theorem QqN_neg : QR * qN < 0 := by nlinarith [QR_lo, qN_hi]

theorem wC_disc : (QR + qN) ^ 2 < 4 * ((QR + qN) ^ 2 - QR * qN) := by
  nlinarith [QqN_neg, sq_nonneg (QR + qN)]

theorem zC_eq : zC ^ 3 = zC + 1 := by
  have hq := upperRoot_quad zC_disc
  have hr : ((rhoR : ℂ)) ^ 3 = rhoR + 1 := by exact_mod_cast rhoR_eq
  rw [zC]
  push_cast at hq
  linear_combination (upperRoot rhoR (rhoR ^ 2 - 1) - rhoR) * hq + hr

theorem quartic_e1 : (QR + qN) * ((QR + qN) ^ 2 - 2 * (QR * qN)) = 1 := by
  have hsub : QR - qN ≠ 0 := by nlinarith [QR_lo, qN_hi]
  have : (QR - qN) * ((QR + qN) * ((QR + qN) ^ 2 - 2 * (QR * qN)) - 1) = 0 := by
    linear_combination QR_eq - qN_eq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hsub
  · linarith

theorem quartic_e2 : (QR * qN) * ((QR + qN) ^ 2 - QR * qN) = -1 := by
  have hsub : QR - qN ≠ 0 := by nlinarith [QR_lo, qN_hi]
  have : (QR - qN) * ((QR * qN) * ((QR + qN) ^ 2 - QR * qN) + 1) = 0 := by
    linear_combination qN * QR_eq - QR * qN_eq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hsub
  · linarith

theorem wC_eq : wC ^ 4 = wC + 1 := by
  have hq := upperRoot_quad wC_disc
  have e1 : (((QR + qN) * ((QR + qN) ^ 2 - 2 * (QR * qN)) : ℝ) : ℂ) = 1 := by
    exact_mod_cast quartic_e1
  have e2 : (((QR * qN) * ((QR + qN) ^ 2 - QR * qN) : ℝ) : ℂ) = -1 := by
    exact_mod_cast quartic_e2
  rw [wC]
  push_cast at hq e1 e2
  set w := upperRoot (QR + qN) ((QR + qN) ^ 2 - QR * qN)
  linear_combination (w ^ 2 - (QR + qN) * w + QR * qN) * hq + w * e1 - e2

theorem zC_im : 0 < zC.im := upperRoot_im_pos zC_disc
theorem wC_im : 0 < wC.im := upperRoot_im_pos wC_disc

theorem zC_normSq : ‖zC‖ ^ 2 = rhoR ^ 2 - 1 := upperRoot_normSq zC_disc
theorem wC_normSq : ‖wC‖ ^ 2 = (QR + qN) ^ 2 - QR * qN := upperRoot_normSq wC_disc

theorem wC_normSq_gt : 1 < (QR + qN) ^ 2 - QR * qN := by
  nlinarith [QR_lo, QR_hi, qN_lo, qN_hi]

/-- The three roots of `x³ − x − 1`. -/
def zs : Fin 3 → ℂ := ![(rhoR : ℂ), zC, star zC]
/-- The four roots of `x⁴ − x − 1`. -/
def ws : Fin 4 → ℂ := ![(QR : ℂ), (qN : ℂ), wC, star wC]

theorem zs_eq (k : Fin 3) : zs k ^ 3 = zs k + 1 := by
  fin_cases k
  · simp only [zs]; norm_num; exact_mod_cast rhoR_eq
  · simpa [zs] using zC_eq
  · have := congrArg star zC_eq
    simpa [zs] using this

theorem ws_eq (l : Fin 4) : ws l ^ 4 = ws l + 1 := by
  fin_cases l
  · simp only [ws]; norm_num; exact_mod_cast QR_eq
  · simp only [ws]; norm_num; exact_mod_cast qN_eq
  · simpa [ws] using wC_eq
  · have := congrArg star wC_eq
    simpa [ws] using this

theorem zs_injective : Function.Injective zs := by
  have h1 : (rhoR : ℂ) ≠ zC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [zC_im]
  have h2 : (rhoR : ℂ) ≠ star zC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [zC_im]
  have h3 : zC ≠ star zC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [zC_im]
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd h h1 | exact absurd h h1.symm | exact absurd h h2 | exact absurd h h2.symm
    | exact absurd h h3 | exact absurd h h3.symm

theorem ws_injective : Function.Injective ws := by
  have h0 : (QR : ℂ) ≠ (qN : ℂ) := fun h => by
    have := Complex.ofReal_injective h; linarith [QR_lo, qN_hi]
  have h1 : (QR : ℂ) ≠ wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  have h2 : (QR : ℂ) ≠ star wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  have h3 : (qN : ℂ) ≠ wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  have h4 : (qN : ℂ) ≠ star wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  have h5 : wC ≠ star wC := fun h => by
    have := congrArg Complex.im h; simp at this; linarith [wC_im]
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd h h0 | exact absurd h h0.symm | exact absurd h h1 | exact absurd h h1.symm
    | exact absurd h h2 | exact absurd h h2.symm | exact absurd h h3 | exact absurd h h3.symm
    | exact absurd h h4 | exact absurd h h4.symm | exact absurd h h5 | exact absurd h h5.symm

/-! ### Spectra from an intertwining Vandermonde matrix -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem spectral_of_intertwine (A : Matrix ι ι ℤ) (V : Matrix ι ι ℂ) (d : ι → ℂ)
    (hV : V.det ≠ 0) (h : V * (Int.castRingHom ℂ).mapMatrix A = diagonal d * V) :
    eigenvalues A = Multiset.map d Finset.univ.val ∧ ((A.det : ℤ) : ℂ) = ∏ i, d i := by
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr hV
  have hA : (Int.castRingHom ℂ).mapMatrix A = V⁻¹ * diagonal d * V := by
    rw [Matrix.mul_assoc, ← h, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
  have hU : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).mpr hdet
  constructor
  · unfold eigenvalues
    rw [← Matrix.charpoly_map]
    change ((Int.castRingHom ℂ).mapMatrix A).charpoly.roots = _
    rw [hA]
    have := Matrix.charpoly_units_conj' hU.unit (diagonal d)
    simp only [IsUnit.unit_spec] at this
    rw [this, Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod,
      show (fun i => X - C (d i)) = (fun a => X - C a) ∘ d from rfl, ← Multiset.map_map,
      Polynomial.roots_multiset_prod_X_sub_C]
  · rw [show ((A.det : ℤ) : ℂ) = (Int.castRingHom ℂ) A.det from rfl, RingHom.map_det, hA,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have := Matrix.det_nonsing_inv_mul_det V hdet
    linear_combination (∏ i, d i) * this

theorem unstableCount_of_eigen {A : Matrix ι ι ℤ} {d : ι → ℂ}
    (h : eigenvalues A = Multiset.map d Finset.univ.val) :
    unstableCount A = (Finset.univ.filter (fun i => 1 < ‖d i‖)).card := by
  rw [unstableCount, h, Multiset.filter_map, Multiset.card_map]
  rfl

theorem isHyperbolic_of_eigen {A : Matrix ι ι ℤ} {d : ι → ℂ}
    (h : eigenvalues A = Multiset.map d Finset.univ.val) (hd : ∀ i, ‖d i‖ ≠ 1) :
    IsHyperbolic A := by
  intro z hz
  rw [h, Multiset.mem_map] at hz
  obtain ⟨i, -, rfl⟩ := hz
  exact hd i

theorem intertwine_pow {A : Matrix ι ι ℤ} {V : Matrix ι ι ℂ} {d : ι → ℂ}
    (h : V * (Int.castRingHom ℂ).mapMatrix A = diagonal d * V) (n : ℕ) :
    V * (Int.castRingHom ℂ).mapMatrix (A ^ n) = diagonal (d ^ n) * V := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    congr 2

theorem kron_intertwine {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℤ} {B : Matrix n n ℤ} {V : Matrix m m ℂ} {W : Matrix n n ℂ} {a : m → ℂ}
    {b : n → ℂ} (hA : V * (Int.castRingHom ℂ).mapMatrix A = diagonal a * V)
    (hB : W * (Int.castRingHom ℂ).mapMatrix B = diagonal b * W) :
    (V ⊗ₖ W) * (Int.castRingHom ℂ).mapMatrix (A ⊗ₖ B) =
      diagonal (fun p => a p.1 * b p.2) * (V ⊗ₖ W) := by
  have hmap : (Int.castRingHom ℂ).mapMatrix (A ⊗ₖ B) =
      (Int.castRingHom ℂ).mapMatrix A ⊗ₖ (Int.castRingHom ℂ).mapMatrix B := by
    ext i j; simp [Matrix.kroneckerMap_apply]
  rw [hmap, ← Matrix.mul_kronecker_mul, hA, hB, Matrix.mul_kronecker_mul,
    Matrix.diagonal_kronecker_diagonal]

end Spectral

/-! ### The Vandermonde matrices of the two polynomials -/

/-- Rows `(1, z, z²)` over the roots `z` of `x³ − x − 1`. -/
def V3 : Matrix (Fin 3) (Fin 3) ℂ := vandermonde zs
/-- Rows `(1, w, w², w³)` over the roots `w` of `x⁴ − x − 1`. -/
def V4 : Matrix (Fin 4) (Fin 4) ℂ := vandermonde ws

theorem V3_det : V3.det ≠ 0 := det_vandermonde_ne_zero_iff.mpr zs_injective
theorem V4_det : V4.det ≠ 0 := det_vandermonde_ne_zero_iff.mpr ws_injective

theorem V3_Cρ : V3 * (Int.castRingHom ℂ).mapMatrix Cρ = diagonal zs * V3 := by
  ext k j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  fin_cases j <;> simp [Fin.sum_univ_succ, Cρ, V3, vandermonde_apply] <;>
    first | ring1 | linear_combination (zs_eq k) | linear_combination -(zs_eq k)

theorem V4_CQ : V4 * (Int.castRingHom ℂ).mapMatrix CQ = diagonal ws * V4 := by
  ext k j
  rw [Matrix.mul_apply, Matrix.diagonal_mul]
  fin_cases j <;> simp [Fin.sum_univ_succ, CQ, V4, vandermonde_apply] <;>
    first | ring1 | linear_combination (ws_eq k) | linear_combination -(ws_eq k)

theorem V3_one : V3 * (Int.castRingHom ℂ).mapMatrix (1 : Matrix (Fin 3) (Fin 3) ℤ) =
    diagonal (fun _ => 1) * V3 := by simp

theorem V4_one : V4 * (Int.castRingHom ℂ).mapMatrix (1 : Matrix (Fin 4) (Fin 4) ℤ) =
    diagonal (fun _ => 1) * V4 := by simp

theorem V3_Cρinv : V3 * (Int.castRingHom ℂ).mapMatrix (Cρ ^ 2 - 1) =
    diagonal (fun k => zs k ^ 2 - 1) * V3 := by
  rw [map_sub, map_one, Matrix.mul_sub, intertwine_pow V3_Cρ 2, Matrix.mul_one]
  ext i j
  simp [Matrix.diagonal_mul, sub_mul]

theorem V4_θ : V4 * (Int.castRingHom ℂ).mapMatrix (1 - CQ ^ 3) =
    diagonal (fun l => 1 - ws l ^ 3) * V4 := by
  rw [map_sub, map_one, Matrix.mul_sub, intertwine_pow V4_CQ 3, Matrix.mul_one]
  ext i j
  simp [Matrix.diagonal_mul, sub_mul]

/-! ### The characteristic polynomials -/

theorem charpoly_Cρ : Cρ.charpoly = X ^ 3 - X - 1 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [Cρ]
  ring

theorem Cρinv_eq : Cρ ^ 2 - 1 = !![-1, 1, 0; 0, 0, 1; 1, 0, 0] := by decide +kernel

theorem charpoly_Cρinv : (Cρ ^ 2 - 1).charpoly = X ^ 3 + X ^ 2 - 1 := by
  rw [Cρinv_eq, Matrix.charpoly, Matrix.det_fin_three]
  simp
  ring

theorem charpolyCQ : CQ.charpoly = X ^ 4 - X - 1 := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, charmatrix_apply, CQ, Matrix.diagonal_apply,
    Fin.succAbove]
  ring

theorem θmat_eq : 1 - CQ ^ 3 = !![1, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1; -1, 0, 0, 0] := by
  decide +kernel

theorem charpoly_θmat : (1 - CQ ^ 3).charpoly = X ^ 4 - X ^ 3 - 1 := by
  rw [θmat_eq, Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, charmatrix_apply, Matrix.diagonal_apply,
    Fin.succAbove]
  ring

theorem detCQ : CQ.det = -1 := by
  simp [CQ, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rfl

/-! ### Moduli -/

theorem r2_lo : 7548 / 10000 < rhoR ^ 2 - 1 := by nlinarith [rhoR_lo, rhoR_hi]
theorem r2_hi : rhoR ^ 2 - 1 < 7551 / 10000 := by nlinarith [rhoR_lo, rhoR_hi]
theorem Q2_lo : 149 / 100 < QR ^ 2 := by nlinarith [QR_lo, QR_hi]
theorem Q2_hi : QR ^ 2 < 14904 / 10000 := by nlinarith [QR_lo, QR_hi]
theorem q2_lo : 5248 / 10000 < qN ^ 2 := by nlinarith [qN_lo, qN_hi]
theorem q2_hi : qN ^ 2 < 5250 / 10000 := by nlinarith [qN_lo, qN_hi]
theorem Qq_lo : -8845 / 10000 < QR * qN := by
  nlinarith [mul_pos (by linarith [QR_lo] : (0 : ℝ) < QR) (by linarith [qN_lo] :
    (0 : ℝ) < qN + 72450 / 100000), QR_hi]
theorem Qq_hi : QR * qN < -8843 / 10000 := by
  nlinarith [mul_pos (by linarith [QR_lo] : (0 : ℝ) < QR) (by linarith [qN_hi] :
    (0 : ℝ) < -72449 / 100000 - qN), QR_lo]
theorem c_lo : 113 / 100 < (QR + qN) ^ 2 - QR * qN := by
  nlinarith [Q2_lo, q2_lo, Qq_lo]
theorem c_hi : (QR + qN) ^ 2 - QR * qN < 1132 / 1000 := by
  nlinarith [Q2_hi, q2_hi, Qq_hi]

theorem one_lt_of_one_lt_sq {x : ℝ} (hx : 0 ≤ x) (h : 1 < x ^ 2) : 1 < x := by nlinarith
theorem lt_one_of_sq_lt_one {x : ℝ} (hx : 0 ≤ x) (h : x ^ 2 < 1) : x < 1 := by nlinarith

theorem nz0 : ‖zs 0‖ = rhoR := by
  rw [show zs 0 = (rhoR : ℂ) from rfl, Complex.norm_real, Real.norm_of_nonneg
    (by linarith [rhoR_lo])]
theorem nz1 : ‖zs 1‖ ^ 2 = rhoR ^ 2 - 1 := zC_normSq
theorem nz2 : ‖zs 2‖ ^ 2 = rhoR ^ 2 - 1 := by
  rw [show zs 2 = (starRingEnd ℂ) zC from rfl, Complex.norm_conj]; exact zC_normSq
theorem nw0 : ‖ws 0‖ = QR := by
  rw [show ws 0 = (QR : ℂ) from rfl, Complex.norm_real, Real.norm_of_nonneg
    (by linarith [QR_lo])]
theorem nw1 : ‖ws 1‖ = -qN := by
  rw [show ws 1 = (qN : ℂ) from rfl, Complex.norm_real, Real.norm_of_nonpos
    (by linarith [qN_hi])]
theorem nw2 : ‖ws 2‖ ^ 2 = (QR + qN) ^ 2 - QR * qN := wC_normSq
theorem nw3 : ‖ws 3‖ ^ 2 = (QR + qN) ^ 2 - QR * qN := by
  rw [show ws 3 = (starRingEnd ℂ) wC from rfl, Complex.norm_conj]; exact wC_normSq

theorem nz_sq (k : Fin 3) : ‖zs k‖ ^ 2 = ![rhoR ^ 2, rhoR ^ 2 - 1, rhoR ^ 2 - 1] k := by
  fin_cases k
  · simp [nz0]
  · exact nz1
  · exact nz2

theorem nw_sq (l : Fin 4) :
    ‖ws l‖ ^ 2 = ![QR ^ 2, qN ^ 2, (QR + qN) ^ 2 - QR * qN, (QR + qN) ^ 2 - QR * qN] l := by
  fin_cases l
  · simp [nw0]
  · simp [nw1]
  · exact nw2
  · exact nw3

/-- `1/z = z² − 1` for a root of `x³ − x − 1`. -/
theorem zs_inv_norm (k : Fin 3) : ‖zs k ^ 2 - 1‖ * ‖zs k‖ = 1 := by
  rw [← norm_mul, show (zs k ^ 2 - 1) * zs k = 1 by linear_combination zs_eq k, norm_one]

/-- `1 − w³ = −1/w` for a root of `x⁴ − x − 1`. -/
theorem ws_θ_norm (l : Fin 4) : ‖1 - ws l ^ 3‖ * ‖ws l‖ = 1 := by
  rw [← norm_mul, show (1 - ws l ^ 3) * ws l = -1 by linear_combination -(ws_eq l), norm_neg,
    norm_one]

theorem fz0 : 1 < ‖zs 0‖ := by rw [nz0]; linarith [rhoR_lo]
theorem fz1 : ‖zs 1‖ < 1 := lt_one_of_sq_lt_one (norm_nonneg _) (by rw [nz1]; linarith [r2_hi])
theorem fz2 : ‖zs 2‖ < 1 := lt_one_of_sq_lt_one (norm_nonneg _) (by rw [nz2]; linarith [r2_hi])
theorem fw0 : 1 < ‖ws 0‖ := by rw [nw0]; linarith [QR_lo]
theorem fw1 : ‖ws 1‖ < 1 := by rw [nw1]; linarith [qN_lo]
theorem fw2 : 1 < ‖ws 2‖ := one_lt_of_one_lt_sq (norm_nonneg _) (by rw [nw2]; linarith [c_lo])
theorem fw3 : 1 < ‖ws 3‖ := one_lt_of_one_lt_sq (norm_nonneg _) (by rw [nw3]; linarith [c_lo])

theorem inv_lt_one_of {x y : ℝ} (hxy : x * y = 1) (hy : 1 < y) : x < 1 := by
  nlinarith
theorem one_lt_inv_of {x y : ℝ} (hxy : x * y = 1) (hy0 : 0 ≤ y) (hy : y < 1) :
    1 < x := by
  nlinarith

theorem gi0 : ‖zs 0 ^ 2 - 1‖ < 1 := inv_lt_one_of (zs_inv_norm 0) fz0
theorem gi1 : 1 < ‖zs 1 ^ 2 - 1‖ := one_lt_inv_of (zs_inv_norm 1) (norm_nonneg _) fz1
theorem gi2 : 1 < ‖zs 2 ^ 2 - 1‖ := one_lt_inv_of (zs_inv_norm 2) (norm_nonneg _) fz2
theorem t0 : ‖1 - ws 0 ^ 3‖ < 1 := inv_lt_one_of (ws_θ_norm 0) fw0
theorem t1 : 1 < ‖1 - ws 1 ^ 3‖ := one_lt_inv_of (ws_θ_norm 1) (norm_nonneg _) fw1
theorem t2 : ‖1 - ws 2 ^ 3‖ < 1 := inv_lt_one_of (ws_θ_norm 2) fw2
theorem t3 : ‖1 - ws 3 ^ 3‖ < 1 := inv_lt_one_of (ws_θ_norm 3) fw3

theorem pnorm_sq (k : Fin 3) (l : Fin 4) : ‖zs k * ws l‖ ^ 2 = ‖zs k‖ ^ 2 * ‖ws l‖ ^ 2 := by
  rw [norm_mul, mul_pow]

theorem p00 : 1 < ‖zs 0 * ws 0‖ := by rw [norm_mul, nz0, nw0]; nlinarith [rhoR_lo, QR_lo]
theorem p01 : ‖zs 0 * ws 1‖ < 1 := lt_one_of_sq_lt_one (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_hi, q2_hi])
theorem p02 : 1 < ‖zs 0 * ws 2‖ := one_lt_of_one_lt_sq (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_lo, c_lo])
theorem p03 : 1 < ‖zs 0 * ws 3‖ := one_lt_of_one_lt_sq (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_lo, c_lo])
theorem p10 : 1 < ‖zs 1 * ws 0‖ := one_lt_of_one_lt_sq (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_lo, Q2_lo])
theorem p11 : ‖zs 1 * ws 1‖ < 1 := lt_one_of_sq_lt_one (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_hi, r2_lo, q2_hi, q2_lo])
theorem p12 : ‖zs 1 * ws 2‖ < 1 := lt_one_of_sq_lt_one (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_hi, r2_lo, c_hi, c_lo])
theorem p13 : ‖zs 1 * ws 3‖ < 1 := lt_one_of_sq_lt_one (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_hi, r2_lo, c_hi, c_lo])
theorem p20 : 1 < ‖zs 2 * ws 0‖ := one_lt_of_one_lt_sq (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_lo, Q2_lo])
theorem p21 : ‖zs 2 * ws 1‖ < 1 := lt_one_of_sq_lt_one (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_hi, r2_lo, q2_hi, q2_lo])
theorem p22 : ‖zs 2 * ws 2‖ < 1 := lt_one_of_sq_lt_one (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_hi, r2_lo, c_hi, c_lo])
theorem p23 : ‖zs 2 * ws 3‖ < 1 := lt_one_of_sq_lt_one (norm_nonneg _) (by
  rw [pnorm_sq, nz_sq, nw_sq]; simp; nlinarith [r2_hi, r2_lo, c_hi, c_lo])

/-! ### Eigenvalue data of the eight matrices -/


theorem eig_Cρ : eigenvalues Cρ = Multiset.map zs Finset.univ.val :=
  (spectral_of_intertwine Cρ V3 zs V3_det V3_Cρ).1
theorem eig_Cρinv : eigenvalues (Cρ ^ 2 - 1) = Multiset.map (fun k => zs k ^ 2 - 1) Finset.univ.val :=
  (spectral_of_intertwine _ V3 _ V3_det V3_Cρinv).1
theorem eig_CQ : eigenvalues CQ = Multiset.map ws Finset.univ.val :=
  (spectral_of_intertwine CQ V4 ws V4_det V4_CQ).1
theorem eig_θmat : eigenvalues (1 - CQ ^ 3) =
    Multiset.map (fun l => 1 - ws l ^ 3) Finset.univ.val :=
  (spectral_of_intertwine _ V4 _ V4_det V4_θ).1

/-- The product Vandermonde matrix `V3 ⊗ V4`. -/
def V12 : Matrix (Fin 3 × Fin 4) (Fin 3 × Fin 4) ℂ := V3 ⊗ₖ V4

theorem V12_det : V12.det ≠ 0 := by
  rw [V12, Matrix.det_kronecker]
  exact mul_ne_zero (pow_ne_zero _ V3_det) (pow_ne_zero _ V4_det)

theorem eig_mulρ : eigenvalues mulρ = Multiset.map (fun p : Fin 3 × Fin 4 => zs p.1) Finset.univ.val := by
  have h := kron_intertwine V3_Cρ V4_one
  simp only [mul_one] at h
  exact (spectral_of_intertwine _ V12 _ V12_det h).1
theorem eig_mulQ : eigenvalues mulQ = Multiset.map (fun p : Fin 3 × Fin 4 => ws p.2) Finset.univ.val := by
  have h := kron_intertwine V3_one V4_CQ
  simp only [one_mul] at h
  exact (spectral_of_intertwine _ V12 _ V12_det h).1
theorem eig_mulθ : eigenvalues mulθ =
    Multiset.map (fun p : Fin 3 × Fin 4 => 1 - ws p.2 ^ 3) Finset.univ.val := by
  have h := kron_intertwine V3_one V4_θ
  simp only [one_mul] at h
  exact (spectral_of_intertwine _ V12 _ V12_det h).1
theorem eig_mulρQ : eigenvalues mulρQ =
    Multiset.map (fun p : Fin 3 × Fin 4 => zs p.1 * ws p.2) Finset.univ.val :=
  (spectral_of_intertwine _ V12 _ V12_det (kron_intertwine V3_Cρ V4_CQ)).1

/-! ### Counts -/

theorem U_Cρ : unstableCount Cρ = 1 := by
  rw [unstableCount_of_eigen eig_Cρ, Finset.card_filter, Fin.sum_univ_three]
  simp only [fz0, not_lt.mpr fz1.le, not_lt.mpr fz2.le, ite_true, ite_false]
theorem U_Cρinv : unstableCount (Cρ ^ 2 - 1) = 2 := by
  rw [unstableCount_of_eigen eig_Cρinv, Finset.card_filter, Fin.sum_univ_three]
  simp only [gi1, gi2, not_lt.mpr gi0.le, ite_true, ite_false]
theorem U_CQ : unstableCount CQ = 3 := by
  rw [unstableCount_of_eigen eig_CQ, Finset.card_filter, Fin.sum_univ_four]
  simp only [fw0, fw2, fw3, not_lt.mpr fw1.le, ite_true, ite_false]
theorem U_θmat : unstableCount (1 - CQ ^ 3) = 1 := by
  rw [unstableCount_of_eigen eig_θmat, Finset.card_filter, Fin.sum_univ_four]
  simp only [t1, not_lt.mpr t0.le, not_lt.mpr t2.le, not_lt.mpr t3.le, ite_true, ite_false]
theorem U_mulρ : unstableCount mulρ = 4 := by
  rw [unstableCount_of_eigen eig_mulρ, Finset.card_filter, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  simp only [fz0, not_lt.mpr fz1.le, not_lt.mpr fz2.le, ite_true, ite_false]
  simp
theorem U_mulQ : unstableCount mulQ = 9 := by
  rw [unstableCount_of_eigen eig_mulQ, Finset.card_filter, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  simp only [Fin.sum_univ_four, fw0, fw2, fw3, not_lt.mpr fw1.le, ite_true, ite_false]
  norm_num
theorem U_mulθ : unstableCount mulθ = 3 := by
  rw [unstableCount_of_eigen eig_mulθ, Finset.card_filter, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  simp only [Fin.sum_univ_four, t1, not_lt.mpr t0.le, not_lt.mpr t2.le, not_lt.mpr t3.le,
    ite_true, ite_false]
  norm_num
theorem U_mulρQ : unstableCount mulρQ = 5 := by
  rw [unstableCount_of_eigen eig_mulρQ, Finset.card_filter, Fintype.sum_prod_type,
    Fin.sum_univ_three]
  simp only [Fin.sum_univ_four, p00, p02, p03, p10, p20, not_lt.mpr p01.le, not_lt.mpr p11.le,
    not_lt.mpr p12.le, not_lt.mpr p13.le, not_lt.mpr p21.le, not_lt.mpr p22.le,
    not_lt.mpr p23.le, ite_true, ite_false]
  norm_num

/-! ### Hyperbolicity -/

theorem hyp_Cρ : IsHyperbolic Cρ := isHyperbolic_of_eigen eig_Cρ (by
  intro k; fin_cases k
  exacts [fz0.ne', fz1.ne, fz2.ne])
theorem hyp_Cρinv : IsHyperbolic (Cρ ^ 2 - 1) := isHyperbolic_of_eigen eig_Cρinv (by
  intro k; fin_cases k
  exacts [gi0.ne, gi1.ne', gi2.ne'])
theorem hyp_CQ : IsHyperbolic CQ := isHyperbolic_of_eigen eig_CQ (by
  intro l; fin_cases l
  exacts [fw0.ne', fw1.ne, fw2.ne', fw3.ne'])
theorem hyp_θmat : IsHyperbolic (1 - CQ ^ 3) := isHyperbolic_of_eigen eig_θmat (by
  intro l; fin_cases l
  exacts [t0.ne, t1.ne', t2.ne, t3.ne])
theorem hyp_mulρ : IsHyperbolic mulρ := isHyperbolic_of_eigen eig_mulρ (by
  rintro ⟨k, l⟩; fin_cases k
  exacts [fz0.ne', fz1.ne, fz2.ne])
theorem hyp_mulQ : IsHyperbolic mulQ := isHyperbolic_of_eigen eig_mulQ (by
  rintro ⟨k, l⟩; fin_cases l
  exacts [fw0.ne', fw1.ne, fw2.ne', fw3.ne'])
theorem hyp_mulθ : IsHyperbolic mulθ := isHyperbolic_of_eigen eig_mulθ (by
  rintro ⟨k, l⟩; fin_cases l
  exacts [t0.ne, t1.ne', t2.ne, t3.ne])
theorem hyp_mulρQ : IsHyperbolic mulρQ := isHyperbolic_of_eigen eig_mulρQ (by
  rintro ⟨k, l⟩; fin_cases k <;> fin_cases l
  exacts [p00.ne', p01.ne, p02.ne', p03.ne', p10.ne', p11.ne, p12.ne, p13.ne, p20.ne', p21.ne,
    p22.ne, p23.ne])

/-! ### Determinants -/

theorem det_Cρ : Cρ.det = 1 := by simp [Cρ, Matrix.det_fin_three]
theorem det_Cρinv : (Cρ ^ 2 - 1).det = 1 := by rw [Cρinv_eq]; simp [Matrix.det_fin_three]
theorem det_θmat : (1 - CQ ^ 3).det = -1 := by
  rw [θmat_eq]; simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; rfl
theorem det_mulρ : mulρ.det ≠ 0 := by
  rw [mulρ, Matrix.det_kronecker, det_Cρ]; simp
theorem det_mulQ : mulQ.det ≠ 0 := by
  rw [mulQ, Matrix.det_kronecker, detCQ]; simp
theorem det_mulθ : mulθ.det ≠ 0 := by
  rw [mulθ, Matrix.det_kronecker, det_θmat]; simp
theorem det_mulρQ : mulρQ.det ≠ 0 := by
  rw [mulρQ, Matrix.det_kronecker, det_Cρ, detCQ]; simp

/-! ### The expanding eigenvalue of `θ` -/

theorem θ_expanding (z : ℂ) (hz : z ∈ eigenvalues (1 - CQ ^ 3)) (h1 : 1 < ‖z‖) :
    z.im = 0 ∧ (1.3802 : ℝ) < z.re ∧ z.re < 1.3803 := by
  rw [eig_θmat, Multiset.mem_map] at hz
  obtain ⟨l, -, rfl⟩ := hz
  fin_cases l
  · exact absurd h1 (not_lt.mpr t0.le)
  · have ht : (1 - qN ^ 3) * qN = -1 := by linear_combination -qN_eq
    have hre : (1 - ws 1 ^ 3) = ((1 - qN ^ 3 : ℝ) : ℂ) := by
      simp [ws]
    simp only [Fin.mk_one] at hre ⊢
    rw [hre, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨rfl, ?_, ?_⟩
    · nlinarith [qN_lo, qN_hi]
    · nlinarith [qN_lo, qN_hi]
  · exact absurd h1 (not_lt.mpr t2.le)
  · exact absurd h1 (not_lt.mpr t3.le)

/-! ### Backward and forward orbits -/

section Orbits

variable {V : Type*} [TopologicalSpace V] [Zero V]

theorem backward_orbit_zero {F : V → ℂ} (hF : Continuous F) (hF0 : F 0 = 0) {μ : ℂ}
    (hμ : ‖μ‖ < 1) {w : ℕ → V} (hrel : ∀ n, F (w n) = μ * F (w (n + 1)))
    (hwt : Filter.Tendsto w Filter.atTop (nhds 0)) : F (w 0) = 0 := by
  have key : ∀ n, F (w 0) = μ ^ n * F (w n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hrel n, pow_succ]; ring
  have hle : ∀ n, ‖F (w 0)‖ ≤ ‖F (w n)‖ := by
    intro n
    rw [key n, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hμ.le)
  have ht : Filter.Tendsto (fun n => ‖F (w n)‖) Filter.atTop (nhds 0) := by
    have := ((hF.tendsto 0).comp hwt).norm
    simpa [hF0] using this
  have := ge_of_tendsto' ht hle
  exact norm_le_zero_iff.mp this

theorem forward_orbit_zero {f : V → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) {μ : ℝ}
    (hμ : 1 < μ) {s : ℕ → V} (hrel : ∀ n, f (s n) = μ ^ n * f (s 0))
    (hst : Filter.Tendsto s Filter.atTop (nhds 0)) : f (s 0) = 0 := by
  have hle : ∀ n, |f (s 0)| ≤ |f (s n)| := by
    intro n
    rw [hrel n, abs_mul, abs_of_pos (pow_pos (by linarith : (0 : ℝ) < μ) n)]
    exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hμ.le)
  have ht : Filter.Tendsto (fun n => |f (s n)|) Filter.atTop (nhds 0) := by
    have := ((hf.tendsto 0).comp hst).abs
    simpa [hf0] using this
  have := ge_of_tendsto' ht hle
  exact abs_nonpos_iff.mp this

end Orbits

/-! ### The dilation `ρ` on `ℝ³ ⊗ ℝ⁴` -/

/-- The right eigenvector `(1, ρ², ρ)` of `Cρ` for `ρ`. -/
def vr : Fin 3 → ℝ := ![1, rhoR ^ 2, rhoR]
/-- The left eigenvector `(ρ^i)` of `Cρ` for `ρ`. -/
def lr : Fin 3 → ℝ := fun m => rhoR ^ (m : ℕ)

theorem den_r_pos : 0 < 2 * rhoR + 3 := by linarith [rhoR_lo]

theorem lr_vr : lr ⬝ᵥ vr = 2 * rhoR + 3 := by
  simp [lr, vr, dotProduct, Fin.sum_univ_three]
  linear_combination 2 * rhoR_eq

/-- The column `j` of `v ∈ ℝ³ ⊗ ℝ⁴`. -/
def col (v : Fin 3 × Fin 4 → ℝ) (j : Fin 4) : Fin 3 → ℝ := fun m => v (m, j)

theorem act_mulρ (v : Fin 3 × Fin 4 → ℝ) :
    act mulρ v = fun p => ((Cρ.map (Int.cast : ℤ → ℝ)) *ᵥ col v p.2) p.1 := by
  funext p
  simp [act, mulρ, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, col]

theorem lr_vecMul : lr ᵥ* (Cρ.map (Int.cast : ℤ → ℝ)) = rhoR • lr := by
  funext j
  fin_cases j <;> simp [lr, Cρ, vecMul, dotProduct, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination rhoR_eq | linear_combination -rhoR_eq

theorem mulVec_vr : (Cρ.map (Int.cast : ℤ → ℝ)) *ᵥ vr = rhoR • vr := by
  funext i
  fin_cases i <;> simp [vr, Cρ, mulVec, dotProduct, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination rhoR_eq | linear_combination -rhoR_eq

/-- The spectral projection of `mulρ` onto `E^u` along `E^s`: `Π ⊗ I₄` with
`Π = vr lrᵀ / (lr · vr)`. -/
def Pρ : (Fin 3 × Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 × Fin 4 → ℝ) where
  toFun v p := vr p.1 * (lr ⬝ᵥ col v p.2) / (2 * rhoR + 3)
  map_add' v v' := by
    funext p
    simp only [Pi.add_apply]
    rw [show col (v + v') p.2 = col v p.2 + col v' p.2 from rfl, dotProduct_add]
    ring
  map_smul' c v := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show col (c • v) p.2 = c • col v p.2 from rfl, dotProduct_smul, smul_eq_mul]
    ring

theorem Pρ_apply (v : Fin 3 × Fin 4 → ℝ) (p : Fin 3 × Fin 4) :
    Pρ v p = vr p.1 * (lr ⬝ᵥ col v p.2) / (2 * rhoR + 3) := rfl

theorem act_Pρ (v : Fin 3 × Fin 4 → ℝ) : act mulρ (Pρ v) = rhoR • Pρ v := by
  rw [act_mulρ]
  funext p
  have hcol : col (Pρ v) p.2 = ((lr ⬝ᵥ col v p.2) / (2 * rhoR + 3)) • vr := by
    funext m; simp [col, Pρ_apply]; ring
  rw [hcol, Matrix.mulVec_smul, mulVec_vr]
  simp [Pρ_apply]
  ring

theorem Pρ_mem_unstable (v : Fin 3 × Fin 4 → ℝ) : Pρ v ∈ unstableSet mulρ := by
  refine ⟨fun n => (rhoR⁻¹) ^ n • Pρ v, by simp, fun n => ?_, ?_⟩
  · rw [map_smul, act_Pρ, smul_smul, pow_succ, mul_assoc,
      inv_mul_cancel₀ (by linarith [rhoR_lo] : rhoR ≠ 0), mul_one]
  · have h : Filter.Tendsto (fun n : ℕ => (rhoR⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (by linarith [rhoR_lo])).le
        (inv_lt_one_of_one_lt₀ (by linarith [rhoR_lo]))
    simpa using h.smul_const (Pρ v)

theorem fR_act (v : Fin 3 × Fin 4 → ℝ) (j : Fin 4) :
    lr ⬝ᵥ col (act mulρ v) j = rhoR * (lr ⬝ᵥ col v j) := by
  rw [show col (act mulρ v) j = (Cρ.map (Int.cast : ℤ → ℝ)) *ᵥ col v j by
    rw [act_mulρ]; rfl, Matrix.dotProduct_mulVec, lr_vecMul, smul_dotProduct, smul_eq_mul]

theorem Pρ_stable (v : Fin 3 × Fin 4 → ℝ) (hv : v ∈ stableSet mulρ) : Pρ v = 0 := by
  have hz : ∀ j, lr ⬝ᵥ col v j = 0 := by
    intro j
    have hc : Continuous (fun x : Fin 3 × Fin 4 → ℝ => lr ⬝ᵥ col x j) := by
      simp only [dotProduct, col]; fun_prop
    have step : ∀ n, lr ⬝ᵥ col ((act mulρ ^ (n + 1)) v) j =
        rhoR * lr ⬝ᵥ col ((act mulρ ^ n) v) j := fun n => by
      rw [pow_succ', Module.End.mul_apply, fR_act]
    have hrel : ∀ n, lr ⬝ᵥ col ((act mulρ ^ n) v) j =
        rhoR ^ n * lr ⬝ᵥ col ((act mulρ ^ 0) v) j := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [step, ih, pow_succ]; ring
    have h0 : lr ⬝ᵥ col (0 : Fin 3 × Fin 4 → ℝ) j = 0 := by simp [col, dotProduct]
    have := forward_orbit_zero (f := fun x => lr ⬝ᵥ col x j) hc h0
      (by linarith [rhoR_lo] : (1 : ℝ) < rhoR) (s := fun n => (act mulρ ^ n) v) hrel hv
    simpa using this
  funext p
  simp [Pρ_apply, hz]

/-- Complexified integer matrices act compatibly with casting. -/
theorem cast_mulVec {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℤ) (y : n → ℝ) :
    (fun m => (((M.map (Int.cast : ℤ → ℝ)) *ᵥ y) m : ℂ)) =
      (Int.castRingHom ℂ).mapMatrix M *ᵥ (fun m => (y m : ℂ)) := by
  funext m
  simp [Matrix.mulVec, dotProduct, Complex.ofReal_sum]

theorem V3_mulVec (x : Fin 3 → ℂ) (k : Fin 3) :
    (V3 *ᵥ ((Int.castRingHom ℂ).mapMatrix Cρ *ᵥ x)) k = zs k * (V3 *ᵥ x) k := by
  rw [Matrix.mulVec_mulVec, V3_Cρ, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

theorem V4_mulVec_θ (x : Fin 4 → ℂ) (l : Fin 4) :
    (V4 *ᵥ ((Int.castRingHom ℂ).mapMatrix (1 - CQ ^ 3) *ᵥ x)) l = (1 - ws l ^ 3) * (V4 *ᵥ x) l := by
  rw [Matrix.mulVec_mulVec, V4_θ, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

theorem V3_vr (k : Fin 3) (hk : k ≠ 0) : (V3 *ᵥ (fun m => (vr m : ℂ))) k = 0 := by
  have hne : zs k ≠ (rhoR : ℂ) := fun h => hk (zs_injective (h.trans rfl))
  have hrc : ((rhoR : ℂ)) ^ 3 = rhoR + 1 := by exact_mod_cast rhoR_eq
  have key : (zs k - rhoR) * (1 + zs k * rhoR ^ 2 + zs k ^ 2 * rhoR) = 0 := by
    linear_combination (rhoR : ℂ) * zs_eq k - zs k * hrc
  have h2 := (mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr hne)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, V3, vandermonde_apply, vr]
  linear_combination h2

/-- A vector with a backward `mulρ`-orbit tending to `0` has every column on the line `ℝ vr`. -/
theorem unstable_col (v : Fin 3 × Fin 4 → ℝ) (hv : v ∈ unstableSet mulρ) (j : Fin 4) :
    col v j = ((lr ⬝ᵥ col v j) / (2 * rhoR + 3)) • vr := by
  obtain ⟨w, hw0, hw, hwt⟩ := hv
  set c := (lr ⬝ᵥ col v j) / (2 * rhoR + 3) with hc
  -- the two contracting rows of `V3` kill the column
  have hkill : ∀ k : Fin 3, k ≠ 0 → (V3 *ᵥ (fun m => (col v j m : ℂ))) k = 0 := by
    intro k hk
    have hk1 : ‖zs k‖ < 1 := by
      fin_cases k
      · exact absurd rfl hk
      · exact fz1
      · exact fz2
    have hF : Continuous (fun x : Fin 3 × Fin 4 → ℝ => (V3 *ᵥ (fun m => (col x j m : ℂ))) k) := by
      simp only [Matrix.mulVec, dotProduct, col]; fun_prop
    have hrel : ∀ n, (V3 *ᵥ (fun m => (col (w n) j m : ℂ))) k =
        zs k * (V3 *ᵥ (fun m => (col (w (n + 1)) j m : ℂ))) k := by
      intro n
      rw [← V3_mulVec, ← cast_mulVec, ← hw n, act_mulρ]
      rfl
    have := backward_orbit_zero (F := fun x => (V3 *ᵥ (fun m => (col x j m : ℂ))) k) hF
      (by simp [col, Matrix.mulVec, dotProduct]) hk1 hrel hwt
    simpa [hw0] using this
  have hy : (fun m => ((col v j m - c * vr m : ℝ) : ℂ)) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero V3_det
    funext k
    have hsplit : (V3 *ᵥ (fun m => ((col v j m - c * vr m : ℝ) : ℂ))) k =
        (V3 *ᵥ (fun m => (col v j m : ℂ))) k - c * (V3 *ᵥ (fun m => (vr m : ℂ))) k := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [hsplit]
    by_cases hk : k = 0
    · subst hk
      have hl : lr ⬝ᵥ col v j - c * (lr ⬝ᵥ vr) = 0 := by
        rw [lr_vr, hc]; field_simp [den_r_pos.ne']; ring
      have e1 : (V3 *ᵥ (fun m => (col v j m : ℂ))) 0 = ((lr ⬝ᵥ col v j : ℝ) : ℂ) := by
        simp [Matrix.mulVec, dotProduct, V3, vandermonde_apply, lr, zs, Complex.ofReal_sum]
      have e2 : (V3 *ᵥ (fun m => (vr m : ℂ))) 0 = ((lr ⬝ᵥ vr : ℝ) : ℂ) := by
        simp [Matrix.mulVec, dotProduct, V3, vandermonde_apply, lr, zs, Complex.ofReal_sum]
      rw [e1, e2]
      simp only [Pi.zero_apply]
      exact_mod_cast hl
    · rw [hkill k hk, V3_vr k hk]; simp
  funext m
  have := congrFun hy m
  simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

theorem Pρ_unstable (v : Fin 3 × Fin 4 → ℝ) (hv : v ∈ unstableSet mulρ) : Pρ v = v := by
  funext p
  have h := congrFun (unstable_col v hv p.2) p.1
  simp only [col, Pi.smul_apply, smul_eq_mul] at h
  rw [Pρ_apply, show v p = v (p.1, p.2) from rfl, h]
  ring

theorem col_sectorQ (u : Fin 4 → ℝ) (j : Fin 4) : lr ⬝ᵥ col (sectorQ u) j = u j := by
  simp [dotProduct, col, sectorQ, lr]

theorem Pρ_sectorQ (u : Fin 4 → ℝ) :
    Pρ (sectorQ u) = fun p => (vr p.1 / (2 * rhoR + 3)) * u p.2 := by
  funext p
  rw [Pρ_apply, col_sectorQ]
  ring

theorem pairing_kron_pure {m n : Type*} [Fintype m] [Fintype n] (G : Matrix m m ℤ)
    (H : Matrix n n ℤ) (a a' : m → ℝ) (b b' : n → ℝ) :
    pairing (G ⊗ₖ H) (fun p => a p.1 * b p.2) (fun p => a' p.1 * b' p.2) =
      pairing G a a' * pairing H b b' := by
  simp only [pairing, dotProduct, mulVec, Fintype.sum_prod_type, Matrix.map_apply,
    kroneckerMap_apply, Int.cast_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm (a i) _ (b j) _, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem pairing_vr : pairing GramRho (fun i => vr i / (2 * rhoR + 3))
    (fun i => vr i / (2 * rhoR + 3)) = 1 := by
  have hd := den_r_pos.ne'
  simp [pairing, dotProduct, mulVec, Fin.sum_univ_three, GramRho, vr]
  field_simp
  linear_combination (2 * rhoR + 6) * rhoR_eq

theorem dilation_rho :
    ∃ r : ℝ, r ^ 3 = r + 1 ∧ (∀ v ∈ unstableSet mulρ, act mulρ v = r • v) ∧
      ∃ P : (Fin 3 × Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 × Fin 4 → ℝ),
        (∀ v, P v ∈ unstableSet mulρ) ∧ (∀ v ∈ unstableSet mulρ, P v = v) ∧
        (∀ v ∈ stableSet mulρ, P v = 0) ∧
        (∀ v ∈ unstableSet mulρ, ∃! u : Fin 4 → ℝ, P (sectorQ u) = v) ∧
        ∀ u u' : Fin 4 → ℝ,
          pairing (GramRho ⊗ₖ GramQ) (P (sectorQ u)) (P (sectorQ u')) = pairing GramQ u u' := by
  refine ⟨rhoR, rhoR_eq, fun v hv => ?_, Pρ, Pρ_mem_unstable, Pρ_unstable, Pρ_stable,
    fun v hv => ?_, fun u u' => ?_⟩
  · rw [← Pρ_unstable v hv, act_Pρ]
  · refine ⟨fun j => lr ⬝ᵥ col v j, ?_, fun u hu => ?_⟩
    · funext p
      have h := congrFun (Pρ_unstable v hv) p
      rw [Pρ_apply] at h
      rw [Pρ_sectorQ, ← h]
      dsimp only
      ring
    · funext j
      have h1 := congrFun hu (0, j)
      have h2 := congrFun (Pρ_unstable v hv) (0, j)
      rw [Pρ_sectorQ] at h1
      rw [Pρ_apply] at h2
      simp only [vr, Matrix.cons_val_zero] at h1 h2
      have hd := den_r_pos.ne'
      field_simp at h1 h2
      linarith
  · have h := pairing_kron_pure GramRho GramQ (fun i => vr i / (2 * rhoR + 3))
      (fun i => vr i / (2 * rhoR + 3)) u u'
    rw [Pρ_sectorQ, Pρ_sectorQ, h, pairing_vr, one_mul]

/-! ### The dilation `θ` on `ℝ³ ⊗ ℝ⁴` -/

/-- The expanding eigenvalue `t = 1 − q′³ = −1/q′ ≈ 1.38028` of `I₄ − CQ³`. -/
def tθ : ℝ := 1 - qN ^ 3
/-- The right eigenvector `(1, q′³, q′², q′)` of `I₄ − CQ³` for `t`. -/
def vθ : Fin 4 → ℝ := ![1, qN ^ 3, qN ^ 2, qN]
/-- The left eigenvector `(q′^j)` of `I₄ − CQ³` for `t`. -/
def lθ : Fin 4 → ℝ := fun n => qN ^ (n : ℕ)

theorem den_t_pos : 0 < 3 * qN + 4 := by linarith [qN_lo]

theorem tθ_gt : 1 < tθ := by
  have : qN ^ 3 < 0 := by
    have h : qN < 0 := by linarith [qN_hi]
    nlinarith [sq_nonneg qN, mul_pos (neg_pos.mpr h) (neg_pos.mpr h)]
  unfold tθ; linarith

theorem tθ_eq : tθ ^ 4 = tθ ^ 3 + 1 := by
  unfold tθ
  linear_combination (qN ^ 8 - 2 * qN ^ 5 + qN ^ 4 + qN ^ 2 - qN + 1) * qN_eq

theorem lθ_vθ : lθ ⬝ᵥ vθ = 3 * qN + 4 := by
  simp [lθ, vθ, dotProduct, Fin.sum_univ_four]
  linear_combination 3 * qN_eq

/-- The row `i` of `v ∈ ℝ³ ⊗ ℝ⁴`. -/
def row (v : Fin 3 × Fin 4 → ℝ) (i : Fin 3) : Fin 4 → ℝ := fun n => v (i, n)

theorem act_mulθ (v : Fin 3 × Fin 4 → ℝ) :
    act mulθ v = fun p => (((1 - CQ ^ 3).map (Int.cast : ℤ → ℝ)) *ᵥ row v p.1) p.2 := by
  funext p
  simp [act, mulθ, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, row]

theorem lθ_vecMul : lθ ᵥ* ((1 - CQ ^ 3).map (Int.cast : ℤ → ℝ)) = tθ • lθ := by
  rw [θmat_eq]
  funext j
  fin_cases j
  all_goals simp [lθ, vecMul, dotProduct, Fin.sum_univ_four, tθ]
  all_goals first
    | ring1
    | linear_combination qN_eq
    | linear_combination qN * qN_eq
    | linear_combination qN ^ 2 * qN_eq

theorem mulVec_vθ : ((1 - CQ ^ 3).map (Int.cast : ℤ → ℝ)) *ᵥ vθ = tθ • vθ := by
  rw [θmat_eq]
  funext i
  fin_cases i
  all_goals simp [vθ, mulVec, dotProduct, Fin.sum_univ_four, tθ]
  all_goals first
    | ring1
    | linear_combination qN_eq
    | linear_combination qN * qN_eq
    | linear_combination qN ^ 2 * qN_eq

/-- The spectral projection of `mulθ` onto `E^u` along `E^s`: `I₃ ⊗ Π` with
`Π = vθ lθᵀ / (lθ · vθ)`. -/
def Pθ : (Fin 3 × Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 × Fin 4 → ℝ) where
  toFun v p := vθ p.2 * (lθ ⬝ᵥ row v p.1) / (3 * qN + 4)
  map_add' v v' := by
    funext p
    simp only [Pi.add_apply]
    rw [show row (v + v') p.1 = row v p.1 + row v' p.1 from rfl, dotProduct_add]
    ring
  map_smul' c v := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show row (c • v) p.1 = c • row v p.1 from rfl, dotProduct_smul, smul_eq_mul]
    ring

theorem Pθ_apply (v : Fin 3 × Fin 4 → ℝ) (p : Fin 3 × Fin 4) :
    Pθ v p = vθ p.2 * (lθ ⬝ᵥ row v p.1) / (3 * qN + 4) := rfl

theorem act_Pθ (v : Fin 3 × Fin 4 → ℝ) : act mulθ (Pθ v) = tθ • Pθ v := by
  rw [act_mulθ]
  funext p
  have hrow : row (Pθ v) p.1 = ((lθ ⬝ᵥ row v p.1) / (3 * qN + 4)) • vθ := by
    funext m; simp [row, Pθ_apply]; ring
  rw [hrow, Matrix.mulVec_smul, mulVec_vθ]
  simp [Pθ_apply]
  ring

theorem Pθ_mem_unstable (v : Fin 3 × Fin 4 → ℝ) : Pθ v ∈ unstableSet mulθ := by
  refine ⟨fun n => (tθ⁻¹) ^ n • Pθ v, by simp, fun n => ?_, ?_⟩
  · rw [map_smul, act_Pθ, smul_smul, pow_succ, mul_assoc,
      inv_mul_cancel₀ (by linarith [tθ_gt] : tθ ≠ 0), mul_one]
  · have h : Filter.Tendsto (fun n : ℕ => (tθ⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (by linarith [tθ_gt])).le
        (inv_lt_one_of_one_lt₀ tθ_gt)
    simpa using h.smul_const (Pθ v)

theorem fθ_act (v : Fin 3 × Fin 4 → ℝ) (i : Fin 3) :
    lθ ⬝ᵥ row (act mulθ v) i = tθ * (lθ ⬝ᵥ row v i) := by
  rw [show row (act mulθ v) i = ((1 - CQ ^ 3).map (Int.cast : ℤ → ℝ)) *ᵥ row v i by
    rw [act_mulθ]; rfl, Matrix.dotProduct_mulVec, lθ_vecMul, smul_dotProduct, smul_eq_mul]

theorem Pθ_stable (v : Fin 3 × Fin 4 → ℝ) (hv : v ∈ stableSet mulθ) : Pθ v = 0 := by
  have hz : ∀ i, lθ ⬝ᵥ row v i = 0 := by
    intro i
    have hc : Continuous (fun x : Fin 3 × Fin 4 → ℝ => lθ ⬝ᵥ row x i) := by
      simp only [dotProduct, row]; fun_prop
    have step : ∀ n, lθ ⬝ᵥ row ((act mulθ ^ (n + 1)) v) i =
        tθ * lθ ⬝ᵥ row ((act mulθ ^ n) v) i := fun n => by
      rw [pow_succ', Module.End.mul_apply, fθ_act]
    have hrel : ∀ n, lθ ⬝ᵥ row ((act mulθ ^ n) v) i =
        tθ ^ n * lθ ⬝ᵥ row ((act mulθ ^ 0) v) i := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [step, ih, pow_succ]; ring
    have h0 : lθ ⬝ᵥ row (0 : Fin 3 × Fin 4 → ℝ) i = 0 := by simp [row, dotProduct]
    have := forward_orbit_zero (f := fun x => lθ ⬝ᵥ row x i) hc h0 tθ_gt
      (s := fun n => (act mulθ ^ n) v) hrel hv
    simpa using this
  funext p
  simp [Pθ_apply, hz]

theorem V4_vθ (l : Fin 4) (hl : l ≠ 1) : (V4 *ᵥ (fun m => (vθ m : ℂ))) l = 0 := by
  have hne : ws l ≠ (qN : ℂ) := fun h => hl (ws_injective (h.trans rfl))
  have hqc : ((qN : ℂ)) ^ 4 = qN + 1 := by exact_mod_cast qN_eq
  have key : (ws l - qN) * (1 + ws l * qN ^ 3 + ws l ^ 2 * qN ^ 2 + ws l ^ 3 * qN) = 0 := by
    linear_combination (qN : ℂ) * ws_eq l - ws l * hqc
  have h2 := (mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr hne)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, V4, vandermonde_apply, vθ]
  linear_combination h2

/-- A vector with a backward `mulθ`-orbit tending to `0` has every row on the line `ℝ vθ`. -/
theorem unstable_row (v : Fin 3 × Fin 4 → ℝ) (hv : v ∈ unstableSet mulθ) (i : Fin 3) :
    row v i = ((lθ ⬝ᵥ row v i) / (3 * qN + 4)) • vθ := by
  obtain ⟨w, hw0, hw, hwt⟩ := hv
  set c := (lθ ⬝ᵥ row v i) / (3 * qN + 4) with hc
  have hkill : ∀ l : Fin 4, l ≠ 1 → (V4 *ᵥ (fun m => (row v i m : ℂ))) l = 0 := by
    intro l hl
    have hl1 : ‖1 - ws l ^ 3‖ < 1 := by
      fin_cases l
      · exact t0
      · exact absurd rfl hl
      · exact t2
      · exact t3
    have hF : Continuous (fun x : Fin 3 × Fin 4 → ℝ => (V4 *ᵥ (fun m => (row x i m : ℂ))) l) := by
      simp only [Matrix.mulVec, dotProduct, row]; fun_prop
    have hrel : ∀ n, (V4 *ᵥ (fun m => (row (w n) i m : ℂ))) l =
        (1 - ws l ^ 3) * (V4 *ᵥ (fun m => (row (w (n + 1)) i m : ℂ))) l := by
      intro n
      rw [← V4_mulVec_θ, ← cast_mulVec, ← hw n, act_mulθ]
      rfl
    have := backward_orbit_zero (F := fun x => (V4 *ᵥ (fun m => (row x i m : ℂ))) l) hF
      (by simp [row, Matrix.mulVec, dotProduct]) hl1 hrel hwt
    simpa [hw0] using this
  have hy : (fun m => ((row v i m - c * vθ m : ℝ) : ℂ)) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero V4_det
    funext l
    have hsplit : (V4 *ᵥ (fun m => ((row v i m - c * vθ m : ℝ) : ℂ))) l =
        (V4 *ᵥ (fun m => (row v i m : ℂ))) l - c * (V4 *ᵥ (fun m => (vθ m : ℂ))) l := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [hsplit]
    by_cases hl : l = 1
    · subst hl
      have hl' : lθ ⬝ᵥ row v i - c * (lθ ⬝ᵥ vθ) = 0 := by
        rw [lθ_vθ, hc]; field_simp [den_t_pos.ne']; ring
      have e1 : (V4 *ᵥ (fun m => (row v i m : ℂ))) 1 = ((lθ ⬝ᵥ row v i : ℝ) : ℂ) := by
        simp [Matrix.mulVec, dotProduct, V4, vandermonde_apply, lθ, ws, Complex.ofReal_sum]
      have e2 : (V4 *ᵥ (fun m => (vθ m : ℂ))) 1 = ((lθ ⬝ᵥ vθ : ℝ) : ℂ) := by
        simp [Matrix.mulVec, dotProduct, V4, vandermonde_apply, lθ, ws, Complex.ofReal_sum]
      rw [e1, e2]
      simp only [Pi.zero_apply]
      exact_mod_cast hl'
    · rw [hkill l hl, V4_vθ l hl]; simp
  funext m
  have := congrFun hy m
  simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

theorem Pθ_unstable (v : Fin 3 × Fin 4 → ℝ) (hv : v ∈ unstableSet mulθ) : Pθ v = v := by
  funext p
  have h := congrFun (unstable_row v hv p.1) p.2
  simp only [row, Pi.smul_apply, smul_eq_mul] at h
  rw [Pθ_apply, show v p = v (p.1, p.2) from rfl, h]
  ring

theorem row_sectorRho (u : Fin 3 → ℝ) (i : Fin 3) : lθ ⬝ᵥ row (sectorRho u) i = u i := by
  simp [dotProduct, row, sectorRho, lθ]

theorem Pθ_sectorRho (u : Fin 3 → ℝ) :
    Pθ (sectorRho u) = fun p => u p.1 * (vθ p.2 / (3 * qN + 4)) := by
  funext p
  rw [Pθ_apply, row_sectorRho]
  ring

theorem pairing_vθ : pairing GramQ (fun i => vθ i / (3 * qN + 4))
    (fun i => vθ i / (3 * qN + 4)) = 1 := by
  have hd := den_t_pos.ne'
  simp [pairing, dotProduct, mulVec, Fin.sum_univ_four, GramQ, vθ]
  field_simp
  linear_combination (6 * qN + 12) * qN_eq

theorem dilation_θ :
    ∃ t : ℝ, t ^ 4 = t ^ 3 + 1 ∧ 1 < t ∧ (∀ v ∈ unstableSet mulθ, act mulθ v = t • v) ∧
      ∃ P : (Fin 3 × Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 × Fin 4 → ℝ),
        (∀ v, P v ∈ unstableSet mulθ) ∧ (∀ v ∈ unstableSet mulθ, P v = v) ∧
        (∀ v ∈ stableSet mulθ, P v = 0) ∧
        (∀ v ∈ unstableSet mulθ, ∃! u : Fin 3 → ℝ, P (sectorRho u) = v) ∧
        ∀ u u' : Fin 3 → ℝ,
          pairing (GramRho ⊗ₖ GramQ) (P (sectorRho u)) (P (sectorRho u')) =
            pairing GramRho u u' := by
  refine ⟨tθ, tθ_eq, tθ_gt, fun v hv => ?_, Pθ, Pθ_mem_unstable, Pθ_unstable, Pθ_stable,
    fun v hv => ?_, fun u u' => ?_⟩
  · rw [← Pθ_unstable v hv, act_Pθ]
  · refine ⟨fun i => lθ ⬝ᵥ row v i, ?_, fun u hu => ?_⟩
    · funext p
      have h := congrFun (Pθ_unstable v hv) p
      rw [Pθ_apply] at h
      rw [Pθ_sectorRho, ← h]
      dsimp only
      ring
    · funext i
      have h1 := congrFun hu (i, 0)
      have h2 := congrFun (Pθ_unstable v hv) (i, 0)
      rw [Pθ_sectorRho] at h1
      rw [Pθ_apply] at h2
      simp only [vθ, Matrix.cons_val_zero] at h1 h2
      have hd := den_t_pos.ne'
      field_simp at h1 h2
      linarith
  · have h := pairing_kron_pure GramRho GramQ u u' (fun i => vθ i / (3 * qN + 4))
      (fun i => vθ i / (3 * qN + 4))
    rw [Pθ_sectorRho, Pθ_sectorRho, h, pairing_vθ, mul_one]

/-! ### The signatures of the two sector trace forms -/

theorem formOf_apply {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℤ) (x : n → ℝ) :
    formOf G x = pairing G x x := by
  simp [formOf, pairing, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

/-- The triangular change of variables diagonalizing `GramRho`. -/
def eRho : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x 0 + 2 / 3 * x 2, x 1 + 3 / 2 * x 2, x 2]
  invFun y := ![y 0 - 2 / 3 * y 2, y 1 - 3 / 2 * y 2, y 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by funext i; fin_cases i <;> simp <;> ring
  left_inv x := by funext i; fin_cases i <;> norm_num
  right_inv y := by funext i; fin_cases i <;> norm_num

/-- The triangular change of variables diagonalizing `GramQ`. -/
def eQ : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x := ![x 0 + 3 / 4 * x 3, x 2 + 3 / 4 * x 1, x 1 - 16 / 9 * x 3, x 3]
  invFun y := ![y 0 - 3 / 4 * y 3, y 2 + 16 / 9 * y 3, y 1 - 3 / 4 * (y 2 + 16 / 9 * y 3), y 3]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by funext i; fin_cases i <;> simp <;> ring
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv y := by funext i; fin_cases i <;> simp

theorem equiv_GramRho : QuadraticMap.Equivalent (formOf GramRho)
    (QuadraticMap.weightedSumSquares ℝ (![3, 2, -23 / 6] : Fin 3 → ℝ)) :=
  ⟨{ eRho with
    map_app' := fun x => by
      rw [formOf_apply]
      simp [eRho, pairing, dotProduct, mulVec, Fin.sum_univ_three, GramRho]
      ring }⟩

theorem equiv_GramQ : QuadraticMap.Equivalent (formOf GramQ)
    (QuadraticMap.weightedSumSquares ℝ (![4, 4, -9 / 4, 283 / 36] : Fin 4 → ℝ)) :=
  ⟨{ eQ with
    map_app' := fun x => by
      rw [formOf_apply]
      simp [eQ, pairing, dotProduct, mulVec, Fin.sum_univ_four, GramQ]
      ring }⟩

theorem sig_GramRho : sigPos (formOf GramRho) = 2 ∧ sigNeg (formOf GramRho) = 1 := by
  constructor
  · rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares equiv_GramRho]
    have : {i : Fin 3 | 0 < (![3, 2, -23 / 6] : Fin 3 → ℝ) i} = ↑({0, 1} : Finset (Fin 3)) := by
      ext i; fin_cases i <;> norm_num
    rw [this, Set.ncard_coe_finset]; rfl
  · rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares equiv_GramRho]
    have : {i : Fin 3 | (![3, 2, -23 / 6] : Fin 3 → ℝ) i < 0} = ↑({2} : Finset (Fin 3)) := by
      ext i; fin_cases i <;> norm_num
    rw [this, Set.ncard_coe_finset]; rfl

theorem sig_GramQ : sigPos (formOf GramQ) = 3 ∧ sigNeg (formOf GramQ) = 1 := by
  constructor
  · rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares equiv_GramQ]
    have : {i : Fin 4 | 0 < (![4, 4, -9 / 4, 283 / 36] : Fin 4 → ℝ) i} =
        ↑({0, 1, 3} : Finset (Fin 4)) := by
      ext i; fin_cases i <;> norm_num
    rw [this, Set.ncard_coe_finset]; rfl
  · rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares equiv_GramQ]
    have : {i : Fin 4 | (![4, 4, -9 / 4, 283 / 36] : Fin 4 → ℝ) i < 0} =
        ↑({2} : Finset (Fin 4)) := by
      ext i; fin_cases i <;> norm_num
    rw [this, Set.ncard_coe_finset]; rfl

/-! ### Every element of `ℤ[ρ] ⊗ ℤ[Q]` other than `0, ±1` -/

/-- The eigenvalue of `mulMatrix a` at the pair of roots `(zs p.1, ws p.2)`:
`α(z, w) = Σ a(i,j) z^i w^j`. -/
def αv (a : Fin 3 × Fin 4 → ℤ) (p : Fin 3 × Fin 4) : ℂ :=
  ∑ q : Fin 3 × Fin 4, (a q : ℂ) * (zs p.1 ^ (q.1 : ℕ) * ws p.2 ^ (q.2 : ℕ))

theorem V12_mulMatrix (a : Fin 3 × Fin 4 → ℤ) :
    V12 * (Int.castRingHom ℂ).mapMatrix (mulMatrix a) = diagonal (αv a) * V12 := by
  have hterm : ∀ q : Fin 3 × Fin 4,
      V12 * (Int.castRingHom ℂ).mapMatrix ((Cρ ^ (q.1 : ℕ)) ⊗ₖ (CQ ^ (q.2 : ℕ))) =
        diagonal (fun p => zs p.1 ^ (q.1 : ℕ) * ws p.2 ^ (q.2 : ℕ)) * V12 := fun q =>
    kron_intertwine (intertwine_pow V3_Cρ _) (intertwine_pow V4_CQ _)
  simp only [mulMatrix, map_sum, map_zsmul, Matrix.mul_sum, Matrix.mul_smul, hterm]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_mul, αv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [zsmul_eq_mul]
  ring

theorem eig_mulMatrix (a : Fin 3 × Fin 4 → ℤ) :
    eigenvalues (mulMatrix a) = Multiset.map (αv a) Finset.univ.val ∧
      (((mulMatrix a).det : ℤ) : ℂ) = ∏ p, αv a p :=
  spectral_of_intertwine _ V12 _ V12_det (V12_mulMatrix a)

theorem V12_mulVec_cast (a : Fin 3 × Fin 4 → ℤ) : V12 *ᵥ (fun q => (a q : ℂ)) = αv a := by
  funext p
  simp only [Matrix.mulVec, dotProduct, αv]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [V12, V3, V4, Matrix.kroneckerMap_apply, vandermonde_apply]
  ring

theorem αv_single (p : Fin 3 × Fin 4) : αv (Pi.single (0, 0) 1) p = 1 := by
  simp [αv, Pi.single_apply]

theorem a_eq_of_αv (a : Fin 3 × Fin 4 → ℤ) (c : ℤ) (h : ∀ p, αv a p = c) :
    a = c • Pi.single (0, 0) 1 := by
  have hv : V12 *ᵥ (fun q => ((a q - c * (Pi.single (0, 0) (1 : ℤ) : Fin 3 × Fin 4 → ℤ) q : ℤ) : ℂ)) = 0 := by
    have e : (fun q => ((a q - c * (Pi.single (0, 0) (1 : ℤ) : Fin 3 × Fin 4 → ℤ) q : ℤ) : ℂ)) =
        (fun q => (a q : ℂ)) - (c : ℂ) • (fun q => (((Pi.single (0, 0) (1 : ℤ) : Fin 3 × Fin 4 → ℤ) q : ℤ) : ℂ)) := by
      funext q; simp
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_smul, V12_mulVec_cast, V12_mulVec_cast]
    funext p
    simp [h p, αv_single]
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero V12_det hv
  funext q
  have := congrFun h0 q
  simp only [Pi.zero_apply, Int.cast_eq_zero] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

open HermiteCompositum.Instance in
/-- The complex embedding of `K₃ = ℚ[X]/(X³ − X − 1)` sending the root to `zs k`. -/
def φ₃ (k : Fin 3) : K₃ →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℚ ℂ) (zs k) (by
    simp [HermiteCompositum.Port014.fρ]
    linear_combination zs_eq k)

open HermiteCompositum.Instance in
/-- The complex embedding of `L` sending `ρ ↦ zs p.1` and `Q ↦ ws p.2`. -/
def φL (p : Fin 3 × Fin 4) : L →+* ℂ :=
  AdjoinRoot.lift (φ₃ p.1) (ws p.2) (by
    rw [g, Polynomial.eval₂_map]
    simp [HermiteCompositum.Port014.fQ]
    linear_combination ws_eq p.2)

open HermiteCompositum.Instance in
theorem φL_ρ (p : Fin 3 × Fin 4) : φL p ρ = zs p.1 := by
  simp only [φL, φ₃, HermiteCompositum.Instance.ρ, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of,
    AdjoinRoot.lift_root]

open HermiteCompositum.Instance in
theorem φL_Q (p : Fin 3 × Fin 4) : φL p Q = ws p.2 := by
  simp only [φL, HermiteCompositum.Instance.Q, AdjoinRoot.lift_root]

open HermiteCompositum.Instance in
/-- `β = Σ a(i,j) ρ^i Q^j ∈ L`. -/
def βL (a : Fin 3 × Fin 4 → ℤ) : L :=
  ∑ q : Fin 3 × Fin 4, (a q : L) * (ρ ^ (q.1 : ℕ) * Q ^ (q.2 : ℕ))

theorem φL_β (a : Fin 3 × Fin 4 → ℤ) (p : Fin 3 × Fin 4) : φL p (βL a) = αv a p := by
  simp [βL, αv, map_sum, map_mul, map_intCast, map_pow, φL_ρ, φL_Q]

open HermiteCompositum.Instance in
theorem L_ρ_eq : ρ ^ 3 - ρ - 1 = 0 := by
  have := aeval_ρ
  simpa [HermiteCompositum.Port014.fρ] using this

open HermiteCompositum.Instance in
theorem L_Q_eq : Q ^ 4 - Q - 1 = 0 := by
  have := aeval_Q
  simpa [HermiteCompositum.Port014.fQ] using this

open HermiteCompositum.Instance in
theorem general_part (a : Fin 3 × Fin 4 → ℤ) (h0 : a ≠ 0) (h1 : a ≠ Pi.single (0, 0) 1)
    (h2 : a ≠ -Pi.single (0, 0) 1) :
    (mulMatrix a).det ≠ 0 ∧ IsHyperbolic (mulMatrix a) := by
  have hβ0 : βL a ≠ 0 := by
    intro hβ
    apply h0
    have := a_eq_of_αv a 0 (fun p => by rw [← φL_β, hβ, map_zero, Int.cast_zero])
    simpa using this
  have hne : ∀ p, αv a p ≠ 0 := fun p => by
    rw [← φL_β]; exact (map_ne_zero (φL p)).mpr hβ0
  refine ⟨fun hd => ?_, isHyperbolic_of_eigen (eig_mulMatrix a).1 fun p hp => ?_⟩
  · have := (eig_mulMatrix a).2
    rw [hd, Int.cast_zero] at this
    exact Finset.prod_ne_zero_iff.mpr (fun p _ => hne p) this.symm
  · rw [← φL_β] at hp
    rcases HermiteCompositum.circle_free finrank_L ρ Q L_ρ_eq L_Q_eq (βL a) (φL p) hp with h | h
    · apply h1
      have := a_eq_of_αv a 1 (fun p' => by rw [← φL_β, h, map_one, Int.cast_one])
      simpa using this
    · apply h2
      have := a_eq_of_αv a (-1) (fun p' => by
        rw [← φL_β, h, map_neg, map_one, Int.cast_neg, Int.cast_one])
      simpa using this

/-! ### Power sums of the roots of `x⁴ − x − 1` -/

theorem trace_CQ_pow (n : ℕ) : (((CQ ^ n).trace : ℤ) : ℂ) = ∑ l, ws l ^ n := by
  have h := intertwine_pow V4_CQ n
  have hdet : IsUnit V4.det := isUnit_iff_ne_zero.mpr V4_det
  have hA : (Int.castRingHom ℂ).mapMatrix (CQ ^ n) = V4⁻¹ * (diagonal (ws ^ n) * V4) := by
    rw [← h, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]
  rw [show (((CQ ^ n).trace : ℤ) : ℂ) = ((Int.castRingHom ℂ).mapMatrix (CQ ^ n)).trace by
    simp [Matrix.trace]]
  rw [hA, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
    Matrix.trace_diagonal]
  simp

theorem GramQ_eq_trace (i j : Fin 4) : GramQ i j = (CQ ^ ((i : ℕ) + (j : ℕ))).trace := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem roots_quartic_eq :
    (Polynomial.X ^ 4 - Polynomial.X - 1 : ℂ[X]).roots = Multiset.map ws Finset.univ.val := by
  have h := eig_CQ
  rw [eigenvalues, charpolyCQ] at h
  have hm : (X ^ 4 - X - 1 : ℤ[X]).map (Int.castRingHom ℂ) = X ^ 4 - X - 1 := by simp
  rw [hm] at h
  exact h

end

end Inst

open Inst

/-- `χ_{CQ} = x⁴ − x − 1`. -/
theorem charpoly_CQ : CQ.charpoly = Polynomial.X ^ 4 - Polynomial.X - 1 := charpolyCQ

/-- `det CQ = −1`. -/
theorem det_CQ : CQ.det = -1 := detCQ

/-- `CQ` has no eigenvalue on the unit circle. -/
theorem isHyperbolic_CQ : IsHyperbolic CQ := hyp_CQ

/-- Root location for `x⁴ − x − 1` over `ℂ`: the multiset of roots is `{Q, q′, w, conj w}`. -/
theorem roots_quartic : ∃ (Qr q' : ℝ) (w : ℂ), Qr ^ 4 = Qr + 1 ∧ 1 < Qr ∧ q' ^ 4 = q' + 1 ∧
    q' < 0 ∧ -0.7245 < q' ∧ w.im ≠ 0 ∧ w ^ 4 = w + 1 ∧
    (Polynomial.X ^ 4 - Polynomial.X - 1 : ℂ[X]).roots = {(Qr : ℂ), (q' : ℂ), w, star w} := by
  refine ⟨QR, qN, wC, QR_eq, by linarith [QR_lo], qN_eq, by linarith [qN_hi],
    by have := qN_lo; norm_num at this ⊢; linarith, wC_im.ne', wC_eq, ?_⟩
  rw [roots_quartic_eq, Fin.univ_val_map]
  simp [List.ofFn_succ, ws]
  try rfl

/-- The Gram matrix of `x⁴ − x − 1` is the sum over its roots of `(z^{i+j})`. -/
theorem gramQ_eq_sum_roots (i j : Fin 4) :
    ((GramQ i j : ℤ) : ℂ) =
      ((Polynomial.X ^ 4 - Polynomial.X - 1 : ℂ[X]).roots.map (fun z => z ^ ((i : ℕ) + j))).sum := by
  rw [roots_quartic_eq, Multiset.map_map, GramQ_eq_trace, trace_CQ_pow, ← Finset.sum_eq_multiset_sum]
  rfl

/-- **(8) The sector rings.** On `ℤ[ρ]` (basis `1, ρ, ρ²`) and `ℤ[Q]` (basis `1, Q, Q², Q³`),
multiplication by `ρ`, `ρ⁻¹ = ρ² − 1`, `Q` and `θ = −Q⁻¹ = 1 − Q³` has the stated characteristic
polynomials, is hyperbolic, and needs exactly `1`, `2`, `3`, `1` physical dimensions. The one
expanding eigenvalue of `θ` is real, `t = −1/q′ ≈ 1.38028`. -/
theorem sector_rings :
    Cρ.charpoly = X ^ 3 - X - 1 ∧ (Cρ ^ 2 - 1).charpoly = X ^ 3 + X ^ 2 - 1 ∧
    CQ.charpoly = X ^ 4 - X - 1 ∧ (1 - CQ ^ 3).charpoly = X ^ 4 - X ^ 3 - 1 ∧
    IsHyperbolic Cρ ∧ IsHyperbolic (Cρ ^ 2 - 1) ∧ IsHyperbolic CQ ∧ IsHyperbolic (1 - CQ ^ 3) ∧
    IsLeast (physDims Cρ) 1 ∧ IsLeast (physDims (Cρ ^ 2 - 1)) 2 ∧
    IsLeast (physDims CQ) 3 ∧ IsLeast (physDims (1 - CQ ^ 3)) 1 ∧
    ∀ z ∈ eigenvalues (1 - CQ ^ 3), 1 < ‖z‖ →
      z.im = 0 ∧ (1.3802 : ℝ) < z.re ∧ z.re < 1.3803 := by
  refine ⟨charpoly_Cρ, charpoly_Cρinv, charpolyCQ, charpoly_θmat, hyp_Cρ, hyp_Cρinv, hyp_CQ,
    hyp_θmat, ?_, ?_, ?_, ?_, θ_expanding⟩
  · have := isLeast_physDims_of_isHyperbolic Cρ (by rw [det_Cρ]; norm_num) hyp_Cρ
    rwa [U_Cρ] at this
  · have := isLeast_physDims_of_isHyperbolic (Cρ ^ 2 - 1) (by rw [det_Cρinv]; norm_num) hyp_Cρinv
    rwa [U_Cρinv] at this
  · have := isLeast_physDims_of_isHyperbolic CQ (by rw [detCQ]; norm_num) hyp_CQ
    rwa [U_CQ] at this
  · have := isLeast_physDims_of_isHyperbolic (1 - CQ ^ 3) (by rw [det_θmat]; norm_num) hyp_θmat
    rwa [U_θmat] at this

/-- **(9) The degree-12 lattice `ℤ[ρ] ⊗ ℤ[Q]`.** Every `mulMatrix a` with `a ≠ 0, ±e₀₀` is
invertible and hyperbolic, so it needs exactly `U` physical dimensions; for `ρ`, `θ`, `ρQ` and `Q`
the values are `4`, `3`, `5`, `9`. -/
theorem compositum_lattice :
    (∀ a : Fin 3 × Fin 4 → ℤ, a ≠ 0 → a ≠ Pi.single (0, 0) 1 → a ≠ -Pi.single (0, 0) 1 →
      (mulMatrix a).det ≠ 0 ∧ IsHyperbolic (mulMatrix a) ∧
        IsLeast (physDims (mulMatrix a)) (unstableCount (mulMatrix a))) ∧
    IsHyperbolic mulρ ∧ IsHyperbolic mulθ ∧ IsHyperbolic mulρQ ∧ IsHyperbolic mulQ ∧
    IsLeast (physDims mulρ) 4 ∧ IsLeast (physDims mulθ) 3 ∧
    IsLeast (physDims mulρQ) 5 ∧ IsLeast (physDims mulQ) 9 := by
  refine ⟨fun a h0 h1 h2 => ?_, hyp_mulρ, hyp_mulθ, hyp_mulρQ, hyp_mulQ, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hd, hh⟩ := general_part a h0 h1 h2
    exact ⟨hd, hh, isLeast_physDims_of_isHyperbolic _ hd hh⟩
  · have := isLeast_physDims_of_isHyperbolic mulρ det_mulρ hyp_mulρ
    rwa [U_mulρ] at this
  · have := isLeast_physDims_of_isHyperbolic mulθ det_mulθ hyp_mulθ
    rwa [U_mulθ] at this
  · have := isLeast_physDims_of_isHyperbolic mulρQ det_mulρQ hyp_mulρQ
    rwa [U_mulρQ] at this
  · have := isLeast_physDims_of_isHyperbolic mulQ det_mulQ hyp_mulQ
    rwa [U_mulQ] at this

/-- **(10) The two dilations**, on `ℝ³ ⊗ ℝ⁴` with the pairing of `GramRho ⊗ GramQ`: the spectral
projections carry the quartic, resp. cubic, sector onto `E^u` with multiple exactly `1`, and the
sector forms have types `(3,1)` and `(2,1)`. -/
theorem compositum_dilations :
    (∃ r : ℝ, r ^ 3 = r + 1 ∧ (∀ v ∈ unstableSet mulρ, act mulρ v = r • v) ∧
      ∃ P : (Fin 3 × Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 × Fin 4 → ℝ),
        (∀ v, P v ∈ unstableSet mulρ) ∧ (∀ v ∈ unstableSet mulρ, P v = v) ∧
        (∀ v ∈ stableSet mulρ, P v = 0) ∧
        (∀ v ∈ unstableSet mulρ, ∃! u : Fin 4 → ℝ, P (sectorQ u) = v) ∧
        ∀ u u' : Fin 4 → ℝ,
          pairing (GramRho ⊗ₖ GramQ) (P (sectorQ u)) (P (sectorQ u')) = pairing GramQ u u') ∧
    (∃ t : ℝ, t ^ 4 = t ^ 3 + 1 ∧ 1 < t ∧ (∀ v ∈ unstableSet mulθ, act mulθ v = t • v) ∧
      ∃ P : (Fin 3 × Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 × Fin 4 → ℝ),
        (∀ v, P v ∈ unstableSet mulθ) ∧ (∀ v ∈ unstableSet mulθ, P v = v) ∧
        (∀ v ∈ stableSet mulθ, P v = 0) ∧
        (∀ v ∈ unstableSet mulθ, ∃! u : Fin 3 → ℝ, P (sectorRho u) = v) ∧
        ∀ u u' : Fin 3 → ℝ,
          pairing (GramRho ⊗ₖ GramQ) (P (sectorRho u)) (P (sectorRho u')) =
            pairing GramRho u u') ∧
    sigPos (formOf GramQ) = 3 ∧ sigNeg (formOf GramQ) = 1 ∧
    sigPos (formOf GramRho) = 2 ∧ sigNeg (formOf GramRho) = 1 := by
  exact ⟨dilation_rho, dilation_θ, sig_GramQ.1, sig_GramQ.2, sig_GramRho.1, sig_GramRho.2⟩

end InflationDimension
