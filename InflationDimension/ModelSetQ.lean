module
public import Mathlib
public import InflationDimension.Defs

@[expose] public section

/-!
# The three-dimensional model set of `Q`

On `ℤ⁴ = ℤ[Q]` (basis `1, Q, Q², Q³`, where `Q⁴ = Q + 1`), multiplication by `Q` is the
companion matrix `CQ`. The roots of `x⁴ − x − 1` are a real root `Q > 1`, a real root
`q′ ∈ (−1, 0)` and a non-real pair `w, w̄` of modulus `> 1`. For a root `z`, the functional
`ℓ_z(v) = Σ_j v_j z^j` satisfies `ℓ_z(CQ v) = z ℓ_z(v)`; the four functionals together are the
Vandermonde matrix of the roots, which is invertible.

With the internal coordinate `ℓ = ℓ_{q′}`, the unstable set of `CQ` is `ker ℓ` and the stable set
is the line `ℝ v′`, `v′ = (1, q′³, q′², q′)`. This file proves statement (11): `(ker ℓ, ℝ v′)` is a
`CQ`-invariant cut-and-project scheme with `ℤ⁴ ∩ ker ℓ = 0`; the window `|ℓ| ≤ 1/2` on `ℝ v′` is a
segment, its model set is `{π_E γ : |ℓ(γ)| ≤ 1/2}` and `CQ` maps it into itself; `CQ` has
determinant `−1/q′` on `ker ℓ`; the non-real eigenvalues have `|w|² = 1/(Q|q′|) > 1`; and the form
of `GramQ` has type `(2,1)` on `ker ℓ` and `(1,0)` on `ℝ v′`, from the decomposition of `GramQ` as
the sum over the roots of `(z^{i+j})`.
-/

namespace InflationDimension

open Polynomial Filter Topology Module ComplexConjugate
open scoped Matrix

noncomputable section

namespace QuarticModelSet

/-! ### The real roots of `x⁴ − x − 1` -/

theorem exists_root_Q :
    ∃ Q : ℝ, (12207 / 10000 : ℝ) < Q ∧ Q < 12208 / 10000 ∧ Q ^ 4 = Q + 1 := by
  have hc : ContinuousOn (fun t : ℝ => t ^ 4 - t - 1)
      (Set.Icc (12207 / 10000) (12208 / 10000)) := by fun_prop
  have h := intermediate_value_Ioo (by norm_num : (12207 / 10000 : ℝ) ≤ 12208 / 10000) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 4 - t - 1) (12207 / 10000))
      ((fun t : ℝ => t ^ 4 - t - 1) (12208 / 10000)) := by
    constructor <;> norm_num
  obtain ⟨Q, hQ, hQ0⟩ := h h0
  exact ⟨Q, hQ.1, hQ.2, by simp only at hQ0; linarith⟩

theorem exists_root_q :
    ∃ q : ℝ, (-7245 / 10000 : ℝ) < q ∧ q < -7244 / 10000 ∧ q ^ 4 = q + 1 := by
  have hc : ContinuousOn (fun t : ℝ => t ^ 4 - t - 1)
      (Set.Icc (-7245 / 10000) (-7244 / 10000)) := by fun_prop
  have h := intermediate_value_Ioo' (by norm_num : (-7245 / 10000 : ℝ) ≤ -7244 / 10000) hc
  have h0 : (0 : ℝ) ∈ Set.Ioo ((fun t : ℝ => t ^ 4 - t - 1) (-7244 / 10000))
      ((fun t : ℝ => t ^ 4 - t - 1) (-7245 / 10000)) := by
    constructor <;> norm_num
  obtain ⟨q, hq, hq0⟩ := h h0
  exact ⟨q, hq.1, hq.2, by simp only at hq0; linarith⟩

/-- The two real roots `Q > 1` and `q′ < 0` of `x⁴ − x − 1`, located in rational boxes. -/
structure Roots where
  /-- The root `Q ≈ 1.2207`. -/
  Qr : ℝ
  /-- The root `q′ ≈ −0.7245`. -/
  q : ℝ
  Qr_lo : (12207 / 10000 : ℝ) < Qr
  Qr_hi : Qr < 12208 / 10000
  hQ : Qr ^ 4 = Qr + 1
  q_lo : (-7245 / 10000 : ℝ) < q
  q_hi : q < -7244 / 10000
  hq : q ^ 4 = q + 1

theorem Roots.nonempty : Nonempty Roots := by
  obtain ⟨Q, h1, h2, h3⟩ := exists_root_Q
  obtain ⟨q, h4, h5, h6⟩ := exists_root_q
  exact ⟨⟨Q, q, h1, h2, h3, h4, h5, h6⟩⟩

/-! ### Functionals and the action of `CQ` -/

/-- The functional `ℓ_z(v) = Σ_j v_j z^j` on `ℝ⁴`, for a complex number `z`. -/
def ellC (z : ℂ) : (Fin 4 → ℝ) →ₗ[ℝ] ℂ where
  toFun v := ∑ j, (v j : ℂ) * z ^ (j : ℕ)
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum, mul_assoc]

/-- The internal coordinate `ℓ(v) = Σ_j v_j q^j`, for a real number `q`. -/
def ell (q : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ j, v j * q ^ (j : ℕ)
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum, mul_assoc]

theorem ellC_apply (z : ℂ) (v : Fin 4 → ℝ) : ellC z v = ∑ j, (v j : ℂ) * z ^ (j : ℕ) := rfl

theorem ell_apply (q : ℝ) (v : Fin 4 → ℝ) : ell q v = ∑ j, v j * q ^ (j : ℕ) := rfl

theorem ellC_eq (z : ℂ) (v : Fin 4 → ℝ) :
    ellC z v = v 0 + v 1 * z + v 2 * z ^ 2 + v 3 * z ^ 3 := by
  simp [ellC_apply, Fin.sum_univ_four]

theorem ell_eq (q : ℝ) (v : Fin 4 → ℝ) :
    ell q v = v 0 + v 1 * q + v 2 * q ^ 2 + v 3 * q ^ 3 := by
  simp [ell_apply, Fin.sum_univ_four]

theorem ellC_ofReal (q : ℝ) (v : Fin 4 → ℝ) : ellC (q : ℂ) v = ((ell q v : ℝ) : ℂ) := by
  rw [ellC_eq, ell_eq]; push_cast; ring

theorem act_CQ_apply (v : Fin 4 → ℝ) : act CQ v = ![v 3, v 0 + v 3, v 1, v 2] := by
  ext i
  fin_cases i <;>
    simp [act, CQ, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem ellC_act {z : ℂ} (hz : z ^ 4 = z + 1) (v : Fin 4 → ℝ) :
    ellC z (act CQ v) = z * ellC z v := by
  rw [act_CQ_apply, ellC_eq, ellC_eq]
  simp
  linear_combination (-(v 3 : ℂ)) * hz

theorem ell_act {q : ℝ} (hq : q ^ 4 = q + 1) (v : Fin 4 → ℝ) :
    ell q (act CQ v) = q * ell q v := by
  rw [act_CQ_apply, ell_eq, ell_eq]
  simp
  linear_combination (-(v 3)) * hq

theorem ellC_act_pow {z : ℂ} (hz : z ^ 4 = z + 1) (n : ℕ) (v : Fin 4 → ℝ) :
    ellC z ((act CQ ^ n) v) = z ^ n * ellC z v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ellC_act hz, ih, pow_succ']; ring

theorem ell_act_pow {q : ℝ} (hq : q ^ 4 = q + 1) (n : ℕ) (v : Fin 4 → ℝ) :
    ell q ((act CQ ^ n) v) = q ^ n * ell q v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ell_act hq, ih, pow_succ']; ring

/-- The inverse of `CQ`: multiplication by `Q⁻¹ = Q³ − 1`. -/
def invMap (u : Fin 4 → ℝ) : Fin 4 → ℝ := ![u 1 - u 0, u 2, u 3, u 0]

theorem act_invMap (u : Fin 4 → ℝ) : act CQ (invMap u) = u := by
  rw [act_CQ_apply]
  ext i
  fin_cases i <;> simp [invMap]

theorem invMap_injective : Function.Injective invMap := fun x y h => by
  rw [← act_invMap x, ← act_invMap y, h]

/-- The backward orbit `n ↦ CQ⁻ⁿ v`. -/
def back (v : Fin 4 → ℝ) (n : ℕ) : Fin 4 → ℝ := invMap^[n] v

theorem act_back_succ (v : Fin 4 → ℝ) (n : ℕ) : act CQ (back v (n + 1)) = back v n := by
  simp only [back, Function.iterate_succ_apply', act_invMap]

theorem act_pow_back (v : Fin 4 → ℝ) (n : ℕ) : (act CQ ^ n) (back v n) = v := by
  induction n with
  | zero => simp [back]
  | succ n ih => rw [pow_succ, Module.End.mul_apply, act_back_succ, ih]

theorem ellC_back {z : ℂ} (hz : z ^ 4 = z + 1) (v : Fin 4 → ℝ) (n : ℕ) :
    ellC z (back v n) * z ^ n = ellC z v := by
  induction n with
  | zero => simp [back]
  | succ n ih =>
    have h := ellC_act hz (back v (n + 1))
    rw [act_back_succ] at h
    calc ellC z (back v (n + 1)) * z ^ (n + 1) = (z * ellC z (back v (n + 1))) * z ^ n := by
          ring
      _ = ellC z v := by rw [← h, ih]

theorem ne_zero_of_root {z : ℂ} (hz : z ^ 4 = z + 1) : z ≠ 0 := by
  rintro rfl
  norm_num at hz

/-! ### The lattice `ℤ⁴` -/

theorem mem_intLattice_iff' {v : Fin 4 → ℝ} :
    v ∈ intLattice (Fin 4) ↔ ∃ n : Fin 4 → ℤ, v = fun i => (n i : ℝ) := by
  rw [intLattice, (Pi.basisFun ℝ (Fin 4)).mem_span_iff_repr_mem ℤ]
  simp only [Pi.basisFun_repr, Set.mem_range, algebraMap_int_eq, eq_intCast]
  constructor
  · intro h
    choose n hn using h
    exact ⟨n, funext fun i => (hn i).symm⟩
  · rintro ⟨n, rfl⟩ i
    exact ⟨n i, rfl⟩

theorem act_mem_intLattice' {γ : Fin 4 → ℝ} (hγ : γ ∈ intLattice (Fin 4)) :
    act CQ γ ∈ intLattice (Fin 4) := by
  obtain ⟨n, rfl⟩ := mem_intLattice_iff'.mp hγ
  refine mem_intLattice_iff'.mpr ⟨![n 3, n 0 + n 3, n 1, n 2], ?_⟩
  rw [act_CQ_apply]
  ext i
  fin_cases i <;> simp

theorem act_pow_mem_intLattice' (n : ℕ) {γ : Fin 4 → ℝ} (hγ : γ ∈ intLattice (Fin 4)) :
    (act CQ ^ n) γ ∈ intLattice (Fin 4) := by
  induction n with
  | zero => simpa using hγ
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact act_mem_intLattice' ih

theorem invMap_mem {γ : Fin 4 → ℝ} (hγ : γ ∈ intLattice (Fin 4)) :
    invMap γ ∈ intLattice (Fin 4) := by
  obtain ⟨n, rfl⟩ := mem_intLattice_iff'.mp hγ
  refine mem_intLattice_iff'.mpr ⟨![n 1 - n 0, n 2, n 3, n 0], ?_⟩
  ext i
  fin_cases i <;> simp [invMap]

theorem back_mem {γ : Fin 4 → ℝ} (hγ : γ ∈ intLattice (Fin 4)) (n : ℕ) :
    back γ n ∈ intLattice (Fin 4) := by
  induction n with
  | zero => simpa [back] using hγ
  | succ n ih =>
    simp only [back, Function.iterate_succ_apply'] at ih ⊢
    exact invMap_mem ih

/-- A sequence of lattice vectors tending to `0` reaches `0`. -/
theorem exists_eq_zero_of_tendsto {x : ℕ → Fin 4 → ℝ} (hx : ∀ n, x n ∈ intLattice (Fin 4))
    (hlim : Tendsto x atTop (𝓝 0)) : ∃ N, x N = 0 := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim 1 one_pos
  refine ⟨N, ?_⟩
  have h1 : ‖x N‖ < 1 := by simpa [dist_zero_right] using hN N le_rfl
  obtain ⟨k, hk⟩ := mem_intLattice_iff'.mp (hx N)
  funext j
  have hj : |x N j| < 1 := lt_of_le_of_lt (by simpa using norm_le_pi_norm (x N) j) h1
  have hkj : x N j = k j := by rw [hk]
  rw [hkj] at hj
  have : |k j| < 1 := by exact_mod_cast hj
  rw [Pi.zero_apply, hkj, Int.abs_lt_one_iff.mp this, Int.cast_zero]

/-! ### The characteristic polynomial and determinant of `CQ` -/

theorem charpoly_CQ_eq : CQ.charpoly = X ^ 4 - X - 1 := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.charmatrix_apply, CQ,
    Matrix.submatrix_apply, Fin.succAbove]
  ring

theorem det_CQ_eq : CQ.det = -1 := by
  rw [Matrix.det_eq_sign_charpoly_coeff, charpoly_CQ_eq]
  simp

theorem det_act_CQ : LinearMap.det (act CQ) = -1 := by
  rw [act, LinearMap.det_toLin']
  have : (CQ.map (Int.cast : ℤ → ℝ)).det = ((CQ.det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det CQ).symm
  rw [this, det_CQ_eq]
  norm_num

/-- A root of a real monic quadratic with negative discriminant has `|z|²` equal to the constant
term. -/
theorem normSq_root_of_disc_neg (b c : ℝ) (hd : b ^ 2 - 4 * c < 0) (z : ℂ)
    (hz : z ^ 2 + b * z + c = 0) : Complex.normSq z = c := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp [pow_two] at hre him
  have him' : z.im * (2 * z.re + b) = 0 := by linarith
  rcases mul_eq_zero.mp him' with h | h
  · rw [h] at hre
    nlinarith [sq_nonneg (2 * z.re + b)]
  · have hx : z.re = -b / 2 := by linarith
    rw [Complex.normSq_apply]
    rw [hx] at hre ⊢
    nlinarith

/-! ### The Gram matrix `GramQ` as a sum over the roots -/

theorem formOf_GramQ_apply (x : Fin 4 → ℝ) : formOf GramQ x =
    4 * x 0 ^ 2 + 6 * x 0 * x 3 + 6 * x 1 * x 2 + 8 * x 1 * x 3 + 4 * x 2 ^ 2 + 3 * x 3 ^ 2 := by
  simp [formOf, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply, Fin.sum_univ_four, GramQ]
  ring

/-- The power sums `4, 0, 0, 3, 4, 0, 3` of four numbers `Q, q, u, ū` with `z⁴ = z + 1`,
`u + ū = −(Q + q)`, `u ū = (Q + q)² − Q q`, `(Q + q)((Q + q)² − 2 Q q) = 1`, written as the
identity of quadratic forms `Σ G_{ij} x_i x_j = Σ_z (Σ_j x_j z^j)²`. -/
theorem gram_sum_roots {Q q u ub : ℂ} (hQ : Q ^ 4 = Q + 1) (hq : q ^ 4 = q + 1)
    (hu : u ^ 4 = u + 1) (hub : ub ^ 4 = ub + 1) (hs : u + ub = -(Q + q))
    (hP : u * ub = (Q + q) ^ 2 - Q * q) (E1 : (Q + q) * ((Q + q) ^ 2 - 2 * (Q * q)) = 1)
    (x0 x1 x2 x3 : ℂ) :
    4 * x0 ^ 2 + 6 * x0 * x3 + 6 * x1 * x2 + 8 * x1 * x3 + 4 * x2 ^ 2 + 3 * x3 ^ 2 =
      (x0 + x1 * Q + x2 * Q ^ 2 + x3 * Q ^ 3) ^ 2 + (x0 + x1 * q + x2 * q ^ 2 + x3 * q ^ 3) ^ 2 +
      (x0 + x1 * u + x2 * u ^ 2 + x3 * u ^ 3) ^ 2 +
      (x0 + x1 * ub + x2 * ub ^ 2 + x3 * ub ^ 3) ^ 2 := by
  have p1 : Q + q + u + ub = 0 := by linear_combination hs
  have p2 : Q ^ 2 + q ^ 2 + u ^ 2 + ub ^ 2 = 0 := by
    linear_combination (u + ub - (Q + q)) * hs - 2 * hP
  have p3 : Q ^ 3 + q ^ 3 + u ^ 3 + ub ^ 3 = 3 := by
    linear_combination ((u + ub) ^ 2 - (u + ub) * (Q + q) + (Q + q) ^ 2 - 3 * u * ub) * hs +
      3 * (Q + q) * hP + 3 * E1
  have p4 : Q ^ 4 + q ^ 4 + u ^ 4 + ub ^ 4 = 4 := by
    linear_combination hQ + hq + hu + hub + p1
  have p5 : Q ^ 5 + q ^ 5 + u ^ 5 + ub ^ 5 = 0 := by
    linear_combination Q * hQ + q * hq + u * hu + ub * hub + p2 + p1
  have p6 : Q ^ 6 + q ^ 6 + u ^ 6 + ub ^ 6 = 3 := by
    linear_combination Q ^ 2 * hQ + q ^ 2 * hq + u ^ 2 * hu + ub ^ 2 * hub + p3 + p2
  linear_combination (-(2 * x0 * x1)) * p1 + (-(2 * x0 * x2 + x1 ^ 2)) * p2 +
    (-(2 * x0 * x3 + 2 * x1 * x2)) * p3 + (-(2 * x1 * x3 + x2 ^ 2)) * p4 +
    (-(2 * x2 * x3)) * p5 + (-(x3 ^ 2)) * p6

namespace Roots

variable (R : Roots)

/-! ### The complex roots -/

/-- `a = Q + q′`. -/
def a : ℝ := R.Qr + R.q

/-- `m = Q q′`. -/
def m : ℝ := R.Qr * R.q

/-- `c = a² − m`, the product of the complex pair. -/
def c : ℝ := R.a ^ 2 - R.m

/-- The imaginary part of the complex root. -/
def β : ℝ := Real.sqrt (R.c - R.a ^ 2 / 4)

/-- The complex root `w = −a/2 + iβ` of `x² + a x + c`. -/
def w : ℂ := ⟨-R.a / 2, R.β⟩

theorem Qr_pos : 0 < R.Qr := by linarith [R.Qr_lo]

theorem one_lt_Qr : 1 < R.Qr := by linarith [R.Qr_lo]

theorem q_neg : R.q < 0 := by linarith [R.q_hi]

theorem q_ne_zero : R.q ≠ 0 := R.q_neg.ne

theorem abs_q_lt_one : |R.q| < 1 := by
  rw [abs_lt]; constructor <;> linarith [R.q_lo, R.q_hi]

theorem Qr_ne_q : R.Qr ≠ R.q := (R.q_neg.trans R.Qr_pos).ne'

theorem m_neg : R.m < 0 := mul_neg_of_pos_of_neg R.Qr_pos R.q_neg

theorem e1 : R.a * (R.a ^ 2 - 2 * R.m) = 1 := by
  have hsub : R.Qr - R.q ≠ 0 := sub_ne_zero.mpr R.Qr_ne_q
  have : (R.Qr - R.q) * (R.a * (R.a ^ 2 - 2 * R.m) - 1) = 0 := by
    simp only [a, m]; linear_combination R.hQ - R.hq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hsub
  · linarith

theorem e2 : R.m * R.c = -1 := by
  have hsub : R.Qr - R.q ≠ 0 := sub_ne_zero.mpr R.Qr_ne_q
  have : (R.Qr - R.q) * (R.m * R.c + 1) = 0 := by
    simp only [a, m, c]; linear_combination R.q * R.hQ - R.Qr * R.hq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hsub
  · linarith

theorem disc_pos : 0 < R.c - R.a ^ 2 / 4 := by
  have := R.m_neg
  simp only [c]; nlinarith [sq_nonneg R.a]

theorem β_sq : R.β ^ 2 = R.c - R.a ^ 2 / 4 := Real.sq_sqrt R.disc_pos.le

theorem β_pos : 0 < R.β := Real.sqrt_pos.2 R.disc_pos

@[simp] theorem w_re : R.w.re = -R.a / 2 := rfl

@[simp] theorem w_im : R.w.im = R.β := rfl

theorem w_add_conj : R.w + conj R.w = -((R.Qr : ℂ) + R.q) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, w_re, Complex.neg_re, Complex.ofReal_re,
      a]; ring
  · simp only [Complex.add_im, Complex.conj_im, w_im, Complex.neg_im, Complex.ofReal_im]; ring

theorem w_mul_conj : R.w * conj R.w = ((R.Qr : ℂ) + R.q) ^ 2 - R.Qr * R.q := by
  have hc : ((R.Qr : ℂ) + R.q) ^ 2 - R.Qr * R.q = ((R.c : ℝ) : ℂ) := by
    simp only [c, a, m]; push_cast; ring
  rw [hc]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, w_re, w_im,
      Complex.ofReal_re]
    linear_combination R.β_sq
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, w_re, w_im,
      Complex.ofReal_im]; ring

theorem normSq_w : Complex.normSq R.w = R.c := by
  rw [Complex.normSq_apply, w_re, w_im]
  linear_combination R.β_sq

theorem w_root : R.w ^ 4 = R.w + 1 := by
  have h1 := R.w_add_conj
  have h2 := R.w_mul_conj
  have e1 : ((R.Qr : ℂ) + R.q) * (((R.Qr : ℂ) + R.q) ^ 2 - 2 * (R.Qr * R.q)) = 1 := by
    have := R.e1; simp only [a, m] at this; exact_mod_cast this
  have e2 : ((R.Qr : ℂ) * R.q) * (((R.Qr : ℂ) + R.q) ^ 2 - R.Qr * R.q) = -1 := by
    have := R.e2; simp only [a, m, c] at this; exact_mod_cast this
  -- `w² + a w + c = 0` from the sum and the product of the pair
  have hw2 : R.w ^ 2 + ((R.Qr : ℂ) + R.q) * R.w +
      (((R.Qr : ℂ) + R.q) ^ 2 - R.Qr * R.q) = 0 := by
    linear_combination R.w * h1 - h2
  linear_combination (R.w ^ 2 - ((R.Qr : ℂ) + R.q) * R.w + R.Qr * R.q) * hw2 +
    R.w * e1 - e2

theorem c_eq : R.c = 1 / (R.Qr * |R.q|) := by
  have h := R.e2
  have hm : R.Qr * -R.q ≠ 0 := (mul_pos R.Qr_pos (by linarith [R.q_neg])).ne'
  rw [abs_of_neg R.q_neg, eq_div_iff hm]
  simp only [m] at h
  linear_combination -h

theorem one_lt_c : 1 < R.c := by
  rw [R.c_eq, abs_of_neg R.q_neg]
  have h0 : 0 < R.Qr * -R.q := mul_pos R.Qr_pos (by linarith [R.q_neg])
  have h1 : R.Qr * -R.q < 1 := by nlinarith [R.Qr_hi, R.q_lo, R.Qr_pos]
  rw [lt_div_iff₀ h0]; linarith

theorem one_lt_norm_w : 1 < ‖R.w‖ := by
  have h : ‖R.w‖ ^ 2 = R.c := by rw [Complex.sq_norm, R.normSq_w]
  nlinarith [R.one_lt_c, norm_nonneg R.w]

/-- The four roots `Q, q′, w, w̄` of `x⁴ − x − 1`. -/
def rts : Fin 4 → ℂ := ![(R.Qr : ℂ), (R.q : ℂ), R.w, conj R.w]

theorem rts_root (i : Fin 4) : R.rts i ^ 4 = R.rts i + 1 := by
  fin_cases i
  · simp only [rts]; simp; exact_mod_cast R.hQ
  · simp only [rts]; simp; exact_mod_cast R.hq
  · simpa [rts] using R.w_root
  · have := congrArg conj R.w_root
    simpa [rts, map_pow] using this

theorem rts_one : R.rts 1 = (R.q : ℂ) := rfl

theorem rts_injective : Function.Injective R.rts := by
  have hβ := R.β_pos
  have hlt : R.q < R.Qr := R.q_neg.trans R.Qr_pos
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [rts, Complex.ext_iff] at h ⊢ <;> linarith

theorem norm_rts {i : Fin 4} (hi : i ≠ 1) : 1 < ‖R.rts i‖ := by
  fin_cases i
  · simp only [rts]; simp; rw [abs_of_pos R.Qr_pos]; exact R.one_lt_Qr
  · exact absurd rfl hi
  · simpa [rts] using R.one_lt_norm_w
  · simpa [rts, Complex.norm_conj] using R.one_lt_norm_w

theorem rts_ne_q {i : Fin 4} (hi : i ≠ 1) : R.rts i ≠ (R.q : ℂ) := by
  intro h
  exact hi (R.rts_injective (h.trans R.rts_one.symm))

/-! ### The Vandermonde matrix of the roots -/

/-- The Vandermonde matrix of the four roots: its rows are the functionals `ℓ_z`. -/
def V : Matrix (Fin 4) (Fin 4) ℂ := Matrix.vandermonde R.rts

theorem V_det_ne_zero : R.V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr R.rts_injective

theorem V_mulVec (x : Fin 4 → ℝ) :
    R.V *ᵥ (fun j => (x j : ℂ)) = fun i => ellC (R.rts i) x := by
  ext i
  simp [V, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, ellC_apply, mul_comm]

/-- If every root functional tends to `0` along a sequence, the sequence tends to `0`. -/
theorem tendsto_of_ellC {x : ℕ → Fin 4 → ℝ}
    (h : ∀ i, Tendsto (fun n => ellC (R.rts i) (x n)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  set xc : ℕ → Fin 4 → ℂ := fun n j => (x n j : ℂ) with hxc
  have h1 : Tendsto (fun n => R.V *ᵥ xc n) atTop (𝓝 0) := by
    have : (fun n => R.V *ᵥ xc n) = fun n i => ellC (R.rts i) (x n) := by
      funext n; exact R.V_mulVec (x n)
    rw [this]; exact tendsto_pi_nhds.2 h
  have hinv : ∀ y : Fin 4 → ℂ, R.V⁻¹ *ᵥ (R.V *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr R.V_det_ne_zero),
      Matrix.one_mulVec]
  have h2 : Tendsto xc atTop (𝓝 0) := by
    have hc : Continuous fun y : Fin 4 → ℂ => R.V⁻¹ *ᵥ y :=
      continuous_const.matrix_mulVec continuous_id
    have := (hc.tendsto 0).comp h1
    simp only [Matrix.mulVec_zero] at this
    refine this.congr (fun n => ?_)
    simp [Function.comp, hinv]
  rw [tendsto_pi_nhds] at h2 ⊢
  intro j
  have := (Complex.continuous_re.tendsto 0).comp (h2 j)
  simpa [xc, Function.comp_def] using this

theorem eq_zero_of_ellC {x : Fin 4 → ℝ} (h : ∀ i, ellC (R.rts i) x = 0) : x = 0 := by
  have := R.tendsto_of_ellC (x := fun _ => x) (fun i => by simp [h i])
  exact tendsto_const_nhds_iff.mp this

/-! ### The scheme `(ker ℓ, ℝ v′)` -/

/-- The `q′`-eigenvector `v′ = (1, q′³, q′², q′)` of `CQ`. -/
def vq : Fin 4 → ℝ := ![1, R.q ^ 3, R.q ^ 2, R.q]

theorem act_vq : act CQ R.vq = R.q • R.vq := by
  rw [act_CQ_apply]
  ext i
  fin_cases i <;> simp [vq] <;> first | ring1 | linear_combination -R.hq

theorem act_pow_vq (n : ℕ) : (act CQ ^ n) R.vq = R.q ^ n • R.vq := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, R.act_vq, smul_smul, pow_succ]

theorem ell_vq : ell R.q R.vq = 1 + 3 * R.q ^ 4 := by
  rw [ell_eq]; simp [vq]; ring

theorem ell_vq_pos : 0 < ell R.q R.vq := by rw [R.ell_vq]; positivity

theorem vq_ne_zero : R.vq ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [vq] at this

/-- `ℓ_z(v′) = 0` for the roots `z ≠ q′`. -/
theorem ellC_vq {i : Fin 4} (hi : i ≠ 1) : ellC (R.rts i) R.vq = 0 := by
  have h := ellC_act (R.rts_root i) R.vq
  rw [R.act_vq, map_smul, Complex.real_smul] at h
  have : (R.rts i - R.q) * ellC (R.rts i) R.vq = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd (sub_eq_zero.mp h') (R.rts_ne_q hi)
  · exact h'

/-- The physical space `E = ker ℓ`. -/
def Eu : Submodule ℝ (Fin 4 → ℝ) := LinearMap.ker (ell R.q)

/-- The internal space `H = ℝ v′`. -/
def Es : Submodule ℝ (Fin 4 → ℝ) := ℝ ∙ R.vq

theorem mem_Eu {v : Fin 4 → ℝ} : v ∈ R.Eu ↔ ell R.q v = 0 := LinearMap.mem_ker

theorem ell_surjective : Function.Surjective (ell R.q) := fun t =>
  ⟨(t / ell R.q R.vq) • R.vq, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ R.ell_vq_pos.ne']⟩

theorem isCompl : IsCompl R.Eu R.Es :=
  Submodule.isCompl_span_singleton_of_isCoatom_of_notMem
    (LinearMap.isCoatom_ker_of_surjective R.ell_surjective)
    (by rw [mem_Eu]; exact R.ell_vq_pos.ne')

theorem mapsTo_Eu : ∀ v ∈ R.Eu, act CQ v ∈ R.Eu := by
  intro v hv
  rw [mem_Eu] at hv ⊢
  rw [ell_act R.hq, hv, mul_zero]

theorem mapsTo_Es : ∀ v ∈ R.Es, act CQ v ∈ R.Es := by
  intro v hv
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, R.act_vq, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- `π_H x = (ℓ x / ℓ v′) v′`. -/
theorem projH_apply (x : Fin 4 → ℝ) :
    R.Es.projection R.Eu R.isCompl.symm x = (ell R.q x / ell R.q R.vq) • R.vq := by
  have h1 : x - (ell R.q x / ell R.q R.vq) • R.vq ∈ R.Eu := by
    rw [mem_Eu, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ R.ell_vq_pos.ne', sub_self]
  have h2 : (ell R.q x / ell R.q R.vq) • R.vq ∈ R.Es :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  calc R.Es.projection R.Eu R.isCompl.symm x
      = R.Es.projection R.Eu R.isCompl.symm
          ((x - (ell R.q x / ell R.q R.vq) • R.vq) + (ell R.q x / ell R.q R.vq) • R.vq) := by
        rw [sub_add_cancel]
    _ = (ell R.q x / ell R.q R.vq) • R.vq := by
        rw [map_add, Submodule.projection_apply_of_mem_right R.isCompl.symm h1,
          Submodule.projection_apply_of_mem_left R.isCompl.symm h2, zero_add]

/-- `π_E x = x − (ℓ x / ℓ v′) v′`. -/
theorem projE_apply (x : Fin 4 → ℝ) :
    R.Eu.projection R.Es R.isCompl x = x - (ell R.q x / ell R.q R.vq) • R.vq := by
  have := Submodule.projection_eq_self_sub_projection R.isCompl.symm x
  rw [R.projH_apply] at this
  exact this

theorem inj : ∀ γ ∈ intLattice (Fin 4), γ ∈ R.Es → γ = 0 := by
  intro γ hγ hH
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hH
  have hseq : ∀ n, (act CQ ^ n) (t • R.vq) = (R.q ^ n * t) • R.vq := by
    intro n; rw [map_smul, R.act_pow_vq, smul_smul, mul_comm]
  have hlim : Tendsto (fun n => (act CQ ^ n) (t • R.vq)) atTop (𝓝 0) := by
    simp_rw [hseq]
    have := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one R.abs_q_lt_one).mul_const t).smul_const
      R.vq
    simpa using this
  obtain ⟨N, hN⟩ := exists_eq_zero_of_tendsto (fun n => act_pow_mem_intLattice' n hγ) hlim
  rw [hseq, smul_eq_zero] at hN
  rcases hN with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (pow_ne_zero _ R.q_ne_zero)
    · simp [h']
  · exact absurd h R.vq_ne_zero

theorem tendsto_back {v : Fin 4 → ℝ} (hv : v ∈ R.Eu) : Tendsto (back v) atTop (𝓝 0) := by
  apply R.tendsto_of_ellC
  intro i
  by_cases hi : i = 1
  · subst hi
    have h0 : ellC (R.rts 1) v = 0 := by
      rw [R.rts_one, ellC_ofReal, (R.mem_Eu).mp hv, Complex.ofReal_zero]
    have : ∀ n, ellC (R.rts 1) (back v n) = 0 := by
      intro n
      have h := ellC_back (R.rts_root 1) v n
      rw [h0] at h
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (ne_zero_of_root (R.rts_root 1)))
    simp [this]
  · have hz := R.norm_rts hi
    have hz0 := ne_zero_of_root (R.rts_root i)
    have h : ∀ n, ellC (R.rts i) (back v n) = ellC (R.rts i) v * (R.rts i)⁻¹ ^ n := by
      intro n
      rw [← ellC_back (R.rts_root i) v n, inv_pow, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hz0), mul_one]
    simp_rw [h]
    have h1 : Tendsto (fun n => (R.rts i)⁻¹ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hz)
    simpa using h1.const_mul (ellC (R.rts i) v)

/-- Aperiodicity: `ℤ⁴ ∩ ker ℓ = 0`. -/
theorem aperiodic : ∀ γ ∈ intLattice (Fin 4), γ ∈ R.Eu → γ = 0 := by
  intro γ hγ hE
  obtain ⟨N, hN⟩ := exists_eq_zero_of_tendsto (back_mem hγ) (R.tendsto_back hE)
  rw [← act_pow_back γ N, hN, map_zero]

theorem dense : (R.Es : Set (Fin 4 → ℝ)) ⊆
    closure (R.Es.projection R.Eu R.isCompl.symm '' (intLattice (Fin 4) : Set (Fin 4 → ℝ))) := by
  let G : AddSubgroup ℝ := (intLattice (Fin 4)).toAddSubgroup.map (ell R.q).toAddMonoidHom
  have hG : Dense (G : Set ℝ) := by
    apply AddSubgroup.dense_of_not_isolated_zero
    intro ε hε
    have hq2 : R.q ^ 2 < 1 := by nlinarith [R.q_lo, R.q_hi]
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hq2
    have hpos : (0 : ℝ) < R.q ^ 2 := by nlinarith [R.q_neg]
    refine ⟨(R.q ^ 2) ^ n, ?_, pow_pos hpos n, hn⟩
    refine AddSubgroup.mem_map.mpr ⟨(act CQ ^ (2 * n)) (Pi.single 0 1), ?_, ?_⟩
    · exact act_pow_mem_intLattice' _
        (mem_intLattice_iff'.mpr ⟨Pi.single 0 1, by ext i; fin_cases i <;> simp⟩)
    · simp only [LinearMap.toAddMonoidHom_coe]
      rw [ell_act_pow R.hq, pow_mul, ell_eq]
      simp
  intro h hh
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hh
  have hφ : Continuous fun s : ℝ => (s / ell R.q R.vq) • R.vq :=
    (continuous_id.div_const _).smul continuous_const
  have himg : (fun s : ℝ => (s / ell R.q R.vq) • R.vq) '' (G : Set ℝ) ⊆
      R.Es.projection R.Eu R.isCompl.symm '' (intLattice (Fin 4) : Set (Fin 4 → ℝ)) := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hs
    exact ⟨γ, hγ, by rw [R.projH_apply]; rfl⟩
  have ht : t • R.vq = (fun s : ℝ => (s / ell R.q R.vq) • R.vq) (t * ell R.q R.vq) := by
    simp only [mul_div_cancel_right₀ _ R.ell_vq_pos.ne']
  rw [ht]
  apply closure_mono himg
  apply image_closure_subset_closure_image hφ
  exact ⟨_, by rw [hG.closure_eq]; trivial, rfl⟩

/-- The `CQ`-invariant scheme `(ker ℓ, ℝ v′)` on `ℤ⁴`. -/
def scheme : InvariantCPS CQ where
  E := R.Eu
  H := R.Es
  isCompl := R.isCompl
  mapsTo_E := R.mapsTo_Eu
  mapsTo_H := R.mapsTo_Es
  inj := R.inj
  dense := R.dense

/-! ### `E = E^u`, `H = E^s` -/

theorem unstableSet_eq : unstableSet CQ = (R.Eu : Set (Fin 4 → ℝ)) := by
  ext v
  constructor
  · rintro ⟨u, hu0, hu, hlim⟩
    have hpow : ∀ n, ell R.q v = R.q ^ n * ell R.q (u n) := by
      intro n
      induction n with
      | zero => simp [hu0]
      | succ n ih => rw [ih, ← hu n, ell_act R.hq, pow_succ]; ring
    have hlim' : Tendsto (fun n => |ell R.q (u n)|) atTop (𝓝 0) := by
      have := (((ell R.q).continuous_of_finiteDimensional.tendsto 0).comp hlim).abs
      simpa [Function.comp_def] using this
    have hle : ∀ n, |ell R.q v| ≤ |ell R.q (u n)| := by
      intro n
      rw [hpow n, abs_mul, abs_pow]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (pow_le_one₀ (abs_nonneg _) R.abs_q_lt_one.le)
    have h0 : |ell R.q v| ≤ 0 := ge_of_tendsto' hlim' hle
    exact (R.mem_Eu).mpr (abs_nonpos_iff.mp h0)
  · intro hv
    exact ⟨back v, rfl, fun n => act_back_succ v n, R.tendsto_back hv⟩

theorem stableSet_eq : stableSet CQ = (R.Es : Set (Fin 4 → ℝ)) := by
  ext v
  constructor
  · intro hv
    have hv' : Tendsto (fun n : ℕ => (act CQ ^ n) v) atTop (𝓝 0) := hv
    have hz0 : ∀ i : Fin 4, i ≠ 1 → ellC (R.rts i) v = 0 := by
      intro i hi
      have hlim : Tendsto (fun n => ‖ellC (R.rts i) ((act CQ ^ n) v)‖) atTop (𝓝 0) := by
        have := (((ellC (R.rts i)).continuous_of_finiteDimensional.tendsto 0).comp hv').norm
        simpa [Function.comp_def] using this
      have hle : ∀ n, ‖ellC (R.rts i) v‖ ≤ ‖ellC (R.rts i) ((act CQ ^ n) v)‖ := by
        intro n
        rw [ellC_act_pow (R.rts_root i), norm_mul, norm_pow]
        exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (R.norm_rts hi).le)
      exact norm_le_zero_iff.mp (ge_of_tendsto' hlim hle)
    have hd : v - (ell R.q v / ell R.q R.vq) • R.vq = 0 := by
      apply R.eq_zero_of_ellC
      intro i
      rw [map_sub, map_smul]
      by_cases hi : i = 1
      · subst hi
        rw [R.rts_one, ellC_ofReal, ellC_ofReal, Complex.real_smul, ← Complex.ofReal_mul,
          ← Complex.ofReal_sub, div_mul_cancel₀ _ R.ell_vq_pos.ne', sub_self,
          Complex.ofReal_zero]
      · rw [hz0 i hi, R.ellC_vq hi, smul_zero, sub_zero]
    rw [sub_eq_zero] at hd
    rw [hd]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    show Tendsto (fun n : ℕ => (act CQ ^ n) (t • R.vq)) atTop (𝓝 0)
    have : (fun n : ℕ => (act CQ ^ n) (t • R.vq)) = fun n => R.q ^ n • (t • R.vq) := by
      funext n; rw [map_smul, R.act_pow_vq, smul_comm]
    rw [this]
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one R.abs_q_lt_one).smul_const (t • R.vq)

/-! ### The interval window -/

/-- The window `{h ∈ H : |ℓ h| ≤ 1/2}`. -/
def window : Set (Fin 4 → ℝ) := {h | h ∈ R.Es ∧ |ell R.q h| ≤ 1 / 2}

theorem window_eq_segment :
    R.window = segment ℝ ((-(2 * ell R.q R.vq)⁻¹) • R.vq) ((2 * ell R.q R.vq)⁻¹ • R.vq) := by
  have hpos := R.ell_vq_pos
  set M := (2 * ell R.q R.vq)⁻¹ with hM
  have hM0 : 0 < M := by positivity
  have hMl : M * ell R.q R.vq = 1 / 2 := by rw [hM]; field_simp
  have hseg : segment ℝ ((-M) • R.vq) (M • R.vq) =
      (fun t : ℝ => t • R.vq) '' Set.Icc (-M) M := by
    have := image_segment (f := (LinearMap.toSpanSingleton ℝ (Fin 4 → ℝ) R.vq).toAffineMap)
      (a := -M) (b := M)
    simp only [LinearMap.coe_toAffineMap, LinearMap.toSpanSingleton_apply] at this
    rw [← this, segment_eq_Icc (by linarith)]
  rw [hseg]
  ext h
  constructor
  · rintro ⟨hh, hle⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hh
    refine ⟨t, ?_, rfl⟩
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos hpos] at hle
    exact abs_le.mp (le_of_mul_le_mul_right (hle.trans hMl.symm.le) hpos)
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos hpos, ← hMl]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ht) hpos.le

theorem ball_subset_window :
    Metric.ball (0 : Fin 4 → ℝ) (1 / 8) ∩ (R.Es : Set (Fin 4 → ℝ)) ⊆ R.window := by
  rintro h ⟨hb, hh⟩
  refine ⟨hh, ?_⟩
  have hn : ‖h‖ < 1 / 8 := by simpa using hb
  have hj : ∀ j : Fin 4, |h j * R.q ^ (j : ℕ)| ≤ ‖h‖ := by
    intro j
    rw [abs_mul, abs_pow]
    have h1 : |h j| ≤ ‖h‖ := by simpa using norm_le_pi_norm h j
    have h2 : |R.q| ^ (j : ℕ) ≤ 1 := pow_le_one₀ (abs_nonneg _) R.abs_q_lt_one.le
    calc |h j| * |R.q| ^ (j : ℕ) ≤ ‖h‖ * 1 :=
          mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
      _ = ‖h‖ := mul_one _
  calc |ell R.q h| = |∑ j, h j * R.q ^ (j : ℕ)| := rfl
    _ ≤ ∑ j, |h j * R.q ^ (j : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, ‖h‖ := Finset.sum_le_sum (fun j _ => hj j)
    _ = 4 * ‖h‖ := by simp
    _ ≤ 1 / 2 := by linarith

theorem isWindow : R.scheme.IsWindow R.window := by
  refine ⟨fun h hh => hh.1, ?_, 0, Submodule.zero_mem _, 1 / 8, by norm_num,
    R.ball_subset_window⟩
  rw [R.window_eq_segment]
  exact (Metric.isBounded_closedBall).subset (segment_subset_closedBall_left _ _)

theorem ell_πH (γ : Fin 4 → ℝ) : ell R.q (R.scheme.πH γ) = ell R.q γ := by
  show ell R.q (R.Es.projection R.Eu R.isCompl.symm γ) = ell R.q γ
  rw [R.projH_apply, map_smul, smul_eq_mul, div_mul_cancel₀ _ R.ell_vq_pos.ne']

theorem πE_act (x : Fin 4 → ℝ) : R.scheme.πE (act CQ x) = act CQ (R.scheme.πE x) := by
  show R.Eu.projection R.Es R.isCompl (act CQ x) = act CQ (R.Eu.projection R.Es R.isCompl x)
  rw [R.projE_apply, R.projE_apply, map_sub, map_smul, R.act_vq, smul_smul, ell_act R.hq]
  congr 2
  ring

theorem modelSet_eq : R.scheme.modelSet R.window =
    {x | ∃ γ ∈ intLattice (Fin 4), |ell R.q γ| ≤ 1 / 2 ∧ R.scheme.πE γ = x} := by
  ext x
  simp only [InvariantCPS.modelSet, window, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨γ, hγ, ⟨_, hle⟩, rfl⟩
    refine ⟨γ, hγ, ?_, rfl⟩
    rwa [R.ell_πH] at hle
  · rintro ⟨γ, hγ, hle, rfl⟩
    exact ⟨γ, hγ, ⟨Submodule.projection_apply_mem R.isCompl.symm γ, by rwa [R.ell_πH]⟩, rfl⟩

theorem mapsTo_modelSet :
    Set.MapsTo (act CQ) (R.scheme.modelSet R.window) (R.scheme.modelSet R.window) := by
  rw [R.modelSet_eq]
  rintro _ ⟨γ, hγ, hle, rfl⟩
  refine ⟨act CQ γ, act_mem_intLattice' hγ, ?_, R.πE_act γ⟩
  rw [ell_act R.hq, abs_mul]
  calc |R.q| * |ell R.q γ| ≤ 1 * |ell R.q γ| :=
        mul_le_mul_of_nonneg_right R.abs_q_lt_one.le (abs_nonneg _)
    _ ≤ 1 / 2 := by linarith

/-! ### The determinant on `E` -/

theorem det_restrict_Es : LinearMap.det ((act CQ).restrict R.mapsTo_Es) = R.q := by
  have h : (act CQ).restrict R.mapsTo_Es = R.q • LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨v, hv⟩
    apply Subtype.ext
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp [map_smul, R.act_vq, smul_smul, mul_comm]
  have hf : finrank ℝ R.Es = 1 := finrank_span_singleton R.vq_ne_zero
  rw [h, LinearMap.det_smul, LinearMap.det_id, mul_one, hf, pow_one]

theorem det_split : LinearMap.det (act CQ) =
    LinearMap.det ((act CQ).restrict R.mapsTo_Eu) *
      LinearMap.det ((act CQ).restrict R.mapsTo_Es) := by
  let e := Submodule.prodEquivOfIsCompl R.Eu R.Es R.isCompl
  have h : act CQ = (e : (R.Eu × R.Es) →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ
      (LinearMap.prodMap ((act CQ).restrict R.mapsTo_Eu) ((act CQ).restrict R.mapsTo_Es)) ∘ₗ
      (e.symm : (Fin 4 → ℝ) →ₗ[ℝ] (R.Eu × R.Es)) := by
    apply LinearMap.ext
    intro x
    obtain ⟨p, rfl⟩ := e.surjective x
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  have h2 := congrArg LinearMap.det h
  rw [LinearMap.det_conj, LinearMap.det_prodMap] at h2
  exact h2

theorem det_restrict_Eu : LinearMap.det ((act CQ).restrict R.mapsTo_Eu) = -1 / R.q := by
  have h := R.det_split
  rw [det_act_CQ, R.det_restrict_Es] at h
  rw [eq_div_iff R.q_ne_zero]
  linarith

/-! ### The non-real eigenvalues -/

theorem eigenvalue_norm {z : ℂ} (hz : z ∈ eigenvalues CQ) (him : z.im ≠ 0) :
    ‖z‖ ^ 2 = 1 / (R.Qr * |R.q|) ∧ 1 < ‖z‖ := by
  have hroot : z ^ 4 = z + 1 := by
    rw [eigenvalues, charpoly_CQ_eq] at hz
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one] at hz
    have hne : (X ^ 4 - X - 1 : ℂ[X]) ≠ 0 := by
      intro h
      have := congrArg (Polynomial.eval 0) h
      simp at this
    have := (Polynomial.mem_roots hne).mp hz
    simp at this
    linear_combination this
  have e1 : (R.a : ℂ) * ((R.a : ℂ) ^ 2 - 2 * R.m) = 1 := by exact_mod_cast R.e1
  have e2 : (R.m : ℂ) * R.c = -1 := by exact_mod_cast R.e2
  have ha : (R.a : ℂ) = R.Qr + R.q := by simp [a]
  have hm : (R.m : ℂ) = R.Qr * R.q := by simp [m]
  have hc : (R.c : ℂ) = (R.a : ℂ) ^ 2 - R.m := by simp [c]
  have hfac : (z - R.Qr) * (z - R.q) * (z ^ 2 + (R.a : ℂ) * z + (R.c : ℂ)) = 0 := by
    have : (z - R.Qr) * (z - R.q) = z ^ 2 - (R.a : ℂ) * z + R.m := by rw [ha, hm]; ring
    rw [this]
    linear_combination hroot + (z ^ 2 - (R.a : ℂ) * z) * hc - z * e1 + e2
  have h1 : z - (R.Qr : ℂ) ≠ 0 := by
    intro h; apply him; have := congrArg Complex.im h; simpa using this
  have h2 : z - (R.q : ℂ) ≠ 0 := by
    intro h; apply him; have := congrArg Complex.im h; simpa using this
  have hq2 : z ^ 2 + (R.a : ℂ) * z + (R.c : ℂ) = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h h1
      · exact absurd h h2
    · exact h
  have hd : R.a ^ 2 - 4 * R.c < 0 := by
    have := R.disc_pos; linarith
  have hn : Complex.normSq z = R.c := normSq_root_of_disc_neg R.a R.c hd z hq2
  have hsq : ‖z‖ ^ 2 = R.c := by rw [Complex.sq_norm, hn]
  refine ⟨hsq.trans R.c_eq, ?_⟩
  nlinarith [R.one_lt_c, norm_nonneg z]

/-! ### The signatures of `GramQ` on `E` and on `H` -/

theorem ellC_conj (x : Fin 4 → ℝ) : ellC (conj R.w) x = conj (ellC R.w x) := by
  rw [ellC_eq, ellC_eq]; simp

/-- `Σ G_{ij} x_i x_j = ℓ_Q(x)² + ℓ_{q′}(x)² + 2 (Re ℓ_w(x))² − 2 (Im ℓ_w(x))²`. -/
theorem form_decomp (x : Fin 4 → ℝ) : formOf GramQ x =
    ell R.Qr x ^ 2 + ell R.q x ^ 2 + 2 * (ellC R.w x).re ^ 2 - 2 * (ellC R.w x).im ^ 2 := by
  apply Complex.ofReal_injective
  have E1 : ((R.Qr : ℂ) + R.q) * (((R.Qr : ℂ) + R.q) ^ 2 - 2 * ((R.Qr : ℂ) * R.q)) = 1 := by
    have := R.e1; simp only [a, m] at this; exact_mod_cast this
  have hub : conj R.w ^ 4 = conj R.w + 1 := by
    have := congrArg conj R.w_root; simpa [map_pow] using this
  have key := gram_sum_roots (by exact_mod_cast R.hQ) (by exact_mod_cast R.hq) R.w_root hub
    R.w_add_conj R.w_mul_conj E1 (x 0) (x 1) (x 2) (x 3)
  have h1 : ((ell R.Qr x ^ 2 + ell R.q x ^ 2 + 2 * (ellC R.w x).re ^ 2 -
      2 * (ellC R.w x).im ^ 2 : ℝ) : ℂ) = ellC (R.Qr : ℂ) x ^ 2 + ellC (R.q : ℂ) x ^ 2 +
        ellC R.w x ^ 2 + ellC (conj R.w) x ^ 2 := by
    rw [ellC_ofReal, ellC_ofReal, R.ellC_conj]
    apply Complex.ext <;> simp [sq] <;> ring
  rw [h1, formOf_GramQ_apply, ellC_eq, ellC_eq, ellC_eq, ellC_eq]
  push_cast
  linear_combination key

theorem finrank_Eu : finrank ℝ R.Eu = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker (ell R.q)
  rw [LinearMap.range_eq_top.mpr R.ell_surjective, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at h
  show finrank ℝ (LinearMap.ker (ell R.q)) = 3
  omega

theorem finrank_Es : finrank ℝ R.Es = 1 := finrank_span_singleton R.vq_ne_zero

/-- The coordinates `(ℓ_Q, Re ℓ_w, Im ℓ_w)` on `E`. -/
def coordE : R.Eu →ₗ[ℝ] (Fin 3 → ℝ) :=
  LinearMap.pi ![(ell R.Qr).comp R.Eu.subtype,
    (Complex.reLm.comp (ellC R.w)).comp R.Eu.subtype,
    (Complex.imLm.comp (ellC R.w)).comp R.Eu.subtype]

theorem coordE_injective : Function.Injective R.coordE := by
  refine (injective_iff_map_eq_zero R.coordE).mpr fun x hx => ?_
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  simp [coordE] at h0 h1 h2
  have hw : ellC R.w (x : Fin 4 → ℝ) = 0 := Complex.ext h1 h2
  have hx' : (x : Fin 4 → ℝ) = 0 := by
    apply R.eq_zero_of_ellC
    intro i
    fin_cases i
    · show ellC (R.Qr : ℂ) _ = 0
      rw [ellC_ofReal, h0, Complex.ofReal_zero]
    · show ellC (R.q : ℂ) _ = 0
      rw [ellC_ofReal, (R.mem_Eu).mp x.2, Complex.ofReal_zero]
    · exact hw
    · show ellC (conj R.w) _ = 0
      rw [R.ellC_conj, hw, map_zero]
  exact Subtype.ext hx'

theorem equiv_E : QuadraticMap.Equivalent ((formOf GramQ).comp R.Eu.subtype)
    (QuadraticMap.weightedSumSquares ℝ (![1, 2, -2] : Fin 3 → ℝ)) := by
  have hsurj : Function.Surjective R.coordE :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [R.finrank_Eu, Module.finrank_fin_fun])).mp R.coordE_injective
  let f : R.Eu ≃ₗ[ℝ] (Fin 3 → ℝ) := LinearEquiv.ofBijective R.coordE ⟨R.coordE_injective, hsurj⟩
  have hcomp : (formOf GramQ).comp R.Eu.subtype =
      (QuadraticMap.weightedSumSquares ℝ (![1, 2, -2] : Fin 3 → ℝ)).comp
        (f : R.Eu →ₗ[ℝ] (Fin 3 → ℝ)) := by
    ext x
    have hq0 : ell R.q (x : Fin 4 → ℝ) = 0 := (R.mem_Eu).mp x.2
    rw [QuadraticMap.comp_apply, QuadraticMap.comp_apply, Submodule.subtype_apply,
      R.form_decomp, hq0, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three]
    simp [f, coordE]
    ring
  rw [hcomp]
  exact ⟨(QuadraticMap.isometryEquivOfCompLinearEquiv _ f).symm⟩

/-- The coordinate `ℓ_{q′}` on `H`. -/
def coordH : R.Es →ₗ[ℝ] (Fin 1 → ℝ) := LinearMap.pi ![(ell R.q).comp R.Es.subtype]

theorem coordH_injective : Function.Injective R.coordH := by
  refine (injective_iff_map_eq_zero R.coordH).mpr fun x hx => ?_
  have h0 := congrFun hx 0
  simp [coordH] at h0
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp x.2
  rw [← ht, map_smul, smul_eq_mul] at h0
  have ht0 : t = 0 := (mul_eq_zero.mp h0).resolve_right R.ell_vq_pos.ne'
  apply Subtype.ext
  rw [Submodule.coe_zero, ← ht, ht0, zero_smul]

theorem form_on_Es {x : Fin 4 → ℝ} (hx : x ∈ R.Es) : formOf GramQ x = ell R.q x ^ 2 := by
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have h0 : ell R.Qr R.vq = 0 := by
    have := R.ellC_vq (i := 0) (by decide)
    simp only [rts] at this
    rw [show ![(R.Qr : ℂ), (R.q : ℂ), R.w, conj R.w] 0 = (R.Qr : ℂ) from rfl, ellC_ofReal]
      at this
    exact_mod_cast this
  have h2 : ellC R.w R.vq = 0 := R.ellC_vq (i := 2) (by decide)
  rw [R.form_decomp]
  simp only [map_smul, h0, h2]
  simp

theorem equiv_H : QuadraticMap.Equivalent ((formOf GramQ).comp R.Es.subtype)
    (QuadraticMap.weightedSumSquares ℝ (![1] : Fin 1 → ℝ)) := by
  have hsurj : Function.Surjective R.coordH :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [R.finrank_Es, Module.finrank_fin_fun])).mp R.coordH_injective
  let f : R.Es ≃ₗ[ℝ] (Fin 1 → ℝ) := LinearEquiv.ofBijective R.coordH ⟨R.coordH_injective, hsurj⟩
  have hcomp : (formOf GramQ).comp R.Es.subtype =
      (QuadraticMap.weightedSumSquares ℝ (![1] : Fin 1 → ℝ)).comp
        (f : R.Es →ₗ[ℝ] (Fin 1 → ℝ)) := by
    ext x
    rw [QuadraticMap.comp_apply, QuadraticMap.comp_apply, Submodule.subtype_apply,
      R.form_on_Es x.2, QuadraticMap.weightedSumSquares_apply]
    simp [f, coordH]
    ring
  rw [hcomp]
  exact ⟨(QuadraticMap.isometryEquivOfCompLinearEquiv _ f).symm⟩

theorem sig_E : sigPos ((formOf GramQ).comp R.Eu.subtype) = 2 ∧
    sigNeg ((formOf GramQ).comp R.Eu.subtype) = 1 := by
  have h := R.equiv_E
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares h,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares h]
  constructor
  · have : {i : Fin 3 | 0 < (![1, 2, -2] : Fin 3 → ℝ) i} = {0, 1} := by
      ext i; fin_cases i <;> norm_num
    rw [this, Set.ncard_pair (by decide)]
  · have : {i : Fin 3 | (![1, 2, -2] : Fin 3 → ℝ) i < 0} = {2} := by
      ext i; fin_cases i <;> norm_num
    rw [this, Set.ncard_singleton]

theorem sig_H : sigPos ((formOf GramQ).comp R.Es.subtype) = 1 ∧
    sigNeg ((formOf GramQ).comp R.Es.subtype) = 0 := by
  have h := R.equiv_H
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares h,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares h]
  constructor
  · have : {i : Fin 1 | 0 < (![1] : Fin 1 → ℝ) i} = Set.univ := by
      ext i; fin_cases i; norm_num
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  · have : {i : Fin 1 | (![1] : Fin 1 → ℝ) i < 0} = ∅ := by
      ext i; fin_cases i; norm_num
    rw [this, Set.ncard_empty]

end Roots

end QuarticModelSet

open QuarticModelSet in
/-- **The three-dimensional model set of `Q`.** On `ℤ[Q]` (`CQ`), `(E^u, E^s)` is a `Q`-invariant
scheme with `ℤ⁴ ∩ E = 0`. With `q′ < 0` the negative real root of `x⁴ − x − 1` and the internal
coordinate `h ↦ Σ_j h_j q′^j`, the window `|·| ≤ 1/2` is a segment, its model set is
`{π_E γ : |Σ_j γ_j q′^j| ≤ 1/2}`, and `Q` maps it into itself. `Q` multiplies volume on `E` by
`−1/q′`, its non-real eigenvalues have modulus squared `1/(Q|q′|)` and exceed `1` in modulus, and
the form of `GramQ` has type `(2,1)` on `E` and `(1,0)` on `H`. -/
theorem quartic_model_set :
    ∃ Qr q' : ℝ, Qr ^ 4 = Qr + 1 ∧ 1 < Qr ∧ q' ^ 4 = q' + 1 ∧ q' < 0 ∧
    ∃ S : InvariantCPS CQ,
      (S.E : Set (Fin 4 → ℝ)) = unstableSet CQ ∧ (S.H : Set (Fin 4 → ℝ)) = stableSet CQ ∧
      (∀ γ ∈ intLattice (Fin 4), γ ∈ S.E → γ = 0) ∧
      (∀ W : Set (Fin 4 → ℝ), W = {h | h ∈ S.H ∧ |∑ j, h j * q' ^ (j : ℕ)| ≤ 1 / 2} →
        S.IsWindow W ∧ (∃ a b : Fin 4 → ℝ, W = segment ℝ a b) ∧
        S.modelSet W =
          {x | ∃ γ ∈ intLattice (Fin 4), |∑ j, γ j * q' ^ (j : ℕ)| ≤ 1 / 2 ∧ S.πE γ = x} ∧
        Set.MapsTo (act CQ) (S.modelSet W) (S.modelSet W)) ∧
      LinearMap.det ((act CQ).restrict S.mapsTo_E) = -1 / q' ∧
      (∀ z ∈ eigenvalues CQ, z.im ≠ 0 → ‖z‖ ^ 2 = 1 / (Qr * |q'|) ∧ 1 < ‖z‖) ∧
      sigPos ((formOf GramQ).comp S.E.subtype) = 2 ∧
      sigNeg ((formOf GramQ).comp S.E.subtype) = 1 ∧
      sigPos ((formOf GramQ).comp S.H.subtype) = 1 ∧
      sigNeg ((formOf GramQ).comp S.H.subtype) = 0 := by
  obtain ⟨R⟩ := Roots.nonempty
  refine ⟨R.Qr, R.q, R.hQ, R.one_lt_Qr, R.hq, R.q_neg, R.scheme, R.unstableSet_eq.symm,
    R.stableSet_eq.symm, R.aperiodic, ?_, R.det_restrict_Eu,
    fun z hz him => R.eigenvalue_norm hz him, R.sig_E.1, R.sig_E.2, R.sig_H.1, R.sig_H.2⟩
  rintro W rfl
  exact ⟨R.isWindow, ⟨_, _, R.window_eq_segment⟩, R.modelSet_eq, R.mapsTo_modelSet⟩

end

end InflationDimension
