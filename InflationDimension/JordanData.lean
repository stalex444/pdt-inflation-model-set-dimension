module
public import Mathlib
public import InflationDimension.Count
public import InflationDimension.Hyperbolic

@[expose] public section
/-!
# Jordan data without Jordan form, and the largest power-bounded invariant summand

For an endomorphism `f` of a finite-dimensional vector space and a polynomial `p`, the dimensions
of `ker p(f)`, `ker p(f)²` and `ker p(f) ∩ im p(f)` carry the Jordan data of `f` at the roots of
`p` without a Jordan form:

* `finrank_ker_sq` (any field): `dim ker p(f)² = dim ker p(f) + dim (ker p(f) ∩ im p(f))`;
* `socleCount f c = dim ker c(f) − dim (ker c(f) ∩ im c(f))`, additive over coprime factors
  (`socleCount_mul`); for `c` with distinct roots it counts the Jordan blocks of size one at the
  roots of `c`.

**Rational Jordan data.** For an integer matrix `A` and a monic irreducible factor `p` of `χ_A`
over `ℚ`: the multiplicity `m_p` (`mult`), the number
`r₁(p) = (2 dim_ℚ ker p(A) − dim_ℚ ker p(A)²) / deg p` of Jordan blocks of size one at each root
of `p` (`singleBlocks`; the division is exact, `natDegree_mul_singleBlocks`), and the numbers
`s_p`, `c_p`, `u_p` of roots of `p` of modulus `< 1`, `= 1`, `> 1` (`insideRoots`, `circleRoots`,
`expandingRoots`). Further, `dim_ℚ ker p(A)^{m_p} = m_p deg p` (`kerRank_mult`), `r₁(p) ≤ m_p`, and
`r₁(p) = m_p` if and only if `ker p(A)² = ker p(A)` (`singleBlocks_eq_mult_iff`).

**From `ℚ` to `ℝ`.** A kernel of a rational polynomial in `A` has the same dimension over `ℚ` and
over `ℝ` (`finrank_ker_real`, through the rank normal form), and every monic irreducible real
factor `q` of `p` has real socle count `deg q · r₁(p)` (`socleCount_real_factor`): the real span of
a rational `A`-invariant subspace killed by `p(A)` carries a rational matrix of `A`, so its
characteristic polynomial is a power of `p`, and each real factor of `p` takes its share.

**The largest power-bounded invariant summand.** Let `f` be an endomorphism of a
finite-dimensional real normed space `V`, and factor `χ_f = q_s q_c q_u` over `ℝ` into monic factors
with all complex roots inside, on, and outside the unit circle, with `c` the product of the
distinct irreducible factors of `q_c` (`DiskSplit`; one exists, `exists_diskSplit`). The largest
dimension of an `f`-invariant subspace `H` that has an `f`-invariant complement and on which `f`
is power-bounded is `deg q_s + socleCount f c` (`isGreatest_powerBounded_summand`). The upper bound
rests on two facts: a power-bounded `f` is semisimple on its unit-circle part (a Jordan block of
size `≥ 2` at a root of modulus one grows linearly, `mulVec_sub_smul_eq_zero`), and an invariant
summand `H` killed by `p(f)` misses `im p(f)`, so `dim H ≤ dim ker p(f) − dim (ker p(f) ∩ im p(f))`
(`socle_bound`). The bound is attained by `ker q_s(f) ⊕ U`, with `U` an invariant complement of
`ker c(f) ∩ im c(f)` in `ker c(f)`.

For an integer matrix `A` the value is `dim E^s + Σ_{|λ|=1} s_λ`, with `s_λ = r₁(minpoly_ℚ λ)`
(`largest_powerBounded_summand_jordan`), that is, `Σ_p (m_p s_p + c_p r₁(p))` over the distinct
rational factors `p` of `χ_A` (`largest_powerBounded_summand_factors`).
-/

namespace InflationDimension

open Polynomial Module
open scoped Matrix

noncomputable section

namespace JordanData

/-! ### Kernels and images of `p(f)` over a field -/

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem aeval_mul_apply (f : Module.End K V) (p q : K[X]) (v : V) :
    aeval f (p * q) v = aeval f p (aeval f q v) := by
  rw [map_mul, Module.End.mul_apply]

theorem aeval_comm_apply (f : Module.End K V) (p q : K[X]) (v : V) :
    aeval f p (aeval f q v) = aeval f q (aeval f p v) := by
  rw [← aeval_mul_apply, mul_comm, aeval_mul_apply]

theorem aeval_mem_of_invariant (f : Module.End K V) {W : Submodule K V}
    (hW : ∀ v ∈ W, f v ∈ W) (p : K[X]) : ∀ v ∈ W, aeval f p v ∈ W := by
  induction p using Polynomial.induction_on with
  | C a =>
    intro v hv
    simpa [Module.algebraMap_end_apply] using W.smul_mem a hv
  | add p q hp hq =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp v hv) (hq v hv)
  | monomial n a ih =>
    intro v hv
    have e1 : (C a * X ^ (n + 1) : K[X]) = C a * X ^ n * X := by ring
    rw [e1, aeval_mul_apply, aeval_X]
    exact ih _ (hW v hv)

theorem aeval_restrict_apply (f : Module.End K V) {U : Submodule K V} (hU : ∀ v ∈ U, f v ∈ U)
    (p : K[X]) (v : U) : ((aeval (f.restrict hU) p) v : V) = aeval f p (v : V) := by
  induction p using Polynomial.induction_on generalizing v with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    have e1 : (C a * X ^ (n + 1) : K[X]) = C a * X ^ n * X := by ring
    rw [e1, map_mul (aeval (f.restrict hU)) (C a * X ^ n) X, map_mul (aeval f) (C a * X ^ n) X,
      aeval_X, aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

theorem mapsTo_ker (f : Module.End K V) (p : K[X]) :
    ∀ v ∈ LinearMap.ker (aeval f p), f v ∈ LinearMap.ker (aeval f p) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have := aeval_comm_apply f p X v
  rw [aeval_X] at this
  rw [this, hv, map_zero]

theorem mapsTo_range (f : Module.End K V) (p : K[X]) :
    ∀ v ∈ LinearMap.range (aeval f p), f v ∈ LinearMap.range (aeval f p) := by
  rintro _ ⟨u, rfl⟩
  refine ⟨f u, ?_⟩
  have := aeval_comm_apply f p X u
  rwa [aeval_X] at this

/-- **The rank identity.** `dim ker p(f)² = dim ker p(f) + dim (ker p(f) ∩ im p(f))`: `p(f)` maps
`ker p(f)²` onto `ker p(f) ∩ im p(f)` with kernel `ker p(f)`. -/
theorem finrank_ker_sq [FiniteDimensional K V] (f : Module.End K V) (p : K[X]) :
    finrank K (LinearMap.ker (aeval f (p ^ 2))) =
      finrank K (LinearMap.ker (aeval f p)) +
        finrank K ↥(LinearMap.ker (aeval f p) ⊓ LinearMap.range (aeval f p)) := by
  have hsq : ∀ v, aeval f (p ^ 2) v = aeval f p (aeval f p v) := fun v => by
    rw [sq, aeval_mul_apply]
  let g : LinearMap.ker (aeval f (p ^ 2)) →ₗ[K] V :=
    (aeval f p).comp (LinearMap.ker (aeval f (p ^ 2))).subtype
  have hle : LinearMap.ker (aeval f p) ≤ LinearMap.ker (aeval f (p ^ 2)) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hsq, hv, map_zero]
  have hker : LinearMap.ker g =
      (LinearMap.ker (aeval f p)).comap (LinearMap.ker (aeval f (p ^ 2))).subtype := by
    ext x
    simp [g]
  have hrange : LinearMap.range g = LinearMap.ker (aeval f p) ⊓ LinearMap.range (aeval f p) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      have hx : aeval f (p ^ 2) (x : V) = 0 := x.2
      rw [hsq] at hx
      exact ⟨hx, ⟨(x : V), rfl⟩⟩
    · rintro ⟨hw, ⟨u, rfl⟩⟩
      have hu : u ∈ LinearMap.ker (aeval f (p ^ 2)) := by
        rw [LinearMap.mem_ker, hsq]
        exact hw
      exact ⟨⟨u, hu⟩, rfl⟩
  have key := LinearMap.finrank_range_add_finrank_ker g
  rw [hker, hrange, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at key
  omega

/-- For coprime `p`, `q`: `dim ker (pq)(f) = dim ker p(f) + dim ker q(f)`. -/
theorem finrank_ker_mul_of_coprime [FiniteDimensional K V] (f : Module.End K V) {p q : K[X]}
    (h : IsCoprime p q) :
    finrank K (LinearMap.ker (aeval f (p * q))) =
      finrank K (LinearMap.ker (aeval f p)) + finrank K (LinearMap.ker (aeval f q)) := by
  have key := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval f p))
    (LinearMap.ker (aeval f q))
  rw [Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f h,
    (Polynomial.disjoint_ker_aeval_of_isCoprime f h).eq_bot, finrank_bot, add_zero] at key
  exact key

/-- **The socle bound.** An invariant subspace `H` with an invariant complement, killed by
`p(f)`, misses `im p(f)`, and `dim H ≤ dim ker p(f) − dim (ker p(f) ∩ im p(f))`. -/
theorem socle_bound [FiniteDimensional K V] (f : Module.End K V) (p : K[X])
    {H H' : Submodule K V} (hc : IsCompl H H') (hH' : ∀ v ∈ H', f v ∈ H')
    (hp : ∀ v ∈ H, aeval f p v = 0) :
    Disjoint H (LinearMap.range (aeval f p)) ∧
      finrank K H + finrank K ↥(LinearMap.ker (aeval f p) ⊓ LinearMap.range (aeval f p)) ≤
        finrank K (LinearMap.ker (aeval f p)) := by
  have hdisj : Disjoint H (LinearMap.range (aeval f p)) := by
    rw [Submodule.disjoint_def]
    rintro v hvH ⟨u, rfl⟩
    have hu : u ∈ H ⊔ H' := by rw [hc.codisjoint.eq_top]; exact Submodule.mem_top
    obtain ⟨h, hh, h', hh', rfl⟩ := Submodule.mem_sup.1 hu
    have hgu : aeval f p (h + h') = aeval f p h' := by
      rw [map_add, hp h hh, zero_add]
    rw [hgu] at hvH ⊢
    exact (Submodule.disjoint_def.1 hc.disjoint) _ hvH (aeval_mem_of_invariant f hH' p h' hh')
  refine ⟨hdisj, ?_⟩
  have hle : H ≤ LinearMap.ker (aeval f p) := fun v hv => hp v hv
  have hinf : H ⊓ (LinearMap.ker (aeval f p) ⊓ LinearMap.range (aeval f p)) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact (Submodule.disjoint_def.1 hdisj) v hv.1 hv.2.2
  have key := Submodule.finrank_sup_add_finrank_inf_eq H
    (LinearMap.ker (aeval f p) ⊓ LinearMap.range (aeval f p))
  rw [hinf, finrank_bot, add_zero] at key
  have hmono := Submodule.finrank_mono (sup_le hle (inf_le_left :
    LinearMap.ker (aeval f p) ⊓ LinearMap.range (aeval f p) ≤ LinearMap.ker (aeval f p)))
  omega

/-- For coprime `q`, `s`: `ker q(f) ∩ im (qs)(f) = ker q(f) ∩ im q(f)` (`s(f)` is invertible on
`ker q(f)²`). -/
theorem ker_inf_range_mul (f : Module.End K V) {q s : K[X]} (h : IsCoprime q s) :
    LinearMap.ker (aeval f q) ⊓ LinearMap.range (aeval f (q * s)) =
      LinearMap.ker (aeval f q) ⊓ LinearMap.range (aeval f q) := by
  apply le_antisymm
  · rintro x ⟨hx, ⟨y, rfl⟩⟩
    exact ⟨hx, ⟨aeval f s y, (aeval_mul_apply f q s y).symm⟩⟩
  · rintro x ⟨hx, ⟨y, rfl⟩⟩
    refine ⟨hx, ?_⟩
    obtain ⟨a, b, hab⟩ := h.pow_left (m := 2)
    have hy : aeval f (q ^ 2) y = 0 := by
      rw [sq, aeval_mul_apply]
      exact hx
    have h1 : aeval f (b * s) y = y := by
      have : aeval f (a * q ^ 2 + b * s) y = y := by rw [hab, map_one, Module.End.one_apply]
      rw [map_add, LinearMap.add_apply, aeval_mul_apply, hy, map_zero, zero_add] at this
      exact this
    refine ⟨aeval f b y, ?_⟩
    rw [← aeval_mul_apply, show q * s * b = q * (b * s) by ring, aeval_mul_apply, h1]

/-- The socle count at `c`: `dim ker c(f) − dim (ker c(f) ∩ im c(f))`. For `c` with distinct
roots it is the number of Jordan blocks of size one of `f` at the roots of `c`. -/
def socleCount (f : Module.End K V) (c : K[X]) : ℕ :=
  finrank K (LinearMap.ker (aeval f c)) -
    finrank K ↥(LinearMap.ker (aeval f c) ⊓ LinearMap.range (aeval f c))

/-- The socle count is `2 dim ker c(f) − dim ker c(f)²`. -/
theorem socleCount_eq [FiniteDimensional K V] (f : Module.End K V) (c : K[X]) :
    socleCount f c =
      2 * finrank K (LinearMap.ker (aeval f c)) - finrank K (LinearMap.ker (aeval f (c ^ 2))) := by
  rw [socleCount, finrank_ker_sq]
  omega

/-- The socle count is additive over coprime factors. -/
theorem socleCount_mul [FiniteDimensional K V] (f : Module.End K V) {a b : K[X]}
    (h : IsCoprime a b) : socleCount f (a * b) = socleCount f a + socleCount f b := by
  have e1 := finrank_ker_mul_of_coprime f h
  have e2 : finrank K (LinearMap.ker (aeval f ((a * b) ^ 2))) =
      finrank K (LinearMap.ker (aeval f (a ^ 2))) +
        finrank K (LinearMap.ker (aeval f (b ^ 2))) := by
    rw [mul_pow]
    exact finrank_ker_mul_of_coprime f h.pow
  have ha := finrank_ker_sq f a
  have hb := finrank_ker_sq f b
  have hab := finrank_ker_sq f (a * b)
  have ta := Submodule.finrank_mono (inf_le_left :
    LinearMap.ker (aeval f a) ⊓ LinearMap.range (aeval f a) ≤ LinearMap.ker (aeval f a))
  have tb := Submodule.finrank_mono (inf_le_left :
    LinearMap.ker (aeval f b) ⊓ LinearMap.range (aeval f b) ≤ LinearMap.ker (aeval f b))
  have tab := Submodule.finrank_mono (inf_le_left : LinearMap.ker (aeval f (a * b)) ⊓
    LinearMap.range (aeval f (a * b)) ≤ LinearMap.ker (aeval f (a * b)))
  rw [socleCount, socleCount, socleCount]
  omega

theorem socleCount_one [FiniteDimensional K V] (f : Module.End K V) : socleCount f 1 = 0 := by
  have h : LinearMap.ker (aeval f (1 : K[X])) = ⊥ := by
    rw [map_one]
    exact LinearMap.ker_id
  rw [socleCount, h, bot_inf_eq, finrank_bot]

/-- The socle count of a product of distinct monic irreducible polynomials is the sum of the
socle counts. -/
theorem socleCount_multiset_prod [FiniteDimensional K V] (f : Module.End K V)
    (s : Multiset K[X]) (hs : s.Nodup) (hirr : ∀ q ∈ s, Irreducible q ∧ q.Monic) :
    socleCount f s.prod = (s.map (socleCount f)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [socleCount_one]
  | cons a t ih =>
    rw [Multiset.nodup_cons] at hs
    have hat : IsCoprime a t.prod := by
      have key : ∀ u : Multiset K[X], (∀ b ∈ u, b ≠ a ∧ Irreducible b ∧ b.Monic) →
          IsCoprime a u.prod := by
        intro u
        induction u using Multiset.induction_on with
        | empty => intro _; simpa using isCoprime_one_right
        | cons b u ihu =>
          intro hu
          rw [Multiset.prod_cons]
          refine IsCoprime.mul_right ?_ (ihu fun c hc => hu c (Multiset.mem_cons_of_mem hc))
          obtain ⟨hba, hbi, hbm⟩ := hu b (Multiset.mem_cons_self b u)
          obtain ⟨hai, ham⟩ := hirr a (Multiset.mem_cons_self a t)
          refine (Irreducible.coprime_iff_not_dvd hai).mpr fun hdvd => hba ?_
          exact (Polynomial.eq_of_monic_of_associated ham hbm (hai.associated_of_dvd hbi hdvd)).symm
      exact key t fun b hb => ⟨fun h => hs.1 (h ▸ hb), hirr b (Multiset.mem_cons_of_mem hb)⟩
    rw [Multiset.prod_cons, socleCount_mul f hat, ih hs.2 fun q hq =>
      hirr q (Multiset.mem_cons_of_mem hq), Multiset.map_cons, Multiset.sum_cons]

/-- Every complex root of `χ_h` is a root of every polynomial annihilating `h`. -/
theorem aeval_eq_zero_of_charpoly_root [Algebra K ℂ] [FiniteDimensional K V]
    (h : Module.End K V) {p : K[X]} (hp : aeval h p = 0) (z : ℂ)
    (hz : aeval z h.charpoly = 0) : aeval z p = 0 := by
  classical
  set b := Module.finBasis K V
  set M := LinearMap.toMatrix b b h with hM
  set MC : Matrix (Fin (finrank K V)) (Fin (finrank K V)) ℂ := M.map (algebraMap K ℂ) with hMC
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
  have hMCp : aeval MC (p.map (algebraMap K ℂ)) = 0 := by
    rw [aeval_map_algebraMap]
    have h2 : MC = (Algebra.ofId K ℂ).mapMatrix M := rfl
    rw [h2, aeval_algHom_apply, hMp, map_zero]
  have hlin : aeval (Matrix.toLin' MC) (p.map (algebraMap K ℂ)) = 0 := by
    have := aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ)
      (n := Fin (finrank K V))).toAlgHom MC (p.map (algebraMap K ℂ))
    have e : Matrix.toLinAlgEquiv' MC = Matrix.toLin' MC := rfl
    erw [e] at this
    erw [this, hMCp, map_zero]
  have hev := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap K ℂ)) hw
  rw [hlin, LinearMap.zero_apply] at hev
  have hne : w ≠ 0 := hw.2
  have : (p.map (algebraMap K ℂ)).eval z = 0 := by
    by_contra hc
    exact hne (smul_eq_zero.mp hev.symm |>.resolve_left hc)
  rwa [eval_map_algebraMap] at this

theorem charpoly_eq_mul_of_isCompl [FiniteDimensional K V] (f : Module.End K V)
    (E H : Submodule K V) (h : IsCompl E H) (hE : ∀ v ∈ E, f v ∈ E) (hH : ∀ v ∈ H, f v ∈ H) :
    f.charpoly = (f.restrict hE).charpoly * (f.restrict hH).charpoly := by
  let e := Submodule.prodEquivOfIsCompl E H h
  have hf : e.conj ((f.restrict hE).prodMap (f.restrict hH)) = f := by
    ext v
    obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
    simp [e, LinearEquiv.conj_apply, Submodule.coe_prodEquivOfIsCompl', map_add]
  exact (congrArg LinearMap.charpoly hf.symm).trans
    ((LinearEquiv.charpoly_conj e _).trans (LinearMap.charpoly_prodMap _ _))

/-- **The dimension lemma** over a field `K ⊆ ℂ`: if `χ_f = q r` with `q`, `r` monic and coprime,
then `dim ker q(f) = deg q`. -/
theorem finrank_ker_aeval_of_coprime [Algebra K ℂ] [FiniteDimensional K V]
    (f : Module.End K V) {q r : K[X]} (hq : q.Monic) (hr : r.Monic) (hχ : f.charpoly = q * r)
    (hcop : IsCoprime q r) : finrank K (LinearMap.ker (aeval f q)) = q.natDegree := by
  have hU := mapsTo_ker f q
  have hW := mapsTo_ker f r
  have hcompl : IsCompl (LinearMap.ker (aeval f q)) (LinearMap.ker (aeval f r)) := by
    refine ⟨Polynomial.disjoint_ker_aeval_of_isCoprime f hcop, ?_⟩
    rw [codisjoint_iff, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop, ← hχ,
      LinearMap.aeval_self_charpoly, LinearMap.ker_zero]
  have hsplit := charpoly_eq_mul_of_isCompl f _ _ hcompl hU hW
  have hq0 : aeval (f.restrict hU) q = 0 := by
    ext v
    rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, aeval_restrict_apply]
    exact v.2
  have hr0 : aeval (f.restrict hW) r = 0 := by
    ext v
    rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, aeval_restrict_apply]
    exact v.2
  have hcopC := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K ℂ q r).mp hcop
  have hc₁ : IsCoprime (f.restrict hU).charpoly r := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K ℂ]
    intro a
    by_cases ha : aeval a (f.restrict hU).charpoly = 0
    · right
      exact (hcopC a).resolve_left (not_not.mpr (aeval_eq_zero_of_charpoly_root _ hq0 a ha))
    · left; exact ha
  have hc₂ : IsCoprime (f.restrict hW).charpoly q := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K ℂ]
    intro a
    by_cases ha : aeval a (f.restrict hW).charpoly = 0
    · right
      exact fun hqa => ((hcopC a).resolve_left (not_not.mpr hqa))
        (aeval_eq_zero_of_charpoly_root _ hr0 a ha)
    · left; exact ha
  have hd₁ : (f.restrict hU).charpoly ∣ q := by
    have : (f.restrict hU).charpoly ∣ q * r := by rw [← hχ, hsplit]; exact dvd_mul_right _ _
    exact hc₁.dvd_of_dvd_mul_right this
  have hd₂ : (f.restrict hW).charpoly ∣ r := by
    have : (f.restrict hW).charpoly ∣ r * q := by
      rw [mul_comm, ← hχ, hsplit]; exact dvd_mul_left _ _
    exact hc₂.dvd_of_dvd_mul_right this
  have hle₁ := Polynomial.natDegree_le_of_dvd hd₁ hq.ne_zero
  have hle₂ := Polynomial.natDegree_le_of_dvd hd₂ hr.ne_zero
  have hsum : (f.restrict hU).charpoly.natDegree + (f.restrict hW).charpoly.natDegree =
      q.natDegree + r.natDegree := by
    rw [← (LinearMap.charpoly_monic _).natDegree_mul (LinearMap.charpoly_monic _), ← hsplit, hχ,
      hq.natDegree_mul hr]
  rw [← LinearMap.charpoly_natDegree (f.restrict hU)]
  omega

end Field

/-! ### Divisibility by the degree over `ℚ` -/

section Rational

variable {U : Type*} [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]

/-- An endomorphism killed by a monic irreducible `p` over `ℚ` has characteristic polynomial a
power of `p`; so the dimension is a multiple of `deg p`. -/
theorem natDegree_dvd_finrank_of_aeval_eq_zero (h : Module.End ℚ U) {p : ℚ[X]}
    (hp : Irreducible p) (hpm : p.Monic) (hpz : aeval h p = 0) :
    p.natDegree ∣ finrank ℚ U := by
  classical
  have hχm : h.charpoly.Monic := LinearMap.charpoly_monic h
  have hall : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors h.charpoly, q = p := by
    intro q hq
    have hqi := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hqm : q.Monic := by
      rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
      exact Polynomial.monic_normalize hqi.ne_zero
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ q (degree_pos_of_irreducible hqi).ne'
    have hzχ : aeval z h.charpoly = 0 := by
      obtain ⟨r, hr⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq
      rw [hr, map_mul, hz, zero_mul]
    exact Count.eq_of_common_root hqi hqm hp hpm hz (aeval_eq_zero_of_charpoly_root h hpz z hzχ)
  have hprod : (UniqueFactorizationMonoid.normalizedFactors h.charpoly).prod = h.charpoly :=
    Polynomial.eq_of_monic_of_associated
      (by simpa using Polynomial.monic_multiset_prod_of_monic _ id (fun q hq => by
        rw [hall q hq]; exact hpm))
      hχm (UniqueFactorizationMonoid.prod_normalizedFactors hχm.ne_zero)
  rw [← LinearMap.charpoly_natDegree h, ← hprod, Multiset.eq_replicate_of_mem hall,
    Multiset.prod_replicate, natDegree_pow]
  exact dvd_mul_left _ _

/-- An endomorphism killed by a monic irreducible `p` over `ℚ` has characteristic polynomial
`p ^ (dim / deg p)`. -/
theorem charpoly_eq_pow_of_aeval_eq_zero (h : Module.End ℚ U) {p : ℚ[X]} (hp : Irreducible p)
    (hpm : p.Monic) (hpz : aeval h p = 0) :
    h.charpoly = p ^ (finrank ℚ U / p.natDegree) := by
  classical
  have hχm : h.charpoly.Monic := LinearMap.charpoly_monic h
  have hall : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors h.charpoly, q = p := by
    intro q hq
    have hqi := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hqm : q.Monic := by
      rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
      exact Polynomial.monic_normalize hqi.ne_zero
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ q (degree_pos_of_irreducible hqi).ne'
    have hzχ : aeval z h.charpoly = 0 := by
      obtain ⟨r, hr⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq
      rw [hr, map_mul, hz, zero_mul]
    exact Count.eq_of_common_root hqi hqm hp hpm hz (aeval_eq_zero_of_charpoly_root h hpz z hzχ)
  have hprod : (UniqueFactorizationMonoid.normalizedFactors h.charpoly).prod = h.charpoly :=
    Polynomial.eq_of_monic_of_associated
      (by simpa using Polynomial.monic_multiset_prod_of_monic _ id (fun q hq => by
        rw [hall q hq]; exact hpm))
      hχm (UniqueFactorizationMonoid.prod_normalizedFactors hχm.ne_zero)
  have hrep := Multiset.eq_replicate_of_mem hall
  set n := Multiset.card (UniqueFactorizationMonoid.normalizedFactors h.charpoly) with hn
  have hχ : h.charpoly = p ^ n := by
    calc h.charpoly = (UniqueFactorizationMonoid.normalizedFactors h.charpoly).prod := hprod.symm
      _ = (Multiset.replicate n p).prod := by rw [← hrep]
      _ = p ^ n := Multiset.prod_replicate n p
  have hdeg : finrank ℚ U = n * p.natDegree := by
    rw [← LinearMap.charpoly_natDegree h, hχ, natDegree_pow]
  rw [hχ, hdeg, Nat.mul_div_cancel _ (Irreducible.natDegree_pos hp)]

/-- An invariant subspace killed by `p(f)`, `p` monic irreducible over `ℚ`, has dimension
divisible by `deg p`. -/
theorem natDegree_dvd_finrank_of_le_ker (f : Module.End ℚ U) {p : ℚ[X]} (hp : Irreducible p)
    (hpm : p.Monic) {W : Submodule ℚ U} (hW : ∀ v ∈ W, f v ∈ W)
    (hWp : ∀ v ∈ W, aeval f p v = 0) : p.natDegree ∣ finrank ℚ W := by
  apply natDegree_dvd_finrank_of_aeval_eq_zero (f.restrict hW) hp hpm
  ext x
  rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, aeval_restrict_apply]
  exact hWp x x.2

end Rational

/-! ### Unit-circle Jordan blocks of a power-bounded complex matrix have size one -/

section ComplexMatrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem eq_zero_of_mulVec (A : Matrix κ κ ℂ) (h : ∀ v, A *ᵥ v = 0) : A = 0 := by
  apply Matrix.toLin'.injective
  rw [map_zero]
  exact LinearMap.ext fun v => by rw [Matrix.toLin'_apply, LinearMap.zero_apply]; exact h v

/-- A complex matrix with uniformly bounded powers has no Jordan block of size `≥ 2` at an
eigenvalue of modulus one: `(M − z)² u = 0` forces `(M − z) u = 0`, since otherwise
`z Mⁿ u = zⁿ⁺¹ u + n zⁿ (M − z) u` grows linearly. -/
theorem mulVec_sub_smul_eq_zero (M : Matrix κ κ ℂ) {K : ℝ}
    (hK : ∀ (n : ℕ) (i j : κ), ‖(M ^ n) i j‖ ≤ K) {z : ℂ} (hz : ‖z‖ = 1) {u : κ → ℂ}
    (hu : (M - z • 1) *ᵥ ((M - z • 1) *ᵥ u) = 0) : (M - z • 1) *ᵥ u = 0 := by
  have hsub : ∀ x : κ → ℂ, (M - z • 1) *ᵥ x = M *ᵥ x - z • x := by
    intro x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hw : M *ᵥ ((M - z • 1) *ᵥ u) = z • ((M - z • 1) *ᵥ u) :=
    sub_eq_zero.mp ((hsub _).symm.trans hu)
  have hMu : M *ᵥ u = z • u + (M - z • 1) *ᵥ u := by rw [hsub]; abel
  have hpow : ∀ n : ℕ, z • ((M ^ n) *ᵥ u) =
      z ^ (n + 1) • u + ((n : ℂ) * z ^ n) • ((M - z • 1) *ᵥ u) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ' M n, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ih, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hMu, hw]
      push_cast
      module
  by_contra hne
  obtain ⟨l, hl⟩ : ∃ l, ((M - z • 1) *ᵥ u) l ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  set w := (M - z • 1) *ᵥ u with hwdef
  set D : ℝ := ∑ j, K * ‖u j‖
  have hb : ∀ n : ℕ, (n : ℝ) * ‖w l‖ ≤ D + ‖u l‖ := by
    intro n
    have h1 := congrFun (hpow n) l
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h1
    have h2 : ‖z * ((M ^ n) *ᵥ u) l‖ ≤ D := by
      rw [norm_mul, hz, one_mul, Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hK n l j) (norm_nonneg _)
    rw [h1] at h2
    have h3 : ‖((n : ℂ) * z ^ n) * w l‖ ≤
        ‖z ^ (n + 1) * u l + ((n : ℂ) * z ^ n) * w l‖ + ‖z ^ (n + 1) * u l‖ := by
      calc ‖((n : ℂ) * z ^ n) * w l‖
          = ‖(z ^ (n + 1) * u l + ((n : ℂ) * z ^ n) * w l) - z ^ (n + 1) * u l‖ := by
            rw [add_sub_cancel_left]
        _ ≤ _ := norm_sub_le _ _
    have e1 : ‖((n : ℂ) * z ^ n) * w l‖ = n * ‖w l‖ := by
      rw [norm_mul, norm_mul, norm_pow, hz, one_pow, mul_one, Complex.norm_natCast]
    have e2 : ‖z ^ (n + 1) * u l‖ = ‖u l‖ := by
      rw [norm_mul, norm_pow, hz, one_pow, one_mul]
    rw [e1, e2] at h3
    linarith
  have hpos : 0 < ‖w l‖ := norm_pos_iff.mpr hl
  obtain ⟨n, hn⟩ := exists_nat_gt ((D + ‖u l‖) / ‖w l‖)
  rw [div_lt_iff₀ hpos] at hn
  linarith [hb n]

theorem aeval_X_sub_C (M : Matrix κ κ ℂ) (z : ℂ) : aeval M (X - C z) = M - z • 1 := by
  rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/-- For distinct roots `S` of modulus one and `M` with bounded powers,
`ker (∏_{z ∈ S} (M − z))² = ker ∏_{z ∈ S} (M − z)`. -/
theorem nodal_mulVec_eq_zero (M : Matrix κ κ ℂ) {K : ℝ}
    (hK : ∀ (n : ℕ) (i j : κ), ‖(M ^ n) i j‖ ≤ K) (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z‖ = 1)
    {u : κ → ℂ} (hu : aeval M (Lagrange.nodal S id ^ 2) *ᵥ u = 0) :
    aeval M (Lagrange.nodal S id) *ᵥ u = 0 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa [Lagrange.nodal_empty] using hu
  have hsum := Lagrange.sum_basis (v := (id : ℂ → ℂ)) (Set.injOn_id _) hne
  have hterm : ∀ i ∈ S, aeval M (Lagrange.basis S id i * Lagrange.nodal S id) *ᵥ u = 0 := by
    intro i hi
    have hb : Lagrange.basis S id i =
        C (Lagrange.nodalWeight S id i) * Lagrange.nodal (S.erase i) id := by
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, ← Lagrange.nodal_erase_eq_nodal_div hi]
    have hn : Lagrange.nodal S id = (X - C i) * Lagrange.nodal (S.erase i) id :=
      Lagrange.nodal_eq_mul_nodal_erase hi
    have hpoly : (X - C i) * (X - C i) * Lagrange.nodal (S.erase i) id ^ 2 =
        Lagrange.nodal S id ^ 2 := by
      rw [hn]; ring
    have hy : (M - i • 1) *ᵥ ((M - i • 1) *ᵥ
        (aeval M (Lagrange.nodal (S.erase i) id ^ 2) *ᵥ u)) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← aeval_X_sub_C, ← map_mul, ← map_mul,
        hpoly]
      exact hu
    have hy' := mulVec_sub_smul_eq_zero M hK (hS i hi) hy
    have hpoly2 : Lagrange.basis S id i * Lagrange.nodal S id =
        C (Lagrange.nodalWeight S id i) * ((X - C i) * Lagrange.nodal (S.erase i) id ^ 2) := by
      rw [hb, hn]; ring
    rw [hpoly2, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec, map_mul, aeval_X_sub_C, ← Matrix.mulVec_mulVec, hy', smul_zero]
  have hnodal : Lagrange.nodal S id = ∑ i ∈ S, Lagrange.basis S id i * Lagrange.nodal S id := by
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [hnodal, map_sum, Matrix.sum_mulVec]
  exact Finset.sum_eq_zero hterm

/-- If `∏_{z ∈ S} (M − z)` is nilpotent, `S` of modulus one and `M` with bounded powers, then
`∏_{z ∈ S} (M − z) = 0`. -/
theorem aeval_nodal_eq_zero_of_pow (M : Matrix κ κ ℂ) {K : ℝ}
    (hK : ∀ (n : ℕ) (i j : κ), ‖(M ^ n) i j‖ ≤ K) (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z‖ = 1)
    {N : ℕ} (hN : aeval M (Lagrange.nodal S id ^ N) = 0) : aeval M (Lagrange.nodal S id) = 0 := by
  have hsq : ∀ v, aeval M (Lagrange.nodal S id) *ᵥ (aeval M (Lagrange.nodal S id) *ᵥ v) = 0 →
      aeval M (Lagrange.nodal S id) *ᵥ v = 0 := by
    intro v hv
    apply nodal_mulVec_eq_zero M hK S hS
    rw [map_pow, sq, ← Matrix.mulVec_mulVec]
    exact hv
  set T := aeval M (Lagrange.nodal S id) with hT
  have hTN : T ^ N = 0 := by rw [hT, ← map_pow]; exact hN
  have key : ∀ k : ℕ, T ^ (k + 1) = 0 → T = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      apply ih
      apply eq_zero_of_mulVec
      intro v
      have h2 : T *ᵥ (T *ᵥ ((T ^ k) *ᵥ v)) = 0 := by
        have e : T ^ (k + 1 + 1) = T * (T * T ^ k) := by rw [pow_succ', pow_succ']
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, ← e, hk, Matrix.zero_mulVec]
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact hsq _ h2
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · rw [pow_zero] at hTN
    rw [← mul_one T, hTN, mul_zero]
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    exact key k hTN

end ComplexMatrix

/-! ### The largest power-bounded invariant summand -/

theorem aeval_mul_eq_zero_iff {p q : ℝ[X]} {z : ℂ} :
    aeval z (p * q) = 0 ↔ aeval z p = 0 ∨ aeval z q = 0 := by
  rw [map_mul, mul_eq_zero]

/-- Real polynomials with no common complex root are coprime. -/
theorem isCoprime_of_roots {p q : ℝ[X]}
    (h : ∀ z : ℂ, aeval z p = 0 → aeval z q = 0 → False) : IsCoprime p q :=
  (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ p q).mpr fun z => by
    by_contra hc
    simp only [not_or, ne_eq, not_not] at hc
    exact h z hc.1 hc.2

/-- A factorization `χ = q_s · q_c · q_u` of a monic real polynomial into monic factors whose
complex roots lie inside, on, and outside the unit circle, together with the product `c` of the
distinct irreducible factors of `q_c`: `c` is monic and squarefree, `c ∣ q_c ∣ c^N`, and over `ℂ`
it is the product of `X − z` over its distinct roots `z ∈ S`, all of modulus one. -/
structure DiskSplit (χ : ℝ[X]) where
  /-- The factor with all roots in the open unit disk. -/
  qs : ℝ[X]
  /-- The factor with all roots on the unit circle. -/
  qc : ℝ[X]
  /-- The factor with all roots outside the closed unit disk. -/
  qu : ℝ[X]
  /-- The product of the distinct irreducible factors of `qc`. -/
  c : ℝ[X]
  /-- The distinct complex roots of `c`. -/
  S : Finset ℂ
  /-- An exponent with `qc ∣ c ^ N`. -/
  N : ℕ
  monic_qs : qs.Monic
  monic_qc : qc.Monic
  monic_qu : qu.Monic
  monic_c : c.Monic
  eq_mul : χ = qs * qc * qu
  root_qs : ∀ z : ℂ, aeval z qs = 0 → ‖z‖ < 1
  root_qc : ∀ z : ℂ, aeval z qc = 0 → ‖z‖ = 1
  root_qu : ∀ z : ℂ, aeval z qu = 0 → 1 < ‖z‖
  squarefree_c : Squarefree c
  map_c : c.map (algebraMap ℝ ℂ) = Lagrange.nodal S id
  norm_S : ∀ z ∈ S, ‖z‖ = 1
  c_dvd : c ∣ qc
  dvd_c_pow : qc ∣ c ^ N

namespace DiskSplit

variable {χ : ℝ[X]} (D : DiskSplit χ)

theorem root_c {z : ℂ} (hz : aeval z D.c = 0) : ‖z‖ = 1 := by
  obtain ⟨r, hr⟩ := D.c_dvd
  exact D.root_qc z (by rw [hr, map_mul, hz, zero_mul])

theorem coprime_s_c : IsCoprime D.qs D.c := isCoprime_of_roots fun z h1 h2 => by
  have := D.root_qs z h1
  have := D.root_c h2
  linarith

theorem coprime_s_qc : IsCoprime D.qs D.qc := isCoprime_of_roots fun z h1 h2 => by
  have := D.root_qs z h1
  have := D.root_qc z h2
  linarith

theorem coprime_s_cu : IsCoprime D.qs (D.qc * D.qu) := isCoprime_of_roots fun z h1 h2 => by
  have := D.root_qs z h1
  rcases aeval_mul_eq_zero_iff.mp h2 with h | h
  · have := D.root_qc z h
    linarith
  · have := D.root_qu z h
    linarith

/-- `deg q_s` is the number of complex roots of `χ` of modulus `< 1`, with multiplicity. -/
theorem natDegree_qs :
    D.qs.natDegree = Multiset.card ((χ.map (algebraMap ℝ ℂ)).roots.filter (fun z => ‖z‖ < 1)) := by
  classical
  have hroots : (χ.map (algebraMap ℝ ℂ)).roots = (D.qs.map (algebraMap ℝ ℂ)).roots +
      (D.qc.map (algebraMap ℝ ℂ)).roots + (D.qu.map (algebraMap ℝ ℂ)).roots := by
    have e : (χ.map (algebraMap ℝ ℂ)).roots =
        ((D.qs * D.qc * D.qu).map (algebraMap ℝ ℂ)).roots := by
      rw [← D.eq_mul]
    have h1 : D.qs.map (algebraMap ℝ ℂ) * D.qc.map (algebraMap ℝ ℂ) ≠ 0 :=
      ((D.monic_qs.map _).mul (D.monic_qc.map _)).ne_zero
    have h2 : D.qs.map (algebraMap ℝ ℂ) * D.qc.map (algebraMap ℝ ℂ) *
        D.qu.map (algebraMap ℝ ℂ) ≠ 0 :=
      (((D.monic_qs.map _).mul (D.monic_qc.map _)).mul (D.monic_qu.map _)).ne_zero
    rw [e, Polynomial.map_mul, Polynomial.map_mul, roots_mul h2, roots_mul h1]
  have hs : ∀ z ∈ (D.qs.map (algebraMap ℝ ℂ)).roots, ‖z‖ < 1 := fun z hz =>
    D.root_qs z ((Count.mem_roots_map_iff D.monic_qs.ne_zero).mp hz)
  have hc : ∀ z ∈ (D.qc.map (algebraMap ℝ ℂ)).roots, ¬ ‖z‖ < 1 := fun z hz => by
    rw [D.root_qc z ((Count.mem_roots_map_iff D.monic_qc.ne_zero).mp hz)]
    exact lt_irrefl 1
  have hu : ∀ z ∈ (D.qu.map (algebraMap ℝ ℂ)).roots, ¬ ‖z‖ < 1 := fun z hz =>
    not_lt.mpr (D.root_qu z ((Count.mem_roots_map_iff D.monic_qu.ne_zero).mp hz)).le
  rw [hroots, Multiset.filter_add, Multiset.filter_add, Multiset.filter_eq_self.mpr hs,
    Multiset.filter_eq_nil.mpr hc, Multiset.filter_eq_nil.mpr hu, add_zero, add_zero]
  exact (IsAlgClosed.card_roots_map_eq_natDegree_of_injective _ (algebraMap ℝ ℂ).injective).symm

end DiskSplit

/-- All complex roots in the open unit disk. -/
def RootsInside (g : ℝ[X]) : Prop := ∀ z : ℂ, aeval z g = 0 → ‖z‖ < 1

/-- All complex roots on the unit circle. -/
def RootsOnCircle (g : ℝ[X]) : Prop := ∀ z : ℂ, aeval z g = 0 → ‖z‖ = 1

open Classical in
/-- **Existence of the splitting.** Every monic real polynomial `χ` has a `DiskSplit`: group the
irreducible factors of `χ` by the modulus of their roots (one modulus per irreducible real
factor), and take for `c` the product of the distinct factors on the unit circle. -/
theorem exists_diskSplit (χ : ℝ[X]) (hχ : χ.Monic) : Nonempty (DiskSplit χ) := by
  have hirr : ∀ g ∈ UniqueFactorizationMonoid.normalizedFactors χ, Irreducible g := fun g hg =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg
  have hmon : ∀ g ∈ UniqueFactorizationMonoid.normalizedFactors χ, g.Monic := fun g hg => by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor g hg]
    exact Polynomial.monic_normalize (hirr g hg).ne_zero
  have hprodmon : ∀ s ≤ UniqueFactorizationMonoid.normalizedFactors χ, s.prod.Monic :=
    fun s hs => by
      simpa using Polynomial.monic_multiset_prod_of_monic s id
        (fun g hg => hmon g (Multiset.mem_of_le hs hg))
  have hroot : ∀ (s : Multiset ℝ[X]) (z : ℂ), aeval z s.prod = 0 → ∃ g ∈ s, aeval z g = 0 := by
    intro s z hz
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hz
    obtain ⟨g, hg, hgz⟩ := hz
    exact ⟨g, hg, hgz⟩
  have hprodF : (UniqueFactorizationMonoid.normalizedFactors χ).prod = χ :=
    Polynomial.eq_of_monic_of_associated (hprodmon _ le_rfl) hχ
      (UniqueFactorizationMonoid.prod_normalizedFactors hχ.ne_zero)
  obtain ⟨Fs, hFsdef⟩ : ∃ Fs, Fs = (UniqueFactorizationMonoid.normalizedFactors χ).filter
      RootsInside := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G, G = (UniqueFactorizationMonoid.normalizedFactors χ).filter
      (fun g => ¬ RootsInside g) := ⟨_, rfl⟩
  obtain ⟨Fc, hFcdef⟩ : ∃ Fc, Fc = G.filter RootsOnCircle := ⟨_, rfl⟩
  obtain ⟨Fu, hFudef⟩ : ∃ Fu, Fu = G.filter (fun g => ¬ RootsOnCircle g) := ⟨_, rfl⟩
  have heq : χ = Fs.prod * Fc.prod * Fu.prod := by
    rw [mul_assoc, hFcdef, hFudef, Multiset.prod_filter_mul_prod_filter_not, hGdef, hFsdef,
      Multiset.prod_filter_mul_prod_filter_not, hprodF]
  have hG : G ≤ UniqueFactorizationMonoid.normalizedFactors χ := by
    rw [hGdef]; exact Multiset.filter_le _ _
  have hFs : Fs ≤ UniqueFactorizationMonoid.normalizedFactors χ := by
    rw [hFsdef]; exact Multiset.filter_le _ _
  have hFc : Fc ≤ UniqueFactorizationMonoid.normalizedFactors χ := by
    rw [hFcdef]; exact (Multiset.filter_le _ _).trans hG
  have hFu : Fu ≤ UniqueFactorizationMonoid.normalizedFactors χ := by
    rw [hFudef]; exact (Multiset.filter_le _ _).trans hG
  -- the roots of the three factors
  have hroots : ∀ z : ℂ, aeval z Fs.prod = 0 → ‖z‖ < 1 := by
    intro z hz
    obtain ⟨g, hg, hgz⟩ := hroot Fs z hz
    rw [hFsdef, Multiset.mem_filter] at hg
    exact hg.2 z hgz
  have hrootc : ∀ z : ℂ, aeval z Fc.prod = 0 → ‖z‖ = 1 := by
    intro z hz
    obtain ⟨g, hg, hgz⟩ := hroot Fc z hz
    rw [hFcdef, Multiset.mem_filter] at hg
    exact hg.2 z hgz
  have hrootu : ∀ z : ℂ, aeval z Fu.prod = 0 → 1 < ‖z‖ := by
    intro z hz
    obtain ⟨g, hg, hgz⟩ := hroot Fu z hz
    rw [hFudef, Multiset.mem_filter] at hg
    obtain ⟨hgG, hnc⟩ := hg
    rw [hGdef, Multiset.mem_filter] at hgG
    obtain ⟨hgF, hni⟩ := hgG
    have hgi := hirr g hgF
    simp only [RootsInside, RootsOnCircle, not_forall, not_lt] at hni hnc
    obtain ⟨w, hw, hw1⟩ := hni
    obtain ⟨w', hw', hw'1⟩ := hnc
    have hz' := (Count.mem_roots_map_iff hgi.ne_zero).mpr hgz
    have e1 :=
      Count.norm_eq_of_irreducible hgi hz' ((Count.mem_roots_map_iff hgi.ne_zero).mpr hw)
    have e2 :=
      Count.norm_eq_of_irreducible hgi hz' ((Count.mem_roots_map_iff hgi.ne_zero).mpr hw')
    have h1 : 1 ≤ ‖z‖ := by rw [e1]; exact hw1
    have h2 : (1 : ℝ) ≠ ‖z‖ := fun h => hw'1 (by rw [← e2]; exact h.symm)
    exact lt_of_le_of_ne h1 h2
  -- `c`: the product of the distinct circle factors
  have hFcirr : ∀ g ∈ Fc, Irreducible g := fun g hg => hirr g (Multiset.mem_of_le hFc hg)
  have hFcmon : ∀ g ∈ Fc, g.Monic := fun g hg => hmon g (Multiset.mem_of_le hFc hg)
  have hcmon : Fc.dedup.prod.Monic := hprodmon _ ((Multiset.dedup_le Fc).trans hFc)
  have hsq : Squarefree Fc.dedup.prod := by
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hcmon.ne_zero,
      UniqueFactorizationMonoid.normalizedFactors_prod_eq _
        (fun g hg => hFcirr g (Multiset.mem_dedup.mp hg))]
    have : Fc.dedup.map normalize = Fc.dedup := by
      conv_rhs => rw [← Multiset.map_id Fc.dedup]
      exact Multiset.map_congr rfl fun g hg =>
        (hFcmon g (Multiset.mem_dedup.mp hg)).normalize_eq_self
    rw [this]
    exact Multiset.nodup_dedup Fc
  have hsep : (Fc.dedup.prod.map (algebraMap ℝ ℂ)).Separable :=
    (PerfectField.separable_iff_squarefree.mpr hsq).map
  have hnd := Polynomial.nodup_roots hsep
  have hcmonC : (Fc.dedup.prod.map (algebraMap ℝ ℂ)).Monic := hcmon.map _
  have hcard : Multiset.card (Fc.dedup.prod.map (algebraMap ℝ ℂ)).roots =
      (Fc.dedup.prod.map (algebraMap ℝ ℂ)).natDegree := by
    rw [natDegree_map]
    exact IsAlgClosed.card_roots_map_eq_natDegree_of_injective _ (algebraMap ℝ ℂ).injective
  have hnodal : Fc.dedup.prod.map (algebraMap ℝ ℂ) =
      Lagrange.nodal (Fc.dedup.prod.map (algebraMap ℝ ℂ)).roots.toFinset id := by
    rw [Lagrange.nodal, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnd]
    exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hcmonC hcard).symm
  have hcdvd : Fc.dedup.prod ∣ Fc.prod := Multiset.prod_dvd_prod_of_le (Multiset.dedup_le Fc)
  have hnormS : ∀ z ∈ (Fc.dedup.prod.map (algebraMap ℝ ℂ)).roots.toFinset, ‖z‖ = 1 := by
    intro z hz
    rw [Multiset.mem_toFinset, Count.mem_roots_map_iff hcmon.ne_zero] at hz
    obtain ⟨r, hr⟩ := hcdvd
    exact hrootc z (by rw [hr, map_mul, hz, zero_mul])
  have hpow : Fc.prod ∣ Fc.dedup.prod ^ Multiset.card Fc := by
    rw [← Multiset.prod_nsmul]
    apply Multiset.prod_dvd_prod_of_le
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_nsmul, Multiset.count_dedup]
    split_ifs with ha
    · rw [mul_one]
      exact Multiset.count_le_card a Fc
    · rw [Multiset.count_eq_zero.mpr ha]
      exact Nat.zero_le _
  exact ⟨DiskSplit.mk (qs := Fs.prod) (qc := Fc.prod) (qu := Fu.prod) (c := Fc.dedup.prod)
    (S := (Fc.dedup.prod.map (algebraMap ℝ ℂ)).roots.toFinset) (N := Multiset.card Fc)
    (monic_qs := hprodmon _ hFs) (monic_qc := hprodmon _ hFc) (monic_qu := hprodmon _ hFu)
    (monic_c := hcmon) (eq_mul := heq) (root_qs := hroots) (root_qc := hrootc)
    (root_qu := hrootu) (squarefree_c := hsq) (map_c := hnodal) (norm_S := hnormS)
    (c_dvd := hcdvd) (dvd_c_pow := hpow)⟩

section Real

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- `f` is power-bounded on `H`: one constant `C` with `‖fⁿ v‖ ≤ C ‖v‖` for all `n` and all
`v ∈ H`. -/
def PowerBoundedOn (f : Module.End ℝ V) (H : Submodule ℝ V) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∀ v ∈ H, ‖(f ^ n) v‖ ≤ C * ‖v‖

/-- In finite dimension, bounded orbits give a uniform power bound (Banach–Steinhaus). -/
theorem powerBoundedOn_of_bounded (f : Module.End ℝ V) (H : Submodule ℝ V)
    (h : ∀ v ∈ H, ∃ B : ℝ, ∀ n : ℕ, ‖(f ^ n) v‖ ≤ B) : PowerBoundedOn f H := by
  have : CompleteSpace H := FiniteDimensional.complete ℝ H
  let g : ℕ → H →L[ℝ] V := fun n => LinearMap.toContinuousLinearMap ((f ^ n).comp H.subtype)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := g) (fun x => by
    obtain ⟨B, hB⟩ := h x x.2
    exact ⟨B, fun n => hB n⟩)
  refine ⟨C, fun n v hv => ?_⟩
  calc ‖(f ^ n) v‖ = ‖g n ⟨v, hv⟩‖ := rfl
    _ ≤ ‖g n‖ * ‖(⟨v, hv⟩ : H)‖ := (g n).le_opNorm _
    _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)

/-- **Power-bounded ⇒ semisimple on the unit circle.** If `f` is power-bounded on an invariant
subspace `U` killed by `q(f)`, where `q ∣ c^N` and `c` has distinct complex roots `S` of modulus
one, then `U ⊆ ker c(f)`. -/
theorem aeval_eq_zero_of_powerBoundedOn (f : Module.End ℝ V) {U : Submodule ℝ V}
    (hU : ∀ v ∈ U, f v ∈ U) (hpb : PowerBoundedOn f U) {c q : ℝ[X]} {S : Finset ℂ}
    (hS : ∀ z ∈ S, ‖z‖ = 1) (hc : c.map (algebraMap ℝ ℂ) = Lagrange.nodal S id) {N : ℕ}
    (hq : q ∣ c ^ N) (hqU : ∀ v ∈ U, aeval f q v = 0) : ∀ v ∈ U, aeval f c v = 0 := by
  classical
  have hgq : aeval (f.restrict hU) q = 0 := by
    ext x
    rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, KernelSplit.aeval_restrict_apply]
    exact hqU x x.2
  have hgcN : aeval (f.restrict hU) (c ^ N) = 0 := by
    obtain ⟨r, hr⟩ := hq
    rw [hr, map_mul, hgq, zero_mul]
  obtain ⟨C, hC⟩ := hpb
  have hC' : ∀ (n : ℕ) (x : U), ‖((f.restrict hU) ^ n) x‖ ≤ C * ‖x‖ := by
    intro n x
    have := hC n x x.2
    rw [← PowerBounded.coe_restrict_pow_apply f hU n x] at this
    exact this
  obtain ⟨Kb, hKb⟩ := PowerBounded.entries_bounded_of_powerBounded _ hC'
  set b := Module.finBasis ℝ U
  set M := LinearMap.toMatrixAlgEquiv b (f.restrict hU) with hM
  have hMt : LinearMap.toMatrix b b (f.restrict hU) = M := by
    ext i j
    rw [hM, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  rw [hMt] at hKb
  set MC : Matrix (Fin (finrank ℝ U)) (Fin (finrank ℝ U)) ℂ := M.map (algebraMap ℝ ℂ) with hMC
  have hMCK : ∀ (n : ℕ) (i j : Fin (finrank ℝ U)), ‖(MC ^ n) i j‖ ≤ Kb := by
    intro n i j
    have hpow : (MC ^ n) i j = ((M ^ n) i j : ℂ) := by
      have := congrArg (fun B : Matrix _ _ ℂ => B i j) (map_pow (algebraMap ℝ ℂ).mapMatrix M n)
      simpa [RingHom.mapMatrix_apply, MC] using this.symm
    rw [hpow, Complex.norm_real, Real.norm_eq_abs]
    exact hKb n i j
  have hMalg : ∀ p : ℝ[X],
      aeval M p = LinearMap.toMatrixAlgEquiv b (aeval (f.restrict hU) p) := by
    intro p
    rw [hM]
    exact aeval_algHom_apply ((LinearMap.toMatrixAlgEquiv b).toAlgHom) (f.restrict hU) p
  have hMCalg : ∀ p : ℝ[X], aeval MC (p.map (algebraMap ℝ ℂ)) =
      (algebraMap ℝ ℂ).mapMatrix (aeval M p) := by
    intro p
    rw [aeval_map_algebraMap]
    have h2 : MC = (Algebra.ofId ℝ ℂ).mapMatrix M := rfl
    rw [h2, aeval_algHom_apply]
    rfl
  have hN : aeval MC (Lagrange.nodal S id ^ N) = 0 := by
    rw [← hc, ← Polynomial.map_pow, hMCalg, hMalg, hgcN, map_zero, map_zero]
  have h0 := aeval_nodal_eq_zero_of_pow MC hMCK S hS hN
  rw [← hc, hMCalg, hMalg] at h0
  have hgc : aeval (f.restrict hU) c = 0 := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_zero]
    ext i j
    have := congrFun (congrFun h0 i) j
    simpa [RingHom.mapMatrix_apply] using this
  intro v hv
  have := congrArg (fun T : Module.End ℝ U => ((T ⟨v, hv⟩ : U) : V)) hgc
  simpa [KernelSplit.aeval_restrict_apply] using this

/-- `dim ker q_s(f) = dim ker q_s(f)² = deg q_s`. -/
theorem finrank_ker_qs (f : Module.End ℝ V) (D : DiskSplit f.charpoly) :
    finrank ℝ (LinearMap.ker (aeval f D.qs)) = D.qs.natDegree ∧
      finrank ℝ (LinearMap.ker (aeval f (D.qs ^ 2))) = D.qs.natDegree := by
  have hχ : f.charpoly = D.qs * (D.qc * D.qu) := D.eq_mul.trans (mul_assoc _ _ _)
  obtain ⟨hcompl, hdim⟩ := KernelSplit.finrank_ker_aeval_of_coprime f D.monic_qs
    (D.monic_qc.mul D.monic_qu) hχ D.coprime_s_cu
  refine ⟨hdim, ?_⟩
  have hle : LinearMap.ker (aeval f D.qs) ≤ LinearMap.ker (aeval f (D.qs ^ 2)) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [sq, aeval_mul_apply, hv, map_zero]
  have hdis := Polynomial.disjoint_ker_aeval_of_isCoprime f (D.coprime_s_cu.pow_left (m := 2))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval f (D.qs ^ 2)))
    (LinearMap.ker (aeval f (D.qc * D.qu)))
  rw [hdis.eq_bot, finrank_bot, add_zero] at h2
  have h3 := Submodule.finrank_le
    (LinearMap.ker (aeval f (D.qs ^ 2)) ⊔ LinearMap.ker (aeval f (D.qc * D.qu)))
  have h4 := Submodule.finrank_add_eq_of_isCompl hcompl
  omega

/-- `dim ker (q_s c)(f) − dim (ker (q_s c)(f) ∩ im (q_s c)(f)) = deg q_s + socle count at `c``. -/
theorem finrank_ker_qs_c (f : Module.End ℝ V) (D : DiskSplit f.charpoly) :
    finrank ℝ (LinearMap.ker (aeval f (D.qs * D.c))) -
        finrank ℝ ↥(LinearMap.ker (aeval f (D.qs * D.c)) ⊓
          LinearMap.range (aeval f (D.qs * D.c))) =
      D.qs.natDegree + socleCount f D.c := by
  obtain ⟨hs1, hs2⟩ := finrank_ker_qs f D
  have e1 := finrank_ker_mul_of_coprime f D.coprime_s_c
  have e2 : finrank ℝ (LinearMap.ker (aeval f ((D.qs * D.c) ^ 2))) =
      finrank ℝ (LinearMap.ker (aeval f (D.qs ^ 2))) +
        finrank ℝ (LinearMap.ker (aeval f (D.c ^ 2))) := by
    rw [mul_pow]
    exact finrank_ker_mul_of_coprime f (D.coprime_s_c.pow (m := 2) (n := 2))
  have e3 := finrank_ker_sq f (D.qs * D.c)
  have e4 := finrank_ker_sq f D.c
  have e5 := Submodule.finrank_mono (inf_le_left :
    LinearMap.ker (aeval f D.c) ⊓ LinearMap.range (aeval f D.c) ≤ LinearMap.ker (aeval f D.c))
  rw [socleCount]
  omega

/-- **Largest power-bounded summand, upper bound.** An `f`-invariant subspace with an `f`-invariant
complement, on which `f` is power-bounded, has dimension at most `deg q_s + socle count at c`. -/
theorem finrank_le_of_powerBoundedOn (f : Module.End ℝ V) (D : DiskSplit f.charpoly)
    {H H' : Submodule ℝ V} (hc : IsCompl H H') (hH : ∀ v ∈ H, f v ∈ H)
    (hH' : ∀ v ∈ H', f v ∈ H') (hpb : PowerBoundedOn f H) :
    finrank ℝ H ≤ D.qs.natDegree + socleCount f D.c := by
  classical
  -- every root of `χ_{f|H}` lies in the closed disk
  have hdisk : ∀ z : ℂ, aeval z (f.restrict hH).charpoly = 0 → ‖z‖ ≤ 1 := by
    obtain ⟨C, hC⟩ := hpb
    have hC' : ∀ (n : ℕ) (x : H), ‖((f.restrict hH) ^ n) x‖ ≤ C * ‖x‖ := by
      intro n x
      have := hC n x x.2
      rw [← PowerBounded.coe_restrict_pow_apply f hH n x] at this
      exact this
    obtain ⟨Kb, hKb⟩ := PowerBounded.entries_bounded_of_powerBounded _ hC'
    have hd := PowerBounded.norm_le_one_of_pow_bounded _ Kb hKb
    rw [LinearMap.charpoly_toMatrix] at hd
    intro z hz
    exact hd z (Hyperbolic.mem_roots_of_aeval_eq_zero (LinearMap.charpoly_monic _).ne_zero hz)
  -- so `χ_{f|H}` divides `q_s q_c`, which kills `H`
  have hsplitχ := PowerBounded.charpoly_eq_mul_of_isCompl f H H' hc hH hH'
  have hcopu : IsCoprime (f.restrict hH).charpoly D.qu := isCoprime_of_roots fun z h1 h2 => by
    have := hdisk z h1
    have := D.root_qu z h2
    linarith
  have hdvd : (f.restrict hH).charpoly ∣ D.qs * D.qc := by
    have : (f.restrict hH).charpoly ∣ D.qs * D.qc * D.qu := by
      rw [← D.eq_mul, hsplitχ]
      exact dvd_mul_right _ _
    exact hcopu.dvd_of_dvd_mul_right this
  have hkill : ∀ v ∈ H, aeval f (D.qs * D.qc) v = 0 := by
    intro v hv
    have h0 : aeval (f.restrict hH) (D.qs * D.qc) = 0 := by
      obtain ⟨r, hr⟩ := hdvd
      rw [hr, map_mul, LinearMap.aeval_self_charpoly, zero_mul]
    have := congrArg (fun T : Module.End ℝ H => ((T ⟨v, hv⟩ : H) : V)) h0
    simpa [KernelSplit.aeval_restrict_apply] using this
  -- on the unit-circle part of `H`, `c(f) = 0`
  have hU : ∀ v ∈ H ⊓ LinearMap.ker (aeval f D.qc), f v ∈ H ⊓ LinearMap.ker (aeval f D.qc) :=
    fun v hv => ⟨hH v hv.1, mapsTo_ker f D.qc v hv.2⟩
  have hpbU : PowerBoundedOn f (H ⊓ LinearMap.ker (aeval f D.qc)) := by
    obtain ⟨C, hC⟩ := hpb
    exact ⟨C, fun n v hv => hC n v hv.1⟩
  have hcU := aeval_eq_zero_of_powerBoundedOn f hU hpbU D.norm_S D.map_c D.dvd_c_pow
    (fun v hv => hv.2)
  -- hence `(q_s c)(f)` kills `H`
  obtain ⟨a, b, hab⟩ := D.coprime_s_qc
  have hkill2 : ∀ v ∈ H, aeval f (D.qs * D.c) v = 0 := by
    intro v hv
    have hxy : v = aeval f (a * D.qs) v + aeval f (b * D.qc) v := by
      have : aeval f (a * D.qs + b * D.qc) v = v := by
        rw [hab, map_one, Module.End.one_apply]
      rw [map_add, LinearMap.add_apply] at this
      exact this.symm
    have hx : aeval f (a * D.qs) v ∈ H ⊓ LinearMap.ker (aeval f D.qc) := by
      refine ⟨aeval_mem_of_invariant f hH _ v hv, LinearMap.mem_ker.mpr ?_⟩
      rw [← aeval_mul_apply,
        show D.qc * (a * D.qs) = a * (D.qs * D.qc) by ring, aeval_mul_apply, hkill v hv,
        map_zero]
    have hy : aeval f D.qs (aeval f (b * D.qc) v) = 0 := by
      rw [← aeval_mul_apply, show D.qs * (b * D.qc) = b * (D.qs * D.qc) by ring,
        aeval_mul_apply, hkill v hv, map_zero]
    have h1 : aeval f (D.qs * D.c) (aeval f (a * D.qs) v) = 0 := by
      rw [aeval_mul_apply, hcU _ hx, map_zero]
    have h2 : aeval f (D.qs * D.c) (aeval f (b * D.qc) v) = 0 := by
      rw [mul_comm D.qs D.c, aeval_mul_apply, hy, map_zero]
    rw [hxy, map_add, h1, h2, add_zero]
  -- the socle bound for `p = q_s c`
  have hsoc := (socle_bound f (D.qs * D.c) hc hH' hkill2).2
  have hval := finrank_ker_qs_c f D
  omega

/-- **Largest power-bounded summand, attainment.** `H = ker q_s(f) ⊕ U`, with `U` an `f`-invariant
complement of `ker c(f) ∩ im c(f)` in `ker c(f)`, is a power-bounded invariant summand of dimension
`deg q_s + socle count at c`. Its invariant complement is `N ∩ ker (q_c q_u)(f)`, where `N ⊇ im
c(f)` is the preimage of an invariant complement of the image of `U` in `V / im c(f)`; both
complements exist because `c` is squarefree and kills `ker c(f)` and `V / im c(f)`. -/
theorem exists_powerBounded_summand (f : Module.End ℝ V) (D : DiskSplit f.charpoly) :
    ∃ H E : Submodule ℝ V, IsCompl H E ∧ (∀ v ∈ H, f v ∈ H) ∧ (∀ v ∈ E, f v ∈ E) ∧
      PowerBoundedOn f H ∧ finrank ℝ H = D.qs.natDegree + socleCount f D.c := by
  classical
  have hKcinv : LinearMap.ker (aeval f D.c) ∈ f.invtSubmodule :=
    (Module.End.mem_invtSubmodule f).mpr fun v hv => mapsTo_ker f D.c v hv
  have hRinv : LinearMap.range (aeval f D.c) ∈ f.invtSubmodule :=
    (Module.End.mem_invtSubmodule f).mpr fun v hv => mapsTo_range f D.c v hv
  have hTinv : LinearMap.ker (aeval f D.c) ⊓ LinearMap.range (aeval f D.c) ∈ f.invtSubmodule :=
    (Module.End.mem_invtSubmodule f).mpr fun v hv =>
      ⟨mapsTo_ker f D.c v hv.1, mapsTo_range f D.c v hv.2⟩
  -- an invariant complement `U` of `ker c(f) ∩ im c(f)` inside `ker c(f)`
  have hss : Module.End.IsSemisimple (f.restrict (mapsTo_ker f D.c)) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero D.squarefree_c
      (Hyperbolic.aeval_restrict_ker_eq_zero f D.c)
  obtain ⟨U, hUle, hUinv, hTU, hTUsup⟩ :=
    (Module.End.isSemisimple_restrict_iff (LinearMap.ker (aeval f D.c)) hKcinv).mp hss _ hTinv
      inf_le_left
  have hU : ∀ v ∈ U, f v ∈ U := fun v hv => (Module.End.mem_invtSubmodule f).mp hUinv hv
  have hdimU : finrank ℝ U = socleCount f D.c := by
    have key := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (aeval f D.c) ⊓ LinearMap.range (aeval f D.c)) U
    rw [hTUsup, hTU.eq_bot, finrank_bot, add_zero] at key
    rw [socleCount]
    omega
  have hUR : Disjoint U (LinearMap.range (aeval f D.c)) := by
    rw [Submodule.disjoint_def]
    intro v hvU hvR
    exact (Submodule.disjoint_def.1 hTU) v ⟨hUle hvU, hvR⟩ hvU
  -- the quotient by `R = im c(f)`, on which `c` vanishes
  set R := LinearMap.range (aeval f D.c) with hRdef
  have hRle : R ≤ R.comap f := (Module.End.mem_invtSubmodule f).mp hRinv
  have hq_aeval : ∀ (p : ℝ[X]) (v : V), aeval (R.mapQ R f hRle) p (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (aeval f p v) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      intro v
      simp [Module.algebraMap_end_apply]
    | add p q hp hq =>
      intro v
      simp only [map_add, LinearMap.add_apply, hp, hq, Submodule.Quotient.mk_add]
    | monomial n a ih =>
      intro v
      have e1 : (C a * X ^ (n + 1) : ℝ[X]) = C a * X ^ n * X := by ring
      rw [e1, aeval_mul_apply (R.mapQ R f hRle) (C a * X ^ n) X, aeval_X, Submodule.mapQ_apply,
        ih, aeval_mul_apply f (C a * X ^ n) X, aeval_X]
  have hcq : aeval (R.mapQ R f hRle) D.c = 0 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective R x
    rw [hq_aeval, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨v, rfl⟩
  have hssq : Module.End.IsSemisimple (R.mapQ R f hRle) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero D.squarefree_c hcq
  have hUbinv : U.map R.mkQ ∈ Module.End.invtSubmodule (R.mapQ R f hRle) := by
    refine (Module.End.mem_invtSubmodule _).mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨f u, hU u hu, rfl⟩
  obtain ⟨Nb, hNbinv, hcompl⟩ := Module.End.isSemisimple_iff.mp hssq _ hUbinv
  set N := Nb.comap R.mkQ with hNdef
  have hN : ∀ v ∈ N, f v ∈ N := by
    intro v hv
    have h1 : R.mapQ R f hRle (R.mkQ v) ∈ Nb := (Module.End.mem_invtSubmodule _).mp hNbinv hv
    exact h1
  have hRN : R ≤ N := by
    intro r hr
    have h0 : R.mkQ r = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hr
    show R.mkQ r ∈ Nb
    rw [h0]
    exact Nb.zero_mem
  have hUN : IsCompl U N := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hvU hvN
      have h1 : R.mkQ v ∈ U.map R.mkQ ⊓ Nb := ⟨⟨v, hvU, rfl⟩, hvN⟩
      rw [hcompl.disjoint.eq_bot, Submodule.mem_bot, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at h1
      exact (Submodule.disjoint_def.1 hUR) v hvU h1
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have h1 : R.mkQ v ∈ U.map R.mkQ ⊔ Nb := by
        rw [hcompl.codisjoint.eq_top]
        exact Submodule.mem_top
      obtain ⟨y, ⟨u, hu, rfl⟩, n, hn, hyn⟩ := Submodule.mem_sup.mp h1
      rw [Submodule.mem_sup]
      refine ⟨u, hu, v - u, ?_, by abel⟩
      show R.mkQ (v - u) ∈ Nb
      rw [map_sub, ← hyn, add_sub_cancel_left]
      exact hn
  -- `ker q_s(f) ⊆ im c(f) ⊆ N`
  have hsR : LinearMap.ker (aeval f D.qs) ≤ R := by
    intro x hx
    obtain ⟨a, b, hab⟩ := D.coprime_s_c
    refine ⟨aeval f b x, ?_⟩
    have h1 : aeval f (a * D.qs + b * D.c) x = x := by
      rw [hab, map_one, Module.End.one_apply]
    rw [map_add, LinearMap.add_apply, aeval_mul_apply, LinearMap.mem_ker.mp hx, map_zero,
      zero_add, aeval_mul_apply] at h1
    rw [aeval_comm_apply]
    exact h1
  have hχ0 : ∀ w, aeval f (D.qs * (D.qc * D.qu)) w = 0 := by
    intro w
    rw [← mul_assoc, ← D.eq_mul, LinearMap.aeval_self_charpoly, LinearMap.zero_apply]
  refine ⟨LinearMap.ker (aeval f D.qs) ⊔ U, N ⊓ LinearMap.ker (aeval f (D.qc * D.qu)),
    ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [Submodule.disjoint_def]
      intro x hx hxE
      obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hx
      have huN : u ∈ N := by
        have : (s + u) - s ∈ N := N.sub_mem hxE.1 (hRN (hsR hs))
        rwa [add_sub_cancel_left] at this
      have hu0 : u = 0 := (Submodule.disjoint_def.1 hUN.disjoint) u hu huN
      subst hu0
      rw [add_zero] at hxE ⊢
      exact (Submodule.disjoint_def.1
        (Polynomial.disjoint_ker_aeval_of_isCoprime f D.coprime_s_cu)) s hs hxE.2
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have hv : v ∈ U ⊔ N := by
        rw [hUN.codisjoint.eq_top]
        exact Submodule.mem_top
      obtain ⟨u, hu, n, hn, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨a, b, hab⟩ := D.coprime_s_cu
      have hsplit : aeval f (b * (D.qc * D.qu)) n + aeval f (a * D.qs) n = n := by
        have h1 : aeval f (a * D.qs + b * (D.qc * D.qu)) n = n := by
          rw [hab, map_one, Module.End.one_apply]
        rw [map_add, LinearMap.add_apply] at h1
        rw [add_comm]
        exact h1
      have hs : aeval f (b * (D.qc * D.qu)) n ∈ LinearMap.ker (aeval f D.qs) := by
        rw [LinearMap.mem_ker, ← aeval_mul_apply,
          show D.qs * (b * (D.qc * D.qu)) = b * (D.qs * (D.qc * D.qu)) by ring, aeval_mul_apply,
          hχ0, map_zero]
      have he : aeval f (a * D.qs) n ∈ LinearMap.ker (aeval f (D.qc * D.qu)) := by
        rw [LinearMap.mem_ker, ← aeval_mul_apply,
          show D.qc * D.qu * (a * D.qs) = a * (D.qs * (D.qc * D.qu)) by ring, aeval_mul_apply,
          hχ0, map_zero]
      rw [Submodule.mem_sup]
      refine ⟨aeval f (b * (D.qc * D.qu)) n + u, Submodule.mem_sup.mpr ⟨_, hs, u, hu, rfl⟩,
        aeval f (a * D.qs) n, ⟨aeval_mem_of_invariant f hN _ n hn, he⟩, ?_⟩
      calc aeval f (b * (D.qc * D.qu)) n + u + aeval f (a * D.qs) n
          = u + (aeval f (b * (D.qc * D.qu)) n + aeval f (a * D.qs) n) := by abel
        _ = u + n := by rw [hsplit]
  · intro v hv
    obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (mapsTo_ker f D.qs s hs) (hU u hu)
  · exact fun v hv => ⟨hN v hv.1, mapsTo_ker f _ v hv.2⟩
  · obtain ⟨C₂, hC₂⟩ := KernelSplit.powerBounded_of_nodal f D.monic_c D.S
      (fun z hz => (D.norm_S z hz).le) D.map_c
    have hmk := Hyperbolic.mapsTo_ker_aeval f D.qs
    have hfs : ∀ z : ℂ, aeval z (f.restrict hmk).charpoly = 0 → ‖z‖ < 1 := fun z hz =>
      D.root_qs z (Hyperbolic.aeval_eq_zero_of_charpoly_root _
        (Hyperbolic.aeval_restrict_ker_eq_zero f D.qs) z hz)
    obtain ⟨cs, hcs, -, hcsb⟩ := Hyperbolic.exists_bound_tendsto_zero (f.restrict hmk) hfs
    obtain ⟨Ks, -, hKs⟩ := Hyperbolic.tendsto_bound hcs
    apply powerBoundedOn_of_bounded
    intro v hv
    obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨Ks * ‖s‖ + C₂ * ‖u‖, fun n => ?_⟩
    have h1 : ‖(f ^ n) s‖ ≤ Ks * ‖s‖ := by
      have e : ((((f.restrict hmk) ^ n) ⟨s, hs⟩ : LinearMap.ker (aeval f D.qs)) : V) =
          (f ^ n) s := PowerBounded.coe_restrict_pow_apply f hmk n ⟨s, hs⟩
      calc ‖(f ^ n) s‖ = ‖((f.restrict hmk) ^ n) ⟨s, hs⟩‖ := by rw [← e]; rfl
        _ ≤ cs n * ‖(⟨s, hs⟩ : LinearMap.ker (aeval f D.qs))‖ := hcsb n _
        _ ≤ Ks * ‖s‖ := mul_le_mul_of_nonneg_right (hKs n) (norm_nonneg _)
    have h2 : ‖(f ^ n) u‖ ≤ C₂ * ‖u‖ := hC₂ n u (hUle hu)
    calc ‖(f ^ n) (s + u)‖ = ‖(f ^ n) s + (f ^ n) u‖ := by rw [map_add]
      _ ≤ ‖(f ^ n) s‖ + ‖(f ^ n) u‖ := norm_add_le _ _
      _ ≤ Ks * ‖s‖ + C₂ * ‖u‖ := add_le_add h1 h2
  · have hdis : Disjoint (LinearMap.ker (aeval f D.qs)) U :=
      (Polynomial.disjoint_ker_aeval_of_isCoprime f D.coprime_s_c).mono_right hUle
    have key := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval f D.qs)) U
    rw [hdis.eq_bot, finrank_bot, add_zero, (finrank_ker_qs f D).1, hdimU] at key
    exact key

/-- **The largest power-bounded summand.** The largest dimension of an `f`-invariant subspace that
has an `f`-invariant complement and on which `f` is power-bounded is `deg q_s + socle count at c`:
the dimension of the stable space plus the number of Jordan blocks of size one at eigenvalues of
modulus one. -/
theorem isGreatest_powerBounded_summand (f : Module.End ℝ V) (D : DiskSplit f.charpoly) :
    IsGreatest {d : ℕ | ∃ H E : Submodule ℝ V, IsCompl H E ∧ (∀ v ∈ H, f v ∈ H) ∧
      (∀ v ∈ E, f v ∈ E) ∧ PowerBoundedOn f H ∧ finrank ℝ H = d}
      (D.qs.natDegree + socleCount f D.c) := by
  refine ⟨exists_powerBounded_summand f D, ?_⟩
  rintro d ⟨H, E, hc, hH, hE, hpb, rfl⟩
  exact finrank_le_of_powerBoundedOn f D hc hH hE hpb

/-- **The largest power-bounded summand**, for every endomorphism: a `DiskSplit` of `χ_f` exists,
and for it the largest power-bounded invariant summand has dimension `deg q_s + socle count at c`,
where `deg q_s` is the number of eigenvalues of modulus `< 1` with multiplicity. -/
theorem largest_powerBounded_summand (f : Module.End ℝ V) :
    ∃ D : DiskSplit f.charpoly,
      D.qs.natDegree = Multiset.card
        ((f.charpoly.map (algebraMap ℝ ℂ)).roots.filter (fun z => ‖z‖ < 1)) ∧
      IsGreatest {d : ℕ | ∃ H E : Submodule ℝ V, IsCompl H E ∧ (∀ v ∈ H, f v ∈ H) ∧
        (∀ v ∈ E, f v ∈ E) ∧ PowerBoundedOn f H ∧ finrank ℝ H = d}
        (D.qs.natDegree + socleCount f D.c) := by
  obtain ⟨D⟩ := exists_diskSplit f.charpoly (LinearMap.charpoly_monic f)
  exact ⟨D, D.natDegree_qs, isGreatest_powerBounded_summand f D⟩

end Real

section Scheme

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For an admissible `A`-invariant scheme, the internal space is a power-bounded invariant
summand, so `dim H ≤ deg q_s + socle count at c` for `χ_A = q_s q_c q_u`. -/
theorem finrank_H_le_of_admissible {A : Matrix ι ι ℤ} (S : InvariantCPS A) (hS : S.Admissible)
    (D : DiskSplit (act A).charpoly) :
    finrank ℝ S.H ≤ D.qs.natDegree + socleCount (act A) D.c :=
  finrank_le_of_powerBoundedOn (act A) D S.isCompl.symm S.mapsTo_H S.mapsTo_E
    ((admissible_iff_powerBounded S).mp hS)

end Scheme

/-! ### The Jordan data of an integer matrix at a rational irreducible factor -/

section JordanQ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `A` acting on `ℚ^ι`. -/
def actQ (A : Matrix ι ι ℤ) : Module.End ℚ (ι → ℚ) := Matrix.toLin' (A.map (Int.cast : ℤ → ℚ))

/-- `m_p`: the multiplicity of `p` in `χ_A` over `ℚ`. -/
def mult (A : Matrix ι ι ℤ) (p : ℚ[X]) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).count p

/-- `dim_ℚ ker p(A)^k`. -/
def kerRank (A : Matrix ι ι ℤ) (p : ℚ[X]) (k : ℕ) : ℕ :=
  finrank ℚ (LinearMap.ker (aeval (actQ A) (p ^ k)))

/-- `r₁(p) = (2 dim_ℚ ker p(A) − dim_ℚ ker p(A)²) / deg p`: the number of Jordan blocks of size
one at each root of `p` (`natDegree_mul_singleBlocks`: the division is exact). -/
def singleBlocks (A : Matrix ι ι ℤ) (p : ℚ[X]) : ℕ :=
  (2 * kerRank A p 1 - kerRank A p 2) / p.natDegree

/-- `u_p`: the number of complex roots of `p` of modulus `> 1`, with multiplicity. -/
def expandingRoots (p : ℚ[X]) : ℕ :=
  Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖))

/-- `c_p`: the number of complex roots of `p` of modulus `1`, with multiplicity. -/
def circleRoots (p : ℚ[X]) : ℕ :=
  Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ‖z‖ = 1))

/-- `s_p`: the number of complex roots of `p` of modulus `< 1`, with multiplicity. -/
def insideRoots (p : ℚ[X]) : ℕ :=
  Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ‖z‖ < 1))

theorem charpoly_actQ (A : Matrix ι ι ℤ) : (actQ A).charpoly = charpolyQ A := by
  rw [actQ, Matrix.charpoly_toLin', charpolyQ]
  exact Matrix.charpoly_map A (Int.castRingHom ℚ)

/-- `s_p + c_p + u_p = deg p`. -/
theorem insideRoots_add_circleRoots_add_expandingRoots (p : ℚ[X]) :
    insideRoots p + circleRoots p + expandingRoots p = p.natDegree := by
  classical
  have h1 : Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ‖z‖ < 1)) +
      Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ¬ ‖z‖ < 1)) =
      Multiset.card (p.map (algebraMap ℚ ℂ)).roots := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  have h2 : Multiset.card (((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ¬ ‖z‖ < 1)).filter
      (fun z => ‖z‖ = 1)) + Multiset.card (((p.map (algebraMap ℚ ℂ)).roots.filter
        (fun z => ¬ ‖z‖ < 1)).filter (fun z => ¬ ‖z‖ = 1)) =
      Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ¬ ‖z‖ < 1)) := by
    rw [← Multiset.card_add, Multiset.filter_add_not]
  have e1 : ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ¬ ‖z‖ < 1)).filter
      (fun z => ‖z‖ = 1) = (p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ‖z‖ = 1) := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun z _ =>
      ⟨fun h => h.1, fun h => ⟨h, by rw [h]; exact lt_irrefl 1⟩⟩
  have e2 : ((p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ¬ ‖z‖ < 1)).filter
      (fun z => ¬ ‖z‖ = 1) = (p.map (algebraMap ℚ ℂ)).roots.filter (fun z => 1 < ‖z‖) := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun z _ => ⟨fun h => lt_of_le_of_ne (not_lt.mp h.2) (Ne.symm h.1),
      fun h => ⟨fun h' => absurd h' (ne_of_gt h), not_lt.mpr h.le⟩⟩
  rw [e1, e2] at h2
  rw [insideRoots, circleRoots, expandingRoots, add_assoc, h2, h1,
    IsAlgClosed.card_roots_map_eq_natDegree_of_injective _ (algebraMap ℚ ℂ).injective]

/-- `dim ker p(A)² = dim ker p(A) + dim (ker p(A) ∩ im p(A))` over `ℚ`. -/
theorem kerRank_two (A : Matrix ι ι ℤ) (p : ℚ[X]) :
    kerRank A p 2 = kerRank A p 1 + finrank ℚ ↥(LinearMap.ker (aeval (actQ A) p) ⊓
      LinearMap.range (aeval (actQ A) p)) := by
  rw [kerRank, kerRank, pow_one, finrank_ker_sq]

/-- **The count of Jordan blocks of size one.** For `p` monic irreducible over `ℚ`,
`deg p · r₁(p) = 2 dim ker p(A) − dim ker p(A)² = dim ker p(A) − dim (ker p(A) ∩ im p(A))`:
`deg p` divides both `dim ker p(A)` and `dim (ker p(A) ∩ im p(A))`. -/
theorem natDegree_mul_singleBlocks (A : Matrix ι ι ℤ) {p : ℚ[X]} (hp : Irreducible p)
    (hpm : p.Monic) :
    p.natDegree * singleBlocks A p = 2 * kerRank A p 1 - kerRank A p 2 ∧
      2 * kerRank A p 1 - kerRank A p 2 = kerRank A p 1 - finrank ℚ ↥(LinearMap.ker
        (aeval (actQ A) p) ⊓ LinearMap.range (aeval (actQ A) p)) := by
  have h1 : p.natDegree ∣ kerRank A p 1 := by
    rw [kerRank, pow_one]
    exact natDegree_dvd_finrank_of_le_ker (actQ A) hp hpm (mapsTo_ker (actQ A) p)
      (fun v hv => hv)
  have h2 : p.natDegree ∣ finrank ℚ ↥(LinearMap.ker (aeval (actQ A) p) ⊓
      LinearMap.range (aeval (actQ A) p)) :=
    natDegree_dvd_finrank_of_le_ker (actQ A) hp hpm
      (fun v hv => ⟨mapsTo_ker (actQ A) p v hv.1, mapsTo_range (actQ A) p v hv.2⟩)
      (fun v hv => hv.1)
  have hle := Submodule.finrank_mono (inf_le_left : LinearMap.ker (aeval (actQ A) p) ⊓
      LinearMap.range (aeval (actQ A) p) ≤ LinearMap.ker (aeval (actQ A) p))
  have hk1 : kerRank A p 1 = finrank ℚ (LinearMap.ker (aeval (actQ A) p)) := by
    rw [kerRank, pow_one]
  have e : 2 * kerRank A p 1 - kerRank A p 2 = kerRank A p 1 - finrank ℚ ↥(LinearMap.ker
      (aeval (actQ A) p) ⊓ LinearMap.range (aeval (actQ A) p)) := by
    rw [kerRank_two]
    omega
  refine ⟨?_, e⟩
  rw [singleBlocks, e]
  exact Nat.mul_div_cancel' (Nat.dvd_sub h1 h2)

/-- For a factor `p` of `χ_A` over `ℚ`: `χ_A = p^{m_p} s` with `s` monic and coprime to `p`. -/
theorem charpolyQ_eq_pow_mul (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) :
    ∃ s : ℚ[X], s.Monic ∧ charpolyQ A = p ^ mult A p * s ∧ IsCoprime (p ^ mult A p) s := by
  classical
  set F := UniqueFactorizationMonoid.normalizedFactors (charpolyQ A) with hF
  have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hpm : p.Monic := Count.monic_of_mem A hp
  refine ⟨(F.filter (fun q => ¬ q = p)).prod, ?_, ?_, ?_⟩
  · simpa using Polynomial.monic_multiset_prod_of_monic _ id (fun q hq =>
      Count.monic_of_mem A (Multiset.mem_of_mem_filter hq))
  · rw [mult, ← hF, ← Multiset.prod_replicate, ← Multiset.filter_eq' F p,
      Multiset.prod_filter_mul_prod_filter_not, hF, Count.prod_normalizedFactors_eq]
  · refine IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd hpi).mpr fun hdvd => ?_)
    obtain ⟨q, hq, hpq⟩ := hpi.prime.exists_mem_multiset_dvd hdvd
    have hqF := Multiset.mem_filter.mp hq
    have hqi := UniqueFactorizationMonoid.irreducible_of_normalized_factor q hqF.1
    exact hqF.2 (Polynomial.eq_of_monic_of_associated (Count.monic_of_mem A hqF.1) hpm
      (hpi.associated_of_dvd hqi hpq).symm)

/-- `dim_ℚ ker p(A)^{m_p} = m_p · deg p`: the `p`-primary component of `ℚ^ι`. -/
theorem kerRank_mult (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) :
    kerRank A p (mult A p) = mult A p * p.natDegree := by
  obtain ⟨s, hs, hχ, hcop⟩ := charpolyQ_eq_pow_mul A hp
  rw [kerRank, finrank_ker_aeval_of_coprime (actQ A) ((Count.monic_of_mem A hp).pow _) hs
    (by rw [charpoly_actQ, hχ]) hcop, natDegree_pow]

theorem one_le_mult (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) : 1 ≤ mult A p :=
  Multiset.count_pos.mpr hp

theorem ker_le_ker_pow (A : Matrix ι ι ℤ) (p : ℚ[X]) {k : ℕ} (hk : 1 ≤ k) :
    LinearMap.ker (aeval (actQ A) p) ≤ LinearMap.ker (aeval (actQ A) (p ^ k)) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ, aeval_mul_apply, hv, map_zero]

/-- `r₁(p) ≤ m_p`. -/
theorem singleBlocks_le_mult (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) :
    singleBlocks A p ≤ mult A p := by
  have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hpm : p.Monic := Count.monic_of_mem A hp
  obtain ⟨h1, h2⟩ := natDegree_mul_singleBlocks A hpi hpm
  have hm := kerRank_mult A hp
  have hle : kerRank A p 1 ≤ kerRank A p (mult A p) := by
    rw [kerRank, kerRank, pow_one]
    exact Submodule.finrank_mono (ker_le_ker_pow A p (one_le_mult A hp))
  have hdeg : 0 < p.natDegree := Irreducible.natDegree_pos hpi
  have : p.natDegree * singleBlocks A p ≤ p.natDegree * mult A p := by
    rw [h1, h2, mul_comm p.natDegree (mult A p), ← hm]
    exact (Nat.sub_le _ _).trans hle
  exact Nat.le_of_mul_le_mul_left this hdeg

/-- **Semisimplicity at `p`.** All Jordan blocks at the roots of `p` have size one
(`r₁(p) = m_p`) if and only if `ker p(A)² = ker p(A)`. -/
theorem singleBlocks_eq_mult_iff (A : Matrix ι ι ℤ) {p : ℚ[X]}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)) :
    singleBlocks A p = mult A p ↔
      LinearMap.ker (aeval (actQ A) (p ^ 2)) = LinearMap.ker (aeval (actQ A) p) := by
  have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hpm : p.Monic := Count.monic_of_mem A hp
  obtain ⟨h1, h2⟩ := natDegree_mul_singleBlocks A hpi hpm
  have hm := kerRank_mult A hp
  have hdeg : 0 < p.natDegree := Irreducible.natDegree_pos hpi
  have hk2 := kerRank_two A p
  have hk1 : kerRank A p 1 = finrank ℚ (LinearMap.ker (aeval (actQ A) p)) := by
    rw [kerRank, pow_one]
  have hle : kerRank A p 1 ≤ kerRank A p (mult A p) := by
    rw [hk1, kerRank]
    exact Submodule.finrank_mono (ker_le_ker_pow A p (one_le_mult A hp))
  constructor
  · intro heq
    rw [heq] at h1
    have hT : finrank ℚ ↥(LinearMap.ker (aeval (actQ A) p) ⊓
        LinearMap.range (aeval (actQ A) p)) = 0 := by
      have hm' : kerRank A p (mult A p) = p.natDegree * mult A p := by rw [hm, mul_comm]
      have hTle := Submodule.finrank_mono (inf_le_left : LinearMap.ker (aeval (actQ A) p) ⊓
        LinearMap.range (aeval (actQ A) p) ≤ LinearMap.ker (aeval (actQ A) p))
      generalize p.natDegree * mult A p = P at h1 hm'
      omega
    symm
    apply Submodule.eq_of_le_of_finrank_eq (ker_le_ker_pow A p (by norm_num : 1 ≤ 2))
    rw [← hk1, ← kerRank, hk2, hT, add_zero]
  · intro heq
    -- the kernels stabilize: `ker p(A)^k = ker p(A)` for `k ≥ 1`
    have hstab : ∀ k : ℕ, LinearMap.ker (aeval (actQ A) (p ^ (k + 1))) =
        LinearMap.ker (aeval (actQ A) p) := by
      intro k
      induction k with
      | zero => rw [zero_add, pow_one]
      | succ k ih =>
        refine le_antisymm (fun v hv => ?_) (ker_le_ker_pow A p (by omega))
        rw [← ih, LinearMap.mem_ker]
        rw [LinearMap.mem_ker] at hv
        have h3 : aeval (actQ A) (p ^ k) v ∈ LinearMap.ker (aeval (actQ A) (p ^ 2)) := by
          rw [LinearMap.mem_ker, ← aeval_mul_apply, ← pow_add,
            show 2 + k = k + 1 + 1 by ring]
          exact hv
        rw [heq, LinearMap.mem_ker, ← aeval_mul_apply, ← pow_succ'] at h3
        exact h3
    have hmk : kerRank A p (mult A p) = kerRank A p 1 := by
      obtain ⟨j, hj⟩ : ∃ j, mult A p = j + 1 := ⟨mult A p - 1, by have := one_le_mult A hp; omega⟩
      rw [kerRank, kerRank, hj, hstab j, pow_one]
    have hT : finrank ℚ ↥(LinearMap.ker (aeval (actQ A) p) ⊓
        LinearMap.range (aeval (actQ A) p)) = 0 := by
      have : kerRank A p 2 = kerRank A p 1 := by rw [kerRank, kerRank, heq, pow_one]
      omega
    have : p.natDegree * singleBlocks A p = p.natDegree * mult A p := by
      rw [h1, h2, hT, Nat.sub_zero, ← hmk, hm, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hdeg this

end JordanQ

/-! ### Rational ranks are real ranks -/

section RealRank

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank of a rational matrix is unchanged over `ℝ` (rank normal form). -/
theorem rank_map_real (M : Matrix ι ι ℚ) : (M.map (algebraMap ℚ ℝ)).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, hN⟩ := Matrix.exists_rank_normal_form M
  set w : ι → ℚ := fun i => Sum.elim (fun _ => (1 : ℚ)) (fun _ => 0) (e i) with hw
  have hdiag : (Matrix.fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) ℚ) 0 0 0).submatrix e e =
      Matrix.diagonal w := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
      Matrix.submatrix_diagonal_equiv]
    rfl
  have hVd := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hUd := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have hMr : M.rank = (Matrix.diagonal w).rank := by
    rw [← hdiag, ← hN, Matrix.rank_mul_eq_left_of_isUnit_det U _ hUd,
      Matrix.rank_mul_eq_right_of_isUnit_det V M hVd]
  have hN' : V.map (algebraMap ℚ ℝ) * M.map (algebraMap ℚ ℝ) * U.map (algebraMap ℚ ℝ) =
      Matrix.diagonal (fun i => algebraMap ℚ ℝ (w i)) := by
    have := congrArg (algebraMap ℚ ℝ).mapMatrix hN
    rw [hdiag] at this
    simpa [Matrix.diagonal_map, RingHom.mapMatrix_apply] using this
  have hVd' : IsUnit (V.map (algebraMap ℚ ℝ)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hVd.map _
  have hUd' : IsUnit (U.map (algebraMap ℚ ℝ)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hUd.map _
  rw [← Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVd',
    ← Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUd', hN', hMr, Matrix.rank_diagonal,
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by simp)

/-- The kernel of a rational matrix has the same dimension over `ℚ` and over `ℝ`. -/
theorem finrank_ker_map_real (M : Matrix ι ι ℚ) :
    finrank ℝ (LinearMap.ker (Matrix.toLin' (M.map (algebraMap ℚ ℝ)))) =
      finrank ℚ (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' (M.map (algebraMap ℚ ℝ)))
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have hr := rank_map_real M
  rw [Matrix.rank, Matrix.rank, ← Matrix.toLin'_apply', ← Matrix.toLin'_apply'] at hr
  rw [Module.finrank_fintype_fun_eq_card] at h1 h2
  omega

theorem aeval_actQ (A : Matrix ι ι ℤ) (g : ℚ[X]) :
    aeval (actQ A) g = Matrix.toLin' (aeval (A.map (Int.castRingHom ℚ)) g) :=
  aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℚ) (n := ι)).toAlgHom
    (A.map (Int.castRingHom ℚ)) g

theorem aeval_act_map (A : Matrix ι ι ℤ) (g : ℚ[X]) :
    aeval (act A) (g.map (algebraMap ℚ ℝ)) =
      Matrix.toLin' ((aeval (A.map (Int.castRingHom ℚ)) g).map (algebraMap ℚ ℝ)) := by
  refine LinearMap.ext fun v => ?_
  rw [KernelSplit.aeval_act, KernelSplit.aeval_map_matrix, Matrix.toLin'_apply]

/-- `dim_ℝ ker g(A) = dim_ℚ ker g(A)` for a rational polynomial `g`. -/
theorem finrank_ker_real (A : Matrix ι ι ℤ) (g : ℚ[X]) :
    finrank ℝ (LinearMap.ker (aeval (act A) (g.map (algebraMap ℚ ℝ)))) =
      finrank ℚ (LinearMap.ker (aeval (actQ A) g)) := by
  rw [aeval_act_map, aeval_actQ, finrank_ker_map_real]

/-- `dim_ℝ ker p(A)^k = dim_ℚ ker p(A)^k`. -/
theorem finrank_ker_real_pow (A : Matrix ι ι ℤ) (p : ℚ[X]) (k : ℕ) :
    finrank ℝ (LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ) ^ k))) = kerRank A p k := by
  rw [← Polynomial.map_pow, finrank_ker_real, kerRank]

/-- **The socle count of a rational factor.** For `p` monic irreducible over `ℚ`, the real socle
count of `A` at `p` is `deg p · r₁(p)`. -/
theorem socleCount_map (A : Matrix ι ι ℤ) {p : ℚ[X]} (hp : Irreducible p) (hpm : p.Monic) :
    socleCount (act A) (p.map (algebraMap ℚ ℝ)) = p.natDegree * singleBlocks A p := by
  rw [socleCount_eq, finrank_ker_real_pow A p 2, (natDegree_mul_singleBlocks A hp hpm).1]
  have := finrank_ker_real_pow A p 1
  rw [pow_one] at this
  rw [this]

/-- The coordinatewise inclusion `ℚ^ι → ℝ^ι`. -/
def toReal (ι : Type*) : (ι → ℚ) →ₗ[ℚ] (ι → ℝ) where
  toFun v := algebraMap ℚ ℝ ∘ v
  map_add' v w := by
    funext i
    simp
  map_smul' c v := by
    funext i
    simp [Algebra.smul_def]

omit [Fintype ι] [DecidableEq ι] in
theorem toReal_apply (v : ι → ℚ) : toReal ι v = algebraMap ℚ ℝ ∘ v := rfl

theorem aeval_toReal (A : Matrix ι ι ℤ) (g : ℚ[X]) (v : ι → ℚ) :
    aeval (act A) (g.map (algebraMap ℚ ℝ)) (toReal ι v) = toReal ι (aeval (actQ A) g v) := by
  rw [aeval_act_map, aeval_actQ, Matrix.toLin'_apply, Matrix.toLin'_apply, toReal_apply,
    toReal_apply]
  exact (KernelSplit.cast_mulVec _ v).symm

theorem act_toReal (A : Matrix ι ι ℤ) (v : ι → ℚ) :
    act A (toReal ι v) = toReal ι (actQ A v) := by
  have := aeval_toReal A X v
  rwa [Polynomial.map_X, aeval_X, aeval_X] at this

omit [DecidableEq ι] in
/-- A `ℚ`-linearly independent family of rational vectors is `ℝ`-linearly independent in `ℝ^ι`
(its Gram matrix is invertible over `ℚ`, hence over `ℝ`). -/
theorem linearIndependent_toReal {k : ℕ} (b : Fin k → (ι → ℚ)) (hb : LinearIndependent ℚ b) :
    LinearIndependent ℝ (fun j => toReal ι (b j)) := by
  classical
  set B : Matrix ι (Fin k) ℚ := Matrix.of fun i j => b j i with hB
  have hsum : ∀ c : Fin k → ℚ, B *ᵥ c = ∑ j, c j • b j := by
    intro c
    funext i
    simp [hB, Matrix.mulVec, dotProduct, mul_comm]
  have hB0 : ∀ c : Fin k → ℚ, B *ᵥ c = 0 → c = 0 := by
    intro c hc
    rw [hsum] at hc
    funext j
    exact Fintype.linearIndependent_iff.mp hb c hc j
  have hG : Function.Injective (Bᵀ * B).mulVec := by
    intro c c' h
    have h0 : (Bᵀ * B) *ᵥ (c - c') = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
    have h1 : (B *ᵥ (c - c')) ⬝ᵥ (B *ᵥ (c - c')) = 0 := by
      have : (c - c') ⬝ᵥ ((Bᵀ * B) *ᵥ (c - c')) = 0 := by rw [h0, dotProduct_zero]
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
      exact this
    exact sub_eq_zero.mp (hB0 _ (dotProduct_self_eq_zero.mp h1))
  have hGu : IsUnit (Bᵀ * B) := Matrix.mulVec_injective_iff_isUnit.mp hG
  set BR : Matrix ι (Fin k) ℝ := B.map (algebraMap ℚ ℝ) with hBR
  have hGR : IsUnit (BRᵀ * BR) := by
    have : BRᵀ * BR = (algebraMap ℚ ℝ).mapMatrix (Bᵀ * B) := by
      rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
    rw [this]
    exact hGu.map _
  have hBR0 : ∀ c : Fin k → ℝ, BR *ᵥ c = 0 → c = 0 := by
    intro c hc
    have h1 : (BRᵀ * BR) *ᵥ c = (BRᵀ * BR) *ᵥ 0 := by
      rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero, Matrix.mulVec_zero]
    exact Matrix.mulVec_injective_iff_isUnit.mpr hGR h1
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have e : BR *ᵥ c = ∑ j, c j • toReal ι (b j) := by
    funext i
    simp [hBR, hB, Matrix.mulVec, dotProduct, toReal_apply, mul_comm]
  rw [← e] at hc
  exact congrFun (hBR0 c hc) j

/-- **Uniformity over the real factors of `p`.** Let `W ⊆ ℚ^ι` be `A`-invariant and killed by
`p(A)`, `p` monic irreducible over `ℚ`. The real span `W_ℝ` of a `ℚ`-basis of `W` has dimension
`dim W`, and `A` acts on it with characteristic polynomial `p^{dim W / deg p}` (the matrix of `A`
in that basis is rational); hence every monic irreducible real factor `q` of `p` has
`dim (W_ℝ ∩ ker q(A)) = deg q · dim W / deg p`. -/
theorem exists_realSpan (A : Matrix ι ι ℤ) {p : ℚ[X]} (hp : Irreducible p) (hpm : p.Monic)
    {W : Submodule ℚ (ι → ℚ)} (hW : ∀ v ∈ W, actQ A v ∈ W)
    (hWp : ∀ v ∈ W, aeval (actQ A) p v = 0) :
    ∃ Wr : Submodule ℝ (ι → ℝ), Wr ≤ Submodule.span ℝ (toReal ι '' W) ∧
      finrank ℝ Wr = finrank ℚ W ∧
      ∀ q : ℝ[X], Irreducible q → q.Monic → q ∣ p.map (algebraMap ℚ ℝ) →
        finrank ℝ ↥(Wr ⊓ LinearMap.ker (aeval (act A) q)) * p.natDegree =
          q.natDegree * finrank ℚ W := by
  classical
  have hli : LinearIndependent ℝ
      (fun j => toReal ι ((Module.finBasis ℚ W j : W) : ι → ℚ)) :=
    linearIndependent_toReal _ ((Module.finBasis ℚ W).linearIndependent.map' W.subtype
      (Submodule.ker_subtype W))
  have hle : Submodule.span ℝ (Set.range
      (fun j => toReal ι ((Module.finBasis ℚ W j : W) : ι → ℚ))) ≤
      Submodule.span ℝ (toReal ι '' W) :=
    Submodule.span_mono (by
      rintro _ ⟨j, rfl⟩
      exact ⟨_, (Module.finBasis ℚ W j).2, rfl⟩)
  refine ⟨_, hle, by rw [finrank_span_eq_card hli, Fintype.card_fin], ?_⟩
  intro q hq hqm hqp
  set b := Module.finBasis ℚ W with hb
  set Wr := Submodule.span ℝ (Set.range (fun j => toReal ι ((b j : W) : ι → ℚ))) with hWr
  -- rational combinations of the basis lie in `Wr`
  have hcomb : ∀ w ∈ W, toReal ι w ∈ Wr := by
    intro w hw
    have h1 := congrArg (fun x : W => toReal ι (x : ι → ℚ)) (b.sum_repr ⟨w, hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at h1
    rw [← h1]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hWr_le : Wr ≤ Wr.comap (act A) := Submodule.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    show act A (toReal ι ((b j : W) : ι → ℚ)) ∈ Wr
    rw [act_toReal]
    exact hcomb _ (hW _ (b j).2))
  have hWr_inv : ∀ v ∈ Wr, act A v ∈ Wr := fun v hv => hWr_le hv
  have hWr_p : Wr ≤ LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ))) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      show aeval (act A) (p.map (algebraMap ℚ ℝ)) (toReal ι ((b j : W) : ι → ℚ)) = 0
      rw [aeval_toReal, hWp _ (b j).2, map_zero])
  -- the matrix of `A` on `Wr` is the rational matrix of `A` on `W`
  have hgb : ∀ j, (act A).restrict hWr_inv (Basis.span hli j) =
      ∑ i, algebraMap ℚ ℝ (LinearMap.toMatrix b b ((actQ A).restrict hW) i j) •
        Basis.span hli i := by
    intro j
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, Basis.span_apply, Submodule.coe_sum]
    have h1 := congrArg (fun x : W => toReal ι (x : ι → ℚ))
      (b.sum_repr ((actQ A).restrict hW (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
      LinearMap.coe_restrict_apply] at h1
    rw [act_toReal, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Basis.span_apply, algebraMap_smul, LinearMap.toMatrix_apply]
  have hMat : LinearMap.toMatrix (Basis.span hli) (Basis.span hli) ((act A).restrict hWr_inv) =
      (LinearMap.toMatrix b b ((actQ A).restrict hW)).map (algebraMap ℚ ℝ) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hgb, Basis.repr_sum_self, Matrix.map_apply]
  have hres0 : aeval ((actQ A).restrict hW) p = 0 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, aeval_restrict_apply]
    exact hWp x x.2
  have hχg : ((act A).restrict hWr_inv).charpoly =
      (p.map (algebraMap ℚ ℝ)) ^ (finrank ℚ W / p.natDegree) := by
    rw [← LinearMap.charpoly_toMatrix ((act A).restrict hWr_inv) (Basis.span hli), hMat,
      Matrix.charpoly_map, LinearMap.charpoly_toMatrix,
      charpoly_eq_pow_of_aeval_eq_zero _ hp hpm hres0, Polynomial.map_pow]
  have hgp : aeval ((act A).restrict hWr_inv) (p.map (algebraMap ℚ ℝ)) = 0 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, aeval_restrict_apply]
    exact hWr_p x.2
  -- `p = q s` over `ℝ` with `q`, `s` coprime
  obtain ⟨s, hs⟩ := hqp
  have hsm : s.Monic := hqm.of_mul_monic_left (by rw [← hs]; exact hpm.map _)
  have hsq : Squarefree (p.map (algebraMap ℚ ℝ)) := (hp.separable.map).squarefree
  have hcop : IsCoprime q s := (Irreducible.coprime_iff_not_dvd hq).mpr fun hdvd => by
    obtain ⟨t, ht⟩ := hdvd
    have : q * q ∣ p.map (algebraMap ℚ ℝ) := ⟨t, by rw [hs, ht]; ring⟩
    exact hq.not_isUnit (hsq q this)
  have hkd : p.natDegree ∣ finrank ℚ W := natDegree_dvd_finrank_of_le_ker (actQ A) hp hpm hW hWp
  set n := finrank ℚ W / p.natDegree with hn
  have hkn : finrank ℚ W = n * p.natDegree := (Nat.div_mul_cancel hkd).symm
  -- the kernel of `q(A)` on `Wr`, through the restriction
  have hmap : (LinearMap.ker (aeval ((act A).restrict hWr_inv) q)).map Wr.subtype =
      Wr ⊓ LinearMap.ker (aeval (act A) q) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [← aeval_restrict_apply (act A) hWr_inv q y, hy, ZeroMemClass.coe_zero]
    · rintro ⟨hx, hxq⟩
      refine ⟨⟨x, hx⟩, Subtype.ext ?_, rfl⟩
      rw [aeval_restrict_apply, ZeroMemClass.coe_zero]
      exact hxq
  have hfr := Submodule.finrank_map_subtype_eq Wr
    (LinearMap.ker (aeval ((act A).restrict hWr_inv) q))
  rw [hmap] at hfr
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have hk0 : finrank ℚ W = 0 := by rw [hkn, hn0, zero_mul]
    have h0 : finrank ℝ ↥(Wr ⊓ LinearMap.ker (aeval (act A) q)) = 0 := by
      have h1 := Submodule.finrank_mono (inf_le_left : Wr ⊓ LinearMap.ker (aeval (act A) q) ≤ Wr)
      have h2 : finrank ℝ Wr = finrank ℚ W := by
        rw [hWr, finrank_span_eq_card hli, Fintype.card_fin]
      omega
    rw [h0, hk0, zero_mul, mul_zero]
  have hχ2 : ((act A).restrict hWr_inv).charpoly = q ^ n * s ^ n := by rw [hχg, hs, mul_pow]
  have hdim := finrank_ker_aeval_of_coprime ((act A).restrict hWr_inv) (hqm.pow n) (hsm.pow n)
    hχ2 (hcop.pow)
  rw [natDegree_pow] at hdim
  have hker : LinearMap.ker (aeval ((act A).restrict hWr_inv) (q ^ n)) =
      LinearMap.ker (aeval ((act A).restrict hWr_inv) q) := by
    obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
    · rw [LinearMap.mem_ker] at hv ⊢
      have h1 : aeval ((act A).restrict hWr_inv) q v ∈
          LinearMap.ker (aeval ((act A).restrict hWr_inv) s) := by
        rw [LinearMap.mem_ker, ← aeval_mul_apply, mul_comm, ← hs, hgp, LinearMap.zero_apply]
      have h2 : aeval ((act A).restrict hWr_inv) q v ∈
          LinearMap.ker (aeval ((act A).restrict hWr_inv) (q ^ j)) := by
        rw [LinearMap.mem_ker, ← aeval_mul_apply, ← pow_succ, ← hj]
        exact hv
      exact (Submodule.disjoint_def.1 (Polynomial.disjoint_ker_aeval_of_isCoprime _
        (hcop.symm.pow_right (n := j)))) _ h1 h2
    · rw [LinearMap.mem_ker] at hv ⊢
      rw [hj, pow_succ, aeval_mul_apply, hv, map_zero]
  rw [hfr, ← hker, hdim, hkn]
  ring

/-- A monic irreducible real factor `q` of a rational irreducible `p` has a monic cofactor coprime
to it (`p` is separable). -/
theorem exists_coprime_cofactor {p : ℚ[X]} (hp : Irreducible p) (hpm : p.Monic) {q : ℝ[X]}
    (hq : Irreducible q) (hqm : q.Monic) (hqp : q ∣ p.map (algebraMap ℚ ℝ)) :
    ∃ s : ℝ[X], s.Monic ∧ p.map (algebraMap ℚ ℝ) = q * s ∧ IsCoprime q s := by
  obtain ⟨s, hs⟩ := hqp
  have hsm : s.Monic := hqm.of_mul_monic_left (by rw [← hs]; exact hpm.map _)
  have hsq : Squarefree (p.map (algebraMap ℚ ℝ)) := (hp.separable.map).squarefree
  refine ⟨s, hsm, hs, (Irreducible.coprime_iff_not_dvd hq).mpr fun hdvd => ?_⟩
  obtain ⟨t, ht⟩ := hdvd
  have : q * q ∣ p.map (algebraMap ℚ ℝ) := ⟨t, by rw [hs, ht]; ring⟩
  exact hq.not_isUnit (hsq q this)

/-- **Real eigenspaces of a rational factor.** For `p` monic irreducible over `ℚ` and `q` a monic
irreducible real factor of `p`: `dim_ℝ ker q(A) · deg p = deg q · dim_ℚ ker p(A)`. -/
theorem finrank_ker_real_factor (A : Matrix ι ι ℤ) {p : ℚ[X]} (hp : Irreducible p)
    (hpm : p.Monic) {q : ℝ[X]} (hq : Irreducible q) (hqm : q.Monic)
    (hqp : q ∣ p.map (algebraMap ℚ ℝ)) :
    finrank ℝ (LinearMap.ker (aeval (act A) q)) * p.natDegree = q.natDegree * kerRank A p 1 := by
  obtain ⟨Wr, hle, hfin, hq'⟩ := exists_realSpan A hp hpm
    (W := LinearMap.ker (aeval (actQ A) p)) (mapsTo_ker _ p) (fun v hv => hv)
  have hWr : Wr = LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ))) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · refine hle.trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨w, hw, rfl⟩
      show aeval (act A) (p.map (algebraMap ℚ ℝ)) (toReal ι w) = 0
      rw [aeval_toReal, LinearMap.mem_ker.mp hw, map_zero]
    · rw [hfin, finrank_ker_real]
  have hqle : LinearMap.ker (aeval (act A) q) ≤ Wr := by
    rw [hWr]
    intro v hv
    obtain ⟨s, hs⟩ := hqp
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hs, mul_comm, aeval_mul_apply, hv, map_zero]
  have := hq' q hq hqm hqp
  rw [inf_eq_right.mpr hqle] at this
  rw [kerRank, pow_one]
  exact this

/-- **Real socles of a rational factor.** For `p` monic irreducible over `ℚ` and `q` a monic
irreducible real factor of `p`:
`dim_ℝ (ker q(A) ∩ im q(A)) · deg p = deg q · dim_ℚ (ker p(A) ∩ im p(A))`. -/
theorem finrank_ker_inf_range_real_factor (A : Matrix ι ι ℤ) {p : ℚ[X]} (hp : Irreducible p)
    (hpm : p.Monic) {q : ℝ[X]} (hq : Irreducible q) (hqm : q.Monic)
    (hqp : q ∣ p.map (algebraMap ℚ ℝ)) :
    finrank ℝ ↥(LinearMap.ker (aeval (act A) q) ⊓ LinearMap.range (aeval (act A) q)) *
        p.natDegree =
      q.natDegree * finrank ℚ ↥(LinearMap.ker (aeval (actQ A) p) ⊓
        LinearMap.range (aeval (actQ A) p)) := by
  have hT : ∀ v ∈ LinearMap.ker (aeval (actQ A) p) ⊓ LinearMap.range (aeval (actQ A) p),
      actQ A v ∈ LinearMap.ker (aeval (actQ A) p) ⊓ LinearMap.range (aeval (actQ A) p) :=
    fun v hv => ⟨mapsTo_ker _ p v hv.1, mapsTo_range _ p v hv.2⟩
  obtain ⟨Wr, hle, hfin, hq'⟩ := exists_realSpan A hp hpm hT (fun v hv => hv.1)
  have hWr : Wr = LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ))) ⊓
      LinearMap.range (aeval (act A) (p.map (algebraMap ℚ ℝ))) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · refine hle.trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨w, ⟨hw1, ⟨u, rfl⟩⟩, rfl⟩
      refine ⟨?_, ⟨toReal ι u, aeval_toReal A p u⟩⟩
      show aeval (act A) (p.map (algebraMap ℚ ℝ)) (toReal ι _) = 0
      rw [aeval_toReal, LinearMap.mem_ker.mp hw1, map_zero]
    · have e1 := finrank_ker_sq (act A) (p.map (algebraMap ℚ ℝ))
      have e2 := finrank_ker_sq (actQ A) p
      have e3 := finrank_ker_real A p
      have e4 := finrank_ker_real A (p ^ 2)
      rw [Polynomial.map_pow] at e4
      rw [hfin]
      omega
  obtain ⟨s, -, hs, hcop⟩ := exists_coprime_cofactor hp hpm hq hqm hqp
  have hqle : LinearMap.ker (aeval (act A) q) ≤
      LinearMap.ker (aeval (act A) (p.map (algebraMap ℚ ℝ))) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hs, mul_comm, aeval_mul_apply, hv, map_zero]
  have hinf : Wr ⊓ LinearMap.ker (aeval (act A) q) =
      LinearMap.ker (aeval (act A) q) ⊓ LinearMap.range (aeval (act A) q) := by
    rw [hWr, inf_comm, ← inf_assoc, inf_eq_left.mpr hqle, hs, ker_inf_range_mul _ hcop]
  have := hq' q hq hqm hqp
  rw [hinf] at this
  exact this

/-- **Uniformity of the count of Jordan blocks of size one.** For `p` monic irreducible over `ℚ` and
every monic irreducible real factor `q` of `p`, the real socle count at `q` is `deg q · r₁(p)`: each
root of `p` carries `r₁(p)` Jordan blocks of size one. -/
theorem socleCount_real_factor (A : Matrix ι ι ℤ) {p : ℚ[X]} (hp : Irreducible p)
    (hpm : p.Monic) {q : ℝ[X]} (hq : Irreducible q) (hqm : q.Monic)
    (hqp : q ∣ p.map (algebraMap ℚ ℝ)) :
    socleCount (act A) q = q.natDegree * singleBlocks A p := by
  have h1 := finrank_ker_real_factor A hp hpm hq hqm hqp
  have h2 := finrank_ker_inf_range_real_factor A hp hpm hq hqm hqp
  have e := (natDegree_mul_singleBlocks A hp hpm).1.trans (natDegree_mul_singleBlocks A hp hpm).2
  have hd : 0 < p.natDegree := Irreducible.natDegree_pos hp
  have hT := Submodule.finrank_mono (inf_le_left : LinearMap.ker (aeval (act A) q) ⊓
    LinearMap.range (aeval (act A) q) ≤ LinearMap.ker (aeval (act A) q))
  have hTq : finrank ℚ ↥(LinearMap.ker (aeval (actQ A) p) ⊓ LinearMap.range (aeval (actQ A) p)) ≤
      kerRank A p 1 := by
    rw [kerRank, pow_one]
    exact Submodule.finrank_mono inf_le_left
  have e' : (p.natDegree : ℤ) * singleBlocks A p = (kerRank A p 1 : ℤ) -
      finrank ℚ ↥(LinearMap.ker (aeval (actQ A) p) ⊓ LinearMap.range (aeval (actQ A) p)) := by
    rw [← Nat.cast_sub hTq]
    exact_mod_cast e
  have h1' : (finrank ℝ (LinearMap.ker (aeval (act A) q)) : ℤ) * p.natDegree =
      q.natDegree * kerRank A p 1 := by exact_mod_cast h1
  have h2' : (finrank ℝ ↥(LinearMap.ker (aeval (act A) q) ⊓ LinearMap.range (aeval (act A) q)) :
      ℤ) * p.natDegree = q.natDegree * finrank ℚ ↥(LinearMap.ker (aeval (actQ A) p) ⊓
        LinearMap.range (aeval (actQ A) p)) := by exact_mod_cast h2
  have key : (socleCount (act A) q : ℤ) * p.natDegree =
      ((q.natDegree * singleBlocks A p : ℕ) : ℤ) * p.natDegree := by
    rw [socleCount, Nat.cast_sub hT]
    push_cast
    linear_combination h1' - h2' - (q.natDegree : ℤ) * e'
  have : socleCount (act A) q * p.natDegree = q.natDegree * singleBlocks A p * p.natDegree := by
    exact_mod_cast key
  exact Nat.eq_of_mul_eq_mul_right hd this

theorem mem_eigenvalues_iff (A : Matrix ι ι ℤ) {z : ℂ} :
    z ∈ eigenvalues A ↔ aeval z (act A).charpoly = 0 := by
  rw [eigenvalues, ← Hyperbolic.map_charpoly_complex, ← charpoly_act,
    Count.mem_roots_map_iff (LinearMap.charpoly_monic _).ne_zero]

/-- For a `DiskSplit` of `χ_A`, the roots `S` of `c` are the distinct eigenvalues of `A` of
modulus one. -/
theorem DiskSplit.S_eq (A : Matrix ι ι ℤ) (D : DiskSplit (act A).charpoly) :
    D.S = ((eigenvalues A).filter (fun z => ‖z‖ = 1)).toFinset := by
  classical
  ext z
  have hc : aeval z D.c = 0 ↔ z ∈ D.S := by
    rw [← aeval_map_algebraMap ℂ, D.map_c, coe_aeval_eq_eval, Lagrange.eval_nodal,
      Finset.prod_eq_zero_iff]
    simp [sub_eq_zero]
  have hcqc : aeval z D.c = 0 ↔ aeval z D.qc = 0 := by
    constructor
    · intro h
      obtain ⟨r, hr⟩ := D.c_dvd
      rw [hr, map_mul, h, zero_mul]
    · intro h
      obtain ⟨r, hr⟩ := D.dvd_c_pow
      have h1 : aeval z D.c ^ D.N = 0 := by rw [← map_pow, hr, map_mul, h, zero_mul]
      rcases Nat.eq_zero_or_pos D.N with h0 | hpos
      · rw [h0, pow_zero] at h1
        exact absurd h1 one_ne_zero
      · exact (pow_eq_zero_iff hpos.ne').mp h1
  have hχz : aeval z (act A).charpoly = aeval z D.qs * aeval z D.qc * aeval z D.qu := by
    rw [← map_mul, ← map_mul, ← D.eq_mul]
  rw [← hc, hcqc, Multiset.mem_toFinset, Multiset.mem_filter, mem_eigenvalues_iff, hχz]
  constructor
  · intro h
    exact ⟨by rw [h, mul_zero, zero_mul], D.root_qc z h⟩
  · rintro ⟨h0, h1⟩
    rcases mul_eq_zero.mp h0 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · have := D.root_qs z h3
        linarith
      · exact h3
    · have := D.root_qu z h2
      linarith

/-- **The circle socle in Jordan data.** For a `DiskSplit` of `χ_A`, the socle count at `c` is
`Σ_{|λ| = 1} s_λ`, the sum over the distinct eigenvalues `λ` of modulus one of `r₁(minpoly_ℚ λ)`,
the number of Jordan blocks of size one at `λ`. -/
theorem socleCount_eq_sum (A : Matrix ι ι ℤ) (D : DiskSplit (act A).charpoly) :
    socleCount (act A) D.c = ∑ z ∈ D.S, singleBlocks A (minpoly ℚ z) := by
  classical
  have hFirr : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors D.c, Irreducible q :=
    fun q hq => UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
  have hFmon : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors D.c, q.Monic := fun q hq => by
    rw [← UniqueFactorizationMonoid.normalize_normalized_factor q hq]
    exact Polynomial.monic_normalize (hFirr q hq).ne_zero
  have hFnd : (UniqueFactorizationMonoid.normalizedFactors D.c).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors D.monic_c.ne_zero).mp
      D.squarefree_c
  have hprod : (UniqueFactorizationMonoid.normalizedFactors D.c).prod = D.c :=
    Polynomial.eq_of_monic_of_associated
      (by simpa using Polynomial.monic_multiset_prod_of_monic _ id hFmon) D.monic_c
      (UniqueFactorizationMonoid.prod_normalizedFactors D.monic_c.ne_zero)
  have hχ : (act A).charpoly =
      ((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).map
        (Polynomial.map (algebraMap ℚ ℝ))).prod := by
    rw [← Polynomial.map_multiset_prod, Count.prod_normalizedFactors_eq,
      KernelSplit.charpolyQ_map_real, charpoly_act]
  -- each real factor of `c` lies over a rational factor `p` of `χ_A`, and has socle `deg q · r₁(p)`
  have hterm : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors D.c, socleCount (act A) q =
      ((q.map (algebraMap ℝ ℂ)).roots.map (fun z => singleBlocks A (minpoly ℚ z))).sum := by
    intro q hq
    have hqχ : q ∣ (act A).charpoly := by
      refine (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq).trans
        (D.c_dvd.trans ?_)
      have : D.qc ∣ D.qs * D.qc * D.qu := (dvd_mul_left _ _).mul_right _
      rwa [← D.eq_mul] at this
    rw [hχ] at hqχ
    obtain ⟨p, hpF, hqp⟩ := (hFirr q hq).prime.exists_mem_multiset_map_dvd hqχ
    have hpi := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hpF
    have hpm := Count.monic_of_mem A hpF
    rw [socleCount_real_factor A hpi hpm (hFirr q hq) (hFmon q hq) hqp]
    have hroots : ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots,
        singleBlocks A (minpoly ℚ z) = singleBlocks A p := by
      intro z hz
      have hqz : aeval z q = 0 := (Count.mem_roots_map_iff (hFirr q hq).ne_zero).mp hz
      have hpz : aeval z p = 0 := by
        obtain ⟨t, ht⟩ := hqp
        have : aeval z (p.map (algebraMap ℚ ℝ)) = 0 := by rw [ht, map_mul, hqz, zero_mul]
        rwa [aeval_map_algebraMap] at this
      rw [← minpoly.eq_of_irreducible_of_monic hpi hpz hpm]
    rw [Multiset.map_congr rfl hroots, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
      IsAlgClosed.card_roots_map_eq_natDegree_of_injective _ (algebraMap ℝ ℂ).injective]
  -- sum over the real factors, then over their roots
  have hroots_c : (D.c.map (algebraMap ℝ ℂ)).roots =
      (UniqueFactorizationMonoid.normalizedFactors D.c).bind
        (fun q => (q.map (algebraMap ℝ ℂ)).roots) := by
    conv_lhs => rw [← hprod]
    rw [Polynomial.map_multiset_prod, roots_multiset_prod, Multiset.bind_map]
    rw [Multiset.mem_map]
    rintro ⟨q, hq, h0⟩
    exact (Polynomial.map_ne_zero (hFirr q hq).ne_zero) h0
  have hS : (D.c.map (algebraMap ℝ ℂ)).roots = D.S.val := by
    rw [D.map_c, Lagrange.nodal_eq]
    exact roots_prod_X_sub_C D.S
  rw [← hprod, socleCount_multiset_prod (act A) _ hFnd fun q hq => ⟨hFirr q hq, hFmon q hq⟩,
    Multiset.map_congr rfl hterm, ← Multiset.sum_bind, ← Multiset.map_bind, ← hroots_c, hS]
  rfl

end RealRank

/-! ### The largest power-bounded summand in Jordan data -/

section LemmaFive

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The largest power-bounded summand of an integer matrix, in Jordan data.** The largest
dimension of an `A`-invariant subspace of `ℝ^ι` that has an `A`-invariant complement and on which
`A` is power-bounded is `dim E^s + Σ_{|λ|=1} s_λ`: the number of eigenvalues of modulus `< 1` (with
multiplicity) plus, over the distinct eigenvalues `λ` of modulus one, the number `r₁(minpoly_ℚ λ)`
of Jordan blocks of size one at `λ`. -/
theorem largest_powerBounded_summand_jordan (A : Matrix ι ι ℤ) :
    IsGreatest {d : ℕ | ∃ H E : Submodule ℝ (ι → ℝ), IsCompl H E ∧ (∀ v ∈ H, act A v ∈ H) ∧
      (∀ v ∈ E, act A v ∈ E) ∧ PowerBoundedOn (act A) H ∧ finrank ℝ H = d}
      (Multiset.card ((eigenvalues A).filter (fun z => ‖z‖ < 1)) +
        ∑ z ∈ ((eigenvalues A).filter (fun z => ‖z‖ = 1)).toFinset,
          singleBlocks A (minpoly ℚ z)) := by
  obtain ⟨D⟩ := exists_diskSplit (act A).charpoly (LinearMap.charpoly_monic _)
  have h1 : D.qs.natDegree = Multiset.card ((eigenvalues A).filter (fun z => ‖z‖ < 1)) := by
    rw [D.natDegree_qs, eigenvalues, ← Hyperbolic.map_charpoly_complex, ← charpoly_act]
  have h2 := socleCount_eq_sum A D
  rw [DiskSplit.S_eq A D] at h2
  rw [← h1, ← h2]
  exact isGreatest_powerBounded_summand (act A) D

/-- Eigenvalue counts split over the rational factors of `χ_A` (with multiplicity). -/
theorem card_eigenvalues_filter (A : Matrix ι ι ℤ) (P : ℂ → Prop) [DecidablePred P] :
    Multiset.card ((eigenvalues A).filter P) =
      ((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).map
        fun p => Multiset.card ((p.map (algebraMap ℚ ℂ)).roots.filter P)).sum := by
  rw [Count.eigenvalues_eq_bind A, Multiset.filter_bind, Multiset.card_bind]
  rfl

/-- `U(A) = Σ_p m_p u_p`. -/
theorem unstableCount_eq_sum (A : Matrix ι ι ℤ) :
    unstableCount A = ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
      mult A p * expandingRoots p := by
  classical
  rw [unstableCount, card_eigenvalues_filter, Finset.sum_multiset_map_count]
  rfl

/-- `dim E^s = Σ_p m_p s_p`. -/
theorem card_inside_eq_sum (A : Matrix ι ι ℤ) :
    Multiset.card ((eigenvalues A).filter (fun z => ‖z‖ < 1)) =
      ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        mult A p * insideRoots p := by
  classical
  rw [card_eigenvalues_filter, Finset.sum_multiset_map_count]
  rfl

/-- `Σ_{|λ|=1} s_λ = Σ_p c_p r₁(p)`: the distinct eigenvalues of modulus one are the roots of
modulus one of the distinct rational factors `p`, `c_p` for each `p`, each carrying `r₁(p)`
Jordan blocks of size one. -/
theorem sum_circle_singleBlocks (A : Matrix ι ι ℤ) :
    ∑ z ∈ ((eigenvalues A).filter (fun z => ‖z‖ = 1)).toFinset, singleBlocks A (minpoly ℚ z) =
      ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        circleRoots p * singleBlocks A p := by
  classical
  have hirr : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A), Irreducible p :=
    fun p hp => UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hmon : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A), p.Monic :=
    fun p hp => Count.monic_of_mem A hp
  have hR : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors (charpolyQ A),
      ((p.map (algebraMap ℚ ℂ)).roots).Nodup := fun p hp =>
    nodup_roots (hirr p hp).separable.map
  have hT : ((eigenvalues A).filter (fun z => ‖z‖ = 1)).toFinset =
      ((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).dedup.bind
        fun p => (p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ‖z‖ = 1)).toFinset := by
    ext z
    simp only [Multiset.mem_toFinset, Multiset.mem_filter, Count.eigenvalues_eq_bind A,
      Multiset.mem_bind, Multiset.mem_dedup]
    constructor
    · rintro ⟨⟨p, hp, hz⟩, hP⟩
      exact ⟨p, hp, hz, hP⟩
    · rintro ⟨p, hp, hz, hP⟩
      exact ⟨⟨p, hp, hz⟩, hP⟩
  have hTnd : ((UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).dedup.bind
      fun p => (p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ‖z‖ = 1)).Nodup := by
    refine Multiset.nodup_bind.mpr ⟨fun p hp => (hR p (Multiset.mem_dedup.mp hp)).filter _, ?_⟩
    refine Multiset.Nodup.pairwise (fun p hp p' hp' hne => ?_) (Multiset.nodup_dedup _)
    rw [Multiset.mem_dedup] at hp hp'
    show Disjoint _ _
    refine Multiset.disjoint_left.mpr fun {z} hz hz' => hne ?_
    have h1 := (Count.mem_roots_map_iff (hirr p hp).ne_zero).mp (Multiset.mem_of_mem_filter hz)
    have h2 := (Count.mem_roots_map_iff (hirr p' hp').ne_zero).mp (Multiset.mem_of_mem_filter hz')
    exact Count.eq_of_common_root (hirr p hp) (hmon p hp) (hirr p' hp') (hmon p' hp') h1 h2
  rw [hT, Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hTnd,
    Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum, Multiset.toFinset_val]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  rw [Multiset.mem_dedup] at hp
  have hconst : ∀ z ∈ (p.map (algebraMap ℚ ℂ)).roots.filter (fun z => ‖z‖ = 1),
      singleBlocks A (minpoly ℚ z) = singleBlocks A p := by
    intro z hz
    have hpz := (Count.mem_roots_map_iff (hirr p hp).ne_zero).mp (Multiset.mem_of_mem_filter hz)
    rw [← minpoly.eq_of_irreducible_of_monic (hirr p hp) hpz (hmon p hp)]
  rw [Multiset.map_congr rfl hconst, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]
  rfl

/-- **The largest power-bounded summand of an integer matrix, by rational factors.** The largest
power-bounded `A`-invariant summand of `ℝ^ι` has dimension `Σ_p (m_p s_p + c_p r₁(p))`, over the
distinct monic irreducible factors `p` of `χ_A` over `ℚ`. -/
theorem largest_powerBounded_summand_factors (A : Matrix ι ι ℤ) :
    IsGreatest {d : ℕ | ∃ H E : Submodule ℝ (ι → ℝ), IsCompl H E ∧ (∀ v ∈ H, act A v ∈ H) ∧
      (∀ v ∈ E, act A v ∈ E) ∧ PowerBoundedOn (act A) H ∧ finrank ℝ H = d}
      (∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        (mult A p * insideRoots p + circleRoots p * singleBlocks A p)) := by
  rw [Finset.sum_add_distrib, ← card_inside_eq_sum, ← sum_circle_singleBlocks]
  exact largest_powerBounded_summand_jordan A

/-- `#ι = Σ_p m_p deg p`. -/
theorem card_eq_sum_mult_natDegree (A : Matrix ι ι ℤ) :
    Fintype.card ι = ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
      mult A p * p.natDegree := by
  classical
  have h1 : (charpolyQ A).natDegree = Fintype.card ι := by
    rw [charpolyQ, (Matrix.charpoly_monic A).natDegree_map, Matrix.charpoly_natDegree_eq_dim]
  rw [← h1]
  conv_lhs => rw [← Count.prod_normalizedFactors_eq A]
  rw [natDegree_multiset_prod_of_monic _ (fun p hp => Count.monic_of_mem A hp),
    Finset.sum_multiset_map_count]
  rfl

/-- **The lower bound from the largest power-bounded summand.** Every admissible `A`-invariant
scheme has `dim E ≥ Σ_p (m_p u_p + c_p (m_p − r₁(p)))`: every expanding direction, and every
Jordan block of size `≥ 2` at a root of modulus one, is physical. -/
theorem sum_le_finrank_E (A : Matrix ι ι ℤ) (S : InvariantCPS A) (hS : S.Admissible) :
    ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        (mult A p * expandingRoots p + circleRoots p * (mult A p - singleBlocks A p)) ≤
      finrank ℝ S.E := by
  classical
  have hH := (largest_powerBounded_summand_factors A).2
    ⟨S.H, S.E, S.isCompl.symm, S.mapsTo_H, S.mapsTo_E, (admissible_iff_powerBounded S).mp hS, rfl⟩
  have hdim := Submodule.finrank_add_eq_of_isCompl S.isCompl
  rw [Module.finrank_fintype_fun_eq_card, card_eq_sum_mult_natDegree A] at hdim
  have hsplit : ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
      mult A p * p.natDegree =
      ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        (mult A p * insideRoots p + circleRoots p * singleBlocks A p) +
      ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors (charpolyQ A)).toFinset,
        (mult A p * expandingRoots p + circleRoots p * (mult A p - singleBlocks A p)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hle := singleBlocks_le_mult A (Multiset.mem_toFinset.mp hp)
    rw [← insideRoots_add_circleRoots_add_expandingRoots p]
    obtain ⟨t, ht⟩ : ∃ t, mult A p = singleBlocks A p + t := ⟨_, (Nat.add_sub_cancel' hle).symm⟩
    rw [ht, Nat.add_sub_cancel_left]
    ring
  omega

end LemmaFive

end JordanData

end

end InflationDimension
