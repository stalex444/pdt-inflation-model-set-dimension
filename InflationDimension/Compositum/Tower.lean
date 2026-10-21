module
public import Mathlib

@[expose] public section
/-!
# The degree-12 field `L = K₃[Y]/(Y⁴ − Y − 1)` over `K₃ = ℚ[X]/(X³ − X − 1)`

Ported from the author's registered entry PALOMAR-2026-10-21-000012
(stalex444/pdt-hermite-signature-compositum@5aa870e9), `HermiteCompositum/Defs.lean` (from the
sections `HermiteCompositum.Port014` and `HermiteCompositum.Instance`: `fρ`, `fQ`, their monicity
and degrees, `irreducible_map_of_coprime_finrank`, `algebraRat_eq`, the tower `K₃`, `g`,
`L` with its instances, `ρ`, `Q`, `aeval_ρ`, `aeval_Q`) and `HermiteCompositum/Instance.lean`
(`g_natDegree`, `finrank_K₃_L`, `finrank_L`); changes: the irreducibility of `X³ − X − 1` and
`X⁴ − X − 1` over `ℚ` is taken from Mathlib (`X_pow_sub_X_sub_one_irreducible_rat`) in place of
the reduction modulo 2, and only these declarations are kept.
-/

open Polynomial

namespace HermiteCompositum.Port014

/-- The quartic `X⁴ − X − 1`. -/
noncomputable def fQ : ℚ[X] := X ^ 4 - X - 1

/-- The cubic `X³ − X − 1`. -/
noncomputable def fρ : ℚ[X] := X ^ 3 - X - 1

theorem fQ_monic : fQ.Monic := by
  unfold fQ; monicity!

theorem fρ_monic : fρ.Monic := by
  unfold fρ; monicity!

theorem fQ_natDegree : fQ.natDegree = 4 := by
  unfold fQ; compute_degree!

theorem fρ_natDegree : fρ.natDegree = 3 := by
  unfold fρ; compute_degree!

/-- x³ - x - 1 is irreducible over ℚ. -/
theorem cubicQ_irreducible : Irreducible (X ^ 3 - X - 1 : ℚ[X]) :=
  X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

/-- x⁴ - x - 1 is irreducible over ℚ. -/
theorem quarticQ_irreducible : Irreducible (X ^ 4 - X - 1 : ℚ[X]) :=
  X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

end HermiteCompositum.Port014

namespace HermiteCompositum.Instance

open Polynomial NumberField NumberField.InfinitePlace IntermediateField Module

/-- An irreducible monic polynomial over a field `k` stays irreducible over a finite extension
`F/k` whose degree is coprime to the degree of the polynomial. (Used for `Y⁴ − Y − 1` over the
cubic field; the general statement costs nothing extra.) -/
theorem irreducible_map_of_coprime_finrank {k F : Type*} [Field k] [Field F] [Algebra k F]
    [FiniteDimensional k F] {p : k[X]} (hp : Irreducible p) (hm : p.Monic)
    (hcop : Nat.Coprime p.natDegree (Module.finrank k F)) :
    Irreducible (p.map (algebraMap k F)) := by
  classical
  have hp0 : p ≠ 0 := hm.ne_zero
  have hdeg : (p.map (algebraMap k (AlgebraicClosure F))).degree ≠ 0 := by
    rw [degree_map]; exact (degree_pos_of_irreducible hp).ne'
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root _ hdeg
  have hβ' : aeval β p = 0 := by rwa [aeval_def, ← eval_map]
  have hint : IsIntegral k β := ⟨p, hm, by rwa [← aeval_def]⟩
  have hmin : minpoly k β = p := (minpoly.eq_of_irreducible_of_monic hp hβ' hm).symm
  have hintF : IsIntegral F β := hint.tower_top
  have hqdvd : minpoly F β ∣ p.map (algebraMap k F) := by
    have := minpoly.dvd_map_of_isScalarTower k F β
    rwa [hmin] at this
  have hpF0 : p.map (algebraMap k F) ≠ 0 := Polynomial.map_ne_zero hp0
  have hqm : (minpoly F β).Monic := minpoly.monic hintF
  have hqle : (minpoly F β).natDegree ≤ p.natDegree := by
    have := hqm.natDegree_le_of_dvd hpF0 hqdvd
    rwa [natDegree_map] at this
  have h2 : finrank k F⟮β⟯ = finrank k F * (minpoly F β).natDegree := by
    rw [← adjoin.finrank hintF, Module.finrank_mul_finrank k F F⟮β⟯]
  -- inside `F⟮β⟯`, the generator spans a degree-`n` subfield over `k`, so `n ∣ m · d`
  have hβ'p : aeval (AdjoinSimple.gen F β) p = 0 := by
    rw [← Polynomial.aeval_map_algebraMap F]
    exact Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hqdvd (aeval_gen_minpoly F β)
  have hβ'int : IsIntegral k (AdjoinSimple.gen F β) := ⟨p, hm, by rwa [← aeval_def]⟩
  have hmin' : minpoly k (AdjoinSimple.gen F β) = p :=
    (minpoly.eq_of_irreducible_of_monic hp hβ'p hm).symm
  have h3 : finrank k k⟮AdjoinSimple.gen F β⟯ ∣ finrank k F⟮β⟯ := by
    have := finrank_dvd_of_le_right (le_top : k⟮AdjoinSimple.gen F β⟯ ≤ ⊤)
    rwa [finrank_top'] at this
  rw [adjoin.finrank hβ'int, hmin', h2] at h3
  have h5 : p.natDegree ∣ (minpoly F β).natDegree := hcop.dvd_of_dvd_mul_left h3
  have hqpos : 0 < (minpoly F β).natDegree := minpoly.natDegree_pos hintF
  have hqeq : (minpoly F β).natDegree = p.natDegree :=
    le_antisymm hqle (Nat.le_of_dvd hqpos h5)
  have hmF : (p.map (algebraMap k F)).Monic := hm.map _
  have hd : (p.map (algebraMap k F)).natDegree ≤ (minpoly F β).natDegree := by
    rw [natDegree_map, hqeq]
  rw [Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hmF hqdvd hd]
  exact minpoly.irreducible hintF

/-- Two `ℚ`-algebra structures on a semiring coincide (the bridge between
`DivisionRing.toRatAlgebra` and `AdjoinRoot.instAlgebra`). -/
theorem algebraRat_eq {A : Type*} [Semiring A] (P Q : Algebra ℚ A) : P = Q :=
  Algebra.algebra_ext P Q fun r =>
    congrArg (fun f : ℚ →+* A => f r)
      (RingHom.ext_rat (@algebraMap ℚ A _ _ P) (@algebraMap ℚ A _ _ Q))

open Port014 in
/-- `X³ − X − 1` is irreducible over `ℚ` (from the port of 000014). -/
instance : Fact (Irreducible fρ) := ⟨cubicQ_irreducible⟩

/-- The cubic field `K₃ = ℚ[X]/(X³ − X − 1)` (the base of the tower). -/
abbrev K₃ := AdjoinRoot Port014.fρ

theorem finrank_K₃ : Module.finrank ℚ K₃ = 3 := by
  have h := (AdjoinRoot.powerBasis' Port014.fρ_monic).finrank
  rw [AdjoinRoot.powerBasis'_dim, Port014.fρ_natDegree] at h
  convert h

/-- The quartic `Y⁴ − Y − 1` read over the cubic field. -/
noncomputable def g : K₃[X] := Port014.fQ.map (algebraMap ℚ K₃)

theorem g_monic : g.Monic := Port014.fQ_monic.map _

/-- **Irreducibility over the cubic field**: `Y⁴ − Y − 1` stays irreducible over the cubic field (degrees `3` and
`4` are coprime). -/
theorem g_irreducible : Irreducible g :=
  irreducible_map_of_coprime_finrank Port014.quarticQ_irreducible Port014.fQ_monic
    (by rw [Port014.fQ_natDegree, finrank_K₃]; decide)

instance : Fact (Irreducible g) := ⟨g_irreducible⟩

/-- The degree-12 field `L = K₃[Y]/(Y⁴ − Y − 1)`. -/
abbrev L := AdjoinRoot g

instance : Module.Finite K₃ L := g_monic.finite_adjoinRoot

instance : NumberField L := NumberField.of_module_finite K₃ L

/-- `ρ ∈ L`: the image of the cubic root. -/
noncomputable abbrev ρ : L := algebraMap K₃ L (AdjoinRoot.root Port014.fρ)

/-- `Q ∈ L`: the quartic root. -/
noncomputable abbrev Q : L := AdjoinRoot.root g

theorem aeval_ρ : aeval ρ Port014.fρ = 0 := by
  have h := AdjoinRoot.aeval_eq (f := Port014.fρ) Port014.fρ
  rw [AdjoinRoot.mk_self] at h
  have h2 := congrArg (algebraMap K₃ L) h
  rw [map_zero] at h2
  rw [Polynomial.aeval_algebraMap_apply]
  convert h2 <;> exact algebraRat_eq _ _

theorem aeval_Q : aeval Q Port014.fQ = 0 := by
  rw [← Polynomial.aeval_map_algebraMap K₃, ← g, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem g_natDegree : g.natDegree = 4 := by
  rw [g, natDegree_map, Port014.fQ_natDegree]

theorem finrank_K₃_L : Module.finrank K₃ L = 4 := by
  rw [(AdjoinRoot.powerBasis' g_monic).finrank, AdjoinRoot.powerBasis'_dim, g_natDegree]

/-- `[L : ℚ] = 12`. -/
theorem finrank_L : Module.finrank ℚ L = 12 := by
  rw [← Module.finrank_mul_finrank ℚ K₃ L, finrank_K₃, finrank_K₃_L]

end HermiteCompositum.Instance
