# Imported Mathlib definitions

The compared statements in `Challenge.lean` rest on the Mathlib definitions below. The remaining vocabulary is standard Mathlib and is not quoted: `Submodule`, `Submodule.span`, `Submodule.subtype`, `IsCompl`, `LinearMap.ker`, `LinearMap.id`, `Module.finrank`, `Polynomial.aeval`, `Polynomial.map`, `Polynomial.natDegree`, `Polynomial.X`, `Int.castRingHom`, `algebraMap`, `Irreducible`, `Multiset.filter`/`card`/`map`/`sum`/`toFinset`, `Finset.sum`, `IsUnit`, `min`, natural-number subtraction and division, `Fintype.card`, `Pi.single`, `Set.MapsTo`, `Set.image`, `closure`, `Metric.ball`, `Bornology.IsBounded`, `IsCompact`, `Convex`, `Filter.Tendsto` and `nhds`, the pointwise difference of sets, `Complex.re`/`im` and the norm on `ℂ`, `Matrix.map`, `Matrix.of` (`!![…]`), and the ring, field and order structures. Each excerpt is copied verbatim from Mathlib at the pinned revision `065356127b1dc0016f66b7283ce0ce2c4055aa55` (the revision required in `lakefile.toml` and recorded in `lake-manifest.json`), with its file path, line numbers and a permalink; every excerpt was byte-compared against `raw.githubusercontent.com` at that revision when this file was generated. Mathlib is released under the Apache 2.0 license; copyright of these excerpts remains with the Mathlib authors named in each file's header.

The entry's own definitions (`intLattice`, `act`, `InvariantCPS` and its projections, windows, model sets, admissibility and orbit window, `physDims`, `eigenvalues`, `unstableCount`, `IsHyperbolic`, `stableSet`, `unstableSet`, `charpolyQ`, `IsCircleFactor`, `circleCount`, the Jordan data `factorMult`, `kerRankQ`, `sizeOneBlocks`, `expandingRootCount`, `circleRootCount`, `factorContribution` and `dimensionFormula`, the matrices `Cρ`, `CQ`, `CSalem`, `mulMatrix`, `mulρ`, `mulQ`, `mulθ`, `mulρQ`, `GramRho`, `GramQ`, and `formOf`, `pairing`, `sectorQ`, `sectorRho`) are stated in `Challenge.lean` itself, between the lines `-- BEGIN SHARED DEFINITIONS` and `-- END SHARED DEFINITIONS` (the same text as `InflationDimension/Defs.lean`, on which the proof modules are built), and are described in its opening docstring.

The file `DefinitionAudit.lean` in this repository is built with the package (it is a default target) and checks, as theorems, the facts about these definitions that the informal account relies on. It is not part of the compared set and imports Mathlib only. All its theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound` (see `BUILD.txt`).

## 1. `Matrix.toLin'`: a matrix as a linear map

`Mathlib/LinearAlgebra/Matrix/ToLin.lean`, lines 383–387: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/ToLin.lean#L383-L387>

```lean
/-- A `Matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`.

Note that the forward-direction does not require `DecidableEq` and is `Matrix.mulVecLin`. -/
def Matrix.toLin' : Matrix m n R ≃ₗ[R] (n → R) →ₗ[R] m → R :=
  LinearMap.toMatrix'.symm
```

The entry's `act A` is `Matrix.toLin' (A.map Int.cast)`, the action of the integer matrix `A` on `ℝ^ι`. Kernel-checked: `DefinitionAudit.toLin'_apply` (`Matrix.toLin' M v = M *ᵥ v`) and `DefinitionAudit.toLin'_single` (the image of the `j`-th standard basis vector is the `j`-th column).

## 2. `Pi.basisFun`: the standard basis

`Mathlib/LinearAlgebra/StdBasis.lean`, lines 121–123: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/StdBasis.lean#L121-L123>

```lean
/-- The basis on `η → R` where the `i`th basis vector is `Function.update 0 i 1`. -/
noncomputable def basisFun : Basis η R (η → R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)
```

The entry's `intLattice ι` is the `ℤ`-span of `Set.range (Pi.basisFun ℝ ι)`. Kernel-checked: `DefinitionAudit.mem_span_basisFun_iff` (that span is the set of vectors with integer coordinates, i.e. `ℤ^ι`).

## 3. `Submodule.projectionOnto`: projection along a complement

`Mathlib/LinearAlgebra/Projection.lean`, lines 117–127: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Projection.lean#L117-L127>

```lean
/-- Projection to a submodule along a complement. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.

For the projection from `E` to `E`, see `Submodule.projection`. See also:
* `Submodule.projectionOntoL` and `Submodule.projectionL` for the continuous versions.
* `Submodule.orthogonalProjection` and `Submodule.orthogonalProjectionOnto` for the projections
  along the orthogonal subspace.

See also `LinearMap.linearProjOfIsCompl`. -/
def projectionOnto (h : IsCompl p q) : E →ₗ[R] p :=
  LinearMap.fst R p q ∘ₗ ↑(prodEquivOfIsCompl p q h).symm
```

Used through `Submodule.projection` below.

## 4. `Submodule.projection`: the projection as an endomorphism

`Mathlib/LinearAlgebra/Projection.lean`, lines 129–139: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Projection.lean#L129-L139>

```lean
/-- The linear projection onto a subspace along its complement
as a map from the full space to itself, as opposed to `Submodule.projectionOnto`,
which maps into the subtype.
This version is important as it satisfies `IsIdempotentElem`.

See also:
* `Submodule.projectionOntoL` and `Submodule.projectionL` for the continuous versions.
* `Submodule.orthogonalProjection` and `Submodule.orthogonalProjectionOnto` for the projections
  along the orthogonal subspace. -/
noncomputable def projection (hpq : IsCompl p q) :=
  p.subtype ∘ₗ p.projectionOnto q hpq
```

`InvariantCPS.πE` is `S.E.projection S.H S.isCompl` and `πH` is `S.H.projection S.E S.isCompl.symm`; the density field of `InvariantCPS` and statement 2 use the same projection. Kernel-checked: `DefinitionAudit.projection_add_projection`, `projection_mem`, `projection_of_mem`, `projection_of_mem_compl` (`x = π_E x + π_H x`, `π_E x ∈ E`, `π_E` fixes `E` and kills `H`) and `DefinitionAudit.isCompl_iff`.

## 5. The sup norm on finite products

`Mathlib/Analysis/Normed/Group/Constructions.lean`, lines 301–308: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Normed/Group/Constructions.lean#L301-L308>

```lean
/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
instance Pi.seminormedGroup : SeminormedGroup (∀ i, G i) where
  norm f := ↑(Finset.univ.sup fun b => ‖f b‖₊)
  dist_eq x y :=
    congr_arg (toReal : ℝ≥0 → ℝ) <|
      congr_arg (Finset.sup Finset.univ) <| funext fun a =>
        show nndist (x a) (y a) = ‖(x a)⁻¹ * y a‖₊ from nndist_eq_nnnorm_inv_mul (x a) (y a)
```

The norm on `ι → ℝ` (the orbit window `W_*`, the power bounds of statement 1, the window balls and the Delone radii of statement 13) is the sup norm. Kernel-checked: `DefinitionAudit.norm_le_iff`.

## 6. `Matrix.charmatrix`

`Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`, lines 47–51: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean#L47-L51>

```lean
/-- The "characteristic matrix" of `M : Matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M
```

Used through `Matrix.charpoly` below.

## 7. `Matrix.charpoly`: the characteristic polynomial of a matrix

`Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`, lines 132–135: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean#L132-L135>

```lean
/-- The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$. -/
@[wikidata Q849705]
def charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det
```

`χ_A = det(X·1 − A)` over `ℤ`, monic. Used in `eigenvalues`, `charpolyQ` and statements 3, 5–9 and 12. Kernel-checked: `DefinitionAudit.charpoly_eq_det` (`rfl`), `DefinitionAudit.charpoly_fin_two` (the `2 × 2` formula, statement 7) and `DefinitionAudit.charpoly_map` (the complex eigenvalues of `A` are the roots of `χ_A` mapped to `ℂ`).

## 8. `LinearMap.charpoly`: the characteristic polynomial of an endomorphism

`Mathlib/LinearAlgebra/Charpoly/Basic.lean`, lines 43–45: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Charpoly/Basic.lean#L43-L45>

```lean
/-- The characteristic polynomial of `f : M →ₗ[R] M`. -/
def charpoly : R[X] :=
  (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly
```

The polynomials `q_E`, `q_H` of statements 1 and 3 are `LinearMap.charpoly` of the restrictions `(act A).restrict hE`, `(act A).restrict hH`. Kernel-checked: `DefinitionAudit.charpoly_toMatrix` (it is the characteristic polynomial of the matrix in any basis).

## 9. `LinearMap.restrict`

`Mathlib/Algebra/Module/Submodule/LinearMap.lean`, lines 208–211: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Module/Submodule/LinearMap.lean#L208-L211>

```lean
/-- Restrict domain and codomain of a linear map. -/
def restrict (f : M →ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂} (hf : ∀ x ∈ p, f x ∈ q) :
    p →ₛₗ[σ₁₂] q :=
  (f.domRestrict p).codRestrict q <| SetLike.forall.2 hf
```

The restriction of `act A` to an invariant subspace (statements 1, 3 and 11).

## 10. `Matrix.det`

`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`, lines 58–61: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean#L58-L61>

```lean
/-- The determinant of a matrix given by the Leibniz formula. -/
@[wikidata Q178546]
def det (M : Matrix n n R) : R :=
  detRowAlternating M
```

The hypothesis `A.det ≠ 0` of statements 3, 4 and 5, and `(mulMatrix a).det ≠ 0` in statement 9.

## 11. `LinearMap.det`

`Mathlib/LinearAlgebra/Determinant.lean`, lines 172–181: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Determinant.lean#L172-L181>

```lean
open scoped Classical in
-- Discourage the elaborator from unfolding `det` and producing a huge term by marking it
-- as irreducible.
/-- The determinant of an endomorphism independent of basis.

If there is no finite basis on `M`, the result is `1` instead.
-/
protected irreducible_def det : (M →ₗ[A] M) →* A :=
  if H : ∃ s : Finset M, Nonempty (Basis s A M) then LinearMap.detAux (Trunc.mk H.choose_spec.some)
  else 1
```

The determinant of `Q` on the physical space in statement 11. Kernel-checked: `DefinitionAudit.det_toMatrix` (it is the determinant of the matrix in any basis).

## 12. `Polynomial.roots`: roots with multiplicity

`Mathlib/Algebra/Polynomial/Roots.lean`, lines 56–61: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Roots.lean#L56-L61>

```lean
/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)
```

The entry's `eigenvalues A` is the root multiset of `χ_A` over `ℂ`; `unstableCount A` counts its elements of modulus `> 1` with multiplicity. Kernel-checked: `DefinitionAudit.roots_X_sub_C_sq` (`(X − 1)²` has roots `{1, 1}`).

## 13. `UniqueFactorizationMonoid.normalizedFactors`

`Mathlib/RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean`, lines 34–36: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean#L34-L36>

```lean
/-- Noncomputably determines the multiset of prime factors. -/
noncomputable def normalizedFactors (a : α) : Multiset α :=
  Multiset.map normalize <| factors a
```

The irreducible factors of `χ_A` over `ℚ` with multiplicity, in `circleCount`, `factorMult`, `dimensionFormula` and statements 3, 5 and 6. Kernel-checked: `DefinitionAudit.irreducible_of_mem_normalizedFactors`, `DefinitionAudit.monic_of_mem_normalizedFactors` and `DefinitionAudit.prod_normalizedFactors` (they are monic, irreducible, and multiply to the polynomial up to a unit).

## 14. `Multiset.countP`

`Mathlib/Data/Multiset/Count.lean`, lines 37–40: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Multiset/Count.lean#L37-L40>

```lean
/-- `countP p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
def countP (s : Multiset α) : ℕ :=
  Quot.liftOn s (List.countP p) fun _l₁ _l₂ => Perm.countP_eq (p ·)
```

The number of elements of a multiset satisfying a predicate, with multiplicity; `Multiset.count` is defined from it.

## 15. `Multiset.count`: multiplicity in a multiset

`Mathlib/Data/Multiset/Count.lean`, lines 122–124: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Multiset/Count.lean#L122-L124>

```lean
/-- `count a s` is the multiplicity of `a` in `s`. -/
def count (a : α) : Multiset α → ℕ :=
  countP (a = ·)
```

The multiplicity `m_p` of an irreducible factor `p` in `χ_A` (`factorMult`), in `dimensionFormula` and statement 3. Kernel-checked: `DefinitionAudit.count_replicate_self`.

## 16. `Polynomial.cyclotomic`

`Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean`, lines 229–232: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean#L229-L232>

```lean
/-- The `n`-th cyclotomic polynomial with coefficients in `R`. -/
def cyclotomic (n : ℕ) (R : Type*) [Ring R] : R[X] :=
  if h : n = 0 then 1
  else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.isPrimitiveRoot_exp n h)).choose
```

Statements 3 and 6. Kernel-checked: `DefinitionAudit.cyclotomic_one`, `DefinitionAudit.cyclotomic_two`.

## 17. `Squarefree`

`Mathlib/Algebra/Squarefree/Basic.lean`, lines 40–43: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Squarefree/Basic.lean#L40-L43>

```lean
/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x
```

The hypothesis of statements 3, 5 and 6, applied to `charpolyQ A`. Kernel-checked: `DefinitionAudit.squarefree_iff` (`Iff.rfl`).

## 18. `Matrix.kroneckerMap`

`Mathlib/LinearAlgebra/Matrix/Kronecker.lean`, lines 54–56: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/Kronecker.lean#L54-L56>

```lean
/-- Produce a matrix with `f` applied to every pair of elements from `A` and `B`. -/
def kroneckerMap (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) : Matrix (l × n) (m × p) γ :=
  of fun (i : l × n) (j : m × p) => f (A i.1 j.1) (B i.2 j.2)
```

Used through the notation `⊗ₖ` below.

## 19. The Kronecker product `⊗ₖ`

`Mathlib/LinearAlgebra/Matrix/Kronecker.lean`, lines 271–278: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/Kronecker.lean#L271-L278>

```lean
/-- The Kronecker product. This is just a shorthand for `kroneckerMap (*)`. Prefer the notation
`⊗ₖ` rather than this definition. -/
@[simp]
def kronecker [Mul α] : Matrix l m α → Matrix n p α → Matrix (l × n) (m × p) α :=
  kroneckerMap (· * ·)

@[inherit_doc Matrix.kroneckerMap]
scoped[Kronecker] infixl:100 " ⊗ₖ " => Matrix.kroneckerMap (· * ·)
```

The matrices `mulMatrix`, `mulρ`, `mulQ`, `mulθ`, `mulρQ` and the Gram matrix `GramRho ⊗ₖ GramQ` of statement 10. Kernel-checked: `DefinitionAudit.kronecker_apply` (`(A ⊗ₖ B)_{(i,k),(j,l)} = A_{ij} B_{kl}`, `rfl`).

## 20. `dotProduct`

`Mathlib/Data/Matrix/Mul.lean`, lines 69–73: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Matrix/Mul.lean#L69-L73>

```lean
/-- `dotProduct v w` is the sum of the entrywise products `v i * w i`.

See also `dotProductEquiv`. -/
def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
  ∑ i, v i * w i
```

Used in the entry's `pairing`.

## 21. `Matrix.mulVec`

`Mathlib/Data/Matrix/Mul.lean`, lines 691–699: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Data/Matrix/Mul.lean#L691-L699>

```lean
/--
`M *ᵥ v` (notation for `mulVec M v`) is the matrix-vector product of matrix `M` and vector `v`,
where `v` is seen as a column vector.

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `dotProduct`,
so that `A *ᵥ v ⬝ᵥ B *ᵥ w` is parsed as `(A *ᵥ v) ⬝ᵥ (B *ᵥ w)`.
-/
def mulVec [Fintype n] (M : Matrix m n α) (v : n → α) : m → α
  | i => (fun j => M i j) ⬝ᵥ v
```

Used in the entry's `pairing`. Kernel-checked: `DefinitionAudit.dotProduct_mulVec` (`x ⬝ᵥ (M *ᵥ y) = Σ_{i,j} x_i M_{ij} y_j`).

## 22. `LinearMap.BilinMap.toQuadraticMap`

`Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`, lines 675–679: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean#L675-L679>

```lean
/-- A bilinear map gives a quadratic map by applying the argument twice. -/
def toQuadraticMap (B : BilinMap R M N) : QuadraticMap R M N where
  toFun x := B x x
  toFun_smul a x := by simp only [map_smul, LinearMap.smul_apply, smul_smul]
  exists_companion' := ⟨B + LinearMap.flip B, fun x y => by simp [add_add_add_comm, add_comm]⟩
```

Used through `Matrix.toQuadraticForm'` below.

## 23. `Matrix.toQuadraticForm'`

`Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`, lines 1164–1166: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean#L1164-L1166>

```lean
/-- `M.toQuadraticForm'` is the map `fun x ↦ row x * M * col x` as a quadratic form on `n → R`. -/
def Matrix.toQuadraticForm' (M : Matrix n n R) : QuadraticForm R (n → R) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' R M)
```

The entry's `formOf G` is `(G.map Int.cast).toQuadraticForm'`. Kernel-checked: `DefinitionAudit.toQuadraticForm'_apply` (`c ↦ Σ_{i,j} M_{ij} c_i c_j`).

## 24. `QuadraticMap.comp`

`Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`, lines 540–546: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean#L540-L546>

```lean
/-- Compose the quadratic map with a linear function on the right. -/
def comp (Q : QuadraticMap R N P) (f : M →ₗ[R] N) : QuadraticMap R M P where
  toFun x := Q (f x)
  toFun_smul a x := by simp only [Q.map_smul, map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compl₁₂ f f, fun x y => by simp_rw [f.map_add]; exact h (f x) (f y)⟩
```

The restriction of `formOf GramQ` to a subspace, as `(formOf GramQ).comp S.E.subtype`, in statement 11.

## 25. `sigPos`: the positive index of inertia

`Mathlib/LinearAlgebra/QuadraticForm/Signature.lean`, lines 58–71: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/QuadraticForm/Signature.lean#L58-L71>

```lean
open scoped Classical in
/-- For quadratic forms on finite-dimensional spaces, the maximal finrank of a positive-definite
subspace of `M`. (Defined as `0` if `M` is infinite-dimensional). -/
/-
Note the proof of nonemptiness needed for `max'` is a little fiddly since we are not assuming
`Nontrivial R`, and the `⊥` submodule of a module over the zero ring has finrank 1, not 0.
-/
def sigPos : ℕ := max' {r ∈ Iic (Module.finrank R M) |
    ∃ V : Submodule R M, Module.finrank R V = r ∧ (Q.restrict V).PosDef}
  ⟨Module.finrank R (⊥ : Submodule R M), by
    simp only [mem_filter, mem_Iic]
    refine ⟨?_, ⟨⊥, rfl, fun x hx' ↦ (hx' <| Subsingleton.elim x 0).elim⟩⟩
    nontriviality R
    simp [finrank_bot]⟩
```

`sigPos Q` is the largest dimension of a subspace on which `Q` is positive definite (D. Loeffler's `Signature.lean`). Statements 10 and 11. Kernel-checked: `DefinitionAudit.sigPos_eq_card_pos_weights` (Sylvester's law: the number of positive weights of any diagonalization) and `DefinitionAudit.sigPos_x_sq_sub_y_sq` (non-vacuity).

## 26. `sigNeg`: the negative index of inertia

`Mathlib/LinearAlgebra/QuadraticForm/Signature.lean`, lines 96–98: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/QuadraticForm/Signature.lean#L96-L98>

```lean
/-- For quadratic forms on finite-dimensional spaces, the maximal finrank of a negative-definite
subspace of `M`. (Defined as `0` if `M` is infinite-dimensional). -/
def sigNeg : ℕ := sigPos (-Q)
```

Kernel-checked: `DefinitionAudit.sigNeg_eq_sigPos_neg`, `DefinitionAudit.sigNeg_eq_card_neg_weights` and `DefinitionAudit.sigNeg_x_sq_sub_y_sq`.

## 27. `Delone.DeloneSet`

`Mathlib/Analysis/AperiodicOrder/Delone/Basic.lean`, lines 63–76: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/AperiodicOrder/Delone/Basic.lean#L63-L76>

```lean
/-- A **Delone set** consists of a set together with explicit radii
witnessing uniform discreteness and relative denseness. -/
@[ext]
structure DeloneSet (X : Type*) [MetricSpace X] where
  /-- The underlying set. -/
  carrier : Set X
  /-- Radius such that distinct points of `carrier` are separated by more than `r`. -/
  packingRadius : ℝ≥0
  packingRadius_pos : 0 < packingRadius
  isSeparated_packingRadius : IsSeparated packingRadius carrier
  /-- Radius such that every point of the space is within `R` of `carrier`. -/
  coveringRadius : ℝ≥0
  coveringRadius_pos : 0 < coveringRadius
  isCover_coveringRadius : IsCover coveringRadius .univ carrier
```

Statement 13 (N. Jensen's `Delone/Basic.lean`). Kernel-checked: `DefinitionAudit.deloneSet_separated` (distinct points farther apart than the packing radius) and `DefinitionAudit.deloneSet_cover` (every point within the covering radius of the set).

## 28. `Metric.IsSeparated`

`Mathlib/Topology/MetricSpace/MetricSeparated.lean`, lines 42–44: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/MetricSeparated.lean#L42-L44>

```lean
/-- A set `s` is `ε`-separated if the extended distance between any two distinct
elements is strictly greater than `ε`. -/
def IsSeparated (ε : ℝ≥0∞) (s : Set X) : Prop := s.Pairwise (ε < edist · ·)
```

A field of `Delone.DeloneSet`.

## 29. `Metric.IsCover`

`Mathlib/Topology/MetricSpace/Cover.lean`, lines 42–48: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Topology/MetricSpace/Cover.lean#L42-L48>

```lean
/-- A set `N` is an *`ε`-cover* of a set `s` if every point of `s` lies at distance at most `ε` of
some point of `N`.

This is also called an *`ε`-net* in the literature.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.1. -/
def IsCover (ε : ℝ≥0) (s N : Set X) : Prop := SetRel.IsCover {(x, y) | edist x y ≤ ε} s N
```

A field of `Delone.DeloneSet`.

## 30. `segment`

`Mathlib/Analysis/Convex/Segment.lean`, lines 49–51: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Convex/Segment.lean#L49-L51>

```lean
/-- Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace. -/
def segment (x y : E) : Set E :=
  { z : E | ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • x + b • y = z }
```

Statement 11 (the window is a segment). Kernel-checked: `DefinitionAudit.segment_eq_image`.

## 31. `IsLeast`

`Mathlib/Order/Bounds/Defs.lean`, lines 43–46: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Order/Bounds/Defs.lean#L43-L46>

```lean
@[to_dual
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/]
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s
```

The least physical dimension: `IsLeast (physDims A) d`. Kernel-checked: `DefinitionAudit.isLeast_iff` (`Iff.rfl`).
