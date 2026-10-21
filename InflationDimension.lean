module
public import Mathlib
public import InflationDimension.Defs
public import InflationDimension.Admissibility
public import InflationDimension.Normal
public import InflationDimension.Count
public import InflationDimension.Hyperbolic
public import InflationDimension.DimOne
public import InflationDimension.JordanData
public import InflationDimension.Tilt
public import InflationDimension.FormulaA
public import InflationDimension.Compositum.Tower
public import InflationDimension.Compositum.CircleFree
public import InflationDimension.Instances
public import InflationDimension.ModelSetQ
public import InflationDimension.Meyer

@[expose] public section
/-!
# The least physical dimension of an inflation-symmetric model set

Index of the library. The compared statements are in `Challenge.lean`; `Solution.lean` proves
each of them by one application of the theorem of the same name in namespace
`InflationDimension`.

* `InflationDimension.Defs` — the definitions the compared statements use; the same text as the
  shared block of `Challenge.lean`, so that the Challenge imports Mathlib only.
* `InflationDimension.Admissibility` — statements (1) and (2): the admissibility criterion and
  Kronecker's density criterion in cut-and-project form.
* `InflationDimension.Normal` — the normal form and the characterization of admissible splittings
  when `χ_A` is squarefree (part of statement (3)), and the rational kernel lemma.
* `InflationDimension.Count` — the least physical dimension when `χ_A` is squarefree (part of
  statement (3)).
* `InflationDimension.Hyperbolic` — statement (4): the hyperbolic case.
* `InflationDimension.DimOne` — the squarefree forms of statements (5) and (6), the `ℤ²` examples
  of (7), and statement (12).
* `InflationDimension.JordanData` — Jordan data from rational ranks, and the largest power-bounded
  invariant summand.
* `InflationDimension.Tilt` — a single cyclotomic factor: the semisimple collapse, the tilt, and the
  examples `1 ⊕ J₂(1)`, `1 ⊕ J₃(1)` of (7).
* `InflationDimension.FormulaA` — statement (3) for every nonsingular `A`, and statements (5), (6)
  and (7).
* `InflationDimension.Compositum.Tower`, `InflationDimension.Compositum.CircleFree` — the
  degree-12 field and its circle-freeness, ported from the author's registered entry
  PALOMAR-2026-10-21-000012 (stalex444/pdt-hermite-signature-compositum@5aa870e98236ba240561b798265c629df8c2d031),
  in the namespaces `InflationDimension.Compositum` and `InflationDimension.Compositum.Instance`.
* `InflationDimension.Instances` — statements (8), (9) and (10).
* `InflationDimension.ModelSetQ` — statement (11).
* `InflationDimension.Meyer` — statement (13).
-/
