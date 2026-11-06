module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily

/-!
# The Čech differential squares to zero

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes, `𝔘 = (Uᵢ → U)_i`
a family of morphisms of `Et(S)` with target `U`, and `F` a presheaf on `Et(S)`. The Čech
differentials of `Č^•(𝔘, F)` satisfy `d^{p+1} ∘ d^p = 0` for every `p`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplex_d_comp_d`: `d^{p+1} ∘ d^p = 0`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplex_d_d_apply`: the same identity
  evaluated at a cochain, for presheaves of abelian groups.

## Implementation notes

The Čech complex is a `CochainComplex`, built from the alternating coface maps of a
cosimplicial object; the identity `d ∘ d = 0` is therefore part of the structure of a
homological complex (`HomologicalComplex.d_comp_d`). The cancellation of the terms indexed by
`(k, j)` and `(j, k - 1)` for `j < k` is the cosimplicial identity used in that construction.
The result is stated for any three indices `i, j, k`, which contains the case
`i = p, j = p + 1, k = p + 2`; for non-consecutive indices both differentials vanish.
For `p < 0` there is nothing to prove, the complex being indexed by `ℕ`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe a w v' u' u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : SmallNoetherianSeparatedEtale B S hS} (E : PreZeroHypercover.{w} U)

/-- **`d ∘ d = 0` for the Čech complex.** The composite of two successive Čech differentials
`d^{p+1} ∘ d^p` of `Č^•(𝔘, F)` vanishes. -/
@[weil "lem_fk102_cech_differential_square_zero"]
theorem cechComplex_d_comp_d {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
    [Preadditive A] (F : EtalePresheaf B S hS A) (i j k : ℕ) :
    (cechComplex E F).d i j ≫ (cechComplex E F).d j k = 0 :=
  HomologicalComplex.d_comp_d _ i j k

/-- **`d ∘ d = 0` on cochains.** For a presheaf of abelian groups `F` and a Čech cochain
`s ∈ Č^p(𝔘, F)`, `d^{p+1} (d^p s) = 0`. -/
theorem cechComplex_d_d_apply [HasProducts.{w} AddCommGrpCat.{a}]
    (F : EtalePresheaf B S hS AddCommGrpCat.{a}) (p : ℕ) (s : (cechComplex E F).X p) :
    (cechComplex E F).d (p + 1) (p + 2) ((cechComplex E F).d p (p + 1) s) = 0 := by
  rw [← ConcreteCategory.comp_apply, cechComplex_d_comp_d]
  rfl

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
