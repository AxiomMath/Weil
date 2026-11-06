module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafSecondMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorMiddleExactness

/-!
# The divisor exact sequence of a smooth curve

Let `X` be a smooth curve over a field `k`, with function field `K` and generic point
`j : Spec K ⟶ X`. The sequence of abelian étale sheaves

`0 → 𝒪_X^* → 𝓡_X^* → 𝒟_X → 0`,

where `𝓡_X^* = j_* 𝐆_{m,K}` is the sheaf of invertible rational functions, the first map is the
canonical inclusion and the second is the divisor map `div`, is short exact.

## Main results

* `AlgebraicGeometry.shortExact_curveDivisorSequence`: the sequence is short exact on Mathlib's
  small étale site `X.Etale`.
* `AlgebraicGeometry.SmallEtale.shortExact_curveDivisorSequence`: the sequence
  `0 → 𝐆_{m,X} → 𝓡_X^* → 𝒟_X → 0` is short exact on the small étale site `SmallEtale B X hX`
  of a big étale site `B` containing `X`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.shortExact_curveDivisorSequence`: the
  sequence is short exact in the category of abelian sheaves on the étale site `Et(X)` of
  noetherian separated étale `X`-schemes.

## Implementation notes

A curve is an integral separated scheme of finite type and dimension one over `k`
(`AlgebraicGeometry.IsCurve`); the divisor map `AlgebraicGeometry.curveDivisorMap` is defined for
such curves. The sequence is the fundamental exact sequence of Stacks 03RI,
`Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve`, on `X.Etale`; the other two forms
are its images under the inverses of the equivalences of sheaf categories
`AlgebraicGeometry.SmallEtale.sheafEquiv` and
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquivEtale`, which are exact functors.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]

/-- **The divisor exact sequence on `X.Etale`**: for a smooth curve `X` over a field, the
sequence `0 → 𝐆_{m,X} → j_* 𝐆_{m,K} → 𝒟_X → 0`, with the canonical map and the divisor map
`AlgebraicGeometry.curveDivisorMap`, is a short exact sequence of abelian étale sheaves. -/
@[weil "lem_fk105_divisor_exact_sequence"]
theorem shortExact_curveDivisorSequence :
    (ShortComplex.mk
      (multiplicativeDirectImageComparison.{u, u + 1} (genericPointInclusion X))
      (curveDivisorMap.{u, u + 1} g)
      (multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve.{u, u + 1}
        g)).ShortExact :=
  shortExact_divisorSequenceOfCurve g

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (hX : B.Contains X)

/-- The composite `𝐆_{m,X} → 𝓡_X^* → 𝒟_X` on `SmallEtale B X hX` vanishes. -/
theorem toRationalFunctionUnits_comp_curveDivisorMap :
    toRationalFunctionUnits.{u, u + 1} B X hX ≫ SmallEtale.curveDivisorMap.{u, u + 1} g B hX =
      0 :=
  ((ShortComplex.mk _ _
    (multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve.{u, u + 1}
      g)).map (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse).zero

/-- **The divisor exact sequence on the small étale site of a big étale site**: for a smooth
curve `X` over a field, the sequence `0 → 𝐆_{m,X} → 𝓡_X^* → 𝒟_X → 0`, with the canonical map
`AlgebraicGeometry.SmallEtale.toRationalFunctionUnits` and the divisor map
`AlgebraicGeometry.SmallEtale.curveDivisorMap`, is a short exact sequence of abelian sheaves on
`SmallEtale B X hX`. -/
@[weil "lem_fk105_divisor_exact_sequence"]
theorem shortExact_curveDivisorSequence :
    (ShortComplex.mk _ _ (toRationalFunctionUnits_comp_curveDivisorMap g B hX)).ShortExact :=
  (shortExact_divisorSequenceOfCurve g).map_of_exact
    (sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse

end SmallEtale

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (hX : B.Contains X)

/-- **The canonical map `𝒪_X^* ⟶ 𝓡_X^*` on `Et(X)`**: an invertible function on `U` is pulled
back to an invertible function on the generic fibre `U ×_X Spec K`. -/
abbrev toRationalFunctionUnits :
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    (sheafEquivEtale B X hX AddCommGrpCat.{u + 1}).inverse.obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) ⟶
      (sheafEquivEtale B X hX AddCommGrpCat.{u + 1}).inverse.obj
        ((genericPointDirectImage.{u, u + 1} X).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField))) :=
  haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  (sheafEquivEtale B X hX AddCommGrpCat.{u + 1}).inverse.map
    (multiplicativeDirectImageComparison.{u, u + 1} (genericPointInclusion X))

/-- The composite `𝒪_X^* → 𝓡_X^* → 𝒟_X` on `Et(X)` vanishes. -/
theorem toRationalFunctionUnits_comp_curveDivisorMap :
    toRationalFunctionUnits g B hX ≫
        SmallNoetherianSeparatedEtale.curveDivisorMap.{u, u + 1} g B hX = 0 :=
  haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  ((ShortComplex.mk _ _
    (multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve.{u, u + 1}
      g)).map (sheafEquivEtale B X hX AddCommGrpCat.{u + 1}).inverse).zero

/-- **The divisor exact sequence on `Et(X)`**: for a smooth curve `X` over a field, the sequence
`0 → 𝒪_X^* → 𝓡_X^* → 𝒟_X → 0`, with the canonical map and the divisor map
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.curveDivisorMap` into the sheaf of divisors
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorSheaf`, is a short exact sequence of
abelian sheaves on the étale site of noetherian separated étale `X`-schemes. -/
@[weil "lem_fk105_divisor_exact_sequence"]
theorem shortExact_curveDivisorSequence :
    (ShortComplex.mk _ _ (toRationalFunctionUnits_comp_curveDivisorMap g B hX)).ShortExact :=
  haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  (shortExact_divisorSequenceOfCurve g).map_of_exact
    (sheafEquivEtale B X hX AddCommGrpCat.{u + 1}).inverse

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry
