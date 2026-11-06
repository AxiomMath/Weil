module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafSecondMap

/-!
# The divisor map of a smooth curve is a morphism of sheaves

Let `X` be a smooth curve over a field `k`, `𝓡_X^*` the sheaf of invertible rational functions
on the étale site `Et(X)` and `𝒟_X` the sheaf of divisors. For `U ∈ Et(X)` and `f ∈ 𝓡_X^*(U)`,
let `div_U(f)` be the function on the closed points of `U` whose value at `u` is the order of
vanishing of `f` at `u`. This file proves that `div_U(f)` is a divisor on `U` (it has finite
support), and that the maps `div_U` form a morphism of sheaves of abelian groups
`div : 𝓡_X^* ⟶ 𝒟_X`, the unique one whose components are given by the orders of vanishing.

## Main results

* `SmallNoetherianSeparatedEtale.finite_setOf_etaleGenericFibreOrdOfPoint_ne_zero`: the order
  of vanishing of `f ∈ 𝓡_X^*(U)` is nonzero at only finitely many closed points of `U`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.etaleGenericFibreOrdOfPoint_map`: the order of
  vanishing is compatible with restriction: for `ψ : V ⟶ U` in `Et(X)` and `v ∈ V`, the order of
  `ψ^* f` at `v` is the order of `f` at `ψ(v)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.existsUnique_divisorMap`: there is a unique
  morphism of sheaves of abelian groups `𝓡_X^* ⟶ 𝒟_X` on `Et(X)` whose component over `U` sends
  `f` to the divisor `u ↦ ord_u(f)`; it is
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.curveDivisorMap`.

## Implementation notes

The order of vanishing at a point `u` of `U` is
`Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint`, computed in an integral open neighbourhood
of `u`; by `AlgebraicGeometry.curveDivisorMap_app_apply_closedPoint_eq_iff` at a closed point it
is the exponent `e` with `f_a ∈ t_u ^ e 𝒪_{U,u}^*`, which is the description of the source. The
compatibility with restriction holds at every point of `V`, not only at the closed ones.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.EtaleCohomology

universe u v

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
  (B : BigEtaleSite.{u}) (hX : B.Contains X)

include g in
/-- **The divisor of a rational function has finite support**: for `U ∈ Et(X)` and
`f ∈ 𝓡_X^*(U)`, the order of vanishing of `f` is nonzero at only finitely many closed points of
`U`, so `div_U(f)` is a divisor on `U`. -/
@[weil "lem_fk105_divisor_map_well_defined"]
theorem finite_setOf_etaleGenericFibreOrdOfPoint_ne_zero
    (U : SmallNoetherianSeparatedEtale B X hX)
    (a : Additive ((Γ(pullback
      ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).hom
        (genericPointInclusion X), ⊤))ˣ)) :
    haveI : IsNormal X := isNormal_of_isCurve_of_smooth g
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    haveI : IsLocallyNoetherian
        ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left :=
      isLocallyNoetherian_etale_left X _
    {y : closedPoints ((toScheme B X hX).obj U) |
      etaleGenericFibreOrdOfPoint _ y.1 a ≠ 0}.Finite := by
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : IsLocallyNoetherian
      ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left :=
    isLocallyNoetherian_etale_left X _
  have : CompactSpace ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left :=
    inferInstanceAs (CompactSpace ((toScheme B X hX).obj U))
  have : IsNoetherian ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left := {}
  exact (finite_support_etaleGenericFibreOrdOfPoint _ a).preimage Subtype.val_injective.injOn

include g in
/-- **The order of vanishing is compatible with restriction**: for a morphism `ψ : V ⟶ U` of
`Et(X)`, `f ∈ 𝓡_X^*(U)` and a point `v` of `V`, the order of vanishing of `ψ^* f` at `v` is the
order of vanishing of `f` at `ψ(v)`. -/
@[weil "lem_fk105_divisor_map_well_defined"]
theorem etaleGenericFibreOrdOfPoint_map {V U : SmallNoetherianSeparatedEtale B X hX} (ψ : V ⟶ U)
    (z : ULift.{max (u + 1) v} (Additive ((Γ(pullback
      ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).hom
        (genericPointInclusion X), ⊤))ˣ)))
    (y : (toScheme B X hX).obj V) :
    haveI : IsNormal X := isNormal_of_isCurve_of_smooth g
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    haveI : IsLocallyNoetherian
        ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj V)).left :=
      isLocallyNoetherian_etale_left X _
    haveI : IsLocallyNoetherian
        ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left :=
      isLocallyNoetherian_etale_left X _
    etaleGenericFibreOrdOfPoint
        ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj V)) y
        ((((((sheafEquivEtale B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
          ((genericPointDirectImage.{u, v} X).obj
            (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField)))).obj.map
              ψ.op).hom z : ULift.{max (u + 1) v} (Additive ((Γ(pullback
                ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj V)).hom
                  (genericPointInclusion X), ⊤))ˣ)))).down) =
      etaleGenericFibreOrdOfPoint
        ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U))
        ((toScheme B X hX).map ψ y) z.down := by
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : IsLocallyNoetherian
      ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj V)).left :=
    isLocallyNoetherian_etale_left X _
  have : IsLocallyNoetherian
      ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left :=
    isLocallyNoetherian_etale_left X _
  set φ := (SmallEtale.toEtaleSite B X hX).map ((inclusion B X hX).map ψ)
  have h := genericPointDirectImage_multiplicativeSheaf_map_down.{u, v} X φ z
  change etaleGenericFibreOrdOfPoint _ y
      (((((genericPointDirectImage.{u, v} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.map
          φ.op).hom z).down) = _
  rw [h, smallEtaleBaseChange_map_left_eq_etaleGenericFibreMap φ]
  exact etaleGenericFibreOrdOfPoint_appTop φ y (Additive.toMul z.down)

/-- **The divisor map is a morphism of sheaves** (FK I.5): there is a unique morphism of sheaves
of abelian groups `div : 𝓡_X^* ⟶ 𝒟_X` on `Et(X)` whose component over every `U ∈ Et(X)` sends
`f ∈ 𝓡_X^*(U)` to the divisor `div_U(f)`, whose value at a closed point `u` of `U` is the order of
vanishing of `f` at `u`. It is `AlgebraicGeometry.SmallNoetherianSeparatedEtale.curveDivisorMap`. -/
@[weil "lem_fk105_divisor_map_well_defined"]
theorem existsUnique_divisorMap :
    haveI : IsNormal X := isNormal_of_isCurve_of_smooth g
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
    ∃! φ : (sheafEquivEtale B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
        ((genericPointDirectImage.{u, v} X).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))) ⟶
        divisorSheaf.{u, v} B X hX,
      ∀ (U : SmallNoetherianSeparatedEtale B X hX)
        (z : ULift.{max (u + 1) v} (Additive ((Γ(pullback
          ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).hom
            (genericPointInclusion X), ⊤))ˣ)))
        (y : closedPoints ((toScheme B X hX).obj U)),
        haveI : IsLocallyNoetherian
            ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left :=
          isLocallyNoetherian_etale_left X _
        divisorSheafSectionsAddEquiv.{u, v} U ((φ.hom.app (op U)).hom z) y =
          etaleGenericFibreOrdOfPoint _ y.1 z.down := by
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  refine ⟨curveDivisorMap.{u, v} g B hX, fun U z y =>
    curveDivisorMap_app_apply_closedPoint.{u, v} g B hX U z y, fun φ hφ => ?_⟩
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  induction U using Opposite.rec with | op U => ?_
  refine AddCommGrpCat.ext fun z => (divisorSheafSectionsAddEquiv.{u, v} U).injective ?_
  refine Finsupp.ext fun y => ?_
  exact (hφ U z y).trans (curveDivisorMap_app_apply_closedPoint.{u, v} g B hX U z y).symm

end AlgebraicGeometry.SmallNoetherianSeparatedEtale
