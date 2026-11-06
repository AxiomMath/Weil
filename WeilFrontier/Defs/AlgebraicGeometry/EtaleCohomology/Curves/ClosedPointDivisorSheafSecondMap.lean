module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafSecondMap

/-!
# The divisor map of a smooth curve on the étale site

Let `X` be a smooth curve over a field `k`, with function field `K`, generic point
`j : Spec K ⟶ X` and set of closed points `X_0`. For an étale `X`-scheme `U` the sections of
`𝓡_X^* = j_* 𝔾_{m,K}` over `U` are the invertible functions on the generic fibre `U ×_X Spec K`,
and the sections of the sheaf of divisors `𝒟_X = ⨁_{x ∈ X_0} i_{x,*} ℤ` over `U` are the
divisors on `U`, the finitely supported `ℤ`-valued functions on the closed points of `U`
(`AlgebraicGeometry.Scheme.Etale.closedPointDivisorSheafSectionsAddEquiv`). The *divisor map*
`div : 𝓡_X^* ⟶ 𝒟_X` sends `f ∈ 𝓡_X^*(U)` to the divisor `div_U(f)` whose value at a closed
point `u` of `U` is the order of vanishing of `f` at `u`, and which vanishes at the points of `U`
that are not closed.

## Main definitions

* `AlgebraicGeometry.curveDivisorMap`: the divisor map `𝓡_X^* ⟶ 𝒟_X`, a morphism of sheaves of
  abelian groups on the small étale site `X.Etale`; it is the second map
  `Stacks.EtaleCohomology.divisorSequenceSecondMapOfCurve` of the fundamental exact sequence
  `0 → 𝔾_m → j_* 𝔾_{m,K} → ⨁_x i_{x,*} ℤ → 0`.
* `AlgebraicGeometry.SmallEtale.curveDivisorMap`: the same morphism on the small étale site
  `AlgebraicGeometry.SmallEtale B X hX` of a big étale site.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.curveDivisorMap`: the same morphism on the
  étale site `Et(X)` of noetherian separated étale `X`-schemes, with target the sheaf of divisors
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorSheaf`.

## Main results

* `AlgebraicGeometry.curveDivisorMap_app_apply`: over an étale `X`-scheme `U` with noetherian
  underlying space, `div_U(f)` is the family of orders of vanishing
  `Stacks.EtaleCohomology.closedPointDivisorSheafSection U f`.
* `AlgebraicGeometry.curveDivisorMap_app_apply_closedPoint`: for `U` quasi-compact and
  quasi-separated, the value of the divisor `div_U(f)` at a closed point `u` of `U` is the order
  of vanishing `Stacks.EtaleCohomology.etaleGenericFibreOrdOfPoint U u f` of `f` at `u`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.curveDivisorMap_app_apply_closedPoint`: the
  same formula on `Et(X)`.

## Implementation notes

The order of vanishing of `f` at a point `u` of `U` is computed in an integral open neighbourhood
`W` of `u` in `U` (every point of a scheme étale over a normal integral scheme has one): it is
Mathlib's order of vanishing `AlgebraicGeometry.Scheme.ord` at `u` of the image of `f` in the
function field of `W`. Since the local ring `𝒪_{U,u}` at a closed point is a discrete valuation
ring with fraction field the function field of `W`, this is the order of `f` along
`𝒪_{U,u} → K(W)` in the sense of `IsLocalRing.ordAlong`
(`AlgebraicGeometry.Scheme.ordAlong_algebraMap_stalk_functionField`). The order of a unit is an
integer, so the divisor takes values in `ℤ` rather than in `ℤ ∪ {±∞}`.

The value `0` at the non-closed points is built into the target: a section of `𝒟_X` is a
divisor supported on the closed points.

The morphism is constructed on Mathlib's small étale site, where the fundamental exact sequence
is proved; the forms on the small étale site of a big étale site and on `Et(X)` are its images
under the restriction equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv` and
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquivEtale`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Stacks.EtaleCohomology

universe u v

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]

/-- **The divisor map** `div : 𝓡_X^* ⟶ 𝒟_X` of a smooth curve `X` over a field, on the small
étale site of `X`: an invertible function `f` on the generic fibre of an étale `X`-scheme `U` is
sent to its divisor `div_U(f)`, the family of its orders of vanishing at the closed points of
`U`. -/
@[weil "def_fk105_divisor_map"]
abbrev curveDivisorMap :
    (genericPointDirectImage.{u, v} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField)) ⟶
      closedPointDivisorSheaf.{u, v} X :=
  divisorSequenceSecondMapOfCurve.{u, v} g

/-- **The divisor map on sections**: over an étale `X`-scheme `U` with noetherian underlying
space, the divisor of `f` is the family of orders of vanishing of `f`. -/
theorem curveDivisorMap_app_apply (U : X.Etale) [NoetherianSpace U.left]
    (z : ULift.{max (u + 1) v} (Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ))) :
    haveI : IsNormal X := isNormal_of_isCurve_of_smooth g
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    haveI : IsLocallyNoetherian U.left := isLocallyNoetherian_etale_left X U
    ((curveDivisorMap.{u, v} g).hom.app (op U)).hom z =
      closedPointDivisorSheafSection.{u, v} U z.down := by
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : IsLocallyNoetherian U.left := isLocallyNoetherian_etale_left X U
  refine Functor.IsCoverDense.ext (Scheme.AffineEtale.Spec X)
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v})).obj
      (closedPointDivisorSheaf.{u, v} X)) U fun W φ => ?_
  have : NoetherianSpace ((Scheme.AffineEtale.Spec X).obj W).left :=
    noetherianSpace_affineEtale_left X W
  have : IsLocallyNoetherian ((Scheme.AffineEtale.Spec X).obj W).left :=
    isLocallyNoetherian_etale_left X _
  change ((closedPointDivisorSheaf.{u, v} X).obj.map φ.op).hom
      (((curveDivisorMap.{u, v} g).hom.app (op U)).hom z) =
    ((closedPointDivisorSheaf.{u, v} X).obj.map φ.op).hom
      (closedPointDivisorSheafSection.{u, v} U z.down)
  have hn := NatTrans.naturality_apply (curveDivisorMap.{u, v} g).hom φ.op z
  refine hn.symm.trans ?_
  have h := divisorSequenceSecondMap_hom_app.{u, v} X W
  have h2 := closedPointDivisorSheafSection_map.{u, v} φ (Additive.toMul z.down)
  rw [show (curveDivisorMap.{u, v} g).hom.app (op ((Scheme.AffineEtale.Spec X).obj W)) =
    affineEtaleDivisorApp.{u, v} X W from h]
  change (affineEtaleDivisorApp.{u, v} X W).hom _ = _
  refine (affineEtaleDivisorApp_apply.{u, v} X W _).trans (Eq.trans ?_ h2.symm)
  rfl

/-- **The value of the divisor at a closed point is the order of vanishing**: for a quasi-compact
quasi-separated étale `X`-scheme `U`, `f ∈ 𝓡_X^*(U)` and a closed point `u` of `U`,
`div_U(f)(u)` is the order of vanishing of `f` at `u`. -/
@[weil "def_fk105_divisor_map"]
theorem curveDivisorMap_app_apply_closedPoint (U : X.Etale) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left]
    (z : ULift.{max (u + 1) v} (Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)))
    (y : closedPoints U.left) :
    haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
    haveI : IsNormal X := isNormal_of_isCurve_of_smooth g
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    haveI : IsLocallyNoetherian U.left := isLocallyNoetherian_etale_left X U
    Scheme.Etale.closedPointDivisorSheafSectionsAddEquiv.{u, v} U
        (((curveDivisorMap.{u, v} g).hom.app (op U)).hom z) y =
      etaleGenericFibreOrdOfPoint U y.1 z.down := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : IsLocallyNoetherian U.left := isLocallyNoetherian_etale_left X U
  have : IsNoetherian U.left := {}
  have : NoetherianSpace U.left := inferInstance
  let x : closedPoints X := ⟨U.hom y.1, (Scheme.Etale.mem_closedPoints_iff U).1 y.2⟩
  rw [Scheme.Etale.closedPointDivisorSheafSectionsAddEquiv_apply.{u, v} U _ y x rfl,
    curveDivisorMap_app_apply g U z]
  rw [closedPointDivisorSheafSection_apply]
  -- the instance arguments of the two sides differ up to unfolding of the identity functor
  erw [closedPointDivisorSheaf.sectionsAddEquivDirectSum_symm_apply]
  erw [closedPointDivisorSections_apply]
  change ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x.1 U).hom
      ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x.1 U).inv
        (residueFibreOrdOfPoint.{u, v} U x.1 z.down))
        ((U.hom.fiberHomeo x.1).symm ⟨y.1, rfl⟩)).down = _
  rw [Iso.inv_hom_id_apply]
  exact congrArg (fun p => etaleGenericFibreOrdOfPoint U p z.down)
    (U.hom.fiberι_fiberHomeo_symm x.1 ⟨y.1, rfl⟩)

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (hX : B.Contains X)

/-- **The divisor map on the small étale site of a big étale site**: the restriction of
`AlgebraicGeometry.curveDivisorMap` along `AlgebraicGeometry.SmallEtale.toEtaleSite`. -/
abbrev curveDivisorMap :
    (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
        ((genericPointDirectImage.{u, v} X).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))) ⟶
      (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
        (closedPointDivisorSheaf.{u, v} X) :=
  (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}).inverse.map
    (AlgebraicGeometry.curveDivisorMap.{u, v} g)

/-- The divisor map on `AlgebraicGeometry.SmallEtale B X hX` over `V` is the divisor map over
the underlying étale `X`-scheme. -/
theorem curveDivisorMap_hom_app (V : SmallEtale B X hX) :
    (curveDivisorMap.{u, v} g B hX).hom.app (op V) =
      (AlgebraicGeometry.curveDivisorMap.{u, v} g).hom.app (op ((toEtaleSite B X hX).obj V)) :=
  rfl

end SmallEtale

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (hX : B.Contains X)

/-- **The divisor map on the étale site `Et(X)`** of noetherian separated étale `X`-schemes,
`div : 𝓡_X^* ⟶ 𝒟_X` with target the sheaf of divisors
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorSheaf`. -/
@[weil "def_fk105_divisor_map"]
abbrev curveDivisorMap :
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    (sheafEquivEtale B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
        ((genericPointDirectImage.{u, v} X).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))) ⟶
      divisorSheaf.{u, v} B X hX :=
  haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  (sheafEquivEtale B X hX AddCommGrpCat.{max (u + 1) v}).inverse.map
    (AlgebraicGeometry.curveDivisorMap.{u, v} g)

/-- **The divisor on `Et(X)` at a closed point is the order of vanishing**: for `U` in `Et(X)`,
`f ∈ 𝓡_X^*(U)` and a closed point `u` of `U`, `div_U(f)(u)` is the order of vanishing of `f` at
`u`. -/
@[weil "def_fk105_divisor_map"]
theorem curveDivisorMap_app_apply_closedPoint (U : SmallNoetherianSeparatedEtale B X hX)
    (z : ULift.{max (u + 1) v} (Additive ((Γ(pullback
      ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).hom
        (genericPointInclusion X), ⊤))ˣ)))
    (y : closedPoints ((toScheme B X hX).obj U)) :
    haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
    haveI : IsNormal X := isNormal_of_isCurve_of_smooth g
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    haveI : IsLocallyNoetherian
        ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left :=
      isLocallyNoetherian_etale_left X _
    divisorSheafSectionsAddEquiv.{u, v} U
        (((curveDivisorMap.{u, v} g B hX).hom.app (op U)).hom z) y =
      etaleGenericFibreOrdOfPoint _ y.1 z.down := by
  have : CompactSpace ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left :=
    inferInstanceAs (CompactSpace ((toScheme B X hX).obj U))
  have : QuasiSeparatedSpace
      ((SmallEtale.toEtaleSite B X hX).obj ((inclusion B X hX).obj U)).left :=
    inferInstanceAs (QuasiSeparatedSpace ((toScheme B X hX).obj U))
  exact AlgebraicGeometry.curveDivisorMap_app_apply_closedPoint.{u, v} g _ z y

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry
