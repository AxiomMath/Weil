module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafSecondMap
public import StacksFrontier.AlgebraicGeometry.Properties.NormalStalkDvr
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.Etale
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic

/-!
# The divisor map at a closed point is the valuation

Let `X` be a smooth curve over a field `k`, `U` an étale `X`-scheme and `f ∈ 𝓡_X^*(U)` an
invertible function on the generic fibre of `U`. Its divisor `div_U(f)` is the family of orders
of vanishing of `f` at the closed points of `U`. This file identifies that order with the
valuation of `f` at the local ring: if `u` is a closed point of `U`, `t` a generator of the
maximal ideal of `𝒪_{U,u}` and `f_a` the component of `f` on the irreducible component of `U`
through `u` (a rational function on an integral open neighbourhood of `u`), then
`div_U(f)(u)` is the integer `e` with `f_a ∈ t ^ e 𝒪_{U,u}^*`.

The proof is local algebra: `𝒪_{U,u}` is a discrete valuation ring whose fraction field is the
function field of the component, so `t` is a uniformizer and every nonzero rational function is
`t ^ e w` for a unique `e ∈ ℤ` and some unit `w`.

## Main results

* `IsDiscreteValuationRing.ordFrac_eq_exp_iff`: over a discrete valuation ring with irreducible
  `ϖ`, a nonzero element of the fraction field has order `n` iff it lies in `ϖ ^ n R^*`.
* `AlgebraicGeometry.Scheme.ord_eq_iff_exists_units`: the same for Mathlib's order of vanishing
  at a point of coheight one with discrete valuation ring stalk.
* `AlgebraicGeometry.etaleGenericFibreOrdOfPoint_eq_iff_exists_units`: the order of vanishing
  at a point of coheight one of an étale scheme over an integral normal scheme.
* `AlgebraicGeometry.curveDivisorMap_app_apply_closedPoint_eq_iff`: **the divisor map at a
  closed point is the valuation**, on the small étale site of `X`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.curveDivisorMap_app_apply_closedPoint_eq_iff`:
  the same on the étale site `Et(X)`.

## Implementation notes

The ring of rational functions on `U` is the product of the function fields of its irreducible
components, and the component of `f` on the component through `u` is read in the function field
of an integral open neighbourhood `W` of `u`, which is the residue field at the generic point of
that component. The local ring `𝒪_{U,u}` is embedded in this field through the canonical
isomorphism `𝒪_{U,u} ≅ 𝒪_{W,u}`. The results are stated as an equivalence, which says both that
`f_a ∈ t ^ e 𝒪_{U,u}^*` for `e = div_U(f)(u)` and that this `e` is the only such integer.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing WithZero

universe u v

namespace IsDiscreteValuationRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The order of `ϖ ^ n * w`, for `ϖ` irreducible and `w` a unit, is `n`. -/
theorem ordFrac_zpow_mul_unit {ϖ : R} (hϖ : Irreducible ϖ) (n : ℤ) (w : Rˣ) :
    Ring.ordFrac R (algebraMap R K ϖ ^ n * algebraMap R K w) = exp n := by
  rw [map_mul, map_zpow₀, Ring.ordFrac_irreducible hϖ,
    Ring.ordFrac_of_isUnit w.isUnit, mul_one, ← exp_zsmul, smul_eq_mul, mul_one]

/-- Over a discrete valuation ring with irreducible `ϖ`, a nonzero `x` of the fraction field has
order `n` if and only if `x ∈ ϖ ^ n R^*`. -/
theorem ordFrac_eq_exp_iff {ϖ : R} (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) (n : ℤ) :
    Ring.ordFrac R x = exp n ↔ ∃ w : Rˣ, x = algebraMap R K ϖ ^ n * algebraMap R K w := by
  constructor
  · intro h
    obtain ⟨m, w, rfl⟩ := exists_units_eq_smul_zpow_of_irreducible (K := K) hϖ hx
    have hw : (w • algebraMap R K ϖ ^ m : K) = algebraMap R K ϖ ^ m * algebraMap R K w := by
      rw [Units.smul_def, Algebra.smul_def, mul_comm]
    rw [hw, ordFrac_zpow_mul_unit hϖ, exp_inj] at h
    exact ⟨w, h ▸ hw⟩
  · rintro ⟨w, rfl⟩
    exact ordFrac_zpow_mul_unit hϖ n w

end IsDiscreteValuationRing

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- At a point `x` of coheight one with discrete valuation ring stalk, and for `t` irreducible in
`𝒪_{X,x}`, a nonzero rational function `f` has order of vanishing `n` at `x` if and only if
`f ∈ t ^ n 𝒪_{X,x}^*`. -/
theorem ord_eq_iff_exists_units {x : X} (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {t : X.presheaf.stalk x} (ht : Irreducible t)
    {f : X.functionField} (hf : f ≠ 0) (n : ℤ) :
    X.ord f x = n ↔ ∃ w : (X.presheaf.stalk x)ˣ,
      f = algebraMap (X.presheaf.stalk x) X.functionField t ^ n *
        algebraMap (X.presheaf.stalk x) X.functionField w := by
  rw [ord_eq_iff hx hf, ← IsDiscreteValuationRing.ordFrac_eq_exp_iff ht hf]
  rfl

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] [IsNormal X] (U : X.Etale) [IsLocallyNoetherian U.left]

/-- **The order of vanishing at a codimension-one point of an étale `X`-scheme, read off a
generator of the maximal ideal.** Let `W` be an integral open subscheme of `U`, `x` a point of
`W` of coheight one in `U`, `t` a generator of the maximal ideal of `𝒪_{U,x}` and `a` an
invertible function on the generic fibre of `U`. Then the order of vanishing of `a` at `x` is `n`
if and only if the rational function on `W` defined by `a` lies in `t ^ n 𝒪_{U,x}^*`, where
`𝒪_{U,x}` is embedded in the function field of `W` through `𝒪_{U,x} ≅ 𝒪_{W,x}`. -/
theorem etaleGenericFibreOrdOfPoint_eq_iff_exists_units (W : U.left.Opens)
    [AlgebraicGeometry.IsIntegral W.toScheme] (x : W.toScheme) (hx : Order.coheight x.1 = 1)
    {t : U.left.presheaf.stalk x.1}
    (ht : maximalIdeal (U.left.presheaf.stalk x.1) = Ideal.span {t})
    (a : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) (n : ℤ) :
    haveI : Etale U.hom := U.prop
    etaleGenericFibreOrdOfPoint U x.1 (Additive.ofMul a) = n ↔
      ∃ w : (U.left.presheaf.stalk x.1)ˣ,
        genericFibreToFunctionField (X := X) (W.ι ≫ U.hom)
            ((genericFibreOpensMap (X := X) U.hom W).appTop a) =
          algebraMap _ W.toScheme.functionField ((W.stalkIso x).inv.hom t) ^ n *
            algebraMap _ W.toScheme.functionField ((W.stalkIso x).inv.hom w) := by
  have : Etale U.hom := U.prop
  have : IsNormal U.left := isNormal_of_etale (X := U.left) (Y := X) U.hom
  have : IsDiscreteValuationRing (U.left.presheaf.stalk x.1) :=
    isDiscreteValuationRing_stalk_of_coheight_eq_one hx
  have hxW : Order.coheight x = 1 := (coheight_eq_of_etale W.ι x).symm.trans hx
  have : IsDiscreteValuationRing (W.toScheme.presheaf.stalk x) :=
    isDiscreteValuationRing_stalk_of_coheight_eq_one hxW
  let e : U.left.presheaf.stalk x.1 ≃+* W.toScheme.presheaf.stalk x :=
    (W.stalkIso x).symm.commRingCatIsoToRingEquiv
  have hte : Irreducible (e t) :=
    (MulEquiv.irreducible_iff e.toMulEquiv).2
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer t).2 ht)
  set f := genericFibreToFunctionField (X := X) (W.ι ≫ U.hom)
    ((genericFibreOpensMap (X := X) U.hom W).appTop a) with hf_def
  have hf : f ≠ 0 := by
    have hu : IsUnit ((genericFibreOpensMap (X := X) U.hom W).appTop a) :=
      a.isUnit.map _
    exact (hu.map _).ne_zero
  have hord : etaleGenericFibreOrdOfPoint U x.1 (Additive.ofMul a) = W.toScheme.ord f x := by
    have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
      inferInstanceAs (IsLocallyNoetherian U.left)
    have h1 := genericFibreOrdOfPoint_eq_genericFibreOrdOfOpen (X := X) U.hom (W := W) x
      (Additive.ofMul a)
    exact h1
  rw [hord, Scheme.ord_eq_iff_exists_units hxW hte hf n]
  have he : ∀ s, e s = (W.stalkIso x).inv.hom s := fun _ => rfl
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨Units.map e.symm.toMonoidHom w, ?_⟩
    rw [hw, he]
    change _ = _ * algebraMap _ _ (e (e.symm (w : W.toScheme.presheaf.stalk x)))
    rw [e.apply_symm_apply]
  · rintro ⟨w, hw⟩
    refine ⟨Units.map e.toMonoidHom w, ?_⟩
    rw [hw, he]
    rfl

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]

include g in
/-- A closed point of an étale `X`-scheme, for `X` a curve over a field, has coheight one. -/
theorem coheight_eq_one_of_mem_closedPoints_etale (U : X.Etale) {y : U.left}
    (hy : y ∈ closedPoints U.left) : Order.coheight y = 1 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  have : Etale U.hom := U.prop
  have hy' := (Scheme.Etale.mem_closedPoints_iff U).1 hy
  rw [← coheight_eq_of_etale U.hom y]
  exact coheight_eq_one_of_isCurve k g hy'

/-- **The divisor map at a closed point is the valuation.** Let `X` be a smooth curve over a field
`k`, `U` a quasi-compact quasi-separated étale `X`-scheme, `f ∈ 𝓡_X^*(U)`, `W` an integral open
subscheme of `U` (an open of the irreducible component of `U` through `x`, whose function field is
the residue field at the generic point of that component), `x` a closed point of `U` in `W` and
`t` a generator of the maximal ideal of `𝒪_{U,x}`. Then `div_U(f)(x) = e` if and only if the
component of `f` in the function field of `W` lies in `t ^ e 𝒪_{U,x}^*`. -/
@[weil "lem_fk105_divisor_map_valuation"]
theorem curveDivisorMap_app_apply_closedPoint_eq_iff (U : X.Etale) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left]
    (z : ULift.{max (u + 1) v} (Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)))
    (W : U.left.Opens) [AlgebraicGeometry.IsIntegral W.toScheme] (x : W.toScheme)
    (hx : x.1 ∈ closedPoints U.left) {t : U.left.presheaf.stalk x.1}
    (ht : maximalIdeal (U.left.presheaf.stalk x.1) = Ideal.span {t}) (e : ℤ) :
    haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
    haveI : IsNormal X := isNormal_of_isCurve_of_smooth g
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    haveI : IsLocallyNoetherian U.left := isLocallyNoetherian_etale_left X U
    haveI : Etale U.hom := U.prop
    Scheme.Etale.closedPointDivisorSheafSectionsAddEquiv.{u, v} U
        (((curveDivisorMap.{u, v} g).hom.app (op U)).hom z) ⟨x.1, hx⟩ = e ↔
      ∃ w : (U.left.presheaf.stalk x.1)ˣ,
        genericFibreToFunctionField (X := X) (W.ι ≫ U.hom)
            ((genericFibreOpensMap (X := X) U.hom W).appTop
              ((Additive.toMul z.down : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) :
                Γ(pullback U.hom (genericPointInclusion X), ⊤))) =
          algebraMap _ W.toScheme.functionField ((W.stalkIso x).inv.hom t) ^ e *
            algebraMap _ W.toScheme.functionField ((W.stalkIso x).inv.hom w) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : IsLocallyNoetherian U.left := isLocallyNoetherian_etale_left X U
  rw [curveDivisorMap_app_apply_closedPoint g U z ⟨x.1, hx⟩]
  exact etaleGenericFibreOrdOfPoint_eq_iff_exists_units U W x
    (coheight_eq_one_of_mem_closedPoints_etale g U hx) ht (Additive.toMul z.down) e

/-- **The divisor map on `Et(X)` at a closed point is the valuation**: the statement of
`AlgebraicGeometry.curveDivisorMap_app_apply_closedPoint_eq_iff` for `U` in the étale site
`Et(X)` of noetherian separated étale `X`-schemes. -/
@[weil "lem_fk105_divisor_map_valuation"]
theorem SmallNoetherianSeparatedEtale.curveDivisorMap_app_apply_closedPoint_eq_iff
    (B : BigEtaleSite.{u}) (hX : B.Contains X) (U : SmallNoetherianSeparatedEtale B X hX)
    (z : ULift.{max (u + 1) v} (Additive ((Γ(pullback
      ((SmallEtale.toEtaleSite B X hX).obj ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj
        U)).hom (genericPointInclusion X), ⊤))ˣ)))
    (W : ((SmallEtale.toEtaleSite B X hX).obj
      ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).left.Opens)
    [AlgebraicGeometry.IsIntegral W.toScheme] (x : W.toScheme)
    (hx : x.1 ∈ closedPoints ((SmallNoetherianSeparatedEtale.toScheme B X hX).obj U))
    {t : ((SmallEtale.toEtaleSite B X hX).obj
      ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).left.presheaf.stalk x.1}
    (ht : maximalIdeal (((SmallEtale.toEtaleSite B X hX).obj
      ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).left.presheaf.stalk x.1) =
        Ideal.span {t}) (e : ℤ) :
    haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
    haveI : IsNormal X := isNormal_of_isCurve_of_smooth g
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
    haveI : Etale ((SmallEtale.toEtaleSite B X hX).obj
      ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).hom :=
      ((SmallEtale.toEtaleSite B X hX).obj
        ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).prop
    SmallNoetherianSeparatedEtale.divisorSheafSectionsAddEquiv.{u, v} U
        (((SmallNoetherianSeparatedEtale.curveDivisorMap.{u, v} g B hX).hom.app (op U)).hom z)
          ⟨x.1, hx⟩ = e ↔
      ∃ w : (((SmallEtale.toEtaleSite B X hX).obj
          ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).left.presheaf.stalk x.1)ˣ,
        genericFibreToFunctionField (X := X) (W.ι ≫ ((SmallEtale.toEtaleSite B X hX).obj
            ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).hom)
            ((genericFibreOpensMap (X := X) ((SmallEtale.toEtaleSite B X hX).obj
              ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).hom W).appTop
              ((Additive.toMul z.down : (Γ(pullback ((SmallEtale.toEtaleSite B X hX).obj
                ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).hom
                  (genericPointInclusion X), ⊤))ˣ) :
                Γ(pullback ((SmallEtale.toEtaleSite B X hX).obj
                  ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).hom
                    (genericPointInclusion X), ⊤))) =
          algebraMap _ W.toScheme.functionField ((W.stalkIso x).inv.hom t) ^ e *
            algebraMap _ W.toScheme.functionField ((W.stalkIso x).inv.hom w) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : IsLocallyNoetherian ((SmallEtale.toEtaleSite B X hX).obj
      ((SmallNoetherianSeparatedEtale.inclusion B X hX).obj U)).left :=
    isLocallyNoetherian_etale_left X _
  rw [SmallNoetherianSeparatedEtale.curveDivisorMap_app_apply_closedPoint g B hX U z ⟨x.1, hx⟩]
  exact etaleGenericFibreOrdOfPoint_eq_iff_exists_units _ W x
    (coheight_eq_one_of_mem_closedPoints_etale g _ hx) ht (Additive.toMul z.down) e

end Curve

end AlgebraicGeometry
