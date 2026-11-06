module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import Weil.Attr

/-!
# The map from the stalk of a represented sheaf to the geometric fibre

Let `S` be a scheme, `s` a geometric point of `S` and `Y` an object of the small étale site of
`S`. The stalk at `s` of the sheaf `Ỹ` represented by `Y` is the colimit
`Ỹ_s = colim_{(U, u)} Hom_S(U, Y)` over the pointed étale neighbourhoods `(U, u)` of `s`. For
each such neighbourhood, `f ↦ u ≫ f` sends `Hom_S(U, Y)` to the set `Y(s)` of lifts of `s` to
`Y`; these maps form a cocone, since `v ≫ (h ≫ f) = u ≫ f` for a morphism of neighbourhoods
`h : (V, v) ⟶ (U, u)`. The induced map on the colimit is `ε_Y : Ỹ_s ⟶ Y(s)`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.stalkToFiberMap`: the map `ε_Y : Ỹ_s ⟶ Y(s)`.

## Main results

* `AlgebraicGeometry.GeometricPoint.ι_stalkToFiberMap` and
  `AlgebraicGeometry.GeometricPoint.stalkToFiberMap_etaleStalkGerm`: `ε_Y` sends the germ at
  `(U, u)` of `f : U ⟶ Y` to `u ≫ f`, which characterizes it as the map induced on the colimit.
* `AlgebraicGeometry.GeometricPoint.stalkToFiberMap_naturality`: `ε_Y` is natural in `Y`.
* `AlgebraicGeometry.GeometricPoint.bijective_stalkToFiberMap`: `ε_Y` is bijective.

## Implementation notes

`ε_Y` is the component at `Y` of the natural isomorphism
`AlgebraicGeometry.smallEtaleYonedaCompEtaleStalkFunctorIso` between the stalk of the represented
sheaf and the fibre functor `AlgebraicGeometry.geometricPointFiber`. Geometric points take values
in algebraically closed fields, and the étale site is the small étale site
`AlgebraicGeometry.SmallEtale` of a big étale site, following the Stacks project.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
-/

/- The map from the stalk to the fibre is
StacksFrontier's `smallEtaleYonedaCompEtaleStalkFunctorIso`, reused. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GeometricPoint

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : GeometricPoint S)

/-- **The map `ε_Y : Ỹ_s ⟶ Y(s)`** from the stalk at `s` of the sheaf represented by `Y` to the
set of lifts of `s` to `Y`, induced on the colimit over pointed étale neighbourhoods `(U, u)` of
`s` by the maps `Hom_S(U, Y) → Y(s)`, `f ↦ u ≫ f` (see `ι_stalkToFiberMap`). -/
@[weil "def_fka1_stalk_to_fiber_map"]
def stalkToFiberMap (Y : SmallEtale B S hS) :
    (etaleStalkFunctor.{u, u} B S hS s).obj (SmallEtale.representedSheaf Y) ⟶
      (geometricPointFiber B S hS s).obj Y :=
  (smallEtaleYonedaCompEtaleStalkFunctorIso B S hS s).hom.app Y

/-- `ε_Y` is the map induced on the colimit by `f ↦ u ≫ f` on `Hom_S(U, Y)`, for each pointed
étale neighbourhood `(U, u)` of `s`. -/
@[weil "def_fka1_stalk_to_fiber_map", reassoc]
theorem ι_stalkToFiberMap (Y : SmallEtale B S hS) (U : (geometricPointFiber B S hS s).Elements) :
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.representedSheaf Y).obj) (op U) ≫ stalkToFiberMap s Y =
      ↾ fun f ↦ (geometricPointFiber B S hS s).map f U.2 :=
  colimit_ι_comp_yonedaCompEtaleStalkPresheafFunctorIso_hom B S hS s Y U

/-- `ε_Y` sends the germ at `(U, u)` of `f : U ⟶ Y` to the lift `u ≫ f` of `s`. -/
@[simp]
theorem stalkToFiberMap_etaleStalkGerm (Y : SmallEtale B S hS)
    (U : (geometricPointFiber B S hS s).Elements) (f : U.1 ⟶ Y) :
    stalkToFiberMap s Y (etaleStalkGerm.{u, u} B S hS s (SmallEtale.representedSheaf Y) U f) =
      (geometricPointFiber B S hS s).map f U.2 :=
  smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm B S hS s Y U f

/-- The underlying morphism of schemes of `ε_Y` applied to the germ at `(U, u)` of `f : U ⟶ Y`
is the composite `u ≫ f`. -/
theorem coe_stalkToFiberMap_etaleStalkGerm (Y : SmallEtale B S hS)
    (U : (geometricPointFiber B S hS s).Elements) (f : U.1 ⟶ Y) :
    (stalkToFiberMap s Y
        (etaleStalkGerm.{u, u} B S hS s (SmallEtale.representedSheaf Y) U f)).1 =
      U.2.1 ≫ (SmallEtale.toScheme B S hS).map f :=
  smallEtaleYonedaCompEtaleStalkFunctorIso_hom_app_etaleStalkGerm_val B S hS s Y U f

/-- `ε_Y` is natural in `Y`: for `v : Y ⟶ Y'`, `ε_{Y'} ∘ ṽ_s = v ∘ ε_Y`. -/
@[reassoc]
theorem stalkToFiberMap_naturality {Y Y' : SmallEtale B S hS} (v : Y ⟶ Y') :
    (etaleStalkFunctor.{u, u} B S hS s).map ((smallEtaleYoneda B S hS).map v) ≫
        stalkToFiberMap s Y' =
      stalkToFiberMap s Y ≫ (geometricPointFiber B S hS s).map v :=
  (smallEtaleYonedaCompEtaleStalkFunctorIso B S hS s).hom.naturality v

instance isIso_stalkToFiberMap (Y : SmallEtale B S hS) : IsIso (stalkToFiberMap s Y) :=
  inferInstanceAs (IsIso ((smallEtaleYonedaCompEtaleStalkFunctorIso B S hS s).hom.app Y))

/-- `ε_Y` is bijective. -/
theorem bijective_stalkToFiberMap (Y : SmallEtale B S hS) :
    Function.Bijective (stalkToFiberMap s Y) :=
  (isIso_iff_bijective _).mp inferInstance

end AlgebraicGeometry.GeometricPoint

end
