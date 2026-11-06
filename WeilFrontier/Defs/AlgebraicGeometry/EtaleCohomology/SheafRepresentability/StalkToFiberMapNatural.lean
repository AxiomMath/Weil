module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.StalkFiberComparison
public import Weil.Attr

/-!
# Naturality of the map from the stalk of a represented sheaf to the geometric fibre

Let `S` be a scheme, `s` a geometric point of `S` and `v : Y ⟶ Y'` a morphism of the small étale
site of `S`. Postcomposition with `v` is a morphism `ṽ : Ỹ ⟶ Ỹ'` of the represented sheaves,
`f ↦ f ≫ v`, and `v` induces `v(s) : Y(s) ⟶ Y'(s)`, `α ↦ α ≫ v`, on the sets of lifts of `s`.
The maps `ε_Y : Ỹ_s ⟶ Y(s)` from the stalk of the represented sheaf to the set of lifts
(`AlgebraicGeometry.GeometricPoint.stalkToFiberMap`) are natural:
`ε_{Y'} ∘ (ṽ)_s = v(s) ∘ ε_Y`.

On the germ at a pointed étale neighbourhood `(U, u)` of `f : U ⟶ Y`, the map `(ṽ)_s` gives the
germ of `f ≫ v`, which `ε_{Y'}` sends to `u ≫ f ≫ v = v(s)(ε_Y(germ of f))`.

## Main results

* `AlgebraicGeometry.GeometricPoint.stalkToFiberMap_etaleStalkFunctor_map_apply`:
  `ε_{Y'}((ṽ)_s x) = v(s)(ε_Y x)` for every `x ∈ Ỹ_s`.
* `AlgebraicGeometry.GeometricPoint.stalkToFiberMap_etaleStalkFunctor_map_etaleStalkGerm`: on
  the germ at `(U, u)` of `f`, both sides are the lift `u ≫ f ≫ v`.

## Implementation notes

The morphism form of the naturality is
`AlgebraicGeometry.GeometricPoint.stalkToFiberMap_naturality`, the naturality of StacksFrontier's
`AlgebraicGeometry.smallEtaleYonedaCompEtaleStalkFunctorIso`. Geometric points take values in
algebraically closed fields, and the étale site is the small étale site
`AlgebraicGeometry.SmallEtale` of a big étale site, following the Stacks project.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GeometricPoint

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : GeometricPoint S)

/-- The morphism `ṽ : Ỹ ⟶ Ỹ'` of represented sheaves induced by `v : Y ⟶ Y'` is
postcomposition with `v`. -/
theorem smallEtaleYoneda_map_hom_app_apply {Y Y' : SmallEtale B S hS} (v : Y ⟶ Y')
    (U : SmallEtale B S hS) (f : (SmallEtale.representedSheaf Y).obj.obj (op U)) :
    ((smallEtaleYoneda B S hS).map v).hom.app (op U) f = (show U ⟶ Y from f) ≫ v :=
  rfl

/-- **Naturality of `ε`.** For a morphism `v : Y ⟶ Y'` of the small étale site,
`ε_{Y'} ∘ (ṽ)_s = v(s) ∘ ε_Y`, where `ṽ : Ỹ ⟶ Ỹ'` is postcomposition with `v`. -/
@[weil "lem_fka1_stalk_to_fiber_map_natural"]
theorem stalkToFiberMap_etaleStalkFunctor_map_apply {Y Y' : SmallEtale B S hS} (v : Y ⟶ Y')
    (x : (etaleStalkFunctor.{u, u} B S hS s).obj (SmallEtale.representedSheaf Y)) :
    stalkToFiberMap s Y'
        ((etaleStalkFunctor.{u, u} B S hS s).map ((smallEtaleYoneda B S hS).map v) x) =
      (geometricPointFiber B S hS s).map v (stalkToFiberMap s Y x) :=
  ConcreteCategory.congr_hom (stalkToFiberMap_naturality s v) x

/-- On the germ at a pointed étale neighbourhood `(U, u)` of `f : U ⟶ Y`, both sides of the
naturality of `ε` are the lift `u ≫ f ≫ v` of `s` to `Y'`. -/
theorem stalkToFiberMap_etaleStalkFunctor_map_etaleStalkGerm {Y Y' : SmallEtale B S hS}
    (v : Y ⟶ Y') (U : (geometricPointFiber B S hS s).Elements) (f : U.1 ⟶ Y) :
    stalkToFiberMap s Y'
        ((etaleStalkFunctor.{u, u} B S hS s).map ((smallEtaleYoneda B S hS).map v)
          (etaleStalkGerm.{u, u} B S hS s (SmallEtale.representedSheaf Y) U f)) =
      (geometricPointFiber B S hS s).map (f ≫ v) U.2 := by
  exact (congrArg (stalkToFiberMap s Y') (etaleStalkFunctor_map_etaleStalkGerm'
    ((smallEtaleYoneda B S hS).map v) U f)).trans (stalkToFiberMap_etaleStalkGerm s Y' U (f ≫ v))

end AlgebraicGeometry.GeometricPoint

end
