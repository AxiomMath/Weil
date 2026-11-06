module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import Weil.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import Weil.Attr

/-!
# The functor of geometric points over a geometric point

Let `s : Spec Ω ⟶ X` be a geometric point of a scheme `X`. For an `X`-scheme `p : Y ⟶ X` let
`Y(s) = Hom_X(Spec Ω, Y)` be the set of morphisms `α : Spec Ω ⟶ Y` with `α ≫ p = s`. An
`X`-morphism `f : Y₁ ⟶ Y₂` induces `f(s) : Y₁(s) → Y₂(s)`, `α ↦ α ≫ f`, and this makes
`Y ↦ Y(s)` a functor from `X`-schemes to sets, the *functor of geometric points over `s`*.
It is the functor corepresented by `s` regarded as an `X`-scheme.

Restricted to the category `Cov(X)` of covering spaces (finite étale `X`-schemes) it is the
geometric fibre functor `AlgebraicGeometry.finiteEtaleFiberFunctor s`, whose values are finite.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.fiberFunctor s` — the functor `Over X ⥤ Type u`,
  `Y ↦ Y(s)`.
* `AlgebraicGeometry.GeometricPoint.fiberFunctorIsoCoyoneda s` — it is corepresented by `s`
  regarded as an object of `Over X`.

## Main results

* `AlgebraicGeometry.GeometricPoint.forget_comp_fiberFunctor` — restricted to `Cov(X)` the
  functor is the geometric fibre functor `finiteEtaleFiberFunctor s` on the nose.
* `AlgebraicGeometry.GeometricPoint.finite_fiberFunctor_obj` — `Y(s)` is finite for every
  covering space `Y` of `X`.

## Implementation notes

Geometric points take values in algebraically closed fields (`AlgebraicGeometry.GeometricPoint`),
following the convention of the Stacks project; the source allows separably closed fields.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2)
-/

/- The restriction of the geometric fibre functor
to `Cov(X)` is StacksFrontier's `finiteEtaleFiberFunctor`, reused. -/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

variable {X : Scheme.{u}} (s : GeometricPoint X)

/-- **The functor of geometric points over `s`.** It sends an `X`-scheme `p : Y ⟶ X` to the set
`Y(s)` of morphisms `α : Spec Ω ⟶ Y` with `α ≫ p = s`, and an `X`-morphism `f` to
`α ↦ α ≫ f`. -/
@[weil "def_fka1_geometric_fiber_functor"]
def fiberFunctor : Over X ⥤ Type u where
  obj Y := { α : s.source ⟶ Y.left // α ≫ Y.hom = s.hom }
  map {Y Z} f := ↾ (fun α ↦ ⟨α.1 ≫ f.left, by rw [Category.assoc, Over.w f, α.2]⟩)
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

@[simp]
lemma fiberFunctor_obj (Y : Over X) :
    (fiberFunctor s).obj Y = { α : s.source ⟶ Y.left // α ≫ Y.hom = s.hom } :=
  rfl

@[simp]
lemma coe_fiberFunctor_map_apply {Y Z : Over X} (f : Y ⟶ Z) (α : (fiberFunctor s).obj Y) :
    ((fiberFunctor s).map f α).1 = α.1 ≫ f.left :=
  rfl

/-- The functor of geometric points over `s` is corepresented by `s`, regarded as the
`X`-scheme `Spec Ω ⟶ X`: `Y(s) = Hom_X(Spec Ω, Y)`. -/
def fiberFunctorIsoCoyoneda : fiberFunctor s ≅ coyoneda.obj (op (Over.mk s.hom)) :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso
      { toFun := fun α ↦ Over.homMk α.1 α.2
        invFun := fun g ↦ ⟨g.left, Over.w g⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })
    (fun _ ↦ rfl)

/-- **Restriction to `Cov(X)`.** On covering spaces, the functor of geometric points over `s` is
the geometric fibre functor `finiteEtaleFiberFunctor s : Cov(X) ⥤ Type u`. -/
@[weil "def_fka1_geometric_fiber_functor"]
theorem forget_comp_fiberFunctor :
    MorphismProperty.Over.forget _ _ X ⋙ fiberFunctor s =
      (finiteEtaleFiberFunctor s : X.CoveringSpace ⥤ Type u) :=
  rfl

/-- The set `Y(s)` of geometric points of a covering space over `s` is finite. -/
instance finite_fiberFunctor_obj (Y : X.CoveringSpace) :
    Finite ((fiberFunctor s).obj ((MorphismProperty.Over.forget _ _ X).obj Y)) :=
  finite_finiteEtaleFiber s Y

end GeometricPoint

end AlgebraicGeometry

end
