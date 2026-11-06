module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import WeilFrontier.AlgebraicGeometry.Fiber

/-!
# Isomorphisms of étale sheaves are detected at points closed in their fibre

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and `φ : F ⟶ G` a morphism of
sheaves of sets, or of abelian groups, on the small étale site of `X`. Then `φ` is an
isomorphism if and only if the induced map `φₓ` on stalks is bijective at every geometric point
`x` of `X` whose underlying point is closed in its fibre over `S`.

The "only if" direction is functoriality of the stalk. For the "if" direction, the points of
`X` closed in their fibre form a detecting set
(`AlgebraicGeometry.Scheme.Hom.smallEtale_isDetecting_closedInFiberPoints`), and isomorphisms
of étale sheaves are detected on stalks at the geometric points over a detecting set.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_iff_forall_bijective_sheafFiber_of_mem_closedInFiberPoints`
  — the criterion for sheaves of sets.
* `AlgebraicGeometry.Scheme.Hom.isIso_iff_forall_bijective_etaleStalk_of_mem_closedInFiberPoints`
  — the criterion for sheaves of abelian groups.

## Implementation notes

A finitely generated morphism in the sense of Freitag–Kiehl is a morphism locally of finite type
(`AlgebraicGeometry.LocallyOfFiniteType`). The small étale site is `AlgebraicGeometry.SmallEtale`
over a big étale site containing `X`, and geometric points take values in algebraically closed
fields; the underlying point of a geometric point `x` is `x.hom.base default`.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FK]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
  (B : BigEtaleSite.{u}) (hX : B.Contains X)

/-- A morphism `φ` of sheaves of sets on the small étale site of `X`, for `f : X ⟶ S` locally of
finite type, is an isomorphism if and only if it is bijective on the stalk at every geometric
point of `X` whose underlying point is closed in its fibre under `f`. -/
@[weil "lem_fk102_points_closed_in_fibre_suffice"]
theorem isIso_iff_forall_bijective_sheafFiber_of_mem_closedInFiberPoints
    {F G : Sheaf (SmallEtale.topology B X hX) (Type u)} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ x : GeometricPoint X, x.hom.base default ∈ f.closedInFiberPoints →
      Function.Bijective (((geometricPointSitePoint B X hX x).sheafFiber (A := Type u)).map φ) :=
  ⟨fun h x _ => (isIso_iff_forall_bijective_geometricPointSitePoint_sheafFiber B X hX φ).1 h x,
    fun h => isIso_of_bijective_presheafFiber_of_isDetecting_type
      (f.smallEtale_isDetecting_closedInFiberPoints B hX) φ h⟩

/-- A morphism `φ` of sheaves of abelian groups on the small étale site of `X`, for `f : X ⟶ S`
locally of finite type, is an isomorphism if and only if it is bijective on the stalk at every
geometric point of `X` whose underlying point is closed in its fibre under `f`. -/
@[weil "lem_fk102_points_closed_in_fibre_suffice"]
theorem isIso_iff_forall_bijective_etaleStalk_of_mem_closedInFiberPoints [UnivLE.{u, v}]
    {F G : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{v}} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ x : GeometricPoint X, x.hom.base default ∈ f.closedInFiberPoints →
      Function.Bijective ((etaleStalkPresheafFunctor B X hX x AddCommGrpCat.{v}).map φ.hom) := by
  refine ⟨fun h x _ =>
    (isIso_iff_forall_bijective_etaleStalkPresheafFunctor_map B X hX φ).1 h x, fun h => ?_⟩
  exact isIso_of_isIso_etaleStalkMap_of_isDetecting
    (f.smallEtale_isDetecting_closedInFiberPoints B hX) φ fun x hx =>
      (ConcreteCategory.isIso_iff_bijective _).2 (h x hx)

end AlgebraicGeometry.Scheme.Hom
