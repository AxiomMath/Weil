module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# The category of étale neighbourhoods of a geometric point

Let `s : Spec k ⟶ S` be a geometric point of a scheme `S`. An étale neighbourhood of `s` is a
pair `(U, u)` of a scheme `U` étale over `S`, with structure map `π_U : U ⟶ S`, and a morphism
`u : Spec k ⟶ U` with `u ≫ π_U = s`; a morphism `(U, u) ⟶ (V, v)` is a morphism `h : U ⟶ V`
over `S` with `u ≫ h = v`. These form the category `N(s)`
(`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood`), which comes with a forgetful functor
`N(s) ⥤ Et(S)`, `(U, u) ↦ U`, to the small étale site of `S`.

The category `N(s)` is equivalent to the category of elements of the fibre functor of the point
`AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site defined by `s`, compatibly
with the two forgetful functors to `S.Etale`. Consequently `N(s)` is cofiltered and initially
small, so that colimits over `N(s)ᵒᵖ` of presheaves with values in sets, abelian groups or rings
exist.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.forget`: the forgetful functor
  `N(s) ⥤ S.Etale`.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.equivFiberElements`: the equivalence of
  `N(s)` with the category of elements of the fibre functor of `Scheme.pointSmallEtale s.hom`.

## Main results

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.equivFiberElements_functor_comp_π`: the
  equivalence commutes with the forgetful functors to `S.Etale`.
* instances: `N(s)` is cofiltered and initially small.

## Implementation notes

Geometric points take values in algebraically closed fields
(`AlgebraicGeometry.GeometricPoint`), and the category `N(s)` is the one of the Stacks project,
`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood`, which is reused here. The source asks
`N(s)` to be essentially small; since étale schemes over `S` carry no finiteness condition here
(arbitrary disjoint unions of copies of an étale neighbourhood are étale neighbourhoods), the
category is not essentially small in the universe of `S`. What is used of smallness, the
existence of colimits over `N(s)ᵒᵖ`, follows from initial smallness, which is proved.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
* [Stacks Project, Tag 03PO](https://stacks.math.columbia.edu/tag/03PO)
-/

/- The category of étale neighbourhoods is StacksFrontier's `GeometricPoint.EtaleNeighborhood`
(geometric points over algebraically closed fields, following the Stacks project convention); FK's
"essentially small" is replaced by `InitiallySmall` (see the implementation notes). -/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

namespace EtaleNeighborhood

variable {S : Scheme.{u}} {s : GeometricPoint S}

/-- The object of the small étale site underlying an étale neighbourhood. -/
abbrev toEtale (U : EtaleNeighborhood s) : S.Etale :=
  Scheme.Etale.mk U.toBase

/-- The étale neighbourhood given by an object of the small étale site and a lift of the
geometric point to it. -/
@[simps]
def ofEtale (V : S.Etale) (p : s.source ⟶ V.left) (hp : p ≫ V.hom = s.hom) :
    EtaleNeighborhood s where
  scheme := V.left
  toBase := V.hom
  point := p
  point_comp := hp

/-- A morphism of étale neighbourhoods built from a morphism of schemes over the base carrying
the lift to the lift. -/
@[simps]
def homMk {U V : EtaleNeighborhood s} (h : U.scheme ⟶ V.scheme) (over : h ≫ V.toBase = U.toBase)
    (point_comp : U.point ≫ h = V.point) : U ⟶ V where
  hom := h
  over := over
  point_comp := point_comp

variable (s) in
/-- The forgetful functor from étale neighbourhoods of `s` to the small étale site,
`(U, u) ↦ U`. -/
@[weil "def_fk102_etale_neighborhood", simps]
def forget : EtaleNeighborhood s ⥤ S.Etale where
  obj U := U.toEtale
  map f := MorphismProperty.Over.homMk f.hom f.over

variable (s) in
/-- An étale neighbourhood of `s` as an element of the fibre functor of the point
`Scheme.pointSmallEtale s.hom` of the small étale site. -/
@[simps]
def toFiberElements : EtaleNeighborhood s ⥤ (Scheme.pointSmallEtale s.hom).fiber.Elements where
  obj U := ⟨U.toEtale, Over.homMk U.point U.point_comp⟩
  map f := ⟨MorphismProperty.Over.homMk f.hom f.over, by
    apply Over.OverMorphism.ext
    exact f.point_comp⟩

variable (s) in
/-- An element of the fibre functor of the point `Scheme.pointSmallEtale s.hom` as an étale
neighbourhood of `s`. -/
@[simps!]
def ofFiberElements : (Scheme.pointSmallEtale s.hom).fiber.Elements ⥤ EtaleNeighborhood s where
  obj V := ofEtale V.1 V.2.left (Over.w V.2)
  map {V W} f := homMk f.1.left (Over.w ((Scheme.Etale.forget S).map f.1))
    (congrArg CommaMorphism.left f.2)

variable (s) in
/-- The category of étale neighbourhoods of `s` is the category of elements of the fibre
functor of the point `Scheme.pointSmallEtale s.hom` of the small étale site. -/
@[weil "def_fk102_etale_neighborhood"]
def equivFiberElements : EtaleNeighborhood s ≌ (Scheme.pointSmallEtale s.hom).fiber.Elements :=
  { functor := toFiberElements s
    inverse := ofFiberElements s
    unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
      apply Hom.ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
    counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
      apply CategoryOfElements.ext
      simp
      rfl) }

lemma equivFiberElements_functor :
    (equivFiberElements s).functor = toFiberElements s :=
  rfl

lemma equivFiberElements_inverse :
    (equivFiberElements s).inverse = ofFiberElements s :=
  rfl

lemma toFiberElements_comp_π :
    toFiberElements s ⋙ CategoryOfElements.π _ = forget s := by
  fapply CategoryTheory.Functor.ext
  · intro U
    rfl
  · intro U V f
    simp
    rfl

instance : IsCofiltered (EtaleNeighborhood s) :=
  IsCofiltered.of_equivalence (equivFiberElements s).symm

instance : InitiallySmall.{u} (EtaleNeighborhood s) :=
  initiallySmall_of_initial_of_initiallySmall (equivFiberElements s).inverse

end EtaleNeighborhood

end GeometricPoint

end AlgebraicGeometry

end
