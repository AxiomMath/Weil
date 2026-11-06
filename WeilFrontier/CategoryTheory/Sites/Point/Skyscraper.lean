/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Stalks of étale sheaves commute with colimits

Let `S` be a scheme and `s : Spec Ω ⟶ S` a geometric point, `Ω` a separably closed field.
For a small diagram `K : I ⥤ Sheaf (smallEtaleTopology S) A` of étale sheaves (of sets, of
abelian groups, or more generally with values in a concrete category with products, colimits and
sheafification), the colimit of `K` exists in the category of sheaves, and the canonical map
`colim_i (K i)_s ⟶ (colim_i K i)_s` is bijective.

## Main results

* `AlgebraicGeometry.Scheme.bijective_colimit_post_sheafFiber_pointSmallEtale`: the general
  statement for sheaves with values in a concrete category.
* `AlgebraicGeometry.Scheme.bijective_colimit_post_sheafFiber_pointSmallEtale_type` and
  `AlgebraicGeometry.Scheme.bijective_colimit_post_sheafFiber_pointSmallEtale_addCommGrp`:
  the cases of sheaves of sets and of abelian groups; the existence of the colimit in sheaves is
  the instance `CategoryTheory.Sheaf.instHasColimitsOfShape`, recorded in
  `AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtale_type` and
  `AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtale_addCommGrp`.

## Implementation notes

The stalk of a sheaf `F` at `s` is `(pointSmallEtale s).sheafFiber.obj F`, the colimit of `F`
over the category of étale neighbourhoods of `s`. Rather than through the objectwise colimit
presheaf and its sheafification, the commutation is obtained from the fact that the fiber
functor at a point of a site is a left adjoint (its right adjoint is the skyscraper sheaf
functor), so it preserves all colimits.

The values of the sheaves live in an arbitrary universe `w` with `UnivLE.{u, w}`, assuming that
sheafification exists for them; both hold for `w = u` and for `w = u + 1`.
-/

@[expose] public section

universe u w

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The colimits of small diagrams of étale sheaves of sets exist. -/
@[weil "lem_fk104_stalks_commute_colimits"]
theorem hasColimitsOfShape_sheaf_smallEtale_type [UnivLE.{u, w}]
    [HasSheafify (smallEtaleTopology S) (Type w)] (I : Type u) [Category.{u} I] :
    HasColimitsOfShape I (Sheaf (smallEtaleTopology S) (Type w)) :=
  inferInstance

/-- The colimits of small diagrams of étale sheaves of abelian groups exist. -/
@[weil "lem_fk104_stalks_commute_colimits"]
theorem hasColimitsOfShape_sheaf_smallEtale_addCommGrp [UnivLE.{u, w}]
    [HasSheafify (smallEtaleTopology S) AddCommGrpCat.{w}] (I : Type u) [Category.{u} I] :
    HasColimitsOfShape I (Sheaf (smallEtaleTopology S) AddCommGrpCat.{w}) :=
  inferInstance

/-- The stalk at a geometric point commutes with small colimits of étale sheaves: the canonical
map from the colimit of the stalks to the stalk of the colimit is bijective. -/
theorem bijective_colimit_post_sheafFiber_pointSmallEtale
    {A : Type*} [Category A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    {I : Type*} [Category I] (K : I ⥤ Sheaf (smallEtaleTopology S) A)
    [HasColimit K] [HasColimit (K ⋙ (pointSmallEtale s).sheafFiber)] :
    Function.Bijective
      (ConcreteCategory.hom (colimit.post K (pointSmallEtale s).sheafFiber)) :=
  ConcreteCategory.bijective_of_isIso _

/-- The stalk at a geometric point of a small colimit of étale sheaves of sets is the colimit
of the stalks. -/
@[weil "lem_fk104_stalks_commute_colimits"]
theorem bijective_colimit_post_sheafFiber_pointSmallEtale_type [UnivLE.{u, w}]
    [HasSheafify (smallEtaleTopology S) (Type w)]
    {I : Type u} [Category.{u} I] (K : I ⥤ Sheaf (smallEtaleTopology S) (Type w)) :
    Function.Bijective (colimit.post K (pointSmallEtale s).sheafFiber) :=
  bijective_colimit_post_sheafFiber_pointSmallEtale s K

/-- The stalk at a geometric point of a small colimit of étale sheaves of abelian groups is the
colimit of the stalks. -/
@[weil "lem_fk104_stalks_commute_colimits"]
theorem bijective_colimit_post_sheafFiber_pointSmallEtale_addCommGrp [UnivLE.{u, w}]
    [HasSheafify (smallEtaleTopology S) AddCommGrpCat.{w}]
    {I : Type u} [Category.{u} I] (K : I ⥤ Sheaf (smallEtaleTopology S) AddCommGrpCat.{w}) :
    Function.Bijective (colimit.post K (pointSmallEtale s).sheafFiber) :=
  bijective_colimit_post_sheafFiber_pointSmallEtale s K

end AlgebraicGeometry.Scheme

end
