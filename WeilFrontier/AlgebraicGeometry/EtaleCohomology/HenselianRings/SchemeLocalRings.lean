/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.ConnectedAffineNeighbourhoodsDirected
public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.StalkColimits
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings
public import Weil.Attr

/-!
# The strict local ring as a colimit over connected affine étale neighbourhoods

Let `s` be a geometric point of a locally noetherian scheme `S`, and let `N₀(s)` be the full
subcategory of connected affine étale neighbourhoods of `s` inside the category `N(s)` of all
étale neighbourhoods (`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.IsConnectedAffine`).
Every étale neighbourhood receives a morphism from an object of `N₀(s)`, and `N(s)` is
cofiltered, so the inclusion `N₀(s) ⥤ N(s)` is initial. Hence colimits of presheaves over
`N₀(s)ᵒᵖ` agree with colimits over `N(s)ᵒᵖ`, and these compute stalks:

* the rings of functions `Γ(U, 𝒪_U)`, for `(U, u)` in `N₀(s)`, together with the germ maps
  `Γ(U, 𝒪_U) ⟶ 𝒪̃_{S,s}`, form a colimit cocone with vertex the strict local ring
  `AlgebraicGeometry.strictLocalRing`;
* for every presheaf `P` on the small étale site of `S`, the values `P(U)`, for `(U, u)` in
  `N₀(s)`, form a colimit cocone with vertex the stalk of `P` at `s`.

The germ map `Γ(U, 𝒪_U) ⟶ 𝒪̃_{S,s}` at an arbitrary étale neighbourhood `U` is the restriction
`Γ(U, 𝒪_U) ⟶ Γ(V, 𝒪_V)` along any morphism from an étale neighbourhood `V` of the bounded small
étale site, followed by the germ at `V` (`strictLocalRingGermCocone_ι_app`).

## Main definitions

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.forgetToScheme`: the functor
  `(U, u) ↦ U`.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.functionsDiagram`: the functor
  `(U, u) ↦ Γ(U, 𝒪_U)`.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.strictLocalRingGermCocone`: the germ maps
  `Γ(U, 𝒪_U) ⟶ 𝒪̃_{S,s}` over all étale neighbourhoods.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.connectedAffineStrictLocalRingCocone` and
  `connectedAffinePresheafFiberCocone`: the cocones over `N₀(s)ᵒᵖ`.

## Main results

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.isColimitStrictLocalRingGermCocone`: the
  strict local ring is the colimit of `Γ(U, 𝒪_U)` over all étale neighbourhoods.
* `EtaleNeighborhood.isColimitConnectedAffineStrictLocalRingCocone`:
  the strict local ring is the colimit of `Γ(U, 𝒪_U)` over the connected affine étale
  neighbourhoods.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.isColimitConnectedAffinePresheafFiberCocone`:
  the stalk at `s` of a presheaf on the small étale site is the colimit of its values on the
  connected affine étale neighbourhoods.

## Implementation notes

The strict local ring is defined on the bounded small étale site `SmallEtale B S hS`, whose
objects are bounded in size, while étale neighbourhoods are arbitrary schemes étale over `S`.
The comparison functor from the category of elements of the fibre functor of the bounded site's
point to `N(s)` is fully faithful and initial, so the germ cocone of the strict local ring
extends uniquely to all étale neighbourhoods. For the same reason a presheaf on the bounded site
cannot be evaluated on an arbitrary connected affine étale neighbourhood, so the presheaf
statement is made for presheaves on the small étale site `S.Etale`, whose stalk at `s` is the
fibre at the point `AlgebraicGeometry.Scheme.pointSmallEtale s.hom`. The source assumes `S`
noetherian; local noetherianity is what the cofinality of `N₀(s)` uses.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
-/

/- FK's "canonical map from the colimit
is an isomorphism" is stated as: the cocone of canonical maps is a colimit cocone. The presheaf
clause is stated for presheaves on Mathlib's `S.Etale` (values in any category with `u`-small
colimits), since objects of `N₀(s)` need not be objects of the bounded site. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.GeometricPoint.EtaleNeighborhood

variable {S : Scheme.{u}} (s : GeometricPoint S)

/-- The functor `(U, u) ↦ U` from the étale neighbourhoods of `s` to schemes. -/
def forgetToScheme : EtaleNeighborhood s ⥤ Scheme.{u} :=
  forget s ⋙ MorphismProperty.Over.forget _ _ _ ⋙ Over.forget S

@[simp]
lemma forgetToScheme_obj (U : EtaleNeighborhood s) : (forgetToScheme s).obj U = U.scheme := rfl

@[simp]
lemma forgetToScheme_map {U V : EtaleNeighborhood s} (f : U ⟶ V) :
    (forgetToScheme s).map f = f.hom := rfl

/-- The rings of functions on étale neighbourhoods, `(U, u) ↦ Γ(U, 𝒪_U)`, with transition maps
the pullbacks of functions. -/
def functionsDiagram : (EtaleNeighborhood s)ᵒᵖ ⥤ CommRingCat.{u} :=
  (forgetToScheme s).op ⋙ Scheme.Γ

/-- On the étale neighbourhoods coming from the bounded small étale site, the rings of functions
are the diagram defining the strict local ring. -/
lemma ofGeometricPointSitePointFiberElements_op_comp_functionsDiagram
    (B : BigEtaleSite.{u}) (hS : B.Contains S) :
    (ofGeometricPointSitePointFiberElements B hS s).op ⋙ functionsDiagram s =
      strictLocalRingDiagram B S hS s :=
  rfl

/-- Over a locally noetherian scheme, the inclusion of the connected affine étale neighbourhoods
into all étale neighbourhoods is initial. -/
instance initial_ι_isConnectedAffine [IsLocallyNoetherian S] :
    (IsConnectedAffine (s := s)).ι.Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (fun U => by
    obtain ⟨V, hV, ⟨f⟩⟩ := exists_isConnectedAffine_hom U
    exact ⟨⟨V, hV⟩, ⟨f⟩⟩)

section StrictLocalRing

variable (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- The germ maps `Γ(U, 𝒪_U) ⟶ 𝒪̃_{S,s}` from the rings of functions on all étale neighbourhoods
of `s` to the strict local ring: the extension of the germ cocone of the bounded small étale
site along the initial comparison functor. -/
def strictLocalRingGermCocone : Cocone (functionsDiagram s) :=
  (Functor.Final.extendCocone (F := (ofGeometricPointSitePointFiberElements B hS s).op)).obj
    (AlgebraicGeometry.strictLocalRingCocone B S hS s)

@[simp]
lemma strictLocalRingGermCocone_pt :
    (strictLocalRingGermCocone s B hS).pt = strictLocalRing B S hS s := rfl

/-- The germ map at an étale neighbourhood `U` is the pullback to any étale neighbourhood `V`
of the bounded small étale site mapping to `U`, followed by the germ at `V`. -/
lemma strictLocalRingGermCocone_ι_app (U : EtaleNeighborhood s)
    (V : (geometricPointSitePoint B S hS s).fiber.Elements)
    (f : (ofGeometricPointSitePointFiberElements B hS s).obj V ⟶ U) :
    (strictLocalRingGermCocone s B hS).ι.app (op U) =
      (functionsDiagram s).map f.op ≫
        (AlgebraicGeometry.strictLocalRingCocone B S hS s).ι.app (op V) :=
  Functor.Final.extendCocone_obj_ι_app' (F := (ofGeometricPointSitePointFiberElements B hS s).op)
    _ f.op

/-- The strict local ring of `S` at `s` is the colimit of the rings of functions `Γ(U, 𝒪_U)`
over all étale neighbourhoods `(U, u)` of `s`. -/
def isColimitStrictLocalRingGermCocone : IsColimit (strictLocalRingGermCocone s B hS) :=
  (Functor.Final.isColimitExtendCoconeEquiv
    (ofGeometricPointSitePointFiberElements B hS s).op _).symm
    (AlgebraicGeometry.isColimitStrictLocalRingCocone B S hS s)

/-- The germ maps `Γ(U, 𝒪_U) ⟶ 𝒪̃_{S,s}` from the rings of functions on the connected affine
étale neighbourhoods of `s` to the strict local ring. -/
def connectedAffineStrictLocalRingCocone :
    Cocone ((IsConnectedAffine (s := s)).ι.op ⋙ functionsDiagram s) :=
  (strictLocalRingGermCocone s B hS).whisker (IsConnectedAffine (s := s)).ι.op

@[simp]
lemma connectedAffineStrictLocalRingCocone_ι_app
    (U : (IsConnectedAffine (s := s)).FullSubcategory) :
    (connectedAffineStrictLocalRingCocone s B hS).ι.app (op U) =
      (strictLocalRingGermCocone s B hS).ι.app (op U.obj) := rfl

/-- **The strict local ring is a colimit over connected affine neighbourhoods.** Over a locally
noetherian scheme `S`, the canonical map from the colimit of the rings of functions
`Γ(U, 𝒪_U)` over the connected affine étale neighbourhoods `(U, u)` of a geometric point `s` to
the strict local ring `𝒪̃_{S,s}` is an isomorphism: the germ maps form a colimit cocone. -/
@[weil "lem_fk104_strict_henselization_colimit_connected_affine"]
def isColimitConnectedAffineStrictLocalRingCocone [IsLocallyNoetherian S] :
    IsColimit (connectedAffineStrictLocalRingCocone s B hS) :=
  (Functor.Final.isColimitWhiskerEquiv (IsConnectedAffine (s := s)).ι.op _).symm
    (isColimitStrictLocalRingGermCocone s B hS)

end StrictLocalRing

section Presheaf

variable {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A] (P : S.Etaleᵒᵖ ⥤ A)

instance [IsLocallyNoetherian S] :
    ((IsConnectedAffine (s := s)).ι ⋙ toFiberElements s).Initial :=
  inferInstanceAs ((IsConnectedAffine (s := s)).ι ⋙ (equivFiberElements s).functor).Initial

/-- The canonical maps `P(U) ⟶ P_s` from the values of a presheaf `P` on the small étale site on
the connected affine étale neighbourhoods `(U, u)` of `s` to its stalk at `s`. -/
def connectedAffinePresheafFiberCocone :
    Cocone (((IsConnectedAffine (s := s)).ι ⋙ forget s).op ⋙ P) :=
  ((Scheme.pointSmallEtale s.hom).presheafFiberCocone P).whisker
    ((IsConnectedAffine (s := s)).ι ⋙ toFiberElements s).op

@[simp]
lemma connectedAffinePresheafFiberCocone_pt :
    (connectedAffinePresheafFiberCocone s P).pt =
      (Scheme.pointSmallEtale s.hom).presheafFiber.obj P := rfl

/-- **Stalks are colimits over connected affine neighbourhoods.** Over a locally noetherian
scheme `S`, for every presheaf `P` on the small étale site of `S`, the canonical map from the
colimit of the values `P(U)` over the connected affine étale neighbourhoods `(U, u)` of a
geometric point `s` to the stalk of `P` at `s` is an isomorphism. -/
@[weil "lem_fk104_strict_henselization_colimit_connected_affine"]
def isColimitConnectedAffinePresheafFiberCocone [IsLocallyNoetherian S] :
    IsColimit (connectedAffinePresheafFiberCocone s P) :=
  (Functor.Final.isColimitWhiskerEquiv
    ((IsConnectedAffine (s := s)).ι ⋙ toFiberElements s).op _).symm
    ((Scheme.pointSmallEtale s.hom).isColimitPresheafFiberCocone P)

end Presheaf

end AlgebraicGeometry.GeometricPoint.EtaleNeighborhood
