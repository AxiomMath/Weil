module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.RepresentableSheaf
public import Weil.Attr

/-!
# Étale schemes as sheaves on the small étale site

Let `B` be a big étale site containing a scheme `X`. For `Z` in the small étale site of `X`,
the presheaf `h_Z : U ↦ Hom_X(U, Z)` is a sheaf for the étale topology, and the functor
`Z ↦ h_Z`, `g ↦ h_g` from the small étale site of `X` to the category of étale sheaves of sets
on it is fully faithful. Indeed `h_Z` is the Yoneda presheaf of `Z` in the small étale site,
the small étale topology is subcanonical (morphisms of schemes descend along étale coverings),
sheaves form a full subcategory of presheaves, and the Yoneda embedding is fully faithful.

## Main definitions

* `AlgebraicGeometry.SmallEtale.representableSheaf`: the functor `Z ↦ h_Z`, `g ↦ h_g`, from the
  small étale site of `X` to étale sheaves of sets on it.
* `AlgebraicGeometry.SmallEtale.representableSheafIsoYoneda`: this functor is isomorphic to the
  Yoneda embedding of the subcanonical small étale site.

## Main results

* `AlgebraicGeometry.SmallEtale.isSheaf_representablePresheaf_obj_toOver`: `h_Z` is an étale
  sheaf for every `Z` in the small étale site of `X`.
* `AlgebraicGeometry.SmallEtale.fullyFaithfulRepresentableSheaf`: the functor `Z ↦ h_Z` is
  fully faithful.

## Implementation notes

The étale site is the small étale site `AlgebraicGeometry.SmallEtale B X hX` of all étale
`X`-schemes lying in `B` (Stacks, Tag 021B), with its étale topology. The category `Et(X)` of
noetherian separated étale `X`-schemes of Freitag–Kiehl is a full subcategory of it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.2
* [Stacks Project, Tag 04JL](https://stacks.math.columbia.edu/tag/04JL)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- **`h_Z` is an étale sheaf.** For `Z` in the small étale site of `X`, the presheaf
`h_Z : U ↦ Hom_X(U, Z)` is a sheaf for the étale topology. -/
@[weil "lem_fk102_representable_embedding_fully_faithful"]
theorem isSheaf_representablePresheaf_obj_toOver (Z : SmallEtale B X hX) :
    Presheaf.IsSheaf (topology B X hX)
      ((representablePresheaf B X hX).obj ((toOver B X hX).obj Z)) :=
  (Presheaf.isSheaf_of_iso_iff ((toOverCompRepresentablePresheafIso B X hX).app Z)).2
    ((topology B X hX).yoneda.obj Z).property

/-- **The functor `Z ↦ h_Z` into étale sheaves.** It sends `Z` in the small étale site of `X`
to the étale sheaf `h_Z : U ↦ Hom_X(U, Z)`, and a morphism `g` to postcomposition `h_g`. -/
@[weil "lem_fk102_representable_embedding_fully_faithful"]
def representableSheaf : SmallEtale B X hX ⥤ Sheaf (topology B X hX) (Type u) :=
  ObjectProperty.lift _ (toOver B X hX ⋙ representablePresheaf B X hX)
    (isSheaf_representablePresheaf_obj_toOver B X hX)

variable {B X hX} in
@[simp]
lemma representableSheaf_obj_obj (Z : SmallEtale B X hX) :
    ((representableSheaf B X hX).obj Z).obj =
      (representablePresheaf B X hX).obj ((toOver B X hX).obj Z) :=
  rfl

variable {B X hX} in
@[simp]
lemma representableSheaf_map_hom {Z Z' : SmallEtale B X hX} (g : Z ⟶ Z') :
    ((representableSheaf B X hX).map g).hom =
      (representablePresheaf B X hX).map ((toOver B X hX).map g) :=
  rfl

/-- The functor `Z ↦ h_Z` is isomorphic to the Yoneda embedding of the (subcanonical) small
étale site. -/
def representableSheafIsoYoneda : representableSheaf B X hX ≅ (topology B X hX).yoneda :=
  NatIso.ofComponents
    (fun Z ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      ((toOverCompRepresentablePresheafIso B X hX).app Z))
    (fun {Z Z'} g ↦ (fullyFaithfulSheafToPresheaf _ _).map_injective (by
      simp only [Functor.map_comp]
      exact (toOverCompRepresentablePresheafIso B X hX).hom.naturality g))

/-- **The functor `Z ↦ h_Z` is fully faithful.** For `Z, Z'` in the small étale site of `X`,
`g ↦ h_g` is a bijection from `Hom_X(Z, Z')` onto the morphisms of étale sheaves
`h_Z ⟶ h_{Z'}`. -/
@[weil "lem_fk102_representable_embedding_fully_faithful"]
def fullyFaithfulRepresentableSheaf : (representableSheaf B X hX).FullyFaithful :=
  (topology B X hX).yonedaFullyFaithful.ofIso (representableSheafIsoYoneda B X hX).symm

instance : (representableSheaf B X hX).Full := (fullyFaithfulRepresentableSheaf B X hX).full

instance : (representableSheaf B X hX).Faithful :=
  (fullyFaithfulRepresentableSheaf B X hX).faithful

end AlgebraicGeometry.SmallEtale

end
