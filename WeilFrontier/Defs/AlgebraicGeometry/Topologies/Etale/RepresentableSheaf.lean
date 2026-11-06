module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf
public import Weil.Attr

/-!
# The presheaf represented by a scheme over `X` on the small étale site

Let `B` be a big étale site containing a scheme `X`. For an `X`-scheme `Z`, the presheaf
`h_Z` on the small étale site of `X` sends an étale `X`-scheme `U` to the set
`Hom_X(U, Z)` of morphisms of `X`-schemes, restriction along a morphism `V ⟶ U` being
precomposition. For a morphism of `X`-schemes `g : Z ⟶ Z'`, the morphism of presheaves
`h_g : h_Z ⟶ h_{Z'}` is postcomposition with `g`. This is the functor
`Over X ⥤ (SmallEtale B X hX)ᵒᵖ ⥤ Type u` obtained from the Yoneda embedding of the category
of `X`-schemes by restricting along the canonical full embedding of the small étale site into
the `X`-schemes.

## Main definitions

* `AlgebraicGeometry.SmallEtale.representablePresheaf`: the functor `Z ↦ h_Z`, `g ↦ h_g`.

## Main results

* `AlgebraicGeometry.SmallEtale.representablePresheaf_obj_obj`,
  `AlgebraicGeometry.SmallEtale.representablePresheaf_obj_map`,
  `AlgebraicGeometry.SmallEtale.representablePresheaf_map_app`: the sections of `h_Z` over `U`
  are the `X`-morphisms `U ⟶ Z`, restriction is precomposition, and `h_g` is postcomposition
  with `g`.
* `AlgebraicGeometry.SmallEtale.fullyFaithfulToOver`: the small étale site is a full
  subcategory of the `X`-schemes.
* `AlgebraicGeometry.SmallEtale.toOverCompRepresentablePresheafIso`: for `Z` étale over `X`,
  `h_Z` is the Yoneda presheaf of `Z` in the small étale site.

## Implementation notes

The small étale site is `AlgebraicGeometry.SmallEtale B X hX`, whose objects are étale
`X`-schemes lying in the big étale site `B`, i.e. below a size cutoff (Stacks, Tag 021B). The
category `Et(X)` of noetherian separated étale `X`-schemes of Freitag–Kiehl is a full
subcategory of it, and `h_Z` on `Et(X)` is the restriction of the presheaf defined here. The
scheme `Z` is an arbitrary `X`-scheme, not required to lie in `B` nor to be étale over `X`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.2
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- The small étale site of `X` is a full subcategory of the category of `X`-schemes. -/
def fullyFaithfulToOver : (toOver B X hX).FullyFaithful :=
  (ObjectProperty.fullyFaithfulι _).comp ((ObjectProperty.fullyFaithfulι _).over (B.obj X hX))

instance : (toOver B X hX).Full := (fullyFaithfulToOver B X hX).full

instance : (toOver B X hX).Faithful := (fullyFaithfulToOver B X hX).faithful

@[simp]
lemma toOver_obj_hom (U : SmallEtale B X hX) :
    ((toOver B X hX).obj U).hom = B.inclusion.map U.obj.hom :=
  rfl

@[simp]
lemma toOver_map_left {U V : SmallEtale B X hX} (f : U ⟶ V) :
    ((toOver B X hX).map f).left = (toScheme B X hX).map f :=
  rfl

/-- **The presheaf `h_Z`.** For an `X`-scheme `Z`, `h_Z` is the presheaf on the small étale
site of `X` sending `U` to the set `Hom_X(U, Z)`, restriction along `V ⟶ U` being
precomposition; for an `X`-morphism `g : Z ⟶ Z'`, `h_g : h_Z ⟶ h_{Z'}` is postcomposition
with `g`. -/
@[weil "not_fk102_representable_sheaf"]
def representablePresheaf : Over X ⥤ (SmallEtale B X hX)ᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (toOver B X hX).op

variable {B X hX}

/-- The sections of `h_Z` over `U` are the `X`-morphisms `U ⟶ Z`. -/
@[weil "not_fk102_representable_sheaf"]
lemma representablePresheaf_obj_obj (Z : Over X) (U : SmallEtale B X hX) :
    ((representablePresheaf B X hX).obj Z).obj (op U) = ((toOver B X hX).obj U ⟶ Z) :=
  rfl

/-- Restriction in `h_Z` along `f : V ⟶ U` is precomposition with `f`. -/
@[weil "not_fk102_representable_sheaf", simp]
lemma representablePresheaf_obj_map (Z : Over X) {U V : SmallEtale B X hX} (f : V ⟶ U)
    (φ : (toOver B X hX).obj U ⟶ Z) :
    ((representablePresheaf B X hX).obj Z).map f.op φ = (toOver B X hX).map f ≫ φ :=
  rfl

/-- The morphism `h_g : h_Z ⟶ h_{Z'}` is postcomposition with `g`. -/
@[weil "not_fk102_representable_sheaf", simp]
lemma representablePresheaf_map_app {Z Z' : Over X} (g : Z ⟶ Z') (U : SmallEtale B X hX)
    (φ : (toOver B X hX).obj U ⟶ Z) :
    ((representablePresheaf B X hX).map g).app (op U) φ = φ ≫ g :=
  rfl

variable (B X hX)

/-- For `Z` in the small étale site of `X`, the presheaf `h_Z` is the Yoneda presheaf of `Z`
in the small étale site: an `X`-morphism `U ⟶ Z` is the same as a morphism of the site. -/
def toOverCompRepresentablePresheafIso :
    toOver B X hX ⋙ representablePresheaf B X hX ≅ yoneda :=
  NatIso.ofComponents
    (fun Z ↦ NatIso.ofComponents
      (fun U ↦ ((fullyFaithfulToOver B X hX).homEquiv (X := unop U) (Y := Z)).symm.toIso)
      (fun {U V} f ↦ by
        ext (φ : (toOver B X hX).obj (unop U) ⟶ (toOver B X hX).obj Z)
        change (fullyFaithfulToOver B X hX).preimage ((toOver B X hX).map f.unop ≫ φ) =
          f.unop ≫ (fullyFaithfulToOver B X hX).preimage φ
        exact (fullyFaithfulToOver B X hX).map_injective (by
          rw [Functor.map_comp, Functor.FullyFaithful.map_preimage,
            Functor.FullyFaithful.map_preimage])))
    (fun {Z Z'} g ↦ by
      ext U (φ : (toOver B X hX).obj (unop U) ⟶ (toOver B X hX).obj Z)
      change (fullyFaithfulToOver B X hX).preimage (φ ≫ (toOver B X hX).map g) =
        (fullyFaithfulToOver B X hX).preimage φ ≫ g
      exact (fullyFaithfulToOver B X hX).map_injective (by
        rw [Functor.map_comp, Functor.FullyFaithful.map_preimage,
          Functor.FullyFaithful.map_preimage]))

@[simp]
lemma toOverCompRepresentablePresheafIso_hom_app_app (Z U : SmallEtale B X hX)
    (φ : (toOver B X hX).obj U ⟶ (toOver B X hX).obj Z) :
    (toOver B X hX).map
      (((toOverCompRepresentablePresheafIso B X hX).hom.app Z).app (op U) φ) = φ :=
  (fullyFaithfulToOver B X hX).map_preimage φ

end AlgebraicGeometry.SmallEtale

end
