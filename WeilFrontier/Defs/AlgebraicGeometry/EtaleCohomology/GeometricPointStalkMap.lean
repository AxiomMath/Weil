module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import Weil.Attr

/-!
# Galois transport on étale stalks

Let `S` be a scheme in a big étale site `B`, let `b : Spec k ⟶ S` be a geometric point with
algebraically closed field `k`, and let `σ : k →+* k` be a field endomorphism (in the main case
an automorphism of `k` over a base field `κ`). Then `b ∘ Spec σ` is again a geometric point of
`S`, and `Spec σ` is a morphism of geometric points from `b ∘ Spec σ` to `b`. Precomposition with
`Spec σ` sends an étale neighbourhood `(U, u)` of `b` to the étale neighbourhood
`(U, u ∘ Spec σ)` of `b ∘ Spec σ`, compatibly with the forgetful functors to the small étale
site, so it induces a map of stalks
`T^b_σ : F_b ⟶ F_{b ∘ Spec σ}`,
the *transport* along `σ`. On germs it is `s_{(U,u)} ↦ s_{(U, u ∘ Spec σ)}`.

The transport is the canonical map of stalk functors along a morphism of geometric points,
`AlgebraicGeometry.geometricPointStalkMap` [Stacks, Tag 04FN], applied to the morphism of
geometric points given by `Spec σ`; it is therefore natural in the presheaf and an isomorphism.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.precompSpec`: the geometric point `b ∘ Spec σ`.
* `AlgebraicGeometry.GeometricPoint.specHom`: `Spec σ` as a morphism of geometric points
  `b ∘ Spec σ ⟶ b`.
* `AlgebraicGeometry.galoisTransport`: the transport `T^b_σ : F_b ⟶ F_{b ∘ Spec σ}`, as a
  natural transformation of étale stalk functors on presheaves with values in any category
  with the relevant colimits (sets and abelian groups in particular).

## Main results

* `AlgebraicGeometry.galoisTransport_germ`: on germs, `T^b_σ (s_{(U,u)}) = s_{(U, u ∘ Spec σ)}`.
* `AlgebraicGeometry.ι_galoisTransport_app`: the same rule in morphism form, for any
  coefficient category.
* `AlgebraicGeometry.galoisTransport_naturality`: the transport commutes with morphisms of
  presheaves.
* `AlgebraicGeometry.galoisTransport_isIso`: the transport is an isomorphism.

## Implementation notes

The source treats sheaves of sets or of abelian groups on the small étale site of `X₀` and
automorphisms `σ ∈ Aut(k/κ)`. The definition here is stated for presheaves on the small étale
site `AlgebraicGeometry.SmallEtale B S hS` with values in an arbitrary category having the
colimits defining stalks, and for an arbitrary ring endomorphism `σ` of `k`; a sheaf `F` enters
through its underlying presheaf `F.val`, and an automorphism `σ : k ≃ₐ[κ] k` through
`σ.toAlgHom.toRingHom`. The condition `σ ∈ Aut(k/κ)` is only needed for `b ∘ Spec σ` to be a
`κ`-point again; the stalk map itself does not use it.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.4][freitagkiehl1988]
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

namespace GeometricPoint

variable {S : Scheme.{u}}

/-- The geometric point `b ∘ Spec σ` obtained from a geometric point `b` by precomposing with
the spectrum of an endomorphism `σ` of its field. -/
abbrev precompSpec (b : GeometricPoint S) (σ : b.residueField →+* b.residueField) :
    GeometricPoint S where
  residueField := b.residueField
  hom := Spec.map (CommRingCat.ofHom σ) ≫ b.hom

/-- `Spec σ` as a morphism of geometric points from `b ∘ Spec σ` to `b`. -/
def specHom (b : GeometricPoint S) (σ : b.residueField →+* b.residueField) :
    Hom (b.precompSpec σ) b where
  hom := Spec.map (CommRingCat.ofHom σ)
  comm := rfl

@[simp]
lemma specHom_hom (b : GeometricPoint S) (σ : b.residueField →+* b.residueField) :
    (b.specHom σ).hom = Spec.map (CommRingCat.ofHom σ) := rfl

end GeometricPoint

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The Galois transport `T^b_σ : F_b ⟶ F_{b ∘ Spec σ}` on étale stalks, induced by the functor
`(U, u) ↦ (U, u ∘ Spec σ)` of étale neighbourhoods; natural in the presheaf `F`. -/
@[weil "def_fk204_galois_transport_on_stalk"]
def galoisTransport (b : GeometricPoint S) (σ : b.residueField →+* b.residueField)
    (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS b).Elementsᵒᵖ A]
    [HasColimitsOfShape (geometricPointFiber B S hS (b.precompSpec σ)).Elementsᵒᵖ A] :
    etaleStalkPresheafFunctor B S hS b A ⟶
      etaleStalkPresheafFunctor B S hS (b.precompSpec σ) A :=
  geometricPointStalkMap B S hS (b.specHom σ) A

variable {B S hS}

/-- The neighbourhood `(U, u ∘ Spec σ)` of `b ∘ Spec σ` attached to a neighbourhood `(U, u)`
of `b` has the same underlying étale scheme and the lift `Spec σ ≫ u`. -/
@[simp]
lemma neighborhoodFunctor_specHom_obj (b : GeometricPoint S)
    (σ : b.residueField →+* b.residueField) (U : (geometricPointFiber B S hS b).Elements) :
    (neighborhoodFunctor B S hS (b.specHom σ)).obj U =
      ⟨U.1, ⟨Spec.map (CommRingCat.ofHom σ) ≫ U.2.1, by
        rw [Category.assoc, U.2.2]⟩⟩ := rfl

/-- The germ rule for the transport, in morphism form and for any coefficient category: the
germ at `(U, u)` followed by `T^b_σ` is the germ at `(U, u ∘ Spec σ)`. -/
@[reassoc (attr := simp)]
lemma ι_galoisTransport_app (b : GeometricPoint S) (σ : b.residueField →+* b.residueField)
    (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS b).Elementsᵒᵖ A]
    [HasColimitsOfShape (geometricPointFiber B S hS (b.precompSpec σ)).Elementsᵒᵖ A]
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ A) (U : (geometricPointFiber B S hS b).Elementsᵒᵖ) :
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS b)).op ⋙ F) U ≫
        (galoisTransport B S hS b σ A).app F =
      colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B S hS (b.precompSpec σ))).op ⋙ F)
        ((neighborhoodFunctor B S hS (b.specHom σ)).op.obj U) :=
  colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B S hS (b.precompSpec σ))).op ⋙ F)
    (neighborhoodFunctor B S hS (b.specHom σ)).op U

/-- **Germ rule.** For a set-valued presheaf `F`, a neighbourhood `(U, u)` of `b` and a section
`s ∈ F(U)`, the transport sends the germ `s_{(U,u)}` to the germ `s_{(U, u ∘ Spec σ)}`. -/
@[weil "def_fk204_galois_transport_on_stalk", simp]
lemma galoisTransport_germ (b : GeometricPoint S) (σ : b.residueField →+* b.residueField)
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ Type u) (U : (geometricPointFiber B S hS b).Elementsᵒᵖ)
    (s : F.obj (op U.unop.1)) :
    (galoisTransport B S hS b σ (Type u)).app F
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS b)).op ⋙ F) U s) =
      colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B S hS (b.precompSpec σ))).op ⋙ F)
        ((neighborhoodFunctor B S hS (b.specHom σ)).op.obj U) s :=
  geometricPointStalkMap_germ B S hS (b.specHom σ) F U s

/-- The transport commutes with morphisms of presheaves: `ψ_{b ∘ Spec σ} ∘ T^b_σ = T^b_σ ∘ ψ_b`. -/
@[reassoc]
lemma galoisTransport_naturality (b : GeometricPoint S) (σ : b.residueField →+* b.residueField)
    (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS b).Elementsᵒᵖ A]
    [HasColimitsOfShape (geometricPointFiber B S hS (b.precompSpec σ)).Elementsᵒᵖ A]
    {F G : (SmallEtale B S hS)ᵒᵖ ⥤ A} (ψ : F ⟶ G) :
    (etaleStalkPresheafFunctor B S hS b A).map ψ ≫ (galoisTransport B S hS b σ A).app G =
      (galoisTransport B S hS b σ A).app F ≫
        (etaleStalkPresheafFunctor B S hS (b.precompSpec σ) A).map ψ :=
  (galoisTransport B S hS b σ A).naturality ψ

/-- The transport is an isomorphism of stalk functors. -/
instance galoisTransport_isIso (b : GeometricPoint S) (σ : b.residueField →+* b.residueField)
    (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS b).Elementsᵒᵖ A]
    [HasColimitsOfShape (geometricPointFiber B S hS (b.precompSpec σ)).Elementsᵒᵖ A] :
    IsIso (galoisTransport B S hS b σ A) :=
  geometricPointStalkMap_isIso B S hS (b.specHom σ) A

/-- The transport is an isomorphism on the stalk of each presheaf. -/
instance galoisTransport_app_isIso (b : GeometricPoint S) (σ : b.residueField →+* b.residueField)
    (A : Type v) [Category.{w} A]
    [HasColimitsOfShape (geometricPointFiber B S hS b).Elementsᵒᵖ A]
    [HasColimitsOfShape (geometricPointFiber B S hS (b.precompSpec σ)).Elementsᵒᵖ A]
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    IsIso ((galoisTransport B S hS b σ A).app F) :=
  inferInstance

end AlgebraicGeometry

end
