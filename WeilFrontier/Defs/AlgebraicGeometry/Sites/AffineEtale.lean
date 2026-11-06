module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# The étale category of a ring

For a commutative ring `A`, the étale category `Et(A)` is the full subcategory of the category
of `A`-algebras whose objects are the `A`-algebras `B` with étale structure map `A → B`; its
morphisms are all `A`-algebra homomorphisms.

We define `Et(A)` as the opposite of Mathlib's small affine étale site of `Spec A`, so that
presheaves, sheaves and coverings on `Et(A)` are those of `Scheme.AffineEtale`, and we show
that it is equivalent to the full subcategory of étale `A`-algebras in `CommAlgCat A`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory A`: the étale category of `A`, as
  `(Scheme.AffineEtale (Spec A))ᵒᵖ`.
- `AlgebraicGeometry.EtaleCategory.IsEtaleAlgebra A`: the property of an `A`-algebra of being
  étale.
- `AlgebraicGeometry.EtaleCategory.fromAlgebras A`: the functor from étale `A`-algebras to
  `EtaleCategory A`, sending `B` to `Spec B → Spec A`.

## Main results

- `AlgebraicGeometry.EtaleCategory.algebraEquiv A`: the equivalence between the full
  subcategory of étale `A`-algebras and `EtaleCategory A`.

## Implementation notes

The source works with noetherian rings only; no noetherian hypothesis is needed here. The
`A`-algebras are taken in the same universe as `A`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The étale category of a commutative ring `A`. -/
@[weil "def_fk101_etale_category"]
abbrev EtaleCategory (A : CommRingCat.{u}) : Type (u + 1) :=
  (Scheme.AffineEtale (Spec A))ᵒᵖ

namespace EtaleCategory

variable (A : CommRingCat.{u})

/-- The étale `A`-algebras. -/
abbrev IsEtaleAlgebra : ObjectProperty (CommAlgCat.{u} A) := fun B ↦ Algebra.Etale A B

variable {A}

lemma etale_spec_map_algebraMap (B : CommAlgCat.{u} A) [Algebra.Etale A B] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr ‹_›

lemma spec_map_comp_algebraMap {B C : CommAlgCat.{u} A} (f : B ⟶ C) :
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact f.hom.commutes x

variable (A) in
/-- The object of the étale category attached to an étale `A`-algebra. -/
def ofAlgebra (B : (IsEtaleAlgebra A).FullSubcategory) : EtaleCategory A :=
  haveI : Algebra.Etale A B.obj := B.property
  haveI := etale_spec_map_algebraMap B.obj
  op (Scheme.AffineEtale.mk (Spec.map (CommRingCat.ofHom (algebraMap A B.obj))))

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism of the étale category attached to a morphism of étale `A`-algebras. -/
def homOfAlgebra {B C : (IsEtaleAlgebra A).FullSubcategory} (f : B ⟶ C) :
    ofAlgebra A B ⟶ ofAlgebra A C :=
  Quiver.Hom.op (X := unop (ofAlgebra A C)) (Y := unop (ofAlgebra A B))
    (MorphismProperty.CostructuredArrow.homMk (CommRingCat.ofHom f.hom.hom.toRingHom).op trivial
      (spec_map_comp_algebraMap f.hom))

set_option backward.isDefEq.respectTransparency.types false in
variable (A) in
/-- The functor from étale `A`-algebras to the étale category. -/
def fromAlgebras : (IsEtaleAlgebra A).FullSubcategory ⥤ EtaleCategory A where
  obj := ofAlgebra A
  map := homOfAlgebra
  map_id B := by
    apply Quiver.Hom.unop_inj
    exact MorphismProperty.CostructuredArrow.Hom.ext rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    exact MorphismProperty.CostructuredArrow.Hom.ext rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma algebraMap_comp_unop_left {B C : (IsEtaleAlgebra A).FullSubcategory}
    (g : ofAlgebra A B ⟶ ofAlgebra A C) :
    CommRingCat.ofHom (algebraMap A B.obj) ≫ g.unop.left.unop =
      CommRingCat.ofHom (algebraMap A C.obj) := by
  apply Spec.map_injective
  rw [Spec.map_comp]
  exact g.unop.w.trans (by simp; rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism of étale `A`-algebras underlying a morphism of the étale category. -/
def algHomOfHom {B C : (IsEtaleAlgebra A).FullSubcategory} (g : ofAlgebra A B ⟶ ofAlgebra A C) :
    B.obj →ₐ[A] C.obj where
  toRingHom := g.unop.left.unop.hom
  commutes' a := congr($(algebraMap_comp_unop_left g).hom a)

set_option backward.isDefEq.respectTransparency.types false in
variable (A) in
/-- The functor `fromAlgebras` is fully faithful. -/
def fullyFaithfulFromAlgebras : (fromAlgebras A).FullyFaithful where
  preimage g := ObjectProperty.homMk (CommAlgCat.ofHom (algHomOfHom g))
  map_preimage g := by
    apply Quiver.Hom.unop_inj
    exact MorphismProperty.CostructuredArrow.Hom.ext rfl
  preimage_map f := by
    apply ObjectProperty.hom_ext
    rfl

instance : (fromAlgebras A).Full := (fullyFaithfulFromAlgebras A).full

instance : (fromAlgebras A).Faithful := (fullyFaithfulFromAlgebras A).faithful

set_option backward.isDefEq.respectTransparency.types false in
/-- The étale `A`-algebra underlying an object of the étale category. -/
def toAlgebra (X : EtaleCategory A) : (IsEtaleAlgebra A).FullSubcategory :=
  letI : Algebra A X.unop.left.unop := (Spec.preimage X.unop.hom).hom.toAlgebra
  ⟨CommAlgCat.of A X.unop.left.unop, by
    have h : Etale (Spec.map (Spec.preimage X.unop.hom)) := by
      rw [Spec.map_preimage]; exact X.unop.prop
    rw [HasRingHomProperty.Spec_iff (P := @Etale)] at h
    exact RingHom.etale_algebraMap.mp h⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Every object of the étale category comes from an étale `A`-algebra. -/
def ofAlgebraToAlgebraIso (X : EtaleCategory A) : ofAlgebra A (toAlgebra X) ≅ X :=
  Iso.op (X := X.unop) (Y := unop (ofAlgebra A (toAlgebra X)))
    (MorphismProperty.CostructuredArrow.isoMk (A := X.unop) (B := unop (ofAlgebra A (toAlgebra X)))
      (Iso.refl _) trivial trivial (by
        refine (congrArg (· ≫ _) (Scheme.Spec.map_id _)).trans ?_
        exact (Category.id_comp _).trans (Spec.map_preimage X.unop.hom)))

instance : (fromAlgebras A).EssSurj where
  mem_essImage X := ⟨toAlgebra X, ⟨ofAlgebraToAlgebraIso X⟩⟩

instance : (fromAlgebras A).IsEquivalence where

variable (A) in
/-- The étale category of `A` is equivalent to the full subcategory of `A`-algebras whose
structure map is étale, with all `A`-algebra homomorphisms as morphisms. -/
@[weil "def_fk101_etale_category"]
def algebraEquiv : (IsEtaleAlgebra A).FullSubcategory ≌ EtaleCategory A :=
  (fromAlgebras A).asEquivalence
end EtaleCategory

end AlgebraicGeometry
