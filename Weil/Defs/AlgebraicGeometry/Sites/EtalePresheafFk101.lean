module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.AffineEtale

/-!
# Presheaves on the étale category of a ring

For a commutative ring `A`, a presheaf on the étale category `Et(A)` with values in a category
`C` (sets, abelian groups, ...) is a covariant functor `Et(A) ⥤ C`; a morphism of presheaves is a
natural transformation. For a morphism `f : B ⟶ C` of `Et(A)` and a section `s ∈ F(B)`, the
restriction `s|_C` is `F.map f s`.

Since `Et(A)` is the opposite of the small affine étale site of `Spec A`, a presheaf on `Et(A)`
is the same thing as a presheaf on `Scheme.AffineEtale (Spec A)`; and since `Et(A)` is
equivalent to the category of étale `A`-algebras, presheaves on `Et(A)` are equivalent to
covariant functors on étale `A`-algebras.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.Presheaf A C`: the category of presheaves on `Et(A)` with
  values in `C`, i.e. the functor category `EtaleCategory A ⥤ C`.
- `AlgebraicGeometry.EtaleCategory.Presheaf.equivAlgebras A C`: the equivalence between
  presheaves on `Et(A)` and functors from the full subcategory of étale `A`-algebras to `C`.

## Main results

- `AlgebraicGeometry.EtaleCategory.Presheaf.map_id_apply`,
  `AlgebraicGeometry.EtaleCategory.Presheaf.map_comp_apply`: restriction of sections of a
  presheaf of sets is functorial.
- `AlgebraicGeometry.EtaleCategory.Presheaf.naturality_apply`: a morphism of presheaves of sets
  commutes with restriction.

## Implementation notes

No new structure is introduced: a presheaf is an object of Mathlib's functor category, a morphism
of presheaves is a natural transformation, and `s|_C` is written `F.map f s`. By definition
`EtaleCategory.Presheaf A C` is `(Scheme.AffineEtale (Spec A))ᵒᵖ ⥤ C`, so the presheaves,
sheaves and topology of Mathlib's affine étale site apply to it unchanged.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

/-- **Presheaves on `Et(A)`.** A presheaf on the étale category of `A` with values in a category
`C` is a covariant functor `Et(A) ⥤ C`; morphisms of presheaves are natural transformations. -/
@[weil "def_fk101_etale_presheaf"]
abbrev Presheaf (A : CommRingCat.{u}) (C : Type v) [Category.{w} C] : Type _ :=
  EtaleCategory A ⥤ C

namespace Presheaf

variable {A : CommRingCat.{u}}

/-- A presheaf on `Et(A)` is a presheaf on Mathlib's small affine étale site of `Spec A`. -/
lemma eq_affineEtale (C : Type v) [Category.{w} C] :
    Presheaf A C = ((Scheme.AffineEtale (Spec A))ᵒᵖ ⥤ C) := rfl

variable (A) in
/-- Presheaves on `Et(A)` with values in `C` are equivalent to covariant functors from the
category of étale `A`-algebras (with all `A`-algebra homomorphisms) to `C`. -/
@[weil "def_fk101_etale_presheaf"]
def equivAlgebras (C : Type v) [Category.{w} C] :
    Presheaf A C ≌ ((EtaleCategory.IsEtaleAlgebra A).FullSubcategory ⥤ C) :=
  (algebraEquiv A).symm.congrLeft

@[simp]
lemma equivAlgebras_functor_obj (C : Type v) [Category.{w} C] (F : Presheaf A C) :
    (equivAlgebras A C).functor.obj F = fromAlgebras A ⋙ F := rfl

/-- The section of `F` at an étale `A`-algebra `B`. -/
lemma equivAlgebras_functor_obj_obj (C : Type v) [Category.{w} C] (F : Presheaf A C)
    (B : (EtaleCategory.IsEtaleAlgebra A).FullSubcategory) :
    ((equivAlgebras A C).functor.obj F).obj B = F.obj (ofAlgebra A B) := rfl

/-- Restriction along the identity is the identity. -/
lemma map_id_apply (F : Presheaf A (Type v)) (B : EtaleCategory A) (s : F.obj B) :
    F.map (𝟙 B) s = s := by
  simp

/-- Restriction is functorial: `s|_D = (s|_C)|_D`. -/
lemma map_comp_apply (F : Presheaf A (Type v)) {B C D : EtaleCategory A} (f : B ⟶ C)
    (g : C ⟶ D) (s : F.obj B) : F.map (f ≫ g) s = F.map g (F.map f s) := by
  simp

/-- A morphism of presheaves of sets commutes with restriction. -/
lemma naturality_apply {F G : Presheaf A (Type v)} (φ : F ⟶ G) {B C : EtaleCategory A}
    (f : B ⟶ C) (s : F.obj B) : φ.app C (F.map f s) = G.map f (φ.app B s) :=
  NatTrans.naturality_apply φ f s

end Presheaf

end EtaleCategory

end AlgebraicGeometry
