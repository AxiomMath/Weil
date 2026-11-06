module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.AffineEtale

/-!
# Morphisms of the étale category are étale

Let `A` be a commutative ring. Every morphism `ψ : B → C` of the étale category `Et(A)` is an
étale ring homomorphism: if `φ : A → B` and `χ : A → C` are the (étale) structure maps, then
`ψ ∘ φ = χ`, and a ring homomorphism whose composite with an étale one is étale is itself
étale.

## Main results

- `AlgebraicGeometry.EtaleCategory.etale_hom`: the ring homomorphism underlying a morphism of
  `EtaleCategory A` is étale.
- `AlgebraicGeometry.EtaleCategory.etale_algHom`: an `A`-algebra homomorphism between étale
  `A`-algebras is étale, in the presentation of `Et(A)` as a full subcategory of `A`-algebras.

## Implementation notes

The source works with noetherian rings only; no noetherian hypothesis is needed here.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

/-- Every morphism of the étale category `Et(A)` is an étale ring homomorphism: for
`g : X ⟶ Y` in `EtaleCategory A`, the ring homomorphism `g.unop.left.unop` from the ring of `X`
to the ring of `Y` is étale. -/
@[weil "lem_fk101_etale_category_morphisms_etale"]
theorem etale_hom {X Y : EtaleCategory A} (g : X ⟶ Y) : g.unop.left.unop.hom.Etale := by
  have hY : Etale Y.unop.hom := Y.unop.prop
  have hX : Etale X.unop.hom := X.unop.prop
  have : Etale (Scheme.Spec.map g.unop.left ≫ X.unop.hom) := by
    rw [g.unop.w.trans (Category.comp_id _)]; exact hY
  have h : Etale (Spec.map g.unop.left.unop) :=
    Etale.of_comp (Scheme.Spec.map g.unop.left) X.unop.hom
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp h

/-- In the presentation of `Et(A)` as the full subcategory of étale `A`-algebras, every
morphism is an étale ring homomorphism. -/
@[weil "lem_fk101_etale_category_morphisms_etale"]
theorem etale_algHom {B C : (IsEtaleAlgebra A).FullSubcategory} (f : B ⟶ C) :
    f.hom.hom.toRingHom.Etale := by
  let := f.hom.hom.toRingHom.toAlgebra
  have : Algebra.Etale A B.obj := B.property
  have : Algebra.Etale A C.obj := C.property
  have : IsScalarTower A B.obj C.obj := IsScalarTower.of_algebraMap_eq fun a ↦
    (f.hom.hom.commutes a).symm
  have : Algebra.Etale B.obj C.obj := Algebra.Etale.of_restrictScalars A B.obj C.obj
  exact RingHom.etale_algebraMap.mpr ‹_›

end EtaleCategory

end AlgebraicGeometry
