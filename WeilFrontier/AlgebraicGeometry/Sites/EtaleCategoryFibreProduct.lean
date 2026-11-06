module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.RingTheory.Etale.Basic

/-!
# Fibre products in the étale category

Let `A` be a commutative ring and let `g₁ : B → C₁`, `g₂ : B → C₂` be morphisms of étale
`A`-algebras. Then `C₁ ⊗[B] C₂` is again an étale `A`-algebra, and the canonical maps
`c ↦ c ⊗ 1` and `c ↦ 1 ⊗ c` are morphisms of étale `A`-algebras.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.tensorProduct g₁ g₂`: the étale `A`-algebra `C₁ ⊗[B] C₂`.
- `AlgebraicGeometry.EtaleCategory.inl g₁ g₂`, `AlgebraicGeometry.EtaleCategory.inr g₁ g₂`: the
  canonical morphisms `C₁ ⟶ C₁ ⊗[B] C₂` and `C₂ ⟶ C₁ ⊗[B] C₂`.

## Main results

- `Algebra.Etale.tensorProduct_of_isScalarTower`: if `B`, `C₁`, `C₂` are étale `A`-algebras and
  `C₁`, `C₂` are `B`-algebras compatibly with `A`, then `C₁ ⊗[B] C₂` is étale over `A`.

## Implementation notes

The source assumes all rings noetherian; no noetherian hypothesis is needed here.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TensorProduct

namespace Algebra.Etale

variable (A B C₁ C₂ : Type*) [CommRing A] [CommRing B] [CommRing C₁] [CommRing C₂]
  [Algebra A B] [Algebra A C₁] [Algebra A C₂] [Algebra B C₁] [Algebra B C₂]
  [IsScalarTower A B C₁] [IsScalarTower A B C₂]

/-- If `B`, `C₁` and `C₂` are étale `A`-algebras and `C₁`, `C₂` are `B`-algebras compatibly
with `A`, then `C₁ ⊗[B] C₂` is an étale `A`-algebra. -/
@[weil "lem_fk101_etale_category_fibre_product"]
theorem tensorProduct_of_isScalarTower [Algebra.Etale A B] [Algebra.Etale A C₁]
    [Algebra.Etale A C₂] : Algebra.Etale A (C₁ ⊗[B] C₂) := by
  have : Algebra.Etale B C₂ := Algebra.Etale.of_restrictScalars A B C₂
  have : Algebra.Etale C₁ (C₁ ⊗[B] C₂) := Algebra.Etale.baseChange B C₂ C₁
  exact Algebra.Etale.comp A C₁ (C₁ ⊗[B] C₂)

end Algebra.Etale

namespace AlgebraicGeometry.EtaleCategory

variable {A : CommRingCat.{u}} {B C₁ C₂ : (IsEtaleAlgebra A).FullSubcategory}

/-- The `B`-algebra structure on the target of a morphism of étale `A`-algebras. -/
abbrev algebraOfHom (g : B ⟶ C₁) : Algebra B.obj C₁.obj := g.hom.hom.toAlgebra

lemma isScalarTower_of_hom (g : B ⟶ C₁) :
    letI := algebraOfHom g
    IsScalarTower A B.obj C₁.obj := by
  let _ : Algebra B.obj C₁.obj := algebraOfHom g
  exact IsScalarTower.of_algebraMap_eq fun a ↦ (g.hom.hom.commutes a).symm

/-- The tensor product `C₁ ⊗[B] C₂` of two morphisms `g₁ : B ⟶ C₁`, `g₂ : B ⟶ C₂` of étale
`A`-algebras, as an étale `A`-algebra. -/
@[weil "lem_fk101_etale_category_fibre_product"]
def tensorProduct (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) : (IsEtaleAlgebra A).FullSubcategory :=
  letI := algebraOfHom g₁
  letI := algebraOfHom g₂
  haveI := isScalarTower_of_hom g₁
  haveI := isScalarTower_of_hom g₂
  haveI : Algebra.Etale A B.obj := B.property
  haveI : Algebra.Etale A C₁.obj := C₁.property
  haveI : Algebra.Etale A C₂.obj := C₂.property
  ⟨CommAlgCat.of A (C₁.obj ⊗[B.obj] C₂.obj),
    Algebra.Etale.tensorProduct_of_isScalarTower A B.obj C₁.obj C₂.obj⟩

/-- The canonical morphism `C₁ ⟶ C₁ ⊗[B] C₂`, `c ↦ c ⊗ 1`. -/
@[weil "lem_fk101_etale_category_fibre_product"]
def inl (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) : C₁ ⟶ tensorProduct g₁ g₂ :=
  letI := algebraOfHom g₁
  letI := algebraOfHom g₂
  haveI := isScalarTower_of_hom g₁
  ObjectProperty.homMk (CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft (S := A)))

/-- The canonical morphism `C₂ ⟶ C₁ ⊗[B] C₂`, `c ↦ 1 ⊗ c`. -/
@[weil "lem_fk101_etale_category_fibre_product"]
def inr (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) : C₂ ⟶ tensorProduct g₁ g₂ :=
  letI := algebraOfHom g₁
  letI := algebraOfHom g₂
  haveI := isScalarTower_of_hom g₁
  haveI := isScalarTower_of_hom g₂
  ObjectProperty.homMk (CommAlgCat.ofHom
    ((Algebra.TensorProduct.includeRight (R := B.obj) (A := C₁.obj) (B := C₂.obj)).restrictScalars
      A))

lemma inl_apply (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) (c : C₁.obj) :
    letI := algebraOfHom g₁
    letI := algebraOfHom g₂
    (inl g₁ g₂).hom.hom c = (c ⊗ₜ[B.obj] (1 : C₂.obj) : C₁.obj ⊗[B.obj] C₂.obj) := rfl

lemma inr_apply (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) (c : C₂.obj) :
    letI := algebraOfHom g₁
    letI := algebraOfHom g₂
    (inr g₁ g₂).hom.hom c = ((1 : C₁.obj) ⊗ₜ[B.obj] c : C₁.obj ⊗[B.obj] C₂.obj) := rfl

/-- The square formed by `g₁`, `g₂`, `inl` and `inr` commutes. -/
lemma comp_inl_eq_comp_inr (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) :
    g₁ ≫ inl g₁ g₂ = g₂ ≫ inr g₁ g₂ := by
  let _ := algebraOfHom g₁
  let _ := algebraOfHom g₂
  apply ObjectProperty.hom_ext
  ext b
  change (algebraMap B.obj C₁.obj b) ⊗ₜ[B.obj] (1 : C₂.obj) = 1 ⊗ₜ algebraMap B.obj C₂.obj b
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end AlgebraicGeometry.EtaleCategory
