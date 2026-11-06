module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Sites.EtaleCategoryFibreProduct

/-!
# Compatibility of sections via the tensor product

Let `A` be a commutative ring, `F` a presheaf on the category of étale `A`-algebras (a covariant
functor to types), and `g₁ : B ⟶ C₁`, `g₂ : B ⟶ C₂` morphisms of étale `A`-algebras. Two
sections `s₁ ∈ F(C₁)` and `s₂ ∈ F(C₂)` have the same image in `F(C₁ ⊗[B] C₂)` if and only if
`F(u)(s₁) = F(v)(s₂)` for every étale `A`-algebra `D` and all `u : C₁ ⟶ D`, `v : C₂ ⟶ D` with
`g₁ ≫ u = g₂ ≫ v`. This holds because `C₁ ⊗[B] C₂`, with its canonical maps, is a pushout of
`g₁` and `g₂` among étale `A`-algebras.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.tensorProductLift`: the morphism `C₁ ⊗[B] C₂ ⟶ D`,
  `c₁ ⊗ c₂ ↦ u c₁ * v c₂`, induced by `u` and `v` with `g₁ ≫ u = g₂ ≫ v`.

## Main results

- `AlgebraicGeometry.EtaleCategory.map_inl_eq_map_inr_iff`: the compatibility criterion above.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory TensorProduct

namespace AlgebraicGeometry.EtaleCategory

variable {A : CommRingCat.{u}} {B C₁ C₂ D : (IsEtaleAlgebra A).FullSubcategory}

/-- The morphism `C₁ ⊗[B] C₂ ⟶ D`, `c₁ ⊗ c₂ ↦ u c₁ * v c₂`, induced by morphisms
`u : C₁ ⟶ D` and `v : C₂ ⟶ D` of étale `A`-algebras with `g₁ ≫ u = g₂ ≫ v`. -/
def tensorProductLift (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) (u : C₁ ⟶ D) (v : C₂ ⟶ D)
    (h : g₁ ≫ u = g₂ ≫ v) : tensorProduct g₁ g₂ ⟶ D :=
  letI := algebraOfHom g₁
  letI := algebraOfHom g₂
  letI := algebraOfHom (g₁ ≫ u)
  haveI := isScalarTower_of_hom g₁
  haveI := isScalarTower_of_hom g₂
  haveI := isScalarTower_of_hom (g₁ ≫ u)
  let u' : C₁.obj →ₐ[B.obj] D.obj :=
    { u.hom.hom.toRingHom with commutes' := fun _ ↦ rfl }
  let v' : C₂.obj →ₐ[B.obj] D.obj :=
    { v.hom.hom.toRingHom with
      commutes' := fun b ↦ by
        change (g₂ ≫ v).hom.hom b = (g₁ ≫ u).hom.hom b
        rw [h] }
  ObjectProperty.homMk (CommAlgCat.ofHom
    ((Algebra.TensorProduct.productMap u' v').restrictScalars A))

lemma inl_comp_tensorProductLift (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) (u : C₁ ⟶ D) (v : C₂ ⟶ D)
    (h : g₁ ≫ u = g₂ ≫ v) : inl g₁ g₂ ≫ tensorProductLift g₁ g₂ u v h = u := by
  apply ObjectProperty.hom_ext
  ext c
  change u.hom.hom c * v.hom.hom 1 = u.hom.hom c
  rw [map_one, mul_one]

lemma inr_comp_tensorProductLift (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) (u : C₁ ⟶ D) (v : C₂ ⟶ D)
    (h : g₁ ≫ u = g₂ ≫ v) : inr g₁ g₂ ≫ tensorProductLift g₁ g₂ u v h = v := by
  apply ObjectProperty.hom_ext
  ext c
  change u.hom.hom 1 * v.hom.hom c = v.hom.hom c
  rw [map_one, one_mul]

/-- Two sections `s₁ ∈ F(C₁)`, `s₂ ∈ F(C₂)` of a presheaf on the étale `A`-algebras agree in
`F(C₁ ⊗[B] C₂)` if and only if `F(u)(s₁) = F(v)(s₂)` for all `u : C₁ ⟶ D`, `v : C₂ ⟶ D` with
`g₁ ≫ u = g₂ ≫ v`. -/
@[weil "lem_fk101_compatibility_via_tensor"]
theorem map_inl_eq_map_inr_iff (F : (IsEtaleAlgebra A).FullSubcategory ⥤ Type v)
    (g₁ : B ⟶ C₁) (g₂ : B ⟶ C₂) (s₁ : F.obj C₁) (s₂ : F.obj C₂) :
    F.map (inl g₁ g₂) s₁ = F.map (inr g₁ g₂) s₂ ↔
      ∀ (D : (IsEtaleAlgebra A).FullSubcategory) (u : C₁ ⟶ D) (v : C₂ ⟶ D),
        g₁ ≫ u = g₂ ≫ v → F.map u s₁ = F.map v s₂ := by
  refine ⟨fun hs D u v h ↦ ?_, fun H ↦ H _ _ _ (comp_inl_eq_comp_inr g₁ g₂)⟩
  calc F.map u s₁ = F.map (inl g₁ g₂ ≫ tensorProductLift g₁ g₂ u v h) s₁ := by
        rw [inl_comp_tensorProductLift]
    _ = F.map (inr g₁ g₂ ≫ tensorProductLift g₁ g₂ u v h) s₂ := by
        rw [Functor.map_comp_apply, Functor.map_comp_apply, hs]
    _ = F.map v s₂ := by rw [inr_comp_tensorProductLift]

end AlgebraicGeometry.EtaleCategory
