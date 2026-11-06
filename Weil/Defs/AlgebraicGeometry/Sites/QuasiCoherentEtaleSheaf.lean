module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.EtalePresheafFk101
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The presheaf `M~` on the étale category of a ring

Let `A` be a commutative ring and `M` an `A`-module. The presheaf of abelian groups `M~` on the
étale category `Et(A)` sends an étale `A`-algebra `B` to `M ⊗_A B`, and a morphism
`f : B → C` of étale `A`-algebras to `id_M ⊗ f : M ⊗_A B → M ⊗_A C`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.toAlgebras A`: the functor from `Et(A)` to the category of
  étale `A`-algebras, inverse to `AlgebraicGeometry.EtaleCategory.fromAlgebras A`.
- `AlgebraicGeometry.EtaleCategory.tensorAlgebras M`: the functor `B ↦ M ⊗_A B` from étale
  `A`-algebras to abelian groups.
- `AlgebraicGeometry.EtaleCategory.tensorPresheaf M`: the presheaf `M~` on `Et(A)`.

## Main results

- `AlgebraicGeometry.EtaleCategory.tensorPresheaf_obj`,
  `AlgebraicGeometry.EtaleCategory.tensorPresheaf_map_tmul`: the value of `M~` on an
  object `X` of `Et(A)` is `M ⊗_A B` for the étale `A`-algebra `B` underlying `X`, and a
  morphism acts by `m ⊗ b ↦ m ⊗ f b`.
- `AlgebraicGeometry.EtaleCategory.fromAlgebrasCompTensorPresheafIso M`: on étale
  `A`-algebras, `M~` is the functor `B ↦ M ⊗_A B`.

## Implementation notes

`Et(A)` is the opposite of Mathlib's affine étale site of `Spec A`, so an object `X` is an
affine scheme étale over `Spec A`, and its étale `A`-algebra is the ring of `X` with the
structure map recovered from `X → Spec A` (`AlgebraicGeometry.EtaleCategory.toAlgebra`). The
presheaf is the composite of the functor `X ↦` (its algebra) with `B ↦ M ⊗_A B`.

The source works over a noetherian ring; no noetherian hypothesis is needed for the definition.

The presheaf `T ↦ Γ(T, T⁺ M̃)` on schemes over `Spec A` (`AlgebraicGeometry.quasiCoherentPresheaf`,
[Stacks, Tag 03DS]) restricts on `Spec B` to a group only isomorphic to `M ⊗_A B`; the presheaf
here is the tensor product itself, as in the source.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

variable (A) in
set_option backward.isDefEq.respectTransparency.types false in
/-- The functor from the étale category of `A` to the étale `A`-algebras: an affine scheme
étale over `Spec A` is sent to its ring of global sections, with its `A`-algebra structure. -/
def toAlgebras : EtaleCategory A ⥤ (IsEtaleAlgebra A).FullSubcategory where
  obj := toAlgebra
  map {X Y} g := (fullyFaithfulFromAlgebras A).preimage
    ((ofAlgebraToAlgebraIso X).hom ≫ g ≫ (ofAlgebraToAlgebraIso Y).inv)
  map_id X := by
    apply (fullyFaithfulFromAlgebras A).map_injective
    simp
  map_comp f g := by
    apply (fullyFaithfulFromAlgebras A).map_injective
    simp

/-- The `A`-algebra homomorphism underlying the image of a morphism of `Et(A)`. -/
lemma toAlgebras_map_hom_apply {X Y : EtaleCategory A} (g : X ⟶ Y)
    (x : (toAlgebra X).obj) :
    ((toAlgebras A).map g).hom.hom x = g.unop.left.unop.hom x := rfl

variable (M : Type u) [AddCommGroup M] [Module A M]

/-- The functor `B ↦ M ⊗_A B` from étale `A`-algebras to abelian groups, a morphism `f` acting
by `id_M ⊗ f`. -/
def tensorAlgebras : (IsEtaleAlgebra A).FullSubcategory ⥤ AddCommGrpCat.{u} where
  obj B := AddCommGrpCat.of (M ⊗[A] B.obj)
  map f := AddCommGrpCat.ofHom (LinearMap.lTensor M f.hom.hom.toLinearMap).toAddMonoidHom
  map_id B := by
    ext x
    simp
  map_comp f g := by
    ext x
    simp [LinearMap.lTensor_comp_apply]

@[simp]
lemma tensorAlgebras_obj (B : (IsEtaleAlgebra A).FullSubcategory) :
    (tensorAlgebras M).obj B = AddCommGrpCat.of (M ⊗[A] B.obj) := rfl

@[simp]
lemma tensorAlgebras_map_tmul {B C : (IsEtaleAlgebra A).FullSubcategory} (f : B ⟶ C) (m : M)
    (b : B.obj) : (tensorAlgebras M).map f (m ⊗ₜ b) = m ⊗ₜ f.hom.hom b := rfl

/-- **The presheaf `M~` on `Et(A)`.** For an `A`-module `M`, the presheaf of abelian groups on
the étale category of `A` sending an étale `A`-algebra `B` to `M ⊗_A B`, a morphism
`f : B → C` acting by `id_M ⊗ f`. -/
@[weil "def_fk101_quasi_coherent_etale_sheaf"]
def tensorPresheaf : Presheaf A AddCommGrpCat.{u} :=
  toAlgebras A ⋙ tensorAlgebras M

/-- The value of `M~` on an object of `Et(A)` is `M ⊗_A B`, `B` its étale `A`-algebra. -/
@[weil "def_fk101_quasi_coherent_etale_sheaf"]
lemma tensorPresheaf_obj (X : EtaleCategory A) :
    (tensorPresheaf M).obj X = AddCommGrpCat.of (M ⊗[A] (toAlgebra X).obj) := rfl

/-- A morphism `f : B → C` of `Et(A)` acts on `M~` by `id_M ⊗ f`. -/
@[weil "def_fk101_quasi_coherent_etale_sheaf"]
lemma tensorPresheaf_map_tmul {X Y : EtaleCategory A} (g : X ⟶ Y) (m : M)
    (b : (toAlgebra X).obj) :
    (tensorPresheaf M).map g (m ⊗ₜ b) =
      m ⊗ₜ[A] (((toAlgebras A).map g).hom.hom b : (toAlgebra Y).obj) := rfl

variable (A) in
set_option backward.isDefEq.respectTransparency.types false in
/-- Going from étale `A`-algebras to `Et(A)` and back is isomorphic to the identity. -/
def fromAlgebrasCompToAlgebrasIso : fromAlgebras A ⋙ toAlgebras A ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun B ↦ (fullyFaithfulFromAlgebras A).preimageIso (ofAlgebraToAlgebraIso (ofAlgebra A B)))
    (fun {B C} f ↦ by
      apply ObjectProperty.hom_ext
      rfl)

/-- On étale `A`-algebras, `M~` is the functor `B ↦ M ⊗_A B`. -/
def fromAlgebrasCompTensorPresheafIso :
    fromAlgebras A ⋙ tensorPresheaf M ≅ tensorAlgebras M :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fromAlgebrasCompToAlgebrasIso A) (tensorAlgebras M) ≪≫
    Functor.leftUnitor _

/-- The identification of `M~(B)` with `M ⊗_A B` is the identity on pure tensors. -/
lemma fromAlgebrasCompTensorPresheafIso_hom_app_tmul
    (B : (IsEtaleAlgebra A).FullSubcategory) (m : M) (b : (toAlgebra (ofAlgebra A B)).obj) :
    (fromAlgebrasCompTensorPresheafIso M).hom.app B (m ⊗ₜ b) =
      m ⊗ₜ[A] (show B.obj from b) := rfl

end EtaleCategory

end AlgebraicGeometry
