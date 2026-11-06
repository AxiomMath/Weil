module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Descent.FpqcFullyFaithful.AmitsurEqualizer
public import Weil.AlgebraicGeometry.Sites.EtaleSheaf
public import Weil.AlgebraicGeometry.Sites.EtaleCategoryFibreProduct
public import Weil.Defs.AlgebraicGeometry.Sites.QuasiCoherentEtaleSheaf
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The presheaf `M~` on the étale category is a sheaf

Let `A` be a commutative ring and `M` an `A`-module. The presheaf `M~ : B ↦ M ⊗_A B` on the étale
category `Et(A)` is a sheaf of abelian groups for the étale topology. We check the sheaf axioms:
`M ⊗_A -` commutes with finite products, and for a faithfully flat morphism `B → C` of étale
`A`-algebras the sequence `M ⊗_A B → M ⊗_A C ⇉ M ⊗_A (C ⊗_B C)` is an equalizer, by faithfully
flat descent applied to the `B`-module `B ⊗_A M`.

## Main definitions

- `TensorProduct.AlgebraTensorModule.cancelBaseChangeLeft`: the isomorphism
  `(S ⊗_R M) ⊗_S X ≃ M ⊗_R X` for an `R`-algebra `S` and an `S`-module `X`.

## Main results

- `Module.FaithfullyFlat.injective_lTensor_toAlgHom`,
  `Module.FaithfullyFlat.range_lTensor_toAlgHom`: for `R → S → T` with `T` faithfully flat over
  `S` and an `R`-module `M`, the map `M ⊗_R S → M ⊗_R T` is injective, with image the set where
  the two maps `M ⊗_R T → M ⊗_R (T ⊗_S T)` induced by `t ↦ t ⊗ 1` and `t ↦ 1 ⊗ t` agree.
- `AlgebraicGeometry.EtaleCategory.isSheafAxioms_tensorPresheaf`: `M~` satisfies the sheaf axioms.
- `AlgebraicGeometry.EtaleCategory.isSheaf_tensorPresheaf`: `M~` is a sheaf on `Et(A)`.

## Implementation notes

The source works over a noetherian ring; no noetherian hypothesis is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
* [Stacks, Tag 03DT]
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TensorProduct

namespace TensorProduct.AlgebraTensorModule

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (M : Type*) [AddCommGroup M] [Module R M]
  (X : Type*) [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]

/-- The isomorphism `(S ⊗[R] M) ⊗[S] X ≃ M ⊗[R] X`, `(s ⊗ m) ⊗ x ↦ m ⊗ s • x`, for an
`R`-algebra `S`, an `R`-module `M` and an `S`-module `X`. -/
noncomputable def cancelBaseChangeLeft : (S ⊗[R] M) ⊗[S] X ≃ₗ[R] M ⊗[R] X :=
  ((TensorProduct.comm S (S ⊗[R] M) X).restrictScalars R) ≪≫ₗ
    ((cancelBaseChange R S S X M).restrictScalars R) ≪≫ₗ
    TensorProduct.comm R X M

@[simp]
lemma cancelBaseChangeLeft_tmul (s : S) (m : M) (x : X) :
    cancelBaseChangeLeft R M X ((s ⊗ₜ m) ⊗ₜ x) = m ⊗ₜ (s • x) := by
  simp [cancelBaseChangeLeft]

variable {R M} {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- On `(S ⊗[R] M) ⊗[S] T` for an `S`-algebra `T`, the element `n ⊗ 1` corresponds to the image
of `n` under `M ⊗[R] S → M ⊗[R] T`. -/
lemma cancelBaseChangeLeft_tmul_one (n : S ⊗[R] M) :
    cancelBaseChangeLeft R M T (n ⊗ₜ 1) =
      (IsScalarTower.toAlgHom R S T).toLinearMap.lTensor M (TensorProduct.comm R S M n) := by
  induction n using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp [Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

end TensorProduct.AlgebraTensorModule

namespace Module.FaithfullyFlat

open TensorProduct.AlgebraTensorModule

variable (R : Type*) {S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
  [Algebra R T] [Algebra S T] [IsScalarTower R S T] (M : Type*) [AddCommGroup M] [Module R M]

variable {R M}

variable (R S T M) in
/-- For `R → S → T` with `T` faithfully flat over `S` and an `R`-module `M`, the map
`M ⊗[R] S → M ⊗[R] T` is injective. -/
theorem injective_lTensor_toAlgHom [Module.FaithfullyFlat S T] :
    Function.Injective ((IsScalarTower.toAlgHom R S T).toLinearMap.lTensor M) := by
  intro x y h
  have key (z : M ⊗[R] S) : (IsScalarTower.toAlgHom R S T).toLinearMap.lTensor M z =
      cancelBaseChangeLeft R M T ((TensorProduct.comm R M S z) ⊗ₜ 1) := by
    rw [cancelBaseChangeLeft_tmul_one]
    simp
  rw [key, key] at h
  exact (TensorProduct.comm R M S).injective
    (injective_tmul_one S T (S ⊗[R] M) ((cancelBaseChangeLeft R M T).injective h))

variable (R S T M) in
/-- **Faithfully flat descent for base changes.** For `R → S → T` with `T` faithfully flat over
`S` and an `R`-module `M`, the image of `M ⊗[R] S → M ⊗[R] T` is the set of elements on which the
two maps `M ⊗[R] T → M ⊗[R] (T ⊗[S] T)` induced by `t ↦ t ⊗ 1` and `t ↦ 1 ⊗ t` agree. -/
theorem range_lTensor_toAlgHom [Module.FaithfullyFlat S T] :
    LinearMap.range ((IsScalarTower.toAlgHom R S T).toLinearMap.lTensor M) =
      LinearMap.eqLocus
        ((Algebra.TensorProduct.includeLeft (S := R) : T →ₐ[R] T ⊗[S] T).toLinearMap.lTensor M)
        (LinearMap.lTensor M
          ((Algebra.TensorProduct.includeRight (R := S) (A := T) (B := T)).restrictScalars
            R).toLinearMap) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp]
    congr 2
    ext s
    change (algebraMap S T s) ⊗ₜ[S] (1 : T) = (1 : T) ⊗ₜ[S] algebraMap S T s
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · intro s hs
    rw [LinearMap.mem_eqLocus] at hs
    let Ψ : (S ⊗[R] M) ⊗[S] T ⊗[S] T ≃ₗ[R] M ⊗[R] (T ⊗[S] T) :=
      (TensorProduct.assoc S (S ⊗[R] M) T T).restrictScalars R ≪≫ₗ
        cancelBaseChangeLeft R M (T ⊗[S] T)
    have h1 (y : (S ⊗[R] M) ⊗[S] T) : Ψ ((TensorProduct.mk S _ T).flip 1 y) =
        (Algebra.TensorProduct.includeLeft (S := R) : T →ₐ[R] T ⊗[S] T).toLinearMap.lTensor M
          (cancelBaseChangeLeft R M T y) := by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul n t =>
        induction n using TensorProduct.induction_on with
        | zero => simp
        | tmul s m => simp [Ψ, TensorProduct.smul_tmul']
        | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy] at *
      | add x y hx hy => simp only [map_add, hx, hy]
    have h2 (y : (S ⊗[R] M) ⊗[S] T) :
        Ψ ((((TensorProduct.mk S (S ⊗[R] M) T).flip 1).rTensor T) y) =
        LinearMap.lTensor M
          ((Algebra.TensorProduct.includeRight : T →ₐ[S] T ⊗[S] T).restrictScalars R).toLinearMap
          (cancelBaseChangeLeft R M T y) := by
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul n t =>
        induction n using TensorProduct.induction_on with
        | zero => simp
        | tmul s m => simp [Ψ]
        | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy] at *
      | add x y hx hy => simp only [map_add, hx, hy]
    obtain ⟨y, rfl⟩ := (cancelBaseChangeLeft (S := S) R M T).surjective s
    have hy : y ∈ LinearMap.eqLocus (((TensorProduct.mk S (S ⊗[R] M) T).flip 1).rTensor T)
        ((TensorProduct.mk S _ T).flip 1) := by
      rw [LinearMap.mem_eqLocus]
      apply Ψ.injective
      rw [h1, h2, hs]
    rw [← range_tmul_one_eq_eqLocus] at hy
    obtain ⟨n, rfl⟩ := hy
    exact ⟨TensorProduct.comm R S M n, (cancelBaseChangeLeft_tmul_one n).symm⟩

end Module.FaithfullyFlat

namespace AlgebraicGeometry.EtaleCategory

variable {A : CommRingCat.{u}} (M : Type u) [AddCommGroup M] [Module A M]

set_option backward.isDefEq.respectTransparency.types false in
/-- The presheaf `M~` on `Et(A)` satisfies the sheaf axioms. -/
theorem isSheafAxioms_tensorPresheaf :
    IsSheafAxioms (tensorPresheaf (A := A) M ⋙ forget AddCommGrpCat) where
  bijective_pi := by
    intro ι _ B D p hp
    classical
    have := Fintype.ofFinite ι
    let f : ((toAlgebras A).obj D).obj →ₗ[A] ((k : ι) → ((toAlgebras A).obj (B k)).obj) :=
      LinearMap.pi fun k ↦ ((toAlgebras A).map (p k)).hom.hom.toLinearMap
    have hf : Function.Bijective f := hp
    let e := (LinearEquiv.ofBijective f hf).lTensor M ≪≫ₗ
      TensorProduct.piRight A A M (fun k ↦ ((toAlgebras A).obj (B k)).obj)
    have he (s : M ⊗[A] ((toAlgebras A).obj D).obj) (k : ι) :
        ((toAlgebras A).map (p k)).hom.hom.toLinearMap.lTensor M s = e s k := by
      induction s using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (congrFun (map_zero e) k).symm
      | tmul m d => rfl
      | add x y hx hy =>
        exact (map_add _ x y).trans (by rw [hx, hy]; exact (congrFun (map_add e x y) k).symm)
    have h2 : (fun (s : M ⊗[A] ((toAlgebras A).obj D).obj) (k : ι) ↦
        ((toAlgebras A).map (p k)).hom.hom.toLinearMap.lTensor M s) = ⇑e :=
      funext fun s ↦ funext fun k ↦ he s k
    change Function.Bijective
      (fun (s : M ⊗[A] ((toAlgebras A).obj D).obj) (k : ι) ↦
        ((toAlgebras A).map (p k)).hom.hom.toLinearMap.lTensor M s)
    rw [h2]
    exact e.bijective
  injective_of_faithfullyFlat := by
    intro B C g hg
    let _ : Algebra ((toAlgebras A).obj B).obj ((toAlgebras A).obj C).obj :=
      ((toAlgebras A).map g).hom.hom.toRingHom.toAlgebra
    have : IsScalarTower A ((toAlgebras A).obj B).obj ((toAlgebras A).obj C).obj :=
      IsScalarTower.of_algebraMap_eq fun a ↦ (((toAlgebras A).map g).hom.hom.commutes a).symm
    have : Module.FaithfullyFlat ((toAlgebras A).obj B).obj ((toAlgebras A).obj C).obj := hg
    exact Module.FaithfullyFlat.injective_lTensor_toAlgHom A _ _ M
  range_of_faithfullyFlat := by
    intro B C g hg
    let S := ((toAlgebras A).obj B).obj
    let T := ((toAlgebras A).obj C).obj
    let _ : Algebra S T := ((toAlgebras A).map g).hom.hom.toRingHom.toAlgebra
    have : IsScalarTower A S T :=
      IsScalarTower.of_algebraMap_eq fun a ↦ (((toAlgebras A).map g).hom.hom.commutes a).symm
    have : Module.FaithfullyFlat S T := hg
    ext s
    constructor
    · rintro ⟨x, rfl⟩ D u v huv
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, huv]
    · intro hs
      have : Algebra.Etale A S := ((toAlgebras A).obj B).property
      have : Algebra.Etale A T := ((toAlgebras A).obj C).property
      have : Algebra.Etale A (T ⊗[S] T) := Algebra.Etale.tensorProduct_of_isScalarTower A S T T
      let φ : A ⟶ CommRingCat.of (T ⊗[S] T) := CommRingCat.ofHom (algebraMap A (T ⊗[S] T))
      have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr inferInstance
      let i₁ : T →ₐ[A] T ⊗[S] T := Algebra.TensorProduct.includeLeft
      let i₂ : T →ₐ[A] T ⊗[S] T := Algebra.TensorProduct.includeRight.restrictScalars A
      let u : C ⟶ mk φ hφ := homMk (CommRingCat.ofHom i₁.toRingHom) (by
        rw [structureMap_mk]; ext a; exact i₁.commutes a)
      let v : C ⟶ mk φ hφ := homMk (CommRingCat.ofHom i₂.toRingHom) (by
        rw [structureMap_mk]; ext a; exact i₂.commutes a)
      have huv : g ≫ u = g ≫ v := by
        apply hom_ext
        rw [ringHom_comp, ringHom_comp]
        ext b
        change algebraMap S T b ⊗ₜ[S] (1 : T) = (1 : T) ⊗ₜ[S] algebraMap S T b
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      have h := hs u v huv
      let e : ((toAlgebras A).obj (mk φ hφ)).obj ≃ₐ[A] T ⊗[S] T :=
        { RingEquiv.refl (T ⊗[S] T) with
          commutes' := fun a ↦ by
            change (structureMap (mk φ hφ)).hom a = φ.hom a
            rw [structureMap_mk]
            rfl }
      have hu : i₁.toLinearMap = e.toLinearMap ∘ₗ ((toAlgebras A).map u).hom.hom.toLinearMap :=
        LinearMap.ext fun _ ↦ rfl
      have hv : i₂.toLinearMap = e.toLinearMap ∘ₗ ((toAlgebras A).map v).hom.hom.toLinearMap :=
        LinearMap.ext fun _ ↦ rfl
      change ((toAlgebras A).map u).hom.hom.toLinearMap.lTensor M s =
        ((toAlgebras A).map v).hom.hom.toLinearMap.lTensor M s at h
      have key : i₁.toLinearMap.lTensor M s = i₂.toLinearMap.lTensor M s := by
        rw [hu, hv, LinearMap.lTensor_comp_apply, LinearMap.lTensor_comp_apply, h]
      have hmem : (s : M ⊗[A] T) ∈ LinearMap.range
          ((IsScalarTower.toAlgHom A S T).toLinearMap.lTensor M) := by
        rw [Module.FaithfullyFlat.range_lTensor_toAlgHom]
        exact key
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, hx⟩

/-- **The presheaf `M~` is a sheaf** [FK, I.1]. For an `A`-module `M`, the presheaf
`B ↦ M ⊗_A B` on the étale category of `A` is a sheaf of abelian groups for the étale
topology. -/
@[weil "lem_fk101_quasi_coherent_etale_sheaf_is_sheaf"]
theorem isSheaf_tensorPresheaf :
    CategoryTheory.Presheaf.IsSheaf (Scheme.AffineEtale.topology (Spec A)) (tensorPresheaf M) :=
  (isSheaf_iff_isSheafAxioms_forget _).2 (isSheafAxioms_tensorPresheaf M)

end AlgebraicGeometry.EtaleCategory
