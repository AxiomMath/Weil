module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Descent.Module.AugmentedDescentComplex

/-!
# Base change of the Amitsur complex along the extension itself

Let `A → B` be a homomorphism of commutative rings and `M` an `A`-module. Put `B' = B ⊗[A] B`,
a `B`-algebra through the left factor `b ↦ b ⊗ 1`, and `M' = B ⊗[A] M`, a `B`-module. Tensoring
the Amitsur complex of `(A → B, M)` with `B` over `A` gives the Amitsur complex of
`(B → B', M')`: in each degree there is a `B`-linear isomorphism
`κ : B ⊗[A] (B^{⊗(n + 1)} ⊗[A] M) ≃ B'^{⊗_B (n + 1)} ⊗[B] M'`,
`b ⊗ (b₀ ⊗ ⋯ ⊗ bₙ ⊗ m) ↦ (1 ⊗ b₀) ⊗ ⋯ ⊗ (1 ⊗ bₙ) ⊗ (b ⊗ m)`, and these isomorphisms commute
with the differentials. Moreover `B → B'` has the `B`-linear section `b ⊗ b' ↦ b b'`, so the
base-changed extension is split.

The isomorphism is built in two steps: the `B`-algebra isomorphism
`B'^{⊗_B (n + 1)} ≃ B ⊗[A] B^{⊗(n + 1)}` matching the `j`-th tensor slots, obtained from the
universal property of tensor powers (`Stacks.Descent.tensorSlotDesc`), and then the
associativity and cancellation isomorphisms of the tensor product. Since the insertion of a `1`
into the `i`-th slot is characterised on slots, the identification carries `id_B ⊗ δᵢ` to `δᵢ'`,
and summing with signs gives the compatibility with the differentials.

## Main definitions

* `Algebra.baseChangeTensorPowerEquiv A B n`: the `B`-algebra isomorphism
  `(B ⊗[A] B)^{⊗_B (n + 1)} ≃ₐ[B] B ⊗[A] B^{⊗(n + 1)}`.
* `Algebra.amitsurBaseChangeEquiv A B M n`: the `B`-linear isomorphism
  `B ⊗[A] (amitsurComplex A B M).X n ≃ (amitsurComplex B (B ⊗[A] B) (B ⊗[A] M)).X n`.

## Main results

* `Algebra.amitsurBaseChangeEquiv_succ_tmul`, `Algebra.amitsurBaseChangeTermEquiv_tmul`,
  `Algebra.baseChangeTensorPowerEquiv_symm_one_tmul_tensorSlot`: the isomorphism on pure tensors.
* `Algebra.amitsurBaseChangeEquiv_comp_baseChange_d`: the isomorphisms commute with the
  differentials, `κ_{n + 1} ∘ (id_B ⊗ d_n) = d'_n ∘ κ_n`.
* `Algebra.exists_section_algebraMap_tensorProduct_self`: `B → B ⊗[A] B` has a `B`-linear
  section `b ⊗ b' ↦ b b'`.

## Implementation notes

The Amitsur complex is indexed by `ℕ` with `M` in degree `0`, so the source's degree `n ≥ -1`
is degree `n + 1` here, and the `B`-factors stand to the left of `M`. In degree `0` the
isomorphism is the identity of `B ⊗[A] M`. The source's formula places `b` in front of `m`;
here it is read through the identification of tensor powers, `κ (b ⊗ (x ⊗ m)) = e⁻¹ (b ⊗ x) ⊗
(1 ⊗ m)`, which is the same element since `κ` is `B`-linear and `e⁻¹ (1 ⊗ (b₀ ⊗ ⋯ ⊗ bₙ)) =
(1 ⊗ b₀) ⊗ ⋯ ⊗ (1 ⊗ bₙ)`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
-/

@[expose] public section

open CategoryTheory AlgebraicTopology Stacks.Descent
open scoped TensorProduct

universe u v

namespace Algebra

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- The `A`-algebra structure on a tensor power of `B ⊗[A] B` over `B`, through `B`. -/
noncomputable abbrev baseChangeTensorPowerAlgebra (n : ℕ) :
    Algebra A (tensorPowerAlg B (B ⊗[A] B) n : Type u) :=
  ((algebraMap B (tensorPowerAlg B (B ⊗[A] B) n : Type u)).comp (algebraMap A B)).toAlgebra

attribute [local instance] baseChangeTensorPowerAlgebra

lemma baseChangeTensorPowerAlgebra_isScalarTower (n : ℕ) :
    IsScalarTower A B (tensorPowerAlg B (B ⊗[A] B) n : Type u) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] baseChangeTensorPowerAlgebra_isScalarTower

/-- The comparison `(B ⊗[A] B)^{⊗_B (n + 1)} → B ⊗[A] B^{⊗(n + 1)}`, sending the `j`-th slot
`b ⊗ b'` to `b ⊗ (b'` in the `j`-th slot`)`. -/
noncomputable def baseChangeTensorPowerHom (n : ℕ) :
    tensorPowerAlg B (B ⊗[A] B) n ⟶ CommAlgCat.of B (B ⊗[A] (tensorPowerAlg A B n : Type u)) :=
  tensorSlotDesc B (B ⊗[A] B) n fun j =>
    CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id B B) (tensorSlot A B n j).hom)

/-- The comparison `B ⊗[A] B^{⊗(n + 1)} → (B ⊗[A] B)^{⊗_B (n + 1)}`, the `B`-algebra map
sending `1 ⊗ (b` in the `j`-th slot`)` to `1 ⊗ b` in the `j`-th slot. -/
noncomputable def baseChangeTensorPowerInv (n : ℕ) :
    CommAlgCat.of B (B ⊗[A] (tensorPowerAlg A B n : Type u)) ⟶ tensorPowerAlg B (B ⊗[A] B) n :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lift (Algebra.ofId B _)
    (tensorSlotDesc (T := CommAlgCat.of A (tensorPowerAlg B (B ⊗[A] B) n : Type u)) A B n
      (fun j => CommAlgCat.ofHom (((tensorSlot B (B ⊗[A] B) n j).hom.restrictScalars A).comp
        Algebra.TensorProduct.includeRight))).hom
    fun _ _ => Commute.all _ _)

/-- `baseChangeTensorPowerHom` on the `j`-th slot. -/
lemma tensorSlot_comp_baseChangeTensorPowerHom (n : ℕ) (j : Fin (n + 1)) :
    tensorSlot B (B ⊗[A] B) n j ≫ baseChangeTensorPowerHom A B n =
      CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id B B) (tensorSlot A B n j).hom) :=
  tensorSlot_comp_tensorSlotDesc _ _ n _ j

/-- `baseChangeTensorPowerHom` on an element of the `j`-th slot. -/
lemma baseChangeTensorPowerHom_tensorSlot_apply (n : ℕ) (j : Fin (n + 1)) (x : B ⊗[A] B) :
    (baseChangeTensorPowerHom A B n).hom ((tensorSlot B (B ⊗[A] B) n j).hom x) =
      Algebra.TensorProduct.map (AlgHom.id B B) (tensorSlot A B n j).hom x :=
  congrArg (fun f => CommAlgCat.Hom.hom f x) (tensorSlot_comp_baseChangeTensorPowerHom A B n j)

/-- `baseChangeTensorPowerInv` on `1 ⊗ (b` in the `j`-th slot`)`. -/
lemma baseChangeTensorPowerInv_one_tmul_tensorSlot (n : ℕ) (j : Fin (n + 1)) (b : B) :
    (baseChangeTensorPowerInv A B n).hom ((1 : B) ⊗ₜ[A] (tensorSlot A B n j).hom b) =
      (tensorSlot B (B ⊗[A] B) n j).hom ((1 : B) ⊗ₜ[A] b) := by
  have h := congrArg (fun f => CommAlgCat.Hom.hom f b)
    (tensorSlot_comp_tensorSlotDesc (T := CommAlgCat.of A (tensorPowerAlg B (B ⊗[A] B) n : Type u))
      A B n (fun j => CommAlgCat.ofHom (((tensorSlot B (B ⊗[A] B) n j).hom.restrictScalars A).comp
        Algebra.TensorProduct.includeRight)) j)
  simp only [baseChangeTensorPowerInv, CommAlgCat.hom_ofHom, Algebra.TensorProduct.lift_tmul,
    map_one, one_mul]
  exact h

/-- `baseChangeTensorPowerInv` is a left inverse of `baseChangeTensorPowerHom`. -/
lemma baseChangeTensorPowerHom_comp_inv (n : ℕ) :
    baseChangeTensorPowerHom A B n ≫ baseChangeTensorPowerInv A B n = 𝟙 _ := by
  refine tensorPowerAlg_hom_ext B (B ⊗[A] B) n fun j => ?_
  rw [← Category.assoc, tensorSlot_comp_baseChangeTensorPowerHom, Category.comp_id]
  refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_)
  ext b
  simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact baseChangeTensorPowerInv_one_tmul_tensorSlot A B n j b

/-- `baseChangeTensorPowerInv` is a right inverse of `baseChangeTensorPowerHom`. -/
lemma baseChangeTensorPowerInv_comp_hom (n : ℕ) :
    baseChangeTensorPowerInv A B n ≫ baseChangeTensorPowerHom A B n = 𝟙 _ := by
  refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_)
  have := tensorPowerAlg_hom_ext (T := CommAlgCat.of A (B ⊗[A] (tensorPowerAlg A B n : Type u)))
    A B n (g₁ := CommAlgCat.ofHom (((baseChangeTensorPowerInv A B n ≫
      baseChangeTensorPowerHom A B n).hom.restrictScalars A).comp
        Algebra.TensorProduct.includeRight))
    (g₂ := CommAlgCat.ofHom Algebra.TensorProduct.includeRight) fun j => by
      ext b
      simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, AlgHom.coe_comp,
        AlgHom.coe_restrictScalars', Function.comp_apply, Algebra.TensorProduct.includeRight_apply]
      rw [baseChangeTensorPowerInv_one_tmul_tensorSlot, baseChangeTensorPowerHom_tensorSlot_apply]
      rfl
  exact congrArg CommAlgCat.Hom.hom this

/-- **Tensor powers of the base-changed extension**: the `B`-algebra isomorphism
`(B ⊗[A] B)^{⊗_B (n + 1)} ≃ B ⊗[A] B^{⊗(n + 1)}`, matching the `j`-th tensor slots. -/
noncomputable def baseChangeTensorPowerEquiv (n : ℕ) :
    (tensorPowerAlg B (B ⊗[A] B) n : Type u) ≃ₐ[B] B ⊗[A] (tensorPowerAlg A B n : Type u) :=
  AlgEquiv.ofAlgHom (baseChangeTensorPowerHom A B n).hom (baseChangeTensorPowerInv A B n).hom
    (congrArg CommAlgCat.Hom.hom (baseChangeTensorPowerInv_comp_hom A B n))
    (congrArg CommAlgCat.Hom.hom (baseChangeTensorPowerHom_comp_inv A B n))

/-- The inverse of `baseChangeTensorPowerEquiv` sends `1 ⊗ (b` in the `j`-th slot`)` to `1 ⊗ b`
in the `j`-th slot; being a `B`-algebra map, this determines it:
`1 ⊗ (b₀ ⊗ ⋯ ⊗ bₙ) ↦ (1 ⊗ b₀) ⊗ ⋯ ⊗ (1 ⊗ bₙ)`. -/
@[weil "lem_fka3_base_changed_extension_split"]
lemma baseChangeTensorPowerEquiv_symm_one_tmul_tensorSlot (n : ℕ) (j : Fin (n + 1)) (b : B) :
    (baseChangeTensorPowerEquiv A B n).symm ((1 : B) ⊗ₜ[A] (tensorSlot A B n j).hom b) =
      (tensorSlot B (B ⊗[A] B) n j).hom ((1 : B) ⊗ₜ[A] b) :=
  baseChangeTensorPowerInv_one_tmul_tensorSlot A B n j b

/-- The comparison carries the insertion of `1` into the `i`-th slot of `(B ⊗[A] B)^{⊗_B (n + 1)}`
to `id_B ⊗` the insertion of `1` into the `i`-th slot of `B^{⊗(n + 1)}`. -/
lemma tensorInsertOne_comp_baseChangeTensorPowerHom (n : ℕ) (i : Fin (n + 2)) :
    tensorInsertOne B (B ⊗[A] B) n i ≫ baseChangeTensorPowerHom A B (n + 1) =
      baseChangeTensorPowerHom A B n ≫ CommAlgCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id B B) (tensorInsertOne A B n i).hom) := by
  refine tensorPowerAlg_hom_ext B (B ⊗[A] B) n fun j => ?_
  rw [← Category.assoc, tensorSlot_comp_tensorInsertOne, tensorSlot_comp_baseChangeTensorPowerHom,
    ← Category.assoc, tensorSlot_comp_baseChangeTensorPowerHom]
  refine CommAlgCat.hom_ext (Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_)
  ext b
  have h := congrArg (fun f => CommAlgCat.Hom.hom f b) (tensorSlot_comp_tensorInsertOne A B n i j)
  simp only [CommAlgCat.hom_comp] at h
  simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, AlgHom.coe_restrictScalars',
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    AlgHom.comp_apply]
  rw [← h]
  rfl

/-- The inverse comparison carries `id_B ⊗ δᵢ` to `δᵢ'`. -/
lemma baseChangeTensorPowerEquiv_symm_map_tensorInsertOne (n : ℕ) (i : Fin (n + 2))
    (x : B ⊗[A] (tensorPowerAlg A B n : Type u)) :
    (baseChangeTensorPowerEquiv A B (n + 1)).symm
        (Algebra.TensorProduct.map (AlgHom.id B B) (tensorInsertOne A B n i).hom x) =
      (tensorInsertOne B (B ⊗[A] B) n i).hom ((baseChangeTensorPowerEquiv A B n).symm x) := by
  rw [AlgEquiv.symm_apply_eq]
  have h := congrArg (fun f => CommAlgCat.Hom.hom f ((baseChangeTensorPowerEquiv A B n).symm x))
    (tensorInsertOne_comp_baseChangeTensorPowerHom A B n i)
  simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, AlgHom.comp_apply] at h
  rw [show (baseChangeTensorPowerEquiv A B (n + 1)) _ = _ from h]
  congr 1
  exact ((baseChangeTensorPowerEquiv A B n).apply_symm_apply x).symm

variable (M : Type (max u v)) [AddCommGroup M] [Module A M]

/-- The `B`-linear isomorphism `B ⊗[A] (B^{⊗(n + 1)} ⊗[A] M) ≃ B'^{⊗_B (n + 1)} ⊗[B] (B ⊗[A] M)`
on the terms of the Amitsur complexes, `B' = B ⊗[A] B`. -/
noncomputable def amitsurBaseChangeTermEquiv (n : ℕ) :
    B ⊗[A] ((tensorPowerAlg A B n : Type u) ⊗[A] M) ≃ₗ[B]
      (tensorPowerAlg B (B ⊗[A] B) n : Type u) ⊗[B] (B ⊗[A] M) :=
  (TensorProduct.AlgebraTensorModule.assoc A A B B (tensorPowerAlg A B n : Type u) M).symm ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B
      (B ⊗[A] (tensorPowerAlg A B n : Type u)) M).symm ≪≫ₗ
    LinearEquiv.rTensor (B ⊗[A] M) (baseChangeTensorPowerEquiv A B n).symm.toLinearEquiv

/-- `amitsurBaseChangeTermEquiv` on a pure tensor: `b ⊗ (x ⊗ m) ↦ e⁻¹ (b ⊗ x) ⊗ (1 ⊗ m)`. -/
@[weil "lem_fka3_base_changed_extension_split"]
lemma amitsurBaseChangeTermEquiv_tmul (n : ℕ) (b : B) (x : (tensorPowerAlg A B n : Type u))
    (m : M) :
    amitsurBaseChangeTermEquiv A B M n (b ⊗ₜ[A] (x ⊗ₜ[A] m)) =
      (baseChangeTensorPowerEquiv A B n).symm (b ⊗ₜ[A] x) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m) := by
  simp [amitsurBaseChangeTermEquiv]

/-- **The base change of the Amitsur complex along `A → B`**: the `B`-linear isomorphisms
`κ : B ⊗[A] (amitsurComplex A B M).X n ≃ (amitsurComplex B (B ⊗[A] B) (B ⊗[A] M)).X n`; in
degree `0` it is the identity of `B ⊗[A] M`, and in degree `n + 1` it is
`amitsurBaseChangeTermEquiv` read through the identifications of the terms with tensor powers. -/
@[weil "lem_fka3_base_changed_extension_split"]
noncomputable def amitsurBaseChangeEquiv :
    (n : ℕ) → B ⊗[A] (amitsurComplex A B M).X n ≃ₗ[B]
      (amitsurComplex B (B ⊗[A] B) (B ⊗[A] M)).X n
  | 0 => LinearEquiv.refl B (B ⊗[A] M)
  | n + 1 =>
      (LinearEquiv.baseChange A B _ _ (amitsurComplexXIso A B M n).toLinearEquiv).symm ≪≫ₗ
        amitsurBaseChangeTermEquiv A B M n ≪≫ₗ
        (amitsurComplexXIso B (B ⊗[A] B) (B ⊗[A] M) n).toLinearEquiv

/-- `amitsurBaseChangeTermEquiv` carries `id_B ⊗ (δᵢ ⊗ id_M)` to `δᵢ' ⊗ id_{M'}`. -/
lemma amitsurBaseChangeTermEquiv_baseChange_insertOne (n : ℕ) (i : Fin (n + 2))
    (z : B ⊗[A] ((tensorPowerAlg A B n : Type u) ⊗[A] M)) :
    amitsurBaseChangeTermEquiv A B M (n + 1)
        (LinearMap.baseChange B
          (LinearMap.rTensor M (tensorInsertOne A B n i).hom.toLinearMap) z) =
      LinearMap.rTensor (B ⊗[A] M) (tensorInsertOne B (B ⊗[A] B) n i).hom.toLinearMap
        (amitsurBaseChangeTermEquiv A B M n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul b w =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
    | tmul x m =>
      rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, amitsurBaseChangeTermEquiv_tmul,
        amitsurBaseChangeTermEquiv_tmul, LinearMap.rTensor_tmul]
      congr 1
      exact baseChangeTensorPowerEquiv_symm_map_tensorInsertOne A B n i (b ⊗ₜ[A] x)

/-- In degree `0` the isomorphism is the identity of `B ⊗[A] M`. -/
@[weil "lem_fka3_base_changed_extension_split"]
lemma amitsurBaseChangeEquiv_zero_apply (z : B ⊗[A] M) :
    amitsurBaseChangeEquiv A B M 0 z = z :=
  rfl

/-- In degree `n + 1` the isomorphism is `amitsurBaseChangeTermEquiv`. -/
@[weil "lem_fka3_base_changed_extension_split"]
lemma amitsurBaseChangeEquiv_succ_tmul (n : ℕ) (b : B)
    (w : (tensorPowerAlg A B n : Type u) ⊗[A] M) :
    amitsurBaseChangeEquiv A B M (n + 1) (b ⊗ₜ[A] (amitsurComplexXIso A B M n).hom w) =
      (amitsurComplexXIso B (B ⊗[A] B) (B ⊗[A] M) n).hom
        (amitsurBaseChangeTermEquiv A B M n (b ⊗ₜ[A] w)) := by
  have h : (LinearEquiv.baseChange A B _ _ (amitsurComplexXIso A B M n).toLinearEquiv).symm
      (b ⊗ₜ[A] (amitsurComplexXIso A B M n).hom w) = b ⊗ₜ[A] w :=
    (LinearEquiv.symm_apply_eq _).mpr rfl
  simp only [amitsurBaseChangeEquiv, LinearEquiv.trans_apply]
  erw [h]
  rfl

/-- The differential of the Amitsur complex on an element of `B^{⊗(n + 1)} ⊗[A] M`. -/
lemma amitsurComplex_d_succ_apply_eq_sum (n : ℕ) (w : (tensorPowerAlg A B n : Type u) ⊗[A] M) :
    (amitsurComplex A B M).d (n + 1) (n + 1 + 1) ((amitsurComplexXIso A B M n).hom w) =
      (amitsurComplexXIso A B M (n + 1)).hom (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        LinearMap.rTensor M (tensorInsertOne A B n i).hom.toLinearMap w) := by
  have hsum : (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (tensorModuleFunctor A M).map (tensorInsertOne A B n i)) =
      ModuleCat.ofHom (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        LinearMap.rTensor M (tensorInsertOne A B n i).hom.toLinearMap) := by
    refine ModuleCat.hom_ext ((ModuleCat.hom_sum _ _).trans ?_)
    exact (Finset.sum_congr rfl fun i _ => ModuleCat.hom_zsmul _ _).trans rfl
  have h := congr($(amitsurComplex_d_succ A B M n).hom w)
  rw [hsum] at h
  refine h.trans ?_
  change (amitsurComplexXIso A B M (n + 1)).hom.hom ((∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    LinearMap.rTensor M (tensorInsertOne A B n i).hom.toLinearMap) w) = _
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

/-- **The base change of the Amitsur complex is the Amitsur complex of the base change**:
`κ_{n + 1} ∘ (id_B ⊗ d_n) = d'_n ∘ κ_n` for every `n`, where `d` is the differential of the
Amitsur complex of `(A → B, M)` and `d'` that of `(B → B ⊗[A] B, B ⊗[A] M)`. -/
@[weil "lem_fka3_base_changed_extension_split"]
theorem amitsurBaseChangeEquiv_comp_baseChange_d (n : ℕ) :
    (amitsurBaseChangeEquiv A B M (n + 1)).toLinearMap ∘ₗ
        ((amitsurComplex A B M).d n (n + 1)).hom.baseChange B =
      ((amitsurComplex B (B ⊗[A] B) (B ⊗[A] M)).d n (n + 1)).hom ∘ₗ
        (amitsurBaseChangeEquiv A B M n).toLinearMap := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => exact (LinearMap.map_zero _).trans (LinearMap.map_zero _).symm
  | add z₁ z₂ h₁ h₂ =>
    exact (LinearMap.map_add _ _ _).trans
      ((congrArg₂ (· + ·) h₁ h₂).trans (LinearMap.map_add _ _ _).symm)
  | tmul b y =>
    cases n with
    | zero =>
      have e1 : (baseChangeTensorPowerEquiv A B 0).symm (b ⊗ₜ[A] (1 : B)) =
          algebraMap B _ b :=
        (baseChangeTensorPowerEquiv A B 0).symm.commutes b
      have hd := amitsurComplex_d_zero_one A B M y
      have hd' := amitsurComplex_d_zero_one B (B ⊗[A] B) (B ⊗[A] M) (b ⊗ₜ[A] y)
      change amitsurBaseChangeEquiv A B M 1 (b ⊗ₜ[A] (amitsurComplex A B M).d 0 1 y) =
        (amitsurComplex B (B ⊗[A] B) (B ⊗[A] M)).d 0 1 (b ⊗ₜ[A] y)
      rw [hd, hd', amitsurBaseChangeEquiv_succ_tmul]
      congr 1
      erw [amitsurBaseChangeTermEquiv_tmul, e1, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | succ n =>
      obtain ⟨w, rfl⟩ : ∃ w, (amitsurComplexXIso A B M n).hom w = y :=
        ⟨(amitsurComplexXIso A B M n).inv y, Iso.inv_hom_id_apply _ y⟩
      have hd := amitsurComplex_d_succ_apply_eq_sum A B M n w
      have hd' := amitsurComplex_d_succ_apply_eq_sum B (B ⊗[A] B) (B ⊗[A] M) n
        (amitsurBaseChangeTermEquiv A B M n (b ⊗ₜ[A] w))
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe]
      rw [hd, amitsurBaseChangeEquiv_succ_tmul, amitsurBaseChangeEquiv_succ_tmul, hd']
      congr 1
      simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_zsmul]
      refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
      exact amitsurBaseChangeTermEquiv_baseChange_insertOne A B M n i (b ⊗ₜ[A] w)

/-- **The base-changed extension is split**: `b ↦ b ⊗ 1` has the `B`-linear section
`b ⊗ b' ↦ b b'`. -/
@[weil "lem_fka3_base_changed_extension_split"]
theorem exists_section_algebraMap_tensorProduct_self :
    ∃ s : B ⊗[A] B →ₗ[B] B, (∀ b b' : B, s (b ⊗ₜ[A] b') = b * b') ∧
      ∀ b : B, s (algebraMap B (B ⊗[A] B) b) = b :=
  ⟨(Algebra.TensorProduct.lmul'' A).toLinearMap, fun _ _ => rfl,
    (Algebra.TensorProduct.lmul'' A).commutes⟩

end Algebra
