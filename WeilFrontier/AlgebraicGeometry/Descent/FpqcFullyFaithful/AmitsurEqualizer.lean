module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcFullyFaithful.AmitsurEqualizer

/-!
# Descent of elements along a faithfully flat ring map

Let `A → B` be a faithfully flat ring map and `M` an `A`-module. Then the sequence
`0 → M → M ⊗[A] B → (M ⊗[A] B) ⊗[A] B`, with maps `m ↦ m ⊗ 1` and
`m ⊗ b ↦ m ⊗ 1 ⊗ b - m ⊗ b ⊗ 1`, is exact: the map `M → M ⊗[A] B` is injective, and its image is
the submodule of `M ⊗[A] B` on which the two coface maps `m ⊗ b ↦ m ⊗ 1 ⊗ b` and
`m ⊗ b ↦ m ⊗ b ⊗ 1` agree.

## Main results

* `Module.FaithfullyFlat.injective_tmul_one`: `m ↦ m ⊗ 1` is injective.
* `Module.FaithfullyFlat.exact_tmul_one_rTensor_sub`: the sequence is exact at `M ⊗[A] B`.
* `Module.FaithfullyFlat.range_tmul_one_eq_eqLocus`: the image of `M` is the equalizer of the
  two coface maps.

## Implementation notes

The statements are written with `M` on the left, as in the source, and the third term bracketed
as `(M ⊗[A] B) ⊗[A] B`. The proofs transport `Stacks.Descent.injective_amitsurUnit` and
`Stacks.Descent.exact_amitsurUnit_amitsurDiff`, where the algebra factors stand on the left,
along the evident commutativity and associativity isomorphisms; under them the two coface maps
correspond to `Stacks.Descent.amitsurCoface₀` and `Stacks.Descent.amitsurCoface₁` in this order,
so no sign appears.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FreitagKiehl]
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public noncomputable section

open TensorProduct

namespace Module.FaithfullyFlat

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]

/-- The isomorphism `(M ⊗ B) ⊗ B ≃ B ⊗ (B ⊗ M)`, `(m ⊗ x) ⊗ y ↦ x ⊗ (y ⊗ m)`, comparing the
third term of the sequence with the one of `Stacks.Descent`. -/
private def thirdTermEquiv (A B M : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] : (M ⊗[A] B) ⊗[A] B ≃ₗ[A] B ⊗[A] (B ⊗[A] M) :=
  TensorProduct.assoc A M B B ≪≫ₗ TensorProduct.comm A M (B ⊗[A] B) ≪≫ₗ
    TensorProduct.assoc A B B M

private lemma comm_tmul_one (m : M) :
    TensorProduct.comm A M B ((TensorProduct.mk A M B).flip 1 m) =
      Stacks.Descent.amitsurUnit A B M m := rfl

private lemma thirdTermEquiv_rTensor (x : M ⊗[A] B) :
    thirdTermEquiv A B M (((TensorProduct.mk A M B).flip 1).rTensor B x) =
      Stacks.Descent.amitsurCoface₀ A B M (TensorProduct.comm A M B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma thirdTermEquiv_tmul_one (x : M ⊗[A] B) :
    thirdTermEquiv A B M ((TensorProduct.mk A (M ⊗[A] B) B).flip 1 x) =
      Stacks.Descent.amitsurCoface₁ A B M (TensorProduct.comm A M B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [thirdTermEquiv]
  | tmul m b => rfl
  | add x y hx hy =>
    simp only [map_add] at hx hy ⊢
    rw [hx, hy]

variable [Module.FaithfullyFlat A B]

variable (A B M) in
/-- **Faithfully flat descent, degree `-1`.** For a faithfully flat `A → B`, the map
`M → M ⊗[A] B`, `m ↦ m ⊗ 1`, is injective. -/
@[weil "lem_fka3_descent_lemma_modules"]
theorem injective_tmul_one : Function.Injective ((TensorProduct.mk A M B).flip 1) := by
  intro m n h
  apply Stacks.Descent.injective_amitsurUnit A B M
  rw [← comm_tmul_one, ← comm_tmul_one, h]

variable (A B M) in
/-- **Faithfully flat descent, degree `0`.** For a faithfully flat `A → B`, the sequence
`M → M ⊗[A] B → (M ⊗[A] B) ⊗[A] B`, `m ↦ m ⊗ 1`, `m ⊗ b ↦ m ⊗ 1 ⊗ b - m ⊗ b ⊗ 1`, is exact. -/
@[weil "lem_fka3_descent_lemma_modules"]
theorem exact_tmul_one_rTensor_sub :
    Function.Exact ((TensorProduct.mk A M B).flip 1)
      (((TensorProduct.mk A M B).flip 1).rTensor B - (TensorProduct.mk A (M ⊗[A] B) B).flip 1) := by
  intro x
  have key : (((TensorProduct.mk A M B).flip 1).rTensor B -
      (TensorProduct.mk A (M ⊗[A] B) B).flip 1) x = 0 ↔
      Stacks.Descent.amitsurDiff A B M (TensorProduct.comm A M B x) = 0 := by
    rw [← (thirdTermEquiv A B M).map_eq_zero_iff, LinearMap.sub_apply, map_sub,
      thirdTermEquiv_rTensor, thirdTermEquiv_tmul_one, Stacks.Descent.amitsurDiff_apply]
  rw [key, Stacks.Descent.exact_amitsurUnit_amitsurDiff A B M]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, (TensorProduct.comm A M B).injective ?_⟩
    rw [comm_tmul_one, hm]
  · rintro ⟨m, rfl⟩
    exact ⟨m, rfl⟩

variable (A B M) in
/-- **Faithfully flat descent of elements.** For a faithfully flat `A → B`, the image of
`M → M ⊗[A] B`, `m ↦ m ⊗ 1`, is the set of elements on which the two maps
`m ⊗ b ↦ m ⊗ 1 ⊗ b` and `m ⊗ b ↦ m ⊗ b ⊗ 1` agree. -/
@[weil "lem_fka3_descent_lemma_modules"]
theorem range_tmul_one_eq_eqLocus :
    LinearMap.range ((TensorProduct.mk A M B).flip 1) =
      LinearMap.eqLocus (((TensorProduct.mk A M B).flip 1).rTensor B)
        ((TensorProduct.mk A (M ⊗[A] B) B).flip 1) := by
  ext x
  rw [LinearMap.mem_eqLocus, ← sub_eq_zero, ← LinearMap.sub_apply,
    exact_tmul_one_rTensor_sub A B M x]
  rfl

end Module.FaithfullyFlat

end
