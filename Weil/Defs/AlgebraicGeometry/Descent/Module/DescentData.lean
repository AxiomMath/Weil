module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.DescentData
public import Weil.Attr

/-!
# Affine descent data

Let `R → A` be a homomorphism of commutative rings. An affine descent datum for `R → A` is a
pair `(N, σ)` of an `A`-module `N` and an `A ⊗[R] A`-linear isomorphism
`σ : N ⊗[R] A ≃ A ⊗[R] N`, where `(a ⊗ b) • (n ⊗ c) = a n ⊗ b c` and
`(a ⊗ b) • (c ⊗ n) = a c ⊗ b n`, satisfying the cocycle condition `σ₁₃ = σ₂₃ ∘ σ₁₂` on
`N ⊗ A ⊗ A`. Here `σ₁₂ = σ ⊗ id`, `σ₂₃ = id ⊗ σ` and `σ₁₃ = τ' ∘ σ₁₂ ∘ τ`, with `τ` exchanging
the two copies of `A` in `N ⊗ A ⊗ A` and `τ'` the last two factors of `A ⊗ N ⊗ A`.

This object is `ModuleCat.DescentData R A`. The present file records, on pure tensors, that its
three pullbacks `ModuleCat.transition01`, `ModuleCat.transition12` and `ModuleCat.transition02`
are the maps `σ₁₂`, `σ₂₃` and `σ₁₃`, so that its `cocycle` field is the cocycle condition above.

## Main results

* `ModuleCat.transition01_tmul`: `σ₁₂ (n ⊗ b ⊗ c) = σ (n ⊗ b) ⊗ c`.
* `ModuleCat.transition12_tmul`: `σ₂₃ (x ⊗ n ⊗ b) = x ⊗ σ (n ⊗ b)`.
* `ModuleCat.transition02_eq_comp`: `σ₁₃ = τ' ∘ σ₁₂ ∘ τ`.
* `ModuleCat.transition02_tmul_of_eq_sum`: if `σ (n ⊗ c) = ∑ᵣ xᵣ ⊗ νᵣ`, then
  `σ₁₃ (n ⊗ b ⊗ c) = ∑ᵣ xᵣ ⊗ b ⊗ νᵣ`.
* `ModuleCat.DescentData.cocycle_tmul`: the cocycle condition on pure tensors.

## Implementation notes

Triple tensor products are bracketed as `(N ⊗ A) ⊗ A`, `(A ⊗ N) ⊗ A` and `(A ⊗ A) ⊗ N`; the
statements use `TensorProduct.assoc` and `TensorProduct.rightComm` to move between brackets.
The `A ⊗[R] A`-module structures on `N ⊗[R] A` and `A ⊗[R] N` are
`ModuleCat.sourceTensorModule` and `ModuleCat.targetTensorModule`, whose actions on pure
tensors are `ModuleCat.sourceTensor_smul_tmul` and `ModuleCat.targetTensor_smul_tmul`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], Appendix A III
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
-/

/- FK's affine descent datum is
StacksFrontier's `ModuleCat.DescentData` (reused, no new definition); the lemmas below identify
its fields with FK's σ₁₂, σ₂₃, σ₁₃. -/

@[expose] public section

universe u v w

noncomputable section

namespace ModuleCat

open TensorProduct

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- `σ₁₂ = σ ⊗ id` on pure tensors. -/
@[weil "def_fka3_affine_descent_datum", simp]
theorem transition01_tmul (N : ModuleCat.{w} A)
    (e : (restrictModule R A N ⊗[R] A) ≃ₗ[A ⊗[R] A] (A ⊗[R] restrictModule R A N))
    (n : restrictModule R A N) (b c : A) :
    transition01 R A N e ((n ⊗ₜ[R] b) ⊗ₜ[R] c) = e (n ⊗ₜ[R] b) ⊗ₜ[R] c := rfl

/-- `σ₂₃ = id ⊗ σ` on pure tensors. -/
@[weil "def_fka3_affine_descent_datum", simp]
theorem transition12_tmul (N : ModuleCat.{w} A)
    (e : (restrictModule R A N ⊗[R] A) ≃ₗ[A ⊗[R] A] (A ⊗[R] restrictModule R A N))
    (x : A) (n : restrictModule R A N) (b : A) :
    transition12 R A N e ((x ⊗ₜ[R] n) ⊗ₜ[R] b) =
      (TensorProduct.assoc R A A (restrictModule R A N)).symm (x ⊗ₜ[R] e (n ⊗ₜ[R] b)) := rfl

/-- `σ₁₃ = τ' ∘ σ₁₂ ∘ τ`, where `τ` exchanges the two factors `A` of `(N ⊗ A) ⊗ A` and `τ'`
exchanges the last two factors of `(A ⊗ N) ⊗ A`. -/
@[weil "def_fka3_affine_descent_datum"]
theorem transition02_eq_comp (N : ModuleCat.{w} A)
    (e : (restrictModule R A N ⊗[R] A) ≃ₗ[A ⊗[R] A] (A ⊗[R] restrictModule R A N)) :
    transition02 R A N e =
      (TensorProduct.rightComm R A (restrictModule R A N) A).toLinearMap ∘ₗ
        transition01 R A N e ∘ₗ
          (TensorProduct.rightComm R (restrictModule R A N) A A).toLinearMap := rfl

/-- `σ₁₃ (n ⊗ b ⊗ c)` is `σ (n ⊗ c)` with `b` inserted in the middle. -/
@[simp]
theorem transition02_tmul (N : ModuleCat.{w} A)
    (e : (restrictModule R A N ⊗[R] A) ≃ₗ[A ⊗[R] A] (A ⊗[R] restrictModule R A N))
    (n : restrictModule R A N) (b c : A) :
    transition02 R A N e ((n ⊗ₜ[R] b) ⊗ₜ[R] c) =
      TensorProduct.rightComm R A (restrictModule R A N) A (e (n ⊗ₜ[R] c) ⊗ₜ[R] b) := rfl

/-- If `σ (n ⊗ c) = ∑ᵣ xᵣ ⊗ νᵣ`, then `σ₁₃ (n ⊗ b ⊗ c) = ∑ᵣ xᵣ ⊗ b ⊗ νᵣ`. -/
@[weil "def_fka3_affine_descent_datum"]
theorem transition02_tmul_of_eq_sum {ι : Type*} (s : Finset ι) (N : ModuleCat.{w} A)
    (e : (restrictModule R A N ⊗[R] A) ≃ₗ[A ⊗[R] A] (A ⊗[R] restrictModule R A N))
    (n : restrictModule R A N) (b c : A) (x : ι → A) (ν : ι → restrictModule R A N)
    (h : e (n ⊗ₜ[R] c) = ∑ r ∈ s, x r ⊗ₜ[R] ν r) :
    transition02 R A N e ((n ⊗ₜ[R] b) ⊗ₜ[R] c) = ∑ r ∈ s, (x r ⊗ₜ[R] b) ⊗ₜ[R] ν r := by
  rw [transition02_tmul, h, TensorProduct.sum_tmul, map_sum]
  rfl

namespace DescentData

/-- The cocycle condition `σ₁₃ = σ₂₃ ∘ σ₁₂` of a descent datum, on pure tensors. -/
@[weil "def_fka3_affine_descent_datum"]
theorem cocycle_tmul (D : DescentData.{u, v, w} R A) (n : restrictModule R A D.module)
    (b c : A) :
    transition12 R A D.module D.transition
        (transition01 R A D.module D.transition ((n ⊗ₜ[R] b) ⊗ₜ[R] c)) =
      transition02 R A D.module D.transition ((n ⊗ₜ[R] b) ⊗ₜ[R] c) :=
  LinearMap.congr_fun D.cocycle _

end DescentData

end ModuleCat

end

end
