module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Descent.Module.HomDescent

/-!
# The two pullbacks of a module map to `B ⊗[R] B`

Let `R → B` be a map of commutative rings and let `M`, `N` be `R`-modules. A `B`-linear map
`ψ : B ⊗[R] M → B ⊗[R] N` has two base changes to `B ⊗[R] B`, one along each of the ring maps
`ι₁ = includeLeft : b ↦ b ⊗ 1` and `ι₂ = includeRight : b ↦ 1 ⊗ b`. They are the
`B ⊗[R] B`-linear maps `(B ⊗[R] B) ⊗[R] M → (B ⊗[R] B) ⊗[R] N` given on generators by

* `e₁ ψ ((c ⊗ c') ⊗ m) = ∑ᵣ (βᵣ c ⊗ c') ⊗ nᵣ`,
* `e₂ ψ ((c ⊗ c') ⊗ m) = ∑ᵣ (c ⊗ βᵣ c') ⊗ nᵣ`,

whenever `ψ (1 ⊗ m) = ∑ᵣ βᵣ ⊗ nᵣ`. For an `R`-linear `f : M → N`, the base change
`f_B = id_B ⊗ f` is Mathlib's `LinearMap.baseChange B f`, and `e₁ f_B = e₂ f_B = f_{B ⊗ B}`.
These are the maps of the descent sequence for homomorphisms of modules along `R → B`.

## Main definitions

* `Stacks.Descent.homBaseChangeIncludeLeft`: the pullback `e₁` along `ι₁`.
* `Stacks.Descent.homBaseChangeIncludeRight`: the pullback `e₂` along `ι₂`.

## Main results

* `Stacks.Descent.homBaseChangeIncludeLeft_tmul_of_eq_sum`,
  `Stacks.Descent.homBaseChangeIncludeRight_tmul_of_eq_sum`: the explicit formulas above.
* `Stacks.Descent.homBaseChangeIncludeLeft_comp_rTensor`,
  `Stacks.Descent.homBaseChangeIncludeRight_comp_rTensor`: `e_k ψ` is the base change of `ψ`
  along `ι_k`, i.e. the square with vertical maps `ι_k ⊗ id` commutes, and it is the unique
  `B ⊗[R] B`-linear map doing so.
* `Stacks.Descent.homBaseChangeIncludeLeft_baseChange`,
  `Stacks.Descent.homBaseChangeIncludeRight_baseChange`: `e_k (f_B) = f_{B ⊗ B}`.

## Implementation notes

The source writes the base ring on the right (`M ⊗ B`, `M ⊗ B ⊗ B`); here, following Mathlib's
`LinearMap.baseChange`, it is on the left (`B ⊗[R] M`, `(B ⊗[R] B) ⊗[R] M`). Both pullbacks are
`Stacks.Descent.homBaseChange` along the corresponding `R`-algebra map `B →ₐ[R] B ⊗[R] B`; this
defines them as `B ⊗[R] B`-linear maps without making `B ⊗[R] B` a `B`-algebra in two
incompatible ways, so the source's identifications
`(N ⊗ B) ⊗_{B, ι_k} (B ⊗ B) ≅ N ⊗ B ⊗ B` are built into the definition, and the characterisation
by the commuting square replaces them.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A.3]
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open scoped TensorProduct

open Algebra.TensorProduct

universe u v w w'

namespace Stacks.Descent

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {M : Type w} [AddCommGroup M] [Module R M] {N : Type w'} [AddCommGroup N] [Module R N]

/-- The pullback `e₁ ψ` of a `B`-linear map `ψ : B ⊗[R] M → B ⊗[R] N` along the first inclusion
`b ↦ b ⊗ 1` of `B` into `B ⊗[R] B`. -/
@[weil "def_fka3_affine_hom_pullbacks"]
noncomputable abbrev homBaseChangeIncludeLeft (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) :
    (B ⊗[R] B) ⊗[R] M →ₗ[B ⊗[R] B] (B ⊗[R] B) ⊗[R] N :=
  homBaseChange R B (includeLeft : B →ₐ[R] B ⊗[R] B) ψ

/-- The pullback `e₂ ψ` of a `B`-linear map `ψ : B ⊗[R] M → B ⊗[R] N` along the second inclusion
`b ↦ 1 ⊗ b` of `B` into `B ⊗[R] B`. -/
@[weil "def_fka3_affine_hom_pullbacks"]
noncomputable abbrev homBaseChangeIncludeRight (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) :
    (B ⊗[R] B) ⊗[R] M →ₗ[B ⊗[R] B] (B ⊗[R] B) ⊗[R] N :=
  homBaseChange R B (includeRight : B →ₐ[R] B ⊗[R] B) ψ

/-- The explicit formula for `e₁`: if `ψ (1 ⊗ m) = ∑ᵣ βᵣ ⊗ nᵣ`, then
`e₁ ψ ((c ⊗ c') ⊗ m) = ∑ᵣ (βᵣ c ⊗ c') ⊗ nᵣ`. -/
theorem homBaseChangeIncludeLeft_tmul_of_eq_sum (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) {ι : Type*}
    (s : Finset ι) (β : ι → B) (n : ι → N) (m : M) (hm : ψ (1 ⊗ₜ m) = ∑ r ∈ s, β r ⊗ₜ n r)
    (c c' : B) :
    homBaseChangeIncludeLeft ψ ((c ⊗ₜ c') ⊗ₜ m) = ∑ r ∈ s, ((β r * c) ⊗ₜ[R] c') ⊗ₜ[R] n r := by
  rw [homBaseChangeIncludeLeft, homBaseChange_tmul, hm, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [TensorProduct.smul_tmul', mul_comm _ (β r)]

/-- The explicit formula for `e₂`: if `ψ (1 ⊗ m) = ∑ᵣ βᵣ ⊗ nᵣ`, then
`e₂ ψ ((c ⊗ c') ⊗ m) = ∑ᵣ (c ⊗ βᵣ c') ⊗ nᵣ`. -/
theorem homBaseChangeIncludeRight_tmul_of_eq_sum (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) {ι : Type*}
    (s : Finset ι) (β : ι → B) (n : ι → N) (m : M) (hm : ψ (1 ⊗ₜ m) = ∑ r ∈ s, β r ⊗ₜ n r)
    (c c' : B) :
    homBaseChangeIncludeRight ψ ((c ⊗ₜ c') ⊗ₜ m) = ∑ r ∈ s, (c ⊗ₜ[R] (β r * c')) ⊗ₜ[R] n r := by
  rw [homBaseChangeIncludeRight, homBaseChange_tmul, hm, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [TensorProduct.smul_tmul', mul_comm _ (β r)]

/-- `e₁ ψ` is the base change of `ψ` along `b ↦ b ⊗ 1`: the square with vertical maps
`ι₁ ⊗ id` commutes. -/
theorem homBaseChangeIncludeLeft_comp_rTensor (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) :
    (homBaseChangeIncludeLeft ψ).restrictScalars R ∘ₗ
        LinearMap.rTensor M (includeLeft : B →ₐ[R] B ⊗[R] B).toLinearMap =
      LinearMap.rTensor N (includeLeft : B →ₐ[R] B ⊗[R] B).toLinearMap ∘ₗ ψ.restrictScalars R :=
  homBaseChange_comp_rTensor R B _ ψ

/-- `e₂ ψ` is the base change of `ψ` along `b ↦ 1 ⊗ b`: the square with vertical maps
`ι₂ ⊗ id` commutes. -/
theorem homBaseChangeIncludeRight_comp_rTensor (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N) :
    (homBaseChangeIncludeRight ψ).restrictScalars R ∘ₗ
        LinearMap.rTensor M (includeRight : B →ₐ[R] B ⊗[R] B).toLinearMap =
      LinearMap.rTensor N (includeRight : B →ₐ[R] B ⊗[R] B).toLinearMap ∘ₗ ψ.restrictScalars R :=
  homBaseChange_comp_rTensor R B _ ψ

/-- `e₁ ψ` is the unique `B ⊗[R] B`-linear map making the square along `ι₁` commute. -/
theorem eq_homBaseChangeIncludeLeft_of_comp_rTensor (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N)
    (α : (B ⊗[R] B) ⊗[R] M →ₗ[B ⊗[R] B] (B ⊗[R] B) ⊗[R] N)
    (h : α.restrictScalars R ∘ₗ
        LinearMap.rTensor M (includeLeft : B →ₐ[R] B ⊗[R] B).toLinearMap =
      LinearMap.rTensor N (includeLeft : B →ₐ[R] B ⊗[R] B).toLinearMap ∘ₗ ψ.restrictScalars R) :
    α = homBaseChangeIncludeLeft ψ :=
  homBaseChange_eq_of_comp_rTensor R B _ ψ α h

/-- `e₂ ψ` is the unique `B ⊗[R] B`-linear map making the square along `ι₂` commute. -/
theorem eq_homBaseChangeIncludeRight_of_comp_rTensor (ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N)
    (α : (B ⊗[R] B) ⊗[R] M →ₗ[B ⊗[R] B] (B ⊗[R] B) ⊗[R] N)
    (h : α.restrictScalars R ∘ₗ
        LinearMap.rTensor M (includeRight : B →ₐ[R] B ⊗[R] B).toLinearMap =
      LinearMap.rTensor N (includeRight : B →ₐ[R] B ⊗[R] B).toLinearMap ∘ₗ ψ.restrictScalars R) :
    α = homBaseChangeIncludeRight ψ :=
  homBaseChange_eq_of_comp_rTensor R B _ ψ α h

/-- The pullback `e₁` of `f_B` is `f_{B ⊗ B}`. -/
@[simp]
theorem homBaseChangeIncludeLeft_baseChange (f : M →ₗ[R] N) :
    homBaseChangeIncludeLeft (f.baseChange B) = f.baseChange (B ⊗[R] B) :=
  homBaseChange_baseChange R B _ f

/-- The pullback `e₂` of `f_B` is `f_{B ⊗ B}`. -/
@[simp]
theorem homBaseChangeIncludeRight_baseChange (f : M →ₗ[R] N) :
    homBaseChangeIncludeRight (f.baseChange B) = f.baseChange (B ⊗[R] B) :=
  homBaseChange_baseChange R B _ f

/-- The two pullbacks agree on a base change `f_B`. -/
theorem homBaseChangeIncludeLeft_baseChange_eq_includeRight (f : M →ₗ[R] N) :
    homBaseChangeIncludeLeft (f.baseChange B) = homBaseChangeIncludeRight (f.baseChange B) := by
  simp

end Stacks.Descent

end
