module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.InvariantsEffective
public import WeilFrontier.AlgebraicGeometry.Descent.Module.Pushforward
public import Weil.Attr

/-!
# Affine descent data along a faithfully flat map are effective

Let `R → A` be a faithfully flat homomorphism of commutative rings and `(N, σ)` an affine
descent datum for `R → A`, with module of invariants `N^σ = {n ∈ N | σ (n ⊗ 1) = 1 ⊗ n}`.
The map `α : N^σ ⊗[R] A → N`, `m ⊗ b ↦ b • m`, is an isomorphism; it is `A`-linear for the
action of `A` on the right factor of `N^σ ⊗[R] A`.

## Main definitions

* `ModuleCat.DescentData.invariantsTensorLift`: the map `α : N^σ ⊗[R] A → N`,
  `m ⊗ b ↦ b • m`.
* `ModuleCat.DescentData.invariantsTensorLinearEquiv`: `α` as a linear isomorphism, for a
  faithfully flat `R → A`.

## Main results

* `ModuleCat.DescentData.bijective_invariantsTensorLift`: for a faithfully flat `R → A`, `α` is
  bijective.
* `ModuleCat.DescentData.invariantsTensorLift_lTensor_mulLeft`: `α` is linear for the action of
  `A` on the right factor.

## Implementation notes

The bijectivity is deduced from `Stacks.Descent.invariantsTensorEquiv`, the isomorphism
`A ⊗[R] N^σ ≃ₗ[A] N`, `a ⊗ m ↦ a • m`, which holds for every universally injective ring map,
in particular for a faithfully flat one (`Algebra.UniversallyInjective.of_faithfullyFlat`):
`α` is that isomorphism composed with the swap of the two tensor factors. That isomorphism
needs `R` and `A` in one universe, and so do the results here.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], Appendix A III.5
* [Grothendieck, *FGA*, Exp. 190, Thm. 1]
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
-/

/- Effectivity of affine descent data:
FK's `A → B` is `R → A` here, FK's `N^σ ⊗ B` is `invariantSubmodule R A D ⊗[R] A`. -/

@[expose] public section

noncomputable section

universe u w

namespace ModuleCat.DescentData

open TensorProduct

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The map `α : N^σ ⊗[R] A → N`, `m ⊗ b ↦ b • m`, from the base extension of the invariants of
an affine descent datum `(N, σ)` to its module. -/
def invariantsTensorLift (D : DescentData.{u, u, w} R A) :
    invariantSubmodule R A D ⊗[R] A →ₗ[R] restrictModule R A D.module :=
  TensorProduct.lift
    { toFun := fun m =>
        { toFun := fun b => ((b • (m.1 : D.module) : D.module) : restrictModule R A D.module)
          map_add' := fun b c => add_smul b c (m.1 : D.module)
          map_smul' := fun r b => by
            change (r • b) • (m.1 : D.module) = algebraMap R A r • b • (m.1 : D.module)
            rw [Algebra.smul_def, mul_smul] }
      map_add' := fun m n => by
        ext b
        exact smul_add b (m.1 : D.module) (n.1 : D.module)
      map_smul' := fun r m => by
        ext b
        change b • algebraMap R A r • (m.1 : D.module) =
          algebraMap R A r • b • (m.1 : D.module)
        rw [smul_comm] }

@[simp]
theorem invariantsTensorLift_tmul (D : DescentData.{u, u, w} R A)
    (m : invariantSubmodule R A D) (b : A) :
    invariantsTensorLift D (m ⊗ₜ[R] b) =
      ((b • (m.1 : D.module) : D.module) : restrictModule R A D.module) := rfl

/-- `α` is linear for the action of `A` on the right factor of `N^σ ⊗[R] A`:
`α (m ⊗ c b) = c • α (m ⊗ b)`. -/
theorem invariantsTensorLift_lTensor_mulLeft (D : DescentData.{u, u, w} R A) (c : A)
    (x : invariantSubmodule R A D ⊗[R] A) :
    invariantsTensorLift D ((LinearMap.mulLeft R c).lTensor _ x) =
      ((c • (invariantsTensorLift D x : D.module) : D.module) :
        restrictModule R A D.module) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    exact (smul_zero c).symm
  | tmul m b =>
    change (c * b) • (m.1 : D.module) = c • b • (m.1 : D.module)
    rw [mul_smul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    exact (smul_add c (invariantsTensorLift D x : D.module)
      (invariantsTensorLift D y : D.module)).symm

/-- `α` is the isomorphism `Stacks.Descent.invariantsTensorEquiv` after swapping the two
tensor factors. -/
theorem invariantsTensorLift_apply_eq (h : Algebra.UniversallyInjective R A)
    (D : DescentData.{u, u, w} R A) (x : invariantSubmodule R A D ⊗[R] A) :
    (invariantsTensorLift D x : D.module) =
      Stacks.Descent.invariantsTensorEquiv R A h D (TensorProduct.comm R _ A x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    rfl
  | tmul m b =>
    rw [TensorProduct.comm_tmul, Stacks.Descent.invariantsTensorEquiv_tmul]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy

/-- **Effectivity of affine descent data along a faithfully flat map.** For a faithfully flat
`R → A` and an affine descent datum `(N, σ)` for `R → A`, the map
`α : N^σ ⊗[R] A → N`, `m ⊗ b ↦ b • m`, is bijective. -/
@[weil "lem_fka3_affine_descent_datum_effective"]
theorem bijective_invariantsTensorLift [Module.FaithfullyFlat R A]
    (D : DescentData.{u, u, w} R A) :
    Function.Bijective (invariantsTensorLift D) := by
  have h := Algebra.UniversallyInjective.of_faithfullyFlat R A
  have he : (fun x => (invariantsTensorLift D x : D.module)) =
      (Stacks.Descent.invariantsTensorEquiv R A h D) ∘ (TensorProduct.comm R _ A) :=
    funext (invariantsTensorLift_apply_eq h D)
  have hb : Function.Bijective
      ((Stacks.Descent.invariantsTensorEquiv R A h D) ∘ (TensorProduct.comm R _ A)) :=
    (Stacks.Descent.invariantsTensorEquiv R A h D).bijective.comp
      (TensorProduct.comm R _ A).bijective
  rw [← he] at hb
  exact hb

/-- For a faithfully flat `R → A`, the map `α : N^σ ⊗[R] A → N`, `m ⊗ b ↦ b • m`, as a linear
isomorphism. -/
def invariantsTensorLinearEquiv [Module.FaithfullyFlat R A]
    (D : DescentData.{u, u, w} R A) :
    (invariantSubmodule R A D ⊗[R] A) ≃ₗ[R] restrictModule R A D.module :=
  LinearEquiv.ofBijective (invariantsTensorLift D) (bijective_invariantsTensorLift D)

@[simp]
theorem invariantsTensorLinearEquiv_tmul [Module.FaithfullyFlat R A]
    (D : DescentData.{u, u, w} R A) (m : invariantSubmodule R A D) (b : A) :
    invariantsTensorLinearEquiv D (m ⊗ₜ[R] b) =
      ((b • (m.1 : D.module) : D.module) : restrictModule R A D.module) := rfl

end ModuleCat.DescentData

end

end
