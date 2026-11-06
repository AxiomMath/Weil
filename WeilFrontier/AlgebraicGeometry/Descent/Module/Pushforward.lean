module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.Pushforward
public import WeilFrontier.Defs.AlgebraicGeometry.Descent.Module.DescentData
public import Weil.Attr

/-!
# Invariants of an affine descent datum

Let `R → A` be a homomorphism of commutative rings and `(N, σ)` an affine descent datum for
`R → A`, that is, an object of `ModuleCat.DescentData R A`. Its module of invariants is the
`R`-submodule
`N^σ = {n ∈ N | σ (n ⊗ 1) = 1 ⊗ n}`
of `N`, regarded as an `R`-module by restriction of scalars. This is
`ModuleCat.invariantSubmodule R A D`, the object part of the functor `ModuleCat.pushforward`.

## Main results

* `ModuleCat.mem_invariantSubmodule_iff`: `n ∈ N^σ ↔ σ (n ⊗ 1) = 1 ⊗ n`.
* `ModuleCat.transition_tmul_one_of_mem_invariantSubmodule`: for `n ∈ N^σ`,
  `σ (n ⊗ 1) = 1 ⊗ n`.

## Implementation notes

The invariants are not given a new definition: they are `ModuleCat.invariantSubmodule`, whose
defining condition is stated through the `R`-linear map `DescentData.transitionRestrictScalars`.
The lemmas here restate membership through the `A ⊗[R] A`-linear isomorphism
`DescentData.transition` itself.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], Appendix A III
* [Stacks Project, Tag 08X5](https://stacks.math.columbia.edu/tag/08X5)
-/

/- FK's module of descent invariants is
StacksFrontier's `ModuleCat.invariantSubmodule` (reused, no new definition); the lemma below
identifies its carrier with FK's `{n ∈ N : σ (n ⊗ 1) = 1 ⊗ n}`. FK's `A → B` is `R → A` here. -/

public section

universe u v w

namespace ModuleCat

open TensorProduct

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- An element `n` of the underlying module of a descent datum `(N, σ)` is invariant iff
`σ (n ⊗ 1) = 1 ⊗ n`. -/
@[weil "def_fka3_descent_invariants"]
theorem mem_invariantSubmodule_iff (D : DescentData.{u, v, w} R A)
    (n : restrictModule R A D.module) :
    n ∈ invariantSubmodule R A D ↔ D.transition (n ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] n :=
  Iff.rfl

/-- The descent isomorphism sends `n ⊗ 1` to `1 ⊗ n` for an invariant `n`. -/
@[simp]
theorem transition_tmul_one_of_mem_invariantSubmodule (D : DescentData.{u, v, w} R A)
    (n : invariantSubmodule R A D) :
    D.transition ((n : restrictModule R A D.module) ⊗ₜ[R] (1 : A)) =
      (1 : A) ⊗ₜ[R] (n : restrictModule R A D.module) :=
  n.2

end ModuleCat

end
