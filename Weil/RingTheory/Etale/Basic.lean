module

public import Mathlib.RingTheory.Etale.Basic
public import Weil.Attr

/-!
# Tensor products of étale algebras

If `B` and `C` are étale `A`-algebras, then so is `B ⊗[A] C`: the algebra `B ⊗[A] C` is étale
over `B` by base change, and `B` is étale over `A`, so the composite `A → B → B ⊗[A] C`, which
is the structure map of `B ⊗[A] C`, is étale.

## Main results

* `Algebra.Etale.tensorProduct`: `B ⊗[A] C` is an étale `A`-algebra when `B` and `C` are.

## Implementation notes

The source states the result for noetherian rings, where its notion of étale homomorphism
agrees with `Algebra.Etale`; no noetherian hypothesis is needed here. The source composes
through `C` rather than `B`; the two routes are symmetric.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1
-/

public section

open TensorProduct

universe u v w

namespace Algebra.Etale

variable (A : Type u) (B : Type v) (C : Type w) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

/-- The tensor product of two étale `A`-algebras is an étale `A`-algebra. -/
@[weil "lem_fk101_tensor_product_of_etale_is_etale"]
theorem tensorProduct [Algebra.Etale A B] [Algebra.Etale A C] : Algebra.Etale A (B ⊗[A] C) :=
  Algebra.Etale.comp A B (B ⊗[A] C)

end Algebra.Etale
