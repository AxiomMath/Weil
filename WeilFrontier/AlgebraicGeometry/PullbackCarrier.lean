module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Weil.Attr

/-!
# Primes of a tensor product over two primes with a common contraction

Let `R → A` and `R → C` be ring homomorphisms, and let `𝔭 ⊆ A`, `𝔮 ⊆ C` be primes with the same
preimage in `R`. Then there is a prime of `A ⊗[R] C` whose preimages under `a ↦ a ⊗ 1` and
`c ↦ 1 ⊗ c` are `𝔭` and `𝔮`. Equivalently, the map
`Spec (A ⊗[R] C) → Spec A ×_{Spec R} Spec C` of underlying sets is surjective.

## Main results

* `Ideal.exists_isPrime_tensorProduct_comap_eq`: the existence of such a prime.

## Implementation notes

The proof goes through schemes: `Spec` sends the pushout square of `A ⊗[R] C` to a pullback
square (`AlgebraicGeometry.isPullback_SpecMap_of_isPushout`), and a pullback of schemes is
surjective onto pairs of points with a common image
(`AlgebraicGeometry.Scheme.exists_preimage_of_isPullback`). This needs the three rings in one
universe.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

namespace Ideal

/-- **A prime of a tensor product over two primes with a common contraction.** If `p ⊆ A` and
`q ⊆ C` are primes of two `R`-algebras with the same preimage in `R`, some prime of `A ⊗[R] C`
contracts to `p` along `a ↦ a ⊗ 1` and to `q` along `c ↦ 1 ⊗ c`. -/
@[weil "lem_fk101_spec_tensor_surjective"]
theorem exists_isPrime_tensorProduct_comap_eq {R A C : Type u} [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra R C] (p : Ideal A) [p.IsPrime] (q : Ideal C) [q.IsPrime]
    (h : p.comap (algebraMap R A) = q.comap (algebraMap R C)) :
    ∃ P : Ideal (A ⊗[R] C), P.IsPrime ∧
      P.comap Algebra.TensorProduct.includeLeftRingHom = p ∧
      P.comap Algebra.TensorProduct.includeRight.toRingHom = q := by
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R A C)
  obtain ⟨z, hz1, hz2⟩ := Scheme.exists_preimage_of_isPullback hpb
    (⟨p, inferInstance⟩ : PrimeSpectrum A) (⟨q, inferInstance⟩ : PrimeSpectrum C)
    (PrimeSpectrum.ext h)
  exact ⟨z.asIdeal, z.isPrime, congrArg PrimeSpectrum.asIdeal hz1,
    congrArg PrimeSpectrum.asIdeal hz2⟩

end Ideal

end
