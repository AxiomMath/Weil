module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.RationalCohomologyFrobenius
public import Mathlib.Topology.KrullDimension
public import Weil.Definitions

/-!
# The ℓ-adic Euler characteristic of a proper scheme over a finite field

Let `k` be a finite field, `ℓ` a prime and `X` a scheme proper over `k` of dimension `n`. With
`b_ν = dim_{ℚ_ℓ} H^ν(X_k̄, ℚ_ℓ)` the ℓ-adic Betti numbers, the *Euler characteristic* of `X` is

`χ(X) = ∑_{ν = 0}^{2n} (-1)^ν b_ν`.

## Main definitions

These are defined in `Weil.Definitions`:

* `Weil.schemeDimension`: the Krull dimension `n` of (the underlying space of) `X`, as a natural
  number.
* `Weil.bettiNumber`: `b_ν = dim_{ℚ_ℓ} H^ν(X_k̄, ℚ_ℓ)`.
* `Weil.eulerCharacteristic`: `χ(X) = ∑_{ν = 0}^{2n} (-1)^ν b_ν`.

## Main results

* `Weil.eulerCharacteristic_eq_sum_range`: if `X` has dimension `n`, then
  `χ(X) = ∑_{ν = 0}^{2n} (-1)^ν b_ν`.

## Implementation notes

The dimension `n` is the topological Krull dimension of `X`, which for a nonempty scheme proper
over a field is a natural number; for the empty scheme it is `⊥`, read here as `0` (then every
cohomology group vanishes and `χ = 0` in any reading). The upper bound `2n` of the sum is the
one of the source; it is read off from `X`, so `eulerCharacteristic` takes no dimension
argument.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Weil

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

theorem schemeDimension_eq_of_topologicalKrullDim_eq {n : ℕ}
    (h : topologicalKrullDim X.1 = n) : schemeDimension B X = n := by
  simp [schemeDimension, h]

/-- If `X` has dimension `n`, then `χ(X) = ∑_{ν = 0}^{2n} (-1)^ν b_ν`. -/
theorem eulerCharacteristic_eq_sum_range {n : ℕ} (h : topologicalKrullDim X.1 = n) :
    eulerCharacteristic B X f ℓ =
      ∑ ν ∈ Finset.range (2 * n + 1), (-1) ^ ν * (bettiNumber B X f ℓ ν : ℤ) := by
  rw [eulerCharacteristic, schemeDimension_eq_of_topologicalKrullDim_eq B X h]

end Weil
