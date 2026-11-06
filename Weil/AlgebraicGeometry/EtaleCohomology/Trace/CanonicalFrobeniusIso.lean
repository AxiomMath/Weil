module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.RationalCohomologyFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusIso
public import Weil.Attr

/-!
# The Frobenius endomorphism of `H^ν(X_k̄, ℚ_ℓ)` is invertible

Let `X` be a scheme proper over a finite field `k`. For every `ν ≥ 0` the Frobenius
endomorphism `F_ν` of the rational ℓ-adic cohomology `H^ν(X_k̄, ℚ_ℓ)` is invertible.
Geometrically: the geometric Frobenius is a universal homeomorphism, so it induces an
automorphism of `RΓ_c(X_k̄, -)`, hence of every cohomology group, of their inverse limit and of
its tensor product with `ℚ_ℓ`.

## Main results

* `Weil.isIso_rationalFrobenius`: `F_ν` is an isomorphism in `ModuleCat ℚ_ℓ`.
* `Weil.isUnit_rationalFrobenius`: `F_ν` is a unit of `Module.End ℚ_ℓ (H^ν(X_k̄, ℚ_ℓ))`.

## Implementation notes

The result holds for any ℓ (no hypothesis `ℓ ≠ char k` is needed), and the underlying Stacks
statement holds for any ℓ-adic sheaf on any separated scheme of finite type over `k`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Weil

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The Frobenius `F_ν` of `H^ν(X_k̄, ℚ_ℓ)`, as a morphism of `ℚ_ℓ`-modules, is an
isomorphism. -/
theorem isIso_rationalFrobenius (ν : ℕ) :
    IsIso (ModuleCat.ofHom (rationalFrobenius B X f ℓ ν)) := by
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  exact LAdicSheaf.isIso_rationalGeometricCompactlySupportedFrobenius B X ℓ f
    (CompactificationOf.ofProper f) (AlgebraicClosure k) (ringChar k)
    (FiniteField.card k (ringChar k)).choose (FiniteField.card k (ringChar k)).choose_spec.2
    (LAdicSheaf.constantSystem B X ℓ) ν

/-- **The Frobenius endomorphism `F_ν` of `H^ν(X_k̄, ℚ_ℓ)` is invertible**, for `X` proper
over the finite field `k` and every `ν ≥ 0`. -/
@[weil "lem_fk401_frobenius_on_cohomology_invertible"]
theorem isUnit_rationalFrobenius (ν : ℕ) : IsUnit (rationalFrobenius B X f ℓ ν) := by
  have := isIso_rationalFrobenius B X f ℓ ν
  exact (Module.End.isUnit_iff _).2
    ((ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom (rationalFrobenius B X f ℓ ν))).1 this)

end Weil
