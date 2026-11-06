module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Weil.Attr

/-!
# Quasi-finite local homomorphisms

Let `A` be a local ring with maximal ideal `𝔪`, and `B` an `A`-algebra. The algebra map
`A → B` is a *quasi-finite local homomorphism* if it is a local homomorphism and the closed
fibre `B ⧸ 𝔪 B` is a finite-dimensional vector space over the residue field `A ⧸ 𝔪`.

## Main definitions

* `Algebra.IsQuasiFiniteLocalHom A B`: the algebra map `A → B` is local, and `B ⧸ 𝔪 B` is a
  finite `A ⧸ 𝔪`-module.

## Main results

* `Algebra.isQuasiFiniteLocalHom_iff_finite_restrictScalars`: the closed-fibre condition may
  equivalently be stated over `A` itself.
* `Algebra.IsQuasiFiniteLocalHom.of_finite`: a finite local homomorphism is quasi-finite.

## Implementation notes

The source works with noetherian local rings `A` and `B`. Neither noetherianity nor locality of
`B` is needed to state the definition, so they are not assumed; when `B` is local,
`IsLocalHom (algebraMap A B)` is equivalent to `𝔪 B ⊆ 𝔪(B)` (`IsLocalRing.local_hom_TFAE`),
which is the source's notion of a local homomorphism.

Mathlib's `Algebra.QuasiFiniteAt` asks for finite fibres over every prime of `A`; it is stronger
than the closed-fibre condition used here unless `B` is essentially of finite type over `A`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

open IsLocalRing

namespace Algebra

variable (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]

/-- The algebra map `A → B` out of a local ring `A` is a *quasi-finite local homomorphism* if it
is a local homomorphism and the closed fibre `B ⧸ 𝔪(A) B` is a finite module over the residue
field `A ⧸ 𝔪(A)`. -/
@[weil "def_fk101_quasi_finite_local_homomorphism"]
class IsQuasiFiniteLocalHom : Prop where
  /-- The algebra map is a local homomorphism. -/
  isLocalHom : IsLocalHom (algebraMap A B)
  /-- The closed fibre `B ⧸ 𝔪(A) B` is finite-dimensional over `A ⧸ 𝔪(A)`. -/
  finite_quotient :
    Module.Finite (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A).map (algebraMap A B))

theorem isQuasiFiniteLocalHom_iff :
    IsQuasiFiniteLocalHom A B ↔ IsLocalHom (algebraMap A B) ∧
      Module.Finite (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
  ⟨fun h ↦ ⟨h.isLocalHom, h.finite_quotient⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- The closed fibre `B ⧸ 𝔪(A) B` is finite over `A ⧸ 𝔪(A)` if and only if it is finite
over `A`. -/
theorem finite_quotient_iff_finite_restrictScalars :
    Module.Finite (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A).map (algebraMap A B)) ↔
      Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
  ⟨fun _ ↦ Module.Finite.trans (A ⧸ maximalIdeal A) _,
    fun _ ↦ Module.Finite.of_restrictScalars_finite A (A ⧸ maximalIdeal A) _⟩

theorem isQuasiFiniteLocalHom_iff_finite_restrictScalars :
    IsQuasiFiniteLocalHom A B ↔ IsLocalHom (algebraMap A B) ∧
      Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  rw [isQuasiFiniteLocalHom_iff, finite_quotient_iff_finite_restrictScalars]

namespace IsQuasiFiniteLocalHom

attribute [instance] isLocalHom finite_quotient

variable {A B}

/-- A quasi-finite local homomorphism has a closed fibre that is finite over `A`. -/
instance finite_restrictScalars [IsQuasiFiniteLocalHom A B] :
    Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
  ((isQuasiFiniteLocalHom_iff_finite_restrictScalars A B).1 ‹_›).2

theorem of_finite_restrictScalars [IsLocalHom (algebraMap A B)]
    [Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B))] :
    IsQuasiFiniteLocalHom A B :=
  (isQuasiFiniteLocalHom_iff_finite_restrictScalars A B).2 ⟨‹_›, ‹_›⟩

/-- A finite local homomorphism is a quasi-finite local homomorphism. -/
theorem of_finite [IsLocalHom (algebraMap A B)] [Module.Finite A B] :
    IsQuasiFiniteLocalHom A B :=
  have : Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ A ((maximalIdeal A).map (algebraMap A B))).toLinearMap
      Ideal.Quotient.mk_surjective
  of_finite_restrictScalars

end IsQuasiFiniteLocalHom

end Algebra

end
