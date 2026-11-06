module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Weil.Attr

/-!
# Finitely generated local homomorphisms

Following Freitag–Kiehl, a ring homomorphism `A → B` is a *finitely generated local homomorphism*
if it is a local homomorphism and `B` is, as an `A`-algebra, isomorphic to the localization
`C_𝔮` of a finitely generated `A`-algebra `C` at a prime ideal `𝔮 ⊆ C`.

In Mathlib's language this is the conjunction of `IsLocalHom (algebraMap A B)` with
`Algebra.EssFiniteType A B` (a localization of a finite-type subalgebra at a submonoid). The two
descriptions agree because, for a local ring `B`, any such localization is already the
localization at the prime ideal lying under the maximal ideal of `B`.

## Main definitions

* `Algebra.IsFinitelyGeneratedLocal A B`: the algebra map `A → B` is local and `B` is essentially
  of finite type over `A`.

## Main results

* `Algebra.essFiniteType_iff_exists_algEquiv_localization_atPrime`: for a local ring `B`,
  `B` is essentially of finite type over `A` if and only if `B ≃ₐ[A] C_𝔮` for a finitely
  generated `A`-algebra `C` and a prime `𝔮` of `C`.
* `Algebra.isFinitelyGeneratedLocal_iff`: the Freitag–Kiehl form of the definition.

## Implementation notes

Freitag–Kiehl assume `A` and `B` noetherian and local; neither assumption is needed for the
definition or for the comparison, so locality and noetherianity are left to separate instances
where consumers need them. `IsLocalHom` only asks that the map reflect units; for local rings it
is equivalent to `φ(𝔪_A) ⊆ 𝔪_B` (`IsLocalRing.local_hom_TFAE`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

@[expose] public section

universe u v w

namespace Algebra

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- A *finitely generated local homomorphism* `A → B` (Freitag–Kiehl): the algebra map is a
local homomorphism and `B` is essentially of finite type over `A`. See
`Algebra.isFinitelyGeneratedLocal_iff` for the description as a localization `C_𝔮` of a finitely
generated `A`-algebra at a prime. -/
@[weil "def_fk101_finitely_generated_local_homomorphism"]
abbrev IsFinitelyGeneratedLocal : Prop :=
  IsLocalHom (algebraMap A B) ∧ EssFiniteType A B

variable {A B}

/-- A localization of a finitely generated `A`-algebra at a prime is essentially of finite type,
and so is any `A`-algebra isomorphic to one. -/
theorem EssFiniteType.of_algEquiv_localization_atPrime {C : Type w} [CommRing C] [Algebra A C]
    [FiniteType A C] (q : Ideal C) [q.IsPrime] (e : Localization.AtPrime q ≃ₐ[A] B) :
    EssFiniteType A B := by
  have : EssFiniteType C (Localization.AtPrime q) :=
    EssFiniteType.of_isLocalization (Localization.AtPrime q) q.primeCompl
  have : EssFiniteType A (Localization.AtPrime q) :=
    EssFiniteType.comp A C (Localization.AtPrime q)
  exact EssFiniteType.of_surjective e.toAlgHom e.surjective

/-- For a local ring `B`, an `A`-algebra `B` is essentially of finite type if and only if it is
isomorphic, as an `A`-algebra, to the localization `C_𝔮` of a finitely generated `A`-algebra `C`
at a prime ideal `𝔮`. -/
@[weil "def_fk101_finitely_generated_local_homomorphism"]
theorem essFiniteType_iff_exists_algEquiv_localization_atPrime [IsLocalRing B] :
    EssFiniteType A B ↔ ∃ (C : Type v) (_ : CommRing C) (_ : Algebra A C) (_ : FiniteType A C)
      (q : Ideal C) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[A] B) := by
  constructor
  · intro h
    obtain ⟨S₀, M, hft, hloc⟩ := (essFiniteType_iff_exists_subalgebra A B).mp h
    let q : Ideal S₀ := (IsLocalRing.maximalIdeal B).comap (algebraMap S₀ B)
    have : q.IsPrime := Ideal.comap_isPrime _ _
    have : IsLocalization q.primeCompl B := by
      refine IsLocalization.of_le M q.primeCompl ?_ ?_
      · intro m hm hq
        exact (IsLocalRing.mem_maximalIdeal _).mp hq (IsLocalization.map_units B ⟨m, hm⟩)
      · intro r hr
        by_contra hu
        exact hr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
    exact ⟨S₀, inferInstance, inferInstance, hft, q, inferInstance,
      ⟨(IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) B).restrictScalars A⟩⟩
  · rintro ⟨C, _, _, _, q, _, ⟨e⟩⟩
    exact EssFiniteType.of_algEquiv_localization_atPrime q e

/-- The Freitag–Kiehl description: `A → B` is a finitely generated local homomorphism if and only
if it is a local homomorphism and `B ≃ₐ[A] C_𝔮` for a finitely generated `A`-algebra `C` and a
prime `𝔮` of `C`. -/
theorem isFinitelyGeneratedLocal_iff [IsLocalRing B] :
    IsFinitelyGeneratedLocal A B ↔ IsLocalHom (algebraMap A B) ∧
      ∃ (C : Type v) (_ : CommRing C) (_ : Algebra A C) (_ : FiniteType A C)
        (q : Ideal C) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[A] B) :=
  and_congr_right' essFiniteType_iff_exists_algEquiv_localization_atPrime

/-- A localization at a prime of a finitely generated algebra is local, so the hypothesis
`IsLocalRing B` is automatic in the `C_𝔮` description. -/
theorem IsFinitelyGeneratedLocal.of_algEquiv_localization_atPrime {C : Type w} [CommRing C]
    [Algebra A C] [FiniteType A C] (q : Ideal C) [q.IsPrime]
    (e : Localization.AtPrime q ≃ₐ[A] B) (h : IsLocalHom (algebraMap A B)) :
    IsFinitelyGeneratedLocal A B :=
  ⟨h, EssFiniteType.of_algEquiv_localization_atPrime q e⟩

/-- The target of a finitely generated local homomorphism given as `C_𝔮` is a local ring. -/
theorem isLocalRing_of_algEquiv_localization_atPrime {C : Type w} [CommRing C] [Algebra A C]
    (q : Ideal C) [q.IsPrime] (e : Localization.AtPrime q ≃ₐ[A] B) : IsLocalRing B :=
  have : Nontrivial B := e.injective.nontrivial
  IsLocalRing.of_surjective' e.toRingEquiv.toRingHom e.surjective

namespace IsFinitelyGeneratedLocal

variable (h : IsFinitelyGeneratedLocal A B)
include h

theorem isLocalHom : IsLocalHom (algebraMap A B) := h.1

theorem essFiniteType : EssFiniteType A B := h.2

end IsFinitelyGeneratedLocal

end Algebra

end
