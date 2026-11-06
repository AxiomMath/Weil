module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import WeilFrontier.Defs.RingTheory.EssentialFiniteness
public import WeilFrontier.Defs.RingTheory.Unramified.LocalRing

/-!
# Local-étale homomorphisms

A homomorphism `A → B` of noetherian local rings is *local-étale* if it is a finitely generated
local homomorphism (a local homomorphism with `B` essentially of finite type over `A`), `B` is
flat over `A`, and `A → B` is an unramified local homomorphism (`m_A B = m_B` and the residue
field extension is finite separable).

This notion is `RingHom.IsEtaleLocalHom`: a local homomorphism of noetherian local rings which is
flat, formally unramified and essentially of finite type. Under essential finite type, formal
unramifiedness is the same as being an unramified local homomorphism
(`Algebra.isUnramifiedLocal_iff_formallyUnramified`), which gives the comparison below.

## Main results

* `Algebra.isEtaleLocalHom_algebraMap_iff`: for a local homomorphism `A → B` of noetherian local
  rings, `RingHom.IsEtaleLocalHom (algebraMap A B)` holds iff `B` is essentially of finite type
  and flat over `A` and `A → B` is an unramified local homomorphism.
* `Algebra.isEtaleLocalHom_algebraMap_of_isFinitelyGeneratedLocal`: the definition in the form
  of the source, starting from a finitely generated local homomorphism.

## Implementation notes

The notion is not redefined: `RingHom.IsEtaleLocalHom` is used, and its relation to étaleness at a
prime of a finite type algebra is `Algebra.isEtaleAt_iff_isEtaleLocalHom`. Being a local
homomorphism is an instance argument `IsLocalHom (algebraMap A B)`, since the unramified condition
depends on it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1.4
* [Stacks Project, Tag 0258]
-/

@[expose] public section

universe u v

namespace Algebra

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]

/-- A local homomorphism `A → B` of noetherian local rings is local-étale
(`RingHom.IsEtaleLocalHom`) if and only if `B` is essentially of finite type and flat over `A`
and `A → B` is an unramified local homomorphism. -/
@[weil "def_fk101_local_etale_homomorphism"]
theorem isEtaleLocalHom_algebraMap_iff [IsLocalHom (algebraMap A B)] :
    (algebraMap A B).IsEtaleLocalHom ↔
      EssFiniteType A B ∧ Module.Flat A B ∧ IsUnramifiedLocal A B := by
  unfold RingHom.IsEtaleLocalHom
  rw [RingHom.flat_algebraMap_iff, RingHom.formallyUnramified_algebraMap,
    RingHom.essFiniteType_algebraMap]
  constructor
  · rintro ⟨hf, hu, he⟩
    exact ⟨he, hf, (isUnramifiedLocal_iff_formallyUnramified A B).2 hu⟩
  · rintro ⟨he, hf, hu⟩
    exact ⟨hf, (isUnramifiedLocal_iff_formallyUnramified A B).1 hu, he⟩

variable {A B}

/-- The source's form of the definition: a finitely generated local homomorphism of noetherian
local rings which is flat and an unramified local homomorphism is local-étale. -/
theorem isEtaleLocalHom_algebraMap_of_isFinitelyGeneratedLocal
    (h : IsFinitelyGeneratedLocal A B) [Module.Flat A B]
    (hu : letI := h.1; IsUnramifiedLocal A B) :
    letI := h.1; (algebraMap A B).IsEtaleLocalHom :=
  letI := h.1
  haveI := h.2
  (isEtaleLocalHom_algebraMap_iff A B).2 ⟨inferInstance, inferInstance, hu⟩

/-- A local-étale homomorphism is a finitely generated local homomorphism. -/
theorem IsFinitelyGeneratedLocal.of_isEtaleLocalHom [IsLocalHom (algebraMap A B)]
    (h : (algebraMap A B).IsEtaleLocalHom) : IsFinitelyGeneratedLocal A B :=
  ⟨inferInstance, ((isEtaleLocalHom_algebraMap_iff A B).1 h).1⟩

/-- A local-étale homomorphism is flat. -/
theorem flat_of_isEtaleLocalHom [IsLocalHom (algebraMap A B)]
    (h : (algebraMap A B).IsEtaleLocalHom) : Module.Flat A B :=
  ((isEtaleLocalHom_algebraMap_iff A B).1 h).2.1

/-- A local-étale homomorphism is an unramified local homomorphism. -/
theorem isUnramifiedLocal_of_isEtaleLocalHom [IsLocalHom (algebraMap A B)]
    (h : (algebraMap A B).IsEtaleLocalHom) : IsUnramifiedLocal A B :=
  ((isEtaleLocalHom_algebraMap_iff A B).1 h).2.2

end Algebra
