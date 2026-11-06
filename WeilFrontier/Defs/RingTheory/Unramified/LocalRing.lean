module

public import Weil.Attr
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Unramified local homomorphisms

Let `R → S` be a local homomorphism of local rings. It is called *unramified* if
`m_R · S = m_S` and the residue field extension `κ(R) → κ(S)` is finite and separable.

This is the classical (Freitag–Kiehl, Grothendieck) notion. It does not require `S` to be
essentially of finite type over `R`; for instance a noetherian local ring maps unramifiedly to its
completion, which is not formally unramified in general (its module of differentials need not
vanish). When `S` is essentially of finite type over `R`, it agrees with Mathlib's
`Algebra.FormallyUnramified` (`Algebra.isUnramifiedLocal_iff_formallyUnramified`), and at primes
of an essentially finite type algebra with `Algebra.IsUnramifiedAt`
(`Algebra.isUnramifiedAt_iff_isUnramifiedLocal`).

## Main definitions

- `Algebra.IsUnramifiedLocal R S`: the local homomorphism `algebraMap R S` is unramified.

## Main results

- `Algebra.isUnramifiedLocal_iff_formallyUnramified`: for `S` essentially of finite type over `R`,
  being an unramified local homomorphism is equivalent to being formally unramified.
- `Algebra.isUnramifiedAt_iff_isUnramifiedLocal`: for `S` essentially of finite type over `R` and
  a prime `q` of `S` over `p`, `S` is unramified at `q` iff `R_p → S_q` is an unramified local
  homomorphism.

## Implementation notes

The source states the notion for noetherian rings; noetherianity is not needed for the
definition and is dropped. Being a local homomorphism is the instance argument
`IsLocalHom (algebraMap R S)`, as in Mathlib, since the residue field map depends on it.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
* [Stacks, Tag 02FM]
-/

@[expose] public section

open IsLocalRing

namespace Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- A local homomorphism `R → S` of local rings is *unramified* if `m_R · S = m_S` and the
residue field extension `κ(R) → κ(S)` is finite and separable. -/
@[weil "def_fk101_unramified_local_homomorphism", mk_iff]
class IsUnramifiedLocal : Prop where
  map_maximalIdeal : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S
  finite_residueField : Module.Finite (ResidueField R) (ResidueField S)
  isSeparable_residueField : Algebra.IsSeparable (ResidueField R) (ResidueField S)

namespace IsUnramifiedLocal

variable {R S}

attribute [instance] finite_residueField isSeparable_residueField

/-- An unramified local homomorphism essentially of finite type is formally unramified. -/
instance formallyUnramified [EssFiniteType R S] [IsUnramifiedLocal R S] :
    FormallyUnramified R S :=
  .of_map_maximalIdeal (map_maximalIdeal (R := R) (S := S))

/-- A formally unramified local homomorphism essentially of finite type is unramified. -/
instance of_formallyUnramified [EssFiniteType R S] [FormallyUnramified R S] :
    IsUnramifiedLocal R S :=
  ⟨FormallyUnramified.map_maximalIdeal, inferInstance, inferInstance⟩

/-- The criterion with the finiteness of the residue field extension omitted: under
essential finite type it follows from the other two conditions. -/
lemma of_map_maximalIdeal_of_isSeparable [EssFiniteType R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    (H : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) : IsUnramifiedLocal R S :=
  have : FormallyUnramified R S := .of_map_maximalIdeal H
  inferInstance

end IsUnramifiedLocal

/-- For `S` essentially of finite type over `R`, an unramified local homomorphism is the same as
a formally unramified one. -/
lemma isUnramifiedLocal_iff_formallyUnramified [EssFiniteType R S] :
    IsUnramifiedLocal R S ↔ FormallyUnramified R S :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

end Algebra

namespace Algebra

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

instance _root_.Localization.AtPrime.isLocalHom_algebraMap_of_isLiesOverAlgebra :
    IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
  rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
  exact Localization.isLocalHom_localRingHom _ _ _ _

/-- For `S` essentially of finite type over `R` and a prime `q` of `S` over `p`, `S` is unramified
at `q` iff `R_p → S_q` is an unramified local homomorphism. -/
lemma isUnramifiedAt_iff_isUnramifiedLocal [EssFiniteType R S] :
    IsUnramifiedAt R q ↔ IsUnramifiedLocal (Localization.AtPrime p) (Localization.AtPrime q) := by
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  rw [isUnramifiedLocal_iff_formallyUnramified]
  exact ⟨fun _ ↦ .of_restrictScalars R _ _,
    fun _ ↦ Algebra.FormallyUnramified.comp _ (Localization.AtPrime p) _⟩

end Algebra
