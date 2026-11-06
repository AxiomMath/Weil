module

public import Weil.Attr
public import Weil.Defs.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import Weil.Defs.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom

/-!
# Openness of the locus of flat unramified local homomorphisms

Let `A` be a noetherian ring and `B` a finitely generated `A`-algebra. For a prime `q` of `B`
lying over `p = q ∩ A`, consider the local homomorphism `A_p → B_q`. The set of primes `q` at
which `B_q` is flat over `A_p` and `A_p → B_q` is an unramified local homomorphism is open in
`Spec B`: it is the intersection of the unramified locus and the flat locus, both of which are
open.

## Main results

- `Algebra.flat_localization_atPrime_iff`: `B_q` is flat over `A_p` iff it is flat over `A`.
- `Algebra.isOpen_setOf_flat_and_isUnramifiedLocal`: the locus of primes `q` of `B` at which
  `A_{q ∩ A} → B_q` is flat and an unramified local homomorphism is open.

## Implementation notes

The algebra structure of `B_q` over `A_{q ∩ A}` is `Localization.AtPrime.algebraOfLiesOver`, the
one induced by `A → B`. The pointwise statements are given for any algebra structure satisfying
`Localization.AtPrime.IsLiesOverAlgebra`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
* [Stacks, Tag 00RC] (openness of the flat locus)
-/

@[expose] public section

namespace Algebra

section Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

/-- `B_q` is flat over `A_p` if and only if it is flat over `A`. -/
lemma flat_localization_atPrime_iff :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) ↔
      Module.Flat A (Localization.AtPrime q) :=
  Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _

end Pointwise

/-- Flatness over `A` of the localization of `B` at a prime `q`, in its two forms. -/
lemma flat_localizedModule_atPrime_iff {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsPrime] :
    Module.Flat A (LocalizedModule.AtPrime q B) ↔ Module.Flat A (Localization.AtPrime q) :=
  Module.Flat.equiv_iff
    ((IsLocalizedModule.linearEquiv q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl B)
      (Algebra.linearMap B (Localization.AtPrime q))).restrictScalars A)

attribute [local instance] Localization.AtPrime.algebraOfLiesOver in
/-- **The locus of flat unramified local homomorphisms is open.** Let `A` be a noetherian ring and
`B` a finitely generated `A`-algebra. The set of primes `q` of `B` such that `B_q` is flat over
`A_{q ∩ A}` and `A_{q ∩ A} → B_q` is an unramified local homomorphism is open in `Spec B`. -/
@[weil "lem_fk101_etale_locus_open"]
theorem isOpen_setOf_flat_and_isUnramifiedLocal (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [Algebra.FiniteType A B] :
    IsOpen {q : PrimeSpectrum B |
      Module.Flat (Localization.AtPrime (q.asIdeal.under A)) (Localization.AtPrime q.asIdeal) ∧
        IsUnramifiedLocal (Localization.AtPrime (q.asIdeal.under A))
          (Localization.AtPrime q.asIdeal)} := by
  have hflat := Module.isOpen_setOf_flat_localizedModule_atPrime_of_isNoetherianRing
    (R := A) (S := B) (M := B)
  have hunr := isOpen_unramifiedLocus (R := A) (A := B)
  convert hflat.inter hunr using 1
  ext q
  exact and_congr ((flat_localization_atPrime_iff _ _).trans
    (flat_localizedModule_atPrime_iff _).symm)
    (isUnramifiedAt_iff_isUnramifiedLocal A (q.asIdeal.under A) q.asIdeal).symm

end Algebra

/-! ### A local-étale homomorphism is a localization of an étale one -/

/-!
# A local-étale homomorphism is a localization of an étale one

Let `A → B` be a local-étale homomorphism of noetherian local rings
(`RingHom.IsEtaleLocalHom`). Then there are an étale `A`-algebra `C` and a prime `𝔭 ⊆ C` with
`B ≃ₐ[A] C_𝔭`.

Write `B ≃ₐ[A] (C₀)_𝔮` for a finitely generated `A`-algebra `C₀` and a prime `𝔮` of `C₀`. Since
`A → B` is local, `𝔮` lies over the maximal ideal of `A`, so `A_{𝔮 ∩ A} → (C₀)_𝔮` is flat and
unramified, and `C₀` is étale at `𝔮`. The étale locus is open, so some basic open `D(f) ∋ 𝔮` lies
in it, and `C = (C₀)_f` with `𝔭 = 𝔮 C` works.

## Main results

* `Algebra.exists_etale_algEquiv_localization_atPrime_of_isEtaleLocalHom`: the statement above.
* `Algebra.isEtaleAt_of_isEtaleLocalHom_of_algEquiv`: if `(C₀)_𝔮 ≃ₐ[A] B` with `C₀` of finite
  type and `A → B` local-étale, then `C₀` is étale over `A` at `𝔮`.

## Implementation notes

Étaleness of `A → C` is Mathlib's `Algebra.Etale` (flat, formally unramified, finitely
presented), which for a noetherian base is the source's notion. The openness of the étale locus
used is `Algebra.exists_etale_of_isEtaleAt`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

@[expose] public section

universe u v w

namespace Algebra

open IsLocalRing

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

/-- If `A → B` is local-étale and `B ≃ₐ[A] (C₀)_𝔮` for a finite type `A`-algebra `C₀` and a prime
`𝔮` of `C₀`, then `C₀` is étale over `A` at `𝔮`. -/
theorem isEtaleAt_of_isEtaleLocalHom_of_algEquiv (h : (algebraMap A B).IsEtaleLocalHom)
    {C : Type w} [CommRing C] [Algebra A C] [FiniteType A C] (q : Ideal C) [q.IsPrime]
    (e : Localization.AtPrime q ≃ₐ[A] B) : IsEtaleAt A q := by
  obtain ⟨_, hflat, hunr⟩ := (isEtaleLocalHom_algebraMap_iff A B).1 h
  have hfu : FormallyUnramified A B :=
    (isUnramifiedLocal_iff_formallyUnramified A B).1 hunr
  have : FormallyUnramified A (Localization.AtPrime q) := .of_equiv e.symm
  have : Module.Flat A (Localization.AtPrime q) := Module.Flat.of_linearEquiv e.toLinearEquiv
  have : IsUnramifiedAt A q := ‹_›
  let p : Ideal A := q.under A
  have : q.LiesOver p := ⟨rfl⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).2 ‹_›
  have : FinitePresentation A C := FinitePresentation.of_finiteType.mp inferInstance
  exact IsEtaleAt.of_flat_of_map_eq_maximalIdeal p q
    ((isUnramifiedAt_iff_map_eq A p q).mp inferInstance).2

variable (A B) in
/-- **A local-étale homomorphism is a localization of an étale one.** If `A → B` is a
local-étale homomorphism of noetherian local rings, there are an étale `A`-algebra `C` and a
prime ideal `𝔭` of `C` with `C_𝔭 ≃ₐ[A] B`. -/
@[weil "lem_fk101_local_etale_is_localization_of_etale"]
theorem exists_etale_algEquiv_localization_atPrime_of_isEtaleLocalHom
    (h : (algebraMap A B).IsEtaleLocalHom) :
    ∃ (C : Type v) (_ : CommRing C) (_ : Algebra A C), Etale A C ∧
      ∃ (𝔭 : Ideal C) (_ : 𝔭.IsPrime), Nonempty (Localization.AtPrime 𝔭 ≃ₐ[A] B) := by
  have hft : EssFiniteType A B := ((isEtaleLocalHom_algebraMap_iff A B).1 h).1
  obtain ⟨C₀, _, _, _, q, _, ⟨e⟩⟩ :=
    essFiniteType_iff_exists_algEquiv_localization_atPrime.mp hft
  have : IsEtaleAt A q := isEtaleAt_of_isEtaleLocalHom_of_algEquiv h q e
  have : FinitePresentation A C₀ := FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨f, hf, het⟩ := exists_etale_of_isEtaleAt (R := A) q
  let 𝔭 : Ideal (Localization.Away f) := q.map (algebraMap C₀ (Localization.Away f))
  have hdisj : Disjoint (Submonoid.powers f : Set C₀) q := by
    rw [Set.disjoint_right]
    intro x hx hx'
    obtain ⟨n, rfl⟩ := hx'
    exact hf (‹q.IsPrime›.mem_of_pow_mem n hx)
  have : 𝔭.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ q ‹_› hdisj
  have hcomap : 𝔭.under C₀ = q :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hdisj
  -- `(C₀_f)_𝔭` is a localization of `C₀` at `q`.
  have : IsLocalization.AtPrime (Localization.AtPrime 𝔭) q := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers f) (Localization.AtPrime 𝔭) 𝔭
    have heq : (𝔭.under C₀).primeCompl = q.primeCompl := by
      ext x
      simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe, hcomap]
    change IsLocalization q.primeCompl _
    exact heq ▸ this
  let e' : Localization.AtPrime 𝔭 ≃ₐ[A] Localization.AtPrime q :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime 𝔭)
      (Localization.AtPrime q)).restrictScalars A
  exact ⟨Localization.Away f, inferInstance, inferInstance, het, 𝔭, ‹_›, ⟨e'.trans e⟩⟩

end Algebra
