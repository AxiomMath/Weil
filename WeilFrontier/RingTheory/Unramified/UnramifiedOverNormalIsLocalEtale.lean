module

public import Weil.Attr
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import StacksFrontier.RingTheory.Etale.LocalRingPropertyList
public import WeilFrontier.Defs.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom

/-!
# Unramified algebras over normal domains are flat

Let `A` be an integrally closed domain and `B` a local `A`-algebra, essentially of finite type
and formally unramified, such that `A → B` is injective. Then `B` is flat over `A`. In
particular, an injective unramified finitely generated local homomorphism `A → B` of noetherian
local rings with `A` normal is local-étale (EGA IV 18.10.1).

The proof follows the source. By the local structure of unramified algebras, `B` is a quotient
`P_Q / 𝔞` of the localization of a standard étale `A`-algebra `P` at a prime `Q`. Since `A` is
normal, so is `P_Q`; in particular it is a domain. A prime `𝔓` of `B` lying over the generic
point of `A` (it exists as `A → B` is injective) pulls back to a prime of `P_Q` containing `𝔞`
and lying over `0`, as does the zero ideal of `P_Q`. Since `P_Q` is quasi-finite over `A`, primes
of `P_Q` over the same prime of `A` are incomparable, so the pull-back of `𝔓` is `0` and `𝔞 = 0`.
Hence `B ≅ P_Q` is flat over `A`.

## Main results

* `Algebra.flat_of_formallyUnramified_of_injective`: an injective, formally unramified, local
  algebra essentially of finite type over an integrally closed domain is flat.
* `Algebra.isEtaleLocalHom_algebraMap_of_isUnramifiedLocal_of_injective`: an injective unramified
  local homomorphism `A → B` of noetherian local rings, `B` essentially of finite type over `A`
  and `A` normal, is local-étale.

## Implementation notes

The flatness statement needs neither noetherianity nor locality of `A`, nor that `A → B` is a
local homomorphism; these are only used to speak of a local-étale homomorphism. The source's
argument through the generic fibre (`Frac A ⊗_A P` is a finite product of fields) is replaced by
the incomparability of primes in the fibres of a quasi-finite algebra
(`Algebra.QuasiFinite.eq_of_le_of_under_eq`), which is the same fact.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1.5
* [A. Grothendieck, *EGA IV*, 18.10.1]
-/

public section

universe u v

open IsLocalRing

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- An injective, formally unramified algebra `B` over an integrally closed domain `A`, with `B`
local and essentially of finite type over `A`, is flat over `A`. -/
theorem flat_of_formallyUnramified_of_injective [IsDomain A] [IsIntegrallyClosed A]
    [IsLocalRing B] [EssFiniteType A B] [FormallyUnramified A B]
    (hinj : Function.Injective (algebraMap A B)) : Module.Flat A B := by
  -- `B` is a localization `C_q` of a finite type algebra `C`.
  obtain ⟨C, _, _, _, q, _, ⟨e⟩⟩ :=
    essFiniteType_iff_exists_algEquiv_localization_atPrime.mp ‹EssFiniteType A B›
  have : FormallyUnramified A (Localization.AtPrime q) := .of_equiv e.symm
  have : IsUnramifiedAt A q := ‹_›
  -- A standard étale algebra `P` surjects onto `C_f` for some `f ∉ q`.
  obtain ⟨f, hfq, P, φ, hφ⟩ := IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := A) q
  have hfu : ∀ y : Submonoid.powers f,
      IsUnit ((IsScalarTower.toAlgHom A C (Localization.AtPrime q)) y) := by
    rintro ⟨y, n, rfl⟩
    refine IsLocalization.map_units (M := q.primeCompl) _ ⟨f ^ n, ?_⟩
    exact fun h ↦ hfq (‹q.IsPrime›.mem_of_pow_mem n h)
  let g : Localization.Away f →ₐ[A] Localization.AtPrime q :=
    IsLocalization.liftAlgHom (M := Submonoid.powers f) hfu
  have hg : ∀ c : C, g (algebraMap C _ c) = algebraMap C _ c := fun c ↦ by
    simp [g]
  let ψ : P.Ring →ₐ[A] B := (e.toAlgHom.comp g).comp φ
  -- Every element of `B` is a fraction of values of `ψ`.
  have hψ : ∀ b : B, ∃ x t : P.Ring, IsUnit (ψ t) ∧ b * ψ t = ψ x := by
    intro b
    obtain ⟨z, rfl⟩ := e.surjective b
    obtain ⟨c, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl z
    obtain ⟨x, hx⟩ := hφ (algebraMap C _ c)
    obtain ⟨t, ht⟩ := hφ (algebraMap C _ s)
    have hψt : ψ t = e (algebraMap C _ s) := by simp [ψ, ht, hg]
    have hψx : ψ x = e (algebraMap C _ c) := by simp [ψ, hx, hg]
    refine ⟨x, t, ?_, ?_⟩
    · rw [hψt]
      exact (IsLocalization.map_units (M := q.primeCompl) _ ⟨s, hs⟩).map e
    · rw [hψt, hψx, ← map_mul, IsLocalization.mk'_spec]
  -- The localization `P_Q` at the prime `Q` under the maximal ideal of `B`.
  let Q : Ideal P.Ring := (maximalIdeal B).comap ψ
  let Bt := Localization.AtPrime Q
  have hunit : ∀ y : Q.primeCompl, IsUnit (ψ y) := fun ⟨y, hy⟩ ↦ by
    by_contra h
    exact hy ((mem_maximalIdeal _).2 h)
  let θ : Bt →ₐ[A] B := IsLocalization.liftAlgHom (M := Q.primeCompl) hunit
  have hθ : ∀ x : P.Ring, θ (algebraMap P.Ring Bt x) = ψ x := fun x ↦ by simp [θ]
  have hθA : (θ : Bt →+* B).comp (algebraMap A Bt) = algebraMap A B := by
    ext a; exact θ.commutes a
  -- `θ` is surjective.
  have hsurj : Function.Surjective θ := by
    intro b
    obtain ⟨x, t, ht, hb⟩ := hψ b
    have htQ : t ∈ Q.primeCompl := fun h ↦ (mem_maximalIdeal _).1 h ht
    refine ⟨IsLocalization.mk' Bt x ⟨t, htQ⟩, ?_⟩
    rw [← ht.mul_left_inj, ← hθ t, ← map_mul, IsLocalization.mk'_spec, hθ, hθ, hb]
  -- `P_Q` is a normal domain, since `A` is.
  let p : Ideal A := Q.comap (algebraMap A P.Ring)
  have hnA : IsNormalDomain (Localization.AtPrime p) :=
    ⟨IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors,
      isIntegrallyClosed_of_isLocalization _ p.primeCompl
      p.primeCompl_le_nonZeroDivisors⟩
  have hnB : IsNormalDomain Bt :=
    (isNormalDomain_localizationAtPrime_iff_of_etale p Q rfl).1 hnA
  -- `P_Q` is quasi-finite over `A`.
  have : QuasiFinite A Bt := inferInstance
  -- A prime of `B` over the generic point of `A`.
  obtain ⟨𝔓, h𝔓, h𝔓A⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hinj ⊥
    (by rw [IsDomain.minimalPrimes_eq_singleton_bot]; rfl)
  let 𝔓' : Ideal Bt := 𝔓.comap (θ : Bt →+* B)
  have h𝔓'A : 𝔓'.under A = (⊥ : Ideal Bt).under A := by
    have hinj' : Function.Injective (algebraMap A Bt) := by
      have h2 : Function.Injective ((θ : Bt →+* B) ∘ algebraMap A Bt) := by
        rw [← RingHom.coe_comp, hθA]
        exact hinj
      exact h2.of_comp
    rw [Ideal.under, Ideal.under, Ideal.comap_bot_of_injective _ hinj']
    change Ideal.comap (algebraMap A Bt) (Ideal.comap (θ : Bt →+* B) 𝔓) = ⊥
    rw [Ideal.comap_comap, hθA, h𝔓A]
  have hbot : (⊥ : Ideal Bt) = 𝔓' :=
    QuasiFinite.eq_of_le_of_under_eq (R := A) _ _ bot_le h𝔓'A.symm
  -- `θ` is injective.
  have hinjθ : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ 𝔓' := by
      change (θ : Bt →+* B) x ∈ 𝔓
      have hx' : (θ : Bt →+* B) x = 0 := hx
      rw [hx']
      exact 𝔓.zero_mem
    rw [← hbot] at this
    exact this
  let e' : Bt ≃ₐ[A] B := AlgEquiv.ofBijective θ ⟨hinjθ, hsurj⟩
  have : Module.Flat P.Ring Bt := IsLocalization.flat Bt Q.primeCompl
  have : Module.Flat A Bt := Module.Flat.trans A P.Ring Bt
  exact Module.Flat.of_linearEquiv e'.symm.toLinearEquiv

/-- **Unramified over normal is local-étale.** Let `A → B` be an injective local homomorphism of
noetherian local rings which is unramified, with `B` essentially of finite type over `A` and `A`
an integrally closed domain. Then `A → B` is local-étale. -/
@[weil "lem_fk101_unramified_over_normal_is_local_etale"]
theorem isEtaleLocalHom_algebraMap_of_isUnramifiedLocal_of_injective
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [IsDomain A] [IsIntegrallyClosed A] (h : IsFinitelyGeneratedLocal A B)
    (hu : letI := h.1; IsUnramifiedLocal A B) (hinj : Function.Injective (algebraMap A B)) :
    letI := h.1; (algebraMap A B).IsEtaleLocalHom := by
  let := h.1
  have := h.2
  have := (isUnramifiedLocal_iff_formallyUnramified A B).1 hu
  have := flat_of_formallyUnramified_of_injective hinj
  exact (isEtaleLocalHom_algebraMap_iff A B).2 ⟨inferInstance, inferInstance, hu⟩

end Algebra
