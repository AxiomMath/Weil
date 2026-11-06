module

public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.Catenary.LocalCriterion
public import Weil.Defs.RingTheory.EssentialFiniteness
public import Weil.Attr

/-!
# Universally catenary rings and the dimension formula

A Noetherian ring `A` is *universally catenary* if every `A`-algebra of finite type is catenary
(`Ring.IsUniversallyCatenary`). Freitag and Kiehl define a Noetherian local ring `A` to be
universally catenary when the dimension formula
`dim B = dim B_𝔭 + dim B/𝔭`
holds for every local domain `B` essentially of finite type over `A` and every prime `𝔭` of `B`.
This file shows that the two notions agree, for every Noetherian ring `A`.

The forward direction uses that an algebra essentially of finite type over a universally catenary
ring is universally catenary, and that heights are additive in a universally catenary Noetherian
domain. For the converse, a local ring `T` essentially of finite type over `A` is catenary as soon
as `𝔮 ↦ dim T/𝔮` drops by exactly one along every covering pair of primes `𝔭 ⋖ 𝔮`
(Stacks 0ECF); the dimension formula for the local domain `T/𝔭` at the prime `𝔮/𝔭`, of height
one, is exactly that statement.

## Main results

* `Ring.IsUniversallyCatenary.ringKrullDim_eq_ringKrullDim_localization_add_ringKrullDim_quotient`:
  the dimension formula for a local domain essentially of finite type over a Noetherian
  universally catenary ring.
* `Ring.isCatenary_of_forall_ringKrullDim_eq`: a Noetherian local ring essentially of finite type
  over `A` is catenary when the dimension formula holds over `A`.
* `Ring.isUniversallyCatenary_iff_forall_ringKrullDim_eq`: a Noetherian ring is universally
  catenary if and only if the dimension formula holds for every local domain essentially of
  finite type over it.
* `Ring.IsUniversallyCatenary.ringKrullDim_eq_of_isFinitelyGeneratedLocal`: the dimension formula
  along a finitely generated local homomorphism `A → B` to a domain.

## Implementation notes

Freitag and Kiehl ask for the dimension formula only along finitely generated *local*
homomorphisms `A → B`. The characterisation proved here quantifies over all local domains
essentially of finite type over `A`, which is the standard form of the criterion (Ratliff; see
Matsumura, §31, and EGA IV 5.6.2); the restricted form along local homomorphisms is recorded as a
consequence. The algebras `B` range over the universe of `A`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
* [H. Matsumura, *Commutative Ring Theory*][Matsumura1986], §31
* [The Stacks Project, Tags 00NL, 0ECF][stacks-project]
-/

/- FK's printed condition for universally catenary rings (along finitely generated local
homomorphisms) is replaced by the standard (EGA/Stacks) meaning (all local domains essentially of
finite type); the definition itself is StacksFrontier's `Ring.IsUniversallyCatenary`. -/

@[expose] public section

universe u

open IsLocalRing

namespace Ring

/-- **The dimension formula over a universally catenary ring.** If `A` is Noetherian and
universally catenary and `B` is a local domain essentially of finite type over `A`, then
`dim B = dim B_𝔭 + dim B/𝔭` for every prime `𝔭` of `B`. -/
theorem IsUniversallyCatenary.ringKrullDim_eq_ringKrullDim_localization_add_ringKrullDim_quotient
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.EssFiniteType A B] (hA : Ring.IsUniversallyCatenary A)
    (p : Ideal B) [p.IsPrime] :
    ringKrullDim B = ringKrullDim (Localization.AtPrime p) + ringKrullDim (B ⧸ p) := by
  have : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  have hB : _root_.IsUniversallyCatenary B :=
    Ring.isUniversallyCatenary_iff_isUniversallyCatenary.mp (hA.of_essFiniteType (B := B))
  have h := catenary_height_add hB p (maximalIdeal B)
    (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
  have : IsLocalRing (B ⧸ p) := IsLocalRing.of_surjective' (Ideal.Quotient.mk p)
    Ideal.Quotient.mk_surjective
  have hm : Ideal.map (Ideal.Quotient.mk p) (maximalIdeal B) = maximalIdeal (B ⧸ p) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    ← maximalIdeal_height_eq_ringKrullDim,
    ← maximalIdeal_height_eq_ringKrullDim, h, hm]
  push_cast
  rfl

/-- In a Noetherian local ring, the saturated-chain form of catenarity implies `Ring.IsCatenary`:
chains of primes are bounded by the (finite) Krull dimension. -/
theorem isCatenary_of_isCatenaryRingSaturated {T : Type u} [CommRing T] [IsNoetherianRing T]
    [IsLocalRing T] (h : IsCatenaryRingSaturated T) : Ring.IsCatenary T := by
  intro p q hpq
  obtain ⟨⟨N, hN⟩, heq⟩ := h p q hpq
  refine ⟨⟨N, fun s hs ht => hN s hs ht⟩, ?_⟩
  by_cases hex : ∃ s : LTSeries (PrimeSpectrum T), s.head = p ∧ s.last = q ∧
      ∀ i : Fin s.length, s i.castSucc ⋖ s i.succ
  · obtain ⟨t, htp, htq, htsat⟩ := hex
    refine ⟨t.length, fun s hs ht hsat => ?_⟩
    let s' : CovChain T := ⟨s.length, s.toFun, hsat⟩
    let t' : CovChain T := ⟨t.length, t.toFun, htsat⟩
    exact heq s' t' hs ht htp htq
  · exact ⟨0, fun s hs ht hsat => (hex ⟨s, hs, ht, hsat⟩).elim⟩

/-- For a prime `𝔭` of `T`, the Krull dimension of `T ⧸ 𝔭` is the coheight of `𝔭` in
`Spec T`. -/
private theorem ringKrullDim_quotient_eq_coheight {T : Type u} [CommRing T] (p : PrimeSpectrum T) :
    ringKrullDim (T ⧸ p.asIdeal) = Order.coheight p := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  rfl

/-- **The dimension formula forces catenarity.** Let `A` be a ring such that
`dim B = dim B_𝔭 + dim B/𝔭` for every local domain `B` essentially of finite type over `A` and
every prime `𝔭` of `B`. Then every Noetherian local ring `T` essentially of finite type over `A`
is catenary. -/
theorem isCatenary_of_forall_ringKrullDim_eq {A T : Type u} [CommRing A] [CommRing T]
    [IsNoetherianRing T] [IsLocalRing T] [Algebra A T] [Algebra.EssFiniteType A T]
    (H : ∀ (B : Type u) [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B]
      [Algebra.EssFiniteType A B] (p : Ideal B) [p.IsPrime],
      ringKrullDim B = ringKrullDim (Localization.AtPrime p) + ringKrullDim (B ⧸ p)) :
    Ring.IsCatenary T := by
  refine isCatenary_of_isCatenaryRingSaturated (catenary_of_coheight_covby fun x y hxy => ?_)
  have hxy' : x.asIdeal ≤ y.asIdeal := hxy.le
  have : x.asIdeal.IsPrime := x.isPrime
  have : IsLocalRing (T ⧸ x.asIdeal) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective
  have : Algebra.EssFiniteType T (T ⧸ x.asIdeal) :=
    Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ T x.asIdeal)
      (Ideal.Quotient.mkₐ_surjective T x.asIdeal)
  have : Algebra.EssFiniteType A (T ⧸ x.asIdeal) := Algebra.EssFiniteType.comp A T _
  set P : Ideal (T ⧸ x.asIdeal) := Ideal.map (Ideal.Quotient.mk x.asIdeal) y.asIdeal with hP
  have : P.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hxy'
  have hH := H (T ⧸ x.asIdeal) P
  -- the three dimensions in the formula
  rw [ringKrullDim_quotient_eq_coheight x,
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hxy'),
    ringKrullDim_quotient_eq_coheight y,
    IsLocalization.AtPrime.ringKrullDim_eq_height P] at hH
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus x.asIdeal
  let P' : PrimeSpectrum (T ⧸ x.asIdeal) := ⟨P, inferInstance⟩
  have heP : (e P').1 = y := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk x.asIdeal) P = y.asIdeal
    exact Ideal.comap_map_mk hxy'
  have hheight : Order.height P' = 1 := by
    apply le_antisymm
    · refine not_lt.mp fun hlt => ?_
      obtain ⟨a, b, hba, hab⟩ := Order.one_lt_height_iff.mp hlt
      have h1 : x ≤ (e b).1 := (e b).2
      have h2 : (e b).1 < (e a).1 := e.strictMono hba
      have h3 : (e a).1 < (e P').1 := e.strictMono hab
      rw [heP] at h3
      exact hxy.2 (lt_of_le_of_lt h1 h2) h3
    · let b : PrimeSpectrum (T ⧸ x.asIdeal) := e.symm ⟨x, show x.asIdeal ≤ x.asIdeal from le_rfl⟩
      have hb : b < P' := by
        rw [← e.lt_iff_lt, OrderIso.apply_symm_apply, ← Subtype.coe_lt_coe]
        change x < (e P').1
        rw [heP]
        exact hxy.lt
      have := Order.height_add_one_le hb
      exact le_trans le_add_self this
  rw [PrimeSpectrum.height_eq_orderHeight P', hheight] at hH
  have hH' : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) =
      ((Order.coheight y + 1 : ℕ∞) : WithBot ℕ∞) := by
    rw [hH, add_comm]
    push_cast
    rfl
  exact WithBot.coe_injective hH'

/-- **Universally catenary rings via the dimension formula.** A Noetherian ring `A` is
universally catenary if and only if `dim B = dim B_𝔭 + dim B/𝔭` for every local domain `B`
essentially of finite type over `A` and every prime `𝔭` of `B`. -/
@[weil "def_fk101_universally_catenary_fk"]
theorem isUniversallyCatenary_iff_forall_ringKrullDim_eq (A : Type u) [CommRing A]
    [IsNoetherianRing A] :
    Ring.IsUniversallyCatenary A ↔
      ∀ (B : Type u) [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B]
        [Algebra.EssFiniteType A B] (p : Ideal B) [p.IsPrime],
        ringKrullDim B = ringKrullDim (Localization.AtPrime p) + ringKrullDim (B ⧸ p) := by
  refine ⟨fun hA B _ _ _ _ _ p _ =>
    hA.ringKrullDim_eq_ringKrullDim_localization_add_ringKrullDim_quotient p, fun H => ?_⟩
  intro C _ _ _
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  apply AlgebraicGeometry.ringIsCatenary_of_forall_primeLocalization
  intro p _ T _ _ _
  let : Algebra A T := ((algebraMap C T).comp (algebraMap A C)).toAlgebra
  have : IsScalarTower A C T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.EssFiniteType C T := Algebra.EssFiniteType.of_isLocalization T p.primeCompl
  have : Algebra.EssFiniteType A T := Algebra.EssFiniteType.comp A C T
  have : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T p
  have : IsNoetherianRing T := IsLocalization.isNoetherianRing p.primeCompl T inferInstance
  exact isCatenary_of_forall_ringKrullDim_eq H

/-- **The dimension formula along a finitely generated local homomorphism** (Freitag–Kiehl's
form of the condition): if `A` is Noetherian and universally catenary and `A → B` is a finitely
generated local homomorphism to a domain, then `dim B = dim B_𝔭 + dim B/𝔭` for every prime `𝔭`
of `B`. -/
theorem IsUniversallyCatenary.ringKrullDim_eq_of_isFinitelyGeneratedLocal
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B]
    [IsNoetherianRing A] (hA : Ring.IsUniversallyCatenary A)
    (hAB : Algebra.IsFinitelyGeneratedLocal A B) (p : Ideal B) [p.IsPrime] :
    ringKrullDim B = ringKrullDim (Localization.AtPrime p) + ringKrullDim (B ⧸ p) :=
  have : Algebra.EssFiniteType A B := hAB.2
  hA.ringKrullDim_eq_ringKrullDim_localization_add_ringKrullDim_quotient p

end Ring
