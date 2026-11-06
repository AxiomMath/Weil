module

public import Weil.Attr
public import WeilFrontier.Defs.RingTheory.Ideal.AssociatedPrime.Basic
public import WeilFrontier.RingTheory.Henselian.Henselization.HenselianLineNormal
public import WeilFrontier.RingTheory.Henselian.Henselization.HenselianLinePrimaryExtension
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import Mathlib.RingTheory.Lasker
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Divisorial ideals of `A{T}` containing an extended divisorial ideal descend to `A`

Let `A` be a normal henselian noetherian local domain and `B = A{T}` the Henselization of the
polynomial ring `A[T]` at the origin, `T` a finite family of indeterminates. If `𝔞 ⊆ A` is a
divisorial ideal and `𝔟 ⊆ B` a divisorial ideal containing `𝔞 B`, then `𝔟 = 𝔟₀ B` for a
divisorial ideal `𝔟₀ ⊇ 𝔞` of `A`; one can take `𝔟₀ = 𝔟 ∩ A`.

The proof takes a minimal primary decomposition `𝔟 = ⋂ J` of `𝔟`. The radical `P` of each
component `J` is an associated prime of `B ⧸ 𝔟`, hence of height one, and contains `𝔞 B`. Put
`𝔭 = P ∩ A`: it contains `𝔞 ≠ 0`, so `𝔭 B` is a nonzero prime (`A → B` is faithfully flat and
`𝔭 B` is prime) contained in `P`, and `P = 𝔭 B` because `P` has height one. The same argument
shows that `𝔭` is minimal over `𝔞`, so `𝔭` is an associated prime of `A ⧸ 𝔞` and has height one.
Since `B` is a normal noetherian domain, `B_P` is a discrete valuation ring with maximal ideal
`𝔭 B_P`, so `J B_P = 𝔭ⁿ B_P` for some `n`; as `J` and `(J ∩ A) B` are `P`-primary, both are
saturated with respect to `B → B_P`, which gives `J = (J ∩ A) B`. Finally flat extension commutes
with finite intersections, so `𝔟 = (𝔟 ∩ A) B`, and `𝔟 ∩ A = ⋂ (J ∩ A)` is an intersection of
primary ideals whose radicals have height one, hence divisorial.

## Main results

* `MvPolynomial.IsHenselianPolynomialRing.exists_isDivisorial_map_eq`: a divisorial ideal of
  `A{T}` containing `𝔞 A{T}`, for `𝔞` divisorial, is `𝔟₀ A{T}` for a divisorial `𝔟₀ ⊇ 𝔞`.

## Implementation notes

The source treats one indeterminate `t` (the case `σ = Fin 1`); any finite family is allowed
here. The source proves that each `P`-primary component descends by computing in `B_P` with a
uniformizer of `A_𝔭`; here `B_P` is shown to be a discrete valuation ring directly, `B` being a
normal noetherian domain and `P` of height one.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

public section

open IsLocalRing

universe u v w

namespace Ideal

variable {R : Type*} [CommRing R]

/-- In a domain, a nonzero prime contained in a prime of height one is equal to it. -/
private theorem eq_of_le_of_height_eq_one' [IsDomain R] {Q P : Ideal R} [Q.IsPrime] [P.IsPrime]
    (hQ : Q ≠ ⊥) (hP : P.height = 1) (h : Q ≤ P) : Q = P := by
  by_contra hne
  have hlt := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne h hne)
  rw [hP] at hlt
  have h0 : Q.height ≠ 0 := by rwa [Ne, Ideal.height_eq_zero_iff_eq_bot]
  have : Q.height ≤ 0 := by
    have h1 : Q.height + 1 ≤ 0 + 1 := by simpa using hlt
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h1
  exact h0 (nonpos_iff_eq_zero.1 this)

/-- The associated primes of the submodule `I` of `R` are those of the module `R ⧸ I`. -/
private theorem mem_associatedPrimes_quotient' [IsNoetherianRing R] {I P : Ideal R}
    (h : P ∈ (I : Submodule R R).associatedPrimes) : P ∈ associatedPrimes R (R ⧸ I) := by
  obtain ⟨hP, x, rfl⟩ := (Submodule.isAssociatedPrime_iff).1 h
  refine (isAssociatedPrime_iff).2 ⟨hP, Submodule.Quotient.mk x, ?_⟩
  ext y
  rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, Submodule.mem_bot,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]

/-- The intersection of two divisorial ideals is divisorial. -/
private theorem IsDivisorial.inf' {I J : Ideal R} (hI : I.IsDivisorial) (hJ : J.IsDivisorial) :
    (I ⊓ J).IsDivisorial := by
  intro P hP
  let φ : (R ⧸ (I ⊓ J)) →ₗ[R] (R ⧸ I) × (R ⧸ J) :=
    (Submodule.factor inf_le_left).prod (Submodule.factor inf_le_right)
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [LinearMap.mem_ker] at hz
    have h1 := congrArg Prod.fst hz
    have h2 := congrArg Prod.snd hz
    simp only [φ, LinearMap.prod_apply, Prod.fst_zero, Prod.snd_zero] at h1 h2
    change Submodule.Quotient.mk (p := I) x = 0 at h1
    change Submodule.Quotient.mk (p := J) x = 0 at h2
    rw [Submodule.Quotient.mk_eq_zero] at h1 h2
    rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨h1, h2⟩
  have hP' := associatedPrimes.subset_of_injective hφ hP
  rw [associatedPrimes.prod] at hP'
  rcases hP' with h | h
  · exact hI P h
  · exact hJ P h

/-- A finite intersection of divisorial ideals is divisorial. -/
private theorem isDivisorial_finsetInf' {ι : Type*} (s : Finset ι) (I : ι → Ideal R)
    (h : ∀ i ∈ s, (I i).IsDivisorial) : (s.inf I).IsDivisorial := by
  classical
  induction s using Finset.induction_on with
  | empty => exact isDivisorial_top
  | insert i s _ ih =>
    rw [Finset.inf_insert]
    exact (h i (Finset.mem_insert_self i s)).inf' (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Over a noetherian ring, a primary ideal whose radical has height one is divisorial. -/
private theorem IsPrimary.isDivisorial' [IsNoetherianRing R] {q : Ideal R} (hq : q.IsPrimary)
    (h : q.radical.height = 1) : q.IsDivisorial := by
  intro P hP
  rw [associatedPrimes.eq_singleton_of_isPrimary hq, Set.mem_singleton_iff] at hP
  rw [hP, h]

/-- In a domain, the zero ideal is not divisorial: `0` is an associated prime of `R ⧸ 0`. -/
private theorem not_isDivisorial_bot' [IsNoetherianRing R] [IsDomain R] :
    ¬ (⊥ : Ideal R).IsDivisorial := by
  intro h
  have hmem : (⊥ : Ideal R) ∈ associatedPrimes R (R ⧸ (⊥ : Ideal R)) := by
    refine (isAssociatedPrime_iff).2 ⟨Ideal.isPrime_bot, Submodule.Quotient.mk 1, ?_⟩
    ext y
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Submodule.mem_bot,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one,
      Submodule.mem_bot]
  have := h _ hmem
  rw [Ideal.height_bot] at this
  exact zero_ne_one this

/-- Extension of ideals along a flat ring map commutes with finite intersections. -/
private theorem map_finsetInf_of_flat' {S : Type*} [CommRing S] [Algebra R S] [Module.Flat R S]
    {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    (s.inf I).map (algebraMap R S) = s.inf fun i => (I i).map (algebraMap R S) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Ideal.map_top _
  | insert i s _ ih => rw [Finset.inf_insert, Finset.inf_insert, map_inf_of_flat, ih]

end Ideal

namespace MvPolynomial.IsHenselianPolynomialRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A] [IsDomain A]
  [IsIntegrallyClosed A] {σ : Type v} [Finite σ] {B : Type w} [CommRing B] [IsLocalRing B]
  [Algebra (LocalizationAtOrigin A σ) B] [Algebra A B]
  [IsScalarTower A (LocalizationAtOrigin A σ) B]

/-- Let `𝔭 ⊂ A` be a prime with `P = 𝔭 B` of height one. A `P`-primary ideal `J` of `B = A{T}`
is extended from `A`: `J = (J ∩ A) B`. -/
private theorem eq_map_comap_of_isPrimary (hB : IsHenselianPolynomialRing A σ B) (p : Ideal A)
    [p.IsPrime] (hP1 : (p.map (algebraMap A B)).height = 1) {J : Ideal B} (hJ : J.IsPrimary)
    (hrad : J.radical = p.map (algebraMap A B)) :
    J = (J.comap (algebraMap A B)).map (algebraMap A B) := by
  set f := algebraMap A B
  set P := p.map f with hPdef
  have hPp : P.IsPrime := isPrime_map p hB
  have : IsHenselization (LocalizationAtOrigin A σ)
      (ResidueField (LocalizationAtOrigin A σ)) B := hB
  have : IsNoetherianRing B :=
    isNoetherianRing_of_isHenselization (A := LocalizationAtOrigin A σ)
      (ResidueField (LocalizationAtOrigin A σ))
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed hB
  have : Module.FaithfullyFlat A B := hB.faithfullyFlat
  let BP := Localization.AtPrime P
  have : IsDomain BP := inferInstance
  have : IsNoetherianRing BP := inferInstance
  have : IsIntegrallyClosed BP :=
    isIntegrallyClosed_of_isLocalization BP P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hginj : Function.Injective (algebraMap B BP) :=
    IsLocalization.injective BP P.primeCompl_le_nonZeroDivisors
  -- saturation of `P`-primary ideals
  have hsat : ∀ K : Ideal B, K.IsPrimary → K ≤ P →
      (K.map (algebraMap B BP)).comap (algebraMap B BP) = K := fun K hK hKP =>
    IsLocalization.under_map_of_isPrimary_disjoint P.primeCompl BP hK
      (Set.disjoint_left.2 fun x hx hxK => hx (hKP hxK))
  have hJP : J ≤ P := hrad ▸ Ideal.le_radical
  -- `B_P` is a discrete valuation ring: its nonzero primes are maximal
  have hprimes : ∀ Q : Ideal BP, Q ≠ ⊥ → Q.IsPrime → Q = maximalIdeal BP := by
    intro Q hQ hQp
    have hle : Q.comap (algebraMap B BP) ≤ P :=
      (Ideal.comap_mono (le_maximalIdeal hQp.ne_top)).trans_eq
        (IsLocalization.AtPrime.under_maximalIdeal (S := BP) (I := P))
    have hne : Q.comap (algebraMap B BP) ≠ ⊥ := by
      intro h0
      apply hQ
      rw [← IsLocalization.map_under P.primeCompl BP Q, Ideal.under_def, h0, Ideal.map_bot]
    have heq := Ideal.eq_of_le_of_height_eq_one' hne hP1 hle
    rw [← IsLocalization.map_under P.primeCompl BP Q, Ideal.under_def, heq,
      Localization.AtPrime.map_eq_maximalIdeal]
  have hdvr := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain BP).out 4 7
  obtain ⟨n, hn⟩ := hdvr.1 ⟨inferInstance, hprimes⟩ (J.map (algebraMap B BP)) (by
    intro h0
    have : J ≤ ⊥ := by
      rw [← hsat J hJ hJP, h0, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot (algebraMap B BP)).1
        hginj]
    exact Ideal.ne_bot_of_height_eq_one hP1
      (by rw [← hrad, le_bot_iff.1 this, Ideal.isPrime_bot.radical]))
  have hPn : P ^ n = (p ^ n).map f := (Ideal.map_pow f p n).symm
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, hPn] at hn
  -- `q = J ∩ A` is `𝔭`-primary
  set q := J.comap f
  have hq : q.IsPrimary := hJ.comap f
  have hqrad : q.radical = p := by
    rw [← Ideal.comap_radical, hrad, Ideal.comap_map_eq_self_of_faithfullyFlat]
  have hqB : (q.map f).IsPrimary := isPrimary_map hq hB
  have hqBP : q.map f ≤ P := by
    calc q.map f ≤ (q.map f).radical := Ideal.le_radical
      _ = P := by rw [radical_map_eq_of_isPrimary hq hB, hqrad]
  -- `𝔭ⁿ ⊆ q`
  have hpn : p ^ n ≤ q := by
    rw [← Ideal.map_le_iff_le_comap]
    calc (p ^ n).map f ≤ (((p ^ n).map f).map (algebraMap B BP)).comap (algebraMap B BP) :=
          Ideal.le_comap_map
      _ = J := by rw [← hn, hsat J hJ hJP]
  refine le_antisymm ?_ Ideal.map_comap_le
  calc J ≤ (J.map (algebraMap B BP)).comap (algebraMap B BP) := Ideal.le_comap_map
    _ = (((p ^ n).map f).map (algebraMap B BP)).comap (algebraMap B BP) := by rw [hn]
    _ ≤ ((q.map f).map (algebraMap B BP)).comap (algebraMap B BP) :=
        Ideal.comap_mono (Ideal.map_mono (Ideal.map_mono hpn))
    _ = q.map f := hsat _ hqB hqBP

/-- **Divisorial ideals of `A{T}` over an extended divisorial ideal descend.** Let `A` be a normal
henselian noetherian local domain, `B = A{T}` the Henselization of the polynomial ring `A[T]` at
the origin, `T` a finite family of indeterminates, `𝔞 ⊆ A` a divisorial ideal and `𝔟 ⊆ B` a
divisorial ideal with `𝔞 B ⊆ 𝔟`. Then `𝔟 = 𝔟₀ B` for a divisorial ideal `𝔟₀ ⊇ 𝔞` of `A`. -/
@[weil "lem_fk107_henselian_line_divisorial_descends"]
theorem exists_isDivisorial_map_eq (hB : IsHenselianPolynomialRing A σ B) {𝔞 : Ideal A}
    (h𝔞 : 𝔞.IsDivisorial) {𝔟 : Ideal B} (h𝔟 : 𝔟.IsDivisorial)
    (hle : 𝔞.map (algebraMap A B) ≤ 𝔟) :
    ∃ 𝔟₀ : Ideal A, 𝔟₀.IsDivisorial ∧ 𝔞 ≤ 𝔟₀ ∧ 𝔟₀.map (algebraMap A B) = 𝔟 := by
  set f := algebraMap A B
  have : IsHenselization (LocalizationAtOrigin A σ)
      (ResidueField (LocalizationAtOrigin A σ)) B := hB
  have : IsNoetherianRing B :=
    isNoetherianRing_of_isHenselization (A := LocalizationAtOrigin A σ)
      (ResidueField (LocalizationAtOrigin A σ))
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed hB
  have : Module.FaithfullyFlat A B := hB.faithfullyFlat
  have hcm : ∀ I : Ideal A, (I.map f).comap f = I := fun I =>
    Ideal.comap_map_eq_self_of_faithfullyFlat I
  have h𝔞0 : 𝔞 ≠ ⊥ := fun h => Ideal.not_isDivisorial_bot' (h ▸ h𝔞)
  obtain ⟨t, ht⟩ :=
    Submodule.IsLasker.exists_isMinimalPrimaryDecomposition (Submodule.isLasker B B) 𝔟
  have hinf : t.inf id = 𝔟 := ht.inf_eq
  -- every primary component of `𝔟` is extended from a divisorial ideal of `A`
  have key : ∀ J : Ideal B, J ∈ t → (J.comap f).map f = J ∧ (J.comap f).IsDivisorial := by
    intro J hJt
    have hJ : J.IsPrimary := ht.primary hJt
    have h𝔟J : 𝔟 ≤ J := hinf ▸ Finset.inf_le (f := id) hJt
    set P := J.radical with hPdef
    have hPp : P.IsPrime := Ideal.isPrime_radical hJ
    have hPass : P ∈ associatedPrimes B (B ⧸ 𝔟) := by
      have := ht.mem_associatedPrimes hJt
      rw [Submodule.colon_univ] at this
      exact Ideal.mem_associatedPrimes_quotient' this
    have hP1 : P.height = 1 := h𝔟 P hPass
    set p := P.comap f
    have hpp : p.IsPrime := Ideal.comap_isPrime f P
    have h𝔞p : 𝔞 ≤ p := Ideal.map_le_iff_le_comap.1 (hle.trans (h𝔟J.trans Ideal.le_radical))
    -- a nonzero prime `Q ≤ 𝔭` of `A` with `Q B ≤ P` satisfies `Q B = P`
    have hext : ∀ Q : Ideal A, Q.IsPrime → 𝔞 ≤ Q → Q ≤ p → Q.map f = P := by
      intro Q hQ h𝔞Q hQp
      have : (Q.map f).IsPrime := isPrime_map Q hB
      refine Ideal.eq_of_le_of_height_eq_one' ?_ hP1 (Ideal.map_le_iff_le_comap.2 hQp)
      intro h0
      have hbot := hcm ⊥
      rw [Ideal.map_bot] at hbot
      apply h𝔞0
      rw [eq_bot_iff, ← hbot, ← h0, hcm Q]
      exact h𝔞Q
    have hpP : p.map f = P := hext p hpp h𝔞p le_rfl
    -- `𝔭` is minimal over `𝔞`, hence an associated prime of `A ⧸ 𝔞`, of height one
    have hpmin : p ∈ 𝔞.minimalPrimes := by
      refine ⟨⟨hpp, h𝔞p⟩, fun Q ⟨hQ, h𝔞Q⟩ hQp => ?_⟩
      have := hext Q hQ h𝔞Q hQp
      rw [← hcm Q, this]
    have hpass : p ∈ associatedPrimes A (A ⧸ 𝔞) := by
      apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      rwa [Ideal.annihilator_quotient]
    have hp1 : p.height = 1 := h𝔞 p hpass
    have hJeq := eq_map_comap_of_isPrimary hB p (hpP ▸ hP1) hJ hpP.symm
    refine ⟨hJeq.symm, Ideal.IsPrimary.isDivisorial' (hJ.comap f) ?_⟩
    rw [← Ideal.comap_radical, ← hPdef]
    exact hp1
  refine ⟨𝔟.comap f, ?_, Ideal.map_le_iff_le_comap.1 hle, ?_⟩
  · rw [← hinf, Ideal.comap_finsetInf]
    exact Ideal.isDivisorial_finsetInf' t _ fun J hJ => (key J hJ).2
  · calc (𝔟.comap f).map f = (t.inf fun J => Ideal.comap f J).map f := by
          rw [← hinf, Ideal.comap_finsetInf]; rfl
      _ = t.inf fun J => (Ideal.comap f J).map f := Ideal.map_finsetInf_of_flat' t _
      _ = t.inf id := Finset.inf_congr rfl fun J hJ => (key J hJ).1
      _ = 𝔟 := hinf

end MvPolynomial.IsHenselianPolynomialRing

end
