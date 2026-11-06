module

public import Weil.Attr
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.HenselianPolynomialRing
public import WeilFrontier.RingTheory.Henselian.HenselizationQuotient
public import WeilFrontier.RingTheory.Henselian.QuasiFinite

/-!
# The adic completion of the Henselization of a polynomial ring

Let `A` be a henselian local ring, `T = (T_i)_{i ∈ σ}` a finite family of indeterminates and
`A{T}` the Henselization of `A[T]` at the origin `𝔭₀ = (𝔪(A), T)`. Then the `(T)`-adic completion
of `A{T}` is isomorphic, as an `A[T]`-algebra, to the power series ring `A[[T]]`.

For every `v`, the ring `A[T]/(T)^v` is finite over `A`, and every polynomial outside `𝔭₀` is a
unit modulo `(T)^v` (its constant term is a unit and the rest is nilpotent). Hence
`A[T]/(T)^v = A[T]_{𝔭₀}/(T)^v`, and this local ring is henselian, being a localization of a finite
algebra over the henselian ring `A`. The Henselization modulo an ideal with henselian quotient is
that quotient, so `A{T}/(T)^v A{T} = A[T]/(T)^v`, compatibly in `v`. Passing to the inverse limit,
the completion of `A{T}` is the `(T)`-adic completion of `A[T]`, which is `A[[T]]`.

## Main definitions

* `AdicCompletion.algEquivOfQuotientMapBijective`: an `S`-algebra `T` such that
  `S ⧸ I ^ n → T ⧸ I ^ n T` is bijective for every `n` has the same `I`-adic completion as `S`.
* `MvPolynomial.IsHenselianPolynomialRing.adicCompletionAlgEquiv`: the `(T)`-adic completion of
  `A{T}` is `A[[T]]`, as an `A[T]`-algebra.
* `MvPolynomial.IsHenselianPolynomialRing.adicCompletionSpanXAlgEquiv`: the case of one
  indeterminate: the `t`-adic completion of `A{t}` is `A[[t]]`, as an `A[t]`-algebra.

## Main results

* `MvPolynomial.quotientMap_localizationAtOrigin_bijective`: `A[T]/(T)^v → A[T]_{𝔭₀}/(T)^v` is
  bijective.
* `MvPolynomial.henselianLocalRing_quotient_localizationAtOrigin`: `A[T]_{𝔭₀}/(T)^v` is a
  henselian local ring for `v ≥ 1`.
* `MvPolynomial.IsHenselianPolynomialRing.quotientMap_bijective`: `A[T]/(T)^v → A{T}/(T)^v A{T}`
  is bijective.
* `MvPolynomial.map_idealOfVars_fin_one`: in one indeterminate, `(T) A{t} = (t)`.

## Implementation notes

The source states the result for one indeterminate `t` over a henselian noetherian local ring
`A'`. The proof needs neither the noetherian hypothesis nor a single indeterminate: it is given
for any henselian local ring and any finite family of indeterminates, the source's case being
`σ = Fin 1`, where `(T) = (t)`
(`MvPolynomial.IsHenselianPolynomialRing.adicCompletionSpanXAlgEquiv`).
The passage from compatible isomorphisms on the quotients to the completions is
`adicCompletionAlgEquivOfQuotientEquiv`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], proof of I.7.7
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace AdicCompletion

variable {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] (I : Ideal S)

/-- The isomorphisms `S ⧸ I ^ n ≃ T ⧸ (I T) ^ n` induced by an `S`-algebra `T` for which every
`S ⧸ I ^ n → T ⧸ I ^ n T` is bijective. -/
noncomputable def quotientPowAlgEquivOfBijective
    (h : ∀ n, Function.Bijective (Ideal.quotientMap ((I ^ n).map (algebraMap S T))
      (algebraMap S T) Ideal.le_comap_map)) (n : ℕ) :
    (S ⧸ I ^ n) ≃ₐ[S] T ⧸ I.map (algebraMap S T) ^ n :=
  (AlgEquiv.ofBijective (Ideal.quotientMapₐ ((I ^ n).map (algebraMap S T)) (Algebra.ofId S T)
    Ideal.le_comap_map) (h n)).trans (Ideal.quotientEquivAlgOfEq S (Ideal.map_pow _ _ _))

theorem quotientPowAlgEquivOfBijective_mk
    (h : ∀ n, Function.Bijective (Ideal.quotientMap ((I ^ n).map (algebraMap S T))
      (algebraMap S T) Ideal.le_comap_map)) (n : ℕ) (x : S) :
    quotientPowAlgEquivOfBijective I h n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap S T x) :=
  rfl

/-- **Invariance of the adic completion.** If `T` is an `S`-algebra such that
`S ⧸ I ^ n → T ⧸ I ^ n T` is bijective for every `n`, then the `I`-adic completion of `S` and the
`I T`-adic completion of `T` are isomorphic as `S`-algebras. -/
noncomputable def algEquivOfQuotientMapBijective
    (h : ∀ n, Function.Bijective (Ideal.quotientMap ((I ^ n).map (algebraMap S T))
      (algebraMap S T) Ideal.le_comap_map)) :
    AdicCompletion I S ≃ₐ[S] AdicCompletion (I.map (algebraMap S T)) T :=
  adicCompletionAlgEquivOfQuotientEquiv I (I.map (algebraMap S T))
    (quotientPowAlgEquivOfBijective I h) fun {m n} hmn x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl

end AdicCompletion

namespace MvPolynomial

section LocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {σ : Type v}

omit [IsLocalRing A] in
theorem sub_C_constantCoeff_mem_idealOfVars (p : MvPolynomial σ A) :
    p - C (constantCoeff p) ∈ idealOfVars σ A := by
  rw [← pow_one (idealOfVars σ A), mem_pow_idealOfVars_iff']
  intro x hx
  have hx0 : x = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  subst hx0
  simp [← constantCoeff_eq]

/-- A polynomial outside `𝔭₀ = (𝔪, T)` is a unit modulo `(T) ^ n`. -/
theorem isUnit_mk_pow_idealOfVars_of_notMem_originIdeal (n : ℕ) {p : MvPolynomial σ A}
    (hp : p ∉ originIdeal A σ) : IsUnit (Ideal.Quotient.mk (idealOfVars σ A ^ n) p) := by
  have hu : IsUnit (Ideal.Quotient.mk (idealOfVars σ A ^ n) (C (constantCoeff p))) :=
    ((IsLocalRing.notMem_maximalIdeal.mp hp).map C).map _
  have hnil : IsNilpotent (Ideal.Quotient.mk (idealOfVars σ A ^ n) (p - C (constantCoeff p))) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
           exact Ideal.pow_mem_pow (sub_C_constantCoeff_mem_idealOfVars p) n⟩
  have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
  rwa [← map_add, add_sub_cancel] at this

/-- `A[T] / (T) ^ n → A[T]_{𝔭₀} / (T) ^ n` is bijective: elements outside `𝔭₀` are already units
modulo `(T) ^ n`. -/
theorem quotientMap_localizationAtOrigin_bijective (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((idealOfVars σ A ^ n).map
      (algebraMap (MvPolynomial σ A) (LocalizationAtOrigin A σ)))
      (algebraMap (MvPolynomial σ A) (LocalizationAtOrigin A σ)) Ideal.le_comap_map) := by
  set K := idealOfVars σ A ^ n
  have hle : Algebra.algebraMapSubmonoid (MvPolynomial σ A ⧸ K) (originIdeal A σ).primeCompl ≤
      IsUnit.submonoid _ := by
    rintro _ ⟨p, hp, rfl⟩
    exact isUnit_mk_pow_idealOfVars_of_notMem_originIdeal n hp
  exact (IsLocalization.atUnits (MvPolynomial σ A ⧸ K) _
    (S := LocalizationAtOrigin A σ ⧸
      K.map (algebraMap (MvPolynomial σ A) (LocalizationAtOrigin A σ))) hle).bijective

end LocalRing

section Henselian

variable {A : Type u} [CommRing A] {σ : Type v}

theorem isIntegral_mk_pow_idealOfVars (n : ℕ) (p : MvPolynomial σ A) :
    IsIntegral A (Ideal.Quotient.mk (idealOfVars σ A ^ n) p) := by
  have hX (i : σ) : IsIntegral A (Ideal.Quotient.mk (idealOfVars σ A ^ n) (X i)) := by
    refine IsIntegral.of_pow (Nat.succ_pos n) ?_
    have hmem : (X i : MvPolynomial σ A) ^ (n + 1) ∈ idealOfVars σ A ^ n := by
      rw [pow_succ]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) n)
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
    exact isIntegral_zero
  induction p using MvPolynomial.induction_on with
  | C a => exact isIntegral_algebraMap (x := a)
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp => rw [map_mul]; exact hp.mul (hX i)

/-- For finitely many indeterminates, `A[T] / (T) ^ n` is a finite `A`-module. -/
instance moduleFinite_quotient_pow_idealOfVars [Finite σ] (n : ℕ) :
    Module.Finite A (MvPolynomial σ A ⧸ idealOfVars σ A ^ n) := by
  have : Algebra.IsIntegral A (MvPolynomial σ A ⧸ idealOfVars σ A ^ n) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact isIntegral_mk_pow_idealOfVars n p
  exact Algebra.IsIntegral.finite

variable [HenselianLocalRing A]

theorem pow_idealOfVars_le_originIdeal {n : ℕ} (hn : n ≠ 0) :
    idealOfVars σ A ^ n ≤ originIdeal A σ :=
  (Ideal.pow_le_self hn).trans (by rw [originIdeal_eq]; exact le_sup_right)

/-- For a henselian local ring `A`, finitely many indeterminates and `n ≠ 0`, the local ring
`A[T]_{𝔭₀} / (T) ^ n` is henselian. -/
theorem henselianLocalRing_quotient_localizationAtOrigin [Finite σ] {n : ℕ} (hn : n ≠ 0) :
    HenselianLocalRing (LocalizationAtOrigin A σ ⧸ (idealOfVars σ A ^ n).map
      (algebraMap (MvPolynomial σ A) (LocalizationAtOrigin A σ))) := by
  set K := idealOfVars σ A ^ n with hKdef
  have hK : K ≤ originIdeal A σ := pow_idealOfVars_le_originIdeal hn
  let 𝔫 : Ideal (MvPolynomial σ A ⧸ K) := (originIdeal A σ).map (Ideal.Quotient.mk K)
  have hunit : ∀ x : MvPolynomial σ A ⧸ K, x ∉ 𝔫 → IsUnit x := by
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact isUnit_mk_pow_idealOfVars_of_notMem_originIdeal n fun hp =>
      hx (Ideal.mem_map_of_mem _ hp)
  have hmax : 𝔫.IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      (originIdeal_isMaximal A σ)).resolve_left fun htop => ?_
    have h1 : (1 : MvPolynomial σ A ⧸ K) ∈ 𝔫 := by
      change (1 : MvPolynomial σ A ⧸ K) ∈ (originIdeal A σ).map (Ideal.Quotient.mk K)
      rw [htop]
      exact Submodule.mem_top
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    obtain ⟨p, hp, hp1⟩ := h1
    rw [← map_one (Ideal.Quotient.mk K), Ideal.Quotient.eq] at hp1
    exact (originIdeal_isMaximal A σ).ne_top ((Ideal.eq_top_iff_one _).2
      (by simpa using sub_mem hp (hK hp1)))
  have hle : Algebra.algebraMapSubmonoid (MvPolynomial σ A ⧸ K) (originIdeal A σ).primeCompl ≤
      IsUnit.submonoid _ := by
    rintro _ ⟨p, hp, rfl⟩
    exact isUnit_mk_pow_idealOfVars_of_notMem_originIdeal n hp
  have h1 : IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial σ A ⧸ K)
      (originIdeal A σ).primeCompl) (MvPolynomial σ A ⧸ K) := IsLocalization.self hle
  have h2 : IsLocalization 𝔫.primeCompl (MvPolynomial σ A ⧸ K) :=
    IsLocalization.self fun x hx => hunit x hx
  have : IsLocalization.AtPrime (LocalizationAtOrigin A σ ⧸
      K.map (algebraMap (MvPolynomial σ A) (LocalizationAtOrigin A σ))) 𝔫 :=
    (IsLocalization.isLocalization_iff_of_isLocalization
      (Algebra.algebraMapSubmonoid _ (originIdeal A σ).primeCompl) 𝔫.primeCompl
      (MvPolynomial σ A ⧸ K)).1 inferInstance
  exact @HenselianLocalRing.of_isLocalization_atPrime_of_finite A _ _ (MvPolynomial σ A ⧸ K) _ _ _
    𝔫 _ _ _ _ _ (IsScalarTower.of_algebraMap_eq fun _ => rfl) _

variable {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A σ) B]
  [Algebra (MvPolynomial σ A) B] [IsScalarTower (MvPolynomial σ A) (LocalizationAtOrigin A σ) B]

/-- For a henselian local ring `A` and finitely many indeterminates, the canonical map
`A[T] / (T) ^ n → A{T} / (T) ^ n A{T}` is bijective for every `n`. -/
theorem IsHenselianPolynomialRing.quotientMap_bijective [Finite σ]
    (h : IsHenselianPolynomialRing A σ B) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((idealOfVars σ A ^ n).map
      (algebraMap (MvPolynomial σ A) B)) (algebraMap (MvPolynomial σ A) B) Ideal.le_comap_map) := by
  set K := idealOfVars σ A ^ n with hKdef
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hK : K = ⊤ := by simp [hKdef]
    have : Subsingleton (MvPolynomial σ A ⧸ K) := Ideal.Quotient.subsingleton_iff.2 hK
    have : Subsingleton (B ⧸ K.map (algebraMap (MvPolynomial σ A) B)) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [hK, Ideal.map_top])
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  have := h
  let R := LocalizationAtOrigin A σ
  let KR := K.map (algebraMap (MvPolynomial σ A) R)
  have := henselianLocalRing_quotient_localizationAtOrigin (A := A) (σ := σ) hn.ne'
  have hI : KR ≤ maximalIdeal R := by
    refine Ideal.map_le_iff_le_comap.2 ((pow_idealOfVars_le_originIdeal hn.ne').trans ?_)
    rw [← Ideal.under_def, Localization.AtPrime.under_maximalIdeal]
  have h2 := IsHenselization.quotientMap_bijective_of_henselianLocalRing (R := R) (Rh := B) KR hI
  have h1 := quotientMap_localizationAtOrigin_bijective (A := A) (σ := σ) n
  have hEq : KR.map (algebraMap R B) = K.map (algebraMap (MvPolynomial σ A) B) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hcomp : Ideal.quotientMap (K.map (algebraMap (MvPolynomial σ A) B))
      (algebraMap (MvPolynomial σ A) B) Ideal.le_comap_map =
      (Ideal.quotEquivOfEq hEq) ∘
        (Ideal.quotientMap (KR.map (algebraMap R B)) (algebraMap R B) Ideal.le_comap_map) ∘
        (Ideal.quotientMap KR (algebraMap (MvPolynomial σ A) R) Ideal.le_comap_map) := by
    funext x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (algebraMap _ B p) =
      Ideal.Quotient.mk _ (algebraMap R B (algebraMap (MvPolynomial σ A) R p))
    rw [← IsScalarTower.algebraMap_apply]
  rw [hcomp]
  exact (Ideal.quotEquivOfEq hEq).bijective.comp (h2.comp h1)

/-- **The `(T)`-adic completion of `A{T}` is `A[[T]]`.** Let `A` be a henselian local ring and
`A{T}` the Henselization of the polynomial ring `A[T]` in finitely many indeterminates at the
origin. Then the `(T)`-adic completion of `A{T}` is isomorphic, as an `A[T]`-algebra, to the
power series ring `A[[T]]`. -/
@[weil "lem_fk107_henselian_line_completion"]
noncomputable def IsHenselianPolynomialRing.adicCompletionAlgEquiv [Finite σ]
    (h : IsHenselianPolynomialRing A σ B) :
    AdicCompletion ((idealOfVars σ A).map (algebraMap (MvPolynomial σ A) B)) B ≃ₐ[MvPolynomial σ A]
      MvPowerSeries σ A :=
  (AdicCompletion.algEquivOfQuotientMapBijective _ h.quotientMap_bijective).symm.trans
    (MvPowerSeries.toAdicCompletionAlgEquiv σ A).symm

end Henselian

section OneVariable

/-- In one indeterminate, `(T) A{t}` is the principal ideal `(t)`. -/
theorem map_idealOfVars_fin_one {A : Type u} [CommRing A] {B : Type w} [CommRing B]
    [Algebra (MvPolynomial (Fin 1) A) B] :
    (idealOfVars (Fin 1) A).map (algebraMap (MvPolynomial (Fin 1) A) B) =
      Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0)} := by
  rw [Ideal.map_span, ← Set.range_comp, Set.range_unique]
  rfl

/-- **The `t`-adic completion of `A{t}` is `A[[t]]`.** For a henselian local ring `A` and the
Henselization `A{t}` of `A[t]` at `(𝔪(A), t)`, the `t`-adic completion of `A{t}` is isomorphic,
as an `A[t]`-algebra, to the power series ring `A[[t]]`. -/
@[weil "lem_fk107_henselian_line_completion"]
noncomputable def IsHenselianPolynomialRing.adicCompletionSpanXAlgEquiv
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {B : Type w} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A (Fin 1)) B]
    [Algebra (MvPolynomial (Fin 1) A) B]
    [IsScalarTower (MvPolynomial (Fin 1) A) (LocalizationAtOrigin A (Fin 1)) B]
    (h : IsHenselianPolynomialRing A (Fin 1) B) :
    AdicCompletion (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0)}) B
      ≃ₐ[MvPolynomial (Fin 1) A] MvPowerSeries (Fin 1) A :=
  map_idealOfVars_fin_one (A := A) (B := B) ▸ h.adicCompletionAlgEquiv

end OneVariable

end MvPolynomial
