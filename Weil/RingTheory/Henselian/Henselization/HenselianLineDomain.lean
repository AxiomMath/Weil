module

public import Weil.Attr
public import Weil.Defs.RingTheory.Henselian.Henselization.HenselianPolynomialRing
public import Weil.RingTheory.Henselian.HenselizationQuotient
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.Henselian.Quotient
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The Henselization of a polynomial ring over a henselian local domain is a domain

Let `A` be a henselian noetherian local domain and let `T = (T_i)_{i ∈ σ}` be finitely many
indeterminates. Then the Henselization `A{T}` of `A[T]` at the origin `𝔭₀ = (𝔪, T)` is an integral
domain.

The proof embeds `A{T}` into the ring of formal power series `A[[T]]`, which is a domain. Since
`A[[T]]` is complete for the `T`-adic topology and `A[[T]]/(T) = A` is henselian, `A[[T]]` is a
henselian local ring. The inclusion `A[T] → A[[T]]` induces a local homomorphism
`ρ : A[T]_{𝔭₀} → A[[T]]`, which extends, by the universal property of the Henselization, to a local
homomorphism `π : A{T} → A[[T]]`. For every `v`, `A[T]_{𝔭₀}/(T)^v ≅ A[[T]]/(T)^v` is henselian,
so `A[T]_{𝔭₀}/(T)^v → A{T}/(T)^v` is bijective; comparing with `A[[T]]/(T)^v` shows that the
kernel of `π` lies in `(T)^v A{T}`. The ring `A{T}` is noetherian and local, so by Krull's
intersection theorem `⋂_v (T)^v A{T} = 0`, and `π` is injective.

## Main results

* `MvPowerSeries.mem_pow_span_range_X_iff`: for finitely many variables, a power series lies in
  the `v`-th power of the ideal `(T)` iff its coefficients of total degree `< v` vanish.
* `MvPowerSeries.instHenselianLocalRingOfFinite`: `A[[T]]` is henselian for `A` henselian and
  finitely many variables.
* `MvPolynomial.IsHenselianPolynomialRing.injective_algHom_toMvPowerSeries`: every
  `A[T]_{𝔭₀}`-algebra map `A{T} → A[[T]]` is injective.
* `MvPolynomial.IsHenselianPolynomialRing.isDomain`: `A{T}` is an integral domain.

## Implementation notes

The source states the result for one indeterminate `t` and argues through the isomorphism of
the `t`-adic completion of `A{t}` with `A[[t]]`; only the injectivity of `A{t} → A[[t]]` is
used, and it is proved directly here, for any finite family of indeterminates.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace MvPowerSeries

variable {σ : Type*} {R : Type*} [CommRing R]

/-- The coefficients of total degree `< v` of a power series in `(T)^v` vanish. -/
theorem coeff_eq_zero_of_mem_pow_span_range_X {v : ℕ} {g : MvPowerSeries σ R}
    (hg : g ∈ Ideal.span (Set.range X) ^ v) {n : σ →₀ ℕ} (hn : n.degree < v) :
    coeff n g = 0 := by
  classical
  induction v generalizing g n with
  | zero => omega
  | succ v ih =>
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · have hb0 : constantCoeff b = 0 := by
        have : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤
            RingHom.ker (constantCoeff (σ := σ) (R := R)) := by
          rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          simp
        exact this hb
      rw [coeff_mul]
      refine Finset.sum_eq_zero fun pq hpq => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
      by_cases hq : pq.2 = 0
      · rw [hq, coeff_zero_eq_constantCoeff_apply, hb0, mul_zero]
      · have hdeg : pq.1.degree + pq.2.degree = n.degree := by
          rw [← hpq, map_add]
        have hq' : pq.2.degree ≠ 0 := fun h => hq ((Finsupp.degree_eq_zero_iff _).mp h)
        rw [ih ha (by omega), zero_mul]
    · rw [map_add, hx, hy, add_zero]

/-- For finitely many variables, a power series whose coefficients of total degree `< v` vanish
lies in `(T)^v`. -/
theorem mem_pow_span_range_X_of_coeff_eq_zero [Finite σ] {v : ℕ} {g : MvPowerSeries σ R}
    (hg : ∀ n : σ →₀ ℕ, n.degree < v → coeff n g = 0) :
    g ∈ Ideal.span (Set.range X) ^ v := by
  set I := MvPolynomial.idealOfVars σ R
  set e := toAdicCompletionAlgEquiv σ R
  have htrunc : truncTotal v g ∈ I ^ v := by
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    rw [coeff_truncTotal _ hx, hg x hx]
  have hker : e g ∈ I ^ v • (⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion I (MvPolynomial σ R))) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R),
      LinearMap.mem_ker, AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply,
      toAdicCompletion_apply_eq_mk_truncTotal]
    rw [Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul, Ideal.mul_top]
    exact htrunc
  have hmap : ∀ r ∈ I ^ v, algebraMap (MvPolynomial σ R) (MvPowerSeries σ R) r ∈
      Ideal.span (Set.range X) ^ v := by
    intro r hr
    have hle : I.map (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) ≤
        Ideal.span (Set.range X) := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨i, (MvPolynomial.coe_X i).symm⟩
    have := Ideal.mem_map_of_mem (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) hr
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle v this
  rw [← e.symm_apply_apply g]
  refine Submodule.smul_induction_on hker (fun r hr c _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (hmap r hr)
  · rw [map_add]
    exact add_mem hx hy

/-- For finitely many variables, a power series lies in `(T)^v` iff its coefficients of total
degree `< v` vanish. -/
theorem mem_pow_span_range_X_iff [Finite σ] {v : ℕ} {g : MvPowerSeries σ R} :
    g ∈ Ideal.span (Set.range X) ^ v ↔ ∀ n : σ →₀ ℕ, n.degree < v → coeff n g = 0 :=
  ⟨fun hg _ hn => coeff_eq_zero_of_mem_pow_span_range_X hg hn,
    mem_pow_span_range_X_of_coeff_eq_zero⟩

theorem mem_span_range_X_iff [Finite σ] {g : MvPowerSeries σ R} :
    g ∈ Ideal.span (Set.range X) ↔ constantCoeff g = 0 := by
  rw [← pow_one (Ideal.span _), mem_pow_span_range_X_iff]
  refine ⟨fun h => ?_, fun h n hn => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    exact h 0 (by simp)
  · have : n = 0 := (Finsupp.degree_eq_zero_iff _).mp (by omega)
    rw [this, coeff_zero_eq_constantCoeff_apply, h]

/-- **Formal power series over a henselian local ring are henselian.** For `R` henselian local
and finitely many variables, `R[[T]]` is a henselian local ring: a simple root modulo the maximal
ideal is first lifted modulo `(T)`, using that `R` is henselian, and then `T`-adically, using
that `R[[T]]` is `(T)`-adically complete. -/
instance instHenselianLocalRingOfFinite [Finite σ] [HenselianLocalRing R] :
    HenselianLocalRing (MvPowerSeries σ R) where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ ha₀ hu := by
    set φ : MvPowerSeries σ R →+* R := constantCoeff
    have hmem : ∀ x, x ∈ maximalIdeal (MvPowerSeries σ R) ↔ φ x ∈ maximalIdeal R := by
      intro x
      simp only [mem_maximalIdeal, mem_nonunits_iff, φ, isUnit_iff_constantCoeff]
    have hunit : ∀ x, IsUnit x ↔ IsUnit (φ x) := fun x => isUnit_iff_constantCoeff
    have heval : ∀ (p : Polynomial (MvPowerSeries σ R)) (x), φ (p.eval x) = (p.map φ).eval (φ x) :=
      fun p x => by rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian (f.map φ) (hf.map φ) (φ a₀)
      (by rw [← heval]; exact (hmem _).1 ha₀)
      (by rw [Polynomial.derivative_map, ← heval]; exact (hunit _).1 hu)
    have hφC : φ (C b) = b := constantCoeff_C b
    -- the derivative stays a unit at `b`
    have hub : IsUnit (φ (f.derivative.eval (C b))) := by
      rw [heval, hφC, ← Polynomial.derivative_map]
      have hy : IsUnit (((f.map φ).derivative).eval (φ a₀)) := by
        rw [Polynomial.derivative_map, ← heval]; exact (hunit _).1 hu
      have hd : ((f.map φ).derivative).eval b - ((f.map φ).derivative).eval (φ a₀) ∈
          maximalIdeal R :=
        Ideal.mem_of_dvd _ (Polynomial.sub_dvd_eval_sub _ _ _) hba
      rw [← notMem_maximalIdeal] at hy ⊢
      intro hx
      exact hy (by simpa using sub_mem hx hd)
    obtain ⟨a, ha, haC⟩ := HenselianRing.is_henselian (I := Ideal.span (Set.range X)) f hf (C b)
      (by rw [mem_span_range_X_iff]; change φ _ = 0; rw [heval, hφC]; exact hb)
      (((hunit _).2 hub).map _)
    refine ⟨a, ha, (hmem _).2 ?_⟩
    have h0 : φ (a - C b) = 0 := mem_span_range_X_iff.1 haC
    have : φ (a - a₀) = φ (a - C b) + (b - φ a₀) := by
      rw [map_sub, map_sub, hφC]; ring
    rw [this, h0, zero_add]
    exact hba

end MvPowerSeries

namespace MvPolynomial

variable {A : Type u} [CommRing A] [IsLocalRing A] {σ : Type v}

omit [IsLocalRing A] in
/-- The constant coefficient of a polynomial is that of the associated power series. -/
@[simp]
theorem constantCoeff_coe (f : MvPolynomial σ A) :
    MvPowerSeries.constantCoeff (f : MvPowerSeries σ A) = constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coe, constantCoeff_eq]

/-- The local homomorphism `A[T]_{𝔭₀} → A[[T]]` induced by the inclusion of polynomials into
formal power series. -/
noncomputable def localizationAtOriginToMvPowerSeries :
    LocalizationAtOrigin A σ →+* MvPowerSeries σ A :=
  IsLocalization.lift (M := (originIdeal A σ).primeCompl)
    (g := (coeToMvPowerSeries.ringHom : MvPolynomial σ A →+* MvPowerSeries σ A)) fun y => by
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      change IsUnit (MvPowerSeries.constantCoeff (y : MvPowerSeries σ A))
      rw [constantCoeff_coe, ← notMem_maximalIdeal]
      exact y.2

@[simp]
theorem localizationAtOriginToMvPowerSeries_algebraMap (f : MvPolynomial σ A) :
    localizationAtOriginToMvPowerSeries (algebraMap _ _ f) = (f : MvPowerSeries σ A) :=
  IsLocalization.lift_eq _ _

instance : IsLocalHom (localizationAtOriginToMvPowerSeries (A := A) (σ := σ)) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (originIdeal A σ).primeCompl x
  dsimp only at hx ⊢
  have hspec := IsLocalization.mk'_spec (LocalizationAtOrigin A σ) f s
  have hs : IsUnit (algebraMap (MvPolynomial σ A) (LocalizationAtOrigin A σ) s) :=
    IsLocalization.map_units _ s
  have hf : IsUnit (algebraMap (MvPolynomial σ A) (LocalizationAtOrigin A σ) f) := by
    have h1 : IsUnit (localizationAtOriginToMvPowerSeries
        (algebraMap (MvPolynomial σ A) (LocalizationAtOrigin A σ) f)) := by
      rw [← hspec, map_mul]
      exact hx.mul (hs.map _)
    rw [localizationAtOriginToMvPowerSeries_algebraMap, MvPowerSeries.isUnit_iff_constantCoeff,
      constantCoeff_coe, ← notMem_maximalIdeal] at h1
    exact IsLocalization.map_units _ (⟨f, h1⟩ : (originIdeal A σ).primeCompl)
  rw [← hspec] at hf
  exact isUnit_of_mul_isUnit_left hf

omit [IsLocalRing A] in
/-- A polynomial lies in `(T)^v` iff it does as a power series. -/
theorem coe_mem_pow_span_range_X_iff [Finite σ] {k : ℕ} {f : MvPolynomial σ A} :
    (f : MvPowerSeries σ A) ∈ Ideal.span (Set.range MvPowerSeries.X) ^ k ↔
      f ∈ idealOfVars σ A ^ k := by
  rw [MvPowerSeries.mem_pow_span_range_X_iff, mem_pow_idealOfVars_iff']
  simp only [coeff_coe]

namespace IsHenselianPolynomialRing

variable [Finite σ]

/-- An element of `A[T]_{𝔭₀}` whose image in `A[[T]]` lies in `(T)^k` lies in `(T)^k`. -/
theorem mem_pow_of_localizationAtOriginToMvPowerSeries_mem {k : ℕ}
    {r : LocalizationAtOrigin A σ}
    (hr : localizationAtOriginToMvPowerSeries r ∈ Ideal.span (Set.range MvPowerSeries.X) ^ k) :
    r ∈ ((idealOfVars σ A).map (algebraMap _ (LocalizationAtOrigin A σ))) ^ k := by
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (originIdeal A σ).primeCompl r
  dsimp only at hr ⊢
  have hspec := IsLocalization.mk'_spec (LocalizationAtOrigin A σ) f s
  have hf : (f : MvPowerSeries σ A) ∈ Ideal.span (Set.range MvPowerSeries.X) ^ k := by
    rw [← localizationAtOriginToMvPowerSeries_algebraMap, ← hspec, map_mul]
    exact Ideal.mul_mem_right _ _ hr
  rw [coe_mem_pow_span_range_X_iff] at hf
  rw [IsLocalization.mk'_eq_mul_mk'_one, ← Ideal.map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hf)

end IsHenselianPolynomialRing

end MvPolynomial

namespace MvPolynomial.IsHenselianPolynomialRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A] {σ : Type v}
  [Finite σ]

/-- **`A{T}` embeds into `A[[T]]`.** Let `A` be a henselian noetherian local ring and `T` a finite
family of indeterminates. Every `A[T]_{𝔭₀}`-algebra map `A{T} → A[[T]]` is injective, for the
algebra structure on `A[[T]]` given by `localizationAtOriginToMvPowerSeries`. -/
theorem injective_algHom_toMvPowerSeries {B : Type w} [CommRing B] [IsLocalRing B]
    [Algebra (LocalizationAtOrigin A σ) B] (h : IsHenselianPolynomialRing A σ B)
    [Algebra (LocalizationAtOrigin A σ) (MvPowerSeries σ A)]
    (hρ : algebraMap (LocalizationAtOrigin A σ) (MvPowerSeries σ A) =
      localizationAtOriginToMvPowerSeries)
    (π : B →ₐ[LocalizationAtOrigin A σ] MvPowerSeries σ A) :
    Function.Injective π := by
  set R := LocalizationAtOrigin A σ
  set P := MvPowerSeries σ A
  set ρ : R →+* P := localizationAtOriginToMvPowerSeries
  have : IsHenselization R (ResidueField R) B := h
  have : IsNoetherianRing B := isNoetherianRing_of_isHenselization (A := R) (ResidueField R)
  set JP : Ideal P := Ideal.span (Set.range MvPowerSeries.X)
  set J : Ideal R := (idealOfVars σ A).map (algebraMap _ R)
  set JB : Ideal B := J.map (algebraMap R B)
  have hπalg : ∀ r : R, π (algebraMap R B r) = ρ r := fun r => by
    rw [π.commutes, hρ]
  -- `π` maps `(T) A{T}` into `(T) A[[T]]`
  have hJP : J ≤ JP.comap ρ := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change ρ (algebraMap _ R (X i)) ∈ JP
    rw [localizationAtOriginToMvPowerSeries_algebraMap, coe_X]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hJB : JB ≤ JP.comap π.toRingHom := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
    intro r hr
    change π (algebraMap R B r) ∈ JP
    rw [hπalg]
    exact hJP hr
  have hJPne : JP ≠ ⊤ := by
    intro htop
    have h1 : (1 : P) ∈ JP := htop ▸ Submodule.mem_top
    rw [MvPowerSeries.mem_span_range_X_iff, map_one] at h1
    exact one_ne_zero h1
  have hJBne : JB ≠ ⊤ := by
    intro htop
    have h1 : (1 : B) ∈ JB.comap (RingHom.id B) := htop ▸ Submodule.mem_top
    have := hJB h1
    rw [Ideal.mem_comap, map_one] at this
    exact hJPne ((Ideal.eq_top_iff_one _).2 this)
  have hJmax : J ≤ maximalIdeal R := by
    refine le_maximalIdeal fun htop => hJPne ((Ideal.eq_top_iff_one _).2 ?_)
    have h1 : (1 : R) ∈ J := htop ▸ Submodule.mem_top
    simpa using hJP h1
  -- the kernel of `π` lies in `(T)^k A{T}` for every `k`
  have hker : ∀ k, ∀ x : B, π x = 0 → x ∈ JB ^ k := by
    intro k x hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    -- `A[T]_{𝔭₀}/(T)^k ≅ A[[T]]/(T)^k` is henselian
    let q : R →+* P ⧸ JP ^ k := (Ideal.Quotient.mk (JP ^ k)).comp ρ
    have hq : Function.Surjective q := by
      intro y
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨algebraMap _ R (MvPowerSeries.truncTotal k g), ?_⟩
      change Ideal.Quotient.mk _ (ρ _) = _
      rw [localizationAtOriginToMvPowerSeries_algebraMap, Ideal.Quotient.eq,
        MvPowerSeries.mem_pow_span_range_X_iff]
      intro n hn
      rw [map_sub, coeff_coe, MvPowerSeries.coeff_truncTotal _ hn, sub_self]
    have hkerq : RingHom.ker q = J ^ k := by
      ext r
      rw [RingHom.mem_ker]
      change Ideal.Quotient.mk _ (ρ r) = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem]
      refine ⟨mem_pow_of_localizationAtOriginToMvPowerSeries_mem, fun hr => ?_⟩
      have : J ^ k ≤ (JP ^ k).comap ρ :=
        (Ideal.pow_right_mono hJP k).trans (Ideal.le_comap_pow ρ k)
      exact this hr
    have hPk : JP ^ k ≠ ⊤ := fun htop => hJPne (eq_top_iff.2 (htop ▸ Ideal.pow_le_self hk.ne'))
    have : HenselianLocalRing (P ⧸ JP ^ k) := Stacks.Henselian.henselianLocalRing_quotient hPk
    have : HenselianLocalRing (R ⧸ J ^ k) := HenselianLocalRing.of_ringEquiv
      ((Ideal.quotEquivOfEq hkerq.symm).trans (RingHom.quotientKerEquivOfSurjective hq)).symm
    obtain ⟨-, hsurj⟩ := IsHenselization.quotientMap_bijective_of_henselianLocalRing
      (Rh := B) (J ^ k) ((Ideal.pow_le_self hk.ne').trans hJmax)
    obtain ⟨r', hr'⟩ := hsurj (Ideal.Quotient.mk _ x)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r'
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, Ideal.map_pow] at hr'
    have hBk : JB ^ k ≤ (JP ^ k).comap π.toRingHom :=
      (Ideal.pow_right_mono hJB k).trans (Ideal.le_comap_pow _ k)
    have h1 : ρ r ∈ JP ^ k := by
      have := hBk hr'
      rw [Ideal.mem_comap, map_sub] at this
      change π _ - π x ∈ _ at this
      rw [hx, sub_zero, hπalg] at this
      exact this
    have h2 : algebraMap R B r ∈ JB ^ k := by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (mem_pow_of_localizationAtOriginToMvPowerSeries_mem h1)
    have := sub_mem h2 hr'
    simpa using this
  -- Krull's intersection theorem
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing JB hJBne
  have : x ∈ ⨅ k, JB ^ k := Ideal.mem_iInf.2 fun k => hker k x hx
  rwa [hinf, Ideal.mem_bot] at this

/-- **The Henselization of a polynomial ring over a henselian local domain is a domain.** Let
`A` be a henselian noetherian local integral domain and `T` a finite family of indeterminates.
Then the Henselization `A{T}` of `A[T]` at the origin is an integral domain. -/
@[weil "lem_fk107_henselian_line_domain"]
theorem isDomain [IsDomain A] {B : Type w} [CommRing B] [IsLocalRing B]
    [Algebra (LocalizationAtOrigin A σ) B] (h : IsHenselianPolynomialRing A σ B) :
    IsDomain B := by
  let : Algebra (LocalizationAtOrigin A σ) (MvPowerSeries σ A) :=
    (localizationAtOriginToMvPowerSeries (A := A) (σ := σ)).toAlgebra
  have : IsLocalHom (algebraMap (LocalizationAtOrigin A σ) (MvPowerSeries σ A)) :=
    inferInstanceAs (IsLocalHom localizationAtOriginToMvPowerSeries)
  have : IsHenselization (LocalizationAtOrigin A σ)
    (ResidueField (LocalizationAtOrigin A σ)) B := h
  obtain ⟨π, -, -, -⟩ := StacksDraft.existsUnique_henselization_map
    (R := LocalizationAtOrigin A σ) (A := LocalizationAtOrigin A σ) (Ah := B)
    (B := MvPowerSeries σ A)
  have : IsDomain (MvPowerSeries σ A) := NoZeroDivisors.to_isDomain _
  exact (injective_algHom_toMvPowerSeries h rfl π).isDomain π.toRingHom

end MvPolynomial.IsHenselianPolynomialRing
