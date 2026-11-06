module

public import Weil.Attr
public import WeilFrontier.RingTheory.Etale.Locus

/-!
# Spreading out a local-étale map from a polynomial ring

Let `A` be a noetherian ring, `C₀` a finitely generated `A`-algebra, `𝔮` a prime of `C₀` and
`C = (C₀)_𝔮`. Let `ψ : A[T₁, …, T_r] → C` be an `A`-algebra homomorphism and
`𝔭 = ψ⁻¹(𝔪_C)`, and suppose that the induced local homomorphism `A[T]_𝔭 → C` is local-étale.
Then there are `s ∈ C₀ ∖ 𝔮` and an étale `A`-algebra homomorphism `ψ₂ : A[T] → C₀[1/s]` whose
composite with the localization map `C₀[1/s] → C` is `ψ`.

The images `ψ(Tᵢ)` have a common denominator `b ∉ 𝔮`, so `ψ` factors through
`C₁ = C₀[1/b]`, which is of finite type over `A[T]`. The local ring of `C₁` at `𝔮₁ = 𝔮 C₁` is
`C`, so `C₁` is étale over `A[T]` at `𝔮₁`, hence étale over `A[T]` after inverting some
`f = c / bᵐ ∉ 𝔮₁`; and `C₁[1/f] = C₀[1/(b c)]`.

## Main results

* `Algebra.isLocalHom_of_comp_algebraMap_eq`: the homomorphism `A[T]_𝔭 → C` induced by `ψ` is
  local.
* `Algebra.exists_etale_away_comp_eq_of_isEtaleLocalHom`: the statement above.

## Implementation notes

The variables `T₁, …, T_r` are indexed by an arbitrary finite type `σ`. The induced homomorphism
`A[T]_𝔭 → C` is given as a ring homomorphism `f` with `f ∘ (A[T] → A[T]_𝔭) = ψ`; such an `f` is
unique by the universal property of localization, and it is local
(`Algebra.isLocalHom_of_comp_algebraMap_eq`). Local-étale is `RingHom.IsEtaleLocalHom`, and an
étale ring homomorphism is `RingHom.Etale` (flat, formally unramified, of finite presentation),
which over a noetherian ring is the source's notion. The map `C₀[1/s] → C` is
`IsLocalization.Away.lift`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1.7
-/

@[expose] public section

namespace Algebra

open IsLocalRing

/-- Let `S` be a local ring and `ψ : R → S` a ring homomorphism. A homomorphism
`f : R_𝔭 → S`, with `𝔭 = ψ⁻¹(𝔪_S)`, extending `ψ` is a local homomorphism. -/
theorem isLocalHom_of_comp_algebraMap_eq {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S]
    (ψ : R →+* S) (f : Localization.AtPrime ((maximalIdeal S).comap ψ) →+* S)
    (hf : f.comp (algebraMap _ _) = ψ) : IsLocalHom f := by
  constructor
  intro x hx
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective
    ((maximalIdeal S).comap ψ).primeCompl x
  have ht : IsUnit (ψ t) := by
    by_contra h
    exact t.2 (by simpa [Ideal.mem_comap] using h)
  have hspec := congrArg f (IsLocalization.mk'_spec (Localization.AtPrime
    ((maximalIdeal S).comap ψ)) a t)
  rw [map_mul] at hspec
  have hfa : ∀ y, f (algebraMap R _ y) = ψ y := fun y => congrArg (· y) hf
  rw [hfa, hfa] at hspec
  have ha : IsUnit (ψ a) := hspec ▸ hx.mul ht
  have ha' : a ∈ ((maximalIdeal S).comap ψ).primeCompl := by
    simpa [Ideal.primeCompl, Ideal.mem_comap] using ha
  change IsUnit (IsLocalization.mk' _ a t)
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact (IsLocalization.map_units _ ⟨a, ha'⟩).mul (isUnit_of_invertible _)

variable {A C₀ σ : Type*} [CommRing A] [CommRing C₀] [Algebra A C₀] [IsNoetherianRing A]
  [FiniteType A C₀] [Finite σ]

/-- **A local-étale map from a polynomial ring spreads out.** Let `A` be a noetherian ring, `C₀`
a finitely generated `A`-algebra, `𝔮` a prime of `C₀`, and `ψ : A[T] → (C₀)_𝔮` an `A`-algebra
homomorphism such that the induced local homomorphism `f : A[T]_𝔭 → (C₀)_𝔮`, `𝔭 = ψ⁻¹(𝔪)`, is
local-étale. Then there are `s ∉ 𝔮` and an étale `A`-algebra homomorphism `ψ₂ : A[T] → C₀[1/s]`
whose composite with the localization map `C₀[1/s] → (C₀)_𝔮` is `ψ`. -/
@[weil "lem_fk107_local_etale_over_polynomial_spreads_out"]
theorem exists_etale_away_comp_eq_of_isEtaleLocalHom (q : Ideal C₀) [q.IsPrime]
    (ψ : MvPolynomial σ A →ₐ[A] Localization.AtPrime q)
    (f : Localization.AtPrime ((maximalIdeal (Localization.AtPrime q)).comap ψ) →+*
      Localization.AtPrime q)
    (hf : f.comp (algebraMap _ _) = ψ.toRingHom) :
    letI : IsNoetherianRing C₀ := FiniteType.isNoetherianRing A C₀
    letI : IsLocalHom f := isLocalHom_of_comp_algebraMap_eq ψ.toRingHom f hf
    f.IsEtaleLocalHom →
      ∃ (s : C₀) (hs : s ∉ q) (ψ₂ : MvPolynomial σ A →ₐ[A] Localization.Away s),
        ψ₂.toRingHom.Etale ∧
        (IsLocalization.Away.lift s
          ((IsLocalization.AtPrime.isUnit_to_map_iff _ q s).2 hs)).comp ψ₂.toRingHom =
          ψ.toRingHom := by
  intro h
  set C := Localization.AtPrime q
  set R := MvPolynomial σ A
  set p := (maximalIdeal C).comap ψ
  have : Fintype σ := Fintype.ofFinite σ
  -- A common denominator `b ∉ 𝔮` of the `ψ(Tᵢ)`.
  obtain ⟨⟨b, hb⟩, hb'⟩ := IsLocalization.exist_integer_multiples q.primeCompl Finset.univ
    (fun i => ψ (MvPolynomial.X i))
  choose a ha using fun i => hb' i (Finset.mem_univ i)
  set C₁ := Localization.Away b
  let ψ₁ : R →ₐ[A] C₁ :=
    MvPolynomial.aeval fun i => algebraMap C₀ C₁ (a i) * IsLocalization.Away.invSelf b
  have hle : Submonoid.powers b ≤ q.primeCompl := Submonoid.powers_le.mpr hb
  let : Algebra C₁ C := IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  have : IsScalarTower C₀ C₁ C :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have hinv : algebraMap C₀ C b * algebraMap C₁ C (IsLocalization.Away.invSelf b) = 1 := by
    rw [IsScalarTower.algebraMap_apply C₀ C₁ C, ← map_mul, IsLocalization.Away.mul_invSelf,
      map_one]
  have hg₁ : (algebraMap C₁ C).comp ψ₁.toRingHom = ψ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change algebraMap C₁ C (ψ₁ (MvPolynomial.C r)) = ψ (MvPolynomial.C r)
      rw [MvPolynomial.algHom_C ψ₁, MvPolynomial.algHom_C ψ, IsScalarTower.algebraMap_apply A C₀ C₁,
        ← IsScalarTower.algebraMap_apply C₀ C₁ C, ← IsScalarTower.algebraMap_apply A C₀ C]
    · intro i
      change algebraMap C₁ C (ψ₁ (MvPolynomial.X i)) = ψ (MvPolynomial.X i)
      rw [show ψ₁ (MvPolynomial.X i) = _ from MvPolynomial.aeval_X _ i, map_mul,
        ← IsScalarTower.algebraMap_apply C₀ C₁ C, ha i, Algebra.smul_def,
        mul_comm (algebraMap C₀ C b), mul_assoc, hinv, mul_one]
  -- `C₁` as an `A[T]`-algebra, and the prime `𝔮₁ = 𝔮 C₁`.
  let : Algebra R C₁ := ψ₁.toRingHom.toAlgebra
  let : Algebra R C := ψ.toRingHom.toAlgebra
  have : IsScalarTower R C₁ C := IsScalarTower.of_algebraMap_eq' hg₁.symm
  have : IsScalarTower A R C₁ := IsScalarTower.of_algebraMap_eq fun r => (ψ₁.commutes r).symm
  have : FiniteType A C₁ := FiniteType.trans (S := C₀) inferInstance inferInstance
  have : FiniteType R C₁ := FiniteType.of_restrictScalars_finiteType A R C₁
  have : FinitePresentation R C₁ := FinitePresentation.of_finiteType.mp inferInstance
  let q₁ : Ideal C₁ := q.map (algebraMap C₀ C₁)
  have hdisj : Disjoint (Submonoid.powers b : Set C₀) q := by
    rw [Set.disjoint_right]
    rintro x hx ⟨n, rfl⟩
    exact hb (‹q.IsPrime›.mem_of_pow_mem n hx)
  have : q₁.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ q ‹_› hdisj
  have hcomap : q₁.under C₀ = q := IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hdisj
  -- `(C₁)_{𝔮₁}` is `C`.
  have : IsLocalization.AtPrime (Localization.AtPrime q₁) q := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers b) (Localization.AtPrime q₁) q₁
    have heq : (q₁.comap (algebraMap C₀ C₁)).primeCompl = q.primeCompl := by
      ext x
      simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe, show q₁.comap (algebraMap C₀ C₁) = q from hcomap]
    change IsLocalization q.primeCompl _
    exact heq ▸ this
  let e₀ : Localization.AtPrime q₁ ≃ₐ[C₀] C :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q₁) C
  have he₀ : (e₀ : Localization.AtPrime q₁ →+* C).comp
      (algebraMap C₁ (Localization.AtPrime q₁)) = algebraMap C₁ C := by
    apply IsLocalization.ringHom_ext (Submonoid.powers b)
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply,
      RingHom.coe_coe]
    exact e₀.commutes x
  let e : Localization.AtPrime q₁ ≃ₐ[R] C := AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) fun x => by
    rw [IsScalarTower.algebraMap_apply R C₁ (Localization.AtPrime q₁),
      IsScalarTower.algebraMap_apply R C₁ C]
    exact congrArg (· (algebraMap R C₁ x)) he₀
  -- `C` is flat and formally unramified over `A[T]`.
  let : Algebra (Localization.AtPrime p) C := f.toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) C := IsScalarTower.of_algebraMap_eq' hf.symm
  obtain ⟨hfl, hfu, -⟩ := h
  have : Module.Flat (Localization.AtPrime p) C := hfl
  have : FormallyUnramified (Localization.AtPrime p) C := hfu
  have : Module.Flat R C := Module.Flat.trans R (Localization.AtPrime p) C
  have : FormallyUnramified R C := FormallyUnramified.comp R (Localization.AtPrime p) C
  have : FormallyUnramified R (Localization.AtPrime q₁) := .of_equiv e.symm
  have : Module.Flat R (Localization.AtPrime q₁) := Module.Flat.of_linearEquiv e.toLinearEquiv
  have : IsUnramifiedAt R q₁ := ‹_›
  let p₁ : Ideal R := q₁.under R
  have : q₁.LiesOver p₁ := ⟨rfl⟩
  let : Algebra (Localization.AtPrime p₁) (Localization.AtPrime q₁) :=
    Localization.AtPrime.algebraOfLiesOver p₁ q₁
  have : Localization.AtPrime.IsLiesOverAlgebra p₁ q₁ := inferInstance
  have : Module.Flat (Localization.AtPrime p₁) (Localization.AtPrime q₁) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p₁) p₁.primeCompl _).2 ‹_›
  have : IsEtaleAt R q₁ := IsEtaleAt.of_flat_of_map_eq_maximalIdeal p₁ q₁
    ((isUnramifiedAt_iff_map_eq R p₁ q₁).mp inferInstance).2
  -- Spread out over a basic open `D(c / bᵐ) ∋ 𝔮₁` of `Spec C₁`, and `C₁[bᵐ / c] = C₀[1 / (b c)]`.
  obtain ⟨f', hf', het⟩ := exists_etale_of_isEtaleAt (R := R) q₁
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers b) f'
  change IsLocalization.mk' C₁ c t ∉ q₁ at hf'
  change Etale R (Localization.Away (IsLocalization.mk' C₁ c t)) at het
  have hassoc : Associated (algebraMap C₀ C₁ c) (IsLocalization.mk' C₁ c t) := by
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact associated_mul_unit_right _ _ (isUnit_of_invertible _)
  set T := Localization.Away (IsLocalization.mk' C₁ c t)
  have : IsLocalization.Away (b * c) T := IsLocalization.Away.mul_of_associated b c _ hassoc
  have hc : c ∉ q := by
    intro hc
    apply hf'
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact q₁.mul_mem_right _ (Ideal.mem_map_of_mem _ hc)
  have hs : b * c ∉ q := fun h => (‹q.IsPrime›.mem_or_mem h).elim hb hc
  let eT : Localization.Away (b * c) ≃ₐ[C₀] T :=
    IsLocalization.algEquiv (Submonoid.powers (b * c)) _ _
  let ψ₂ : R →ₐ[A] Localization.Away (b * c) :=
    { toRingHom := (eT.symm : T →+* Localization.Away (b * c)).comp (algebraMap R T)
      commutes' := fun r => by
        change eT.symm (algebraMap R T (algebraMap A R r)) = _
        rw [IsScalarTower.algebraMap_apply R C₁ T, ← IsScalarTower.algebraMap_apply A R C₁,
          IsScalarTower.algebraMap_apply A C₀ C₁, ← IsScalarTower.algebraMap_apply C₀ C₁ T,
          AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply A C₀] }
  refine ⟨b * c, hs, ψ₂, ?_, ?_⟩
  · let : Algebra R (Localization.Away (b * c)) := ψ₂.toRingHom.toAlgebra
    let eR : T ≃ₐ[R] Localization.Away (b * c) :=
      AlgEquiv.ofRingEquiv (f := eT.symm.toRingEquiv) fun _ => rfl
    have : Etale R (Localization.Away (b * c)) := .of_equiv eR
    exact RingHom.etale_algebraMap.mpr this
  · set L : Localization.Away (b * c) →+* C := IsLocalization.Away.lift (b * c)
      ((IsLocalization.AtPrime.isUnit_to_map_iff C q (b * c)).2 hs)
    have hL : (L.comp (eT.symm : T →+* Localization.Away (b * c))).comp (algebraMap C₁ T) =
        algebraMap C₁ C := by
      apply IsLocalization.ringHom_ext (Submonoid.powers b)
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [← IsScalarTower.algebraMap_apply C₀ C₁ T, AlgEquiv.commutes,
        ← IsScalarTower.algebraMap_apply C₀ C₁ C]
      exact IsLocalization.lift_eq _ x
    change L.comp ((eT.symm : T →+* Localization.Away (b * c)).comp (algebraMap R T)) = _
    rw [IsScalarTower.algebraMap_eq R C₁ T, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hL]
    exact hg₁

end Algebra
