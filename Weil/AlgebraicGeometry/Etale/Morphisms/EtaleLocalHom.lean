module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import Weil.Defs.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Etale.Locus

/-!
# Base change of local-étale homomorphisms, localized

Let `R → E` be a local-étale homomorphism of noetherian local rings and `R → F` a homomorphism
to a noetherian local ring. If `Q` is a prime ideal of `F ⊗[R] E` lying over the maximal ideal of
`F`, then `F → (F ⊗[R] E)_Q` is again local-étale.

The proof uses the description of `RingHom.IsEtaleLocalHom` as flat, formally unramified and
essentially of finite type: each of these is stable under base change and under localization,
and composes.

## Main results

* `Algebra.isNoetherianRing_localization_tensorProduct`: `(F ⊗[R] E)_Q` is noetherian when `E` is
  essentially of finite type over `R` and `F` is noetherian.
* `Algebra.isLocalHom_algebraMap_localization_of_comap_eq_maximalIdeal`: `F → B_Q` is a local
  homomorphism when `Q` lies over the maximal ideal of `F`.
* `Algebra.isEtaleLocalHom_algebraMap_localization_tensorProduct`: the localized base change of
  a local-étale homomorphism is local-étale.

## Implementation notes

The tensor product is written `F ⊗[R] E`, so that its `F`-algebra structure is Mathlib's default
one; it is isomorphic to `E ⊗[R] F` as an `F`-algebra. The source assumes `R → F` local; this
is not needed, since flatness, formal unramifiedness and essential finite type are stable under
arbitrary base change.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3
-/

@[expose] public section

universe u v w

open IsLocalRing TensorProduct

namespace Algebra

/-- If `Q` is a prime of an `F`-algebra `B` lying over the maximal ideal of the local ring `F`,
then `F → B_Q` is a local homomorphism. -/
theorem isLocalHom_algebraMap_localization_of_comap_eq_maximalIdeal {F : Type v} {B : Type w}
    [CommRing F] [CommRing B] [Algebra F B] [IsLocalRing F] (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap F B) = maximalIdeal F) :
    IsLocalHom (algebraMap F (Localization.AtPrime Q)) := by
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have hxQ : algebraMap F B x ∈ Q := by
    rw [← Ideal.mem_comap, hQ]
    exact (mem_maximalIdeal x).2 h
  rw [IsScalarTower.algebraMap_apply F B (Localization.AtPrime Q)] at hx
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q _).1 hx hxQ

/-- The localization at a prime of `F ⊗[R] E` is noetherian when `E` is essentially of finite
type over `R` and `F` is noetherian. -/
theorem isNoetherianRing_localization_tensorProduct (R : Type u) (E : Type v) (F : Type w)
    [CommRing R] [CommRing E] [CommRing F] [Algebra R E] [Algebra R F] [EssFiniteType R E]
    [IsNoetherianRing F] (Q : Ideal (F ⊗[R] E)) [Q.IsPrime] :
    IsNoetherianRing (Localization.AtPrime Q) :=
  have : EssFiniteType F (Localization.AtPrime Q) :=
    EssFiniteType.comp F (F ⊗[R] E) _
  EssFiniteType.isNoetherianRing F _

/-- **Localized base change of a local-étale homomorphism.** Let `R → E` be a local-étale
homomorphism of noetherian local rings and `F` a noetherian local `R`-algebra. If `Q` is a prime
of `F ⊗[R] E` whose preimage in `F` is the maximal ideal, then `F → (F ⊗[R] E)_Q` is
local-étale. -/
@[weil "lem_fk103_local_etale_base_change_localized"]
theorem isEtaleLocalHom_algebraMap_localization_tensorProduct
    (R : Type u) (E : Type v) (F : Type w) [CommRing R] [CommRing E] [CommRing F]
    [Algebra R E] [Algebra R F] [IsNoetherianRing R] [IsNoetherianRing E] [IsNoetherianRing F]
    [IsLocalRing R] [IsLocalRing E] [IsLocalRing F] [IsLocalHom (algebraMap R E)]
    (hE : (algebraMap R E).IsEtaleLocalHom) (Q : Ideal (F ⊗[R] E)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap F (F ⊗[R] E)) = maximalIdeal F) :
    letI : EssFiniteType R E := RingHom.essFiniteType_algebraMap.mp hE.2.2
    letI := isNoetherianRing_localization_tensorProduct R E F Q
    letI := isLocalHom_algebraMap_localization_of_comap_eq_maximalIdeal Q hQ
    (algebraMap F (Localization.AtPrime Q)).IsEtaleLocalHom := by
  obtain ⟨hfl, hfu, hfe⟩ := hE
  have : Module.Flat R E := RingHom.flat_algebraMap_iff.mp hfl
  have : FormallyUnramified R E := RingHom.formallyUnramified_algebraMap.mp hfu
  have : EssFiniteType R E := RingHom.essFiniteType_algebraMap.mp hfe
  have := isNoetherianRing_localization_tensorProduct R E F Q
  have := isLocalHom_algebraMap_localization_of_comap_eq_maximalIdeal Q hQ
  have : Module.Flat (F ⊗[R] E) (Localization.AtPrime Q) :=
    IsLocalization.flat _ Q.primeCompl
  have : Module.Flat F (Localization.AtPrime Q) := Module.Flat.trans F (F ⊗[R] E) _
  have : FormallyUnramified (F ⊗[R] E) (Localization.AtPrime Q) :=
    FormallyUnramified.of_isLocalization Q.primeCompl
  have : FormallyUnramified F (Localization.AtPrime Q) :=
    FormallyUnramified.comp F (F ⊗[R] E) _
  have : EssFiniteType F (Localization.AtPrime Q) := EssFiniteType.comp F (F ⊗[R] E) _
  exact ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
    RingHom.formallyUnramified_algebraMap.mpr inferInstance,
    RingHom.essFiniteType_algebraMap.mpr inferInstance⟩

end Algebra

end

/-! ### Localizations of local-étale homomorphisms -/

/-!
# Localizations of local-étale homomorphisms

Let `A → B` be a local-étale homomorphism of noetherian local rings (`RingHom.IsEtaleLocalHom`),
`𝔭 ⊆ B` a prime ideal and `𝔮 = 𝔭 ∩ A`. Then the induced homomorphism `A_𝔮 → B_𝔭` is again
local-étale: flatness passes to `B_𝔭` over `A` by transitivity and then to `A_𝔮` by
localization of the base; formal unramifiedness passes to `B_𝔭` because a localization is
formally étale, and then to `A_𝔮`; essential finite type is preserved in the same way.

## Main results

* `Algebra.isEtaleLocalHom_localization_atPrime`: for a prime `𝔭` of `B` lying over `𝔮`,
  `A_𝔮 → B_𝔭` is local-étale.
* `Algebra.isEtaleLocalHom_localization_comap_atPrime`: the same with `𝔮 = 𝔭 ∩ A` and the
  canonical algebra structure.

## Implementation notes

The algebra structure of `B_𝔭` over `A_𝔮` is any one compatible with
`Localization.localRingHom` (the class `Localization.AtPrime.IsLiesOverAlgebra`); the algebra map
is then a local homomorphism by the instance
`Localization.AtPrime.isLocalHom_algebraMap_of_isLiesOverAlgebra`. The
unramified part is proved with formal unramifiedness, which by definition is the vanishing of the
Kähler differentials (`Algebra.FormallyUnramified`), so no comparison with `m_A B = m_B` is
needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

@[expose] public section

universe u v

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

/-- Let `A → B` be local-étale and `𝔭` a prime of `B` lying over the prime `𝔮` of `A`. Then
`A_𝔮 → B_𝔭` is local-étale. -/
@[weil "lem_fk101_localization_of_local_etale_is_local_etale"]
theorem isEtaleLocalHom_localization_atPrime (h : (algebraMap A B).IsEtaleLocalHom)
    (q : Ideal A) [q.IsPrime] (p : Ideal B) [p.IsPrime] [p.LiesOver q]
    [Algebra (Localization.AtPrime q) (Localization.AtPrime p)]
    [Localization.AtPrime.IsLiesOverAlgebra q p] :
    (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)).IsEtaleLocalHom := by
  obtain ⟨hf, hu, he⟩ := h
  rw [RingHom.flat_algebraMap_iff] at hf
  rw [RingHom.formallyUnramified_algebraMap] at hu
  rw [RingHom.essFiniteType_algebraMap] at he
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
    RingHom.formallyUnramified_algebraMap.mpr ?_, RingHom.essFiniteType_algebraMap.mpr ?_⟩
  · have : FormallyEtale B (Localization.AtPrime p) :=
      FormallyEtale.of_isLocalization p.primeCompl
    have : FormallyUnramified A (Localization.AtPrime p) :=
      FormallyUnramified.comp A B (Localization.AtPrime p)
    exact FormallyUnramified.localization_base q.primeCompl
  · have : EssFiniteType B (Localization.AtPrime p) :=
      EssFiniteType.of_isLocalization (Localization.AtPrime p) p.primeCompl
    have : EssFiniteType A (Localization.AtPrime p) :=
      EssFiniteType.comp A B (Localization.AtPrime p)
    exact EssFiniteType.of_comp A (Localization.AtPrime q) (Localization.AtPrime p)

/-- Let `A → B` be local-étale, `𝔭` a prime of `B` and `𝔮 = 𝔭 ∩ A`. Then `A_𝔮 → B_𝔭` (with its
canonical algebra structure) is local-étale. -/
@[weil "lem_fk101_localization_of_local_etale_is_local_etale"]
theorem isEtaleLocalHom_localization_comap_atPrime (h : (algebraMap A B).IsEtaleLocalHom)
    (p : Ideal B) [p.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (p.comap (algebraMap A B)) p
    (algebraMap (Localization.AtPrime (p.comap (algebraMap A B)))
      (Localization.AtPrime p)).IsEtaleLocalHom := by
  let := Localization.AtPrime.algebraOfLiesOver (p.comap (algebraMap A B)) p
  exact isEtaleLocalHom_localization_atPrime h _ p

end Algebra

end

/-! ### Localizations of standard étale algebras are local-étale -/

/-!
# Localizations of standard étale algebras are local-étale

Let `A` be a noetherian ring, `P₁, …, Pₙ ∈ A[X₁, …, Xₙ]`, and `C = A[X₁, …, Xₙ] ⧸ (P₁, …, Pₙ)`.
The quotient `C` has the naive presentation with `n` variables and `n` relations, whose Jacobian
is the image `Δ` in `C` of the determinant of `(∂P_μ/∂X_ν)`. Inverting `Δ` turns it into a
submersive presentation of relative dimension `0` of `C[Δ⁻¹]`, so `C[Δ⁻¹]` is étale over `A`.
Hence `C` is étale over `A` at every prime `𝔭` not containing `Δ`, and the induced homomorphism
of local rings `A_{𝔭 ∩ A} → C_𝔭` is local-étale.

## Main results

* `Algebra.etale_localizationAway_det_jacobian`: `C[Δ⁻¹]` is étale over `A` (no noetherian
  hypothesis).
* `Algebra.isEtaleLocalHom_localRingHom_of_det_notMem`: for a prime `q` of `C` not containing
  `Δ`, lying over the prime `p` of `A`, the homomorphism `A_p → C_q` is local-étale.
* `Algebra.isEtaleLocalHom_localRingHom_quotient_of_det_notMem`: the same for a prime `𝔭` of
  `A[X₁, …, Xₙ]` containing the `P_μ` with `Δ ∉ 𝔭`, the local ring being
  `(A[X] ⧸ (P))_𝔭 = C_{𝔭 C}`.

## Implementation notes

The variables are indexed by an arbitrary finite type `ι`, which also indexes the polynomials.
Local-étale is `RingHom.IsEtaleLocalHom`: flat, formally unramified and essentially of finite
type. The local ring `(A[X] ⧸ (P))_𝔭` is the localization of the quotient at the image prime
`𝔭 C`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
* [Stacks Project, Tag 039L](https://stacks.math.columbia.edu/tag/039L)
-/

@[expose] public section

universe u v

open MvPolynomial

namespace Algebra

variable {A : Type u} [CommRing A] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The Jacobian of the naive presentation of `A[X] ⧸ (P)` is the image of
`det (∂P_μ/∂X_ν)`. -/
private lemma jacobian_naive_eq (P : ι → MvPolynomial ι A) :
    (PreSubmersivePresentation.naive (R := A) (v := P) _root_.id Function.injective_id).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range P))
        (Matrix.of fun μ ν ↦ pderiv ν (P μ)).det := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have : (PreSubmersivePresentation.naive (R := A) (v := P) _root_.id
      Function.injective_id).jacobiMatrix =
      (Matrix.of fun μ ν ↦ pderiv ν (P μ)).transpose := by
    ext i j
    simp
  rw [this, Matrix.det_transpose]
  rfl

/-- Let `C = A[X] ⧸ (P)` with as many polynomials `P_μ` as variables, and `Δ` the image in `C` of
the determinant of `(∂P_μ/∂X_ν)`. Then `C[Δ⁻¹]` is étale over `A`. -/
theorem etale_localizationAway_det_jacobian (P : ι → MvPolynomial ι A) :
    Algebra.Etale A (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range P))
        (Matrix.of fun μ ν ↦ pderiv ν (P μ)).det)) := by
  set C := MvPolynomial ι A ⧸ Ideal.span (Set.range P)
  set g : C := Ideal.Quotient.mk (Ideal.span (Set.range P))
    (Matrix.of fun μ ν ↦ pderiv ν (P μ)).det
  let N := PreSubmersivePresentation.naive (R := A) (v := P) _root_.id Function.injective_id
  let Q := PreSubmersivePresentation.localizationAway (Localization.Away g) g
  let NQ := Q.comp N
  have hunit : IsUnit NQ.jacobian := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      PreSubmersivePresentation.localizationAway_jacobian, jacobian_naive_eq, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit g).mul (IsLocalization.Away.algebraMap_isUnit g)
  let SP : SubmersivePresentation A (Localization.Away g) (Unit ⊕ ι) (Unit ⊕ ι) :=
    { toPreSubmersivePresentation := NQ, jacobian_isUnit := hunit }
  have : IsStandardSmoothOfRelativeDimension 0 A (Localization.Away g) :=
    SP.isStandardSmoothOfRelativeDimension (by simp [Presentation.dimension])
  infer_instance

/-- Let `C = A[X] ⧸ (P)` with as many polynomials `P_μ` as variables, `A` noetherian, `q` a
prime of `C` not containing the image of `det (∂P_μ/∂X_ν)`, and `p` the prime of `A` below `q`.
Then `A_p → C_q` is local-étale. -/
theorem isEtaleLocalHom_localRingHom_of_det_notMem [IsNoetherianRing A]
    (P : ι → MvPolynomial ι A) (p : Ideal A) [p.IsPrime]
    (q : Ideal (MvPolynomial ι A ⧸ Ideal.span (Set.range P))) [q.IsPrime] [q.LiesOver p]
    (h : Ideal.Quotient.mk (Ideal.span (Set.range P))
      (Matrix.of fun μ ν ↦ pderiv ν (P μ)).det ∉ q) :
    letI : IsNoetherianRing (Localization.AtPrime p) :=
      IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
    letI : IsNoetherianRing (Localization.AtPrime q) :=
      IsLocalization.isNoetherianRing q.primeCompl _
        (Algebra.FiniteType.isNoetherianRing A (MvPolynomial ι A ⧸ Ideal.span (Set.range P)))
    RingHom.IsEtaleLocalHom (A := Localization.AtPrime p) (B := Localization.AtPrime q)
      (Localization.localRingHom p q (algebraMap A _) Ideal.LiesOver.over) := by
  have hE := etale_localizationAway_det_jacobian P
  have hEt : (⟨q, ‹_›⟩ : PrimeSpectrum (MvPolynomial ι A ⧸ Ideal.span (Set.range P))) ∈
      etaleLocus A (MvPolynomial ι A ⧸ Ideal.span (Set.range P)) :=
    basicOpen_subset_etaleLocus_iff.mpr hE.formallyEtale h
  exact (isEtaleAt_iff_isEtaleLocalHom p q).1 hEt

omit [Fintype ι] [DecidableEq ι] in
/-- For an ideal `I ≤ 𝔭` of `A[X]`, the image `𝔭 (A[X] ⧸ I)` of `𝔭` lies over `𝔭 ∩ A`. -/
theorem under_map_quotient_mk (I 𝔭 : Ideal (MvPolynomial ι A)) (hI : I ≤ 𝔭) :
    (𝔭.map (Ideal.Quotient.mk I)).under A = 𝔭.under A := by
  rw [Ideal.under, Ideal.under, IsScalarTower.algebraMap_eq A (MvPolynomial ι A),
    ← Ideal.comap_comap]
  congr 1
  rw [Ideal.Quotient.algebraMap_eq,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI]

/-- **Freitag–Kiehl.** Let `A` be a noetherian ring, `P₁, …, Pₙ ∈ A[X₁, …, Xₙ]`, `𝔭` a prime of
`A[X₁, …, Xₙ]` containing the `P_μ`, `𝔭₀ = 𝔭 ∩ A`, and assume `det (∂P_μ/∂X_ν) ∉ 𝔭`. Then
`A_{𝔭₀} → B = (A[X₁, …, Xₙ] ⧸ (P₁, …, Pₙ))_𝔭` is local-étale. Here the localization at `𝔭` of
the quotient is its localization at the image prime `𝔭 C`, which lies over `𝔭₀`. -/
@[weil "lem_fk101_standard_etale_local_is_local_etale"]
theorem isEtaleLocalHom_localRingHom_quotient_of_det_notMem [IsNoetherianRing A]
    (P : ι → MvPolynomial ι A) (𝔭 : Ideal (MvPolynomial ι A)) [𝔭.IsPrime]
    (hP : ∀ μ, P μ ∈ 𝔭) (h : (Matrix.of fun μ ν ↦ pderiv ν (P μ)).det ∉ 𝔭) :
    letI : (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P)))).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker, Ideal.span_le]; rintro _ ⟨μ, rfl⟩; exact hP μ)
    letI : IsNoetherianRing (Localization.AtPrime (𝔭.under A)) :=
      IsLocalization.isNoetherianRing (𝔭.under A).primeCompl _ inferInstance
    letI : IsNoetherianRing
        (Localization.AtPrime (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P))))) :=
      IsLocalization.isNoetherianRing
        (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P)))).primeCompl _
        (Algebra.FiniteType.isNoetherianRing A (MvPolynomial ι A ⧸ Ideal.span (Set.range P)))
    RingHom.IsEtaleLocalHom (A := Localization.AtPrime (𝔭.under A))
      (B := Localization.AtPrime (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P)))))
      (Localization.localRingHom (𝔭.under A)
        (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P))))
        (algebraMap A (MvPolynomial ι A ⧸ Ideal.span (Set.range P)))
        (under_map_quotient_mk _ 𝔭
          (by rw [Ideal.span_le]; rintro _ ⟨μ, rfl⟩; exact hP μ)).symm) := by
  have hI : Ideal.span (Set.range P) ≤ 𝔭 := by
    rw [Ideal.span_le]; rintro _ ⟨μ, rfl⟩; exact hP μ
  have : (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have : (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P)))).LiesOver (𝔭.under A) :=
    ⟨(under_map_quotient_mk _ 𝔭 hI).symm⟩
  refine isEtaleLocalHom_localRingHom_of_det_notMem P (𝔭.under A) _ ?_
  rwa [Ideal.mem_quotient_iff_mem hI]

end Algebra
