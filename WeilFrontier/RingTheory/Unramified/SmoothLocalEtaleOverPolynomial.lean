module

public import Weil.Attr
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilFrontier.Defs.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import WeilFrontier.Defs.RingTheory.Smooth.Locus

/-!
# Smooth local homomorphisms are local-étale over localized polynomial rings

Let `A → B` be a smooth local homomorphism of noetherian local rings, that is, `B` is the
localization of a smooth `A`-algebra at a prime ideal. Then there are `r ≥ 0` and elements
`x₁, …, x_r ∈ B` such that, for the `A`-algebra map `ψ : A[T₁, …, T_r] → B`, `T_ν ↦ x_ν`, and
`𝔭 = ψ⁻¹(𝔪_B)`, the induced local homomorphism `A[T₁, …, T_r]_𝔭 → B` is local-étale.

## Main results

* `Algebra.exists_isEtaleLocalHom_lift_of_isLocalization_of_etale`: if `D` is étale over `P` and
  the local ring `B` is a localization of `D`, then for `𝔭` the preimage in `P` of the maximal
  ideal of `B`, the homomorphism `P_𝔭 → B` induced by `P → B` is local-étale.
* `Algebra.IsSmoothLocalization.exists_isEtaleLocalHom_localization_mvPolynomial`: the statement
  above.

## Implementation notes

The source argues on the special fibre: a basis of `Ω_{B̄/k}` gives the `x_ν`, the map of special
fibres is shown unramified, injective and hence local-étale over the normal ring `k[T]_𝔭̄`, and the
fibrewise flatness criterion lifts this to `A[T]_𝔭 → B`. Here the local structure of smooth
algebras (`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`) is used instead: if
`B ≅ C_𝔮` with `C` smooth over `A`, there is `f ∉ 𝔮` such that `C_f` is standard étale over a
polynomial ring `A[T₁, …, T_r]`; the `x_ν` are the images of the `T_ν` in `B`, and `B`, a
localization of the étale `A[T]`-algebra `C_f`, is local-étale over `A[T]_𝔭`.

The induced homomorphism `A[T]_𝔭 → B` is part of the conclusion, characterised as the unique ring
homomorphism whose composite with `A[T] → A[T]_𝔭` is `ψ`. Neither locality of `A` nor of the
homomorphism `A → B` is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace Algebra

/-- Let `D` be an étale `P`-algebra and `B` a local ring which is a localization of `D`. For the
preimage `𝔭` in `P` of the maximal ideal of `B`, the homomorphism `P_𝔭 → B` induced by `P → B` is
a local-étale homomorphism. -/
theorem exists_isEtaleLocalHom_lift_of_isLocalization_of_etale {P : Type u} {D : Type v}
    {B : Type w} [CommRing P] [CommRing D] [CommRing B] [Algebra P D] [Algebra D B]
    [Algebra P B] [IsScalarTower P D B] [Algebra.Etale P D] (M : Submonoid D)
    [IsLocalization M B] [IsLocalRing B] [IsNoetherianRing P] [IsNoetherianRing B]
    (ψ : P →+* B) (hψ : ψ = algebraMap P B) :
    ∃ (φ : Localization.AtPrime ((maximalIdeal B).comap ψ) →+* B) (_ : IsLocalHom φ),
      φ.comp (algebraMap P _) = ψ ∧ φ.IsEtaleLocalHom := by
  subst hψ
  set p := (maximalIdeal B).comap (algebraMap P B)
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap P B y) := by
    intro ⟨y, hy⟩
    by_contra h
    exact hy ((IsLocalRing.mem_maximalIdeal _).2 h)
  let φ : Localization.AtPrime p →+* B :=
    IsLocalization.lift (M := p.primeCompl) (g := algebraMap P B) hunit
  have hφ : φ.comp (algebraMap P _) = algebraMap P B :=
    IsLocalization.lift_comp (M := p.primeCompl) hunit
  have hloc : IsLocalHom φ := by
    refine ⟨fun z hz => ?_⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
    have ha : IsUnit (algebraMap P B a) := by
      have : φ (IsLocalization.mk' (Localization.AtPrime p) a s) * algebraMap P B s =
          algebraMap P B a := by
        rw [← hφ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul,
          IsLocalization.mk'_spec]
      rw [← this]
      exact hz.mul (hunit s)
    have ha' : a ∈ p.primeCompl := fun hmem =>
      ((IsLocalRing.mem_maximalIdeal _).1 hmem) ha
    exact IsUnit.of_mul_eq_one _
      (IsLocalization.mk'_mul_mk'_eq_one (S := Localization.AtPrime p) ⟨a, ha'⟩ s)
  let : Algebra (Localization.AtPrime p) B := φ.toAlgebra
  have : IsScalarTower P (Localization.AtPrime p) B :=
    IsScalarTower.of_algebraMap_eq' hφ.symm
  -- flatness
  have : Module.Flat D B := IsLocalization.flat B M
  have : Module.Flat P B := Module.Flat.trans P D B
  have : Module.Flat (Localization.AtPrime p) B :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl B).2 inferInstance
  -- formal unramifiedness
  have : Algebra.FormallyEtale D B := Algebra.FormallyEtale.of_isLocalization M
  have : Algebra.FormallyEtale P B := Algebra.FormallyEtale.comp P D B
  have : Algebra.FormallyUnramified (Localization.AtPrime p) B :=
    Algebra.FormallyUnramified.localization_base p.primeCompl
  -- essential finite type
  have : Algebra.EssFiniteType D B := Algebra.EssFiniteType.of_isLocalization B M
  have : Algebra.EssFiniteType P B := Algebra.EssFiniteType.comp P D B
  have : Algebra.EssFiniteType (Localization.AtPrime p) B :=
    Algebra.EssFiniteType.of_comp P _ B
  refine ⟨φ, hloc, hφ, ?_, ?_, ?_⟩
  · exact RingHom.flat_algebraMap_iff.2 inferInstance
  · exact RingHom.formallyUnramified_algebraMap.2 inferInstance
  · exact RingHom.essFiniteType_algebraMap.2 inferInstance

/-- **Smooth local homomorphisms are local-étale over a localized polynomial ring.** Let `B` be a
noetherian local ring which is the localization of a smooth `A`-algebra at a prime ideal, `A`
noetherian. There are `r` and `x₁, …, x_r ∈ B` such that, for `ψ : A[T₁, …, T_r] → B`,
`T_ν ↦ x_ν`, and `𝔭 = ψ⁻¹(𝔪_B)`, the homomorphism `A[T₁, …, T_r]_𝔭 → B` induced by `ψ` is a
local-étale homomorphism. -/
@[weil "lem_fk107_smooth_local_etale_over_polynomial"]
theorem IsSmoothLocalization.exists_isEtaleLocalHom_localization_mvPolynomial
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsLocalRing B] [IsNoetherianRing B] (h : IsSmoothLocalization A B) :
    ∃ (r : ℕ) (x : Fin r → B)
      (φ : Localization.AtPrime ((maximalIdeal B).comap (MvPolynomial.aeval (R := A) x)) →+* B)
      (_ : IsLocalHom φ),
      φ.comp (algebraMap _ _) = (MvPolynomial.aeval (R := A) x).toRingHom ∧
        φ.IsEtaleLocalHom := by
  obtain ⟨C, _, _, _, q, _, ⟨e⟩⟩ := h
  obtain ⟨f, hfq, n, _, _, hstd⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := q)
  let P := MvPolynomial (Fin n) A
  let D := Localization.Away f
  have : Algebra.Etale P D := inferInstance
  have hle : Submonoid.powers f ≤ q.primeCompl := Submonoid.powers_le.2 hfq
  let : Algebra D (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f) q.primeCompl hle
  have : IsScalarTower C D (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _
      (Submonoid.powers f) q.primeCompl hle
  have hM : IsLocalization (q.primeCompl.map (algebraMap C D)) (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers f) q.primeCompl hle
  let : Algebra D B := (e.toRingHom.comp (algebraMap D (Localization.AtPrime q))).toAlgebra
  let e' : Localization.AtPrime q ≃ₐ[D] B := { e with commutes' := fun _ => rfl }
  have : IsLocalization (q.primeCompl.map (algebraMap C D)) B :=
    IsLocalization.isLocalization_of_algEquiv _ e'
  let : Algebra P B := ((algebraMap D B).comp (algebraMap P D)).toAlgebra
  have : IsScalarTower P D B := IsScalarTower.of_algebraMap_eq' rfl
  let x : Fin n → B := fun i => algebraMap P B (MvPolynomial.X i)
  have hx : (MvPolynomial.aeval (R := A) x).toRingHom = algebraMap P B := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C,
        ← MvPolynomial.algebraMap_eq]
      change algebraMap A B a = algebraMap D B (algebraMap P D (algebraMap A P a))
      rw [← IsScalarTower.algebraMap_apply A P D, IsScalarTower.algebraMap_apply A C D]
      change algebraMap A B a =
        e (algebraMap D (Localization.AtPrime q) (algebraMap C D (algebraMap A C a)))
      rw [← IsScalarTower.algebraMap_apply C D, ← IsScalarTower.algebraMap_apply A C,
        AlgEquiv.commutes]
    · simp [x]
  exact ⟨n, x, exists_isEtaleLocalHom_lift_of_isLocalization_of_etale (P := P) (D := D)
    (q.primeCompl.map (algebraMap C D)) _ hx⟩

end Algebra
