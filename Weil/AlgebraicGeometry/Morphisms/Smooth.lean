module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The spectrum of a smooth algebra is smooth

If `C` is a smooth `A`-algebra, then the induced morphism of affine schemes
`Spec C ⟶ Spec A` is smooth.

## Main results

* `AlgebraicGeometry.smooth_spec_map_algebraMap`: for `[Algebra.Smooth A C]`, the morphism
  `Spec.map (CommRingCat.ofHom (algebraMap A C))` is `AlgebraicGeometry.Smooth`.

## Implementation notes

Smooth algebras are Mathlib's `Algebra.Smooth` (formally smooth and of finite presentation)
and smooth morphisms are Mathlib's `AlgebraicGeometry.Smooth`, which is defined
affine-locally by `RingHom.Smooth`. The result is then `HasRingHomProperty.Spec_iff`
together with `RingHom.smooth_algebraMap`; no noetherian hypothesis is needed.

## References

* [FK88] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- If `C` is a smooth `A`-algebra, then `Spec C ⟶ Spec A` is a smooth morphism. -/
@[weil "lem_fk107_spec_smooth_algebra_is_smooth"]
theorem smooth_spec_map_algebraMap (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Smooth A C] : Smooth (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
  HasRingHomProperty.Spec_iff.mpr ((RingHom.smooth_algebraMap).mpr ‹_›)

end AlgebraicGeometry

end

/-! ### Smooth morphisms via their local homomorphisms -/

/-!
# Smooth morphisms via their local homomorphisms

A morphism `f : X ⟶ Y` of schemes is smooth (`AlgebraicGeometry.Smooth`) when it is locally of
finite presentation and, locally on source and target, given by smooth ring maps. Over a
locally noetherian base this is the same as asking that `f` be locally of finite type and that,
for every point `x` of `X`, the local homomorphism `𝒪_{Y, f x} → 𝒪_{X, x}` be the localization
at a prime of a smooth `𝒪_{Y, f x}`-algebra: there are a smooth `𝒪_{Y, f x}`-algebra `C` and a
prime `𝔮` of `C` such that `𝒪_{X, x} ≅ C_𝔮` as `𝒪_{Y, f x}`-algebras.

## Main results

* `AlgebraicGeometry.exists_smooth_localization_localRingHom`: for a smooth ring map `R → A`
  and a prime `𝔮` of `A` over `𝔭`, the local homomorphism `R_𝔭 → A_𝔮` is the localization at a
  prime of a smooth `R_𝔭`-algebra.
* `AlgebraicGeometry.formallySmooth_of_exists_smooth_localization`: a ring map which is the
  localization at a prime of a smooth algebra is formally smooth.
* `AlgebraicGeometry.smooth_iff_locallyOfFinitePresentation_and_stalkMap`: a morphism is smooth
  if and only if it is locally of finite presentation and every stalk map is the localization at
  a prime of a smooth algebra.
* `AlgebraicGeometry.smooth_iff_locallyOfFiniteType_and_stalkMap`: over a locally noetherian
  base, a morphism is smooth if and only if it is locally of finite type and every stalk map is
  the localization at a prime of a smooth algebra.

## Implementation notes

The condition on a ring homomorphism `φ : A →+* B` is written out: there are a ring `C`, a
smooth ring map `g : A →+* C`, a prime `𝔮` of `C` and a ring isomorphism
`e : C_𝔮 ≃+* B` with `e ∘ (C → C_𝔮) ∘ g = φ`, which is `B ≅ C_𝔮` as `A`-algebras.

The noetherian hypothesis is needed only on the base, where it makes "locally of finite type"
equivalent to "locally of finite presentation"; the source is arbitrary.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
* [Stacks Project, Tag 01V4](https://stacks.math.columbia.edu/tag/01V4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The condition "localization at a prime of a smooth algebra" travels along isomorphisms of
source and target. -/
theorem exists_smooth_localization_comp_ringEquiv {A A' B B' : Type u} [CommRing A]
    [CommRing A'] [CommRing B] [CommRing B'] {φ : A →+* B}
    (h : ∃ (C : Type u) (_ : CommRing C) (g : A →+* C) (_ : g.Smooth) (q : Ideal C)
      (_ : q.IsPrime) (e : Localization.AtPrime q ≃+* B),
      (e : Localization.AtPrime q →+* B).comp ((algebraMap C _).comp g) = φ)
    (eA : A' ≃+* A) (eB : B ≃+* B') :
    ∃ (C : Type u) (_ : CommRing C) (g : A' →+* C) (_ : g.Smooth) (q : Ideal C)
      (_ : q.IsPrime) (e : Localization.AtPrime q ≃+* B'),
      (e : Localization.AtPrime q →+* B').comp ((algebraMap C _).comp g) =
        (eB : B →+* B').comp (φ.comp (eA : A' →+* A)) := by
  obtain ⟨C, _, g, hg, q, _, e, he⟩ := h
  refine ⟨C, inferInstance, g.comp (eA : A' →+* A),
    (RingHom.Smooth.of_bijective eA.bijective).comp hg, q, inferInstance, e.trans eB, ?_⟩
  rw [← he]
  rfl

/-- A ring homomorphism which is the localization at a prime of a smooth algebra is formally
smooth. -/
theorem formallySmooth_of_exists_smooth_localization {A B : Type u} [CommRing A] [CommRing B]
    {φ : A →+* B}
    (h : ∃ (C : Type u) (_ : CommRing C) (g : A →+* C) (_ : g.Smooth) (q : Ideal C)
      (_ : q.IsPrime) (e : Localization.AtPrime q ≃+* B),
      (e : Localization.AtPrime q →+* B).comp ((algebraMap C _).comp g) = φ) :
    φ.FormallySmooth := by
  obtain ⟨C, _, g, hg, q, _, e, rfl⟩ := h
  refine RingHom.FormallySmooth.comp (RingHom.FormallySmooth.comp hg.formallySmooth ?_)
    (RingHom.FormallySmooth.of_bijective e.bijective)
  rw [RingHom.formallySmooth_algebraMap]
  exact Algebra.FormallySmooth.of_isLocalization q.primeCompl

/-- For a smooth ring map `R → A` and a prime `𝔮` of `A` lying over `𝔭`, the local homomorphism
`R_𝔭 → A_𝔮` is the localization at a prime of the smooth `R_𝔭`-algebra `A_𝔭`. -/
theorem exists_smooth_localization_localRingHom {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (hφ : φ.Smooth) (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime]
    (hpq : p = q.comap φ) :
    ∃ (C : Type u) (_ : CommRing C) (g : Localization.AtPrime p →+* C) (_ : g.Smooth)
      (Q : Ideal C) (_ : Q.IsPrime) (e : Localization.AtPrime Q ≃+* Localization.AtPrime q),
      (e : Localization.AtPrime Q →+* _).comp ((algebraMap C _).comp g) =
        Localization.localRingHom p q φ hpq := by
  algebraize [φ]
  let M : Submonoid A := Algebra.algebraMapSubmonoid A p.primeCompl
  let Ap := Localization M
  have hpush : Algebra.IsPushout R A (Localization.AtPrime p) Ap :=
    Algebra.isPushout_of_isLocalization p.primeCompl (Localization.AtPrime p) A Ap
  have hsm : (algebraMap (Localization.AtPrime p) Ap).Smooth :=
    RingHom.Smooth.isStableUnderBaseChange R A (Localization.AtPrime p) Ap
      (by rwa [RingHom.algebraMap_toAlgebra])
  have hdisj : Disjoint (M : Set A) (q : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsq
    exact hs (by rw [hpq]; exact hsq)
  let Q : Ideal Ap := q.map (algebraMap A Ap)
  have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M Ap q inferInstance hdisj
  have hQq : Q.comap (algebraMap A Ap) = q :=
    IsLocalization.under_map_of_isPrime_disjoint M Ap inferInstance hdisj
  have hloc : IsLocalization.AtPrime (Localization.AtPrime Q) q := by
    have := IsLocalization.isLocalization_atPrime_localization_atPrime M Q
    convert this
    exact hQq.symm
  let e : Localization.AtPrime Q ≃ₐ[A] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl _ _
  refine ⟨Ap, inferInstance, algebraMap _ Ap, hsm, Q, hQ, e.toRingEquiv, ?_⟩
  refine (Localization.localRingHom_unique p q φ hpq fun r => ?_).symm
  change e (algebraMap Ap (Localization.AtPrime Q)
    (algebraMap (Localization.AtPrime p) Ap (algebraMap R _ r))) = _
  rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) Ap,
    IsScalarTower.algebraMap_apply R A Ap, ← IsScalarTower.algebraMap_apply A Ap,
    AlgEquiv.commutes, RingHom.algebraMap_toAlgebra]

/-- Every stalk map of a smooth morphism is the localization at a prime of a smooth algebra:
for `x : X` there are a smooth `𝒪_{Y, f x}`-algebra `C` and a prime `𝔮` of `C` with
`𝒪_{X, x} ≅ C_𝔮` as `𝒪_{Y, f x}`-algebras. -/
theorem Smooth.exists_smooth_localization_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) :
    ∃ (C : Type u) (_ : CommRing C) (g : Y.presheaf.stalk (f x) →+* C) (_ : g.Smooth)
      (q : Ideal C) (_ : q.IsPrime) (e : Localization.AtPrime q ≃+* X.presheaf.stalk x),
      (e : Localization.AtPrime q →+* _).comp ((algebraMap C _).comp g) =
        (f.stalkMap x).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have hsm : (f.appLE U V hVU).hom.Smooth := f.smooth_appLE hU hV hVU
  let i := IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hxV
  have key := Arrow.iso_w' i.symm
  have h := exists_smooth_localization_comp_ringEquiv
    (exists_smooth_localization_localRingHom _ hsm _ _
      congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1).symm)
    (Arrow.leftFunc.mapIso i).commRingCatIsoToRingEquiv
    (Arrow.rightFunc.mapIso i).symm.commRingCatIsoToRingEquiv
  obtain ⟨C, _, g, hg, q, _, e, he⟩ := h
  refine ⟨C, inferInstance, g, hg, q, inferInstance, e, he.trans ?_⟩
  refine Eq.trans ?_ (congrArg CommRingCat.Hom.hom key).symm
  rfl

/-- A morphism of schemes is smooth if and only if it is locally of finite presentation and, for
every point `x`, the local homomorphism `𝒪_{Y, f x} → 𝒪_{X, x}` is the localization at a prime
of a smooth algebra. -/
theorem smooth_iff_locallyOfFinitePresentation_and_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Smooth f ↔ LocallyOfFinitePresentation f ∧ ∀ x : X,
      ∃ (C : Type u) (_ : CommRing C) (g : Y.presheaf.stalk (f x) →+* C) (_ : g.Smooth)
        (q : Ideal C) (_ : q.IsPrime) (e : Localization.AtPrime q ≃+* X.presheaf.stalk x),
        (e : Localization.AtPrime q →+* _).comp ((algebraMap C _).comp g) =
          (f.stalkMap x).hom := by
  refine ⟨fun _ => ⟨inferInstance, Smooth.exists_smooth_localization_stalkMap f⟩, ?_⟩
  rintro ⟨_, h⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
  intro x _
  exact Scheme.Hom.mem_smoothLocus.mpr (formallySmooth_of_exists_smooth_localization (h x))

/-- **Smooth morphisms over a locally noetherian base.** A morphism `f : X ⟶ Y` with `Y` locally
noetherian is smooth if and only if it is locally of finite type and every point of `X` is
smooth over `Y`: for every `x : X` there are a smooth `𝒪_{Y, f x}`-algebra `C` and a prime `𝔮`
of `C` such that `𝒪_{X, x} ≅ C_𝔮` as `𝒪_{Y, f x}`-algebras. -/
@[weil "def_fk107_smooth_morphism"]
theorem smooth_iff_locallyOfFiniteType_and_stalkMap {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) :
    Smooth f ↔ LocallyOfFiniteType f ∧ ∀ x : X,
      ∃ (C : Type u) (_ : CommRing C) (g : Y.presheaf.stalk (f x) →+* C) (_ : g.Smooth)
        (q : Ideal C) (_ : q.IsPrime) (e : Localization.AtPrime q ≃+* X.presheaf.stalk x),
        (e : Localization.AtPrime q →+* _).comp ((algebraMap C _).comp g) =
          (f.stalkMap x).hom := by
  rw [smooth_iff_locallyOfFinitePresentation_and_stalkMap,
    LocallyOfFinitePresentation.iff_locallyOfFiniteType]

end AlgebraicGeometry
