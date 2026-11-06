module

public import Weil.Attr
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.RingTheory.Smoothing.EssentiallySmooth

/-!
# Smooth local homomorphisms

An `A`-algebra `B` is a *localization of a smooth algebra* if there are a smooth `A`-algebra `C`
and a prime ideal `q` of `C` such that `B ≅ C_q` as `A`-algebras. A local homomorphism
`A → B` of noetherian local rings is *smooth* when `B` is such a localization.

## Main definitions

* `Algebra.IsSmoothLocalization A B`: `B` is isomorphic, as an `A`-algebra, to the localization
  of a smooth `A`-algebra at a prime ideal.
* `RingHom.IsSmoothLocalization f`: the same property for a ring homomorphism `f : A →+* B`,
  through the algebra structure `f.toAlgebra`.

## Main results

* `Algebra.IsSmoothLocalization.of_smooth`: `C_q` is a localization of a smooth algebra.
* `Algebra.IsSmoothLocalization.of_algEquiv`: the property is invariant under `A`-algebra
  isomorphism.
* `Algebra.IsSmoothLocalization.formallySmooth`, `Algebra.IsSmoothLocalization.isLocalRing`:
  such a `B` is formally smooth over `A` and local.
* `Algebra.isSmoothLocalization_iff_exists_isSmoothAt`: it suffices that `C` is of finite
  presentation and smooth at `q` (Stacks Tag 00TB).
* `Algebra.isSmoothLocalization_iff_isEssentiallySmooth`: for a local ring `B` the property is
  `RingHom.IsEssentiallySmooth` (essentially of finite presentation and formally smooth).

## Implementation notes

The definition does not assume `A`, `B` local, noetherian or the homomorphism local: these are
the standing hypotheses under which it is applied (`IsLocalRing`, `IsNoetherianRing`,
`IsLocalHom`), and they are kept as separate instances. A smooth algebra is in particular finitely
presented, hence a quotient of a polynomial ring in finitely many variables over `A`; so the
smooth algebra `C` is taken in the universe of `A` without loss of generality.

Smoothness of an algebra is Mathlib's `Algebra.Smooth` (formally smooth and of finite
presentation), which for finitely generated algebras over a noetherian ring is the flat
algebra with geometrically regular fibres of the source.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
* [Stacks Project, Tag 00TB](https://stacks.math.columbia.edu/tag/00TB)
-/

@[expose] public section

universe u v

namespace Algebra

/-- An `A`-algebra `B` is a *localization of a smooth algebra* if there are a smooth `A`-algebra
`C` and a prime ideal `q ⊂ C` such that `B` is isomorphic to `C_q` as an `A`-algebra. For a local
homomorphism of noetherian local rings this is smoothness of the homomorphism. -/
@[weil "def_fk107_smooth_local_homomorphism"]
def IsSmoothLocalization (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    Prop :=
  ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Smooth A C) (q : Ideal C)
    (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[A] B)

namespace IsSmoothLocalization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The localization of a smooth algebra at a prime ideal is a localization of a smooth
algebra. -/
theorem of_smooth (C : Type u) [CommRing C] [Algebra A C] [Algebra.Smooth A C] (q : Ideal C)
    [q.IsPrime] : IsSmoothLocalization A (Localization.AtPrime q) :=
  ⟨C, inferInstance, inferInstance, inferInstance, q, inferInstance, ⟨AlgEquiv.refl⟩⟩

/-- Being a localization of a smooth algebra is invariant under isomorphism of `A`-algebras. -/
theorem of_algEquiv {B' : Type*} [CommRing B'] [Algebra A B'] (h : IsSmoothLocalization A B)
    (e : B ≃ₐ[A] B') : IsSmoothLocalization A B' := by
  obtain ⟨C, _, _, _, q, _, ⟨f⟩⟩ := h
  exact ⟨C, inferInstance, inferInstance, inferInstance, q, inferInstance, ⟨f.trans e⟩⟩

theorem iff_of_algEquiv {B' : Type*} [CommRing B'] [Algebra A B'] (e : B ≃ₐ[A] B') :
    IsSmoothLocalization A B ↔ IsSmoothLocalization A B' :=
  ⟨fun h => h.of_algEquiv e, fun h => h.of_algEquiv e.symm⟩

/-- A localization of a smooth algebra is formally smooth. -/
theorem formallySmooth (h : IsSmoothLocalization A B) : Algebra.FormallySmooth A B := by
  obtain ⟨C, _, _, _, q, _, ⟨f⟩⟩ := h
  exact Algebra.FormallySmooth.of_equiv f

/-- A localization of a smooth algebra at a prime ideal is a local ring. -/
theorem isLocalRing (h : IsSmoothLocalization A B) : IsLocalRing B := by
  obtain ⟨C, _, _, _, q, _, ⟨f⟩⟩ := h
  have : Nontrivial B := f.symm.surjective.nontrivial
  exact IsLocalRing.of_surjective' (f : Localization.AtPrime q →+* B) f.surjective

end IsSmoothLocalization

/-- `B` is a localization of a smooth `A`-algebra if and only if it is the localization of a
finitely presented `A`-algebra `C` at a prime `q` at which `C` is smooth over `A`. -/
theorem isSmoothLocalization_iff_exists_isSmoothAt {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] :
    IsSmoothLocalization A B ↔
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FinitePresentation A C)
        (q : Ideal C) (_ : q.IsPrime), Algebra.IsSmoothAt A q ∧
          Nonempty (Localization.AtPrime q ≃ₐ[A] B) := by
  constructor
  · rintro ⟨C, _, _, _, q, _, e⟩
    exact ⟨C, inferInstance, inferInstance, inferInstance, q, inferInstance, inferInstance, e⟩
  · rintro ⟨C, _, _, _, q, _, hq, ⟨e⟩⟩
    obtain ⟨g, hgq, hg⟩ := Algebra.IsSmoothAt.exists_notMem_smooth A q
    let C' := Localization.Away g
    have hd : Disjoint (Submonoid.powers g : Set C) q := by
      rw [Set.disjoint_left]
      rintro _ ⟨n, rfl⟩ hn
      exact hgq (‹q.IsPrime›.mem_of_pow_mem n hn)
    let q' : Ideal C' := q.map (algebraMap C C')
    have hq' : q'.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) C' q ‹_› hd
    have hcomap : q'.comap (algebraMap C C') = q :=
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) C' ‹_› hd
    have hloc : IsLocalization.AtPrime (Localization.AtPrime q') q := by
      have := IsLocalization.isLocalization_atPrime_localization_atPrime
        (Submonoid.powers g) q'
      have hM : (q'.comap (algebraMap C C')).primeCompl = q.primeCompl := by
        ext x
        simp [Ideal.primeCompl, hcomap]
      change IsLocalization q.primeCompl _
      rw [← hM]
      exact this
    let f₀ : Localization.AtPrime q ≃ₐ[C] Localization.AtPrime q' :=
      IsLocalization.algEquiv q.primeCompl _ _
    exact ⟨C', inferInstance, inferInstance, hg, q', hq',
      ⟨(f₀.restrictScalars A).symm.trans e⟩⟩

end Algebra

namespace RingHom

/-- A ring homomorphism `f : A →+* B` is a *localization of a smooth algebra* if `B`, as an
`A`-algebra through `f`, is isomorphic to the localization of a smooth `A`-algebra at a prime
ideal. For a local homomorphism of noetherian local rings this is smoothness of `f`. -/
@[weil "def_fk107_smooth_local_homomorphism"]
def IsSmoothLocalization {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    Prop :=
  letI := f.toAlgebra
  Algebra.IsSmoothLocalization A B

theorem isSmoothLocalization_algebraMap_iff {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] :
    (algebraMap A B).IsSmoothLocalization ↔ Algebra.IsSmoothLocalization A B := by
  rw [IsSmoothLocalization, toAlgebra_algebraMap]

end RingHom

namespace Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A localization of a smooth algebra is essentially smooth. -/
theorem IsSmoothLocalization.isEssentiallySmooth (h : IsSmoothLocalization A B) :
    (algebraMap A B).IsEssentiallySmooth := by
  obtain ⟨C, _, _, _, q, _, ⟨e⟩⟩ := h
  have h₀ : (algebraMap A (Localization.AtPrime q)).IsEssentiallySmooth := by
    refine ⟨IsEssentiallyOfFinitePresentation.of_isLocalization (C := C) q.primeCompl, ?_⟩
    rw [toAlgebra_algebraMap]
    infer_instance
  have h₁ := h₀.comp_ringEquiv e.toRingEquiv
  have heq : ((e.toRingEquiv : Localization.AtPrime q →+* B).comp
      (algebraMap A (Localization.AtPrime q))) = algebraMap A B := by
    ext a
    exact e.commutes a
  rwa [heq] at h₁

/-- A local `A`-algebra is a localization of a smooth `A`-algebra if and only if it is
essentially smooth over `A`. -/
theorem isSmoothLocalization_iff_isEssentiallySmooth [IsLocalRing B] :
    IsSmoothLocalization A B ↔ (algebraMap A B).IsEssentiallySmooth := by
  refine ⟨IsSmoothLocalization.isEssentiallySmooth, fun ⟨hefp, hfs⟩ => ?_⟩
  unfold IsEssentiallyOfFinitePresentation at hefp
  rw [toAlgebra_algebraMap] at hefp hfs
  obtain ⟨T, _, _, _, M, _, _, hM⟩ := hefp
  -- `B` is its own localization at its maximal ideal, hence `T_q` for `q` the preimage.
  have hself : IsLocalization.AtPrime B (IsLocalRing.maximalIdeal B) :=
    IsLocalization.self fun x hx => (IsUnit.mem_submonoid_iff x).mpr <| by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
  let q : Ideal T := (IsLocalRing.maximalIdeal B).comap (algebraMap T B)
  have hT : IsLocalization.AtPrime B q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M B
      (IsLocalRing.maximalIdeal B)
  let e : Localization.AtPrime q ≃ₐ[T] B := IsLocalization.algEquiv q.primeCompl _ _
  have : Algebra.IsSmoothAt A q := Algebra.FormallySmooth.of_equiv (e.restrictScalars A).symm
  exact isSmoothLocalization_iff_exists_isSmoothAt.mpr
    ⟨T, inferInstance, inferInstance, inferInstance, q, inferInstance, this,
      ⟨e.restrictScalars A⟩⟩

end Algebra
