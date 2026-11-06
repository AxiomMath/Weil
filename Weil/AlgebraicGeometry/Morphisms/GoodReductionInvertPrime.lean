module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import Weil.Defs.AlgebraicGeometry.Morphisms.Smooth
public import Weil.Attr

/-!
# Good reduction over a base on which a given integer is invertible

Let `S₀` over a field `κ` arise by good reduction of `Y` over `ℂ`, through a smooth projective
family `f : X ⟶ Spec R` and ring homomorphisms `φ : R →+* ℂ`, `ψ : R →+* κ`. If an element
`r ∈ R` is nonzero and becomes invertible in `ℂ` and in `κ`, then both `φ` and `ψ` factor through
the localization `R[1/r]`, which is again an integral domain of finite type over `ℤ`, and the base
change `X ×_{Spec R} Spec R[1/r] ⟶ Spec R[1/r]` is again smooth and projective with the same two
fibres. Applied to `r = ℓ` with `ℓ` invertible in `κ`, this shows that the family can be chosen
over a base on which `ℓ` is invertible.

## Main results

* `AlgebraicGeometry.Scheme.ArisesByGoodReduction.intro_away`: the family localized at an element
  `r` invertible in `ℂ` and in `κ` still exhibits good reduction, with `r` a unit of the new base.
* `AlgebraicGeometry.Scheme.ArisesByGoodReduction.exists_isUnit`: if `S₀` arises by good
  reduction of `Y` and `ℓ` is a natural number invertible in `κ`, then the data in the definition
  of good reduction can be chosen with `ℓ` a unit of the base ring.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, 1.2,
  Remark b), p. 257, and the proof of Lemma IV.1.7.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.ArisesByGoodReduction

variable {κ : Type} [Field κ] {S₀ : Scheme.{0}} {s₀ : S₀ ⟶ Spec (.of κ)}
  {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

/-- A localization `A = R[1/r]` of a ring `R` of finite type over `ℤ` is of finite type over `ℤ`.
-/
theorem _root_.IsLocalization.Away.finiteType_int {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType ℤ R] (r : R) [IsLocalization.Away r A] :
    Algebra.FiniteType ℤ A :=
  have : Algebra.FinitePresentation R A := IsLocalization.Away.finitePresentation r
  .trans (S := R) ‹_› inferInstance

/-- Base change of a fibre: if `φ = φ' ∘ ι`, the fibre over `φ'` of the base change of `f` along
`Spec ι` is the fibre over `φ` of `f`, compatibly with the projections to `Spec` of the target. -/
theorem exists_pullback_baseChange_iso {R R' K : Type} [CommRing R] [CommRing R'] [CommRing K]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) (ι : R →+* R') (φ' : R' →+* K) :
    ∃ e : pullback (pullback.snd f (Spec.map (CommRingCat.ofHom ι)))
        (Spec.map (CommRingCat.ofHom φ')) ≅ pullback f (Spec.map (CommRingCat.ofHom (φ'.comp ι))),
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  have hcomp : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom ι) =
      Spec.map (CommRingCat.ofHom (φ'.comp ι)) := by
    rw [← Spec.map_comp]; rfl
  refine ⟨pullbackLeftPullbackSndIso f _ _ ≪≫ pullback.congrHom rfl hcomp, ?_⟩
  rw [Iso.trans_hom, Category.assoc, pullback.congrHom_hom]
  erw [pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- **Localizing a good-reduction family.** Let `f : X ⟶ Spec R` be a smooth projective family
over an integral domain `R` of finite type over `ℤ`, with fibres `Y` over `φ : R →+* ℂ` and `S₀`
over `ψ : R →+* κ`. If `r ∈ R` is nonzero and `φ r`, `ψ r` are units, then the base change of
`f` to `Spec R[1/r]` is smooth and projective, and its fibres over the factorizations of `φ` and
`ψ` through `R[1/r]` are `Y` and `S₀`. -/
theorem intro_away {R : Type} [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) [Smooth f] (hf : IsProjective f)
    (φ : R →+* ℂ) (ψ : R →+* κ)
    (eY : pullback f (Spec.map (CommRingCat.ofHom φ)) ≅ Y) (heY : eY.hom ≫ y = pullback.snd _ _)
    (eS : pullback f (Spec.map (CommRingCat.ofHom ψ)) ≅ S₀) (heS : eS.hom ≫ s₀ = pullback.snd _ _)
    (r : R) (hr : r ≠ 0) (hφr : IsUnit (φ r)) (hψr : IsUnit (ψ r)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : Algebra.FiniteType ℤ R')
      (ι : R →+* R'), IsUnit (ι r) ∧
      ∃ (X' : Scheme.{0}) (f' : X' ⟶ Spec (.of R')) (_ : Smooth f') (_ : IsProjective f')
        (φ' : R' →+* ℂ) (ψ' : R' →+* κ), φ'.comp ι = φ ∧ ψ'.comp ι = ψ ∧
        (∃ e : pullback f' (Spec.map (CommRingCat.ofHom φ')) ≅ Y, e.hom ≫ y = pullback.snd _ _) ∧
        (∃ e : pullback f' (Spec.map (CommRingCat.ofHom ψ')) ≅ S₀,
          e.hom ≫ s₀ = pullback.snd _ _) := by
  let R' := Localization.Away r
  have : IsDomain R' := Localization.Away.isDomain hr
  let ι : R →+* R' := algebraMap R R'
  let φ' : R' →+* ℂ := IsLocalization.Away.lift r hφr
  let ψ' : R' →+* κ := IsLocalization.Away.lift r hψr
  have hφ : φ'.comp ι = φ := IsLocalization.Away.lift_comp r hφr
  have hψ : ψ'.comp ι = ψ := IsLocalization.Away.lift_comp r hψr
  let f' := pullback.snd f (Spec.map (CommRingCat.ofHom ι))
  have hf' : IsProjective f' :=
    IsProjective.of_isPullback (IsPullback.of_hasPullback f _).flip hf
  obtain ⟨eY', heY'⟩ := exists_pullback_baseChange_iso f ι φ'
  obtain ⟨eS', heS'⟩ := exists_pullback_baseChange_iso f ι ψ'
  refine ⟨R', inferInstance, inferInstance,
    IsLocalization.Away.finiteType_int (A := Localization.Away r) r, ι,
    IsLocalization.Away.algebraMap_isUnit r, _, f', inferInstance, hf', φ', ψ', hφ, hψ,
    ⟨eY' ≪≫ pullback.congrHom rfl (by rw [hφ]) ≪≫ eY, ?_⟩,
    ⟨eS' ≪≫ pullback.congrHom rfl (by rw [hψ]) ≪≫ eS, ?_⟩⟩
  · simp only [Iso.trans_hom, Category.assoc, heY, pullback.congrHom_hom, pullback.lift_snd,
      Category.comp_id]
    exact heY'
  · simp only [Iso.trans_hom, Category.assoc, heS, pullback.congrHom_hom, pullback.lift_snd,
      Category.comp_id]
    exact heS'

/-- **Good reduction over a base on which `ℓ` is invertible.** If `S₀` over `κ` arises by good
reduction of `Y` over `ℂ` and the natural number `ℓ` is nonzero in `κ` (for instance a prime
different from the characteristic of `κ`), then the data in the definition of good reduction can
be chosen so that `ℓ` is a unit of the base ring `R`. -/
theorem exists_isUnit (h : ArisesByGoodReduction s₀ y) (ℓ : ℕ) (hℓ : (ℓ : κ) ≠ 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra.FiniteType ℤ R),
      IsUnit (ℓ : R) ∧
      ∃ (X : Scheme.{0}) (f : X ⟶ Spec (.of R)) (_ : Smooth f) (_ : IsProjective f)
        (φ : R →+* ℂ) (ψ : R →+* κ),
        (∃ e : pullback f (Spec.map (CommRingCat.ofHom φ)) ≅ Y, e.hom ≫ y = pullback.snd _ _) ∧
        (∃ e : pullback f (Spec.map (CommRingCat.ofHom ψ)) ≅ S₀,
          e.hom ≫ s₀ = pullback.snd _ _) := by
  obtain ⟨R, _, _, _, X, f, _, hf, φ, ψ, ⟨eY, heY⟩, ⟨eS, heS⟩⟩ := h
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; exact hℓ Nat.cast_zero
  have hr : (ℓ : R) ≠ 0 := fun h0 => hℓ (by simpa using congrArg ψ h0)
  have hφr : IsUnit (φ ℓ) := by
    rw [map_natCast]; exact (Nat.cast_ne_zero.mpr hℓ0).isUnit
  have hψr : IsUnit (ψ ℓ) := by
    rw [map_natCast]; exact hℓ.isUnit
  obtain ⟨R', _, _, _, ι, hι, X', f', _, hf', φ', ψ', -, -, hY, hS⟩ :=
    intro_away f hf φ ψ eY heY eS heS (ℓ : R) hr hφr hψr
  exact ⟨R', inferInstance, inferInstance, inferInstance, by simpa using hι, X', f',
    inferInstance, hf', φ', ψ', hY, hS⟩

end AlgebraicGeometry.Scheme.ArisesByGoodReduction

end
