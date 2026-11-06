/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Purely inseparable morphisms and geometric points

Let `f : X ⟶ Y` be a finite morphism of schemes. Then `f` is purely inseparable (finite,
universally injective and surjective) if and only if for every algebraically closed field `k`,
every geometric point `y : Spec k ⟶ Y` lifts to exactly one geometric point `x : Spec k ⟶ X`
with `x ≫ f = y`.

Uniqueness of lifts for all algebraically closed fields is equivalent to universal injectivity:
a `K`-point for an arbitrary field `K` is determined by its composite with
`Spec K̄ ⟶ Spec K` for an algebraic closure `K̄` of `K`, and universal injectivity is injectivity
on `K`-points for all fields `K` (`AlgebraicGeometry.tfae_universallyInjective`). Existence of
lifts is equivalent to surjectivity: a point of `X` over the image of `y` gives a closed point of
the finite `k`-scheme `X ×_Y Spec k`, which is a `k`-rational point since `k` is algebraically
closed.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_isFinite`: through a finite morphism, a
  geometric point `y` lifts through any point of the fibre over the image of `y`.
* `AlgebraicGeometry.Scheme.Hom.cancel_SpecMap_left`: morphisms from the spectrum of a field
  are determined by their composite with `Spec L ⟶ Spec K` for any field extension `L/K`.
* `AlgebraicGeometry.Scheme.Hom.isPurelyInseparable_iff_existsUnique_comp_eq`: a finite
  morphism is purely inseparable iff every geometric point of the target has exactly one lift.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §3.
* [Stacks, Tag 01S4]
-/

/- A geometric point `Spec k ⟶ Y` with
values in an algebraically closed field `k` is stated as a morphism, so that "a geometric point
`x : Spec k ⟶ X` with the same field `k`" is literal. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Through a finite morphism `f : X ⟶ Y`, a geometric point `y : Spec k ⟶ Y` lifts through
every point `x₀` of `X` lying over the image of `y`. -/
theorem exists_comp_eq_of_isFinite [IsFinite f] {k : Type u} [Field k] [IsAlgClosed k]
    (y : Spec (.of k) ⟶ Y) (a : Spec (.of k)) (x₀ : X) (hx₀ : f x₀ = y a) :
    ∃ x : Spec (.of k) ⟶ X, x ≫ f = y ∧ x a = x₀ := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := y) x₀ a hx₀
  have : IsLocallyArtinian (pullback f y) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd f y)
  let p := pointOfClosedPoint (pullback.snd f y) z isClosed_singleton
  refine ⟨p ≫ pullback.fst f y, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
      Category.id_comp]
  · rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply, hz]

/-- Morphisms from the spectrum of a field `K` to a scheme are determined by their composites
with `Spec L ⟶ Spec K`, for any field extension `ι : K →+* L`. -/
theorem cancel_SpecMap_left {K L : Type u} [Field K] [Field L] (ι : K →+* L)
    {g₁ g₂ : Spec (.of K) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom ι) ≫ g₁ = Spec.map (CommRingCat.ofHom ι) ≫ g₂) :
    g₁ = g₂ := by
  rw [← (X.SpecToEquivOfField K).symm_apply_apply g₁,
    ← (X.SpecToEquivOfField K).symm_apply_apply g₂] at h ⊢
  generalize X.SpecToEquivOfField K g₁ = p₁ at h ⊢
  generalize X.SpecToEquivOfField K g₂ = p₂ at h ⊢
  have key : ∀ p : Σ x : X, X.residueField x ⟶ .of K,
      Spec.map (CommRingCat.ofHom ι) ≫ (X.SpecToEquivOfField K).symm p =
        (X.SpecToEquivOfField L).symm ⟨p.1, p.2 ≫ CommRingCat.ofHom ι⟩ := by
    intro p
    simp [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp]
  rw [key, key] at h
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp ((X.SpecToEquivOfField L).symm.injective h)
  congr 1
  refine Scheme.SpecToEquivOfField_eq_iff.mpr ⟨e, ?_⟩
  ext a
  apply ι.injective
  exact congr($(he).hom a)

/-- **Purely inseparable morphisms via geometric points.** A finite morphism `f : X ⟶ Y` is
purely inseparable if and only if for every algebraically closed field `k`, every geometric
point `y : Spec k ⟶ Y` has exactly one lift `x : Spec k ⟶ X` with `x ≫ f = y`. -/
@[weil "lem_fk103_purely_inseparable_iff_unique_geometric_point"]
theorem isPurelyInseparable_iff_existsUnique_comp_eq [IsFinite f] :
    f.IsPurelyInseparable ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (y : Spec (.of k) ⟶ Y), ∃! x : Spec (.of k) ⟶ X, x ≫ f = y := by
  have h := (tfae_universallyInjective f).out 1 2
  constructor
  · rintro ⟨-, hinj, hsurj⟩ k _ _ y
    obtain ⟨a⟩ : Nonempty (Spec (.of k)) := inferInstance
    obtain ⟨x₀, hx₀⟩ := hsurj.surj (y a)
    obtain ⟨x, hx, -⟩ := exists_comp_eq_of_isFinite f y a x₀ hx₀
    exact ⟨x, hx, fun x' hx' ↦ h.mp hinj k (hx'.trans hx.symm)⟩
  · intro H
    refine ⟨inferInstance, h.mpr fun K _ g₁ g₂ hg ↦ ?_, ⟨fun y ↦ ?_⟩⟩
    · let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
      apply cancel_SpecMap_left ι
      obtain ⟨x, -, hx⟩ := H (AlgebraicClosure K) (Spec.map (CommRingCat.ofHom ι) ≫ g₁ ≫ f)
      refine (hx _ (Category.assoc _ _ _)).trans (hx _ ?_).symm
      simp only [Category.assoc]
      exact congrArg (Spec.map (CommRingCat.ofHom ι) ≫ ·) hg.symm
    · let k := AlgebraicClosure (Y.residueField y)
      let ι : Y.residueField y ⟶ CommRingCat.of k :=
        CommRingCat.ofHom (algebraMap (Y.residueField y) k)
      obtain ⟨x, hx, -⟩ := H k (Spec.map ι ≫ Y.fromSpecResidueField y)
      obtain ⟨a⟩ : Nonempty (Spec (.of k)) := inferInstance
      refine ⟨x a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hx, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

end AlgebraicGeometry.Scheme.Hom
