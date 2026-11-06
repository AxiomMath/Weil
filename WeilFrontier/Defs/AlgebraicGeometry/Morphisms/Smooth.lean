module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Analysis.Complex.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import Weil.Attr
public import WeilFrontier.Definitions

/-!
# Schemes arising by good reduction

Let `κ` be a field, `S₀` a scheme over `κ` and `Y` a scheme over `ℂ`. The scheme `S₀` *arises by
good reduction of `Y`* if both are fibres of one smooth projective family over a finitely
generated base: there are an integral domain `R` of finite type over `ℤ`, a smooth projective
morphism `f : X ⟶ Spec R`, ring homomorphisms `φ : R →+* ℂ` and `ψ : R →+* κ`, an isomorphism of
`ℂ`-schemes `X ×_{Spec R} Spec ℂ ≅ Y` and an isomorphism of `κ`-schemes
`X ×_{Spec R} Spec κ ≅ S₀`.

## Main definitions

`AlgebraicGeometry.Scheme.ArisesByGoodReduction`, the scheme `S₀` over `κ` arising by good
reduction of the scheme `Y` over `ℂ`, is defined in `WeilFrontier.Definitions`, which collects the
definitions entering the statements of the Weil conjectures.

## Main results

* `AlgebraicGeometry.Scheme.ArisesByGoodReduction.intro`: a smooth projective family over
  `Spec R` whose fibres over `ℂ` and over `κ` are `Y` and `S₀` exhibits `S₀` as arising by good
  reduction of `Y`.
* `AlgebraicGeometry.Scheme.ArisesByGoodReduction.of_iso_left`,
  `AlgebraicGeometry.Scheme.ArisesByGoodReduction.of_iso_right`: the notion only depends on the
  isomorphism classes of `S₀` over `κ` and of `Y` over `ℂ`.

## Implementation notes

In the source, `κ` is a finite field and `S₀` and `Y` are smooth and projective over `κ` and `ℂ`.
None of these hypotheses enters the definition, so it is stated for an arbitrary field `κ` and
arbitrary schemes over `κ` and over `ℂ`; when `S₀` arises by good reduction of `Y`, both are base
changes of the smooth projective morphism `f`. Projectivity is the first condition of Stacks
Tag 01W8, `AlgebraicGeometry.IsProjective`. Isomorphisms over the bases are isomorphisms of
schemes commuting with the structure morphisms. All schemes live in `Type`, which contains every
ring of finite type over `ℤ` up to isomorphism.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, 1.2,
  Remark b), p. 257.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

namespace ArisesByGoodReduction

variable {κ : Type} [Field κ] {S₀ : Scheme.{0}} {s₀ : S₀ ⟶ Spec (.of κ)}
  {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

/-- A smooth projective morphism `f : X ⟶ Spec R`, with `R` an integral domain of finite type
over `ℤ`, whose base changes along `Spec ℂ ⟶ Spec R` and `Spec κ ⟶ Spec R` are `Y` over `ℂ` and
`S₀` over `κ`, exhibits `S₀` as arising by good reduction of `Y`. -/
theorem intro {R : Type} [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of R)) [Smooth f] (hf : IsProjective f) (φ : R →+* ℂ) (ψ : R →+* κ)
    (eY : pullback f (Spec.map (CommRingCat.ofHom φ)) ≅ Y) (heY : eY.hom ≫ y = pullback.snd _ _)
    (eS : pullback f (Spec.map (CommRingCat.ofHom ψ)) ≅ S₀) (heS : eS.hom ≫ s₀ = pullback.snd _ _) :
    ArisesByGoodReduction s₀ y :=
  ⟨R, inferInstance, inferInstance, inferInstance, X, f, inferInstance, hf, φ, ψ,
    ⟨eY, heY⟩, ⟨eS, heS⟩⟩

/-- Arising by good reduction only depends on the isomorphism class of `S₀` over `κ`. -/
theorem of_iso_left (h : ArisesByGoodReduction s₀ y) {S₁ : Scheme.{0}}
    {s₁ : S₁ ⟶ Spec (.of κ)} (e : S₀ ≅ S₁) (he : e.hom ≫ s₁ = s₀) :
    ArisesByGoodReduction s₁ y := by
  obtain ⟨R, _, _, _, X, f, _, hf, φ, ψ, hY, eS, heS⟩ := h
  refine ⟨R, inferInstance, inferInstance, inferInstance, X, f, inferInstance, hf, φ, ψ, hY,
    eS ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Category.assoc, he, heS]

/-- Arising by good reduction only depends on the isomorphism class of `Y` over `ℂ`. -/
theorem of_iso_right (h : ArisesByGoodReduction s₀ y) {Y₁ : Scheme.{0}}
    {y₁ : Y₁ ⟶ Spec (.of ℂ)} (e : Y ≅ Y₁) (he : e.hom ≫ y₁ = y) :
    ArisesByGoodReduction s₀ y₁ := by
  obtain ⟨R, _, _, _, X, f, _, hf, φ, ψ, ⟨eY, heY⟩, hS⟩ := h
  refine ⟨R, inferInstance, inferInstance, inferInstance, X, f, inferInstance, hf, φ, ψ,
    ⟨eY ≪≫ e, ?_⟩, hS⟩
  rw [Iso.trans_hom, Category.assoc, he, heY]

end ArisesByGoodReduction

end AlgebraicGeometry.Scheme

end
