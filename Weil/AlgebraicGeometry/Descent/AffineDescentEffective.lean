module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityLargeIndex
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc
public import Weil.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import Weil.Attr

/-!
# Effective descent for affine morphisms along a faithfully flat quasi-compact morphism

Let `f : T ⟶ S` be a faithfully flat (flat and surjective) quasi-compact morphism of schemes and
let `(Y, σ)` be a descent datum relative to `f` whose structure morphism `Y ⟶ T` is affine.
Then `(Y, σ)` is effective: there are an `S`-scheme `X` and an isomorphism `λ : X_T ≅ Y` of
`T`-schemes with `σ ∘ p₁^* λ = p₂^* λ ∘ σ_X`, where `σ_X` is the natural descent datum of
`X_T = X ×_S T`.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_faithfullyFlat` : a descent datum
  relative to a surjective flat quasi-compact morphism, with affine structure morphism, is
  effective.
* `AlgebraicGeometry.DescentDatum.exists_baseChangeTransition_of_isAffineHom` : the same, in the
  base-change form `σ ∘ p₁^* λ = p₂^* λ ∘ σ_X`.

## Implementation notes

The single morphism `f` is the one-member fpqc covering family `{f}`, and the result is the
case of that family of effective descent for affine morphisms along an fpqc covering
(`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex`), whose proof
descends the quasi-coherent algebra `g_* 𝒪_Y` and takes its relative spectrum.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace DescentDatum

variable {T S : Scheme.{u}} {f : T ⟶ S} [Surjective f] [Flat f] [QuasiCompact f]

/-- **Affine descent data are effective.** A descent datum relative to a surjective flat
quasi-compact morphism `f : T ⟶ S` whose structure morphism `Y ⟶ T` is affine is effective. -/
theorem isEffective_of_isAffineHom_of_faithfullyFlat (D : DescentDatum f)
    (hD : IsAffineHom D.over.hom) : DescentData.IsEffective D :=
  (DescentData.isFamilyEffective_iff_isEffective D).1
    (DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex (fun _ : Unit ↦ f)
      (ofArrows_unit_mem_fpqcPrecoverage f) D fun _ ↦ hD)

/-- **Affine descent data are effective, in base-change form.** Let `f : T ⟶ S` be a surjective
flat quasi-compact morphism and `(Y, σ)` a descent datum relative to `f` whose structure morphism
`Y ⟶ T` is affine. Then there are an `S`-scheme `X` and an isomorphism `λ : X_T ≅ Y` of
`T`-schemes with `σ ∘ p₁^* λ = p₂^* λ ∘ σ_X`, where `σ_X` is the natural descent datum of
`X_T`. -/
@[weil "lem_fka3_affine_descent_effective"]
theorem exists_baseChangeTransition_of_isAffineHom (D : DescentDatum f)
    (hD : IsAffineHom D.over.hom) :
    ∃ (X : Over S) (l : (Over.pullback f).obj X ≅ D.over),
      (Over.pullback (pullback.fst f f)).map l.hom ≫ (baseChangeTransition D).hom =
        (naturalDescentIso f X).hom ≫ (Over.pullback (pullback.snd f f)).map l.hom :=
  (isEffective_iff_exists_baseChangeTransition D).1
    (isEffective_of_isAffineHom_of_faithfullyFlat D hD)

end DescentDatum

end AlgebraicGeometry
