module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFpqcDescent
public import Weil.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import Weil.Attr

/-!
# Effective descent of quasi-affine schemes along a faithfully flat quasi-compact morphism

Let `f : T ⟶ S` be a faithfully flat (flat and surjective) quasi-compact morphism of schemes and
let `(Y, σ)` be a descent datum relative to `f` whose structure morphism `Y ⟶ T` is quasi-affine.
Then `(Y, σ)` is effective: there are an `S`-scheme `X` and an isomorphism `λ : X_T ≅ Y` of
`T`-schemes with `σ ∘ p₁^* λ = p₂^* λ ∘ σ_X`, where `σ_X` is the natural descent datum of `X_T`.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_of_isQuasiAffineHom` : a descent datum relative to
  a flat, surjective, quasi-compact morphism whose structure morphism is quasi-affine is
  effective.
* `AlgebraicGeometry.DescentDatum.exists_baseChangeTransition_of_isQuasiAffineHom` : the same
  conclusion in the explicit form, with the isomorphism `λ : X_T ≅ Y`.

## Implementation notes

The one-member family `{f}` is an fpqc covering of `S`
(`AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage`), so the statement is the
one-member case of the fpqc descent of quasi-affine morphisms,
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isQuasiAffineHom` (Stacks 0247), whose proof
is the affine-hull argument: a quasi-affine `Y ⟶ T` is an open immersion into its affine hull
`Spec_T (g_* 𝒪_Y)`, flat base change extends the descent datum to the hull, effective descent of
affine morphisms descends the hull, and the open subscheme `Y` descends since a faithfully flat
quasi-compact morphism is submersive.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.6.
* [SGA 1, VIII 7.9]
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace DescentDatum

variable {T S : Scheme.{u}} (f : T ⟶ S) [Flat f] [Surjective f] [QuasiCompact f]

/-- **Effective descent of quasi-affine schemes.** Let `f : T ⟶ S` be a flat, surjective,
quasi-compact morphism of schemes and `D` a descent datum relative to `f` whose structure morphism
`Y ⟶ T` is quasi-affine. Then `D` is effective. -/
@[weil "prop_fka3_quasi_affine_descent_effective"]
theorem isEffective_of_isQuasiAffineHom (D : DescentDatum f)
    (hD : IsQuasiAffineHom D.over.hom) : DescentData.IsEffective D := by
  have hf : Presieve.ofArrows (fun _ : Unit ↦ T) (fun _ ↦ f) ∈ Scheme.fpqcPrecoverage S := by
    rw [Presieve.ofArrows_pUnit]
    exact f.singleton_mem_fpqcPrecoverage
  exact (DescentData.isFamilyEffective_iff_isEffective D).1
    (DescentData.isFamilyEffective_of_isQuasiAffineHom _ hf D fun _ ↦ hD)

/-- **Effective descent of quasi-affine schemes, explicit form.** Let `f : T ⟶ S` be a flat,
surjective, quasi-compact morphism of schemes and `(Y, σ)` a descent datum relative to `f` whose
structure morphism `Y ⟶ T` is quasi-affine. Then there are an `S`-scheme `X` and an isomorphism
`λ : X_T ≅ Y` of `T`-schemes with `σ ∘ p₁^* λ = p₂^* λ ∘ σ_X`. -/
@[weil "prop_fka3_quasi_affine_descent_effective"]
theorem exists_baseChangeTransition_of_isQuasiAffineHom (D : DescentDatum f)
    (hD : IsQuasiAffineHom D.over.hom) :
    ∃ (X : Over S) (l : (Over.pullback f).obj X ≅ D.over),
      (Over.pullback (pullback.fst f f)).map l.hom ≫ (baseChangeTransition D).hom =
        (naturalDescentIso f X).hom ≫ (Over.pullback (pullback.snd f f)).map l.hom :=
  (isEffective_iff_exists_baseChangeTransition D).1 (isEffective_of_isQuasiAffineHom f D hD)

end DescentDatum

end AlgebraicGeometry
