module

public import Weil.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import Weil.Attr

/-!
# Fibre products of covering spaces

Let `p₁ : Y₁ ⟶ X` and `p₂ : Y₂ ⟶ X` be covering spaces, i.e. finite étale morphisms. Then the
fibre product `Y₁ ×_X Y₂ ⟶ X` is again a covering space: the projection `Y₁ ×_X Y₂ ⟶ Y₁` is the
base change of `p₂` along `p₁`, hence finite étale, and its composite with `p₁` is finite étale
since finite and étale morphisms are stable under composition.

## Main definitions

* `AlgebraicGeometry.Scheme.CoveringSpace.fiberProduct` — the covering space
  `Y₁ ×_X Y₂ ⟶ X`.

## Main results

* `AlgebraicGeometry.Scheme.CoveringSpace.isFinite_pullback_fst_comp`,
  `AlgebraicGeometry.Scheme.CoveringSpace.etale_pullback_fst_comp` — the morphism
  `Y₁ ×_X Y₂ ⟶ X` is finite and étale.

## Implementation notes

The structure morphism of `Y₁ ×_X Y₂` is taken to be `pullback.fst p₁ p₂ ≫ p₁`; it agrees with
`pullback.snd p₁ p₂ ≫ p₂` by `pullback.condition`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.CoveringSpace

variable {X : Scheme.{u}}

/-- **The fibre product of covering spaces is finite.** For covering spaces `p₁ : Y₁ ⟶ X` and
`p₂ : Y₂ ⟶ X`, the morphism `Y₁ ×_X Y₂ ⟶ X` is finite. -/
@[weil "lem_fka1_covering_fiber_product"]
theorem isFinite_pullback_fst_comp (Y₁ Y₂ : X.CoveringSpace) :
    IsFinite (pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom) :=
  inferInstance

/-- **The fibre product of covering spaces is étale.** For covering spaces `p₁ : Y₁ ⟶ X` and
`p₂ : Y₂ ⟶ X`, the morphism `Y₁ ×_X Y₂ ⟶ X` is étale. -/
@[weil "lem_fka1_covering_fiber_product"]
theorem etale_pullback_fst_comp (Y₁ Y₂ : X.CoveringSpace) :
    Etale (pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom) :=
  inferInstance

/-- **The fibre product of covering spaces.** For covering spaces `p₁ : Y₁ ⟶ X` and
`p₂ : Y₂ ⟶ X`, the covering space `Y₁ ×_X Y₂ ⟶ X`. -/
@[weil "lem_fka1_covering_fiber_product"]
noncomputable abbrev fiberProduct (Y₁ Y₂ : X.CoveringSpace) : X.CoveringSpace :=
  have := isFinite_pullback_fst_comp Y₁ Y₂
  have := etale_pullback_fst_comp Y₁ Y₂
  mk (pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom)

theorem fiberProduct_left (Y₁ Y₂ : X.CoveringSpace) :
    (fiberProduct Y₁ Y₂).left = pullback Y₁.hom Y₂.hom :=
  rfl

theorem fiberProduct_hom (Y₁ Y₂ : X.CoveringSpace) :
    (fiberProduct Y₁ Y₂).hom = pullback.fst Y₁.hom Y₂.hom ≫ Y₁.hom :=
  rfl

theorem fiberProduct_hom_eq_snd_comp (Y₁ Y₂ : X.CoveringSpace) :
    (fiberProduct Y₁ Y₂).hom = pullback.snd Y₁.hom Y₂.hom ≫ Y₂.hom :=
  pullback.condition

end AlgebraicGeometry.Scheme.CoveringSpace
