module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleCofinality
public import Weil.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import Weil.Attr

/-!
# Morphisms of covering spaces onto a connected covering space

Let `p₁ : Y₁ ⟶ X` and `p₂ : Y₂ ⟶ X` be covering spaces of a scheme `X` and `f : Y₁ ⟶ Y₂` an
`X`-morphism, with `Y₁` nonempty and `Y₂` connected. Then for every geometric point `s` of `X`
the induced map `f(s) : Y₁(s) → Y₂(s)` on geometric points over `s` is surjective.

The proof regards `f` as a covering space of `Y₂`: it is étale and finite, since `p₂` and
`p₂ ∘ f = p₁` are. A point `α₂ ∈ Y₂(s)` is a geometric point of the connected scheme `Y₂`, and a
nonempty covering space of a connected scheme has nonempty geometric fibres; a point `α₁` of
`Y₁` over `α₂` lies in `Y₁(s)` and maps to `α₂`.

## Main results

* `AlgebraicGeometry.Scheme.CoveringSpace.surjective_fiberFunctor_map` — `f(s)` is surjective.

## Implementation notes

The source works with covering spaces of a noetherian separated scheme and uses that `Y₂` is
separated to see that `f` is finite. Here covering spaces are finite étale morphisms over an
arbitrary scheme; `f` is finite because `p₂` is finite, hence separated, so no hypothesis on `X`
is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.CoveringSpace

variable {X : Scheme.{u}}

/-- **A morphism of covering spaces onto a connected one is surjective on geometric fibres.**
Let `f : Y₁ ⟶ Y₂` be a morphism of covering spaces of `X` with `Y₁` nonempty and `Y₂`
connected. Then for every geometric point `s` of `X` the map `f(s) : Y₁(s) → Y₂(s)` is
surjective. -/
@[weil "lem_fka1_covering_morphism_fiber_surjective"]
theorem surjective_fiberFunctor_map {Y₁ Y₂ : X.CoveringSpace} (f : Y₁ ⟶ Y₂)
    [Nonempty Y₁.left] [ConnectedSpace Y₂.left] (s : GeometricPoint X) :
    Function.Surjective
      ((GeometricPoint.fiberFunctor s).map ((MorphismProperty.Over.forget _ _ X).map f)) := by
  rintro ⟨α₂, hα₂⟩
  have : IsFinite f.left := isFinite_hom_left f
  have : Etale f.left := etale_hom_left f
  let t : GeometricPoint Y₂.left := ⟨s.residueField, α₂⟩
  let V : Y₂.left.CoveringSpace := mk f.left
  have : Nonempty V.left := ‹Nonempty Y₁.left›
  obtain ⟨⟨α₁, hα₁⟩⟩ := nonempty_finiteEtaleFiber_of_nonempty_left t V
  refine ⟨⟨α₁, ?_⟩, ?_⟩
  · have h : α₁ ≫ f.left = α₂ := hα₁
    change α₁ ≫ Y₁.hom = s.hom
    rw [← left_comp_hom f, ← hα₂, ← h]
    exact (Category.assoc _ _ _).symm
  · exact Subtype.ext hα₁

end Scheme.CoveringSpace

end AlgebraicGeometry

end
