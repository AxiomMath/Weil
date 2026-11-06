module

public import Mathlib.Algebra.Homology.Localization
public import Weil.Attr

/-!
# Two-out-of-three for quasi-isomorphisms in the homotopy category

Let `C` be a preadditive category with homology and `c` a complex shape. A morphism `σ` of the
homotopy category `HomotopyCategory C c` is a quasi-isomorphism (`HomotopyCategory.quasiIso`)
when it induces isomorphisms on all homology objects. We show that this class of morphisms has
the two-out-of-three property: if two of `σ`, `τ`, `σ ≫ τ` are quasi-isomorphisms, so is the
third. The proof is functoriality of homology on the homotopy category, together with the
two-out-of-three property of isomorphisms.

## Main results

* `HomotopyCategory.quasiIso_hasTwoOutOfThreeProperty`: `quasiIso C c` has the
  two-out-of-three property; it is also registered as an instance.
* `HomotopyCategory.quasiIso_of_comp_left`, `HomotopyCategory.quasiIso_of_comp_right`:
  the two cancellation statements in explicit form.

## Implementation notes

The statement is proved for an arbitrary complex shape `c` and an arbitrary preadditive
category with homology; the case of cochain complexes indexed by `ℤ` in an abelian category
is the special case `c = ComplexShape.up ℤ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory

namespace HomotopyCategory

variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

/-- The quasi-isomorphisms of the homotopy category have the two-out-of-three property. -/
@[weil "lem_fka2_qis_two_of_three_composition"]
theorem quasiIso_hasTwoOutOfThreeProperty : (quasiIso C c).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg := MorphismProperty.comp_mem _ f g hf hg
  of_postcomp f g hg hfg := by
    rw [mem_quasiIso_iff] at hg hfg ⊢
    intro n
    have := hg n
    have := hfg n
    rw [Functor.map_comp] at this
    exact IsIso.of_isIso_comp_right _ ((homologyFunctor C c n).map g)
  of_precomp f g hf hfg := by
    rw [mem_quasiIso_iff] at hf hfg ⊢
    intro n
    have := hf n
    have := hfg n
    rw [Functor.map_comp] at this
    exact IsIso.of_isIso_comp_left ((homologyFunctor C c n).map f) _

instance : (quasiIso C c).HasTwoOutOfThreeProperty :=
  quasiIso_hasTwoOutOfThreeProperty C c

variable {C c}

/-- If `τ` and `σ ≫ τ` are quasi-isomorphisms in the homotopy category, so is `σ`. -/
theorem quasiIso_of_comp_left {X Y Z : HomotopyCategory C c} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (hτ : quasiIso C c τ) (hστ : quasiIso C c (σ ≫ τ)) : quasiIso C c σ :=
  (quasiIso C c).of_postcomp σ τ hτ hστ

/-- If `σ` and `σ ≫ τ` are quasi-isomorphisms in the homotopy category, so is `τ`. -/
theorem quasiIso_of_comp_right {X Y Z : HomotopyCategory C c} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (hσ : quasiIso C c σ) (hστ : quasiIso C c (σ ≫ τ)) : quasiIso C c τ :=
  (quasiIso C c).of_precomp σ τ hσ hστ

end HomotopyCategory

end
