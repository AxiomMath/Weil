module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications

/-!
# Compactifications of a morphism of schemes

A compactification of a morphism of schemes `f : X ⟶ S` is a triple `(X̄, j, f̄)` of a scheme
`X̄`, an open immersion `j : X ⟶ X̄` and a proper morphism `f̄ : X̄ ⟶ S` with `j ≫ f̄ = f`.
These are exactly the objects of the category `AlgebraicGeometry.CompactificationOf (Over.mk f)`
of compactifications of `X` viewed as an `S`-scheme, whose morphisms are the morphisms of the
ambient `S`-schemes compatible with the open immersions (one compactification dominating
another).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.Compactification f`: the category of compactifications of
  `f : X ⟶ S`.
* `AlgebraicGeometry.Scheme.Hom.Compactification.mk`: the compactification attached to a
  triple `(X̄, j, f̄)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.Compactification.immersion_comp_toBase`: for a compactification
  `c` of `f`, the open immersion followed by the proper structure morphism is `f`.
* `AlgebraicGeometry.Scheme.Hom.nonempty_compactification_iff`: `f` has a compactification if
  and only if it factors as an open immersion followed by a proper morphism.

## Implementation notes

The category of compactifications is the one of the Stacks project, Tag 0ATU, for the
`S`-scheme `Over.mk f`; no new structure is introduced. The ambient scheme, the open immersion
and the proper morphism of `c : f.Compactification` are `c.space`, `c.immersion` and
`c.toBase`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §8.
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- The category of compactifications of a morphism of schemes `f : X ⟶ S`: an object is a
scheme `X̄` with an open immersion `X ⟶ X̄` and a proper morphism `X̄ ⟶ S` whose composite
is `f`; a morphism is a morphism of the ambient `S`-schemes compatible with the open
immersions. -/
@[weil "def_fk108_compactification"]
abbrev Compactification (f : X ⟶ S) : Type (u + 1) :=
  CompactificationOf (Over.mk f)

namespace Compactification

variable {f : X ⟶ S}

/-- The open immersion of a compactification of `f`, followed by its proper morphism to the
base, is `f`. -/
@[reassoc (attr := simp)]
lemma immersion_comp_toBase (c : f.Compactification) : c.immersion ≫ c.toBase = f :=
  Over.w c.obj.hom

/-- The compactification of `f` given by a scheme `X̄`, an open immersion `j : X ⟶ X̄` and a
proper morphism `f̄ : X̄ ⟶ S` with `j ≫ f̄ = f`. -/
def mk (X' : Scheme.{u}) (j : X ⟶ X') [IsOpenImmersion j] (f' : X' ⟶ S) [IsProper f']
    (h : j ≫ f' = f) : f.Compactification :=
  ⟨StructuredArrow.mk (Y := Over.mk f') (Over.homMk j h), ⟨inferInstanceAs (IsOpenImmersion j),
    inferInstanceAs (IsProper f')⟩⟩

variable (X' : Scheme.{u}) (j : X ⟶ X') [IsOpenImmersion j] (f' : X' ⟶ S) [IsProper f']
  (h : j ≫ f' = f)

@[simp]
lemma space_mk : (mk X' j f' h).space = X' := rfl

@[simp]
lemma immersion_mk : (mk X' j f' h).immersion = j := rfl

@[simp]
lemma toBase_mk : (mk X' j f' h).toBase = f' := rfl

end Compactification

/-- A morphism of schemes `f : X ⟶ S` has a compactification if and only if there are a
scheme `X̄`, an open immersion `j : X ⟶ X̄` and a proper morphism `f̄ : X̄ ⟶ S` with
`j ≫ f̄ = f`. -/
@[weil "def_fk108_compactification"]
theorem nonempty_compactification_iff (f : X ⟶ S) :
    Nonempty f.Compactification ↔ ∃ (X' : Scheme.{u}) (j : X ⟶ X') (f' : X' ⟶ S),
      IsOpenImmersion j ∧ IsProper f' ∧ j ≫ f' = f := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.space, c.immersion, c.toBase, inferInstance, inferInstance,
      c.immersion_comp_toBase⟩
  · rintro ⟨X', j, f', hj, hf', h⟩
    exact ⟨Compactification.mk X' j f' h⟩

end Scheme.Hom

end AlgebraicGeometry
