module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.HasCompactification
public import Weil.Defs.AlgebraicGeometry.Flatness.Flattening.Compactifications

/-!
# Compactifiable morphisms of schemes

A morphism of schemes `f : X ⟶ S` is *compactifiable* if it has a compactification, that is,
if it factors as an open immersion `j : X ⟶ X̄` followed by a proper morphism `f̄ : X̄ ⟶ S`.

The predicate used for this is `AlgebraicGeometry.HasCompactification f`, which asks moreover
that the open immersion be quasi-compact. That extra condition is automatic as soon as the
underlying space of `X` is Noetherian, which is the setting of [FK, I.8]: every morphism out of
a Noetherian scheme is quasi-compact. This file identifies the two notions there.

## Main results

* `AlgebraicGeometry.HasCompactification.nonempty_compactification`: a morphism with a
  (quasi-compact) compactification has a compactification.
* `AlgebraicGeometry.hasCompactification_iff_nonempty_compactification`: for `X` with Noetherian
  underlying space, `f : X ⟶ S` is compactifiable if and only if it has a compactification.
* `AlgebraicGeometry.hasCompactification_iff_exists`: for `X` with Noetherian underlying space,
  `f` is compactifiable if and only if `f = j ≫ f̄` with `j` an open immersion and `f̄` proper.

## Implementation notes

The compactifiable morphisms are those satisfying `AlgebraicGeometry.HasCompactification`;
no new predicate is introduced. For a source whose underlying space is not Noetherian,
`AlgebraicGeometry.HasCompactification f` is the standard notion (Stacks, Tag 0F41), which
asks the open immersion to be quasi-compact.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §8, p. 86.
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A morphism with a compactification in the sense of `HasCompactification` (a quasi-compact
open immersion followed by a proper morphism) has a compactification. -/
theorem HasCompactification.nonempty_compactification {f : X ⟶ S}
    (hf : HasCompactification f) : Nonempty f.Compactification :=
  let ⟨j, _⟩ := hf
  ⟨j⟩

/-- A morphism `f : X ⟶ S` whose source has Noetherian underlying space has a
compactification if and only if it is compactifiable: the open immersion of any
compactification is then quasi-compact. -/
@[weil "def_fk108_compactifiable"]
theorem hasCompactification_iff_nonempty_compactification [NoetherianSpace X] (f : X ⟶ S) :
    HasCompactification f ↔ Nonempty f.Compactification :=
  ⟨HasCompactification.nonempty_compactification, fun ⟨c⟩ => ⟨c, inferInstance⟩⟩

/-- A morphism `f : X ⟶ S` whose source has Noetherian underlying space is compactifiable if
and only if it factors as an open immersion `j : X ⟶ X̄` followed by a proper morphism
`f̄ : X̄ ⟶ S`. -/
@[weil "def_fk108_compactifiable"]
theorem hasCompactification_iff_exists [NoetherianSpace X] (f : X ⟶ S) :
    HasCompactification f ↔ ∃ (X' : Scheme.{u}) (j : X ⟶ X') (f' : X' ⟶ S),
      IsOpenImmersion j ∧ IsProper f' ∧ j ≫ f' = f :=
  (hasCompactification_iff_nonempty_compactification f).trans
    (Scheme.Hom.nonempty_compactification_iff f)

end AlgebraicGeometry
