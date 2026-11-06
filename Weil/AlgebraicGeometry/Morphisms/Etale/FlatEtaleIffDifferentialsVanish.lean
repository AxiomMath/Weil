module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.EtaleDescent

/-!
# Flat morphisms: étale iff the relative differentials vanish

Let `f : X ⟶ Y` be a flat morphism of schemes which is locally of finite type, with `Y`
locally noetherian. Then `f` is étale if and only if its sheaf of relative differentials
`Ω_{X/Y}` vanishes.

The proof combines the characterisation of étale morphisms as flat, formally unramified
morphisms locally of finite presentation with the criterion that a morphism is formally
unramified exactly when `Ω_{X/Y}` is zero. Over a locally noetherian base, locally of finite
type and locally of finite presentation agree.

## Main results

* `AlgebraicGeometry.etale_iff_isZero_relativeDifferentials_of_flat`: for a flat morphism
  locally of finite presentation, étale is equivalent to `Ω_{X/Y} = 0`.
* `AlgebraicGeometry.etale_iff_isZero_relativeDifferentials_of_flat_of_isLocallyNoetherian`:
  the same for a flat morphism locally of finite type over a locally noetherian base.

## Implementation notes

The source works with noetherian schemes throughout (its local-étale homomorphisms are maps of
noetherian local rings), so the finite type statement is given over a locally noetherian base.
Without that hypothesis it fails: for `A = ∏ₙ k` and `I = ⊕ₙ k`, the closed immersion
`Spec (A ⧸ I) ⟶ Spec A` is flat (every `A`-module is flat), of finite type, and has vanishing
relative differentials, but it is not of finite presentation, hence not étale. The version for
morphisms locally of finite presentation needs no noetherian hypothesis.

Vanishing of `Ω_{X/Y}` is the categorical predicate `CategoryTheory.Limits.IsZero` on
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.2
* [Stacks Project, Tag 02GU](https://stacks.math.columbia.edu/tag/02GU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A flat morphism of schemes locally of finite presentation is étale if and only if its
sheaf of relative differentials vanishes. -/
theorem etale_iff_isZero_relativeDifferentials_of_flat [Flat f]
    [LocallyOfFinitePresentation f] :
    Etale f ↔ IsZero (Scheme.Hom.relativeDifferentials f) := by
  rw [Etale.iff_flat_and_formallyUnramified, ← formallyUnramified_iff_isZero_relativeDifferentials]
  exact ⟨fun h ↦ h.2.1, fun h ↦ ⟨‹_›, h, ‹_›⟩⟩

/-- **A flat morphism of finite type is étale iff `Ω_{X/Y} = 0`.** Let `f : X ⟶ Y` be a flat
morphism of schemes, locally of finite type, with `Y` locally noetherian. Then `f` is étale if
and only if its sheaf of relative differentials vanishes. -/
@[weil "lem_fk102_flat_etale_iff_differentials_vanish"]
theorem etale_iff_isZero_relativeDifferentials_of_flat_of_isLocallyNoetherian
    [IsLocallyNoetherian Y] [Flat f] [LocallyOfFiniteType f] :
    Etale f ↔ IsZero (Scheme.Hom.relativeDifferentials f) :=
  etale_iff_isZero_relativeDifferentials_of_flat f

end AlgebraicGeometry

end
