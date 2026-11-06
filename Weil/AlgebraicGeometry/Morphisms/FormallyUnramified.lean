module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Noetherian
public import Weil.Attr

/-!
# Flat étale morphisms and open diagonals

Let `f : X ⟶ Y` be a flat morphism locally of finite type with `Y` locally noetherian. Then `f`
is étale if and only if its diagonal `X ⟶ X ×_Y X` is an open immersion.

## Main results

* `AlgebraicGeometry.etale_iff_isOpenImmersion_diagonal_of_flat`: for `f` flat and locally of
  finite type over a locally noetherian base, `f` is étale iff `pullback.diagonal f` is an open
  immersion.

## Implementation notes

The proof goes through formal unramifiedness: a morphism locally of finite type is formally
unramified iff its diagonal is an open immersion, and an étale morphism is the same as a flat,
formally unramified morphism locally of finite presentation; over a locally noetherian base,
locally of finite type and locally of finite presentation agree. Freitag–Kiehl's argument through
the conormal sheaf of the diagonal and Nakayama's lemma is not needed.

Freitag–Kiehl work throughout with noetherian schemes; the statement here only needs the base to
be locally noetherian.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/- FK's
"finitely generated" is `LocallyOfFiniteType`, FK's standing noetherian hypothesis is
`IsLocallyNoetherian Y`. -/

/-- A flat morphism locally of finite type over a locally noetherian scheme is étale if and only
if its diagonal is an open immersion. -/
@[weil "lem_fk102_flat_etale_iff_diagonal_open"]
theorem etale_iff_isOpenImmersion_diagonal_of_flat {X Y : Scheme} (f : X ⟶ Y) [Flat f]
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] :
    Etale f ↔ IsOpenImmersion (pullback.diagonal f) := by
  rw [Etale.iff_flat_and_formallyUnramified]
  constructor
  · rintro ⟨-, hu, -⟩
    infer_instance
  · intro hΔ
    exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry

end
