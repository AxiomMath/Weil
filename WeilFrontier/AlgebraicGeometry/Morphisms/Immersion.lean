module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# A closed subscheme of an open subscheme is open in its closure

Let `i : X ⟶ U` be a closed immersion and `j : U ⟶ P` an open immersion, and suppose the
composite `ι = i ≫ j` is quasi-compact (for instance, `X` is noetherian). Let `X̄ ⊆ P` be the
scheme-theoretic image of `ι`. Then `ι` factors as an open immersion `X ⟶ X̄` followed by the
closed immersion `X̄ ⟶ P`.

The composite `ι` is an immersion, so this is the statement that a quasi-compact immersion is an
open immersion into its scheme-theoretic image.

## Main results

* `AlgebraicGeometry.isOpenImmersion_toImage_comp_of_isClosedImmersion`: for a closed immersion
  `i` followed by an open immersion `j` with `i ≫ j` quasi-compact, `(i ≫ j).toImage` is an open
  immersion, `(i ≫ j).imageι` is a closed immersion, and their composite is `i ≫ j`.
* `AlgebraicGeometry.isOpenImmersion_toImage_comp_of_isNoetherian`: the same for a noetherian
  source.

## Implementation notes

The source assumes `X` noetherian only to obtain the quasi-compactness of `ι`; the main result
assumes quasi-compactness of `ι` directly.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks, Tag 01QV]
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X U P : Scheme.{u}} (i : X ⟶ U) (j : U ⟶ P)

/-- A closed immersion followed by an open immersion, with quasi-compact composite, factors as an
open immersion into its scheme-theoretic image followed by the closed immersion of that image. -/
@[weil "lem_fk108_immersion_open_in_closure"]
theorem isOpenImmersion_toImage_comp_of_isClosedImmersion [IsClosedImmersion i]
    [IsOpenImmersion j] [QuasiCompact (i ≫ j)] :
    IsOpenImmersion (i ≫ j).toImage ∧ IsClosedImmersion (i ≫ j).imageι ∧
      (i ≫ j).toImage ≫ (i ≫ j).imageι = i ≫ j :=
  ⟨inferInstance, inferInstance, (i ≫ j).toImage_imageι⟩

/-- The case of a noetherian source, as in the source: the composite is then quasi-compact. -/
theorem isOpenImmersion_toImage_comp_of_isNoetherian [IsNoetherian X] [IsClosedImmersion i]
    [IsOpenImmersion j] :
    IsOpenImmersion (i ≫ j).toImage ∧ IsClosedImmersion (i ≫ j).imageι ∧
      (i ≫ j).toImage ≫ (i ≫ j).imageι = i ≫ j :=
  have : QuasiCompact (i ≫ j) := inferInstance
  isOpenImmersion_toImage_comp_of_isClosedImmersion i j

end AlgebraicGeometry

end
