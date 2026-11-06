module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Sections
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Sections of étale separated morphisms

Let `p : U ⟶ X` be an étale separated morphism of schemes and `s : X ⟶ U` a section of it,
`s ≫ p = 𝟙 X`. Then the image `s(X)` is open and closed in `U`, `s` is an open immersion, and
the induced isomorphism of `X` onto the open subscheme `s(X)` has inverse the restriction of `p`
to `s(X)`.

This applies to every object `(U, p)` of the étale category `Et(X)`
(`AlgebraicGeometry.SmallNoetherianSeparatedEtale`): its structure morphism is étale, and it is
separated because `U` is a separated scheme.

## Main results

* `AlgebraicGeometry.isClopen_range_of_isSection_of_etale`,
  `AlgebraicGeometry.isOpenImmersion_of_isSection_of_etale`,
  `AlgebraicGeometry.isoOpensRange_inv_of_isSection` — the statements for a section of an
  étale separated morphism.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isClopen_range_of_isSection`,
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isOpenImmersion_of_isSection`,
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isoOpensRange_inv_of_isSection` — the same for
  a section of the structure morphism of an object of `Et(X)`.

## Implementation notes

The isomorphism of `X` onto the open subscheme `s(X)` is Mathlib's
`AlgebraicGeometry.Scheme.Hom.isoOpensRange`, whose composite with the inclusion is `s`
(`AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι`). The proof goes through Stacks Project,
Tag 024T (a section of an unramified morphism is an open immersion, of a separated one a closed
immersion) rather than the diagonal argument of Freitag–Kiehl; the conclusions are the same.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1][FreitagKiehl]
* [Stacks Project, Tag 024T](https://stacks.math.columbia.edu/tag/024T)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X U : Scheme.{u}} (p : U ⟶ X) (s : X ⟶ U)

/-- The image of a section of an étale separated morphism is open and closed. -/
theorem isClopen_range_of_isSection_of_etale (hs : s ≫ p = 𝟙 X) [Etale p] [IsSeparated p] :
    IsClopen (Set.range s.base) :=
  have : Unramified p :=
    (unramified_iff_locallyOfFiniteType_and_formallyUnramified p).2
      ⟨inferInstance, inferInstance⟩
  isClopen_range_of_isSection p s hs

/-- A section of an étale morphism is an open immersion. -/
theorem isOpenImmersion_of_isSection_of_etale (hs : s ≫ p = 𝟙 X) [Etale p] :
    IsOpenImmersion s :=
  have : Unramified p :=
    (unramified_iff_locallyOfFiniteType_and_formallyUnramified p).2
      ⟨inferInstance, inferInstance⟩
  isOpenImmersion_of_isSection p s hs

/-- If a section `s` of `p` is an open immersion, the isomorphism of `X` onto the open
subscheme `s(X)` induced by `s` has inverse the restriction of `p` to `s(X)`. -/
theorem isoOpensRange_inv_of_isSection (hs : s ≫ p = 𝟙 X) [IsOpenImmersion s] :
    s.isoOpensRange.inv = s.opensRange.ι ≫ p := by
  rw [← cancel_epi s.isoOpensRange.hom, Iso.hom_inv_id, ← Category.assoc,
    Scheme.Hom.isoOpensRange_hom_ι, hs]

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}
  (U : SmallNoetherianSeparatedEtale B X hX) (s : X ⟶ (toScheme B X hX).obj U)

/-- The image of a section `s` of the structure morphism of an object `(U, p)` of `Et(X)` is
open and closed in `U`. -/
@[weil "lem_fk111_etale_section_open_closed_immersion"]
theorem isClopen_range_of_isSection (hs : s ≫ structureMorphism U = 𝟙 X) :
    IsClopen (Set.range s.base) :=
  isClopen_range_of_isSection_of_etale (structureMorphism U) s hs

/-- A section `s` of the structure morphism of an object `(U, p)` of `Et(X)` is an open
immersion, i.e. an isomorphism of `X` onto the open subscheme `s(X)` of `U`. -/
@[weil "lem_fk111_etale_section_open_closed_immersion"]
theorem isOpenImmersion_of_isSection (hs : s ≫ structureMorphism U = 𝟙 X) :
    IsOpenImmersion s :=
  isOpenImmersion_of_isSection_of_etale (structureMorphism U) s hs

/-- For a section `s` of the structure morphism `p` of an object `(U, p)` of `Et(X)`, the
isomorphism of `X` onto the open subscheme `s(X)` induced by `s` has inverse `p` restricted
to `s(X)`. -/
@[weil "lem_fk111_etale_section_open_closed_immersion"]
theorem isoOpensRange_inv_of_isSection (hs : s ≫ structureMorphism U = 𝟙 X) :
    have := isOpenImmersion_of_isSection U s hs
    s.isoOpensRange.inv = s.opensRange.ι ≫ structureMorphism U :=
  have := isOpenImmersion_of_isSection U s hs
  AlgebraicGeometry.isoOpensRange_inv_of_isSection (structureMorphism U) s hs

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
