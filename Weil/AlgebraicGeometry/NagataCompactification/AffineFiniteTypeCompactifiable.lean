module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import Weil.AlgebraicGeometry.NagataCompactification.HasCompactification

/-!
# Affine schemes of finite type over a field are compactifiable

Let `Y` be an affine scheme of finite type over a field `κ`. Then the structure morphism
`Y ⟶ Spec κ` is compactifiable: it factors as a quasi-compact open immersion followed by a
proper morphism.

More generally, every locally of finite type morphism from an affine scheme to an affine
scheme is compactifiable. Such a morphism is affine, hence separated, and quasi-compact, so
Nagata's compactification theorem applies.

## Main results

* `AlgebraicGeometry.hasCompactification_of_isAffine`: a locally of finite type morphism
  between affine schemes is compactifiable.
* `AlgebraicGeometry.hasCompactification_of_isAffine_of_field`: an affine scheme of finite type
  over a field is compactifiable over it.

## Implementation notes

[FK] argues through the quasi-projective embedding `Y ⟶ 𝔸^m_κ ⟶ ℙ^m_κ`. Here the result is
deduced from Nagata's theorem (Stacks, Tag 0F41), which covers every separated morphism of
finite type over a quasi-compact quasi-separated base.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Introduction.
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A locally of finite type morphism from an affine scheme to an affine scheme is
compactifiable. -/
theorem hasCompactification_of_isAffine {Y S : Scheme.{u}} [IsAffine Y] [IsAffine S]
    (f : Y ⟶ S) [LocallyOfFiniteType f] : HasCompactification f :=
  hasCompactification_of_compactSpace_quasiSeparatedSpace f

/-- An affine scheme `Y` of finite type over a field `κ` is compactifiable over `κ`: its
structure morphism `Y ⟶ Spec κ` has a compactification. -/
@[weil "lem_fk0_affine_finite_type_compactifiable"]
theorem hasCompactification_of_isAffine_of_field {κ : Type u} [Field κ] {Y : Scheme.{u}}
    [IsAffine Y] (f : Y ⟶ Spec (.of κ)) [LocallyOfFiniteType f] : HasCompactification f :=
  hasCompactification_of_isAffine f

end AlgebraicGeometry
