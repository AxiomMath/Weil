module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfHigherDirectImage
public import StacksFrontier.CategoryTheory.Limits.SystemColimitLift
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings

/-!
# Cohomology of the base change to a strict localization

Let `f : Y ⟶ X` be a quasi-compact quasi-separated morphism of schemes (for instance a morphism
from a noetherian scheme), `x` a geometric point of `X` with strict local ring `𝒪̃_{X,x}`,
`Ỹ = Y ×_X Spec 𝒪̃_{X,x}`, and `F` an abelian sheaf on the small étale site of `Y` with inverse
image `F̃` on `Ỹ`. For every `ν ≥ 0` the inverse-image maps
`H^ν(Y ×_X U, F|_{Y ×_X U}) → H^ν(Ỹ, F̃)` exhibit `H^ν(Ỹ, F̃)` as the colimit, over the étale
neighbourhoods `(U, u)` of `x`, of the groups `H^ν(Y ×_X U, F|_{Y ×_X U})`.

The étale neighbourhoods are those of the directed system of affine étale neighbourhoods of `x`,
whose limit is `Spec 𝒪̃_{X,x}`; the base changes `Y ×_X U` form an inverse system with affine
transition morphisms and limit `Ỹ`, and the statement is the theorem on cohomology along
projective limits of schemes ([Stacks, Tag 09YQ]) for that system.

## Main results

* `AlgebraicGeometry.isOfCoconeCohomologyColimit_strictLocalization`: for `f` quasi-compact and
  quasi-separated, `H^ν(Ỹ, F̃)` is the colimit of the system `H^ν(Y ×_X U, F|_{Y ×_X U})`.
* `AlgebraicGeometry.isOfCoconeCohomologyColimit_strictLocalization_of_isNoetherian`: the same
  for a noetherian scheme `Y`, the setting of the source.
* `AlgebraicGeometry.nonempty_isColimit_cohomology_strictLocalization`: the same, as a colimit
  cocone of a functor on a filtered category.

## Implementation notes

The strict local ring `AlgebraicGeometry.strictLocalRing` is the étale local ring at `x`, so
`Spec 𝒪̃_{X,x}` is `AlgebraicGeometry.strictHenselization` and `Ỹ` is
`AlgebraicGeometry.strictHenselizationBaseChange`, by definition.

The colimit runs over the affine étale neighbourhoods of `x`, which are cofinal among all étale
neighbourhoods. The sheaf on `Y ×_X U` is the inverse image of `F` along the étale morphism
`Y ×_X U ⟶ Y`, which is the restriction of `F`. The transition maps of the system satisfy the
cocycle condition but are not asserted to satisfy the identity law, so the colimit is the
universal property `CategoryTheory.Limits.IsSystemColimit` of a system of groups; over the
filtered category `CategoryTheory.Limits.SystemLift` it is an honest colimit cocone.

The statement is made on Mathlib's small étale sites `Scheme.smallEtaleTopology`, with
coefficients `AddCommGrpCat.{u + 1}`, where the theorem on cohomology along limits is available.
The source assumes `f` of finite type between noetherian separated schemes; only the
quasi-compactness and quasi-separatedness of `f` are used.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.4
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

/- a statement on the bounded small étale site
`AlgebraicGeometry.SmallEtale` with coefficients `AddCommGrpCat.{u}` needs two comparisons not yet
in the library: inverse images along arbitrary morphisms on `SmallEtale` versus
`Stacks.EtaleCohomology.smallEtalePullbackAb` across `SmallEtale.sheafEquiv`, and étale
cohomology across the universe lift `AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u + 1}`. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : Y ⟶ X)
  (x : GeometricPoint X)

/-- `Spec` of the strict local ring of `X` at `x` is the strict henselization of `X` at `x`. -/
theorem spec_strictLocalRing_eq_strictHenselization :
    Spec (strictLocalRing B X hX x) = strictHenselization B X hX x :=
  rfl

section QCQS

variable [QuasiCompact f] [QuasiSeparated f]

/-- **Cohomology of the base change to a strict localization is a colimit.** For a
quasi-compact quasi-separated `f : Y ⟶ X`, a geometric point `x` of `X`, an abelian sheaf `F` on
`Y` and `ν ≥ 0`, the inverse-image maps `H^ν(Y ×_X U, F|_{Y ×_X U}) → H^ν(Ỹ, F̃)`, for the affine
étale neighbourhoods `(U, u)` of `x`, exhibit the cohomology of the inverse image `F̃` of `F` on
`Ỹ = Y ×_X Spec 𝒪̃_{X,x}` as the colimit of the system `H^ν(Y ×_X U, F|_{Y ×_X U})`. -/
@[weil "lem_fk104_cohomology_strict_localization_colimit"]
theorem isOfCoconeCohomologyColimit_strictLocalization
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (ν : ℕ) :
    IsOfCoconeCohomologyColimit (strictHenselizationBaseChangeDirectedι B hX f x)
      (strictHenselizationBaseChangeDirectedDiagram_map_ι B hX f x)
      (strictHenselizationBaseChangeDirectedCone B hX f x)
      (strictHenselizationBaseChangeToSource B hX f x)
      (strictHenselizationBaseChangeDirectedCone_π_app_ι B hX f x) F ν :=
  isOfCoconeCohomologyColimit_strictHenselizationBaseChange B hX f x F ν

/-- **Cohomology of the base change to a strict localization, as a colimit cocone.** The groups
`H^ν(Y ×_X U, F|_{Y ×_X U})`, read as a functor on the filtered category
`CategoryTheory.Limits.SystemLift` of the directed system of affine étale neighbourhoods of `x`,
have colimit `H^ν(Ỹ, F̃)`, with legs the inverse-image maps. -/
theorem nonempty_isColimit_cohomology_strictLocalization
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (ν : ℕ) :
    Nonempty (IsColimit (SystemLift.cocone
      (A := fun i => AddCommGrpCat.of (Sheaf.H.{u + 1}
        ((EtaleSheafSystem.ofCocone (strictHenselizationBaseChangeDirectedι B hX f x)
          (strictHenselizationBaseChangeDirectedDiagram_map_ι B hX f x) F).obj i) ν))
      (T := fun a => AddCommGrpCat.ofHom
        (etaleCohomologyPullback ((strictHenselizationBaseChangeDirectedDiagram B hX f x).map a)
          ((EtaleSheafSystem.ofCocone (strictHenselizationBaseChangeDirectedι B hX f x)
            (strictHenselizationBaseChangeDirectedDiagram_map_ι B hX f x) F).map a) ν))
      (hT := fun a b => IsOfCoconeCohomologyColimit.transition_comp
        (hg := strictHenselizationBaseChangeDirectedCone_π_app_ι B hX f x) a b)
      (B := AddCommGrpCat.of (Sheaf.H.{u + 1}
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hX f x)).obj F) ν))
      (ψ := fun i => AddCommGrpCat.ofHom (etaleCohomologyPullback
          ((strictHenselizationBaseChangeDirectedCone B hX f x).π.app i)
          (EtaleSheafSystem.ofCoconeLeg (strictHenselizationBaseChangeDirectedι B hX f x)
            (strictHenselizationBaseChangeDirectedDiagram_map_ι B hX f x)
            (strictHenselizationBaseChangeDirectedCone B hX f x)
            (strictHenselizationBaseChangeToSource B hX f x)
            (strictHenselizationBaseChangeDirectedCone_π_app_ι B hX f x) F i) ν))
      (hψ := fun a => IsOfCoconeCohomologyColimit.transition_comp_leg a))) :=
  (SystemLift.isSystemColimit_iff _ _ _).mp
    (isOfCoconeCohomologyColimit_strictLocalization B hX f x F ν)

end QCQS

/-- **Cohomology of the base change to a strict localization, for a noetherian source.** For a
morphism `f : Y ⟶ X` from a noetherian scheme, a geometric point `x` of `X`, an abelian sheaf `F`
on `Y` and `ν ≥ 0`, `H^ν(Y ×_X Spec 𝒪̃_{X,x}, F̃)` is the colimit of the groups
`H^ν(Y ×_X U, F|_{Y ×_X U})` over the affine étale neighbourhoods `(U, u)` of `x`, along the
inverse-image maps. -/
@[weil "lem_fk104_cohomology_strict_localization_colimit"]
theorem isOfCoconeCohomologyColimit_strictLocalization_of_isNoetherian [IsNoetherian Y]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (ν : ℕ) :
    IsOfCoconeCohomologyColimit (strictHenselizationBaseChangeDirectedι B hX f x)
      (strictHenselizationBaseChangeDirectedDiagram_map_ι B hX f x)
      (strictHenselizationBaseChangeDirectedCone B hX f x)
      (strictHenselizationBaseChangeToSource B hX f x)
      (strictHenselizationBaseChangeDirectedCone_π_app_ι B hX f x) F ν :=
  isOfCoconeCohomologyColimit_strictLocalization B hX f x F ν

end AlgebraicGeometry

end
