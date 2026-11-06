module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# Constructible abelian sheaves and their underlying sheaves of sets

Let `X` be a scheme whose underlying space is Noetherian. A sheaf of abelian groups `F` on the
small étale site of `X` is constructible *as a sheaf of abelian groups* if there are finitely many
locally closed subschemes `Yⱼ ⟶ X` covering `X` such that each inverse image `F|_{Yⱼ}` is finite
locally constant as a sheaf of abelian groups, i.e. étale locally isomorphic to a constant
abelian sheaf with finite value. This file proves that this holds if and only if the underlying
sheaf of sets of `F` is constructible.

## Main results

* `AlgebraicGeometry.exists_immersion_cover_isFiniteLocallyConstant_iff_isConstructibleSetSheaf`:
  `F` is constructible as a sheaf of abelian groups (strata on which it is finite locally
  constant as an abelian sheaf) if and only if its underlying sheaf of sets is constructible.

## Implementation notes

The constant abelian sheaf `M_U` and the constant sheaf of sets on the underlying set of `M` are
compared through the forgetful functor: inverse image along an immersion commutes with taking
underlying sheaves of sets (`AlgebraicGeometry.smallEtaleUnderlyingSetCommutes`), and finite
local constancy of an abelian sheaf is equivalent to that of its underlying sheaf of sets
(Stacks, Tag 093Q). The detour of [FK] through connected components is not needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]
  [∀ (S T : B.Scheme) (f : T ⟶ S) (V : SmallEtale B S.obj S.property),
    ((Over.post (X := V) (smallEtaleBaseChange B f)).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      ((SmallEtale.topology B S.obj S.property).over V)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj V))).IsRightAdjoint]

/-- **Constructible abelian sheaves and their underlying sheaves of sets.** On a scheme `X` whose
underlying space is Noetherian, a sheaf of abelian groups `F` on the small étale site of `X` is
constructible as a sheaf of abelian groups — there are finitely many immersions `Yⱼ ⟶ X`, jointly
surjective onto `X`, along each of which the inverse image of `F` is finite locally constant as
a sheaf of abelian groups — if and only if the underlying sheaf of sets of `F` is constructible. -/
@[weil "lem_fk104_abelian_constructible_iff_underlying_constructible"]
theorem exists_immersion_cover_isFiniteLocallyConstant_iff_isConstructibleSetSheaf
    [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (∃ (n : ℕ) (Y : Fin n → B.Scheme) (j : ∀ i, Y i ⟶ X),
        (∀ i, IsImmersion (B.inclusion.map (j i))) ∧
        (Set.univ : Set X.obj) = ⋃ i, Set.range (B.inclusion.map (j i)).base ∧
        ∀ i, SmallEtale.IsFiniteLocallyConstant B (Y i).obj (Y i).property
          (((smallEtaleBaseChange B (j i)).sheafPullback AddCommGrpCat.{u + 1}
            (SmallEtale.topology B X.obj X.property)
            (SmallEtale.topology B (Y i).obj (Y i).property)).obj F)) ↔
      IsConstructibleSetSheaf B X ((smallEtaleUnderlyingSetSheaf B X).obj F) := by
  rw [← isConstructibleAbelianSheaf_iff_isConstructibleSetSheaf]
  exact (isConstructibleFiniteSheaf_iff_exists_immersion_cover B X F).symm

end AlgebraicGeometry
