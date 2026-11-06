module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CoefficientUniverseReduction

/-!
# `Ext` of abelian sheaves on the small étale site at a larger coefficient universe

The category of abelian sheaves on the small étale site of `X : Scheme.{u}`, with coefficients in
`AddCommGrpCat.{max (u + 1) v}`, has its `Ext` groups in the universe `max (u + 1) v`.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace AlgebraicGeometry

/-- `Ext` of abelian sheaves at the coefficients `AddCommGrpCat.{max (u + 1) v}` in the universe
`max (u + 1) v`. -/
theorem hasExt_sheaf_smallEtale_max (X : Scheme.{u}) :
    HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  CategoryTheory.IsGrothendieckAbelian.hasExt _

end AlgebraicGeometry
