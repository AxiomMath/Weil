module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekTorsion
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import Weil.Attr

/-!
# Torsion sheaves are detected on stalks

An abelian sheaf `F` on the small étale site of a scheme `S` is a torsion sheaf if and only if
its stalk `F_x` at every geometric point `x` of `S` is a torsion group.

If `F` is torsion, an element of a stalk is the germ of a section over an étale neighbourhood,
and that section is killed by a positive integer on the members of a covering sieve, one of
which carries a lift of the geometric point; so the germ is killed. Conversely, if every stalk is
torsion, for each point of an object `U` the germ of a section `s ∈ F(U)` at a geometric point
over it is killed by some `n`, hence `n • s` vanishes on an étale neighbourhood of that point;
these neighbourhoods are jointly surjective onto `U`, so they generate a covering sieve on whose
members `s` is killed by a positive integer.

## Main results

* `AlgebraicGeometry.SmallEtale.isTorsionSheaf_iff_forall_isAddTorsion_etaleStalk`: an abelian
  sheaf on the small étale site is a torsion sheaf if and only if all its stalks at geometric
  points are torsion groups.

## Implementation notes

Torsion sheaves are `AlgebraicGeometry.SmallEtale.IsTorsionSheaf`, the local notion; for a
locally noetherian `S` it agrees with Freitag and Kiehl's sectionwise one over noetherian
separated étale `S`-schemes by
`AlgebraicGeometry.SmallEtale.isTorsionSheaf_iff_forall_isAddTorsion`.
On that sectionwise form the converse direction is Freitag and Kiehl's argument through finitely
many neighbourhoods covering a quasi-compact object; on the local form no finiteness is needed.
Geometric points are `AlgebraicGeometry.GeometricPoint`, over algebraically closed fields, and
stalks are `AlgebraicGeometry.etaleStalk`, the colimit over étale neighbourhoods. The
coefficients live in the universe `max (u + 1) v`, where the stalks exist.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 0GJX](https://stacks.math.columbia.edu/tag/0GJX)
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A sheaf is torsion if and only if its stalks are.** An abelian sheaf on the small étale
site of `S` is a torsion sheaf if and only if its stalk at every geometric point of `S` is a
torsion group. -/
@[weil "lem_fk104_torsion_sheaf_iff_stalks_torsion"]
theorem isTorsionSheaf_iff_forall_isAddTorsion_etaleStalk
    (F : Sheaf (topology B S hS) AddCommGrpCat.{max (u + 1) v}) :
    IsTorsionSheaf B S hS F ↔
      ∀ t : GeometricPoint S, IsAddTorsion ↑(etaleStalk B S hS t F.obj) := by
  refine ⟨fun hF t g ↦ ?_, fun h ↦ ?_⟩
  · exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      (exists_nsmul_eq_zero_etaleStalk.{u, v} B S hS t F hF g)
  · exact torsionSheafProperty_of_forall_etaleStalk.{u, v} B S hS F fun t g ↦
      isOfFinAddOrder_iff_nsmul_eq_zero.mp (h t g)

end AlgebraicGeometry.SmallEtale

end
