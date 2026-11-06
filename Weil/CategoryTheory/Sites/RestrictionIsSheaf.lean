module

public import Weil.Attr
public import Weil.CategoryTheory.Sites.Over
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtaleSheaf

/-!
# The restriction of an étale sheaf to an object of `Et(X)` is an étale sheaf

Let `U = (U, u)` be an object of the étale category `Et(X)` of noetherian separated étale
`X`-schemes, and `L` an étale sheaf on `Et(X)`. Its restriction `L|_U`, the presheaf on `Et(U)`
sending `v : V ⟶ U` to `L(V, u ∘ v)`, is an étale sheaf on `Et(U)`. Indeed the functor
`Et(U) ⥤ Et(X)/U` is an equivalence identifying the topology of `Et(U)` with that of the
localized site `Et(X)/U`, and the restriction of a sheaf to a localized site is a sheaf.

## Main definitions

* `AlgebraicGeometry.EtaleSheaf.restrict` — the restriction `L|_U` as an étale sheaf on `Et(U)`.

## Main results

* `AlgebraicGeometry.EtaleSheaf.isSheaf_restrict` — for an étale sheaf `L` on `Et(X)` with values
  in any category, the restricted presheaf `L|_U` is a sheaf for the étale topology of `Et(U)`.
* `AlgebraicGeometry.EtalePresheaf.IsEtaleSheaf.restrict` — the same in terms of the sheaf axioms
  a) and b) for presheaves of sets, for `X` locally noetherian.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace AlgebraicGeometry

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type v} [Category.{w} A]

namespace EtaleSheaf

/-- **The restriction of an étale sheaf is an étale sheaf.** For an étale sheaf `L` on `Et(S)`
with values in `A` and `U ∈ Et(S)`, the restricted presheaf `L|_U` on `Et(U)` is a sheaf for
the étale topology of `Et(U)`. -/
@[weil "lem_fk102_restriction_is_sheaf"]
theorem isSheaf_restrict (L : EtaleSheaf B S hS A) (U : SmallNoetherianSeparatedEtale B S hS) :
    Presheaf.IsSheaf (topology B U.obj.obj.left.1 U.obj.obj.left.property)
      (EtalePresheaf.restrict L.obj U) :=
  SmallNoetherianSeparatedEtale.isSheaf_restrict U A L

/-- The restriction `L|_U` of an étale sheaf `L` on `Et(S)` to `U ∈ Et(S)`, as an étale sheaf
on `Et(U)`. -/
abbrev restrict (L : EtaleSheaf B S hS A) (U : SmallNoetherianSeparatedEtale B S hS) :
    EtaleSheaf B U.obj.obj.left.1 U.obj.obj.left.property A :=
  ⟨EtalePresheaf.restrict L.obj U, isSheaf_restrict L U⟩

lemma restrict_eq_restrictSheafFunctor_obj (L : EtaleSheaf B S hS A)
    (U : SmallNoetherianSeparatedEtale B S hS) :
    restrict L U = (restrictSheafFunctor U A).obj L :=
  rfl

end EtaleSheaf

namespace EtalePresheaf

/-- **The restriction of an étale sheaf of sets is an étale sheaf**, in terms of the sheaf
axioms a) and b): for `S` locally noetherian, a presheaf of sets `L` on `Et(S)` satisfying them
and `U ∈ Et(S)`, the restriction `L|_U` on `Et(U)` satisfies them. -/
@[weil "lem_fk102_restriction_is_sheaf"]
theorem IsEtaleSheaf.restrict [IsLocallyNoetherian S] {L : EtalePresheaf B S hS (Type v)}
    (hL : IsEtaleSheaf L) (U : SmallNoetherianSeparatedEtale B S hS) :
    IsEtaleSheaf (EtalePresheaf.restrict L U) :=
  have : IsLocallyNoetherian U.obj.obj.left.1 :=
    inferInstanceAs (IsLocallyNoetherian ((toScheme B S hS).obj U))
  (isSheaf_topology_iff_isEtaleSheaf _).mp
    (EtaleSheaf.isSheaf_restrict (EtaleSheaf.ofIsEtaleSheaf L hL) U)

end EtalePresheaf

end AlgebraicGeometry

end
