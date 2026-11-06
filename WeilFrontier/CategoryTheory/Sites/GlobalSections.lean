module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import Weil.Attr

/-!
# Global sections of étale sheaves are additive and left exact

Let `S` be a scheme in a big étale site `B`, and let `Et(S)` be the small étale site of `S`.
The global sections functor `Γ(S, -) : Sh(Et(S), Ab) ⥤ Ab` sends a sheaf `F` to its value
`F(S)` on the final object `S → S` of `Et(S)`. It is additive and left exact.

Both properties hold for evaluation at any object of any site: the forgetful functor from
sheaves to presheaves is additive and preserves all limits (limits of sheaves are computed
objectwise), and evaluation of presheaves at an object is additive and preserves all limits.

## Main results

* `CategoryTheory.sheafSections_obj_additive'`,
  `CategoryTheory.sheafSections_obj_preservesFiniteLimits`: evaluation of sheaves at an object
  of a site is additive and preserves finite limits.
* `AlgebraicGeometry.SmallEtale.globalSections`: the functor `F ↦ F(S)` on abelian étale
  sheaves on `S`.
* `AlgebraicGeometry.SmallEtale.globalSections_additive`,
  `AlgebraicGeometry.SmallEtale.globalSections_preservesFiniteLimits`: it is additive and
  left exact.
* `AlgebraicGeometry.SmallEtale.globalSections_exact_of_exact`: it sends a left exact sequence
  `0 → F' → F → F''` of sheaves to a left exact sequence of abelian groups.

## Implementation notes

Left exactness of a functor is `Functor.PreservesFiniteLimits`; for an additive functor between
abelian categories this is equivalent to sending `0 → F' → F → F''` exact to an exact
sequence, which is `AlgebraicGeometry.SmallEtale.globalSections_exact_of_exact`.

The functor `globalSections` is evaluation at `SmallEtale.final B S hS`; Mathlib's `Sheaf.Γ`
(the right adjoint of the constant sheaf functor) is isomorphic to it by
`Sheaf.ΓNatIsoSheafSections`, since `SmallEtale.final B S hS` is terminal.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Evaluation of sheaves with values in a preadditive category at an object is additive.
StacksFrontier's `CategoryTheory.sheafSections_obj_additive` states this only at objects of the form
`op U`. -/
instance sheafSections_obj_additive' (A : Type*) [Category A] [Preadditive A] (U : Cᵒᵖ) :
    ((sheafSections J A).obj U).Additive where
  map_add := rfl

/-- Evaluation of sheaves at an object preserves finite limits, since limits of sheaves are
computed objectwise. -/
instance sheafSections_obj_preservesFiniteLimits (A : Type*) [Category A] [HasFiniteLimits A]
    (U : Cᵒᵖ) : PreservesFiniteLimits ((sheafSections J A).obj U) := by
  change PreservesFiniteLimits (sheafToPresheaf J A ⋙ (evaluation _ _).obj U)
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The global sections functor `Γ(S, -) : Sh(Et(S), Ab) ⥤ Ab`, `F ↦ F(S)`, evaluation of
an abelian étale sheaf on `S` at the final object `S → S` of the small étale site. -/
noncomputable abbrev SmallEtale.globalSections :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} :=
  (sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{w}).obj
    (op (SmallEtale.final B S hS))

/-- The global sections functor of abelian étale sheaves is additive. -/
@[weil "lem_fk102_global_sections_left_exact"]
instance SmallEtale.globalSections_additive :
    (SmallEtale.globalSections.{w} B S hS).Additive :=
  inferInstance

/-- The global sections functor of abelian étale sheaves is left exact. -/
@[weil "lem_fk102_global_sections_left_exact"]
instance SmallEtale.globalSections_preservesFiniteLimits :
    PreservesFiniteLimits (SmallEtale.globalSections.{w} B S hS) :=
  inferInstance

/-- The global sections functor sends a left exact sequence `0 → F' → F → F''` of abelian
étale sheaves to a left exact sequence `0 → F'(S) → F(S) → F''(S)` of abelian groups. -/
theorem SmallEtale.globalSections_exact_of_exact
    [HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{w}]
    (T : ShortComplex (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{w}))
    (hT : T.Exact) [Mono T.f] :
    (T.map (SmallEtale.globalSections.{w} B S hS)).Exact ∧
      Mono ((SmallEtale.globalSections.{w} B S hS).map T.f) :=
  ⟨hT.map_of_mono_of_preservesKernel _ inferInstance inferInstance, inferInstance⟩

end AlgebraicGeometry
