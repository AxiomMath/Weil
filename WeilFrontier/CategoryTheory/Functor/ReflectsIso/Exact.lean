module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf
public import Weil.Attr

/-!
# Exactness of presheaves of abelian groups is checked objectwise

A sequence `F ⟶ G ⟶ H` of presheaves of abelian groups (with vanishing composite) is exact in the
abelian category of presheaves if and only if `F(U) → G(U) → H(U)` is an exact sequence of
abelian groups for every object `U`. The category of presheaves is a functor category, in which
kernels and cokernels, hence homology, are computed objectwise; so the evaluation functors are
exact and jointly reflect isomorphisms, and therefore jointly detect exactness.

## Main results

* `CategoryTheory.ShortComplex.exact_iff_forall_function_exact_app`: the statement for presheaves
  of abelian groups on an arbitrary category.
* `AlgebraicGeometry.EtalePresheaf.exact_iff_forall_function_exact`: the statement for presheaves
  of abelian groups on the étale category `Et(S)`.
* `AlgebraicGeometry.SmallEtale.exact_iff_forall_function_exact`: the statement for presheaves
  of abelian groups on the small étale site `SmallEtale B S hS`.

## Implementation notes

Exactness of a sequence of abelian groups is `Function.Exact` (the kernel of the second map is the
image of the first), and exactness of the sequence of presheaves is exactness of the
`ShortComplex` it defines in the abelian functor category. The composite of the two maps is
assumed to vanish, as a short complex requires; it follows from either side of the equivalence.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1][FreitagKiehl]
-/

public section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.ShortComplex

variable {J : Type u} [Category.{v} J]

/-- A sequence `F ⟶ G ⟶ H` of presheaves of abelian groups on a category `J` is exact if and only
if `F(U) → G(U) → H(U)` is exact for every object `U`. -/
theorem exact_iff_forall_function_exact_app {F G H : Jᵒᵖ ⥤ AddCommGrpCat.{w}}
    (α : F ⟶ G) (β : G ⟶ H) (hαβ : α ≫ β = 0) :
    (ShortComplex.mk α β hαβ).Exact ↔ ∀ U : Jᵒᵖ, Function.Exact (α.app U) (β.app U) := by
  have hP : JointlyReflectIsomorphisms (fun U : Jᵒᵖ ↦ (evaluation Jᵒᵖ AddCommGrpCat.{w}).obj U) :=
    ⟨fun f h ↦ by
      have : ∀ U : Jᵒᵖ, IsIso (f.app U) := h
      exact NatIso.isIso_of_isIso_app f⟩
  rw [hP.exact_iff]
  exact forall_congr' fun U ↦ ShortComplex.ab_exact_iff_function_exact _

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Exactness of presheaves on `Et(S)` is objectwise.** A sequence `F ⟶ G ⟶ H` of presheaves of
abelian groups on the étale category `Et(S)` is exact if and only if `F(U) → G(U) → H(U)` is exact
for every object `U` of `Et(S)`. -/
@[weil "lem_fk101_presheaf_exact_iff_objectwise"]
theorem EtalePresheaf.exact_iff_forall_function_exact
    {F G H : EtalePresheaf B S hS AddCommGrpCat.{w}} (α : F ⟶ G) (β : G ⟶ H) (hαβ : α ≫ β = 0) :
    (ShortComplex.mk α β hαβ).Exact ↔ ∀ U, Function.Exact (α.app U) (β.app U) :=
  ShortComplex.exact_iff_forall_function_exact_app α β hαβ

/-- **Exactness of presheaves on the small étale site is objectwise.** A sequence `F ⟶ G ⟶ H` of
presheaves of abelian groups on `SmallEtale B S hS` is exact if and only if `F(U) → G(U) → H(U)`
is exact for every object `U`. -/
@[weil "lem_fk101_presheaf_exact_iff_objectwise"]
theorem SmallEtale.exact_iff_forall_function_exact
    {F G H : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{w}} (α : F ⟶ G) (β : G ⟶ H)
    (hαβ : α ≫ β = 0) :
    (ShortComplex.mk α β hαβ).Exact ↔ ∀ U, Function.Exact (α.app U) (β.app U) :=
  ShortComplex.exact_iff_forall_function_exact_app α β hαβ

end AlgebraicGeometry

end
