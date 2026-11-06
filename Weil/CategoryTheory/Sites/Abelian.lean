module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.CategoryTheory.Functor.ReflectsIso.Exact
public import Weil.Attr

/-!
# Left exactness of sheaves is left exactness of presheaves

Let `J` be a Grothendieck topology on a category `C` and `D` an abelian category for which
sheafification exists. A sequence `0 ⟶ F ⟶ G ⟶ H` of sheaves with values in `D` is exact in the
abelian category of sheaves if and only if it is exact in the abelian category of presheaves.
Indeed, in either category, exactness of `0 ⟶ F ⟶ G ⟶ H` means that `F ⟶ G` is a kernel of
`G ⟶ H`; the forgetful functor from sheaves to presheaves is fully faithful, so it reflects
limits, and it is a right adjoint, so it preserves them.

For sheaves of abelian groups on the small étale site of a scheme, combined with
`AlgebraicGeometry.SmallEtale.exact_iff_forall_function_exact`, this says that
`0 ⟶ F ⟶ G ⟶ H` is exact if and only if `0 → F(U) → G(U) → H(U)` is an exact sequence of
abelian groups for every object `U`.

## Main results

* `CategoryTheory.Sheaf.exact_and_mono_iff_exact_and_mono_hom`: a sequence `0 ⟶ F ⟶ G ⟶ H` of
  sheaves is exact if and only if the underlying sequence of presheaves is exact.
* `AlgebraicGeometry.SmallEtale.sheaf_exact_and_mono_iff_forall`: for abelian sheaves on the small
  étale site, exactness of `0 ⟶ F ⟶ G ⟶ H` is checked on sections over every object.

## Implementation notes

Exactness of `0 ⟶ F ⟶ G ⟶ H` is expressed as exactness of the short complex `F ⟶ G ⟶ H`
together with the monomorphy of `F ⟶ G`. The general statement holds over an arbitrary site;
the étale category `Et(A)` of a ring `A` is the case `J = Scheme.AffineEtale.topology (Spec A)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

public section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type*} [Category D] [Abelian D] [HasSheafify J D]

/-- **Left exactness of sheaves is left exactness of presheaves.** A sequence `0 ⟶ F ⟶ G ⟶ H` of
sheaves with values in an abelian category is exact in the category of sheaves if and only if it
is exact in the category of presheaves. -/
@[weil "lem_fk101_sheaf_left_exact_iff_presheaf_left_exact"]
theorem exact_and_mono_iff_exact_and_mono_hom {F G H : Sheaf J D} (α : F ⟶ G) (β : G ⟶ H)
    (w : α ≫ β = 0) :
    ((ShortComplex.mk α β w).Exact ∧ Mono α) ↔
      ((ShortComplex.mk α.hom β.hom (by simpa using (sheafToPresheaf J D).congr_map w)).Exact ∧
        Mono α.hom) := by
  rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel,
    ShortComplex.exact_and_mono_f_iff_f_is_kernel]
  constructor
  · rintro ⟨h⟩
    exact ⟨isLimitForkMapOfIsLimit (sheafToPresheaf J D) _ h⟩
  · rintro ⟨h⟩
    refine ⟨isLimitOfReflects (sheafToPresheaf J D) ?_⟩
    exact (isLimitMapConeForkEquiv (sheafToPresheaf J D) _).symm h

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Left exactness of étale sheaves is checked on sections.** A sequence `0 ⟶ F ⟶ G ⟶ H` of
sheaves of abelian groups on the small étale site of `S` is exact in the category of sheaves if
and only if `0 → F(U) → G(U) → H(U)` is an exact sequence of abelian groups for every object
`U`. -/
@[weil "lem_fk101_sheaf_left_exact_iff_presheaf_left_exact"]
theorem sheaf_exact_and_mono_iff_forall
    {F G H : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u}} (α : F ⟶ G) (β : G ⟶ H)
    (w : α ≫ β = 0) :
    ((ShortComplex.mk α β w).Exact ∧ Mono α) ↔
      ∀ U, Function.Injective (α.hom.app U) ∧ Function.Exact (α.hom.app U) (β.hom.app U) := by
  rw [Sheaf.exact_and_mono_iff_exact_and_mono_hom, exact_iff_forall_function_exact,
    NatTrans.mono_iff_mono_app]
  simp only [AddCommGrpCat.mono_iff_injective]
  exact ⟨fun h U ↦ ⟨h.2 U, h.1 U⟩, fun h ↦ ⟨fun U ↦ (h U).2, fun U ↦ (h U).1⟩⟩

end AlgebraicGeometry.SmallEtale

end
