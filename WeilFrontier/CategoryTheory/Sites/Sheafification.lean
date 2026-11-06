module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Sheafification is exact

Let `J` be a Grothendieck topology on a category `C` and `A` an abelian category in which
sheafification exists. If `P' ⟶ P ⟶ P''` is a sequence of presheaves which is exact at every
object `U` of `C`, then the sequence of associated sheaves is exact in the abelian category of
sheaves. Indeed, a sequence of presheaves which is exact at every object is exact in the
abelian category of presheaves (the evaluation functors are exact and jointly reflect
isomorphisms), and sheafification, being a left adjoint which preserves finite limits, is an
exact functor.

We specialise to presheaves of abelian groups on the small étale site of a scheme `X`, where
exactness at `U` is exactness of the sequence of abelian groups `P'(U) → P(U) → P''(U)`.

## Main results

* `CategoryTheory.Presheaf.exact_of_forall_exact_evaluation`: a short complex of presheaves
  which is exact at every object is exact.
* `CategoryTheory.Presheaf.exact_presheafToSheaf_map`: sheafification carries a sequence of
  presheaves, exact at every object, to an exact sequence of sheaves.
* `AlgebraicGeometry.SmallEtale.exact_presheafToSheaf_map`: the same for presheaves of
  abelian groups on the small étale site, with objectwise exactness stated as exactness of
  maps of abelian groups.

## Implementation notes

The small étale statement is made for abelian groups in an arbitrary universe `w` in which
sheafification on the small étale site exists. Instance search provides this both for `w = u`
(`AlgebraicGeometry.SmallEtale.hasSheafify`, the site being essentially small) and for
`w = u + 1` (the plus construction, the site being a `u + 1`-small category).

The sheaf associated to a presheaf is `CategoryTheory.presheafToSheaf`; for presheaves of
abelian groups it is canonically isomorphic to the plus construction applied twice
(`CategoryTheory.GrothendieckTopology.sheafify`), and exactness is invariant under
isomorphisms of short complexes.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public section

universe v v' u w

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Presheaf

variable {J : GrothendieckTopology C} {A : Type w} [Category.{v'} A] [Abelian A]
  [HasSheafify J A]

/-- A short complex of presheaves which is exact at every object is exact. -/
theorem exact_of_forall_exact_evaluation (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hS : ∀ U : Cᵒᵖ, (S.map ((evaluation Cᵒᵖ A).obj U)).Exact) : S.Exact :=
  have hJ : JointlyReflectIsomorphisms (fun U : Cᵒᵖ ↦ (evaluation Cᵒᵖ A).obj U) :=
    { isIso f h :=
        have (U : Cᵒᵖ) : IsIso (f.app U) := h U
        NatIso.isIso_of_isIso_app f }
  (hJ.exact_iff S).2 hS

/-- Sheafification carries a sequence of presheaves `P' ⟶ P ⟶ P''`, exact at every object,
to an exact sequence of sheaves `P'^♯ ⟶ P^♯ ⟶ P''^♯`. -/
theorem exact_presheafToSheaf_map (S : ShortComplex (Cᵒᵖ ⥤ A))
    (hS : ∀ U : Cᵒᵖ, (S.map ((evaluation Cᵒᵖ A).obj U)).Exact) :
    (S.map (presheafToSheaf J A)).Exact :=
  (exact_of_forall_exact_evaluation S hS).map _

end Presheaf

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- Let `P' ⟶ P ⟶ P''` be morphisms of presheaves of abelian groups on the small étale site
of `X` such that `P'(U) → P(U) → P''(U)` is exact for every `U`. Then the sequence of
associated sheaves is exact in the abelian category of étale sheaves of abelian groups. -/
@[weil "lem_fk102_sheafification_exact"]
theorem exact_presheafToSheaf_map [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{w}]
    {P' P P'' : (SmallEtale B X hX)ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (f : P' ⟶ P) (g : P ⟶ P'') (w : f ≫ g = 0)
    (h : ∀ U, Function.Exact (f.app U) (g.app U)) :
    (ShortComplex.mk ((presheafToSheaf (SmallEtale.topology B X hX) _).map f)
      ((presheafToSheaf (SmallEtale.topology B X hX) _).map g)
      (by rw [← Functor.map_comp, w, Functor.map_zero])).Exact :=
  Presheaf.exact_presheafToSheaf_map (ShortComplex.mk f g w) fun U ↦
    (ShortComplex.ab_exact_iff_function_exact _).2 (h U)

end AlgebraicGeometry.SmallEtale
