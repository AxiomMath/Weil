module

public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Colimits
public import Weil.Attr
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology

/-!
# The free abelian sheaf on a presheaf of sets

Let `(C, J)` be a site and `F` a presheaf of sets on `C`. The *free abelian sheaf* `F^ab` on `F`
is the sheafification of the presheaf of abelian groups `U ↦ ℤ^(F(U))`, the free abelian group
on the set `F(U)`, a morphism acting by the `ℤ`-linear extension of the restriction map of `F`.

The functor `F ↦ F^ab` is left adjoint to the functor sending a sheaf of abelian groups to its
underlying presheaf of sets: a morphism of abelian sheaves `F^ab ⟶ G` is the same as a morphism
of presheaves of sets `F ⟶ G`. For a representable presheaf `F = Hom(-, X)` this gives
`Hom(X^ab, G) ≃ G(X)`, and `X^ab` is isomorphic to Mathlib's `Sheaf.freeYoneda J X ℤ`.

## Main definitions

* `CategoryTheory.Presheaf.freeAbelianSheafObj`: the free abelian sheaf `F^ab` on `F`, the value
  at `F` of StacksFrontier's functor `CategoryTheory.Presheaf.freeAbelianSheaf`, whose left
  adjointness to the forgetful functor is `CategoryTheory.Presheaf.freeAbelianSheafAdj`.
* `CategoryTheory.Presheaf.freeAbelianSheafHomEquiv`: `(F^ab ⟶ G) ≃ (F ⟶ G ⋙ forget)`.
* `CategoryTheory.Presheaf.freeAbelianSheafYonedaHomEquiv`: `(Hom(-, X)^ab ⟶ G) ≃ G(X)`.

## Main results

* `CategoryTheory.Presheaf.freeAbelianSheafYonedaIsoFreeYoneda`: the free abelian sheaf on a
  representable presheaf is `Sheaf.freeYoneda J X ℤ`.

## Implementation notes

Freitag and Kiehl define `F^ab` for presheaves of sets on the étale site `Et(A)` of a ring; the
construction makes sense on any site, and the definitions here are stated for an arbitrary site
`(C, J)` with sheafification of abelian presheaves, in particular for the small étale site.
Sheafification is Mathlib's `presheafToSheaf`, which for concrete sites is the plus-plus
construction (`GrothendieckTopology.plusPlusIsoSheafify`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section General

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The free abelian sheaf `F^ab` on a presheaf of sets `F`: the sheafification of the presheaf
of abelian groups `U ↦ ℤ^(F(U))`, the free abelian group on `F(U)`. -/
@[weil "def_fk101_free_abelian_sheaf"]
abbrev freeAbelianSheafObj (F : Cᵒᵖ ⥤ Type w) : Sheaf J AddCommGrpCat.{w} :=
  (freeAbelianSheaf J).obj F

lemma freeAbelianSheaf_obj (F : Cᵒᵖ ⥤ Type w) :
    (freeAbelianSheaf J).obj F = freeAbelianSheafObj J F := rfl

/-- Morphisms of abelian sheaves `F^ab ⟶ G` correspond to morphisms of presheaves of sets from
`F` to the underlying presheaf of sets of `G`. -/
def freeAbelianSheafHomEquiv {F : Cᵒᵖ ⥤ Type w} {G : Sheaf J AddCommGrpCat.{w}} :
    (freeAbelianSheafObj J F ⟶ G) ≃ (F ⟶ G.obj ⋙ forget AddCommGrpCat.{w}) :=
  (freeAbelianSheafAdj J).homEquiv F G

/-- The canonical map of presheaves of sets `F ⟶ F^ab`, sending a section to the corresponding
generator. -/
def toFreeAbelianSheaf (F : Cᵒᵖ ⥤ Type w) :
    F ⟶ (freeAbelianSheafObj J F).obj ⋙ forget AddCommGrpCat.{w} :=
  (freeAbelianSheafAdj J).unit.app F

lemma freeAbelianSheafHomEquiv_apply {F : Cᵒᵖ ⥤ Type w} {G : Sheaf J AddCommGrpCat.{w}}
    (f : freeAbelianSheafObj J F ⟶ G) :
    freeAbelianSheafHomEquiv J f =
      toFreeAbelianSheaf J F ≫ Functor.whiskerRight f.hom (forget AddCommGrpCat.{w}) := by
  rw [freeAbelianSheafHomEquiv, Adjunction.homEquiv_unit]
  rfl

end General

section Representable

variable [HasSheafify J AddCommGrpCat.{v}]

/-- Morphisms from the free abelian sheaf on the representable presheaf `Hom(-, X)` to an
abelian sheaf `G` correspond to sections of `G` over `X`. -/
def freeAbelianSheafYonedaHomEquiv {X : C} {G : Sheaf J AddCommGrpCat.{v}} :
    (freeAbelianSheafObj J (yoneda.obj X) ⟶ G) ≃ G.obj.obj (op X) :=
  (freeAbelianSheafHomEquiv J).trans yonedaEquiv

lemma freeAbelianSheafYonedaHomEquiv_comp {X : C} {G G' : Sheaf J AddCommGrpCat.{v}}
    (f : freeAbelianSheafObj J (yoneda.obj X) ⟶ G) (g : G ⟶ G') :
    freeAbelianSheafYonedaHomEquiv J (f ≫ g) =
      g.hom.app (op X) (freeAbelianSheafYonedaHomEquiv J f) := by
  rfl

/-- Morphisms of abelian groups out of (a universe lift of) `ℤ` correspond to elements of the
target. -/
def _root_.AddCommGrpCat.homIntEquiv (M : AddCommGrpCat.{v}) :
    (AddCommGrpCat.of (ULift.{v} ℤ) ⟶ M) ≃ M where
  toFun f := f (ULift.up 1)
  invFun m :=
    AddCommGrpCat.ofHom ((zmultiplesHom M m).comp (AddEquiv.ulift (α := ℤ)).toAddMonoidHom)
  left_inv f := by
    ext ⟨n⟩
    change n • f (ULift.up 1) = f (ULift.up n)
    rw [← map_zsmul]
    congr 1
    ext
    simp
  right_inv m := one_zsmul (G := M) m

omit [HasSheafify J AddCommGrpCat.{v}] in
lemma _root_.CategoryTheory.Sheaf.freeYonedaHomEquiv_comp {A : Type*} [Category* A]
    [HasCoproducts.{v} A] [HasWeakSheafify J A] {X : C} {M : A} {G G' : Sheaf J A}
    (f : Sheaf.freeYoneda J X M ⟶ G) (g : G ⟶ G') :
    Sheaf.freeYonedaHomEquiv (f ≫ g) = Sheaf.freeYonedaHomEquiv f ≫ g.hom.app (op X) := by
  change Presheaf.freeYonedaHomEquiv ((sheafificationAdjunction J A).homEquiv _ _ (f ≫ g)) =
    Presheaf.freeYonedaHomEquiv ((sheafificationAdjunction J A).homEquiv _ _ f) ≫ g.hom.app (op X)
  have h := (sheafificationAdjunction J A).homEquiv_naturality_right
    (X := Presheaf.freeYoneda X M) (f : (presheafToSheaf J A).obj _ ⟶ G) g
  exact (congrArg Presheaf.freeYonedaHomEquiv h).trans (Presheaf.freeYonedaHomEquiv_comp _ _)

/-- The free abelian sheaf on the representable presheaf `Hom(-, X)` is Mathlib's
`Sheaf.freeYoneda J X ℤ`, the sheafification of `U ↦ ⊕_{Hom(U, X)} ℤ`. -/
@[no_expose]
def freeAbelianSheafYonedaIsoFreeYoneda (X : C) :
    freeAbelianSheafObj J (yoneda.obj X) ≅
      Sheaf.freeYoneda J X (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (Coyoneda.fullyFaithful.preimageIso
    (NatIso.ofComponents (fun G => Equiv.toIso
      ((Sheaf.freeYonedaHomEquiv.trans (AddCommGrpCat.homIntEquiv _)).trans
        (freeAbelianSheafYonedaHomEquiv J).symm)) (by
      intro G G' g
      ext f
      apply (freeAbelianSheafYonedaHomEquiv J).injective
      change (freeAbelianSheafYonedaHomEquiv J) ((freeAbelianSheafYonedaHomEquiv J).symm
          (AddCommGrpCat.homIntEquiv _ (Sheaf.freeYonedaHomEquiv (f ≫ g)))) =
        freeAbelianSheafYonedaHomEquiv J ((freeAbelianSheafYonedaHomEquiv J).symm
          (AddCommGrpCat.homIntEquiv _ (Sheaf.freeYonedaHomEquiv f)) ≫ g)
      rw [freeAbelianSheafYonedaHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        Sheaf.freeYonedaHomEquiv_comp J f g]
      rfl))).unop

end Representable

end CategoryTheory.Presheaf
