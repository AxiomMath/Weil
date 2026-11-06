module

public import Weil.Attr
public import Weil.CategoryTheory.Sites.PlusPresheafExistsUnique
public import Weil.Defs.CategoryTheory.Sites.PlusPresheaf
public import Weil.Defs.CategoryTheory.Sites.PlusUnit

/-!
# Naturality of the unit of the plus construction

Let `A` be a commutative ring, `F` a presheaf on the étale category `Et(A)` and `P` its plus
presheaf, with values `F̃(B)`. The maps `ι_{F,B} : F(B) → F̃(B)`, `s ↦ [(id_B), s]`, form a
morphism of presheaves `ι_F : F → F̃`. Indeed, for `f : B ⟶ B'` the pair `(id, (f))` is a
morphism of coverings `(id_B) ⟶ (id_{B'})` over `f`, inducing `F(f)` on sections, so
`F̃(f)(ι_{F,B}(s)) = [(id_{B'}), F(f)(s)] = ι_{F,B'}(F(f)(s))`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.toPlus P`: the morphism of presheaves
  `ι_F : F → F̃` for a presheaf of sets (`F` lifted to the universe of `F̃`).
- `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.toPlus P`: the morphism of presheaves of
  abelian groups `ι_F : F → F̃` (`F` lifted to the universe of `F̃`).

## Main results

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.map_toPlusConstruction`,
  `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.map_toAddPlusConstruction`:
  `F̃(f)(ι_{F,B}(s)) = ι_{F,B'}(F(f)(s))`.

## Implementation notes

The plus construction `F̃(B)` lives in a universe larger than that of `F(B)`, so the morphism of
presheaves `ι_F` has source the composite of `F` with the universe lift.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}} {B B' : EtaleCategory A}

namespace Covering

/-- The morphism of coverings `(id_B) ⟶ (id_{B'})` over `f : B ⟶ B'`: the identity of the index
set and the morphism `f`. -/
private def homOverSelf (f : B ⟶ B') : HomOver f (self.{w} B) (self.{w} B') where
  σ := id
  h _ := f
  comm _ := (Category.id_comp f).trans (Category.comp_id f).symm

@[simp]
private lemma homOverSelf_σ (f : B ⟶ B') (j : (self.{w} B').ι) :
    (homOverSelf.{w} f).σ j = j := rfl

@[simp]
private lemma homOverSelf_h (f : B ⟶ B') (j : (self.{w} B').ι) :
    (homOverSelf.{w} f).h j = f := rfl

end Covering

open Covering

namespace PlusPresheaf

variable {F : Presheaf A (Type v)} (P : PlusPresheaf.{w} F)

/-- **Naturality of `ι_F`** (presheaves of sets): `F̃(f)(ι_{F,B}(s)) = ι_{F,B'}(F(f)(s))`. -/
@[weil "lem_fk101_plus_unit_natural"]
theorem map_toPlusConstruction (f : B ⟶ B') (s : F.obj B) :
    P.map f (toPlusConstruction.{w} F B s) = toPlusConstruction.{w} F B' (F.map f s) := by
  rw [toPlusConstruction_apply, P.map_mk f _ _ (homOverSelf.{w} f), toPlusConstruction_apply]
  rfl

/-- **The morphism of presheaves `ι_F : F → F̃`** (presheaves of sets), with components
`ι_{F,B}`; `F` is lifted to the universe of `F̃`. -/
@[weil "lem_fk101_plus_unit_natural"]
def toPlus : F ⋙ uliftFunctor.{max (u + 1) (w + 1) v} ⟶ P.toPresheaf where
  app B := ↾fun s ↦ toPlusConstruction.{w} F B s.down
  naturality B B' f := by
    ext ⟨s⟩
    exact (P.map_toPlusConstruction f s).symm

@[simp]
lemma toPlus_app_apply (B : EtaleCategory A) (s : F.obj B) :
    P.toPlus.app B (ULift.up s) = toPlusConstruction.{w} F B s :=
  rfl

end PlusPresheaf

namespace AddPlusPresheaf

variable {F : Presheaf A AddCommGrpCat.{v}} (P : AddPlusPresheaf.{w} F)

/-- **Naturality of `ι_F`** (presheaves of abelian groups):
`F̃(f)(ι_{F,B}(s)) = ι_{F,B'}(F(f)(s))`. -/
@[weil "lem_fk101_plus_unit_natural"]
theorem map_toAddPlusConstruction (f : B ⟶ B') (s : F.obj B) :
    P.map f (toAddPlusConstruction.{w} F B s) = toAddPlusConstruction.{w} F B' (F.map f s) := by
  rw [toAddPlusConstruction_apply, P.map_mk f _ _ (homOverSelf.{w} f),
    toAddPlusConstruction_apply]
  rfl

/-- **The morphism of presheaves of abelian groups `ι_F : F → F̃`**, with components
`ι_{F,B}`; `F` is lifted to the universe of `F̃`. -/
@[weil "lem_fk101_plus_unit_natural"]
def toPlus : F ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) (w + 1) v} ⟶ P.toPresheaf where
  app B := AddCommGrpCat.ofHom
    ((toAddPlusConstruction.{w} F B).comp AddEquiv.ulift.toAddMonoidHom)
  naturality B B' f := by
    ext ⟨s⟩
    exact (P.map_toAddPlusConstruction f s).symm

@[simp]
lemma toPlus_app_apply (B : EtaleCategory A) (s : F.obj B) :
    P.toPlus.app B (ULift.up s) = toAddPlusConstruction.{w} F B s :=
  rfl

end AddPlusPresheaf

end EtaleCategory

end AlgebraicGeometry
