module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import StacksFrontier.Homology.Ext.MapExactFunctorComp
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.PullbackAsAMorphismOfDeltaFunctors

/-!
# Pullback on the cohomology of abelian sheaves on topological spaces

Let `f : X ⟶ Y` be a continuous map of topological spaces and `F` an abelian sheaf on `Y`. The
inverse image `f⁻¹` of abelian sheaves is exact, and it carries the constant sheaf `ℤ_Y` to the
constant sheaf `ℤ_X`. Since `Hⁿ(Y, F) = Extⁿ(ℤ_Y, F)`, applying `f⁻¹` to `Ext`-classes and
composing with `ℤ_X ≅ f⁻¹ ℤ_Y` gives the pullback map
`f^* : Hⁿ(Y, F) → Hⁿ(X, f⁻¹ F)`.
This file constructs it, proves that it is natural in `F` and functorial in `f`, and deduces the
pullback `Hⁿ(Y, M) → Hⁿ(X, M)` with coefficients in a constant sheaf, which is strictly
functorial: `(g ≫ f)^* = g^* ∘ f^*` and `(𝟙 X)^* = id`. For a retract
`i : A ⟶ X`, `r : X ⟶ A` with `i ≫ r = 𝟙 A`, the map `r^*` is a split injection, `Hⁿ(A, M)` is a
direct summand of `Hⁿ(X, M)`, and finite generation passes from `Hⁿ(X, M)` to `Hⁿ(A, M)`.

## Main definitions

* `TopCat.SheafCohomology.constantSheafIsoPullback f : constantSheaf ≅ constantSheaf ⋙ f⁻¹`: the
  identification `M_X ≅ f⁻¹ M_Y` of constant sheaves, natural in the abelian group `M`. Both
  functors are left adjoint to global sections on `X`, and this is the comparison of left
  adjoints.
* `TopCat.SheafCohomology.pullbackCompIso f g : (g ≫ f)⁻¹ ≅ f⁻¹ ⋙ g⁻¹` and
  `TopCat.SheafCohomology.pullbackIdIso X : (𝟙 X)⁻¹ ≅ 𝟭`: the comparison of inverse images, again
  as comparisons of left adjoints of the pushforwards.
* `TopCat.SheafCohomology.cohomologyPullback f F n : Hⁿ(Y, F) →+ Hⁿ(X, f⁻¹ F)`.
* `TopCat.SheafCohomology.constantCohomologyPullback f M n : Hⁿ(Y, M_Y) →+ Hⁿ(X, M_X)`.

## Main results

* `TopCat.SheafCohomology.cohomologyPullback_map`: naturality in the sheaf.
* `TopCat.SheafCohomology.cohomologyPullback_id`, `TopCat.SheafCohomology.cohomologyPullback_comp`:
  functoriality in the map, up to `pullbackIdIso` and `pullbackCompIso`.
* `TopCat.SheafCohomology.constantCohomologyPullback_id`,
  `TopCat.SheafCohomology.constantCohomologyPullback_comp`: strict functoriality with constant
  coefficients; `TopCat.SheafCohomology.constantCohomologyPullback_map_coefficients`: naturality in
  the coefficient group.
* `TopCat.SheafCohomology.constantCohomologyPullback_leftInverse_of_retract`,
  `TopCat.SheafCohomology.isCompl_range_ker_of_retract`,
  `TopCat.SheafCohomology.addGroupFG_of_retract`, `TopCat.SheafCohomology.moduleFinite_of_retract`:
  the cohomology of a retract is a direct summand, and inherits finite generation.

## Implementation notes

Cohomology is `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf `ULift ℤ`, on
the site `Opens.grothendieckTopology X`. The inverse image is
`Stacks.Cohomology.AbelianColimit.sheafPullback`, which is `TopCat.Sheaf.pullback` at the site
spelling of the sheaf category, together with its exactness instances.

The functoriality of acting on `Ext` by an exact functor, in the functor, is
`Stacks.Homology.ext_mapExactFunctor_comp_functor`, `Stacks.Homology.ext_mapExactFunctor_id` and
`Stacks.Homology.ext_mapExactFunctor_of_iso`. The only further input is the compatibility of the
identifications `M_X ≅ f⁻¹ M_Y` with `pullbackCompIso` and `pullbackIdIso`
(`constantSheafIsoPullback_comp`, `constantSheafIsoPullback_id`), which is checked after
transposing along the adjunction between constant sheaves and global sections.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian Opposite
open Stacks.Cohomology.AbelianColimit (sheafPullback)

universe u

namespace TopCat.SheafCohomology

variable {X Y Z : TopCat.{u}}

set_option quotPrecheck false in
/-- Abelian sheaves on a topological space, at the site spelling. -/
local notation "Sh(" X ")" => CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat
set_option quotPrecheck false in
/-- The constant sheaf functor on a topological space. -/
local notation "c(" X ")" => constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat
set_option quotPrecheck false in
/-- Global sections on a topological space. -/
local notation "Γ(" X ")" =>
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤)

/-! ### Constant sheaves and inverse images as left adjoints -/

/-- The adjunction between the constant sheaf functor and global sections. -/
abbrev constantSheafAdjunction (X : TopCat.{u}) : c(X) ⊣ Γ(X) :=
  constantSheafAdj _ _ isTerminalTop

/-- The pushforward of abelian sheaves along a continuous map, at the site spelling. -/
abbrev sheafPushforward (f : X ⟶ Y) : Sh(X) ⥤ Sh(Y) :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f

/-- The adjunction between inverse image and pushforward of abelian sheaves. -/
abbrev pullbackAdjunction (f : X ⟶ Y) : sheafPullback f ⊣ sheafPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction _ f

/-- `M ↦ f⁻¹ M_Y` is left adjoint to global sections on `X`, since global sections of `f_* G`
are global sections of `G`. -/
def constantPullbackAdjunction (f : X ⟶ Y) : c(Y) ⋙ sheafPullback f ⊣ Γ(X) :=
  (constantSheafAdjunction Y).comp (pullbackAdjunction f)

theorem constantPullbackAdjunction_unit_app (f : X ⟶ Y) (A : AddCommGrpCat.{u}) :
    (constantPullbackAdjunction f).unit.app A =
      (constantSheafAdjunction Y).unit.app A ≫
        Γ(Y).map ((pullbackAdjunction f).unit.app (c(Y).obj A)) :=
  Adjunction.comp_unit_app _ _ _

/-- `f⁻¹ ⋙ g⁻¹` is left adjoint to the pushforward along `g ≫ f`. -/
def pullbackCompAdjunction (f : X ⟶ Y) (g : Z ⟶ X) :
    sheafPullback f ⋙ sheafPullback g ⊣ sheafPushforward (g ≫ f) :=
  (pullbackAdjunction f).comp (pullbackAdjunction g)

theorem pullbackCompAdjunction_unit_app (f : X ⟶ Y) (g : Z ⟶ X) (F : Sh(Y)) :
    (pullbackCompAdjunction f g).unit.app F =
      (pullbackAdjunction f).unit.app F ≫
        (sheafPushforward f).map ((pullbackAdjunction g).unit.app ((sheafPullback f).obj F)) :=
  Adjunction.comp_unit_app _ _ _

/-- The identity functor is left adjoint to the pushforward along the identity. -/
def idAdjunction (X : TopCat.{u}) : 𝟭 Sh(X) ⊣ sheafPushforward (𝟙 X) :=
  Adjunction.id

/-- **The constant sheaf is preserved by inverse images**: `M_X ≅ f⁻¹ M_Y`, naturally in `M`. -/
def constantSheafIsoPullback (f : X ⟶ Y) : c(X) ≅ c(Y) ⋙ sheafPullback f :=
  (constantSheafAdjunction X).leftAdjointUniq (constantPullbackAdjunction f)

/-- The inverse image along a composite is the composite of the inverse images. -/
def pullbackCompIso (f : X ⟶ Y) (g : Z ⟶ X) :
    sheafPullback (g ≫ f) ≅ sheafPullback f ⋙ sheafPullback g :=
  (pullbackAdjunction (g ≫ f)).leftAdjointUniq (pullbackCompAdjunction f g)

/-- The inverse image along the identity is the identity. -/
def pullbackIdIso (X : TopCat.{u}) : sheafPullback (𝟙 X) ≅ 𝟭 _ :=
  (pullbackAdjunction (𝟙 X)).leftAdjointUniq (idAdjunction X)

theorem pullbackCompIso_unit (f : X ⟶ Y) (g : Z ⟶ X) (F : Sh(Y)) :
    (pullbackAdjunction (g ≫ f)).unit.app F ≫
        (sheafPushforward (g ≫ f)).map ((pullbackCompIso f g).hom.app F) =
      (pullbackAdjunction f).unit.app F ≫
        (sheafPushforward f).map ((pullbackAdjunction g).unit.app ((sheafPullback f).obj F)) := by
  rw [pullbackCompIso, Adjunction.unit_leftAdjointUniq_hom_app, pullbackCompAdjunction_unit_app]

theorem pullbackIdIso_unit (F : Sh(X)) :
    (pullbackAdjunction (𝟙 X)).unit.app F ≫
        (sheafPushforward (𝟙 X)).map ((pullbackIdIso X).hom.app F) = 𝟙 F := by
  rw [pullbackIdIso, Adjunction.unit_leftAdjointUniq_hom_app]
  rfl

theorem constantSheafIsoPullback_unit (f : X ⟶ Y) (A : AddCommGrpCat.{u}) :
    (constantSheafAdjunction X).unit.app A ≫ Γ(X).map ((constantSheafIsoPullback f).hom.app A) =
      (constantSheafAdjunction Y).unit.app A ≫
        Γ(Y).map ((pullbackAdjunction f).unit.app (c(Y).obj A)) := by
  rw [constantSheafIsoPullback, Adjunction.unit_leftAdjointUniq_hom_app,
    constantPullbackAdjunction_unit_app]

/-- **Compatibility of `M_X ≅ f⁻¹ M_Y` with composition**: the two identifications
`M_Z ≅ (g ≫ f)⁻¹ M_Y ≅ g⁻¹ f⁻¹ M_Y` and `M_Z ≅ g⁻¹ M_X ≅ g⁻¹ f⁻¹ M_Y` agree. -/
theorem constantSheafIsoPullback_comp (f : X ⟶ Y) (g : Z ⟶ X) (A : AddCommGrpCat.{u}) :
    (constantSheafIsoPullback (g ≫ f)).hom.app A ≫ (pullbackCompIso f g).hom.app (c(Y).obj A) =
      (constantSheafIsoPullback g).hom.app A ≫
        (sheafPullback g).map ((constantSheafIsoPullback f).hom.app A) := by
  apply ((constantSheafAdjunction Z).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  let uY := (constantSheafAdjunction Y).unit.app A
  let uX := (constantSheafAdjunction X).unit.app A
  let uZ := (constantSheafAdjunction Z).unit.app A
  let ef := (constantSheafIsoPullback f).hom.app A
  let eg := (constantSheafIsoPullback g).hom.app A
  let egf := (constantSheafIsoPullback (g ≫ f)).hom.app A
  let α := (pullbackCompIso f g).hom.app (c(Y).obj A)
  calc (uZ ≫ Γ(Z).map (egf ≫ α) :
        A ⟶ Γ(Z).obj ((sheafPullback f ⋙ sheafPullback g).obj (c(Y).obj A)))
      = ((uZ ≫ Γ(Z).map egf) ≫ Γ(Z).map α :
          A ⟶ Γ(Z).obj ((sheafPullback f ⋙ sheafPullback g).obj (c(Y).obj A))) := by
          rw [Functor.map_comp, Category.assoc]
    _ = ((uY ≫ Γ(Y).map ((pullbackAdjunction (g ≫ f)).unit.app (c(Y).obj A))) ≫
          Γ(Z).map α :
          A ⟶ Γ(Z).obj ((sheafPullback f ⋙ sheafPullback g).obj (c(Y).obj A))) := by
          rw [constantSheafIsoPullback_unit]; rfl
    _ = (uY ≫ Γ(Y).map ((pullbackAdjunction (g ≫ f)).unit.app (c(Y).obj A) ≫
          (sheafPushforward (g ≫ f)).map α) :
          A ⟶ Γ(Z).obj ((sheafPullback f ⋙ sheafPullback g).obj (c(Y).obj A))) := by
          simp only [Functor.map_comp]; rfl
    _ = (uY ≫ Γ(Y).map ((pullbackAdjunction f).unit.app (c(Y).obj A) ≫
          (sheafPushforward f).map ((pullbackAdjunction g).unit.app
            ((sheafPullback f).obj (c(Y).obj A)))) :
          A ⟶ Γ(Z).obj ((sheafPullback f ⋙ sheafPullback g).obj (c(Y).obj A))) := by
          rw [pullbackCompIso_unit]; rfl
    _ = ((uX ≫ Γ(X).map ef) ≫ Γ(X).map ((pullbackAdjunction g).unit.app
            ((sheafPullback f).obj (c(Y).obj A))) :
          A ⟶ Γ(Z).obj ((sheafPullback f ⋙ sheafPullback g).obj (c(Y).obj A))) := by
          rw [constantSheafIsoPullback_unit]; simp only [Functor.map_comp]; rfl
    _ = (uX ≫ Γ(X).map ((pullbackAdjunction g).unit.app (c(X).obj A) ≫
          (sheafPushforward g).map ((sheafPullback g).map ef)) :
          A ⟶ Γ(Z).obj ((sheafPullback f ⋙ sheafPullback g).obj (c(Y).obj A))) :=
          (Category.assoc _ _ _).trans (congrArg (uX ≫ ·)
            ((Γ(X).map_comp _ _).symm.trans (congrArg Γ(X).map
              ((pullbackAdjunction g).unit.naturality ef))))
    _ = ((uZ ≫ Γ(Z).map eg) ≫ Γ(Z).map ((sheafPullback g).map ef) :
          A ⟶ Γ(Z).obj ((sheafPullback f ⋙ sheafPullback g).obj (c(Y).obj A))) := by
          rw [constantSheafIsoPullback_unit]; simp only [Functor.map_comp]; rfl
    _ = (uZ ≫ Γ(Z).map (eg ≫ (sheafPullback g).map ef) :
          A ⟶ Γ(Z).obj ((sheafPullback f ⋙ sheafPullback g).obj (c(Y).obj A))) := by
          rw [Functor.map_comp, Category.assoc]

/-- **Compatibility of `M_X ≅ f⁻¹ M_Y` with the identity**: `M_X ≅ (𝟙 X)⁻¹ M_X ≅ M_X` is the
identity. -/
theorem constantSheafIsoPullback_id (A : AddCommGrpCat.{u}) :
    (constantSheafIsoPullback (𝟙 X)).hom.app A ≫ (pullbackIdIso X).hom.app _ = 𝟙 _ := by
  apply ((constantSheafAdjunction X).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h := constantSheafIsoPullback_unit (𝟙 X) A
  exact (congrArg _ (Γ(X).map_comp _ _)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Γ(X).map ((pullbackIdIso X).hom.app (c(X).obj A))) h).trans
      ((Category.assoc _ _ _).trans (congrArg _ (((Γ(X).map_comp _ _).symm.trans
        (congrArg Γ(X).map (pullbackIdIso_unit _))))))))

theorem constantSheafIsoPullback_comp_inv (f : X ⟶ Y) (g : Z ⟶ X) (A : AddCommGrpCat.{u}) :
    (pullbackCompIso f g).inv.app (c(Y).obj A) ≫ (constantSheafIsoPullback (g ≫ f)).inv.app A =
      (sheafPullback g).map ((constantSheafIsoPullback f).inv.app A) ≫
        (constantSheafIsoPullback g).inv.app A := by
  have := congrArg Iso.inv (Iso.ext (α := (constantSheafIsoPullback (g ≫ f)).app A ≪≫
    (pullbackCompIso f g).app (c(Y).obj A)) (β := (constantSheafIsoPullback g).app A ≪≫
      (sheafPullback g).mapIso ((constantSheafIsoPullback f).app A))
        (constantSheafIsoPullback_comp f g A))
  simpa using this

theorem constantSheafIsoPullback_id_inv (A : AddCommGrpCat.{u}) :
    (pullbackIdIso X).inv.app (c(X).obj A) ≫ (constantSheafIsoPullback (𝟙 X)).inv.app A =
      𝟙 _ := by
  have := congrArg Iso.inv (Iso.ext (α := (constantSheafIsoPullback (𝟙 X)).app A ≪≫
    (pullbackIdIso X).app (c(X).obj A)) (β := Iso.refl _) (constantSheafIsoPullback_id A))
  simpa using this

/-! ### The pullback map on cohomology -/

/-- **The pullback map on sheaf cohomology** `Hⁿ(Y, F) → Hⁿ(X, f⁻¹ F)` along a continuous map
`f : X ⟶ Y`: apply the exact functor `f⁻¹` to a class in `Extⁿ(ℤ_Y, F)` and precompose with
`ℤ_X ≅ f⁻¹ ℤ_Y`. -/
def cohomologyPullback (f : X ⟶ Y) (F : Sh(Y)) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} F n →+ CategoryTheory.Sheaf.H.{u} ((sheafPullback f).obj F) n :=
  ((Ext.mk₀ ((constantSheafIsoPullback f).hom.app (AddCommGrpCat.of (ULift ℤ)))).precomp _
    (zero_add n)).comp ((sheafPullback f).mapExtAddHom _ _ n)

theorem cohomologyPullback_apply (f : X ⟶ Y) (F : Sh(Y)) (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} F n) :
    cohomologyPullback f F n x =
      (Ext.mk₀ ((constantSheafIsoPullback f).hom.app (AddCommGrpCat.of (ULift ℤ)))).comp
        (x.mapExactFunctor (sheafPullback f)) (zero_add n) := rfl

/-- The pullback map is natural in the sheaf. -/
theorem cohomologyPullback_map (f : X ⟶ Y) {F G : Sh(Y)} (φ : F ⟶ G) (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} F n) :
    cohomologyPullback f G n (CategoryTheory.Sheaf.H.map φ n x) =
      CategoryTheory.Sheaf.H.map ((sheafPullback f).map φ) n (cohomologyPullback f F n x) := by
  rw [cohomologyPullback_apply, cohomologyPullback_apply, CategoryTheory.Sheaf.H.map_apply,
    CategoryTheory.Sheaf.H.map_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

/-- The pullback map along the identity is the identity, up to `(𝟙 X)⁻¹ F ≅ F`. -/
theorem cohomologyPullback_id (F : Sh(X)) (n : ℕ) (x : CategoryTheory.Sheaf.H.{u} F n) :
    cohomologyPullback (𝟙 X) F n x =
      CategoryTheory.Sheaf.H.map ((pullbackIdIso X).inv.app F) n x := by
  rw [cohomologyPullback_apply, Stacks.Homology.ext_mapExactFunctor_of_iso (𝟭 _) _
    (pullbackIdIso X).symm _ n F x, Stacks.Homology.ext_mapExactFunctor_id _ n F x,
    Ext.mk₀_comp_mk₀_assoc, CategoryTheory.Sheaf.H.map_apply]
  simp only [Iso.symm_inv, Iso.symm_hom]
  rw [constantSheafIsoPullback_id, Ext.mk₀_id_comp]

/-- **The pullback map is functorial**: `(g ≫ f)^* = g^* ∘ f^*`, up to
`(g ≫ f)⁻¹ F ≅ g⁻¹ f⁻¹ F`. -/
theorem cohomologyPullback_comp (f : X ⟶ Y) (g : Z ⟶ X) (F : Sh(Y)) (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} F n) :
    cohomologyPullback (g ≫ f) F n x =
      CategoryTheory.Sheaf.H.map ((pullbackCompIso f g).inv.app F) n
        (cohomologyPullback g _ n (cohomologyPullback f F n x)) := by
  rw [cohomologyPullback_apply, Stacks.Homology.ext_mapExactFunctor_of_iso
    (sheafPullback f ⋙ sheafPullback g) _ (pullbackCompIso f g).symm _ n F x,
    Stacks.Homology.ext_mapExactFunctor_comp_functor _ _ _ n F x,
    Ext.mk₀_comp_mk₀_assoc, CategoryTheory.Sheaf.H.map_apply, cohomologyPullback_apply,
    cohomologyPullback_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc]
  simp only [Iso.symm_inv, Iso.symm_hom]
  rw [constantSheafIsoPullback_comp, Ext.comp_assoc_of_third_deg_zero]

/-! ### Constant coefficients -/

/-- **The pullback map with constant coefficients** `Hⁿ(Y, M) → Hⁿ(X, M)`: the pullback map
followed by `f⁻¹ M_Y ≅ M_X`. -/
def constantCohomologyPullback (f : X ⟶ Y) (M : AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} (c(Y).obj M) n →+ CategoryTheory.Sheaf.H.{u} (c(X).obj M) n :=
  (CategoryTheory.Sheaf.H.map ((constantSheafIsoPullback f).inv.app M) n).comp
    (cohomologyPullback f _ n)

theorem constantCohomologyPullback_apply (f : X ⟶ Y) (M : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} (c(Y).obj M) n) :
    constantCohomologyPullback f M n x =
      CategoryTheory.Sheaf.H.map ((constantSheafIsoPullback f).inv.app M) n
        (cohomologyPullback f _ n x) := rfl

/-- `(𝟙 X)^* = id` on cohomology with constant coefficients. -/
@[simp]
theorem constantCohomologyPullback_id (M : AddCommGrpCat.{u}) (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} (c(X).obj M) n) :
    constantCohomologyPullback (𝟙 X) M n x = x := by
  rw [constantCohomologyPullback_apply, cohomologyPullback_id,
    ← CategoryTheory.Sheaf.H.map_comp_apply, constantSheafIsoPullback_id_inv,
    CategoryTheory.Sheaf.H.map_id_apply]

/-- `(g ≫ f)^* = g^* ∘ f^*` on cohomology with constant coefficients. -/
theorem constantCohomologyPullback_comp (f : X ⟶ Y) (g : Z ⟶ X) (M : AddCommGrpCat.{u})
    (n : ℕ) (x : CategoryTheory.Sheaf.H.{u} (c(Y).obj M) n) :
    constantCohomologyPullback (g ≫ f) M n x =
      constantCohomologyPullback g M n (constantCohomologyPullback f M n x) := by
  rw [constantCohomologyPullback_apply, cohomologyPullback_comp,
    ← CategoryTheory.Sheaf.H.map_comp_apply, constantSheafIsoPullback_comp_inv,
    constantCohomologyPullback_apply, constantCohomologyPullback_apply, cohomologyPullback_map,
    ← CategoryTheory.Sheaf.H.map_comp_apply]
  rfl

/-- The pullback map with constant coefficients is natural in the coefficient group. -/
theorem constantCohomologyPullback_map_coefficients (f : X ⟶ Y) {M M' : AddCommGrpCat.{u}}
    (φ : M ⟶ M') (n : ℕ) (x : CategoryTheory.Sheaf.H.{u} (c(Y).obj M) n) :
    constantCohomologyPullback f M' n (CategoryTheory.Sheaf.H.map (c(Y).map φ) n x) =
      CategoryTheory.Sheaf.H.map (c(X).map φ) n (constantCohomologyPullback f M n x) := by
  rw [constantCohomologyPullback_apply, constantCohomologyPullback_apply, cohomologyPullback_map,
    ← CategoryTheory.Sheaf.H.map_comp_apply, ← CategoryTheory.Sheaf.H.map_comp_apply]
  congr 2
  exact (constantSheafIsoPullback f).inv.naturality φ

/-! ### Retracts -/

section Retract

variable {A : TopCat.{u}} (i : A ⟶ X) (r : X ⟶ A) (hir : i ≫ r = 𝟙 A) (M : AddCommGrpCat.{u})
  (n : ℕ)
include hir

/-- **Cohomology of a retract**: if `i ≫ r = 𝟙 A`, then `i^* ∘ r^* = id` on `Hⁿ(A, M)`. -/
theorem constantCohomologyPullback_leftInverse_of_retract :
    Function.LeftInverse (constantCohomologyPullback i M n) (constantCohomologyPullback r M n) :=
  fun x => by rw [← constantCohomologyPullback_comp, hir, constantCohomologyPullback_id]

theorem constantCohomologyPullback_injective_of_retract :
    Function.Injective (constantCohomologyPullback r M n) :=
  (constantCohomologyPullback_leftInverse_of_retract i r hir M n).injective

theorem constantCohomologyPullback_surjective_of_retract :
    Function.Surjective (constantCohomologyPullback i M n) :=
  (constantCohomologyPullback_leftInverse_of_retract i r hir M n).surjective

/-- **`Hⁿ(A, M)` is a direct summand of `Hⁿ(X, M)`** for a retract `A` of `X`: the image of `r^*`
and the kernel of `i^*` are complementary subgroups. -/
theorem isCompl_range_ker_of_retract :
    IsCompl (constantCohomologyPullback r M n).range (constantCohomologyPullback i M n).ker := by
  have h := constantCohomologyPullback_leftInverse_of_retract i r hir M n
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro y ⟨⟨x, rfl⟩, hy⟩
    change constantCohomologyPullback i M n (constantCohomologyPullback r M n x) = 0 at hy
    rw [h x] at hy
    simp [hy]
  · rw [codisjoint_iff, eq_top_iff]
    intro y _
    rw [AddSubgroup.mem_sup]
    refine ⟨constantCohomologyPullback r M n (constantCohomologyPullback i M n y), ⟨_, rfl⟩,
      y - constantCohomologyPullback r M n (constantCohomologyPullback i M n y), ?_, by abel⟩
    rw [AddMonoidHom.mem_ker, map_sub, h, sub_self]

/-- Finite generation of `Hⁿ(X, M)` passes to `Hⁿ(A, M)` for a retract `A` of `X`. -/
theorem addGroupFG_of_retract [AddGroup.FG (CategoryTheory.Sheaf.H.{u} (c(X).obj M) n)] :
    AddGroup.FG (CategoryTheory.Sheaf.H.{u} (c(A).obj M) n) :=
  AddGroup.fg_of_surjective (constantCohomologyPullback_surjective_of_retract i r hir M n)

/-- Finiteness of `Hⁿ(X, M)` as a `ℤ`-module passes to `Hⁿ(A, M)` for a retract `A` of `X`. -/
theorem moduleFinite_of_retract [Module.Finite ℤ (CategoryTheory.Sheaf.H.{u} (c(X).obj M) n)] :
    Module.Finite ℤ (CategoryTheory.Sheaf.H.{u} (c(A).obj M) n) :=
  Module.Finite.of_surjective (constantCohomologyPullback i M n).toIntLinearMap
    (constantCohomologyPullback_surjective_of_retract i r hir M n)

end Retract

end TopCat.SheafCohomology
