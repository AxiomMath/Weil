module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.InverseImage
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheafAbelian
public import Weil.Attr

/-!
# The inverse image of the sheaf of locally constant maps

Let `g : X' ⟶ X` be a morphism of schemes of a big étale site `B` and let `M` be a set (resp. an
abelian group, a `Λ`-module). Let `M_X` be the sheaf on the small étale site of `X` sending an
étale `X`-scheme `U` to the locally constant maps `|U| → M`, a sheaf of sets (resp. of abelian
groups, of `Λ`-modules). Then the inverse image `g^* (M_X)` is isomorphic to `M_{X'}`, as a
sheaf of sets (resp. of abelian groups, of `Λ`-modules).

The sheaf `M_X` is the constant sheaf, the sheafification of the constant presheaf `U ↦ M`: the
map from the constant presheaf to `M_X` sending `m` to the constant map with value `m` is a local
isomorphism (`AlgebraicGeometry.SmallEtale.W_constToLocallyConstant`). The inverse image of the
constant sheaf is the constant sheaf
(`AlgebraicGeometry.smallEtaleInverseImageConstantSheafIso`), since both are left adjoint to
sections over the final object.

## Main definitions

* `AlgebraicGeometry.SmallEtale.constantSheafIsoLocallyConstantSheaf`,
  `AlgebraicGeometry.SmallEtale.constantSheafIsoLocallyConstantModuleSheaf` — the constant sheaf
  of sets (resp. of `Λ`-modules) with value `M` is the sheaf of locally constant maps.
* `AlgebraicGeometry.smallEtaleInverseImageLocallyConstantSheafIso` — `g^* (M_X) ≅ M_{X'}` for
  sheaves of sets.
* `AlgebraicGeometry.smallEtaleInverseImageLocallyConstantSheafAbIso` — the same for sheaves of
  abelian groups.
* `AlgebraicGeometry.smallEtaleInverseImageLocallyConstantModuleSheafIso` — the same for sheaves
  of `Λ`-modules.

## Implementation notes

The inverse image is `AlgebraicGeometry.smallEtaleInverseImage`, the left adjoint of the direct
image. Sheaves of sets and of abelian groups take values in the universe `max (u + 1) v`, where
`u` is the universe of the schemes; sheaves of `Λ`-modules take values in `ModuleCat.{u + 1} Λ`
for a ring `Λ : Type (u + 1)`, the universe at which sheafification of sheaves of modules is
available on the small étale site. The ring `Λ` need not be commutative.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The constant sheaf of sets with value `M` on the small étale site of `S` is the sheaf `M_S`
of locally constant maps `|U| → M`. -/
def constantSheafIsoLocallyConstantSheaf (M : Type (max (u + 1) v)) :
    (constantSheaf (topology B S hS) (Type (max (u + 1) v))).obj M ≅
      locallyConstantSheaf B S hS M :=
  @asIso _ _ _ _ ((presheafToSheaf (topology B S hS) (Type (max (u + 1) v))).map
      (constToLocallyConstant B S hS M))
    (((topology B S hS).W_iff (constToLocallyConstant B S hS M)).1
      (W_constToLocallyConstant B S hS M)) ≪≫
    (sheafificationIso (locallyConstantSheaf B S hS M)).symm

section Module

variable (Λ : Type (u + 1)) [Ring Λ] (M : Type (u + 1)) [AddCommGroup M] [Module Λ M]

/-- The map from the constant presheaf of `Λ`-modules with value `M` to `M_S`, sending `m` to
the constant map with value `m`. -/
def constToLocallyConstantModule :
    (Functor.const (SmallEtale B S hS)ᵒᵖ).obj (ModuleCat.of Λ M) ⟶
      locallyConstantModulePresheaf.{0} B S hS Λ M where
  app _ := ModuleCat.ofHom (LocallyConstant.constₗ Λ)
  naturality _ _ _ := rfl

/-- The map from the constant presheaf of `Λ`-modules to `M_S` is a local isomorphism: on
underlying presheaves of sets it is the local isomorphism
`AlgebraicGeometry.SmallEtale.W_constToLocallyConstant`. -/
theorem W_constToLocallyConstantModule :
    (topology B S hS).W (constToLocallyConstantModule B S hS Λ M) := by
  have hW := W_constToLocallyConstant.{0} B S hS M
  have hinj := hW.isLocallyInjective
  have hsurj := hW.isLocallySurjective
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  exact ⟨(Presheaf.isLocallyInjective_forget_iff _ _).1 hinj,
    (Presheaf.isLocallySurjective_iff_whisker_forget _ _).2 hsurj⟩

/-- The constant sheaf of `Λ`-modules with value `M` on the small étale site of `S` is the sheaf
`M_S` of locally constant maps `|U| → M`. -/
def constantSheafIsoLocallyConstantModuleSheaf :
    (constantSheaf (topology B S hS) (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ M) ≅
      locallyConstantModuleSheaf.{0} B S hS Λ M :=
  @asIso _ _ _ _ ((presheafToSheaf (topology B S hS) (ModuleCat.{u + 1} Λ)).map
      (constToLocallyConstantModule B S hS Λ M))
    (((topology B S hS).W_iff (constToLocallyConstantModule B S hS Λ M)).1
      (W_constToLocallyConstantModule B S hS Λ M)) ≪≫
    (sheafificationIso (locallyConstantModuleSheaf.{0} B S hS Λ M)).symm

end Module

end SmallEtale

variable (B : BigEtaleSite.{u}) {X X' : B.Scheme} (g : X' ⟶ X)

/-- **The inverse image of `M_X` is `M_{X'}`, for sheaves of sets.** For a morphism
`g : X' ⟶ X` and a set `M`, the inverse image of the sheaf of locally constant maps `|U| → M`
on the small étale site of `X` is the sheaf of locally constant maps on the small étale site of
`X'`. -/
@[weil "lem_fk104_inverse_image_constant"]
def smallEtaleInverseImageLocallyConstantSheafIso (M : Type (max (u + 1) v)) :
    (smallEtaleInverseImage B g (Type (max (u + 1) v))).obj
        (SmallEtale.locallyConstantSheaf B X.obj X.property M) ≅
      SmallEtale.locallyConstantSheaf B X'.obj X'.property M :=
  (smallEtaleInverseImage B g _).mapIso
      (SmallEtale.constantSheafIsoLocallyConstantSheaf B X.obj X.property M).symm ≪≫
    smallEtaleInverseImageConstantSheafIso B g _ M ≪≫
      SmallEtale.constantSheafIsoLocallyConstantSheaf B X'.obj X'.property M

/-- **The inverse image of `M_X` is `M_{X'}`, for sheaves of abelian groups.** For a morphism
`g : X' ⟶ X` and an abelian group `M`, the inverse image of the abelian sheaf of locally
constant maps `|U| → M` on the small étale site of `X` is the abelian sheaf of locally constant
maps on the small étale site of `X'`. -/
@[weil "lem_fk104_inverse_image_constant"]
def smallEtaleInverseImageLocallyConstantSheafAbIso (M : Type (max (u + 1) v))
    [AddCommGroup M] :
    (smallEtaleInverseImage B g AddCommGrpCat.{max (u + 1) v}).obj
        (locallyConstantSheafAb.{u, v} B X.obj X.property M) ≅
      locallyConstantSheafAb.{u, v} B X'.obj X'.property M :=
  (smallEtaleInverseImage B g _).mapIso
      (constantSheafIsoLocallyConstantMapsAb_smallEtale.{u, v} B X.obj X.property M).symm ≪≫
    smallEtaleInverseImageConstantSheafIso B g _ (AddCommGrpCat.of M) ≪≫
      constantSheafIsoLocallyConstantMapsAb_smallEtale.{u, v} B X'.obj X'.property M

/-- **The inverse image of `M_X` is `M_{X'}`, for sheaves of `Λ`-modules.** For a morphism
`g : X' ⟶ X` and a `Λ`-module `M`, the inverse image of the sheaf of `Λ`-modules of locally
constant maps `|U| → M` on the small étale site of `X` is the sheaf of `Λ`-modules of locally
constant maps on the small étale site of `X'`. -/
@[weil "lem_fk104_inverse_image_constant"]
def smallEtaleInverseImageLocallyConstantModuleSheafIso (Λ : Type (u + 1)) [Ring Λ]
    (M : Type (u + 1)) [AddCommGroup M] [Module Λ M] :
    (smallEtaleInverseImage B g (ModuleCat.{u + 1} Λ)).obj
        (SmallEtale.locallyConstantModuleSheaf.{0} B X.obj X.property Λ M) ≅
      SmallEtale.locallyConstantModuleSheaf.{0} B X'.obj X'.property Λ M :=
  (smallEtaleInverseImage B g _).mapIso
      (SmallEtale.constantSheafIsoLocallyConstantModuleSheaf B X.obj X.property Λ M).symm ≪≫
    smallEtaleInverseImageConstantSheafIso B g _ (ModuleCat.of Λ M) ≪≫
      SmallEtale.constantSheafIsoLocallyConstantModuleSheaf B X'.obj X'.property Λ M

end AlgebraicGeometry

end
