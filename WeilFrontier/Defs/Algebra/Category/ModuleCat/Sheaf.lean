module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteUnconditional

/-!
# Modules over the étale structure sheaf

Let `S` be a scheme and `𝒪_{S,et}` the structure sheaf of its small étale site, the sheaf of
rings `(U ⟶ S) ↦ Γ(U, 𝒪_U)`. An `𝒪_{S,et}`-module is an étale sheaf of abelian groups `L`
together with a `Γ(U, 𝒪_U)`-module structure on each `L(U)` such that restriction along every
morphism `V ⟶ U` of the étale site is semilinear: `(a • s)|_V = a|_V • s|_V`. A morphism of
`𝒪_{S,et}`-modules is a morphism of étale sheaves that is `Γ(U, 𝒪_U)`-linear on every `U`.

This is exactly Mathlib's notion of a sheaf of modules over a sheaf of rings, applied to the
structure sheaf `AlgebraicGeometry.SmallEtale.structureSheaf` of the small étale site; so the
category of `𝒪_{S,et}`-modules is `SheafOfModules (SmallEtale.structureSheaf B S hS)`, and no new
structure is introduced.

## Main definitions

* `AlgebraicGeometry.SmallEtale.OxetModule`: the category of `𝒪_{S,et}`-modules.
* `AlgebraicGeometry.SmallEtale.OxetModule.ofSheaf`: the `𝒪_{S,et}`-module given by an étale
  abelian sheaf with compatible module structures on its sections.
* `AlgebraicGeometry.SmallEtale.OxetModule.homMk`: the morphism of `𝒪_{S,et}`-modules given by a
  morphism of the underlying abelian sheaves that is linear on sections.
* `AlgebraicGeometry.SmallEtale.OxetModule.toSheaf`: the underlying étale abelian sheaf.
* `AlgebraicGeometry.SmallEtale.oxet`: `𝒪_{S,et}` itself, as an `𝒪_{S,et}`-module.

## Main results

* `AlgebraicGeometry.SmallEtale.structureSheaf_obj_obj`: the sections of `𝒪_{S,et}` over
  `u : U ⟶ S` are `Γ(U, 𝒪_U)`.
* `AlgebraicGeometry.SmallEtale.OxetModule.map_smul`: restriction is semilinear.
* `AlgebraicGeometry.SmallEtale.OxetModule.hom_app_smul`: a morphism is linear on sections.
* `AlgebraicGeometry.SmallEtale.OxetModule.ofSheaf_toSheaf`,
  `AlgebraicGeometry.SmallEtale.OxetModule.ofSheaf_smul`: `ofSheaf` has the given underlying
  sheaf and module structures.
* `AlgebraicGeometry.SmallEtale.OxetModule.toSheaf_map_homMk`: `homMk` has the given underlying
  morphism of sheaves.
* `AlgebraicGeometry.SmallEtale.ringedSite_ringSheaf_eq_structureSheaf`: the structure sheaf
  agrees with the ring sheaf of the ringed site `AlgebraicGeometry.smallEtaleRingedSite`, so
  these are also the modules over that ringed site.

## Implementation notes

The étale site is the small étale site `AlgebraicGeometry.SmallEtale B S hS` inside a big étale
site `B`, rather than the category of noetherian separated étale `S`-schemes; the ring sheaf is
`AlgebraicGeometry.SmallEtale.structureSheaf`, which is also the ring sheaf of
`AlgebraicGeometry.SmallEtale.associatedModule`, so the étale module `L_et` attached to a
quasi-coherent `𝒪_S`-module `L` is an object of `OxetModule B S hS`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sections of the structure sheaf `𝒪_{S,et}` of the small étale site over `u : U ⟶ S`
are the global functions `Γ(U, 𝒪_U)`. -/
lemma structureSheaf_obj_obj (U : SmallEtale B S hS) :
    (structureSheaf B S hS).obj.obj (op U) =
      (forget₂ CommRingCat RingCat).obj Γ((toScheme B S hS).obj U, ⊤) :=
  rfl

/-- **`𝒪_{S,et}`-modules.** The category of sheaves of modules over the structure sheaf
`(U ⟶ S) ↦ Γ(U, 𝒪_U)` of the small étale site of `S`: étale sheaves of abelian groups whose
sections over `U` are `Γ(U, 𝒪_U)`-modules, with semilinear restriction maps; morphisms are
morphisms of sheaves that are linear on sections. -/
@[weil "def_fk102_oxet_module"]
abbrev OxetModule : Type (u + 1) :=
  SheafOfModules.{u} (structureSheaf B S hS)

/-- The structure sheaf `𝒪_{S,et}` itself, as an `𝒪_{S,et}`-module. -/
abbrev oxet : OxetModule B S hS :=
  SheafOfModules.unit (structureSheaf B S hS)

namespace OxetModule

variable {B S hS}

/-- The underlying étale sheaf of abelian groups of an `𝒪_{S,et}`-module. -/
abbrev toSheaf : OxetModule B S hS ⥤ Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (structureSheaf B S hS)

/-- Restriction in an `𝒪_{S,et}`-module is semilinear: `(a • s)|_V = a|_V • s|_V`. -/
lemma map_smul (M : OxetModule B S hS) {U V : (SmallEtale B S hS)ᵒᵖ} (f : U ⟶ V)
    (a : (structureSheaf B S hS).obj.obj U) (s : M.val.obj U) :
    M.val.map f (a • s) = (structureSheaf B S hS).obj.map f a • M.val.map f s :=
  M.val.map_smul f a s

/-- A morphism of `𝒪_{S,et}`-modules is `Γ(U, 𝒪_U)`-linear on the sections over every `U`. -/
lemma hom_app_smul {M N : OxetModule B S hS} (φ : M ⟶ N) (U : (SmallEtale B S hS)ᵒᵖ)
    (a : (structureSheaf B S hS).obj.obj U) (s : M.val.obj U) :
    φ.val.app U (a • s) = a • φ.val.app U s :=
  (φ.val.app U).hom.map_smul a s

/-- The `𝒪_{S,et}`-module given by an étale sheaf of abelian groups `L` together with a
`Γ(U, 𝒪_U)`-module structure on each `L(U)` for which restriction is semilinear. -/
@[weil "def_fk102_oxet_module"]
def ofSheaf (L : Sheaf (topology B S hS) AddCommGrpCat.{u})
    [∀ U, Module ((structureSheaf B S hS).obj.obj U) (L.obj.obj U)]
    (map_smul : ∀ ⦃U V : (SmallEtale B S hS)ᵒᵖ⦄ (f : U ⟶ V)
      (a : (structureSheaf B S hS).obj.obj U) (s : L.obj.obj U),
      L.obj.map f (a • s) = (structureSheaf B S hS).obj.map f a • L.obj.map f s) :
    OxetModule B S hS where
  val := PresheafOfModules.ofPresheaf L.obj map_smul
  isSheaf := L.property

section ofSheaf

variable (L : Sheaf (topology B S hS) AddCommGrpCat.{u})
    [∀ U, Module ((structureSheaf B S hS).obj.obj U) (L.obj.obj U)]
    (map_smul : ∀ ⦃U V : (SmallEtale B S hS)ᵒᵖ⦄ (f : U ⟶ V)
      (a : (structureSheaf B S hS).obj.obj U) (s : L.obj.obj U),
      L.obj.map f (a • s) = (structureSheaf B S hS).obj.map f a • L.obj.map f s)

/-- The underlying abelian presheaf of `ofSheaf L map_smul` is that of `L`. -/
@[simp]
lemma ofSheaf_val_presheaf : (ofSheaf L map_smul).val.presheaf = L.obj :=
  rfl

/-- The underlying étale abelian sheaf of `ofSheaf L map_smul` is `L`. -/
@[simp]
lemma ofSheaf_toSheaf : toSheaf.obj (ofSheaf L map_smul) = L :=
  rfl

/-- The sections of `ofSheaf L map_smul` over `U` are those of `L`. -/
lemma ofSheaf_val_obj (U : (SmallEtale B S hS)ᵒᵖ) :
    (ofSheaf L map_smul).val.obj U = ModuleCat.of _ (L.obj.obj U) :=
  rfl

/-- The scalar multiplication of `ofSheaf L map_smul` is the given one. -/
lemma ofSheaf_smul (U : (SmallEtale B S hS)ᵒᵖ) (a : (structureSheaf B S hS).obj.obj U)
    (s : L.obj.obj U) :
    (a • s : (ofSheaf L map_smul).val.obj U) = (a • s : L.obj.obj U) :=
  rfl

end ofSheaf

/-- The morphism of `𝒪_{S,et}`-modules given by a morphism `φ` of the underlying étale abelian
sheaves that is `Γ(U, 𝒪_U)`-linear on every `U`. -/
@[weil "def_fk102_oxet_module"]
def homMk {M N : OxetModule B S hS} (φ : toSheaf.obj M ⟶ toSheaf.obj N)
    (hφ : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (a : (structureSheaf B S hS).obj.obj U)
      (s : M.val.obj U),
      @Eq (N.val.obj U) (φ.hom.app U (a • s)) (a • show N.val.obj U from φ.hom.app U s)) :
    M ⟶ N :=
  ⟨PresheafOfModules.homMk φ.hom hφ⟩

/-- The underlying morphism of sheaves of `homMk φ hφ` is `φ`. -/
@[simp]
lemma toSheaf_map_homMk {M N : OxetModule B S hS} (φ : toSheaf.obj M ⟶ toSheaf.obj N)
    (hφ : ∀ (U : (SmallEtale B S hS)ᵒᵖ) (a : (structureSheaf B S hS).obj.obj U)
      (s : M.val.obj U),
      @Eq (N.val.obj U) (φ.hom.app U (a • s)) (a • show N.val.obj U from φ.hom.app U s)) :
    toSheaf.map (homMk φ hφ) = φ :=
  rfl

/-- `toSheaf` is faithful: a morphism of `𝒪_{S,et}`-modules is determined by its underlying
morphism of sheaves. -/
lemma hom_ext_toSheaf {M N : OxetModule B S hS} {φ ψ : M ⟶ N}
    (h : toSheaf.map φ = toSheaf.map ψ) : φ = ψ := by
  ext U s
  exact congrArg (fun χ : toSheaf.obj M ⟶ toSheaf.obj N => χ.hom.app U s) h

end OxetModule

/-- The structure sheaf of the small étale site agrees with the ring sheaf of the ringed site
`AlgebraicGeometry.smallEtaleRingedSite`, so `𝒪_{S,et}`-modules are the sheaves of modules on
that ringed site. -/
lemma ringedSite_ringSheaf_eq_structureSheaf :
    (smallEtaleRingedSite B S hS).ringSheaf = structureSheaf B S hS :=
  rfl

end AlgebraicGeometry.SmallEtale

end
