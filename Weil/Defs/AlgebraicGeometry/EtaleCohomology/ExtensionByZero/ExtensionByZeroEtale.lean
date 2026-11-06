module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FormulaAdjunction
public import Weil.Attr

/-!
# Extension by zero along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of schemes and `Λ` a ring. For a sheaf `F` of `Λ`-modules
on the small étale site of `X`, the extension by zero `f_! F` is the sheaf of `Λ`-modules on the
small étale site of `Y` associated with the presheaf `P_f F` whose sections over `V → Y` are the
direct sum `⨁_φ F(V →^φ X)` over the `Y`-morphisms `φ : V ⟶ X`. A morphism `α : F ⟶ F'` acts on
`P_f F` summandwise, and so induces `f_! α : f_! F ⟶ f_! F'`; this makes `f_!` a functor. For
`Λ = ℤ` one obtains the extension by zero of abelian sheaves.

The functor itself is the Stacks Project's: `Stacks.EtaleCohomology.etaleModuleExtensionByZero`
for sheaves of `Λ`-modules and `Stacks.EtaleCohomology.extensionByZero` for abelian sheaves, both
the sheafified left Kan extension along composition with `f`, left adjoint to restriction. This
file identifies them with the sheafification of the direct-sum presheaf `P_f`, naturally in the
sheaf, and records that the presheaf-level functor acts summandwise on morphisms.

## Main results

* `AlgebraicGeometry.ι_comp_extensionByZeroDirectSum_map_app`: a morphism `α : F ⟶ F'` acts on
  `P_f F` summandwise.
* `AlgebraicGeometry.etaleModuleExtensionByZeroIsoSheafifyDirectSum`: for sheaves of `Λ`-modules,
  `f_!` is isomorphic to the functor `F ↦ sheafify (P_f F)`.
* `AlgebraicGeometry.etaleModuleExtensionByZeroObjIso` and
  `AlgebraicGeometry.etaleModuleExtensionByZeroObjIso_hom_naturality`: `f_! F ≅ sheafify (P_f F)`,
  compatibly with the maps induced by `α : F ⟶ F'`.
* `AlgebraicGeometry.extensionByZeroIsoSheafifyDirectSum`,
  `AlgebraicGeometry.extensionByZeroObjIso`: the same for abelian sheaves.

## Implementation notes

The construction lives on Mathlib's small étale site `X.Etale` with the topology
`X.smallEtaleTopology`, where the Stacks Project's extension by zero is defined. The coefficient
categories are `ModuleCat.{max (u + 1) r} Λ` and `AddCommGrpCat.{max (u + 1) v}`, the smallest
universes in which sheafification on the small étale site is available.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Etale Stacks.EtaleCohomology

universe w₂ w₁ r v u

namespace AlgebraicGeometry

section General

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  {A : Type w₁} [Category.{w₂} A] [HasCoproducts.{u} A]
  [∀ F : (X.Etale)ᵒᵖ ⥤ A, (smallEtaleCompose f).op.HasPointwiseLeftKanExtension F]

/-- A morphism of presheaves `α : F ⟶ F'` acts on the direct-sum presheaf `P_f` summandwise: it
sends the summand `F(V →^φ X)` to the summand `F'(V →^φ X)` by the component of `α`. -/
@[weil "def_fk108_extension_by_zero_etale"]
theorem ι_comp_extensionByZeroDirectSum_map_app {F F' : (X.Etale)ᵒᵖ ⥤ A} (α : F ⟶ F')
    {V : Y.Etale} (φ : V ⟶ smallEtaleSource f) :
    Sigma.ι (fun ψ : V ⟶ smallEtaleSource f => F.obj (op (sourceDescend f ψ))) φ ≫
        ((extensionByZeroDirectSum f).map α).app (op V) =
      α.app (op (sourceDescend f φ)) ≫
        Sigma.ι (fun ψ : V ⟶ smallEtaleSource f => F'.obj (op (sourceDescend f ψ))) φ := by
  have hF : Sigma.ι (fun ψ : V ⟶ smallEtaleSource f => F.obj (op (sourceDescend f ψ))) φ ≫
      (extensionByZeroPresheafSectionIso f F V).hom = extensionByZeroSummandInclusion f F φ :=
    Sigma.ι_desc (fun ψ => extensionByZeroSummandInclusion f F ψ) φ
  have hF' : Sigma.ι (fun ψ : V ⟶ smallEtaleSource f => F'.obj (op (sourceDescend f ψ))) φ ≫
      (extensionByZeroPresheafSectionIso f F' V).hom = extensionByZeroSummandInclusion f F' φ :=
    Sigma.ι_desc (fun ψ => extensionByZeroSummandInclusion f F' ψ) φ
  change _ ≫ ((extensionByZeroPresheafSectionIso f F V).hom ≫
    ((smallEtaleCompose f).op.lan.map α).app (op V) ≫
    (extensionByZeroPresheafSectionIso f F' V).inv) = _
  rw [← Category.assoc, hF, ← Category.assoc, extensionByZeroSummandInclusion_naturality,
    Category.assoc, ← hF', Category.assoc, Iso.hom_inv_id, Category.comp_id]

end General

section Modules

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

/-- Extension by zero of sheaves of `Λ`-modules along an étale morphism `f` is the functor
`F ↦ sheafify (P_f F)`, where `P_f F` is the direct-sum presheaf acted on summandwise by
morphisms. -/
@[weil "def_fk108_extension_by_zero_etale"]
def etaleModuleExtensionByZeroIsoSheafifyDirectSum :
    etaleModuleExtensionByZero.{u, r} Λ f ≅
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ⋙
        extensionByZeroDirectSum f (A := ModuleCat.{max (u + 1) r} Λ) ⋙
        presheafToSheaf Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (lanIsoExtensionByZeroDirectSum f) _)

/-- The extension by zero `f_! F` of a sheaf of `Λ`-modules is the sheaf associated with the
direct-sum presheaf `P_f F`. -/
@[weil "def_fk108_extension_by_zero_etale"]
def etaleModuleExtensionByZeroObjIso (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleExtensionByZero.{u, r} Λ f).obj F ≅
      (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj
        (etaleExtensionByZeroPresheaf f F) :=
  (etaleModuleExtensionByZeroIsoSheafifyDirectSum Λ f).app F

/-- The morphism `f_! α : f_! F ⟶ f_! F'` induced by `α : F ⟶ F'` is the sheafification of the
summandwise map `P_f F ⟶ P_f F'`. -/
@[weil "def_fk108_extension_by_zero_etale"]
theorem etaleModuleExtensionByZeroObjIso_hom_naturality {F F' : EtaleModules.{u, r} Λ X}
    (α : F ⟶ F') :
    (etaleModuleExtensionByZero.{u, r} Λ f).map α ≫
        (etaleModuleExtensionByZeroObjIso Λ f F').hom =
      (etaleModuleExtensionByZeroObjIso Λ f F).hom ≫
        (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map
          ((extensionByZeroDirectSum f).map α.hom) :=
  (etaleModuleExtensionByZeroIsoSheafifyDirectSum Λ f).hom.naturality α

end Modules

section Abelian

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- Extension by zero of abelian sheaves along an étale morphism `f` is the functor
`F ↦ sheafify (P_f F)`, where `P_f F` is the direct-sum presheaf acted on summandwise by
morphisms. -/
@[weil "def_fk108_extension_by_zero_etale"]
def extensionByZeroIsoSheafifyDirectSum :
    Stacks.EtaleCohomology.extensionByZero.{u, v} f ≅
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
        extensionByZeroDirectSum f (A := AddCommGrpCat.{max (u + 1) v}) ⋙
        presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (lanIsoExtensionByZeroDirectSum f) _)

/-- The extension by zero `f_! F` of an abelian sheaf is the sheaf associated with the
direct-sum presheaf `P_f F`. -/
@[weil "def_fk108_extension_by_zero_etale"]
def extensionByZeroObjIso (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (Stacks.EtaleCohomology.extensionByZero.{u, v} f).obj F ≅
      (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (etaleExtensionByZeroPresheaf f F) :=
  (extensionByZeroIsoSheafifyDirectSum f).app F

/-- The morphism `f_! α` induced by a morphism `α : F ⟶ F'` of abelian sheaves is the
sheafification of the summandwise map `P_f F ⟶ P_f F'`. -/
@[weil "def_fk108_extension_by_zero_etale"]
theorem extensionByZeroObjIso_hom_naturality
    {F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (α : F ⟶ F') :
    (Stacks.EtaleCohomology.extensionByZero.{u, v} f).map α ≫
        (extensionByZeroObjIso f F').hom =
      (extensionByZeroObjIso f F).hom ≫
        (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).map
          ((extensionByZeroDirectSum f).map α.hom) :=
  (extensionByZeroIsoSheafifyDirectSum f).hom.naturality α

end Abelian

end AlgebraicGeometry
