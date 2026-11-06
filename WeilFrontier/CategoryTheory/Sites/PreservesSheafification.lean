module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Weil.Attr

/-!
# Sheafification of a presheaf of modules

Let `Λ` be a ring and `P` a presheaf of `Λ`-modules on a site `(C, J)`. Forgetting the
`Λ`-action, `P` is a presheaf of abelian groups `P ⋙ forget₂`, with abelian sheafification
`ι : P ⋙ forget₂ ⟶ (P ⋙ forget₂)^`. For `λ ∈ Λ` the multiplication by `λ` is an abelian
endomorphism `λ_P` of `P ⋙ forget₂`, and its image under the sheafification functor is an
endomorphism `λ_{P^}` of the abelian sheaf `(P ⋙ forget₂)^`.

The sheafification `sheafify J P` of `P` in `Λ`-modules realises this: the forgetful functor
to abelian groups commutes with sheafification, through an isomorphism under which the unit
of the `Λ`-module sheafification is `ι` and the scalar multiplication by `λ` is `λ_{P^}`;
the unit is `Λ`-linear, and composition with it is a bijection from morphisms of sheaves of
`Λ`-modules out of the sheafification onto morphisms of presheaves of `Λ`-modules out of `P`.

## Main results

* `CategoryTheory.sheafifyMap_smul_comp_sheafifyComposeIso_hom`: under the comparison
  isomorphism, the sheafification of `λ_P` is the multiplication by `λ` on the
  `Λ`-module sheafification.
* `CategoryTheory.sheafify_moduleCat_forget₂`: the three properties together, on any site
  where the sheafifications exist and `forget₂` preserves them.
* `AlgebraicGeometry.Scheme.etale_sheafify_moduleCat_forget₂`: the statement on the small
  étale site of a scheme.
* `AlgebraicGeometry.Scheme.preservesSheafification_forget₂_moduleCat`: on the small étale
  site, `forget₂` from `Λ`-modules to abelian groups commutes with sheafification.

## Implementation notes

A sheaf of `Λ`-modules is a `ModuleCat Λ`-valued sheaf, and the scalar endomorphism
`λ_F` is `ModuleCat.smulNatTrans Λ λ` whiskered by `F`. Rather than putting a module
structure on the abelian sheafification after the fact, the statement identifies the
abelian sheafification with the underlying abelian sheaf of the `Λ`-module sheafification,
compatibly with the units and with the scalar endomorphisms; this determines the
`Λ`-module structure, since composition with the unit is injective. The ring need not be
commutative.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §4.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe w v u r

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [Ring Λ]

section General

variable [HasWeakSheafify J (ModuleCat.{w} Λ)] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The sheafification of the abelian endomorphism `λ_P` (multiplication by `λ`) of the
underlying abelian presheaf of a presheaf of `Λ`-modules `P` corresponds, under the
comparison isomorphism, to the multiplication by `λ` on the sheafification of `P`. -/
theorem sheafifyMap_smul_comp_sheafifyComposeIso_hom (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (l : Λ) :
    sheafifyMap J (Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ l)) ≫
        (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom =
      (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom ≫
        Functor.whiskerLeft (sheafify J P) (ModuleCat.smulNatTrans Λ l) := by
  have hS : Presheaf.IsSheaf J (sheafify J P ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
    GrothendieckTopology.HasSheafCompose.isSheaf _ ((presheafToSheaf J (ModuleCat.{w} Λ)).obj P).property
  apply sheafify_hom_ext J _ _ hS
  rw [← toSheafify_naturality_assoc, sheafComposeIso_hom_fac, sheafComposeIso_hom_fac_assoc]
  ext U : 2
  exact ((ModuleCat.smulNatTrans Λ l).naturality ((toSheafify J P).app U)).symm

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})] in
/-- The unit of the sheafification is `Λ`-linear: it commutes with the scalar
endomorphisms `λ_P` and `λ_{P^}`. -/
theorem smul_comp_whiskerRight_toSheafify (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (l : Λ) :
    Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ l) ≫
        Functor.whiskerRight (toSheafify J P) (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) =
      Functor.whiskerRight (toSheafify J P) (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≫
        Functor.whiskerLeft (sheafify J P) (ModuleCat.smulNatTrans Λ l) := by
  ext U : 2
  exact ((ModuleCat.smulNatTrans Λ l).naturality ((toSheafify J P).app U)).symm

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})] in
/-- Composition with the unit of the sheafification is a bijection from morphisms of
sheaves of `Λ`-modules out of the sheafification of `P` onto morphisms of presheaves of
`Λ`-modules out of `P`. -/
theorem bijective_toSheafify_comp (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (F : Sheaf J (ModuleCat.{w} Λ)) :
    Function.Bijective
      (fun φ : (presheafToSheaf J (ModuleCat.{w} Λ)).obj P ⟶ F ↦
        toSheafify J P ≫ (sheafToPresheaf J (ModuleCat.{w} Λ)).map φ) :=
  ((sheafificationAdjunction J (ModuleCat.{w} Λ)).homEquiv P F).bijective

/-- **Sheafification of a presheaf of `Λ`-modules.** Let `P` be a presheaf of `Λ`-modules.
The comparison isomorphism `e` between the abelian sheafification `(P ⋙ forget₂)^` of the
underlying abelian presheaf and the underlying abelian sheaf of the `Λ`-module sheafification
`sheafify J P` satisfies:
1. it carries the abelian unit `ι` to the (underlying map of the) `Λ`-module unit;
2. it carries the sheafification of `λ_P` to the multiplication by `λ`, so `(P ⋙ forget₂)^`
   with the maps `λ_{P^}` is the sheaf of `Λ`-modules `sheafify J P`;
3. the `Λ`-module unit `toSheafify J P` (a morphism of presheaves of `Λ`-modules, hence
   `Λ`-linear) commutes with `λ_P` and `λ_{P^}`;
4. for every sheaf of `Λ`-modules `F`, composition with the unit is a bijection from
   `Λ`-linear morphisms of sheaves `sheafify J P ⟶ F` onto `Λ`-linear morphisms `P ⟶ F`. -/
theorem sheafify_moduleCat_forget₂ (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) :
    toSheafify J (P ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≫
        (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom =
      Functor.whiskerRight (toSheafify J P) (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ∧
    (∀ l : Λ, sheafifyMap J (Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ l)) ≫
        (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom =
      (sheafifyComposeIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom ≫
        Functor.whiskerLeft (sheafify J P) (ModuleCat.smulNatTrans Λ l)) ∧
    (∀ l : Λ, Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ l) ≫
        Functor.whiskerRight (toSheafify J P) (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) =
      Functor.whiskerRight (toSheafify J P) (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≫
        Functor.whiskerLeft (sheafify J P) (ModuleCat.smulNatTrans Λ l)) ∧
    ∀ F : Sheaf J (ModuleCat.{w} Λ), Function.Bijective
      (fun φ : (presheafToSheaf J (ModuleCat.{w} Λ)).obj P ⟶ F ↦
        toSheafify J P ≫ (sheafToPresheaf J (ModuleCat.{w} Λ)).map φ) :=
  ⟨sheafComposeIso_hom_fac J _ P, sheafifyMap_smul_comp_sheafifyComposeIso_hom J Λ P,
    smul_comp_whiskerRight_toSheafify J Λ P, bijective_toSheafify_comp J Λ P⟩

end General

end CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory Limits

universe u w r

section Instances

variable (X : Scheme.{u}) (Λ : Type r) [Ring Λ] [UnivLE.{u + 1, w}]

/-- The forgetful functor from `Λ`-modules to abelian groups preserves colimits indexed by
categories of the size of the small étale site, in any universe of values containing it. -/
lemma preservesColimits_forget₂_moduleCat :
    PreservesColimitsOfSize.{u + 1, u + 1} (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
  ModuleCat.forget₂PreservesColimitsOfSize.{w, r, u + 1, u + 1} (R := Λ)

/-- The forgetful functor from abelian groups to sets preserves filtered colimits indexed by
categories of the size of the small étale site, in any universe of values containing it. -/
lemma preservesFilteredColimits_forget_addCommGrpCat :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget AddCommGrpCat.{w}) :=
  preservesFilteredColimitsOfSize_of_univLE.{w, w, u + 1, u + 1} _

attribute [local instance] preservesColimits_forget₂_moduleCat
  preservesFilteredColimits_forget_addCommGrpCat in
/-- The forgetful functor from `Λ`-modules to sets preserves filtered colimits indexed by
categories of the size of the small étale site, in any universe of values containing it. -/
lemma preservesFilteredColimits_forget_moduleCat :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget (ModuleCat.{w} Λ)) :=
  comp_preservesFilteredColimits (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat)
    (CategoryTheory.forget _)

/-- The category of `Λ`-modules has the multiequalizers indexed by shapes of the size of the
small étale site, in any universe of values containing it. -/
lemma hasLimitsOfShape_walkingMulticospan_moduleCat
    (I : MulticospanShape.{u + 1, u + 1}) :
    HasLimitsOfShape (WalkingMulticospan I) (ModuleCat.{w} Λ) :=
  (ModuleCat.hasLimitsOfSize.{u + 1, u + 1, w, r}).has_limits_of_shape _

attribute [local instance] preservesColimits_forget₂_moduleCat
  preservesFilteredColimits_forget_addCommGrpCat preservesFilteredColimits_forget_moduleCat
  hasLimitsOfShape_walkingMulticospan_moduleCat in
/-- On the small étale site, the forgetful functor from `Λ`-modules to abelian groups
commutes with sheafification. -/
instance preservesSheafification_forget₂_moduleCat :
    X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
  GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})

end Instances

attribute [local instance] preservesColimits_forget₂_moduleCat
  preservesFilteredColimits_forget_addCommGrpCat preservesFilteredColimits_forget_moduleCat in
/-- **Sheafification of a presheaf of `Λ`-modules on the small étale site** (FK I.4).
For a presheaf `P` of `Λ`-modules on `Et(X)`, the abelian sheafification of `P`, with the
sheafified scalar maps `λ_{P^}`, is the sheaf of `Λ`-modules `sheafify J P`, the unit is
`Λ`-linear, and composition with it identifies morphisms of sheaves of `Λ`-modules out of
the sheafification with `Λ`-linear morphisms of presheaves out of `P`. The ring `Λ` lives in
any universe, and the modules in any universe `w` containing the morphisms of `Et(X)`
(for instance `w = u + 1`). -/
@[weil "lem_fk104_lambda_presheaf_sheafification"]
theorem etale_sheafify_moduleCat_forget₂ (X : Scheme.{u}) (Λ : Type r) [Ring Λ]
    [UnivLE.{u + 1, w}] (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ) :
    toSheafify X.smallEtaleTopology (P ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≫
        (sheafifyComposeIso X.smallEtaleTopology
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom =
      Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ∧
    (∀ l : Λ, sheafifyMap X.smallEtaleTopology
          (Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ l)) ≫
        (sheafifyComposeIso X.smallEtaleTopology
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom =
      (sheafifyComposeIso X.smallEtaleTopology
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom ≫
        Functor.whiskerLeft (sheafify X.smallEtaleTopology P) (ModuleCat.smulNatTrans Λ l)) ∧
    (∀ l : Λ, Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ l) ≫
        Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) =
      Functor.whiskerRight (toSheafify X.smallEtaleTopology P)
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≫
        Functor.whiskerLeft (sheafify X.smallEtaleTopology P) (ModuleCat.smulNatTrans Λ l)) ∧
    ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ), Function.Bijective
      (fun φ : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{w} Λ)).obj P ⟶ F ↦
        toSheafify X.smallEtaleTopology P ≫
          (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{w} Λ)).map φ) :=
  sheafify_moduleCat_forget₂ X.smallEtaleTopology Λ P

end AlgebraicGeometry.Scheme
