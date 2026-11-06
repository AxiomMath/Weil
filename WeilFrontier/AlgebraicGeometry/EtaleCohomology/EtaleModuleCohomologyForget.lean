module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleSheafAcyclicity
public import WeilFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import WeilFrontier.Defs.CategoryTheory.Sites.SheafCohomology.Basic
public import Weil.Attr

/-!
# Étale cohomology of a sheaf of `R`-modules computed in sheaves of `R`-modules

Let `S` be a scheme, `R` a ring and `F` a sheaf of `R`-modules on the small étale site of `S`.
The global sections functor `Γ(S, -)` can be derived in the category of sheaves of `R`-modules or,
after forgetting the module structure, in the category of abelian sheaves, where the étale
cohomology `H^n(S, F)` is defined. The two agree: for an injective resolution `F → I^•` in
sheaves of `R`-modules there is a canonical isomorphism of abelian groups
`H^n(Γ(S, I^•)) ≅ H^n(S, F)`, and the left side is an `R`-module. At the level of functors,
the `n`-th right derived functor of `Γ(S, -)` on sheaves of `R`-modules, followed by forgetting
the module structure, is the étale cohomology of the underlying abelian sheaf.

The proof is the one of the source: forgetting the module structure is exact, and it carries an
injective sheaf of `R`-modules to an abelian sheaf which is acyclic for `Γ(S, -)`, so the
resolution `I^•` of `F` stays a `Γ`-acyclic resolution of the underlying abelian sheaf.

## Main definitions

* `AlgebraicGeometry.SmallEtale.forgetModules`: the underlying abelian sheaf of a sheaf of
  `R`-modules.
* `AlgebraicGeometry.SmallEtale.rightDerivedGlobalSectionsForgetIso`: the right derived functors
  of `Γ(S, -)` on sheaves of `R`-modules, forgotten to abelian groups, are the étale cohomology
  functors of the underlying abelian sheaves, naturally in the sheaf.
* `AlgebraicGeometry.SmallEtale.homologySectionsAddEquivH`: `H^n(Γ(S, I^•)) ≃+ H^n(S, F)` for an
  injective resolution `F → I^•` in sheaves of `R`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.rightAcyclic_globalSectionsAb_forgetModules_obj`: the underlying
  abelian sheaf of an injective sheaf of `R`-modules is acyclic for global sections.

## Implementation notes

The statements are on the small étale site `AlgebraicGeometry.SmallEtale` with coefficients in
the morphism universe `u` of the site, so the ring `R` lives in `Type u`. The acyclicity is the
torsion-free argument of [Stacks, Tag 03FD]
(`Stacks.Cohomology.ModuleSheaf.isZero_rightDerived_sheafSections_of_injective`), and the
collapse of the derived functor of a composite is
`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`. The same statement on Mathlib's
small étale site, with coefficients one universe higher, is
`Stacks.EtaleCohomology.etaleModuleCohomologyForgetIso`.

The source works on the site `Et(X)` of noetherian separated étale `X`-schemes, whose sheaf
category is equivalent to that of `AlgebraicGeometry.SmallEtale`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.4.
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (R : Type u) [Ring R]

/-- The underlying abelian sheaf of a sheaf of `R`-modules on the small étale site. -/
abbrev forgetModules : Sheaf (topology B S hS) (ModuleCat.{u} R) ⥤
    Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  sheafCompose (topology B S hS) (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

instance : (forgetModules B S hS R).Additive := ⟨by intros; rfl⟩

instance : PreservesFiniteLimits (forgetModules B S hS R) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂.{0, u, u, u + 1} _ R

instance : PreservesFiniteColimits (forgetModules B S hS R) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteColimits_sheafCompose_forget₂.{0, u, u, u + 1} _ R

/-- The global sections functor `Γ(S, -)` on abelian sheaves on the small étale site: sections
over the final object. -/
abbrev globalSectionsAb : Sheaf (topology B S hS) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op (final B S hS))

/-- The global sections functor `Γ(S, -)` on sheaves of `R`-modules on the small étale site:
sections over the final object. -/
abbrev globalSectionsModules : Sheaf (topology B S hS) (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  (sheafSections (topology B S hS) (ModuleCat.{u} R)).obj (op (final B S hS))

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The underlying abelian sheaf of an injective sheaf of `R`-modules is acyclic for global
sections** on the small étale site. -/
theorem rightAcyclic_globalSectionsAb_forgetModules_obj
    (I : Sheaf (topology B S hS) (ModuleCat.{u} R)) [Injective I] :
    (globalSectionsAb B S hS).rightAcyclic ((forgetModules B S hS R).obj I) := by
  let := hasExt_sheaf B S hS
  refine (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp => ?_
  exact
    Stacks.Cohomology.ModuleSheaf.isZero_rightDerived_sheafSections_of_injective.{0, u, u, u + 1}
      R I (final B S hS) p hp

/-- The right derived functors of `Γ(S, -) ∘ forget` are those of `Γ(S, -)` on abelian sheaves,
after forgetting: forgetting is exact and carries injectives to `Γ`-acyclic sheaves. -/
def rightDerivedGlobalSectionsAbCompForgetIso (n : ℕ) :
    (forgetModules B S hS R ⋙ globalSectionsAb B S hS).rightDerived n ≅
      forgetModules B S hS R ⋙ (globalSectionsAb B S hS).rightDerived n :=
  Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _
    (fun J _ => rightAcyclic_globalSectionsAb_forgetModules_obj B S hS R J) n

/-- **The derived functors of global sections on sheaves of `R`-modules and on abelian sheaves
agree.** For `n : ℕ`, the `n`-th right derived functor of `Γ(S, -)` on sheaves of `R`-modules on
the small étale site, followed by forgetting the module structure, is the étale cohomology
functor `H^n(S, -)` of the underlying abelian sheaf, naturally in the sheaf. -/
@[weil "lem_fk104_derived_sections_r_modules_agree"]
def rightDerivedGlobalSectionsForgetIso (n : ℕ) :
    letI := hasExt_sheaf B S hS
    (globalSectionsModules B S hS R).rightDerived n ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      forgetModules B S hS R ⋙ Sheaf.functorH (topology B S hS) n :=
  letI := hasExt_sheaf B S hS
  have : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (Functor.rightDerivedCompIso _ _ n).symm ≪≫
    Functor.rightDerivedIsoOfNatIso
      (Iso.refl _ : globalSectionsModules B S hS R ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
        forgetModules B S hS R ⋙ globalSectionsAb B S hS) n ≪≫
    rightDerivedGlobalSectionsAbCompForgetIso B S hS R n ≪≫
    Functor.isoWhiskerLeft _ (functorHIsoRightDerivedSections B S hS n).symm

/-- The cohomology `H^n(Γ(S, I^•))` of the complex of global sections of an injective resolution
`F → I^•` in sheaves of `R`-modules, viewed as an abelian group, is the étale cohomology of the
underlying abelian sheaf of `F`, with `Ext`-groups in the morphism universe of the site. -/
def homologySectionsIsoFunctorH (F : Sheaf (topology B S hS) (ModuleCat.{u} R))
    (I : InjectiveResolution F) (n : ℕ) :
    letI := hasExt_sheaf B S hS
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((((globalSectionsModules B S hS R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex).homology n) ≅
      (Sheaf.functorH (topology B S hS) n).obj ((forgetModules B S hS R).obj F) :=
  letI := hasExt_sheaf B S hS
  have : (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (((((globalSectionsModules B S hS R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).sc n).mapHomologyIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).symm ≪≫
    (I.isoRightDerivedObj (forgetModules B S hS R ⋙ globalSectionsAb B S hS) n).symm ≪≫
    (rightDerivedGlobalSectionsAbCompForgetIso B S hS R n).app F ≪≫
    ((functorHIsoRightDerivedSections B S hS n).app ((forgetModules B S hS R).obj F)).symm

/-- Étale cohomology with `Ext`-groups in an arbitrary universe `w` is that with `Ext`-groups in
the morphism universe of the site, as abelian groups. -/
def hAddEquivFunctorH [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u})]
    (F : Sheaf (topology B S hS) AddCommGrpCat.{u}) (n : ℕ) :
    F.H n ≃+ (letI := hasExt_sheaf B S hS; (Sheaf.functorH (topology B S hS) n).obj F) :=
  { toEquiv := Ext.chgUniv.{u}
    map_add' a b := by
      let := HasDerivedCategory.standard (Sheaf (topology B S hS) AddCommGrpCat.{u})
      apply Ext.homEquiv.{_, u}.injective
      change Ext.homEquiv (Ext.chgUniv.{u} (a + b)) =
        Ext.homEquiv (Ext.chgUniv.{u} a + Ext.chgUniv.{u} b)
      rw [Ext.homEquiv_chgUniv]
      change (a + b).hom = (Ext.chgUniv.{u} a + Ext.chgUniv.{u} b).hom
      rw [Ext.add_hom, Ext.add_hom]
      change Ext.homEquiv a + Ext.homEquiv b = Ext.homEquiv (Ext.chgUniv.{u} a) +
        Ext.homEquiv (Ext.chgUniv.{u} b)
      rw [Ext.homEquiv_chgUniv, Ext.homEquiv_chgUniv] }

/-- **Étale cohomology of a sheaf of `R`-modules is computed by an injective resolution in sheaves
of `R`-modules.** For a sheaf of `R`-modules `F` on the small étale site of `S` and an injective
resolution `F → I^•` in sheaves of `R`-modules, the `n`-th cohomology of the complex of
`R`-modules `Γ(S, I^•)` is, as an abelian group, the étale cohomology `H^n(S, F)` of the
underlying abelian sheaf of `F`. -/
@[weil "lem_fk104_derived_sections_r_modules_agree"]
def homologySectionsAddEquivH [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u})]
    (F : Sheaf (topology B S hS) (ModuleCat.{u} R)) (I : InjectiveResolution F) (n : ℕ) :
    ((((globalSectionsModules B S hS R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).homology n) ≃+ ((forgetModules B S hS R).obj F).H n :=
  (homologySectionsIsoFunctorH B S hS R F I n).addCommGroupIsoToAddEquiv.trans
    (hAddEquivFunctorH B S hS _ n).symm

end AlgebraicGeometry.SmallEtale
