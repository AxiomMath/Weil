module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits

/-!
# Limits, colimits and exactness of étale sheaves of `Λ`-modules

Let `X` be a scheme and `Λ` a ring. The category `Stacks.EtaleCohomology.EtaleModules Λ X` of
sheaves of `Λ`-modules on the small étale site of `X` is abelian
(`Stacks.EtaleCohomology.etaleModules_abelian`). This file shows that its small limits and
colimits are computed in abelian sheaves: the functor
`Stacks.EtaleCohomology.etaleModuleForgetAb` forgetting the module structure creates them.
Concretely, the limit (resp. colimit) of the underlying diagram of abelian sheaves carries a
structure of sheaf of `Λ`-modules making all cone (resp. cocone) maps `Λ`-linear, so equipped it
is a limit (resp. colimit) of sheaves of `Λ`-modules, and that structure is unique up to a
unique isomorphism lying over the identity. Consequently a sequence of sheaves of
`Λ`-modules is exact if and only if the underlying sequence of abelian sheaves is.

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetAbCreatesLimits`,
  `Stacks.EtaleCohomology.etaleModuleForgetAbCreatesColimits`: forgetting the module structure
  creates small limits and small colimits.
* `Stacks.EtaleCohomology.existsUnique_coneIso_of_mapCone_iso`,
  `Stacks.EtaleCohomology.existsUnique_coconeIso_of_mapCocone_iso`: two lifts of a limit
  (resp. colimit) of abelian sheaves to sheaves of `Λ`-modules are uniquely isomorphic over it.
* `Stacks.EtaleCohomology.etaleModuleForgetAb_exact_map_iff`: exactness of a short complex of
  sheaves of `Λ`-modules is exactness of its underlying short complex of abelian sheaves, and
  `Stacks.EtaleCohomology.etaleModuleForgetAb_composableArrows_exact_iff` the same for sequences
  of composable morphisms.

## Implementation notes

Preservation of all small limits and colimits is transported along the equivalence
`Stacks.EtaleCohomology.etaleModuleSheafEquivalence` with sheaves of modules over the constant
sheaf of rings, for which the forgetful functor `SheafOfModules.toSheaf` preserves them. Since
the forgetful functor also reflects isomorphisms and limits and colimits exist on both sides, it
creates them. The source's argument, endowing the abelian colimit with the endomorphisms
`λ_L` by the universal property, is the content of these preservation results; small means
indexed by a category in the universe `max (u + 1) r` of the coefficients.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FK]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (X : Scheme.{u})

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp

/-- Forgetting the module structure of étale sheaves of `Λ`-modules preserves small limits. -/
instance etaleModuleForgetAb_preservesLimitsOfSize :
    PreservesLimitsOfSize.{max (u + 1) r, max (u + 1) r} (etaleModuleForgetAb.{u, r} Λ X) :=
  preservesLimits_of_natIso (etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ X)

/-- Forgetting the module structure of étale sheaves of `Λ`-modules preserves small colimits. -/
instance etaleModuleForgetAb_preservesColimitsOfSize :
    PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r} (etaleModuleForgetAb.{u, r} Λ X) :=
  preservesColimits_of_natIso (etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ X)

/-- Forgetting the module structure of étale sheaves of `Λ`-modules reflects small limits. -/
instance etaleModuleForgetAb_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{max (u + 1) r, max (u + 1) r} (etaleModuleForgetAb.{u, r} Λ X) where
  reflectsLimitsOfShape := reflectsLimitsOfShape_of_reflectsIsomorphisms

/-- Forgetting the module structure of étale sheaves of `Λ`-modules reflects small colimits. -/
instance etaleModuleForgetAb_reflectsColimitsOfSize :
    ReflectsColimitsOfSize.{max (u + 1) r, max (u + 1) r} (etaleModuleForgetAb.{u, r} Λ X) where
  reflectsColimitsOfShape := reflectsColimitsOfShape_of_reflectsIsomorphisms

/-- **Small limits of étale sheaves of `Λ`-modules are computed in abelian sheaves**: the
forgetful functor creates them. -/
@[instance_reducible, weil "lem_fk104_lambda_module_sheaf_category_abelian"]
def etaleModuleForgetAbCreatesLimits :
    CreatesLimitsOfSize.{max (u + 1) r, max (u + 1) r} (etaleModuleForgetAb.{u, r} Λ X) where
  CreatesLimitsOfShape := { CreatesLimit := createsLimitOfReflectsIsomorphismsOfPreserves }

/-- **Small colimits of étale sheaves of `Λ`-modules are computed in abelian sheaves**: the
forgetful functor creates them. -/
@[instance_reducible, weil "lem_fk104_lambda_module_sheaf_category_abelian"]
def etaleModuleForgetAbCreatesColimits :
    CreatesColimitsOfSize.{max (u + 1) r, max (u + 1) r} (etaleModuleForgetAb.{u, r} Λ X) where
  CreatesColimitsOfShape := { CreatesColimit := createsColimitOfReflectsIsomorphismsOfPreserves }

variable {Λ X} {K : Type (max (u + 1) r)} [Category.{max (u + 1) r} K]

/-- **The `Λ`-module structure on a limit of abelian sheaves is unique**: two cones of sheaves of
`Λ`-modules over the same diagram whose underlying cones of abelian sheaves are identified with
one limit cone are isomorphic by a unique isomorphism lying over that identification. -/
@[weil "lem_fk104_lambda_module_sheaf_category_abelian"]
theorem existsUnique_coneIso_of_mapCone_iso {F : K ⥤ EtaleModules.{u, r} Λ X}
    {c : Cone (F ⋙ etaleModuleForgetAb.{u, r} Λ X)} (hc : IsLimit c) (c₁ c₂ : Cone F)
    (e₁ : (etaleModuleForgetAb.{u, r} Λ X).mapCone c₁ ≅ c)
    (e₂ : (etaleModuleForgetAb.{u, r} Λ X).mapCone c₂ ≅ c) :
    ∃! f : c₁ ≅ c₂,
      (Cone.functoriality F (etaleModuleForgetAb.{u, r} Λ X)).mapIso f = e₁ ≪≫ e₂.symm := by
  have h₁ : IsLimit c₁ := isLimitOfReflects _ (hc.ofIsoLimit e₁.symm)
  have h₂ : IsLimit c₂ := isLimitOfReflects _ (hc.ofIsoLimit e₂.symm)
  have hU₂ : IsLimit ((etaleModuleForgetAb.{u, r} Λ X).mapCone c₂) := hc.ofIsoLimit e₂.symm
  refine ⟨h₁.uniqueUpToIso h₂, ?_, fun f _ => ?_⟩
  · ext1
    exact hU₂.uniq_cone_morphism
  · ext1
    exact h₂.uniq_cone_morphism

/-- **The `Λ`-module structure on a colimit of abelian sheaves is unique**: two cocones of
sheaves of `Λ`-modules over the same diagram whose underlying cocones of abelian sheaves are
identified with one colimit cocone are isomorphic by a unique isomorphism lying over that
identification. -/
@[weil "lem_fk104_lambda_module_sheaf_category_abelian"]
theorem existsUnique_coconeIso_of_mapCocone_iso {F : K ⥤ EtaleModules.{u, r} Λ X}
    {c : Cocone (F ⋙ etaleModuleForgetAb.{u, r} Λ X)} (hc : IsColimit c) (c₁ c₂ : Cocone F)
    (e₁ : (etaleModuleForgetAb.{u, r} Λ X).mapCocone c₁ ≅ c)
    (e₂ : (etaleModuleForgetAb.{u, r} Λ X).mapCocone c₂ ≅ c) :
    ∃! f : c₁ ≅ c₂,
      (Cocone.functoriality F (etaleModuleForgetAb.{u, r} Λ X)).mapIso f = e₁ ≪≫ e₂.symm := by
  have h₁ : IsColimit c₁ := isColimitOfReflects _ (hc.ofIsoColimit e₁.symm)
  have h₂ : IsColimit c₂ := isColimitOfReflects _ (hc.ofIsoColimit e₂.symm)
  have hU₁ : IsColimit ((etaleModuleForgetAb.{u, r} Λ X).mapCocone c₁) := hc.ofIsoColimit e₁.symm
  refine ⟨h₁.uniqueUpToIso h₂, ?_, fun f _ => ?_⟩
  · ext1
    exact hU₁.uniq_cocone_morphism
  · ext1
    exact h₁.uniq_cocone_morphism

/-- **Exactness of sheaves of `Λ`-modules is exactness of abelian sheaves**: a short complex of
étale sheaves of `Λ`-modules is exact if and only if the underlying short complex of abelian
sheaves is. -/
@[weil "lem_fk104_lambda_module_sheaf_category_abelian"]
theorem etaleModuleForgetAb_exact_map_iff (S : ShortComplex (EtaleModules.{u, r} Λ X)) :
    (S.map (etaleModuleForgetAb.{u, r} Λ X)).Exact ↔ S.Exact :=
  S.exact_map_iff_of_faithful _

/-- **Exactness of sequences of sheaves of `Λ`-modules is exactness of abelian sheaves**: a
sequence of composable morphisms of étale sheaves of `Λ`-modules is exact if and only if the
underlying sequence of abelian sheaves is. -/
@[weil "lem_fk104_lambda_module_sheaf_category_abelian"]
theorem etaleModuleForgetAb_composableArrows_exact_iff {n : ℕ}
    (S : ComposableArrows (EtaleModules.{u, r} Λ X) n) :
    ComposableArrows.Exact (S ⋙ etaleModuleForgetAb.{u, r} Λ X) ↔ S.Exact := by
  have hc : ComposableArrows.IsComplex (S ⋙ etaleModuleForgetAb.{u, r} Λ X) ↔ S.IsComplex :=
    ⟨fun h => ⟨fun i hi => (etaleModuleForgetAb.{u, r} Λ X).map_injective (by
        simpa using h.zero i hi)⟩,
      fun h => ⟨fun i hi => by
        change (etaleModuleForgetAb.{u, r} Λ X).map _ ≫ (etaleModuleForgetAb.{u, r} Λ X).map _ = 0
        rw [← Functor.map_comp, h.zero i hi, Functor.map_zero]⟩⟩
  refine ⟨fun h => ⟨hc.1 h.toIsComplex, fun i hi => ?_⟩,
    fun h => ⟨hc.2 h.toIsComplex, fun i hi => ?_⟩⟩
  · exact (etaleModuleForgetAb_exact_map_iff _).1 (h.exact i hi)
  · exact (etaleModuleForgetAb_exact_map_iff _).2 (h.exact i hi)

end Stacks.EtaleCohomology
