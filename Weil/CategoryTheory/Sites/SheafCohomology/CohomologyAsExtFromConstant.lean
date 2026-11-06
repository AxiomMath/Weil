module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleSheafAcyclicity
public import Weil.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.Defs.CategoryTheory.Sites.SheafCohomology.Basic
public import Weil.Attr

/-!
# Cohomology of a sheaf of modules as `Ext` out of the constant sheaf

Let `Λ` be a ring and `F` a sheaf of `Λ`-modules on a site with a terminal object `T` (for
instance the small étale site of a scheme `Z`, with `T = Z`). Morphisms of sheaves of
`Λ`-modules out of the constant sheaf `Λ_T` are the sections over `T`:
`Hom_Λ(Λ_T, G) = G(T)`, naturally in `G`. Deriving this identification gives, for every `p ≥ 0`,
an isomorphism
`Hᵖ(T, F) ≅ Extᵖ_Λ(Λ_T, F)`,
where the left side is the cohomology of the underlying abelian sheaf of `F` and the right side
is computed in the category of sheaves of `Λ`-modules.

The proof has three steps. Both `Extᵖ_Λ(Λ_T, -)` and the right derived functors of
`G ↦ Γ(T, G_ab)` are universal `δ`-functors extending the degree-zero identification, so they
agree. Forgetting the module structure is exact and sends injective sheaves of `Λ`-modules to
abelian sheaves acyclic for `Γ(T, -)` ([Stacks, Tag 03FD]), so the right derived functors of
`G ↦ Γ(T, G_ab)` are those of `Γ(T, -)` evaluated at `G_ab`. Finally the right derived functors
of `Γ(T, -)` on abelian sheaves are sheaf cohomology.

## Main definitions

* `CategoryTheory.Sheaf.constantSheafHomAddEquiv`: `Hom_Λ(Λ_T, G) ≃+ G(T)`.
* `CategoryTheory.Sheaf.extZeroConstantIsoForgetSections`: the same for degree-zero `Ext`, as an
  isomorphism of functors.
* `CategoryTheory.Sheaf.extFunctorObjConstantIsoFunctorH`: `Extᵖ_Λ(Λ_T, -) ≅ Hᵖ((-)_ab)`, as
  functors on sheaves of `Λ`-modules.
* `CategoryTheory.Sheaf.extConstantAddEquivH`: `Extᵖ_Λ(Λ_T, F) ≃+ Hᵖ(F_ab)`.
* `AlgebraicGeometry.SmallEtale.extConstantAddEquivH`: the same on the small étale site of a
  scheme.

## Implementation notes

The identification of `Extᵖ_Λ(Λ_T, -)` with the right derived functors of sections comes from the
universality of the two `δ`-functors
(`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso`), which only
asserts existence, so the isomorphisms here are chosen; in degree zero the first factor extends
`extZeroConstantIsoForgetSections`. The coefficient universe is the morphism universe of the
site, and the ring lives in it.

The source works on the site `Et(Z)` of noetherian separated étale `Z`-schemes; its sheaf
category is equivalent to that of `AlgebraicGeometry.SmallEtale`, the convention of this library,
and the statement here needs neither noetherianity nor separatedness.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.4
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian Opposite

universe v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type v) [Ring Λ]
  {T : C} (hT : IsTerminal T)

section HomFromConstant

variable [HasWeakSheafify J (ModuleCat.{v} Λ)]

/-- **`Hom_Λ(Λ_T, G) = G(T)`.** A morphism of sheaves of `Λ`-modules out of the constant sheaf
`Λ_T` is determined by the image of `1` in the sections over the terminal object `T`, and every
section occurs. -/
def constantSheafHomAddEquiv (F : Sheaf J (ModuleCat.{v} Λ)) :
    ((constantSheaf J (ModuleCat.{v} Λ)).obj (ModuleCat.of Λ Λ) ⟶ F) ≃+ F.obj.obj (op T) where
  toFun f := ((constantSheafAdj J (ModuleCat.{v} Λ) hT).homEquiv _ _ f).hom 1
  invFun x := ((constantSheafAdj J (ModuleCat.{v} Λ) hT).homEquiv _ _).symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ x))
  left_inv f := by
    rw [Equiv.symm_apply_eq]
    ext
    simp [LinearMap.toSpanSingleton_apply, ← map_smul]
  right_inv x := by
    simp
  map_add' f g := by
    simp only [Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add]
    rfl

/-- `constantSheafHomAddEquiv` is natural in the sheaf. -/
lemma constantSheafHomAddEquiv_comp {F F' : Sheaf J (ModuleCat.{v} Λ)}
    (f : (constantSheaf J (ModuleCat.{v} Λ)).obj (ModuleCat.of Λ Λ) ⟶ F) (φ : F ⟶ F') :
    constantSheafHomAddEquiv J Λ hT F' (f ≫ φ) =
      φ.hom.app (op T) (constantSheafHomAddEquiv J Λ hT F f) := by
  simp [constantSheafHomAddEquiv, Adjunction.homEquiv_naturality_right]

end HomFromConstant

section Comparison

variable [HasSheafify J (ModuleCat.{v} Λ)] [HasSheafify J AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})]

/-- Sections over `T` of the underlying abelian sheaf of a sheaf of `Λ`-modules. -/
abbrev forgetSections : Sheaf J (ModuleCat.{v} Λ) ⥤ AddCommGrpCat.{v} :=
  sheafCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v}) ⋙
    (sheafSections J AddCommGrpCat.{v}).obj (op T)

/-- Sections over `T` of the underlying abelian sheaf are left exact. -/
instance preservesFiniteLimits_forgetSections :
    PreservesFiniteLimits (forgetSections J Λ (T := T)) := by
  have := Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂.{v, v, v, u} J Λ
  unfold forgetSections
  infer_instance

/-- Forgetting the module structure of a sheaf of `Λ`-modules is additive. -/
instance additive_sheafCompose_forget₂ :
    (sheafCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})).Additive where
  map_add := rfl

/-- Sections over `T` of the underlying abelian sheaf are additive. -/
instance additive_forgetSections : (forgetSections J Λ (T := T)).Additive where
  map_add := rfl

variable [HasExt.{v} (Sheaf J (ModuleCat.{v} Λ))]

/-- Degree-zero `Ext` out of the constant sheaf `Λ` is the functor of sections over a terminal
object. -/
def extZeroConstantIsoForgetSections :
    extFunctorObj.{v} ((constantSheaf J (ModuleCat.{v} Λ)).obj (ModuleCat.of Λ Λ)) 0 ≅
      forgetSections J Λ (T := T) :=
  NatIso.ofComponents
    (fun F ↦ (Ext.addEquiv₀.trans (constantSheafHomAddEquiv J Λ hT F)).toAddCommGrpIso) (by
      intro F G f
      ext e
      exact (congrArg (constantSheafHomAddEquiv J Λ hT G)
          (ModuleSheafCohomology.addEquiv₀_comp_mk₀ e f)).trans
        (constantSheafHomAddEquiv_comp J Λ hT _ f))

variable [EnoughInjectives (Sheaf J (ModuleCat.{v} Λ))]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]

/-- `Extᵖ_Λ(Λ_T, -)` is the `p`-th right derived functor of `G ↦ Γ(T, G_ab)`. This is a chosen
isomorphism (see the implementation notes). -/
def extFunctorObjConstantIsoRightDerived (n : ℕ) :
    extFunctorObj.{v} ((constantSheaf J (ModuleCat.{v} Λ)).obj (ModuleCat.of Λ Λ)) n ≅
      (forgetSections J Λ (T := T)).rightDerived n :=
  (ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso _ _
    (extZeroConstantIsoForgetSections J Λ hT) n).some

/-- The right derived functors of `G ↦ Γ(T, G_ab)` on sheaves of `Λ`-modules are those of
`Γ(T, -)` on abelian sheaves, evaluated at `G_ab`: forgetting is exact and sends injective sheaves
of `Λ`-modules to `Γ(T, -)`-acyclic abelian sheaves ([Stacks, Tag 03FD]). -/
def rightDerivedForgetSectionsIso (n : ℕ) :
    (forgetSections J Λ (T := T)).rightDerived n ≅
      sheafCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v}) ⋙
        ((sheafSections J AddCommGrpCat.{v}).obj (op T)).rightDerived n :=
  have := Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂.{v, v, v, u} J Λ
  have := Stacks.Cohomology.ModuleSheaf.preservesFiniteColimits_sheafCompose_forget₂.{v, v, v, u}
    J Λ
  let := HasDerivedCategory.standard (Sheaf J AddCommGrpCat.{v})
  let := HasDerivedCategory.standard (Sheaf J (ModuleCat.{v} Λ))
  let := HasDerivedCategory.standard AddCommGrpCat.{v}
  Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _
    (fun I _ ↦ (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
      fun p hp ↦ Stacks.Cohomology.ModuleSheaf.isZero_rightDerived_sheafSections_of_injective.{v,
        v, v} Λ I T p hp) n

/-- **`Extᵖ_Λ(Λ_T, -) ≅ Hᵖ((-)_ab)`**, as functors on sheaves of `Λ`-modules, on a site with a
terminal object `T`. -/
def extFunctorObjConstantIsoFunctorH (n : ℕ) :
    extFunctorObj.{v} ((constantSheaf J (ModuleCat.{v} Λ)).obj (ModuleCat.of Λ Λ)) n ≅
      sheafCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v}) ⋙ functorH J n :=
  extFunctorObjConstantIsoRightDerived J Λ hT n ≪≫ rightDerivedForgetSectionsIso J Λ n ≪≫
    Functor.isoWhiskerLeft _ (functorHIsoRightDerivedSections J hT n).symm

/-- **Cohomology of a sheaf of modules as `Ext` out of the constant sheaf.** On a site with a
terminal object `T`, for a sheaf `F` of `Λ`-modules, `Extᵖ_Λ(Λ_T, F) ≃+ Hᵖ(F_ab)`. -/
def extConstantAddEquivH (F : Sheaf J (ModuleCat.{v} Λ)) (n : ℕ) :
    Ext ((constantSheaf J (ModuleCat.{v} Λ)).obj (ModuleCat.of Λ Λ)) F n ≃+
      ((sheafCompose J (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})).obj F).H n :=
  ((extFunctorObjConstantIsoFunctorH J Λ hT n).app F).addCommGroupIsoToAddEquiv

end Comparison

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Λ : Type u) [Ring Λ]

/-- Sheaves of `Λ`-modules on the small étale site have `Ext`-groups in the morphism universe of
the site. Not an instance, following Mathlib's policy for `CategoryTheory.HasExt`. -/
theorem hasExt_sheaf_moduleCat : HasExt.{u} (Sheaf (topology B S hS) (ModuleCat.{u} Λ)) :=
  hasExt_of_enoughInjectives _

/-- **Étale cohomology of a sheaf of modules as `Ext` out of the constant sheaf.** For a ring `Λ`,
a scheme `S` and a sheaf `F` of `Λ`-modules on the small étale site of `S`, for every `p ≥ 0`
there is an isomorphism `Hᵖ(S, F) ≅ Extᵖ_Λ(S; Λ_S, F)`, where `Hᵖ(S, F)` is the étale cohomology
of the underlying abelian sheaf and `Extᵖ_Λ` is computed among sheaves of `Λ`-modules. It is
derived from `Hom_Λ(Λ_S, G) = G(S)` (`CategoryTheory.Sheaf.constantSheafHomAddEquiv`). -/
@[weil "lem_fk104_cohomology_as_ext_from_constant"]
def extConstantAddEquivH (F : Sheaf (topology B S hS) (ModuleCat.{u} Λ)) (p : ℕ) :
    letI := hasExt_sheaf_moduleCat B S hS Λ
    letI := hasExt_sheaf B S hS
    Ext ((constantSheaf (topology B S hS) (ModuleCat.{u} Λ)).obj (ModuleCat.of Λ Λ)) F p ≃+
      ((sheafCompose (topology B S hS) (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F).H p :=
  letI := hasExt_sheaf_moduleCat B S hS Λ
  letI := hasExt_sheaf B S hS
  Sheaf.extConstantAddEquivH (topology B S hS) Λ (finalIsTerminal B S hS) F p

end AlgebraicGeometry.SmallEtale
