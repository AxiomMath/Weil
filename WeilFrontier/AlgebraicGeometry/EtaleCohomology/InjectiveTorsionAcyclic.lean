module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# Underlying abelian sheaves of injective sheaves of modules on the small étale site

Let `Λ` be a ring, `X` a scheme and `I` an injective sheaf of `Λ`-modules on the small étale
site of `X`. The underlying abelian sheaf `I_ab` is in general not an injective abelian sheaf,
but it behaves like one for the functors of étale cohomology:

* its cohomology over every object `U` of the small étale site vanishes in positive degrees;
* for every morphism of schemes `p : X ⟶ S` its higher direct images `R^q p_* I_ab` vanish for
  `q > 0`;
* the direct image `p_* I_ab` is the underlying abelian sheaf of the injective sheaf of
  `Λ`-modules `p_* I`, so its cohomology over `S` vanishes in positive degrees as well.

Moreover every abelian sheaf killed by an integer `n` is a sheaf of `ℤ/nℤ`-modules, so it embeds
into the underlying abelian sheaf of an injective sheaf of `ℤ/nℤ`-modules. Together these say that
sheaves killed by `n` can be effaced by sheaves that are acyclic for `Γ(X, -)`, for `p_*` and for
`Γ(S, p_* -)`.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_sections_forget_injective`:
  `H^q(U, I_ab) = 0` for `q > 0` and every étale `U → X`.
* `Stacks.EtaleCohomology.isZero_rightDerived_pushforward_forget_injective`:
  `R^q p_* I_ab = 0` for `q > 0`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_forget_injective`: `H^q(X, I_ab) = 0` for `q > 0`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_pushforward_forget_injective`:
  `H^q(S, p_* I_ab) = 0` for `q > 0`.
* `Stacks.EtaleCohomology.exists_mono_forget_injective`: an abelian sheaf killed by `n` embeds
  into the underlying abelian sheaf of an injective sheaf of `ℤ/nℤ`-modules.

## Implementation notes

The vanishing statements are [Stacks, Tag 03FD] in the form proved for sheaves of modules over a
sheaf of rings on an arbitrary site, transported along the equivalence between sheaves of
`Λ`-modules and sheaves of modules over the constant sheaf of rings `Λ̲`. The higher direct images
use the description of `R^q p_*` as the sheafification of `V ↦ H^q(X ×_S V, -)`
([Stacks, Tag 072W]). The quasi-compactness and quasi-separatedness of `p` play no role.

The general statements have coefficients in `AddCommGrpCat.{max (u + 1) r}` for a ring
`Λ : Type r`; the forms with `smallEtalePushforwardAb`, whose coefficients are
`AddCommGrpCat.{u + 1}`, take `Λ : Type`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Vanishing

variable (Λ : Type r) [Ring Λ] {X S : Scheme.{u}} (p : X ⟶ S)

/-- **[Stacks, Tag 03FD] over an object of the small étale site.** The underlying abelian sheaf
of an injective sheaf of `Λ`-modules has vanishing cohomology in positive degrees over every
object `U` of the small étale site. -/
theorem isZero_rightDerived_sections_forget_injective (I : EtaleModules.{u, r} Λ X)
    [Injective I] (U : X.Etale) (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj
      (op U)).rightDerived q).obj ((etaleModuleForgetAb.{u, r} Λ X).obj I)) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  let E := etaleModuleSheafEquivalence.{u, r} Λ X
  have : Injective (E.functor.obj I) := E.symm.toAdjunction.map_injective I inferInstance
  have : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) r} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, r}
      (J := X.smallEtaleTopology)
  have : HasExt.{max (u + 1) r} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, r}
      (J := X.smallEtaleTopology)
  exact (Cohomology.InjectiveModuleSheafAcyclicity.isZero_rightDerived_sections_toSheaf_succ.{r}
      X.smallEtaleTopology (etaleConstantRingSheaf.{u, r} Λ X) (E.functor.obj I) U q).of_iso
    ((((sheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj
      (op U)).rightDerived (q + 1)).mapIso
      ((etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ X).app I).symm)

/-- **Higher direct images of the underlying abelian sheaf of an injective sheaf of modules
vanish.** For any morphism of schemes `p : X ⟶ S` and any injective sheaf `I` of `Λ`-modules on
the small étale site of `X`, `R^q p_* I_ab = 0` for `q > 0`. -/
theorem isZero_rightDerived_sheafPushforwardContinuous_forget_injective
    (I : EtaleModules.{u, r} Λ X) [Injective I] (q : ℕ) (hq : 0 < q) :
    IsZero ((((smallEtaleBaseChange p).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) r} S.smallEtaleTopology X.smallEtaleTopology).rightDerived
        q).obj ((etaleModuleForgetAb.{u, r} Λ X).obj I)) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  let E := etaleModuleSheafEquivalence.{u, r} Λ X
  have : Injective (E.functor.obj I) := E.symm.toAdjunction.map_injective I inferInstance
  have : X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) r} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, r}
      (J := X.smallEtaleTopology)
  have : HasExt.{max (u + 1) r} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, r}
      (J := X.smallEtaleTopology)
  exact (Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{r}
      S.smallEtaleTopology X.smallEtaleTopology (smallEtaleBaseChange p)
      (etaleConstantRingSheaf.{u, r} Λ X) (E.functor.obj I) q).of_iso
    ((((smallEtaleBaseChange p).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) r} S.smallEtaleTopology X.smallEtaleTopology).rightDerived
        (q + 1)).mapIso
      ((etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ X).app I).symm)

/-- The direct image of the underlying abelian sheaf of a sheaf of `Λ`-modules is the underlying
abelian sheaf of its direct image as a sheaf of `Λ`-modules. -/
def sheafPushforwardContinuousForgetAbIso (F : EtaleModules.{u, r} Λ X) :
    ((smallEtaleBaseChange p).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) r} S.smallEtaleTopology X.smallEtaleTopology).obj
        ((etaleModuleForgetAb.{u, r} Λ X).obj F) ≅
      (etaleModuleForgetAb.{u, r} Λ S).obj ((etaleModuleDirectImage.{u, r} Λ p).obj F) :=
  Iso.refl _

/-- **`H^q(X, I_ab) = 0` for `q > 0`**, `I` an injective sheaf of `Λ`-modules. -/
theorem subsingleton_sheafH_forget_injective
    [HasExt.{max (u + 1) r} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})]
    (I : EtaleModules.{u, r} Λ X) [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{max (u + 1) r} ((etaleModuleForgetAb.{u, r} Λ X).obj I) q) := by
  have := Stacks.Cohomology.GlobalSections.additive_Γ.{max (u + 1) r} X.smallEtaleTopology
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{r}
    X.smallEtaleTopology _ q).2
    (((Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ _).1
      (rightAcyclic_Γ_etaleModuleForgetAb_obj.{u, r} Λ X I)) q hq)

/-- **`H^q(S, p_* I_ab) = 0` for `q > 0`**, `I` an injective sheaf of `Λ`-modules: `p_* I_ab` is
the underlying abelian sheaf of the injective sheaf of `Λ`-modules `p_* I`. -/
theorem subsingleton_sheafH_sheafPushforwardContinuous_forget_injective
    [HasExt.{max (u + 1) r} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r})]
    (I : EtaleModules.{u, r} Λ X) [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{max (u + 1) r} (((smallEtaleBaseChange p).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) r} S.smallEtaleTopology X.smallEtaleTopology).obj
        ((etaleModuleForgetAb.{u, r} Λ X).obj I)) q) := by
  have : Injective ((etaleModuleDirectImage.{u, r} Λ p).obj I) :=
    (etaleModuleDirectImage.{u, r} Λ p).injective_obj I
  exact subsingleton_sheafH_forget_injective Λ ((etaleModuleDirectImage.{u, r} Λ p).obj I) q hq

end Vanishing

section SmallEtalePushforwardAb

variable (Λ : Type) [Ring Λ] {X S : Scheme.{u}} (p : X ⟶ S)

/-- **`R^q p_* I_ab = 0` for `q > 0`**, `I` an injective sheaf of `Λ`-modules, for the direct
image `smallEtalePushforwardAb p` of abelian sheaves. -/
theorem isZero_rightDerived_pushforward_forget_injective
    (I : EtaleModules.{u, 0} Λ X) [Injective I] (q : ℕ) (hq : 0 < q) :
    IsZero (((smallEtalePushforwardAb p).rightDerived q).obj
      ((etaleModuleForgetAb.{u, 0} Λ X).obj I)) :=
  isZero_rightDerived_sheafPushforwardContinuous_forget_injective Λ p I q hq

/-- **`H^q(S, p_* I_ab) = 0` for `q > 0`**, `I` an injective sheaf of `Λ`-modules, for the direct
image `smallEtalePushforwardAb p` of abelian sheaves. -/
theorem subsingleton_sheafH_pushforward_forget_injective
    [HasExt.{u + 1} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (I : EtaleModules.{u, 0} Λ X) [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((smallEtalePushforwardAb p).obj
      ((etaleModuleForgetAb.{u, 0} Λ X).obj I)) q) :=
  subsingleton_sheafH_sheafPushforwardContinuous_forget_injective Λ p I q hq

end SmallEtalePushforwardAb

section Embedding

variable {X : Scheme.{u}} (n : ℕ)

/-- **An abelian sheaf killed by `n` embeds into the underlying abelian sheaf of an injective
sheaf of `ℤ/nℤ`-modules.** Such a sheaf is a sheaf of `ℤ/nℤ`-modules, and that sheaf embeds into
an injective one; forgetting the module structure preserves monomorphisms. -/
theorem exists_mono_forget_injective (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : (n : ℤ) • 𝟙 F = 0) :
    ∃ (I : EtaleModules.{u, 0} (ZMod n) X) (_ : Injective I)
      (i : F ⟶ (etaleModuleForgetAb.{u, 0} (ZMod n) X).obj I), Mono i := by
  have hF' : n • 𝟙 F = 0 := by rwa [← natCast_zsmul]
  let M : EtaleModules.{u, 0} (ZMod n) X := Stacks.ModuleCatLift.sheafOfEndAction (ZMod n)
    X.smallEtaleTopology F (ZMod.castHom (ringChar.dvd (by rwa [← nsmul_one])) (End F))
  let e : (etaleModuleForgetAb.{u, 0} (ZMod n) X).obj M ≅ F := Iso.refl _
  refine ⟨Injective.under M, inferInstance,
    e.inv ≫ (etaleModuleForgetAb.{u, 0} (ZMod n) X).map (Injective.ι M), ?_⟩
  have : Mono ((etaleModuleForgetAb.{u, 0} (ZMod n) X).map (Injective.ι M)) :=
    Functor.map_mono _ _
  exact mono_comp _ _

end Embedding

end Stacks.EtaleCohomology

end
