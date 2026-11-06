module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyFilteredColimitsTypeU
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoefficientUniverseLift
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.Defs.CategoryTheory.Sites.SheafCohomology.Basic
public import Weil.Attr

/-!
# Étale cohomology of a finite disjoint union of open subschemes

Let `X` be a scheme of a big étale site `B` and `X = U_1 ⊔ ⋯ ⊔ U_r` a decomposition into finitely
many pairwise disjoint open subschemes, the images of open immersions `j_a : U_a ⟶ X`. For every
abelian sheaf `F` on the small étale site of `X` and every `n`, the restriction maps induce an
isomorphism
`H^n(X, F) ≅ ∏_a H^n(U_a, F|_{U_a})`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.restrict`: restriction of abelian sheaves on the small étale
  site along an étale morphism `j : U ⟶ X`, `(F|_U)(V) = F(V)`.
* `AlgebraicGeometry.SmallEtale.cohomologyRestrict`: the restriction map
  `H^n(X, F) → H^n(U, F|_U)` along an open immersion.
* `AlgebraicGeometry.SmallEtale.cohomologyAddEquivPi`: the isomorphism
  `H^n(X, F) ≃+ ∏_a H^n(U_a, F|_{U_a})`.

## Main results

* `AlgebraicGeometry.SmallEtale.bijective_cohomologyRestrict_pi`: the restriction maps to the
  members of a finite disjoint open decomposition together form a bijection.

## Implementation notes

The result is Stacks' `Stacks.EtaleCohomology.bijective_etaleCohomologyPullback_pi`, which is
stated on Mathlib's small étale site `X.smallEtaleTopology` with coefficients in
`AddCommGrpCat.{u + 1}`, transported to the bounded small étale site
`AlgebraicGeometry.SmallEtale` with coefficients in `AddCommGrpCat.{u}`. The transport has two
steps: raising the coefficient universe does not change cohomology
(`Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv`; the universe lift preserves injective
sheaves because the site is essentially small), and the bounded site is a dense subsite of
Mathlib's (`Stacks.Cohomology.DenseSubsite.hAddEquiv`). Restriction along `j` is defined through
Mathlib's site, where it is precomposition with `Scheme.Etale.smallEtaleCompose j`; the
restriction map on cohomology is the transport of Stacks' pull back map
`Stacks.EtaleCohomology.etaleCohomologyPullback`, which is the action of restriction on `Ext`
(`Stacks.EtaleCohomology.etaleCohomologyPullback_eq_restriction`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- Raising the coefficient universe of abelian presheaves on the small étale site preserves
injective objects: the site is essentially small, so this is the statement on a small model. -/
theorem preservesInjectiveObjects_whiskeringRight_uliftFunctor :
    ((Functor.whiskeringRight (SmallEtale B X hX)ᵒᵖ AddCommGrpCat.{u} AddCommGrpCat.{u + 1}).obj
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesInjectiveObjects := by
  have := Stacks.Cohomology.CoefficientLowering.uliftFunctor_preservesInjectiveObjects.{u + 1, u}
  have := Stacks.Cohomology.CoefficientLowering.whiskeringRight_preservesInjectiveObjects
    (C := (SmallModel.{u} (SmallEtale B X hX))ᵒᵖ) AddCommGrpCat.uliftFunctor.{u + 1, u}
  let e : (SmallEtale B X hX)ᵒᵖ ≌ (SmallModel.{u} (SmallEtale B X hX))ᵒᵖ :=
    (equivSmallModel _).op
  refine ⟨fun {F} hF ↦ ?_⟩
  let E := e.congrLeft (E := AddCommGrpCat.{u})
  have : Injective (E.functor.obj F) := E.symm.toAdjunction.map_injective _ hF
  have h1 : Injective ((E.functor.obj F) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
    ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u + 1, u}).injective_obj
      (E.functor.obj F)
  let E' := e.congrLeft (E := AddCommGrpCat.{u + 1})
  have : Injective (E'.inverse.obj ((E.functor.obj F) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})) :=
    E'.toAdjunction.map_injective _ h1
  exact Injective.of_iso
    (Functor.isoWhiskerRight (E.unitIso.app F).symm AddCommGrpCat.uliftFunctor.{u + 1, u}) this

/-- Raising the coefficient universe of abelian sheaves on the small étale site preserves injective
objects: an injective sheaf is an injective presheaf. -/
theorem preservesInjectiveObjects_sheafCompose_uliftFunctor :
    (sheafCompose (topology B X hX)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesInjectiveObjects := by
  have := preservesInjectiveObjects_whiskeringRight_uliftFunctor B X hX
  refine ⟨fun {F} hF ↦ ?_⟩
  have : Injective F.obj := (sheafificationAdjunction _ AddCommGrpCat.{u}).map_injective _ hF
  have : Injective (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
    ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{u + 1, u}).injective_obj F.obj
  exact Functor.injective_of_map_injective (sheafToPresheaf _ AddCommGrpCat.{u + 1})
    (show Injective (F.obj ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) from this)

/-- Abelian sheaves on the small étale site with coefficients in `AddCommGrpCat.{u + 1}` have
enough injectives. -/
theorem enoughInjectives_sheaf_succ :
    EnoughInjectives (Sheaf (topology B X hX) AddCommGrpCat.{u + 1}) :=
  have : EssentiallySmall.{u + 1} (SmallEtale B X hX) := essentiallySmall_lift.{u + 1, u} _
  Stacks.Cohomology.CoefficientLowering.enoughInjectives_sheaf_essentiallySmall _

/-- Abelian sheaves on the small étale site with coefficients in `AddCommGrpCat.{u + 1}` have
`Ext`-groups in `Type (u + 1)`. Not an instance, following Mathlib's policy for `HasExt`. -/
theorem hasExt_sheaf_succ : HasExt.{u + 1} (Sheaf (topology B X hX) AddCommGrpCat.{u + 1}) :=
  have := enoughInjectives_sheaf_succ B X hX
  hasExt_of_enoughInjectives _

variable {B X hX}

/-- Cohomology of an abelian sheaf on the small étale site, at the coefficient universe `u`, is
the cohomology of the corresponding sheaf on Mathlib's small étale site with coefficients raised
to `u + 1`. -/
def cohomologyAddEquivUlift [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{u}) (n : ℕ) :
    F.H n ≃+ Sheaf.H.{u + 1} ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj
      ((sheafCompose (topology B X hX) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F)) n :=
  letI := hasExt_sheaf_succ B X hX
  letI := enoughInjectives_sheaf_succ B X hX
  letI := preservesInjectiveObjects_sheafCompose_uliftFunctor B X hX
  letI := Stacks.Sheaves.UniverseLift.preservesSheafification_uliftFunctor.{u + 1, u, u, u + 1}
    (J := topology B X hX)
  let L := sheafCompose (topology B X hX) AddCommGrpCat.uliftFunctor.{u + 1, u}
  let E := sheafEquiv B X hX AddCommGrpCat.{u + 1}
  (Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv.{u, w, u + 1, u + 1} _ F n).trans <|
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
      (E.unitIso.app (L.obj F)) n).trans
    (Stacks.Cohomology.DenseSubsite.hAddEquiv.{u + 1} (topology B X hX) X.smallEtaleTopology
      (toEtaleSite B X hX) (E.functor.obj (L.obj F)) n).symm

/-- Restriction of abelian sheaves on the small étale site along an étale morphism `j : U ⟶ X`:
`(F|_U)(V) = F(V)` for `V` étale over `U`, regarded as étale over `X` through `j`. -/
def restrict {U : Scheme.{u}} (hU : B.Contains U) (j : U ⟶ X) [Etale j] :
    Sheaf (topology B X hX) AddCommGrpCat.{u} ⥤ Sheaf (topology B U hU) AddCommGrpCat.{u} :=
  (sheafEquiv B X hX AddCommGrpCat.{u}).functor ⋙
    (Scheme.Etale.smallEtaleCompose j).sheafPushforwardContinuous AddCommGrpCat.{u}
      U.smallEtaleTopology X.smallEtaleTopology ⋙
    (sheafEquiv B U hU AddCommGrpCat.{u}).inverse

/-- The restriction of a sheaf along an étale `j : U ⟶ X`, read on Mathlib's site with
coefficients raised to `u + 1`, is the inverse image of the transported sheaf. -/
def restrictUliftIso {U : Scheme.{u}} (hU : B.Contains U) (j : U ⟶ X) [Etale j]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{u}) :
    (Stacks.EtaleCohomology.smallEtalePullbackAb j).obj
        ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj
          ((sheafCompose (topology B X hX) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F)) ≅
      (sheafEquiv B U hU AddCommGrpCat.{u + 1}).functor.obj
        ((sheafCompose (topology B U hU) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          ((restrict hU j).obj F)) := by
  let EX := sheafEquiv B X hX AddCommGrpCat.{u}
  let EX' := sheafEquiv B X hX AddCommGrpCat.{u + 1}
  let EU' := sheafEquiv B U hU AddCommGrpCat.{u + 1}
  let LX := sheafCompose (topology B X hX) AddCommGrpCat.uliftFunctor.{u + 1, u}
  let LXM := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  let LUM := sheafCompose U.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
  let R := (Scheme.Etale.smallEtaleCompose j).sheafPushforwardContinuous AddCommGrpCat.{u}
      U.smallEtaleTopology X.smallEtaleTopology
  let R' := (Scheme.Etale.smallEtaleCompose j).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      U.smallEtaleTopology X.smallEtaleTopology
  -- `F` transported and lifted, in either order
  let e₁ : LXM.obj (EX.functor.obj F) ≅ EX'.functor.obj (LX.obj F) :=
    (EX'.counitIso.app (LXM.obj (EX.functor.obj F))).symm ≪≫
      EX'.functor.mapIso (LX.mapIso (EX.unitIso.app F).symm)
  exact (Stacks.EtaleCohomology.smallEtalePullbackAbRestrictionIso j).app _ ≪≫
    R'.mapIso e₁.symm ≪≫ (EU'.counitIso.app (LUM.obj (R.obj (EX.functor.obj F)))).symm

variable {ι : Type} [Finite ι] {U : ι → Scheme.{u}} (hU : ∀ a, B.Contains (U a))
  (j : ∀ a, U a ⟶ X) [∀ a, IsOpenImmersion (j a)]

/-- The restriction map `H^n(X, F) → H^n(U, F|_U)` on étale cohomology along an open immersion
`j : U ⟶ X`. -/
def cohomologyRestrict {U : Scheme.{u}} (hU : B.Contains U) (j : U ⟶ X) [IsOpenImmersion j]
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf (topology B U hU) AddCommGrpCat.{u})]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{u}) (n : ℕ) :
    F.H n →+ ((restrict hU j).obj F).H n :=
  (cohomologyAddEquivUlift ((restrict hU j).obj F) n).symm.toAddMonoidHom.comp <|
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
      (restrictUliftIso hU j F) n).toAddMonoidHom.comp <|
    (Stacks.EtaleCohomology.etaleCohomologyPullback j (𝟙 _) n).comp
      (cohomologyAddEquivUlift F n).toAddMonoidHom

variable [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})]
  [∀ a, HasExt.{w} (Sheaf (topology B (U a) (hU a)) AddCommGrpCat.{u})]
  (hdisj : Pairwise fun a b => Disjoint (Set.range (j a).base) (Set.range (j b).base))
  (hcov : ⋃ a, Set.range (j a).base = Set.univ)

include hdisj hcov in
/-- **Étale cohomology of a finite disjoint union of open subschemes.** If `X` is the disjoint
union of the open subschemes `U a`, the images of open immersions `j a : U a ⟶ X`, then for
every abelian sheaf `F` on the small étale site of `X` and every `n` the restriction maps
`H^n(X, F) → ∏ a, H^n(U a, F|_{U a})` together form a bijection. -/
@[weil "lem_fk105_cohomology_finite_disjoint_union"]
theorem bijective_cohomologyRestrict_pi (F : Sheaf (topology B X hX) AddCommGrpCat.{u})
    (n : ℕ) :
    Function.Bijective (fun (x : F.H n) a => cohomologyRestrict (hU a) (j a) F n x) := by
  have := Fintype.ofFinite ι
  have h := Stacks.EtaleCohomology.bijective_etaleCohomologyPullback_pi j hdisj hcov
    ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj
      ((sheafCompose (topology B X hX) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F)) n
  have hU' : ∀ a, Function.Bijective (fun y =>
      (cohomologyAddEquivUlift ((restrict (hU a) (j a)).obj F) n).symm
        (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
          (restrictUliftIso (hU a) (j a) F) n y)) := fun a =>
    (cohomologyAddEquivUlift ((restrict (hU a) (j a)).obj F) n).symm.bijective.comp
      (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
        (restrictUliftIso (hU a) (j a) F) n).bijective
  exact ((Function.Bijective.piMap hU').comp h).comp (cohomologyAddEquivUlift F n).bijective

include hdisj hcov in
/-- **Étale cohomology of a finite disjoint union of open subschemes**, as an additive
equivalence `H^n(X, F) ≃+ ∏ a, H^n(U a, F|_{U a})` whose components are the restriction maps. -/
@[weil "lem_fk105_cohomology_finite_disjoint_union"]
def cohomologyAddEquivPi (F : Sheaf (topology B X hX) AddCommGrpCat.{u}) (n : ℕ) :
    F.H n ≃+ ∀ a, ((restrict (hU a) (j a)).obj F).H n :=
  AddEquiv.ofBijective (AddMonoidHom.pi fun a => cohomologyRestrict (hU a) (j a) F n)
    (bijective_cohomologyRestrict_pi hU j hdisj hcov F n)

/-- The components of `AlgebraicGeometry.SmallEtale.cohomologyAddEquivPi` are the restriction
maps. -/
theorem cohomologyAddEquivPi_apply (F : Sheaf (topology B X hX) AddCommGrpCat.{u}) (n : ℕ)
    (x : F.H n) (a : ι) :
    cohomologyAddEquivPi hU j hdisj hcov F n x a = cohomologyRestrict (hU a) (j a) F n x :=
  rfl

end AlgebraicGeometry.SmallEtale
