module

public import Weil.Attr
public import WeilFrontier.Algebra.Category.ModuleCat.ArLimitFunctorWellDefined
public import WeilFrontier.CategoryTheory.ObjectProperty.HomLAdicEqualsArHom
public import WeilFrontier.CategoryTheory.ObjectProperty.LAdicLimitFiniteModule
public import WeilFrontier.CategoryTheory.ObjectProperty.LAdicSystemFromLimit
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArLAdicSystem
public import WeilFrontier.RingTheory.AdicCompletion.Basic
public import WeilFrontier.RingTheory.AdicCompletion.FiniteModuleLAdicallyComplete
public import Mathlib.Algebra.Category.FGModuleCat.Basic

/-!
# A–R `l`-adic systems and finitely generated modules

Let `Λ` be a Noetherian ring, complete for the `l`-adic topology, with `Λ / l Λ` Artinian (for
instance `Λ = ℤ_l`). The projective-limit functor `F ↦ lim F` on the Artin–Rees category,
restricted to the full subcategory of A–R `l`-adic systems, takes values in finitely generated
`Λ`-modules and is an equivalence of this subcategory with the category of finitely generated
`Λ`-modules.

Since the limit functor sends A–R isomorphisms to isomorphisms, it suffices to treat `l`-adic
systems `F`, `G`. For those, every A–R morphism `F → G` is the class of a morphism of projective
systems, and a linear map `θ : lim F → lim G` comes from the unique morphism `h : F ⟶ G` with
`h_n ∘ π_n = π_n ∘ θ`, which exists because the projections `π_n : lim F → F_n` are surjective
with kernel `l^{n+1} lim F`. Essential surjectivity: a finitely generated module `M` is the limit
of the `l`-adic system `S(M) = (M / l^{n+1} M)_n`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.ArCategory.limFunctorArLAdic`: the projective-limit functor
  from the full subcategory of A–R `l`-adic systems to finitely generated `Λ`-modules.
* `CategoryTheory.ProjectiveSystem.ArCategory.arLAdicEquivFGModuleCat`: the resulting
  equivalence of categories.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.homOfLimMap`: the morphism of `l`-adic systems
  `F ⟶ G` inducing a given linear map `lim F → lim G`.

## Main results

* `CategoryTheory.ProjectiveSystem.IsArLAdic.finite_limFunctor_obj`: the limit of an A–R
  `l`-adic system is a finitely generated `Λ`-module.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.bijective_limFunctor_map`: for `l`-adic systems
  `F`, `G`, the limit functor is bijective on `Hom_AR(F, G) → Hom_Λ(lim F, lim G)`.
* `CategoryTheory.ProjectiveSystem.ArCategory.isEquivalence_limFunctorArLAdic`: the limit functor
  is an equivalence of the A–R `l`-adic systems with the finitely generated `Λ`-modules.

## Implementation notes

The source takes `Λ = ℤ_l`; the result is stated for any Noetherian ring `Λ`, `l`-adically
complete, with `Λ / l Λ` Artinian (`PadicInt` satisfies these hypotheses). Finitely generated
`Λ`-modules form Mathlib's `FGModuleCat Λ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- A linear map `q : M → B` whose kernel contains the kernel of a surjective linear map
`p : M → A` factors through `p`. -/
noncomputable def descOfSurjective {M A B : Type*} [AddCommGroup M] [Module Λ M] [AddCommGroup A]
    [Module Λ A] [AddCommGroup B] [Module Λ B] (p : M →ₗ[Λ] A) (hp : Function.Surjective p)
    (q : M →ₗ[Λ] B) (h : LinearMap.ker p ≤ LinearMap.ker q) : A →ₗ[Λ] B :=
  (LinearMap.ker p).liftQ q h ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap

@[simp]
lemma descOfSurjective_apply {M A B : Type*} [AddCommGroup M] [Module Λ M] [AddCommGroup A]
    [Module Λ A] [AddCommGroup B] [Module Λ B] (p : M →ₗ[Λ] A) (hp : Function.Surjective p)
    (q : M →ₗ[Λ] B) (h : LinearMap.ker p ≤ LinearMap.ker q) (x : M) :
    descOfSurjective p hp q h (p x) = q x := by
  have : (p.quotKerEquivOfSurjective hp).symm (p x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [descOfSurjective, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, this,
    Submodule.liftQ_apply]

namespace IsLAdicSystem

variable {F G : ProjectiveSystem.{v} Λ l} (hF : IsLAdicSystem F) (hG : IsLAdicSystem G)
include hF

/-- For an `l`-adic system `F`, every projection `π_n : lim F → F_n`, `n ∈ ℤ`, is surjective. -/
lemma surjective_limProj_int (n : ℤ) : Function.Surjective (F.limProj n) := by
  rcases lt_or_ge n 0 with hn | hn
  · intro y
    exact ⟨0, (ModuleCat.subsingleton_of_isZero (hF.isZero_of_neg n hn)).elim _ _⟩
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact hF.surjective_limProj k

include hG in
/-- For `l`-adic systems `F`, `G` and a linear map `θ : lim F → lim G`, the kernel of
`π_n : lim F → F_n` is contained in the kernel of `π_n ∘ θ : lim F → G_n`. -/
lemma ker_limProj_le_ker_limProj_comp
    (θ : ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] ModuleCat.sectionsSubmodule G.obj) (n : ℤ) :
    LinearMap.ker (F.limProj n) ≤ LinearMap.ker ((G.limProj n).comp θ) := by
  intro x hx
  rcases lt_or_ge n 0 with hn | hn
  · exact (ModuleCat.subsingleton_of_isZero (hG.isZero_of_neg n hn)).elim _ _
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hF.ker_limProj k] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_smul, map_smul]
    exact hG.pow_smul_eq_zero k _

/-- The morphism `h : F ⟶ G` of `l`-adic systems with `h_n ∘ π_n = π_n ∘ θ` for every `n`,
for a linear map `θ : lim F → lim G`. -/
noncomputable def homOfLimMap
    (θ : ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] ModuleCat.sectionsSubmodule G.obj) : F ⟶ G :=
  homMk (fun n => ModuleCat.ofHom (descOfSurjective (F.limProj n) (hF.surjective_limProj_int n)
      ((G.limProj n).comp θ) (hF.ker_limProj_le_ker_limProj_comp hG θ n))) (fun n => by
    ext y
    obtain ⟨x, rfl⟩ := hF.surjective_limProj_int n y
    have hFx := (mem_sectionsSubmodule_iff F x.1).1 x.2 n
    have hGx := (mem_sectionsSubmodule_iff G (θ x).1).1 (θ x).2 n
    have hFx' : F.transition n (F.limProj n x) = F.limProj (n - 1) x := hFx
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    rw [hFx', descOfSurjective_apply, descOfSurjective_apply]
    exact hGx)

lemma homOfLimMap_app_limProj
    (θ : ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] ModuleCat.sectionsSubmodule G.obj) (n : ℤ)
    (x : ModuleCat.sectionsSubmodule F.obj) :
    (app (hF.homOfLimMap hG θ) n).hom (F.limProj n x) = G.limProj n (θ x) :=
  descOfSurjective_apply _ _ _ _ x

/-- The limit of `q(homOfLimMap θ)` is `θ`. -/
lemma limFunctor_map_toArCategory_map_homOfLimMap
    (θ : ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] ModuleCat.sectionsSubmodule G.obj) :
    ArCategory.limFunctor.map ((toArCategory Λ l).map (hF.homOfLimMap hG θ)) =
      ModuleCat.ofHom θ := by
  ext x : 2
  apply Subtype.ext
  funext n
  obtain ⟨n⟩ := n
  exact (ArCategory.limFunctor_map_toArCategory_map_apply _ x n).trans
    (hF.homOfLimMap_app_limProj hG θ n x)

include hG in
/-- **The limit functor is fully faithful on `l`-adic systems.** For `l`-adic systems `F`, `G`,
`φ ↦ lim φ` is a bijection `Hom_AR(F, G) → Hom_Λ(lim F, lim G)`. -/
theorem bijective_limFunctor_map :
    Function.Bijective (fun φ : ArCategory.of F ⟶ ArCategory.of G =>
      ArCategory.limFunctor.map φ) := by
  have hq := hF.bijective_toArCategory_map (G := G) (hG.isZero_of_neg (-1) (by omega))
    hG.pow_smul_eq_zero
  refine ⟨fun φ ψ hφψ => ?_, fun θ => ?_⟩
  · obtain ⟨g, rfl⟩ := hq.2 φ
    obtain ⟨g', rfl⟩ := hq.2 ψ
    congr 1
    refine hom_ext fun n => ?_
    ext y
    obtain ⟨x, rfl⟩ := hF.surjective_limProj_int n y
    have h := congrArg (fun m => ((m.hom x : ModuleCat.sectionsSubmodule G.obj).1 (op n))) hφψ
    exact (ArCategory.limFunctor_map_toArCategory_map_apply g x n).symm.trans
      (h.trans (ArCategory.limFunctor_map_toArCategory_map_apply g' x n))
  · refine ⟨(toArCategory Λ l).map (hF.homOfLimMap hG θ.hom), ?_⟩
    exact hF.limFunctor_map_toArCategory_map_homOfLimMap hG θ.hom

end IsLAdicSystem

/-- The projective limit of an A–R `l`-adic system is a finitely generated `Λ`-module, when `Λ`
is `l`-adically precomplete. -/
@[weil "thm_fk112_limit_equivalence_ar_l_adic_finite_modules"]
theorem IsArLAdic.finite_limFunctor_obj [IsPrecomplete (Ideal.span {l}) Λ]
    {X : ArCategory.{v} Λ l} (hX : IsArLAdic X.obj) :
    Module.Finite Λ (ArCategory.limFunctor.obj X) := by
  have : Module.Finite Λ (ArCategory.limFunctor.obj (ArCategory.of hX.lAdicSystem)) :=
    hX.isLAdicSystem_lAdicSystem.finite_sectionsSubmodule
  exact Module.Finite.equiv (ArCategory.limFunctor.mapIso hX.arIso).symm.toLinearEquiv

namespace ArCategory

/-- The property of objects of the A–R category of being an `l`-adic system. -/
def isLAdicSystem : ObjectProperty (ArCategory.{v} Λ l) :=
  fun X => IsLAdicSystem X.obj

lemma isLAdicSystem_le_isArLAdic :
    (isLAdicSystem : ObjectProperty (ArCategory.{v} Λ l)) ≤ isArLAdic :=
  fun _ hX => IsLAdicSystem.isArLAdic hX

/-- The **projective-limit functor on A–R `l`-adic systems**: the restriction of
`limFunctor`, `F ↦ lim F`, to the full subcategory of A–R `l`-adic systems, with values in
finitely generated `Λ`-modules (`IsArLAdic.finite_limFunctor_obj`). -/
@[weil "thm_fk112_limit_equivalence_ar_l_adic_finite_modules"]
noncomputable def limFunctorArLAdic [IsPrecomplete (Ideal.span {l}) Λ] :
    (isArLAdic : ObjectProperty (ArCategory.{v} Λ l)).FullSubcategory ⥤ FGModuleCat.{v} Λ :=
  (ModuleCat.isFG.{v} Λ).lift (isArLAdic.ι ⋙ limFunctor)
    (fun X => (ModuleCat.isFG_iff _).2 (IsArLAdic.finite_limFunctor_obj X.property))

@[simp]
lemma limFunctorArLAdic_obj_obj [IsPrecomplete (Ideal.span {l}) Λ]
    (X : (isArLAdic : ObjectProperty (ArCategory.{v} Λ l)).FullSubcategory) :
    (limFunctorArLAdic.obj X).obj = limFunctor.obj X.obj := rfl

lemma limFunctorArLAdic_map_hom [IsPrecomplete (Ideal.span {l}) Λ]
    {X Y : (isArLAdic : ObjectProperty (ArCategory.{v} Λ l)).FullSubcategory} (φ : X ⟶ Y) :
    (limFunctorArLAdic.map φ).hom = limFunctor.map φ.hom := rfl

instance essSurj_ιOfLE_isLAdicSystem :
    (ObjectProperty.ιOfLE (isLAdicSystem_le_isArLAdic.{v} (Λ := Λ) (l := l))).EssSurj where
  mem_essImage X :=
    ⟨⟨of X.property.lAdicSystem, X.property.isLAdicSystem_lAdicSystem⟩,
      ⟨(isArLAdic.fullyFaithfulι.preimageIso X.property.arIso).symm⟩⟩

instance isEquivalence_ιOfLE_isLAdicSystem :
    (ObjectProperty.ιOfLE (isLAdicSystem_le_isArLAdic.{v} (Λ := Λ) (l := l))).IsEquivalence
    where

section Equivalence

variable [IsNoetherianRing Λ] [IsAdicComplete (Ideal.span {l}) Λ]
  [IsArtinianRing (Λ ⧸ Ideal.span {l})]

/-- The composite of the inclusion of `l`-adic systems with the limit functor. -/
noncomputable abbrev limFunctorLAdic :
    (isLAdicSystem : ObjectProperty (ArCategory.{v} Λ l)).FullSubcategory ⥤ FGModuleCat.{v} Λ :=
  ObjectProperty.ιOfLE isLAdicSystem_le_isArLAdic ⋙ limFunctorArLAdic

instance faithful_limFunctorLAdic : (limFunctorLAdic.{v} (Λ := Λ) (l := l)).Faithful where
  map_injective {X Y} φ ψ h := by
    have h' : limFunctor.map φ.hom = limFunctor.map ψ.hom := congrArg (fun f => f.hom) h
    exact ObjectProperty.hom_ext _
      ((IsLAdicSystem.bijective_limFunctor_map X.property Y.property).1 h')

instance full_limFunctorLAdic : (limFunctorLAdic.{v} (Λ := Λ) (l := l)).Full where
  map_surjective {X Y} θ := by
    obtain ⟨φ, hφ⟩ := (IsLAdicSystem.bijective_limFunctor_map X.property Y.property).2 θ.hom
    exact ⟨ObjectProperty.homMk φ, InducedCategory.hom_ext hφ⟩

instance essSurj_limFunctorLAdic : (limFunctorLAdic.{v} (Λ := Λ) (l := l)).EssSurj where
  mem_essImage M := by
    have : Module.Finite Λ M.obj := M.property
    let S := (ofModule l).obj M.obj
    have hS : IsLAdicSystem S := isLAdicSystem_ofModule M.obj
    let e : M.obj ≃ₗ[Λ] ModuleCat.sectionsSubmodule S.obj :=
      LinearEquiv.ofBijective _ (bijective_toLimOfModule l M.obj)
    exact ⟨⟨of S, hS⟩, ⟨(ModuleCat.isFG.{v} Λ).fullyFaithfulι.preimageIso
      e.toModuleIso.symm⟩⟩

instance : (limFunctorLAdic.{v} (Λ := Λ) (l := l)).IsEquivalence where

/-- **The limit equivalence.** For a Noetherian ring `Λ`, `l`-adically complete, with `Λ / l Λ`
Artinian (e.g. `Λ = ℤ_l`), the projective-limit functor `F ↦ lim F` is an equivalence of the full
subcategory of the A–R category on the A–R `l`-adic systems with the category of finitely
generated `Λ`-modules. -/
@[weil "thm_fk112_limit_equivalence_ar_l_adic_finite_modules"]
theorem isEquivalence_limFunctorArLAdic :
    (limFunctorArLAdic.{v} (Λ := Λ) (l := l)).IsEquivalence :=
  Functor.isEquivalence_of_comp_left
    (ObjectProperty.ιOfLE isLAdicSystem_le_isArLAdic) limFunctorArLAdic

/-- The equivalence of the A–R `l`-adic systems with the finitely generated `Λ`-modules given by
the projective-limit functor. -/
noncomputable def arLAdicEquivFGModuleCat :
    (isArLAdic : ObjectProperty (ArCategory.{v} Λ l)).FullSubcategory ≌ FGModuleCat.{v} Λ :=
  have := isEquivalence_limFunctorArLAdic.{v} (Λ := Λ) (l := l)
  limFunctorArLAdic.asEquivalence

lemma arLAdicEquivFGModuleCat_functor :
    (arLAdicEquivFGModuleCat.{v} (Λ := Λ) (l := l)).functor = limFunctorArLAdic := rfl

end Equivalence

end ArCategory

end ProjectiveSystem

end CategoryTheory
