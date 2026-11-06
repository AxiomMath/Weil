module

public import Weil.Attr
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Cohomology of sheaves of modules as abelian sheaf cohomology

Let `(C, J)` be a site and `K` a commutative ring which is flat over `ℤ` (for instance `ℚ` or
`ℂ`). For a sheaf `F` of `K`-modules, its cohomology may be computed either as
`Ext^n(K, F)` in the category of sheaves of `K`-modules, `K` the constant sheaf, or as the
cohomology `H^n(F) = Ext^n(ℤ, F)` of the underlying abelian sheaf. We show that the two agree,
naturally in `F` and compatibly with the action of `K`.

The argument is general. For an adjunction `L ⊣ R` between abelian categories in which `R` is
exact and `L` preserves monomorphisms, `R` preserves injective objects, and applying `R` and
precomposing with the unit gives an isomorphism `Ext^n(L X, Y) ≃ Ext^n(X, R Y)` (by induction on
`n`, dimension shifting along an injective presentation of `Y`). We apply it to the forgetful
functor `R` from sheaves of `K`-modules to abelian sheaves, whose left adjoint is the sheafified
extension of scalars `L = K ⊗_ℤ -`: `R` is exact (it is both a left and a right adjoint), `L`
preserves monomorphisms because `K` is flat over `ℤ`, and `L` sends the constant sheaf `ℤ` to the
constant sheaf `K`.

## Main definitions

* `CategoryTheory.Adjunction.extAddEquiv`: `Ext^n(L X, Y) ≃+ Ext^n(X, R Y)` for an adjunction
  `L ⊣ R` with `R` exact and `L` preserving monomorphisms.
* `CategoryTheory.sheafForget₂`: the abelian sheaf underlying a sheaf of `K`-modules.
* `CategoryTheory.extConstantSheafAddEquivH`: `Ext^n(K, F) ≃+ H^n(F)`.
* `CategoryTheory.sheafForget₂HModule`: the `K`-module structure on `H^n(F)` in which `c` acts
  by `H^n(c • 𝟙 F)`.
* `CategoryTheory.extConstantSheafLinearEquivH`: `Ext^n(K, F) ≃ₗ[K] H^n(F)`.

## Main results

* `CategoryTheory.Adjunction.extHom_bijective`: the comparison map
  `Ext^n(L X, Y) → Ext^n(X, R Y)` is bijective.
* `CategoryTheory.extConstantSheafAddEquivH_comp_mk₀`: naturality in `F`.
* `CategoryTheory.extConstantSheafAddEquivH_smul`: compatibility with the action of `K`.
* `CategoryTheory.finrank_ext_constantSheaf_eq`: `dim_K Ext^n(K, F) = dim_K H^n(F)`.

## Implementation notes

On a topological space the comparison holds for every ring `K`, since injective sheaves of
`K`-modules are flasque (R. Hartshorne, *Algebraic Geometry*, III, Proposition 2.6); the argument
here, through the exact left adjoint `K ⊗_ℤ -`, needs `K` flat over `ℤ` but works on every site.

The existence of `Ext` groups (`HasExt`) in both categories, and enough injectives in the
category of sheaves of `K`-modules, are taken as instance arguments, so that any choice of them
(e.g. `CategoryTheory.IsGrothendieckAbelian.hasExt`) specializes the results. For `X` a
topological space and `C` its category of opens, all instance arguments are found by instance
search except `HasExt`.

## References

* [Hartshorne] R. Hartshorne, *Algebraic Geometry*, Chapter III, Proposition 2.6.
-/

@[expose] public section

universe w w' w'' v v' u u'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
variable [HasExt.{w} C] [HasExt.{w'} D]

/-- `Ext^n(X', Y) ≃+ Ext^n(X, Y)` for an isomorphism `X ≅ X'`, by precomposition. -/
noncomputable def Abelian.Ext.addEquivOfIsoLeft {X X' : C} (i : X ≅ X') (Y : C) (n : ℕ) :
    Ext.{w} X' Y n ≃+ Ext.{w} X Y n where
  toFun e := (Ext.mk₀ i.hom).comp e (zero_add n)
  invFun e := (Ext.mk₀ i.inv).comp e (zero_add n)
  left_inv e := by simp [Ext.mk₀_comp_mk₀_assoc]
  right_inv e := by simp [Ext.mk₀_comp_mk₀_assoc]
  map_add' e e' := by simp

lemma Abelian.Ext.addEquivOfIsoLeft_apply {X X' : C} (i : X ≅ X') {Y : C} {n : ℕ}
    (e : Ext.{w} X' Y n) :
    Ext.addEquivOfIsoLeft i Y n e = (Ext.mk₀ i.hom).comp e (zero_add n) :=
  rfl

namespace Adjunction

/-- The comparison map `Ext^n(L X, Y) → Ext^n(X, R Y)`: apply the exact functor `R`, then
precompose with the unit `X ⟶ R (L X)`. -/
noncomputable def extHom (X : C) (Y : D) (n : ℕ) :
    Ext.{w'} (L.obj X) Y n →+ Ext.{w} X (R.obj Y) n :=
  ((Ext.mk₀ (adj.unit.app X)).precomp _ (zero_add n)).comp (R.mapExtAddHom (L.obj X) Y n)

lemma extHom_apply (X : C) (Y : D) {n : ℕ} (e : Ext.{w'} (L.obj X) Y n) :
    adj.extHom X Y n e = (Ext.mk₀ (adj.unit.app X)).comp (e.mapExactFunctor R) (zero_add n) :=
  rfl

lemma extHom_comp {X : C} {Y Y' : D} {a b c : ℕ} (e : Ext.{w'} (L.obj X) Y a)
    (β : Ext.{w'} Y Y' b) (h : a + b = c) :
    adj.extHom X Y' c (e.comp β h) = (adj.extHom X Y a e).comp (β.mapExactFunctor R) h := by
  simp only [extHom_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add a) h (by lia)).symm

lemma extHom_mk₀ {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    adj.extHom X Y 0 (Ext.mk₀ f) = Ext.mk₀ (adj.homEquiv X Y f) := by
  simp [extHom_apply, Ext.mapExactFunctor_mk₀, Adjunction.homEquiv_unit]

lemma extHom_comp_mk₀ {X : C} {Y Y' : D} {n : ℕ} (e : Ext.{w'} (L.obj X) Y n) (g : Y ⟶ Y') :
    adj.extHom X Y' n (e.comp (Ext.mk₀ g) (add_zero n)) =
      (adj.extHom X Y n e).comp (Ext.mk₀ (R.map g)) (add_zero n) := by
  rw [extHom_comp, Ext.mapExactFunctor_mk₀]

lemma extHom_comp_extClass {X : C} {S : ShortComplex D} (hS : S.ShortExact) {n m : ℕ}
    (e : Ext.{w'} (L.obj X) S.X₃ n) (h : n + 1 = m) :
    adj.extHom X S.X₁ m (e.comp hS.extClass h) =
      (adj.extHom X S.X₃ n e).comp (hS.map_of_exact R).extClass h := by
  rw [extHom_comp, Ext.mapExactFunctor_extClass]

lemma extHom_bijective_zero (X : C) (Y : D) : Function.Bijective (adj.extHom X Y 0) := by
  have h : (adj.extHom X Y 0 : Ext (L.obj X) Y 0 → Ext X (R.obj Y) 0) =
      (Ext.mk₀ ∘ adj.homEquiv X Y) ∘ Ext.homEquiv₀ := by
    ext e
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 e
    simp only [Function.comp_apply, extHom_mk₀]
    congr 2
    exact (Ext.homEquiv₀.apply_symm_apply f).symm
  rw [h]
  exact ((Ext.mk₀_bijective _ _).comp (adj.homEquiv X Y).bijective).comp Ext.homEquiv₀.bijective

attribute [local instance] Ext.subsingleton_of_injective in
/-- For an adjunction `L ⊣ R` between abelian categories with `R` exact and `L` preserving
monomorphisms, the comparison map `Ext^n(L X, Y) → Ext^n(X, R Y)` is bijective. -/
theorem extHom_bijective [L.PreservesMonomorphisms] [EnoughInjectives D] (X : C) (Y : D)
    (n : ℕ) : Function.Bijective (adj.extHom X Y n) := by
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  induction n generalizing Y with
  | zero => exact adj.extHom_bijective_zero X Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map R).X₂ := Functor.PreservesInjectiveObjects.injective_obj I.injective
    have : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (adj.extHom X S.X₂ n) (adj.extHom X S.X₃ n) (adj.extHom X S.X₁ (n + 1))
      (by ext e; exact (adj.extHom_comp_mk₀ e S.g).symm)
      (by ext e; exact (adj.extHom_comp_extClass hS e rfl).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (L.obj X) hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X (hS.map_of_exact R) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact R) y₁ (by subsingleton) rfl)

/-- The additive equivalence `Ext^n(L X, Y) ≃+ Ext^n(X, R Y)` for an adjunction `L ⊣ R` between
abelian categories with `R` exact and `L` preserving monomorphisms. -/
noncomputable def extAddEquiv [L.PreservesMonomorphisms] [EnoughInjectives D] (X : C) (Y : D)
    (n : ℕ) : Ext.{w'} (L.obj X) Y n ≃+ Ext.{w} X (R.obj Y) n :=
  AddEquiv.ofBijective (adj.extHom X Y n) (adj.extHom_bijective X Y n)

@[simp]
lemma extAddEquiv_apply [L.PreservesMonomorphisms] [EnoughInjectives D] (X : C) (Y : D)
    {n : ℕ} (e : Ext.{w'} (L.obj X) Y n) : adj.extAddEquiv X Y n e = adj.extHom X Y n e :=
  rfl

end Adjunction

end CategoryTheory

namespace ModuleCat

open CategoryTheory Limits

variable (K : Type w) [CommRing K]

/-- The equivalence between `ℤ`-modules and abelian groups. -/
noncomputable abbrev zModuleEquivalence : ModuleCat.{w} ℤ ≌ AddCommGrpCat.{w} :=
  (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence

/-- Restricting scalars along `ℤ → K` and then forgetting the `ℤ`-module structure is forgetting
the `K`-module structure. -/
noncomputable def restrictScalarsIntCompForget₂Iso :
    restrictScalars.{w} (Int.castRingHom K) ⋙ forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w} ≅
      forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The functor `A ↦ K ⊗_ℤ A` from abelian groups to `K`-modules. -/
noncomputable def extendScalarsInt : AddCommGrpCat.{w} ⥤ ModuleCat.{w} K :=
  (zModuleEquivalence).inverse ⋙ extendScalars.{0, w, w} (Int.castRingHom K)

/-- `A ↦ K ⊗_ℤ A` is left adjoint to the forgetful functor from `K`-modules to abelian groups. -/
noncomputable def extendScalarsIntAdj :
    extendScalarsInt K ⊣ forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w} :=
  (zModuleEquivalence.symm.toAdjunction.comp
    (extendRestrictScalarsAdj.{w, 0, w} (Int.castRingHom K))).ofNatIsoRight
      (restrictScalarsIntCompForget₂Iso K)

/-- The forgetful functor from `K`-modules to abelian groups is left adjoint to
`A ↦ Hom_ℤ(K, A)`. -/
noncomputable def forget₂IntAdj : forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w} ⊣
    zModuleEquivalence.inverse ⋙ coextendScalars.{0, w, w} (Int.castRingHom K) :=
  ((restrictCoextendScalarsAdj.{w, 0, w} (Int.castRingHom K)).comp
    zModuleEquivalence.toAdjunction).ofNatIsoLeft (restrictScalarsIntCompForget₂Iso K)

instance : (forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w}).IsLeftAdjoint :=
  (forget₂IntAdj K).isLeftAdjoint

instance : (forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w}).IsRightAdjoint :=
  (extendScalarsIntAdj K).isRightAdjoint

instance preservesLimitsOfSize_forget₂ :
    PreservesLimitsOfSize.{v', u'} (forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w}) :=
  (extendScalarsIntAdj K).rightAdjoint_preservesLimits

instance preservesLimitsOfSize_coextendScalarsInt :
    PreservesLimitsOfSize.{v', u'}
      (zModuleEquivalence.inverse ⋙ coextendScalars.{0, w, w} (Int.castRingHom K)) :=
  (forget₂IntAdj K).rightAdjoint_preservesLimits

/-- Extension of scalars along `ℤ → K` preserves monomorphisms when `K` is flat over `ℤ`. -/
instance preservesMonomorphisms_extendScalars_int [Module.Flat ℤ K] :
    (extendScalars.{0, w, w} (Int.castRingHom K)).PreservesMonomorphisms where
  preserves {M N} g hg := by
    rw [ModuleCat.mono_iff_injective] at hg ⊢
    have hK : @Module.Flat ℤ K _ _ (Module.compHom K (Int.castRingHom K)) := by
      rw [show Module.compHom K (Int.castRingHom K) = (inferInstance : Module ℤ K) from
        Subsingleton.elim _ _]
      infer_instance
    exact @Module.Flat.lTensor_preserves_injective_linearMap ℤ
      ((restrictScalars.{w} (Int.castRingHom K)).obj (of K K)) M N _ _
      (Module.compHom K (Int.castRingHom K)) _ _ _ _ hK g.hom hg

instance [Module.Flat ℤ K] : (extendScalarsInt K).PreservesMonomorphisms := by
  unfold extendScalarsInt; infer_instance


/-- The additive map `ULift ℤ → K`, `n ↦ n • 1`. -/
def uliftIntToRing : ULift.{w} ℤ →+ K where
  toFun x := (x.down : K)
  map_zero' := by simp
  map_add' x y := by simp

@[simp]
lemma uliftIntToRing_apply (x : ULift.{w} ℤ) : uliftIntToRing K x = (x.down : K) := rfl

lemma ulift_eq_zsmul_one (x : ULift.{w} ℤ) : x = x.down • (⟨1⟩ : ULift.{w} ℤ) := by
  ext; simp

variable {K} in
/-- A left adjoint of the forgetful functor from `K`-modules to abelian groups sends `ℤ` to `K`. -/
noncomputable def leftAdjointObjULiftIntIso {G : AddCommGrpCat.{w} ⥤ ModuleCat.{w} K}
    (adj : G ⊣ forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w}) :
    G.obj (AddCommGrpCat.of (ULift.{w} ℤ)) ≅ ModuleCat.of K K where
  hom := (adj.homEquiv _ _).symm (AddCommGrpCat.ofHom (uliftIntToRing K))
  inv := ModuleCat.ofHom (LinearMap.toSpanSingleton K _ (adj.unit.app _ ⟨1⟩))
  hom_inv_id := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Adjunction.homEquiv_id]
    ext x
    rw [ulift_eq_zsmul_one x]
    simp only [map_zsmul]
    congr 1
    simp
  inv_hom_id := by
    ext
    simp only [hom_comp, LinearMap.coe_comp, Function.comp_apply, hom_ofHom,
      LinearMap.toSpanSingleton_apply, one_smul, hom_id, LinearMap.id_coe, id_eq]
    have h := adj.homEquiv_unit (AddCommGrpCat.of (ULift.{w} ℤ)) (ModuleCat.of K K)
      ((adj.homEquiv _ _).symm (AddCommGrpCat.ofHom (uliftIntToRing K)))
    rw [Equiv.apply_symm_apply] at h
    have := congrArg (fun f => AddCommGrpCat.Hom.hom f (⟨1⟩ : ULift.{w} ℤ)) h
    simp at this
    exact this.symm

end ModuleCat

namespace CategoryTheory

open Limits Abelian ModuleCat

section Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (K : Type w) [CommRing K]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify J (ModuleCat.{w} K)]

/-- The abelian sheaf underlying a sheaf of `K`-modules. -/
noncomputable abbrev sheafForget₂ : Sheaf J (ModuleCat.{w} K) ⥤ Sheaf J AddCommGrpCat.{w} :=
  sheafCompose J (forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w})

/-- The sheafified extension of scalars `A ↦ K ⊗_ℤ A` from abelian sheaves to sheaves of
`K`-modules. -/
noncomputable abbrev sheafExtendScalarsInt :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf J (ModuleCat.{w} K) :=
  Sheaf.composeAndSheafify J (extendScalarsInt K)

/-- The sheafified extension of scalars is left adjoint to the forgetful functor. -/
noncomputable def sheafExtendScalarsIntAdj : sheafExtendScalarsInt J K ⊣ sheafForget₂ J K :=
  Sheaf.adjunction J (extendScalarsIntAdj K)

instance : (sheafForget₂ J K).Additive where
  map_add {F G f g} := by
    ext U : 3
    exact (forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w}).map_add

/-- Forgetting the `K`-module structure of a sheaf commutes with sheafification, so it agrees
with the sheafified forgetful functor. -/
noncomputable def composeAndSheafifyForget₂Iso :
    Sheaf.composeAndSheafify J (forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w}) ≅ sheafForget₂ J K :=
  Functor.isoWhiskerLeft (sheafToPresheaf J _)
      (sheafComposeNatIso J (forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w})
        (sheafificationAdjunction J _) (sheafificationAdjunction J _)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (ModuleCat.{w} K)).counit) _ ≪≫
    Functor.leftUnitor _

instance : (sheafForget₂ J K).IsLeftAdjoint :=
  have : J.HasSheafCompose
      (zModuleEquivalence.inverse ⋙ coextendScalars.{0, w, w} (Int.castRingHom K)) :=
    hasSheafCompose_of_preservesLimitsOfSize J
  have : (Sheaf.composeAndSheafify J (forget₂ (ModuleCat.{w} K) AddCommGrpCat.{w})).IsLeftAdjoint :=
    (Sheaf.adjunction J (forget₂IntAdj K)).isLeftAdjoint
  Functor.isLeftAdjoint_of_iso (composeAndSheafifyForget₂Iso J K)

instance [Module.Flat ℤ K] :
    ((Functor.whiskeringRight Cᵒᵖ _ _).obj (extendScalarsInt K)).PreservesMonomorphisms where
  preserves {P Q} f _ := by
    rw [NatTrans.mono_iff_mono_app] at *
    intro U
    exact (extendScalarsInt K).map_mono (f.app U)

instance [Module.Flat ℤ K] : (sheafExtendScalarsInt J K).PreservesMonomorphisms := by
  unfold sheafExtendScalarsInt Sheaf.composeAndSheafify
  infer_instance

/-- The sheafified extension of scalars sends the constant sheaf `ℤ` to the constant sheaf `K`. -/
noncomputable def sheafExtendScalarsIntConstantIso :
    (sheafExtendScalarsInt J K).obj
        ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) ≅
      (constantSheaf J (ModuleCat.{w} K)).obj (ModuleCat.of K K) :=
  have : J.PreservesSheafification (extendScalarsInt K) :=
    Sheaf.preservesSheafification_of_adjunction J (extendScalarsIntAdj K)
  (presheafToSheafCompComposeAndSheafifyIso J (extendScalarsInt K)).app _ ≪≫
    (presheafToSheaf J _).mapIso (Functor.constComp Cᵒᵖ _ (extendScalarsInt K)) ≪≫
    (constantSheaf J (ModuleCat.{w} K)).mapIso (leftAdjointObjULiftIntIso (extendScalarsIntAdj K))

section Ext

variable [Module.Flat ℤ K] [EnoughInjectives (Sheaf J (ModuleCat.{w} K))]
  [HasExt.{w'} (Sheaf J (ModuleCat.{w} K))] [HasExt.{w''} (Sheaf J AddCommGrpCat.{w})]

/-- For a ring `K` flat over `ℤ` and a sheaf `F` of `K`-modules, `Ext^n(K, F)` among sheaves of
`K`-modules is the cohomology `H^n` of the underlying abelian sheaf of `F`. -/
noncomputable def extConstantSheafAddEquivH (F : Sheaf J (ModuleCat.{w} K)) (n : ℕ) :
    Ext.{w'} ((constantSheaf J (ModuleCat.{w} K)).obj (ModuleCat.of K K)) F n ≃+
      Sheaf.H.{w''} ((sheafForget₂ J K).obj F) n :=
  (Ext.addEquivOfIsoLeft (sheafExtendScalarsIntConstantIso J K) F n).trans
    ((sheafExtendScalarsIntAdj J K).extAddEquiv _ F n)

/-- The identification `Ext^n(K, F) ≃+ H^n(F)` is natural in `F`. -/
lemma extConstantSheafAddEquivH_comp_mk₀ {F F' : Sheaf J (ModuleCat.{w} K)} (g : F ⟶ F') {n : ℕ}
    (e : Ext.{w'} ((constantSheaf J (ModuleCat.{w} K)).obj (ModuleCat.of K K)) F n) :
    extConstantSheafAddEquivH J K F' n (e.comp (Ext.mk₀ g) (add_zero n)) =
      Sheaf.H.map ((sheafForget₂ J K).map g) n (extConstantSheafAddEquivH J K F n e) := by
  simp only [extConstantSheafAddEquivH, AddEquiv.trans_apply, Ext.addEquivOfIsoLeft_apply,
    Adjunction.extAddEquiv_apply, Sheaf.H.map_apply]
  rw [← Adjunction.extHom_comp_mk₀]
  congr 1
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

/-- The identification `Ext^n(K, F) ≃+ H^n(F)` sends the `K`-module structure of `Ext` to the
action of `K` on `H^n(F)` by functoriality: `c` acts through `H^n(c • 𝟙 F)`. -/
lemma extConstantSheafAddEquivH_smul {F : Sheaf J (ModuleCat.{w} K)} {n : ℕ} (c : K)
    (e : Ext.{w'} ((constantSheaf J (ModuleCat.{w} K)).obj (ModuleCat.of K K)) F n) :
    extConstantSheafAddEquivH J K F n (c • e) =
      Sheaf.H.map ((sheafForget₂ J K).map (c • 𝟙 F)) n (extConstantSheafAddEquivH J K F n e) := by
  rw [Ext.smul_eq_comp_mk₀, extConstantSheafAddEquivH_comp_mk₀]

/-- The action of `K` on the cohomology `H^n` of the abelian sheaf underlying a sheaf `F` of
`K`-modules: `c` acts by `H^n(c • 𝟙 F)`. -/
noncomputable abbrev sheafForget₂HSMul (F : Sheaf J (ModuleCat.{w} K)) (n : ℕ) :
    SMul K (Sheaf.H.{w''} ((sheafForget₂ J K).obj F) n) where
  smul c x := Sheaf.H.map ((sheafForget₂ J K).map (c • 𝟙 F)) n x

/-- The `K`-module structure on the cohomology `H^n` of the abelian sheaf underlying a sheaf `F`
of `K`-modules, `c` acting by `H^n(c • 𝟙 F)`. It is not an instance: `H^n` is an `Ext` group
of abelian sheaves, which carries its own instances. -/
noncomputable abbrev sheafForget₂HModule (F : Sheaf J (ModuleCat.{w} K)) (n : ℕ) :
    Module K (Sheaf.H.{w''} ((sheafForget₂ J K).obj F) n) :=
  letI := sheafForget₂HSMul J K F n
  Function.Injective.module K
    (extConstantSheafAddEquivH J K F n).symm.toAddMonoidHom
    (extConstantSheafAddEquivH J K F n).symm.injective
    (fun c x => by
      apply (extConstantSheafAddEquivH J K F n).injective
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
        extConstantSheafAddEquivH_smul, AddEquiv.apply_symm_apply]
      rfl)

/-- `Ext^n(K, F) ≃ₗ[K] H^n(F)`, for `H^n(F)` with the `K`-module structure
`sheafForget₂HModule`. -/
noncomputable def extConstantSheafLinearEquivH (F : Sheaf J (ModuleCat.{w} K)) (n : ℕ) :
    letI := sheafForget₂HModule J K F n
    Ext.{w'} ((constantSheaf J (ModuleCat.{w} K)).obj (ModuleCat.of K K)) F n ≃ₗ[K]
      Sheaf.H.{w''} ((sheafForget₂ J K).obj F) n :=
  letI := sheafForget₂HModule J K F n
  { extConstantSheafAddEquivH J K F n with
    map_smul' c e := extConstantSheafAddEquivH_smul J K c e }

/-- The rank of `Ext^n(K, F)` is that of `H^n(F)` with the `K`-action by functoriality. -/
lemma finrank_ext_constantSheaf_eq (F : Sheaf J (ModuleCat.{w} K)) (n : ℕ) :
    Module.finrank K
        (Ext.{w'} ((constantSheaf J (ModuleCat.{w} K)).obj (ModuleCat.of K K)) F n) =
      @Module.finrank K (Sheaf.H.{w''} ((sheafForget₂ J K).obj F) n) _ _
        (sheafForget₂HModule J K F n) :=
  letI := sheafForget₂HModule J K F n
  (extConstantSheafLinearEquivH J K F n).finrank_eq

end Ext

end Sheaf

end CategoryTheory
