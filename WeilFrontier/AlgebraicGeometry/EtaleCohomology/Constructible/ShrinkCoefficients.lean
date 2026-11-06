module

public import Weil.Attr
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.Ext.YonedaExtensionClasses
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.EpiEffacement
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShrinkCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
import all StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.YonedaClassMap

/-!
# Yoneda extensions of constructible sheaves

Let `X` be a Noetherian scheme, `n ≥ 1`, `𝒜` the category of sheaves of `ℤ/nℤ`-modules on the
small étale site of `X` and `𝒞 ⊆ 𝒜` the full subcategory of constructible sheaves. For
constructible `F`, `G` and `p ≥ 1`, regarding a `p`-extension `0 → G → D_1 → ⋯ → D_p → F → 0` in
`𝒞` as one in `𝒜` induces a bijection `YExt^p_𝒞(F, G) → YExt^p_𝒜(F, G)`.

The statement is an instance of a general comparison. Let `F : C ⥤ D` be an exact fully faithful
functor of abelian categories such that every epimorphism `Z ⟶ F X` of `D` is dominated by the
image of an epimorphism `X' ⟶ X` of `C`. Then `F` induces bijections
`Ext^n_C(X, Y) ≃ Ext^n_D(F X, F Y)`, by induction on `n`: a class of positive degree is killed by
an epimorphism onto its source (in `D`, lifted to `C` by the hypothesis), and the contravariant
long exact sequences of `Ext` in `C` and in `D` of the resulting short exact sequence compare the
class with one of lower degree. Since the class map of Yoneda extensions is a bijection
`YExt^{n+1} ≃ Ext^{n+1}` in any abelian category and commutes with exact functors, `F` also
induces bijections on Yoneda extension classes.

For constructible sheaves the hypothesis holds: an epimorphism `p : Z ⟶ K` onto a constructible
sheaf is dominated by an epimorphism from a constructible sheaf, because `Z` is a filtered
colimit of constructible sheaves and `K` is a noetherian object, so one of the composites
`Zᵢ ⟶ Z ⟶ K` is already an epimorphism.

## Main definitions

* `CategoryTheory.Abelian.YonedaExtension.map`, `CategoryTheory.Abelian.YonedaExt.map`: the image
  of a Yoneda extension, and the induced map on Yoneda extension classes, under an exact functor.
* `AlgebraicGeometry.ConstructibleModuleSheafCategory`: the constructible sheaves of `R`-modules
  on the small étale site, as a full subcategory.

## Main results

* `CategoryTheory.Abelian.extClassMap_map`: the class map commutes with exact functors.
* `CategoryTheory.Functor.mapExt_bijective_of_exists_epi_lift`: an exact fully faithful functor
  with the epimorphism lifting property induces bijections on `Ext`.
* `CategoryTheory.Abelian.YonedaExt.map_bijective_of_exists_epi_lift`: the same for Yoneda
  extension classes.
* `AlgebraicGeometry.exists_isConstructibleModuleSheaf_epi_comp`: an epimorphism onto a
  constructible sheaf is dominated by an epimorphism from a constructible sheaf.
* `AlgebraicGeometry.ConstructibleModuleSheafCategory.yonedaExt_map_ι_bijective`: Yoneda
  extensions of constructible sheaves of modules over a Noetherian ring may be computed with
  constructible sequences.
* `AlgebraicGeometry.ConstructibleModuleSheafCategory.yonedaExt_map_ι_bijective_zmod`: the case
  `R = ℤ/nℤ`.

## Implementation notes

The proof goes through `Ext` rather than through the explicit construction of constructible
subextensions of a `p`-extension: the effacement of positive-degree classes and the long exact
sequences of `Ext` replace the step-by-step choice of constructible subsheaves. The noetherian
property of constructible sheaves enters in the same way, through the existence of a
constructible sheaf mapping onto a given constructible quotient.

Constructibility of a sheaf of `ℤ/nℤ`-modules is that of Stacks 03RW (3): on the strata of a
finite partition into constructible locally closed subschemes the sheaf is locally constant of
finite type. The result is proved for a Noetherian coefficient ring `R` small in the coefficient
universe, and the separatedness of `X` assumed in the source is not needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 06XU](https://stacks.math.columbia.edu/tag/06XU)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 09YV](https://stacks.math.columbia.edu/tag/09YV)
-/

@[expose] public section

universe w w' v v' u u' r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor carries an exact sequence of composable arrows to an exact sequence. -/
theorem Exact.mapComposableArrows {n : ℕ} {T : ComposableArrows C n} (hT : T.Exact) :
    ((F.mapComposableArrows n).obj T).Exact := by
  refine ⟨⟨fun i hi => ?_⟩, fun i hi => ?_⟩
  · change F.map (T.map' i (i + 1)) ≫ F.map (T.map' (i + 1) (i + 2)) = 0
    rw [← Functor.map_comp, hT.toIsComplex.zero' i (i + 1) (i + 2), F.map_zero]
  · change ((T.sc hT.toIsComplex i).map F).Exact
    exact (hT.exact i hi).map F

/-- An exact functor carries an exact two-term sequence to an exact sequence. -/
theorem Exact.map_mk₂ {X Y Z : C} {a : X ⟶ Y} {b : Y ⟶ Z} (h : (mk₂ a b).Exact) :
    (mk₂ (F.map a) (F.map b)).Exact :=
  exact_of_iso (F.mapComposableArrowsObjMk₂Iso a b) (h.mapComposableArrows F)

end ComposableArrows

namespace IsNoetherianObject

/-- **An epimorphism from a filtered colimit onto a noetherian object is reached by one term.**
If `c` is a colimit cocone of a filtered diagram and `f : c.pt ⟶ K` is an epimorphism onto a
noetherian object, then `c.ι.app i ≫ f` is an epimorphism for some `i`: the images of these
composites form a directed family of subobjects of `K`, whose greatest member contains the image
of `f`. -/
theorem exists_epi_ι_comp_of_isColimit {C : Type u} [Category.{v} C] [Abelian C]
    {I : Type w} [Category.{w'} I] [IsFiltered I] {D : I ⥤ C}
    {c : Cocone D} (hc : IsColimit c) {K : C} [IsNoetherianObject K] (f : c.pt ⟶ K) [Epi f] :
    ∃ i, Epi (c.ι.app i ≫ f) := by
  let S : I → Subobject K := fun i ↦ imageSubobject (c.ι.app i ≫ f)
  have hS : ∀ {i j : I} (g : i ⟶ j), S i ≤ S j := fun {i j} g ↦ by
    have h := imageSubobject_comp_le (D.map g) (c.ι.app j ≫ f)
    rwa [c.w_assoc g] at h
  obtain ⟨_, ⟨i₀, rfl⟩, hmax⟩ := (wellFounded_gt (α := Subobject K)).has_min (Set.range S)
    ⟨_, ⟨(IsFiltered.nonempty (C := I)).some, rfl⟩⟩
  have hle : ∀ i, S i ≤ S i₀ := fun i ↦ by
    have h₀ : S i₀ ≤ S (IsFiltered.max i i₀) := hS (IsFiltered.rightToMax i i₀)
    have heq : S (IsFiltered.max i i₀) = S i₀ :=
      (eq_or_lt_of_le h₀).elim Eq.symm fun hlt ↦ (hmax _ ⟨_, rfl⟩ hlt).elim
    exact heq ▸ hS (IsFiltered.leftToMax i i₀)
  have hfac : ∀ i, (S i₀).Factors (c.ι.app i ≫ f) := fun i ↦
    Subobject.factors_of_le _ (hle i)
      ((Subobject.factors_iff _ _).mpr ⟨_, imageSubobject_arrow_comp (c.ι.app i ≫ f)⟩)
  let c' : Cocone D :=
    { pt := (S i₀ : C)
      ι :=
        { app := fun i ↦ (S i₀).factorThru (c.ι.app i ≫ f) (hfac i)
          naturality := fun i j g ↦ by
            rw [← cancel_mono (S i₀).arrow]
            simp [c.w_assoc g] } }
  have hs : hc.desc c' ≫ (S i₀).arrow = f :=
    hc.hom_ext fun j ↦ by
      rw [← Category.assoc, hc.fac]
      simp [c']
  have : Epi (S i₀).arrow := epi_of_epi_fac hs
  have : IsIso (S i₀).arrow := isIso_of_mono_of_epi _
  refine ⟨i₀, ?_⟩
  rw [← imageSubobject_arrow_comp (c.ι.app i₀ ≫ f)]
  infer_instance

end IsNoetherianObject

namespace Abelian

open ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

namespace YonedaExtension

variable {B A : C} {n : ℕ}

/-- The middle terms of a Yoneda extension, preceded by its first map, stay exact under an exact
functor. -/
theorem exact_precomp_map (E : YonedaExtension B A n) :
    (((F.mapComposableArrows n).obj E.Z).precomp (F.map E.f)).Exact := by
  obtain _ | m := n
  · exact exact₁ _
  · have h := (exact_iff_δ₀ _).1 E.exact
    exact exact_of_δ₀ (h.1.map_mk₂ F) (h.2.mapComposableArrows F)

/-- The last two maps of a Yoneda extension stay exact under an exact functor. -/
theorem exact_g_map (E : YonedaExtension B A n) :
    (mk₂ ((((F.mapComposableArrows n).obj E.Z).precomp (F.map E.f)).map' n (n + 1))
      (F.map E.g)).Exact := by
  obtain _ | m := n
  · exact E.exact_g.map_mk₂ F
  · exact E.exact_g.map_mk₂ F

/-- The image of a Yoneda extension under an exact functor. -/
noncomputable def map (E : YonedaExtension B A n) :
    YonedaExtension (F.obj B) (F.obj A) n where
  Z := (F.mapComposableArrows n).obj E.Z
  f := F.map E.f
  g := F.map E.g
  exact := E.exact_precomp_map F
  exact_g := E.exact_g_map F

@[simp] lemma map_f (E : YonedaExtension B A n) : (E.map F).f = F.map E.f := rfl

@[simp] lemma map_g (E : YonedaExtension B A n) : (E.map F).g = F.map E.g := rfl

lemma map_Z (E : YonedaExtension B A n) : (E.map F).Z = (F.mapComposableArrows n).obj E.Z := rfl

/-- An exact functor carries a dominance to a dominance. -/
lemma Dominates.map {E' E : YonedaExtension B A n} (h : E'.Dominates E) :
    (E'.map F).Dominates (E.map F) := by
  obtain ⟨φ, h₁, h₂⟩ := h
  refine ⟨(F.mapComposableArrows n).map φ, ?_, ?_⟩
  · change F.map E'.f ≫ F.map (app' φ 0) = F.map E.f
    rw [← F.map_comp, h₁]
  · change F.map (app' φ n) ≫ F.map E.g = F.map E'.g
    rw [← F.map_comp, h₂]

end YonedaExtension

namespace YonedaExt

variable {B A : C} {n : ℕ}

/-- The map `YExt^{n+1}(B, A) → YExt^{n+1}(F B, F A)` induced by an exact functor `F`. -/
noncomputable def map : YonedaExt B A n → YonedaExt (F.obj B) (F.obj A) n :=
  Quot.lift (fun E => mk (E.map F)) fun _ _ h => mk_eq_mk_of_dominates (h.map F)

@[simp] lemma map_mk (E : YonedaExtension B A n) : map F (mk E) = mk (E.map F) := rfl

end YonedaExt

/-- **The class map commutes with exact functors.** -/
theorem extClassMap_map [HasExt.{w} C] [HasExt.{w'} D] {B : C} :
    ∀ (n : ℕ) {A : C} (E : YonedaExtension B A n),
      extClassMap.{w'} n (E.map F) = (extClassMap.{w} n E).mapExactFunctor F := by
  intro n
  induction n with
  | zero =>
    intro A E
    rw [extClassMap_zero, extClassMap_zero, Ext.mapExactFunctor_extClass]
    rfl
  | succ n ih =>
    intro A E
    obtain ⟨C', E', p, h, hS, φ, w₁, w₂⟩ := exists_cut E
    have h' : F.map E.f ≫ F.map p = 0 := by rw [← F.map_comp, h, F.map_zero]
    have hS' : (ShortComplex.mk (F.map E.f) (F.map p) h').ShortExact := hS.map_of_exact F
    rw [extClassMap_succ_of_cut E E' p h hS φ w₁ w₂, Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_extClass, ← ih,
      extClassMap_succ_of_cut (E.map F) (E'.map F) (F.map p) h' hS'
        ((F.mapComposableArrows n).mapIso φ)
        (by
          change F.map (E.Z.map' 0 1) ≫ F.map (app' φ.hom 0) = F.map p ≫ F.map E'.f
          exact (F.map_comp _ _).symm.trans ((congrArg F.map w₁).trans (F.map_comp _ _)))
        (by
          change F.map (app' φ.hom n) ≫ F.map E'.g = F.map E.g
          exact (F.map_comp _ _).symm.trans (congrArg F.map w₂))]
    rfl

/-- **Comparison of `Ext` along an exact fully faithful functor with the epimorphism lifting
property.** Let `F : C ⥤ D` be an exact fully faithful functor of abelian categories such that
every epimorphism `Z ⟶ F X` in `D` is dominated by the image of an epimorphism `X' ⟶ X` of `C`.
Then `F` induces bijections `Ext^n_C(X, Y) → Ext^n_D(F X, F Y)` for all `n`. -/
theorem _root_.CategoryTheory.Functor.mapExt_bijective_of_exists_epi_lift [F.Full] [F.Faithful]
    [HasExt.{w} C] [HasExt.{w'} D]
    (hF : ∀ (X : C) (Z : D) (p : Z ⟶ F.obj X), Epi p →
      ∃ (X' : C) (q : X' ⟶ X) (_ : Epi q) (a : F.obj X' ⟶ Z), a ≫ p = F.map q)
    (X Y : C) (n : ℕ) : Function.Bijective (F.mapExtAddHom X Y n) := by
  induction n generalizing X with
  | zero => simpa [Ext.mapExactFunctor₀] using ⟨F.map_injective, F.map_surjective⟩
  | succ n hn =>
    constructor
    · rw [injective_iff_map_eq_zero]
      intro ξ hξ
      obtain ⟨Z, p, hp, hpξ⟩ := exists_epi_mk₀_comp_eq_zero.{w} n ξ
      let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p }
      obtain ⟨η, rfl⟩ := Ext.contravariant_sequence_exact₃ hS Y ξ hpξ (add_comm 1 n)
      have h₁ : (hS.map_of_exact F).extClass.comp (η.mapExactFunctor F) (add_comm 1 n) = 0 := by
        rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp,
          Ext.mapExactFunctor_extClass] at hξ
        exact hξ
      obtain ⟨θ, hθ⟩ := Ext.contravariant_sequence_exact₁ (hS.map_of_exact F) _ _
        (add_comm 1 n) h₁
      obtain ⟨θ', rfl⟩ := (hn Z).2 θ
      have hη : η = (Ext.mk₀ S.f).comp θ' (zero_add n) := by
        apply (hn S.X₁).1
        rw [Functor.mapExtAddHom_apply, Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp,
          Ext.mapExactFunctor_mk₀]
        exact hθ.symm
      rw [hη]
      exact hS.extClass_comp_assoc θ'
    · intro ζ
      obtain ⟨Z, p, hp, hpζ⟩ := exists_epi_mk₀_comp_eq_zero.{w'} n ζ
      obtain ⟨X', q, hq, a, ha⟩ := hF X Z p hp
      let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
      have h₀ : (Ext.mk₀ (S.map F).g).comp ζ (zero_add (n + 1)) = 0 := by
        change (Ext.mk₀ (F.map q)).comp ζ (zero_add (n + 1)) = 0
        rw [← ha, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hpζ, Ext.comp_zero]
      obtain ⟨η, hη⟩ := Ext.contravariant_sequence_exact₃ (hS.map_of_exact F) _ ζ h₀
        (add_comm 1 n)
      obtain ⟨η', rfl⟩ := (hn S.X₁).2 η
      refine ⟨hS.extClass.comp η' (add_comm 1 n), ?_⟩
      rw [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
      exact hη

/-- **Comparison of Yoneda extension classes along an exact fully faithful functor with the
epimorphism lifting property.** Under the hypotheses of
`CategoryTheory.Functor.mapExt_bijective_of_exists_epi_lift`, regarding a Yoneda extension in `C`
as one in `D` induces a bijection `YExt^{n+1}_C(B, A) → YExt^{n+1}_D(F B, F A)`. -/
theorem YonedaExt.map_bijective_of_exists_epi_lift [F.Full] [F.Faithful]
    (hF : ∀ (X : C) (Z : D) (p : Z ⟶ F.obj X), Epi p →
      ∃ (X' : C) (q : X' ⟶ X) (_ : Epi q) (a : F.obj X' ⟶ Z), a ≫ p = F.map q)
    (B A : C) (n : ℕ) :
    Function.Bijective (YonedaExt.map F : YonedaExt B A n → YonedaExt (F.obj B) (F.obj A) n) := by
  let := HasExt.standard C
  let := HasExt.standard D
  have hcomm : YonedaExt.extClass ∘ YonedaExt.map F =
      F.mapExtAddHom B A (n + 1) ∘ (YonedaExt.extClass : YonedaExt B A n → _) := by
    funext x
    obtain ⟨E, rfl⟩ := YonedaExt.mk_surjective x
    exact extClassMap_map F n E
  have h : Function.Bijective (YonedaExt.extClass ∘ YonedaExt.map F :
      YonedaExt B A n → Ext (F.obj B) (F.obj A) (n + 1)) := by
    rw [hcomm]
    exact (F.mapExt_bijective_of_exists_epi_lift hF B A (n + 1)).comp
      YonedaExt.extClass_bijective
  exact (Function.Bijective.of_comp_iff' YonedaExt.extClass_bijective _).1 h

end Abelian

end CategoryTheory

namespace AlgebraicGeometry

open CategoryTheory.Abelian

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type r) [CommRing R] [Small.{u + 1} R]
  [IsNoetherianRing R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} R)]

/-- **Constructible approximation of an epimorphism.** On a Noetherian scheme `X`, an
epimorphism `p : Z ⟶ K` of sheaves of `R`-modules onto a constructible sheaf is dominated by
an epimorphism from a constructible sheaf: there are a constructible `Z'` and `a : Z' ⟶ Z`
with `a ≫ p` an epimorphism. -/
theorem exists_isConstructibleModuleSheaf_epi_comp [IsNoetherian X.obj]
    [HasSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)]
    {Z K : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)} (p : Z ⟶ K)
    [Epi p] (hK : IsConstructibleModuleSheaf B X R K) :
    ∃ (Z' : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
      (_ : IsConstructibleModuleSheaf B X R Z') (a : Z' ⟶ Z), Epi (a ≫ p) := by
  have hN := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  have _ : CompactSpace X.1 := hN.2
  have _ : IsLocallyNoetherian X.1 := hN.1
  have _ : QuasiSeparatedSpace X.1 := IsLocallyNoetherian.quasiSeparatedSpace
  have _ : IsNoetherianObject K := isNoetherianObject_of_isConstructibleModuleSheaf' B R X K hK
  have _ := isRightAdjoint_sheafPushforwardContinuous_shrink B R
  have _ := hasWeakSheafify_over_shrink B R
  let E := SmallEtale.sheafShrinkEquivalence B R X
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleModuleSheaf_of_qcqs B X (Shrink.{u + 1} R)
      (E.functor.obj Z)
  have hc' := isColimitOfPreserves E.inverse hc
  obtain ⟨i, hi⟩ := IsNoetherianObject.exists_epi_ι_comp_of_isColimit hc'
    (E.unitIso.inv.app Z ≫ p)
  refine ⟨E.inverse.obj (D.obj i), ?_, (E.inverse.mapCocone (Cocone.mk _ ι)).ι.app i ≫
    E.unitIso.inv.app Z, by simpa only [Category.assoc] using hi⟩
  refine isConstructibleModuleSheaf_of_shrink B R X _ ?_
  exact isConstructibleModuleSheaf_of_epi B X (Shrink.{u + 1} R) (E.counitIso.inv.app (D.obj i))
    (hD i)

/-- The full subcategory of the sheaves of `R`-modules on the small étale site of `X` whose
objects are the constructible sheaves. -/
abbrev ConstructibleModuleSheafCategory :=
  ObjectProperty.FullSubcategory
    (fun F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R) =>
      IsConstructibleModuleSheaf B X R F)

namespace ConstructibleModuleSheafCategory

/-- The inclusion of the constructible sheaves into all sheaves of `R`-modules. -/
abbrev ι : ConstructibleModuleSheafCategory B X R ⥤
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R) :=
  ObjectProperty.ι _

variable [IsNoetherian X.obj]
  [HasSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)]

/-- On a Noetherian scheme the constructible sheaves of `R`-modules form a Serre class. -/
instance isSerreClass :
    ObjectProperty.IsSerreClass
      (fun F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R) =>
        IsConstructibleModuleSheaf B X R F) :=
  isSerreClass_isConstructibleModuleSheaf_of_small B R X

/-- On a Noetherian scheme the constructible sheaves of `R`-modules form an abelian category. -/
noncomputable instance abelian : Abelian (ConstructibleModuleSheafCategory B X R) :=
  inferInstance

/-- Kernels of constructible sheaves are computed among all sheaves. -/
instance preservesFiniteLimits_ι : PreservesFiniteLimits (ι B X R) :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- Cokernels of constructible sheaves are computed among all sheaves. -/
instance preservesFiniteColimits_ι : PreservesFiniteColimits (ι B X R) :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- **Yoneda extensions of constructible sheaves may be computed with constructible
sequences.** Let `X` be a Noetherian scheme, `R` a Noetherian ring, `𝒜` the category of sheaves
of `R`-modules on the small étale site of `X` and `𝒞 ⊆ 𝒜` the full subcategory of constructible
sheaves. For constructible `F`, `G` and `p = n + 1 ≥ 1`, regarding a `p`-extension
`0 → G → D_1 → ⋯ → D_p → F → 0` in `𝒞` as one in `𝒜` induces a bijection
`YExt^p_𝒞(F, G) → YExt^p_𝒜(F, G)`. -/
theorem yonedaExt_map_ι_bijective (F G : ConstructibleModuleSheafCategory B X R) (n : ℕ) :
    Function.Bijective (YonedaExt.map (ι B X R) : YonedaExt F G n → YonedaExt F.obj G.obj n) := by
  refine YonedaExt.map_bijective_of_exists_epi_lift (ι B X R) (fun K Z p hp => ?_) F G n
  obtain ⟨Z', hZ', a, ha⟩ := exists_isConstructibleModuleSheaf_epi_comp B X R p K.property
  refine ⟨⟨Z', hZ'⟩, ObjectProperty.homMk (a ≫ p), ?_, a, rfl⟩
  exact (ι B X R).epi_of_epi_map ha

end ConstructibleModuleSheafCategory

section ZMod

attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  SmallEtale.hasWeakSheafify_over_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (n : ℕ) [NeZero n]

/-- Sheafification of presheaves of `ℤ/nℤ`-modules on the small étale site. -/
local instance : HasSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} (ZMod n)) :=
  SmallEtale.hasSheafify_moduleCat.{u, 0, u + 1} B X (ZMod n)

/-- **[FK, I.4] Yoneda extensions of constructible sheaves may be computed with constructible
sequences.** Let `X` be a Noetherian scheme, `n ≥ 1`, `𝒜 = Mod_{ℤ/n}(X)` the category of
sheaves of `ℤ/nℤ`-modules on the small étale site of `X` and `𝒞 ⊆ 𝒜` the full subcategory of
constructible sheaves. For constructible `F`, `G` and `p = m + 1 ≥ 1`, the map
`YExt^p_𝒞(F, G) → YExt^p_𝒜(F, G)` induced by regarding a `p`-extension in `𝒞` as one in `𝒜` is
bijective. -/
@[weil "lem_fk104_yoneda_ext_constructible_sequences_suffice"]
theorem ConstructibleModuleSheafCategory.yonedaExt_map_ι_bijective_zmod [IsNoetherian X.obj]
    (F G : ConstructibleModuleSheafCategory B X (ZMod n)) (m : ℕ) :
    Function.Bijective (YonedaExt.map (ConstructibleModuleSheafCategory.ι B X (ZMod n)) :
      YonedaExt F G m → YonedaExt F.obj G.obj m) :=
  ConstructibleModuleSheafCategory.yonedaExt_map_ι_bijective B X (ZMod n) F G m

end ZMod

end AlgebraicGeometry

