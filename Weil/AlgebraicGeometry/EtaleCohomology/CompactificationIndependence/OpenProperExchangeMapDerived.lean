module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.OpenProperExchangeMapDerived
public import Weil.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HomSheafAcyclicEverywhere
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedAdjunction
public import Weil.Attr

/-!
# The derived exchange morphism `j_! Rf_* ⟶ Rf'_* i_!` is well defined

Consider a commutative square of schemes
```
  X --i--> X'
  |        |
  f        f'
  v        v
  Y --j--> Y'
```
with `i` and `j` open immersions, and the exchange morphisms `α_G : j_! f_* G ⟶ f'_* i_! G`,
natural in the sheaf `G` of `Λ`-modules on the small étale site of `X`. Let `F` be a bounded
below complex of sheaves of `Λ`-modules on `X` and `u : i_! F ⟶ J` an injective resolution. Then:

* `F ≅ (i_! F)|_X ⟶ J|_X` is an injective resolution, since restriction to `X` is exact,
  preserves injective objects, and `(i_! F)|_X ≅ F`;
* the exchange chain map `θ_J = (f'_*(ε^n) ∘ α^n)_n : j_! f_* (J|_X) ⟶ f'_* J` is a chain map;
* the morphism `(*) : j_! Rf_* F ⟶ Rf'_* (i_! F)` of bounded below derived categories that
  `θ_J` represents does not depend on the choice of `J` and is natural in `F`.

The argument is categorical. Given an adjunction `e ⊣ r` with invertible unit and exact `r`
preserving injectives, additive functors `f₀`, `F'`, an exact functor `g` and a natural
transformation `θ : r ⋙ f₀ ⋙ g ⟶ F'`, the morphism `g(Rf₀(K)) ⟶ RF'(e(K))` represented by
`θ_J` is defined for every injective resolution `e(K) ⟶ J`
(`CategoryTheory.Adjunction.exchangeDerivedMap`). A morphism `φ : K ⟶ K'` lifts, uniquely up to
homotopy, to a chain map `h : J ⟶ J'` of the resolutions; the naturality of `θ` and of the
units of the derived functors then gives naturality in `K`, and the case `φ = 𝟙` gives
independence of `J`.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusObjIsoOfInjective`: `RG(K) ≅ G(J)` for an
  injective resolution `K ⟶ J`.
* `CategoryTheory.Adjunction.restrictResolution`: the resolution `K ⟶ r(e(K)) ⟶ r(J)`.
* `CategoryTheory.Adjunction.exchangeDerivedMap`: the morphism `g(Rf₀(K)) ⟶ RF'(e(K))`
  represented by `θ_J`.
* `AlgebraicGeometry.openProperExchangeDerivedMap`: the morphism `(*)`.

## Main results

* `AlgebraicGeometry.quasiIso_restrictResolution_and_injective`: `F ⟶ J|_X` is an injective
  resolution.
* `AlgebraicGeometry.exchangeChainMap_comm`: `θ_J` commutes with the differentials.
* `AlgebraicGeometry.openProperExchangeDerivedMap_eq`: `(*)` is represented by `θ_J`.
* `AlgebraicGeometry.openProperExchangeDerivedMap_eq_of_resolution`: `(*)` does not depend on
  the injective resolution.
* `AlgebraicGeometry.openProperExchangeDerivedMap_naturality`: `(*)` is natural in `F`.

## Implementation notes

The derived functors are Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlus`, in the
forms `Stacks.EtaleCohomology.etaleModuleDerivedDirectImage` and
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZero`, on Mathlib's small étale sites, in
the standard model `HasDerivedCategory.standard` of the derived category. The bounded below
complexes are objects of `CochainComplex.Plus`, an object of `D⁺` being presented by the
localization `DerivedCategory.Plus.Qh` of the bounded below homotopy category.

The results are stated for an arbitrary natural transformation `α : j_! f_* ⟶ f'_* i_!`, for `i`
an étale monomorphism (an open immersion is one), `j` étale and `f`, `f'` arbitrary; neither the
properness of `f` nor the exchange property of `α` is used. The source's case is the one where
`α` consists of the exchange morphisms.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.5, p. 88.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- A quasi-isomorphism of bounded below complexes becomes invertible in `D⁺`. -/
lemma isIso_plusQh_map_quotient_map {K L : CochainComplex.Plus C} (u : K ⟶ L) [QuasiIso u.hom] :
    IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map u)) :=
  Localization.inverts _ (HomotopyCategory.Plus.quasiIso C) _ (by
    rw [HomotopyCategory.Plus.quasiIso_iff]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff u.hom).2
      ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))

variable [EnoughInjectives C] (G : C ⥤ D) [G.Additive]

/-- For an injective resolution `u : K ⟶ J` of a bounded below complex (a quasi-isomorphism into
a bounded below complex of injective objects), the isomorphism `RG(K) ≅ G(J)` in `D⁺`: the
image of `u` under `RG`, followed by the inverse of the unit of `RG` at `J`. -/
def rightDerivedFunctorPlusObjIsoOfInjective {K J : CochainComplex.Plus C} (u : K ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    G.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj K)) ≅
      DerivedCategory.Plus.Qh.obj
        (G.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient C).obj J)) :=
  have := isIso_plusQh_map_quotient_map u
  G.rightDerivedFunctorPlus.mapIso
      (asIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map u))) ≪≫
    (asIso (G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj J))).symm

/-- The isomorphisms `RG(K) ≅ G(J)` are natural: if `h : J ⟶ J'` is compatible up to homotopy
with `φ : K ⟶ K'` and the resolutions, then `RG(φ)` corresponds to `G(h)`. -/
lemma rightDerivedFunctorPlus_map_comp_objIsoOfInjective_hom {K K' J J' : CochainComplex.Plus C}
    (u : K ⟶ J) (u' : K' ⟶ J') [QuasiIso u.hom] [QuasiIso u'.hom] [∀ n, Injective (J.obj.X n)]
    [∀ n, Injective (J'.obj.X n)] (φ : K ⟶ K') (h : J ⟶ J')
    (hh : (HomotopyCategory.Plus.quotient C).map (u ≫ h) =
      (HomotopyCategory.Plus.quotient C).map (φ ≫ u')) :
    G.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map φ)) ≫
        (G.rightDerivedFunctorPlusObjIsoOfInjective u').hom =
      (G.rightDerivedFunctorPlusObjIsoOfInjective u).hom ≫
        DerivedCategory.Plus.Qh.map
          (G.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient C).map h)) := by
  have hn := G.rightDerivedFunctorPlusUnit.naturality ((HomotopyCategory.Plus.quotient C).map h)
  simp only [rightDerivedFunctorPlusObjIsoOfInjective, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, Iso.symm_hom, asIso_inv]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, ← Functor.map_comp, ← hh, Functor.map_comp,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact hn.symm

end CategoryTheory.Functor

namespace CochainComplex.Plus

variable {C : Type*} [Category* C] [Abelian C]

/-- A morphism `φ : K ⟶ K'` lifts, up to homotopy, along a quasi-isomorphism `u : K ⟶ J` to any
bounded below complex of injectives `J'` receiving a morphism `u' : K' ⟶ J'`. -/
lemma exists_quotient_map_comp_eq {K K' J J' : CochainComplex.Plus C} (u : K ⟶ J) (u' : K' ⟶ J')
    [QuasiIso u.hom] [∀ n, Injective (J'.obj.X n)] (φ : K ⟶ K') :
    ∃ h : J ⟶ J', (HomotopyCategory.Plus.quotient C).map (u ≫ h) =
      (HomotopyCategory.Plus.quotient C).map (φ ≫ u') := by
  obtain ⟨d, hd⟩ := J'.property
  obtain ⟨g, hg⟩ := (CochainComplex.bijective_precomp_quotient_map_of_quasiIso_of_injective u.hom
    J'.obj d).2 ((HomotopyCategory.quotient C _).map (φ ≫ u').hom)
  obtain ⟨h, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective g
  refine ⟨ObjectProperty.homMk h, ?_⟩
  ext1
  simp only [← Functor.map_comp] at hg
  exact hg

end CochainComplex.Plus

namespace CategoryTheory.Adjunction

variable {C C₀ D₀ D : Type*} [Category* C] [Category* C₀] [Category* D₀] [Category* D]
  [Abelian C] [Abelian C₀] [Abelian D₀] [Abelian D]
  {e : C₀ ⥤ C} {r : C ⥤ C₀} [e.Additive] [r.Additive] (adj : e ⊣ r)

/-- The unit `K ⟶ r(e(K))` of `e ⊣ r`, applied termwise to a complex. -/
def unitCochainComplexPlus (K : CochainComplex.Plus C₀) :
    K ⟶ r.mapCochainComplexPlus.obj (e.mapCochainComplexPlus.obj K) :=
  ObjectProperty.homMk
    { f := fun n => adj.unit.app (K.obj.X n)
      comm' := fun i j _ => (adj.unit.naturality (K.obj.d i j)).symm }

/-- The termwise unit is an isomorphism of complexes when the unit is invertible. -/
instance [IsIso adj.unit] (K : CochainComplex.Plus C₀) :
    IsIso (adj.unitCochainComplexPlus K).hom := by
  have (n : ℤ) : IsIso ((adj.unitCochainComplexPlus K).hom.f n) := by
    dsimp [unitCochainComplexPlus]; exact NatIso.isIso_app_of_isIso adj.unit _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- For `u : e(K) ⟶ J`, the composite `K ⟶ r(e(K)) ⟶ r(J)` of the unit of `e ⊣ r` with `r(u)`;
for `e = i_!` and `r` the restriction to `X`, this is `F ⟶ J|_X`. -/
def restrictResolution {K : CochainComplex.Plus C₀} {J : CochainComplex.Plus C}
    (u : e.mapCochainComplexPlus.obj K ⟶ J) : K ⟶ r.mapCochainComplexPlus.obj J :=
  adj.unitCochainComplexPlus K ≫ r.mapCochainComplexPlus.map u

/-- When the unit of `e ⊣ r` is invertible and `r` is exact, `K ⟶ r(J)` is a
quasi-isomorphism. -/
instance quasiIso_restrictResolution_hom [IsIso adj.unit] [r.PreservesHomology]
    {K : CochainComplex.Plus C₀} {J : CochainComplex.Plus C}
    (u : e.mapCochainComplexPlus.obj K ⟶ J) [QuasiIso u.hom] :
    QuasiIso (adj.restrictResolution u).hom := by
  have : QuasiIso ((r.mapHomologicalComplex _).map u.hom) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology u.hom r
  have h₁ : QuasiIso (adj.unitCochainComplexPlus K).hom := inferInstance
  exact quasiIso_comp (adj.unitCochainComplexPlus K).hom ((r.mapHomologicalComplex _).map u.hom)
    (hφ := h₁) (hφ' := this)

/-- A functor preserving injective objects maps a complex of injectives to one. -/
instance _root_.CategoryTheory.Functor.injective_mapCochainComplexPlus_obj_X
    [r.PreservesInjectiveObjects]
    (J : CochainComplex.Plus C) [∀ n, Injective (J.obj.X n)] (n : ℤ) :
    Injective ((r.mapCochainComplexPlus.obj J).obj.X n) :=
  r.injective_obj (J.obj.X n)

/-- A morphism `h : J ⟶ J'` compatible up to homotopy with `e(φ)` and the resolutions
`u`, `u'` restricts to a morphism `r(h)` compatible up to homotopy with `φ` and the restricted
resolutions. -/
lemma quotient_map_restrictResolution_comp {K K' : CochainComplex.Plus C₀}
    {J J' : CochainComplex.Plus C} (u : e.mapCochainComplexPlus.obj K ⟶ J)
    (u' : e.mapCochainComplexPlus.obj K' ⟶ J') (φ : K ⟶ K') (h : J ⟶ J')
    (hh : (HomotopyCategory.Plus.quotient C).map (u ≫ h) =
      (HomotopyCategory.Plus.quotient C).map (e.mapCochainComplexPlus.map φ ≫ u')) :
    (HomotopyCategory.Plus.quotient C₀).map
        (adj.restrictResolution u ≫ r.mapCochainComplexPlus.map h) =
      (HomotopyCategory.Plus.quotient C₀).map (φ ≫ adj.restrictResolution u') := by
  have hh' : (HomotopyCategory.quotient C _).map (u.hom ≫ h.hom) =
      (HomotopyCategory.quotient C _).map ((e.mapCochainComplexPlus.map φ).hom ≫ u'.hom) :=
    congrArg (fun a => a.hom) hh
  let H := r.mapHomotopy (HomotopyCategory.homotopyOfEq _ _ hh')
  have hφ : φ ≫ adj.unitCochainComplexPlus K' =
      adj.unitCochainComplexPlus K ≫
        r.mapCochainComplexPlus.map (e.mapCochainComplexPlus.map φ) := by
    ext n
    exact (adj.unit.naturality (φ.hom.f n))
  ext1
  apply HomotopyCategory.eq_of_homotopy
  have e₁ : (adj.restrictResolution u ≫ r.mapCochainComplexPlus.map h).hom =
      (adj.unitCochainComplexPlus K).hom ≫ (r.mapHomologicalComplex _).map (u.hom ≫ h.hom) := by
    simp [restrictResolution]; rfl
  have e₂ : (φ ≫ adj.restrictResolution u').hom =
      (adj.unitCochainComplexPlus K).hom ≫
        (r.mapHomologicalComplex _).map ((e.mapCochainComplexPlus.map φ).hom ≫ u'.hom) := by
    rw [restrictResolution, ← Category.assoc, hφ]
    simp; rfl
  change Homotopy (adj.restrictResolution u ≫ r.mapCochainComplexPlus.map h).hom
    (φ ≫ adj.restrictResolution u').hom
  rw [e₁, e₂]
  exact H.compLeft _


section Derived

variable [HasDerivedCategory C] [HasDerivedCategory C₀] [HasDerivedCategory D₀]
  [HasDerivedCategory D] [EnoughInjectives C] [EnoughInjectives C₀] [EnoughInjectives D₀]
  [IsIso adj.unit] [r.PreservesHomology] [r.PreservesInjectiveObjects]
  (f₀ : C₀ ⥤ D₀) (g : D₀ ⥤ D) (F' : C ⥤ D) [f₀.Additive] [g.Additive] [F'.Additive]
  [g.PreservesHomology] (θ : r ⋙ f₀ ⋙ g ⟶ F')

/-- The chain map `θ_J : g(f₀(r(J))) ⟶ F'(J)`, in the bounded below homotopy category. -/
def exchangeHomotopyCategoryPlusMap (J : CochainComplex.Plus C) :
    g.mapHomotopyCategoryPlus.obj (f₀.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient C₀).obj (r.mapCochainComplexPlus.obj J))) ⟶
      F'.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient C).obj J) :=
  ObjectProperty.homMk ((HomotopyCategory.quotient D _).map
    ((NatTrans.mapHomologicalComplex θ _).app J.obj))

omit [IsIso adj.unit] [r.PreservesHomology] [r.PreservesInjectiveObjects] [HasDerivedCategory C]
  [HasDerivedCategory C₀] [HasDerivedCategory D₀] [HasDerivedCategory D] [EnoughInjectives C]
  [EnoughInjectives C₀] [EnoughInjectives D₀] [g.PreservesHomology] in
/-- The chain map `θ_J` is natural in `J`, in the bounded below homotopy category. -/
lemma exchangeHomotopyCategoryPlusMap_naturality {J J' : CochainComplex.Plus C} (h : J ⟶ J') :
    exchangeHomotopyCategoryPlusMap f₀ g F' θ J ≫
        F'.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient C).map h) =
      g.mapHomotopyCategoryPlus.map (f₀.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient C₀).map (r.mapCochainComplexPlus.map h))) ≫
        exchangeHomotopyCategoryPlusMap f₀ g F' θ J' := by
  ext1
  have := NatTrans.mapHomologicalComplex_naturality θ (c := ComplexShape.up ℤ) h.hom
  have h' := (HomotopyCategory.quotient D _).congr_map this
  rw [Functor.map_comp, Functor.map_comp] at h'
  exact h'.symm


/-- The morphism `g(Rf₀(K)) ⟶ RF'(e(K))` of bounded below derived categories represented by the
chain map `θ_J : g(f₀(r(J))) ⟶ F'(J)`, for an injective resolution `u : e(K) ⟶ J`: the
derived functor `Rf₀` is computed on the resolution `K ⟶ r(J)` (`restrictResolution`), the exact
functor `g` termwise, and `RF'` on `J`. -/
def exchangeDerivedMap {K : CochainComplex.Plus C₀} {J : CochainComplex.Plus C}
    (u : e.mapCochainComplexPlus.obj K ⟶ J) [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    g.rightDerivedFunctorPlus.obj (f₀.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C₀).obj K))) ⟶
      F'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient C).obj (e.mapCochainComplexPlus.obj K))) :=
  have := Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology g
  g.rightDerivedFunctorPlus.map
      (f₀.rightDerivedFunctorPlusObjIsoOfInjective (adj.restrictResolution u)).hom ≫
    ((asIso g.rightDerivedFunctorPlusUnit).app (f₀.mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.quotient C₀).obj (r.mapCochainComplexPlus.obj J)))).inv ≫
    DerivedCategory.Plus.Qh.map (exchangeHomotopyCategoryPlusMap f₀ g F' θ J) ≫
    (F'.rightDerivedFunctorPlusObjIsoOfInjective u).inv

/-- The morphism `exchangeDerivedMap` is natural in `K`: for `φ : K ⟶ K'` and injective
resolutions `u : e(K) ⟶ J`, `u' : e(K') ⟶ J'`, the square with `g(Rf₀(φ))` and `RF'(e(φ))`
commutes. -/
theorem exchangeDerivedMap_naturality {K K' : CochainComplex.Plus C₀}
    {J J' : CochainComplex.Plus C} (u : e.mapCochainComplexPlus.obj K ⟶ J)
    (u' : e.mapCochainComplexPlus.obj K' ⟶ J') [QuasiIso u.hom] [QuasiIso u'.hom]
    [∀ n, Injective (J.obj.X n)] [∀ n, Injective (J'.obj.X n)] (φ : K ⟶ K') :
    adj.exchangeDerivedMap f₀ g F' θ u ≫ F'.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient C).map (e.mapCochainComplexPlus.map φ))) =
      g.rightDerivedFunctorPlus.map (f₀.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C₀).map φ))) ≫
        adj.exchangeDerivedMap f₀ g F' θ u' := by
  have := Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology g
  obtain ⟨h, hh⟩ := CochainComplex.Plus.exists_quotient_map_comp_eq u u'
    (e.mapCochainComplexPlus.map φ)
  have h₁ := F'.rightDerivedFunctorPlus_map_comp_objIsoOfInjective_hom u u' _ h hh
  have h₂ := f₀.rightDerivedFunctorPlus_map_comp_objIsoOfInjective_hom
    (adj.restrictResolution u) (adj.restrictResolution u') φ (r.mapCochainComplexPlus.map h)
    (adj.quotient_map_restrictResolution_comp u u' φ h hh)
  have h₃ := g.rightDerivedFunctorPlusUnit.naturality (f₀.mapHomotopyCategoryPlus.map
    ((HomotopyCategory.Plus.quotient C₀).map (r.mapCochainComplexPlus.map h)))
  have h₄ := exchangeHomotopyCategoryPlusMap_naturality f₀ g F' θ h
  have h₁' : (F'.rightDerivedFunctorPlusObjIsoOfInjective u).inv ≫
      F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient C).map (e.mapCochainComplexPlus.map φ))) =
      DerivedCategory.Plus.Qh.map
          (F'.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient C).map h)) ≫
        (F'.rightDerivedFunctorPlusObjIsoOfInjective u').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h₃' : ((asIso g.rightDerivedFunctorPlusUnit).app (f₀.mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient C₀).obj (r.mapCochainComplexPlus.obj J)))).inv ≫
      DerivedCategory.Plus.Qh.map (g.mapHomotopyCategoryPlus.map (f₀.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient C₀).map (r.mapCochainComplexPlus.map h)))) =
      g.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (f₀.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient C₀).map (r.mapCochainComplexPlus.map h)))) ≫
        ((asIso g.rightDerivedFunctorPlusUnit).app (f₀.mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient C₀).obj (r.mapCochainComplexPlus.obj J')))).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact h₃
  simp only [exchangeDerivedMap, Category.assoc]
  rw [h₁', ← Functor.map_comp_assoc, h₄, Functor.map_comp_assoc, reassoc_of% h₃',
    ← Functor.map_comp_assoc, ← h₂, Functor.map_comp_assoc]

/-- The morphism `exchangeDerivedMap` does not depend on the injective resolution. -/
theorem exchangeDerivedMap_eq {K : CochainComplex.Plus C₀} {J J' : CochainComplex.Plus C}
    (u : e.mapCochainComplexPlus.obj K ⟶ J) (u' : e.mapCochainComplexPlus.obj K ⟶ J')
    [QuasiIso u.hom] [QuasiIso u'.hom] [∀ n, Injective (J.obj.X n)]
    [∀ n, Injective (J'.obj.X n)] :
    adj.exchangeDerivedMap f₀ g F' θ u = adj.exchangeDerivedMap f₀ g F' θ u' := by
  simpa using adj.exchangeDerivedMap_naturality f₀ g F' θ u u' (𝟙 K)

end Derived

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

universe r u

section

variable (Λ : Type r) [Ring Λ] {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') [Etale i] [Mono i]
  (j : Y ⟶ Y') [Etale j] {f : X ⟶ Y} {f' : X' ⟶ Y'}

omit [Mono i] in
/-- Restriction along an étale morphism, being exact, preserves homology. -/
instance : (etaleModuleRestriction.{u, r} Λ i).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- For an injective resolution `u : i_! F ⟶ J` of a bounded below complex `F` of sheaves of
`Λ`-modules on `X`, the composite `F ≅ (i_! F)|_X ⟶ J|_X` is an injective resolution: a
quasi-isomorphism into a bounded below complex of injective sheaves. -/
@[weil "lem_fk108_open_proper_exchange_map_derived_well_defined"]
theorem quasiIso_restrictResolution_and_injective
    {F : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    {J : CochainComplex.Plus (EtaleModules.{u, r} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    QuasiIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).restrictResolution u).hom ∧
      ∀ n, Injective (((etaleModuleRestriction.{u, r} Λ i).mapCochainComplexPlus.obj J).obj.X n) :=
  ⟨inferInstance, fun _ => inferInstance⟩

omit [Mono i] in
/-- The exchange chain map `θ_J : j_! f_* (J|_X) ⟶ f'_* J` is a chain map: it commutes with the
differentials. -/
@[weil "lem_fk108_open_proper_exchange_map_derived_well_defined"]
theorem exchangeChainMap_comm
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (J : CochainComplex (EtaleModules.{u, r} Λ X') ℤ) (p q : ℤ) :
    (exchangeChainMap Λ i j α J).f p ≫
        (((etaleModuleDirectImage.{u, r} Λ f').mapHomologicalComplex _).obj J).d p q =
      (((etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f ⋙
        etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex _).obj J).d p q ≫
        (exchangeChainMap Λ i j α J).f q :=
  (exchangeChainMap Λ i j α J).comm p q

/-- The morphism `(*) : j_! Rf_* F ⟶ Rf'_* (i_! F)` of bounded below derived categories of
sheaves of `Λ`-modules on `Y'` represented by the exchange chain map `θ_J`, for an injective
resolution `u : i_! F ⟶ J`. -/
@[weil "lem_fk108_open_proper_exchange_map_derived_well_defined"]
def openProperExchangeDerivedMap
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    {F : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    {J : CochainComplex.Plus (EtaleModules.{u, r} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    (etaleModuleDerivedExtensionByZero.{u, r} Λ j).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ f).obj
          (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj F))) ⟶
      (etaleModuleDerivedDirectImage.{u, r} Λ f').obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
          ((etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F))) :=
  (etaleModuleExtensionByZeroAdj.{u, r} Λ i).exchangeDerivedMap
    (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleExtensionByZero.{u, r} Λ j)
    (etaleModuleDirectImage.{u, r} Λ f') (exchangeCounitTransformation Λ i j α) u

/-- The morphism `(*)` is represented by the exchange chain map `θ_J`: it is the image of `θ_J`
in the derived category, composed with the identifications of `j_! Rf_* F` with `j_! f_* (J|_X)`
(through the injective resolution `F ⟶ J|_X` and the exactness of `j_!`) and of
`Rf'_* (i_! F)` with `f'_* J`. -/
@[weil "lem_fk108_open_proper_exchange_map_derived_well_defined"]
theorem openProperExchangeDerivedMap_eq
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    {F : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    {J : CochainComplex.Plus (EtaleModules.{u, r} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    openProperExchangeDerivedMap Λ i j α u =
      (etaleModuleDerivedExtensionByZero.{u, r} Λ j).map
          ((etaleModuleDirectImage.{u, r} Λ f).rightDerivedFunctorPlusObjIsoOfInjective
            ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).restrictResolution u)).hom ≫
        ((asIso (etaleModuleExtensionByZero.{u, r} Λ j).rightDerivedFunctorPlusUnit).app
          ((etaleModuleDirectImage.{u, r} Λ f).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj
              ((etaleModuleRestriction.{u, r} Λ i).mapCochainComplexPlus.obj J)))).inv ≫
        DerivedCategory.Plus.Qh.map (Adjunction.exchangeHomotopyCategoryPlusMap
          (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleExtensionByZero.{u, r} Λ j)
          (etaleModuleDirectImage.{u, r} Λ f') (exchangeCounitTransformation Λ i j α) J) ≫
        ((etaleModuleDirectImage.{u, r} Λ f').rightDerivedFunctorPlusObjIsoOfInjective u).inv :=
  rfl

omit [Mono i] in
/-- The chain map representing `(*)` is the exchange chain map `θ_J`. -/
theorem exchangeHomotopyCategoryPlusMap_hom
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (J : CochainComplex.Plus (EtaleModules.{u, r} Λ X')) :
    (Adjunction.exchangeHomotopyCategoryPlusMap (etaleModuleDirectImage.{u, r} Λ f)
        (etaleModuleExtensionByZero.{u, r} Λ j) (etaleModuleDirectImage.{u, r} Λ f')
        (exchangeCounitTransformation Λ i j α) J).hom =
      (HomotopyCategory.quotient _ _).map (exchangeChainMap Λ i j α J.obj) :=
  rfl

/-- The morphism `(*) : j_! Rf_* F ⟶ Rf'_* (i_! F)` does not depend on the choice of the
injective resolution `i_! F ⟶ J`. -/
@[weil "lem_fk108_open_proper_exchange_map_derived_well_defined"]
theorem openProperExchangeDerivedMap_eq_of_resolution
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    {F : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    {J J' : CochainComplex.Plus (EtaleModules.{u, r} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    (u' : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J')
    [QuasiIso u.hom] [QuasiIso u'.hom] [∀ n, Injective (J.obj.X n)]
    [∀ n, Injective (J'.obj.X n)] :
    openProperExchangeDerivedMap Λ i j α u = openProperExchangeDerivedMap Λ i j α u' :=
  (etaleModuleExtensionByZeroAdj.{u, r} Λ i).exchangeDerivedMap_eq _ _ _ _ u u'

/-- The morphism `(*) : j_! Rf_* F ⟶ Rf'_* (i_! F)` is natural in the bounded below complex
`F`. -/
@[weil "lem_fk108_open_proper_exchange_map_derived_well_defined"]
theorem openProperExchangeDerivedMap_naturality
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    {F F' : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    {J J' : CochainComplex.Plus (EtaleModules.{u, r} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    (u' : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F' ⟶ J')
    [QuasiIso u.hom] [QuasiIso u'.hom] [∀ n, Injective (J.obj.X n)]
    [∀ n, Injective (J'.obj.X n)] (φ : F ⟶ F') :
    openProperExchangeDerivedMap Λ i j α u ≫
        (etaleModuleDerivedDirectImage.{u, r} Λ f').map (DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient _).map
            ((etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.map φ))) =
      (etaleModuleDerivedExtensionByZero.{u, r} Λ j).map
          ((etaleModuleDerivedDirectImage.{u, r} Λ f).map
            (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map φ))) ≫
        openProperExchangeDerivedMap Λ i j α u' :=
  (etaleModuleExtensionByZeroAdj.{u, r} Λ i).exchangeDerivedMap_naturality _ _ _ _ u u' φ

end

end AlgebraicGeometry
