module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDerived
public import Weil.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChange
public import Weil.Defs.Algebra.Homology.DerivedCategory.Basic
public import Weil.Attr

/-!
# The open-closed triangle for the derived direct image with proper support

Let `f : X ⟶ S` be a morphism of schemes with a compactification `c = (X̄, φ, f̄)`, let
`j : U ⟶ X` be an open immersion and `i : A ⟶ X` a closed immersion whose images are
complementary. Then `f ∘ j` and `f ∘ i` have compactifications induced by `c`, and for bounded
below complexes `K` of sheaves of `Λ`-modules on the small étale site of `X` there is a triangle
`R(f ∘ j)_!(j⁻¹ K) ⟶ Rf_! K ⟶ R(f ∘ i)_!(i⁻¹ K) ⟶ R(f ∘ j)_!(j⁻¹ K)[1]`
in the derived category of `S`, admissible for every `K` and natural in `K` for morphisms of
complexes.

The proof is the source's. The counit of `j_! ⊣ j⁻¹` and the unit of `i⁻¹ ⊣ i_*` give, degreewise,
a short exact sequence of complexes `0 ⟶ j_! j⁻¹ K ⟶ K ⟶ i_* i⁻¹ K ⟶ 0` natural in `K`
(Stacks, Tag 095L); its triangle in the derived category is natural in `K` because the connecting
morphism of a short exact sequence of complexes is natural
(`DerivedCategory.triangleOfSESδ_naturality`). The triangulated functor `Rf_!` carries it to a
natural distinguished triangle, whose first and third vertices are identified with
`R(f ∘ j)_! j⁻¹` and `R(f ∘ i)_! i⁻¹` by `Stacks.EtaleCohomology.derivedLowerShriekRestrictOpenIso`
and `Stacks.EtaleCohomology.derivedLowerShriekRestrictClosedIso`.

## Main definitions

* `CategoryTheory.Pretriangulated.ExistsNatDistTriang`: three functors to a pretriangulated
  category carry natural transformations `a`, `b`, `δ` whose components are distinguished
  triangles.
* `Stacks.EtaleCohomology.etaleModuleOpenClosedShortComplex`: the short exact sequence of complexes
  `0 ⟶ j_! j⁻¹ K ⟶ K ⟶ i_* i⁻¹ K ⟶ 0`, as a functor of the complex `K`.

## Main results

* `Stacks.EtaleCohomology.existsNatDistTriang_openClosed_plus`: the triangle
  `j_! j⁻¹ K ⟶ K ⟶ i_* i⁻¹ K ⟶` in `D⁺(X_ét, Λ)`, natural in bounded below complexes `K`.
* `Stacks.EtaleCohomology.existsNatDistTriang_derivedLowerShriek_openClosed`: the open-closed
  triangle for `Rf_!` on Mathlib's small étale sites, natural in bounded below complexes.
* `AlgebraicGeometry.SmallEtale.exists_mem_admissibleTriangles_derivedLowerShriek_openClosed`: the
  open-closed admissible triangle for `Rf_!` on the small étale sites `SmallEtale B X` of a big
  étale site, natural in bounded below complexes, with the compactifiability of `f ∘ j` and
  `f ∘ i`.

## Implementation notes

The source states the result for abelian sheaves and complexes with torsion cohomology. The
construction uses neither condition, so it is stated for sheaves of `Λ`-modules over an
arbitrary ring `Λ` and for all bounded below complexes; the source's case is `Λ = ℤ` restricted
to torsion complexes.

The functor `Rf_!` is `AlgebraicGeometry.SmallEtale.derivedLowerShriek`, computed with the
compactification `c`; `R(f ∘ j)_!` and `R(f ∘ i)_!` are computed with the compactifications
`AlgebraicGeometry.CompactificationOf.restrictOpen` and
`AlgebraicGeometry.CompactificationOf.restrictClosed` induced by `c`, the ones of the source's
proof. Any other choice gives isomorphic functors, by the independence of the compactification.
The closed subscheme `A` may carry any closed subscheme structure. The open-closed triangle on
Mathlib's sites needs `f` quasi-compact, which holds in the source's noetherian setting.

The triangle is admissible in the sense of `DerivedCategory.admissibleTriangles`, whose third
morphism has the opposite sign of Mathlib's distinguished triangles: the theorem negates the
connecting morphism of the distinguished triangle. "Functorially in `K`" is the existence of
natural transformations `a`, `b`, `δ` between the three vertex functors on the category
`CochainComplex.Plus` of bounded below complexes.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 0GKP](https://stacks.math.columbia.edu/tag/0GKP)
* [Stacks Project, Tag 0GKL](https://stacks.math.columbia.edu/tag/0GKL)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Pretriangulated

section Generic

variable {𝒞 : Type*} [Category* 𝒞] {D : Type*} [Category* D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Three functors `F₁ F₂ F₃ : 𝒞 ⥤ D` to a pretriangulated category carry a *natural
distinguished triangle* if there are natural transformations `a : F₁ ⟶ F₂`, `b : F₂ ⟶ F₃` and
`δ : F₃ ⟶ F₁[1]` whose components form a distinguished triangle at every object of `𝒞`. -/
def ExistsNatDistTriang (F₁ F₂ F₃ : 𝒞 ⥤ D) : Prop :=
  ∃ (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃) (δ : F₃ ⟶ F₁ ⋙ shiftFunctor D (1 : ℤ)),
    ∀ K, Triangle.mk (a.app K) (b.app K) (δ.app K) ∈ distTriang D

namespace ExistsNatDistTriang

variable {F₁ F₂ F₃ G₁ G₂ G₃ : 𝒞 ⥤ D}

/-- A natural distinguished triangle can be transported along isomorphisms of its three
vertex functors. -/
theorem of_iso (h : ExistsNatDistTriang F₁ F₂ F₃) (e₁ : F₁ ≅ G₁) (e₂ : F₂ ≅ G₂)
    (e₃ : F₃ ≅ G₃) : ExistsNatDistTriang G₁ G₂ G₃ := by
  obtain ⟨a, b, δ, hT⟩ := h
  refine ⟨e₁.inv ≫ a ≫ e₂.hom, e₂.inv ≫ b ≫ e₃.hom,
    e₃.inv ≫ δ ≫ Functor.whiskerRight e₁.hom (shiftFunctor D (1 : ℤ)), fun K => ?_⟩
  refine isomorphic_distinguished _ (hT K) _
    (Triangle.isoMk _ _ (e₁.app K).symm (e₂.app K).symm (e₃.app K).symm ?_ ?_ ?_)
  · simp
  · simp
  · simp [← Functor.map_comp]

/-- A natural distinguished triangle restricts along any functor `P : 𝒞' ⥤ 𝒞`. -/
theorem whiskerLeft {𝒞' : Type*} [Category* 𝒞'] (h : ExistsNatDistTriang F₁ F₂ F₃)
    (P : 𝒞' ⥤ 𝒞) : ExistsNatDistTriang (P ⋙ F₁) (P ⋙ F₂) (P ⋙ F₃) := by
  obtain ⟨a, b, δ, hT⟩ := h
  exact ⟨Functor.whiskerLeft P a, Functor.whiskerLeft P b, Functor.whiskerLeft P δ,
    fun K => hT (P.obj K)⟩

variable {D' : Type*} [Category* D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/-- A triangulated functor `H` carries a natural distinguished triangle to a natural
distinguished triangle. -/
theorem map (h : ExistsNatDistTriang F₁ F₂ F₃) (H : D ⥤ D') [H.CommShift ℤ]
    [H.IsTriangulated] : ExistsNatDistTriang (F₁ ⋙ H) (F₂ ⋙ H) (F₃ ⋙ H) := by
  obtain ⟨a, b, δ, hT⟩ := h
  refine ⟨Functor.whiskerRight a H, Functor.whiskerRight b H,
    Functor.whiskerRight δ H ≫ Functor.whiskerLeft F₁ (H.commShiftIso (1 : ℤ)).hom,
    fun K => ?_⟩
  exact H.map_distinguished _ (hT K)

end ExistsNatDistTriang

end Generic

section Derived

variable {𝒞 : Type*} [Category* 𝒞] {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A functor `S` to short exact sequences of cochain complexes gives a natural distinguished
triangle `Q S₁ ⟶ Q S₂ ⟶ Q S₃ ⟶ (Q S₁)[1]` in the derived category, the third morphism being the
connecting morphism `DerivedCategory.triangleOfSESδ`. -/
theorem existsNatDistTriang_of_shortExact (S : 𝒞 ⥤ ShortComplex (CochainComplex C ℤ))
    (hS : ∀ K, (S.obj K).ShortExact) :
    ExistsNatDistTriang (S ⋙ ShortComplex.π₁ ⋙ DerivedCategory.Q)
      (S ⋙ ShortComplex.π₂ ⋙ DerivedCategory.Q) (S ⋙ ShortComplex.π₃ ⋙ DerivedCategory.Q) :=
  ⟨Functor.whiskerLeft S (Functor.whiskerRight ShortComplex.π₁Toπ₂ DerivedCategory.Q),
    Functor.whiskerLeft S (Functor.whiskerRight ShortComplex.π₂Toπ₃ DerivedCategory.Q),
    { app K := DerivedCategory.triangleOfSESδ (hS K)
      naturality K L φ := by
        exact (DerivedCategory.triangleOfSESδ_naturality (hS K) (hS L) (S.map φ)).symm },
    fun K => DerivedCategory.triangleOfSES_distinguished (hS K)⟩

/-- A natural distinguished triangle in `D(C)` whose vertices lie in the bounded below derived
category is a natural distinguished triangle in `D⁺(C)`. -/
theorem ExistsNatDistTriang.of_comp_plusι {F₁ F₂ F₃ : 𝒞 ⥤ DerivedCategory.Plus C}
    (h : ExistsNatDistTriang (F₁ ⋙ DerivedCategory.Plus.ι) (F₂ ⋙ DerivedCategory.Plus.ι)
      (F₃ ⋙ DerivedCategory.Plus.ι)) : ExistsNatDistTriang F₁ F₂ F₃ := by
  obtain ⟨a, b, δ, hT⟩ := h
  let hι :=
    (ObjectProperty.fullyFaithfulι (DerivedCategory.TStructure.t (C := C)).plus).whiskeringRight 𝒞
  let δ' : F₃ ⋙ DerivedCategory.Plus.ι ⟶
      (F₁ ⋙ shiftFunctor (DerivedCategory.Plus C) (1 : ℤ)) ⋙ DerivedCategory.Plus.ι :=
    δ ≫ Functor.whiskerLeft F₁ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv
  have ha : ∀ K, ((hι.preimage a).app K).hom = a.app K := fun K =>
    congrArg (fun t => t.app K) (hι.map_preimage a)
  have hb : ∀ K, ((hι.preimage b).app K).hom = b.app K := fun K =>
    congrArg (fun t => t.app K) (hι.map_preimage b)
  have hδ : ∀ K, ((hι.preimage δ').app K).hom = δ'.app K := fun K =>
    congrArg (fun t => t.app K) (hι.map_preimage δ')
  refine ⟨hι.preimage a, hι.preimage b, hι.preimage δ', fun K => ?_⟩
  change DerivedCategory.Plus.ι.mapTriangle.obj _ ∈ distTriang (DerivedCategory C)
  refine isomorphic_distinguished _ (hT K) _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_)
  · exact (comp_id _).trans ((ha K).trans (id_comp _).symm)
  · exact (comp_id _).trans ((hb K).trans (id_comp _).symm)
  · change (((hι.preimage δ').app K).hom ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app (F₁.obj K)) ≫
          (shiftFunctor (DerivedCategory C) (1 : ℤ)).map (𝟙 _) = 𝟙 _ ≫ δ.app K
    rw [hδ]
    simp [δ']

end Derived

end CategoryTheory.Pretriangulated

universe u r

namespace CategoryTheory.Functor

section PlusComparison

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- For an exact functor `F`, the bounded below derived functor `F : D⁺(A) ⥤ D⁺(B)` applied to
the image of a bounded below complex is the image of the complex `F K`:
`Q⁺ ⋙ F ≅ F ⋙ Q⁺`, on bounded below complexes. -/
def plusQCompMapDerivedCategoryPlusIso (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] :
    DerivedCategory.Plus.Q ⋙ F.mapDerivedCategoryPlus ≅
      F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q :=
  ((ObjectProperty.fullyFaithfulι
      (DerivedCategory.TStructure.t (C := B)).plus).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι A) F.mapDerivedCategoryFactors)

/-- An isomorphism of additive functors induces an isomorphism of the functors they induce on
bounded below complexes. -/
def mapCochainComplexPlusIsoOfIso {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ≅ G) :
    F.mapCochainComplexPlus ≅ G.mapCochainComplexPlus :=
  ((CochainComplex.Plus.fullyFaithfulι B).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι A) (NatIso.mapHomologicalComplex α _))

end PlusComparison

end CategoryTheory.Functor

open _root_.AlgebraicGeometry CategoryTheory.Pretriangulated

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

section OpenClosed

variable (Λ : Type r) [Ring Λ] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The short exact sequence of complexes `0 ⟶ j_! j⁻¹ K ⟶ K ⟶ i_* i⁻¹ K ⟶ 0` of sheaves of
`Λ`-modules on the small étale site of `X`, functorial in the complex `K`: degreewise the counit
of `j_! ⊣ j⁻¹` and the unit of `i⁻¹ ⊣ i_*`. -/
def etaleModuleOpenClosedShortComplex (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤
      ShortComplex (CochainComplex (EtaleModules.{u, r} Λ X) ℤ) where
  obj K := ShortComplex.mk
    ((Functor.mapCochainComplexTransToId (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit).app K)
    ((Functor.mapCochainComplexTransFromId (etaleModuleInverseImageAdj.{u, r} Λ i).unit).app K)
    (by
      ext n
      simp [etaleModuleExtensionByZero_counit_comp_inverseImage_unit Λ i j hij])
  map φ :=
    { τ₁ := ((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j).mapHomologicalComplex _).map φ
      τ₂ := φ
      τ₃ := ((etaleModuleDirectImageOfInverseImage.{u, r} Λ i).mapHomologicalComplex _).map φ
      comm₁₂ := (Functor.mapCochainComplexTransToId
        (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit).naturality φ
      comm₂₃ := (Functor.mapCochainComplexTransFromId
        (etaleModuleInverseImageAdj.{u, r} Λ i).unit).naturality φ }

/-- The sequence `0 ⟶ j_! j⁻¹ K ⟶ K ⟶ i_* i⁻¹ K ⟶ 0` of complexes is short exact: it is so in each
degree, by Stacks, Tag 095L. -/
theorem shortExact_etaleModuleOpenClosedShortComplex_obj
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    ((etaleModuleOpenClosedShortComplex Λ i j hij).obj K).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  obtain ⟨_, h⟩ := shortExact_etaleModuleExtensionByZero_directImage.{u, r} Λ i j hij (K.X n)
  exact h

/-- **The open-closed triangle on bounded below complexes** (Stacks, Tag 0GKL, functorial
form). For bounded below complexes `K` of sheaves of `Λ`-modules on the small étale site of `X`,
there is a distinguished triangle `j_! j⁻¹ K ⟶ K ⟶ i_* i⁻¹ K ⟶ (j_! j⁻¹ K)[1]` in `D⁺(X_ét, Λ)`,
natural in `K` for morphisms of complexes. -/
theorem existsNatDistTriang_openClosed_plus (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ExistsNatDistTriang
      ((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q)
      DerivedCategory.Plus.Q
      ((etaleModuleDirectImageOfInverseImage.{u, r} Λ i).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q) :=
  ExistsNatDistTriang.of_comp_plusι
    ((existsNatDistTriang_of_shortExact
      (CochainComplex.Plus.ι _ ⋙ etaleModuleOpenClosedShortComplex Λ i j hij)
      (fun K => shortExact_etaleModuleOpenClosedShortComplex_obj Λ i j hij K.obj)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _))

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits
  CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable {Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : CompactificationOf (Over.mk f))

/-- `Rf_!(j_! j⁻¹ K) ≅ Rg_!(j⁻¹ K)` for bounded below complexes `K`, natural in `K`, where
`g = j ≫ f` and `Rg_!` is computed with the compactification induced by `c`. -/
def derivedLowerShriekOpenPartIso :
    ((etaleModuleExtensionByZeroOfRestriction.{u, r} Λ j).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q) ⋙ derivedLowerShriek.{u, r} f c Λ ≅
      DerivedCategory.Plus.Q ⋙ (etaleModuleInverseImage.{u, r} Λ j).mapDerivedCategoryPlus ⋙
        derivedLowerShriek.{u, r} (j ≫ f) (c.restrictOpen j) Λ :=
  Functor.isoWhiskerRight (Functor.isoWhiskerRight (Functor.mapCochainComplexPlusIsoOfIso
      (Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, r} Λ j).symm
        (etaleModuleExtensionByZero.{u, r} Λ j))) _) _ ≪≫
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (etaleModuleInverseImage.{u, r} Λ j).mapCochainComplexPlus
      (Functor.plusQCompMapDerivedCategoryPlusIso
        (etaleModuleExtensionByZero.{u, r} Λ j)).symm) _ :
      ((etaleModuleInverseImage.{u, r} Λ j).mapCochainComplexPlus ⋙
        (etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus ⋙
          DerivedCategory.Plus.Q) ⋙ derivedLowerShriek.{u, r} f c Λ ≅ _) ≪≫
    (Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (Functor.plusQCompMapDerivedCategoryPlusIso (etaleModuleInverseImage.{u, r} Λ j)).symm
      (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategoryPlus) _ :
      (((etaleModuleInverseImage.{u, r} Λ j).mapCochainComplexPlus ⋙
          DerivedCategory.Plus.Q) ⋙
        (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategoryPlus) ⋙
          derivedLowerShriek.{u, r} f c Λ ≅ _) ≪≫
    (Functor.isoWhiskerLeft (DerivedCategory.Plus.Q ⋙
        (etaleModuleInverseImage.{u, r} Λ j).mapDerivedCategoryPlus)
      (Functor.isoWhiskerRight
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso
          (etaleModuleExtensionByZero.{u, r} Λ j)) _ ≪≫
        (derivedLowerShriekRestrictOpenIso.{u, r} Λ c j).symm) :
      (DerivedCategory.Plus.Q ⋙ (etaleModuleInverseImage.{u, r} Λ j).mapDerivedCategoryPlus) ⋙
        (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategoryPlus ⋙
          derivedLowerShriek.{u, r} f c Λ ≅ _)

/-- `Rf_!(i_* i⁻¹ K) ≅ Rh_!(i⁻¹ K)` for bounded below complexes `K`, natural in `K`, where
`h = i ≫ f` and `Rh_!` is computed with the compactification induced by `c`. -/
def derivedLowerShriekClosedPartIso :
    ((etaleModuleDirectImageOfInverseImage.{u, r} Λ i).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q) ⋙ derivedLowerShriek.{u, r} f c Λ ≅
      DerivedCategory.Plus.Q ⋙ (etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus ⋙
        derivedLowerShriek.{u, r} (i ≫ f) (c.restrictClosed i) Λ :=
  (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (etaleModuleInverseImage.{u, r} Λ i).mapCochainComplexPlus
      (Functor.plusQCompMapDerivedCategoryPlusIso
        (etaleModuleDirectImage.{u, r} Λ i)).symm) _ :
      ((etaleModuleInverseImage.{u, r} Λ i).mapCochainComplexPlus ⋙
        (etaleModuleDirectImage.{u, r} Λ i).mapCochainComplexPlus ⋙
          DerivedCategory.Plus.Q) ⋙ derivedLowerShriek.{u, r} f c Λ ≅ _) ≪≫
    (Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (Functor.plusQCompMapDerivedCategoryPlusIso (etaleModuleInverseImage.{u, r} Λ i)).symm
      (etaleModuleDirectImage.{u, r} Λ i).mapDerivedCategoryPlus) _ :
      (((etaleModuleInverseImage.{u, r} Λ i).mapCochainComplexPlus ⋙
          DerivedCategory.Plus.Q) ⋙
        (etaleModuleDirectImage.{u, r} Λ i).mapDerivedCategoryPlus) ⋙
          derivedLowerShriek.{u, r} f c Λ ≅ _) ≪≫
    (Functor.isoWhiskerLeft (DerivedCategory.Plus.Q ⋙
        (etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus)
      (Functor.isoWhiskerRight
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso
          (etaleModuleDirectImage.{u, r} Λ i)) _ ≪≫
        (derivedLowerShriekRestrictClosedIso.{u, r} Λ c i).symm) :
      (DerivedCategory.Plus.Q ⋙ (etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus) ⋙
        (etaleModuleDirectImage.{u, r} Λ i).mapDerivedCategoryPlus ⋙
          derivedLowerShriek.{u, r} f c Λ ≅ _)

/-- **The open-closed triangle for `Rf_!`, functorial in bounded below complexes** (Stacks,
Tag 0GKP, on Mathlib's small étale sites). -/
theorem existsNatDistTriang_derivedLowerShriek_openClosed
    (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ExistsNatDistTriang
      (DerivedCategory.Plus.Q ⋙ (etaleModuleInverseImage.{u, r} Λ j).mapDerivedCategoryPlus ⋙
        derivedLowerShriek.{u, r} (j ≫ f) (c.restrictOpen j) Λ)
      (DerivedCategory.Plus.Q ⋙ derivedLowerShriek.{u, r} f c Λ)
      (DerivedCategory.Plus.Q ⋙ (etaleModuleInverseImage.{u, r} Λ i).mapDerivedCategoryPlus ⋙
        derivedLowerShriek.{u, r} (i ≫ f) (c.restrictClosed i) Λ) :=
  ((existsNatDistTriang_openClosed_plus Λ i j hij).map (derivedLowerShriek.{u, r} f c Λ)).of_iso
    (derivedLowerShriekOpenPartIso Λ j c) (Iso.refl _) (derivedLowerShriekClosedPartIso Λ i c)

end OpenClosed

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.SmallEtale

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {B : BigEtaleSite.{u}} (Λ : Type r) [Ring Λ]

section Transport

variable {X S : B.Scheme}

/-- The functor `D⁺(S_ét, Λ) ⥤ D(SmallEtale B S, Λ)` from Mathlib's small étale site to the small
étale site of `B`: forget the boundedness, then apply the equivalence of sheaf categories. -/
abbrev plusToSmallEtaleDerived (S : B.Scheme) :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ S.obj) ⥤
      DerivedCategory (ModuleSheaf.{u, r, r} B S Λ) :=
  DerivedCategory.Plus.ι ⋙ (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategory

/-- A functor `M : D⁺(X_ét, Λ) ⥤ D⁺(S_ét, Λ)` on Mathlib's small étale sites, read on the small
étale sites of `B` and applied to bounded below complexes, is the composite of the transport of
complexes, `M` and the transport back. -/
def transportDerivedPlusIso
    (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ S.obj)) :
    DerivedCategory.Plus.Q ⋙ (moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlus ⋙
        M ⋙ (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus ⋙
          DerivedCategory.Plus.ι ≅
      (moduleSheafEquivEtaleModules B Λ X).functor.mapCochainComplexPlus ⋙
        (DerivedCategory.Plus.Q ⋙ M) ⋙ plusToSmallEtaleDerived Λ S :=
  Functor.isoWhiskerRight
    (Functor.plusQCompMapDerivedCategoryPlusIso (moduleSheafEquivEtaleModules B Λ X).functor)
    (M ⋙ (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus ⋙
      DerivedCategory.Plus.ι)

end Transport

section OpenClosed

variable {X S U A : B.Scheme} (f : X.obj ⟶ S.obj) [QuasiCompact f] (c : f.Compactification)
  (j : U.obj ⟶ X.obj) [IsOpenImmersion j] (i : A.obj ⟶ X.obj) [IsClosedImmersion i]

/-- `j⁻¹` followed by `Rg_!` on the small étale sites of `B` is `j⁻¹` followed by `Rg_!` on
Mathlib's small étale sites, across the equivalences of sheaf categories. -/
def derivedInverseImageCompDerivedLowerShriekIso {T : B.Scheme} (e : T.obj ⟶ X.obj)
    (c' : (e ≫ f).Compactification) :
    derivedInverseImage Λ e ⋙ derivedLowerShriek Λ (e ≫ f) c' ≅
      (moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlus ⋙
        (etaleModuleDerivedInverseImagePlus.{u, r} Λ e ⋙
          Stacks.EtaleCohomology.derivedLowerShriek.{u, r} (e ≫ f) c' Λ) ⋙
        (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus :=
  Functor.isoWhiskerLeft ((moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlus ⋙
      etaleModuleDerivedInverseImagePlus.{u, r} Λ e)
    (Functor.isoWhiskerRight (mapDerivedCategoryPlusInverseCompFunctorIso Λ T)
      (Stacks.EtaleCohomology.derivedLowerShriek.{u, r} (e ≫ f) c' Λ ⋙
        (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus) ≪≫
      Functor.leftUnitor _)

/-- The open-closed natural distinguished triangle for `Rf_!` on the small étale sites of `B`,
in Mathlib's sign convention. -/
theorem existsNatDistTriang_derivedLowerShriek_openClosed
    (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    ExistsNatDistTriang
      (DerivedCategory.Plus.Q ⋙ derivedInverseImage Λ j ⋙
        derivedLowerShriek Λ (j ≫ f) (c.restrictOpen j) ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.Q ⋙ derivedLowerShriek Λ f c ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.Q ⋙ derivedInverseImage Λ i ⋙
        derivedLowerShriek Λ (i ≫ f) (c.restrictClosed i) ⋙ DerivedCategory.Plus.ι) :=
  (((Stacks.EtaleCohomology.existsNatDistTriang_derivedLowerShriek_openClosed Λ i j c
      hij).map (plusToSmallEtaleDerived Λ S)).whiskerLeft
      (moduleSheafEquivEtaleModules B Λ X).functor.mapCochainComplexPlus).of_iso
    ((Functor.isoWhiskerLeft DerivedCategory.Plus.Q (Functor.isoWhiskerRight
        (derivedInverseImageCompDerivedLowerShriekIso Λ f j (c.restrictOpen j))
        DerivedCategory.Plus.ι) ≪≫
      transportDerivedPlusIso Λ (etaleModuleDerivedInverseImagePlus.{u, r} Λ j ⋙
          Stacks.EtaleCohomology.derivedLowerShriek.{u, r} (j ≫ f) (c.restrictOpen j) Λ)).symm)
    (transportDerivedPlusIso Λ (Stacks.EtaleCohomology.derivedLowerShriek.{u, r} f c Λ)).symm
    ((Functor.isoWhiskerLeft DerivedCategory.Plus.Q (Functor.isoWhiskerRight
        (derivedInverseImageCompDerivedLowerShriekIso Λ f i (c.restrictClosed i))
        DerivedCategory.Plus.ι) ≪≫
      transportDerivedPlusIso Λ (etaleModuleDerivedInverseImagePlus.{u, r} Λ i ⋙
          Stacks.EtaleCohomology.derivedLowerShriek.{u, r} (i ≫ f) (c.restrictClosed i) Λ)).symm)

/-- **The open-closed triangle for the derived direct image with proper support.** Let
`f : X ⟶ S` be compactifiable, with compactification `c`, let `j : U ⟶ X` be an open immersion
and `i : A ⟶ X` a closed immersion with complementary images. Then `f ∘ j` and `f ∘ i` are
compactifiable, and to each bounded below complex `K` of sheaves of `Λ`-modules on the small
étale site of `X` there is assigned, naturally in `K` for morphisms of complexes, an admissible
triangle
`R(f ∘ j)_!(j⁻¹ K) ⟶ Rf_! K ⟶ R(f ∘ i)_!(i⁻¹ K) ⟶ R(f ∘ j)_!(j⁻¹ K)[1]`
in the derived category of sheaves of `Λ`-modules on the small étale site of `S`. Here `Rf_!` is
computed with `c`, and `R(f ∘ j)_!` and `R(f ∘ i)_!` with the compactifications `c` induces. -/
@[weil "thm_fk108_proper_direct_image_distinguished_triangle"]
theorem exists_mem_admissibleTriangles_derivedLowerShriek_openClosed
    (hij : Set.range j.base = (Set.range i.base)ᶜ) :
    Nonempty (j ≫ f).Compactification ∧ Nonempty (i ≫ f).Compactification ∧
      ∃ (a : DerivedCategory.Plus.Q ⋙ derivedInverseImage Λ j ⋙
            derivedLowerShriek Λ (j ≫ f) (c.restrictOpen j) ⋙ DerivedCategory.Plus.ι ⟶
          DerivedCategory.Plus.Q ⋙ derivedLowerShriek Λ f c ⋙ DerivedCategory.Plus.ι)
        (b : DerivedCategory.Plus.Q ⋙ derivedLowerShriek Λ f c ⋙ DerivedCategory.Plus.ι ⟶
          DerivedCategory.Plus.Q ⋙ derivedInverseImage Λ i ⋙
            derivedLowerShriek Λ (i ≫ f) (c.restrictClosed i) ⋙ DerivedCategory.Plus.ι)
        (δ : DerivedCategory.Plus.Q ⋙ derivedInverseImage Λ i ⋙
            derivedLowerShriek Λ (i ≫ f) (c.restrictClosed i) ⋙ DerivedCategory.Plus.ι ⟶
          (DerivedCategory.Plus.Q ⋙ derivedInverseImage Λ j ⋙
            derivedLowerShriek Λ (j ≫ f) (c.restrictOpen j) ⋙ DerivedCategory.Plus.ι) ⋙
              shiftFunctor _ (1 : ℤ)),
        ∀ K, Triangle.mk (a.app K) (b.app K) (δ.app K) ∈
          DerivedCategory.admissibleTriangles (ModuleSheaf.{u, r, r} B S Λ) := by
  refine ⟨⟨c.restrictOpen j⟩, ⟨c.restrictClosed i⟩, ?_⟩
  obtain ⟨a, b, δ, hT⟩ := existsNatDistTriang_derivedLowerShriek_openClosed Λ f c j i hij
  refine ⟨a, b, -δ, fun K => ?_⟩
  rw [DerivedCategory.mem_admissibleTriangles_iff]
  simpa only [Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃, NatTrans.app_neg, neg_neg]
    using hT K

end OpenClosed

end AlgebraicGeometry.SmallEtale
