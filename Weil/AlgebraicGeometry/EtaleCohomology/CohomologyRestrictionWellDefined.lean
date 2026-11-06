module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Weil.Attr
public import Weil.CategoryTheory.Abelian.RightDerived
public import Weil.CategoryTheory.Sites.GlobalSections
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.RestrictionOnSections
public import Weil.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.PowerOfPair

/-!
# The restriction map on étale cohomology is independent of the restriction datum

Let `h : T ⟶ S` be a morphism of schemes and `F` an abelian sheaf on the small étale site of
`S`. A *restriction datum* for `(h, F)` consists of an injective resolution `F ⟶ I•`, an
injective resolution `h^* F ⟶ J•` and a cochain map `ρ : h^* I• ⟶ J•` over `𝟙 (h^* F)`. It
induces the restriction map `Hⁱ(Γ(S, I•)) ⟶ Hⁱ(Γ(T, J•))`, the homology of
`Γ(S, I•) ⟶ Γ(T, h^* I•) ⟶ Γ(T, J•)` (restriction of global sections followed by `Γ(T, ρ)`).
This file shows that the restriction maps of two restriction data agree under the canonical
identifications of the cohomology groups computed by different injective resolutions.

The argument is abstract. For an exact functor `L : C ⥤ D` of abelian categories, additive
functors `Γ_X : C ⥤ E`, `Γ_Y : D ⥤ E` and any natural transformation `r : Γ_X ⟶ Γ_Y ∘ L`, let
`α : I ⟶ I'` and `β : J ⟶ J'` be comparison maps of the resolutions. The cochain maps
`ρ ≫ β` and `L(α) ≫ ρ'` from `L(I)` to `J'` both lie over `𝟙 (L F)`; since `L(I)` is a
resolution of `L(F)` (as `L` is exact) and `J'` is a complex of injectives, they are homotopic.
Naturality of `r` and additivity of `Γ_Y` then give the equality on cohomology.

## Main definitions

* `CochainComplex.homotopyOfExactOfInjective`: two cochain maps from an exact augmented complex
  `A ⟶ K⁰ ⟶ K¹ ⟶ ⋯` to a complex of injectives that agree on `A` are homotopic.
* `CategoryTheory.InjectiveResolution.restrictionHomologyMap`: the restriction map
  `Hⁿ(Γ_X(I)) ⟶ Hⁿ(Γ_Y(J))` of a restriction datum `(I, J, ρ)`.
* `AlgebraicGeometry.smallEtaleRestrictionOnGlobalSectionsNatTrans`: restriction of global
  sections `Γ(S, -) ⟶ Γ(T, h^* -)` as a natural transformation.

## Main results

* `CategoryTheory.InjectiveResolution.restrictionHomologyMap_comp_homologyIso_hom`: the
  abstract independence statement.
* `AlgebraicGeometry.smallEtaleRestrictionHomologyMap_comp_homologyIso_hom`: the restriction map
  on étale cohomology does not depend on the restriction datum.

## Implementation notes

The homotopy `CochainComplex.homotopyOfExactOfInjective` is the construction of
`CategoryTheory.InjectiveResolution.descHomotopy`, which needs injectivity only of the target;
the source here is `h^* I•`, which is exact but in general not injective.

The statement holds for every natural transformation `r : Γ(S, -) ⟶ Γ(T, h^* -)`; the étale
form uses restriction of global sections `smallEtaleRestrictionOnGlobalSections`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
* [C. Weibel, *An introduction to homological algebra*, 2.3.7][Weibel]
-/

@[expose] public noncomputable section

universe v u v' u' v'' u''

open CategoryTheory Category Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

section HomotopyZero

variable {A : C} {K L : CochainComplex C ℕ} [∀ n, Injective (L.X n)]
  (e : A ⟶ K.X 0) (he : e ≫ K.d 0 1 = 0)
  (hK₀ : (ShortComplex.mk e (K.d 0 1) he).Exact)
  (hK : ∀ n, (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2)) (K.d_comp_d _ _ _)).Exact)
  (f : K ⟶ L) (comm : e ≫ f.f 0 = 0)

/-- Degree-zero component of `homotopyZeroOfExactOfInjective`. -/
def homotopyZeroOfExactOfInjectiveZero : K.X 1 ⟶ L.X 0 :=
  hK₀.descToInjective (f.f 0) comm

include hK₀ in
@[reassoc (attr := simp)]
lemma d_comp_homotopyZeroOfExactOfInjectiveZero :
    K.d 0 1 ≫ homotopyZeroOfExactOfInjectiveZero e he hK₀ f comm = f.f 0 :=
  hK₀.comp_descToInjective _ _

/-- Degree-one component of `homotopyZeroOfExactOfInjective`. -/
def homotopyZeroOfExactOfInjectiveOne : K.X 2 ⟶ L.X 1 :=
  (hK 0).descToInjective (f.f 1 - homotopyZeroOfExactOfInjectiveZero e he hK₀ f comm ≫ L.d 0 1)
    (by
      dsimp
      rw [Preadditive.comp_sub, d_comp_homotopyZeroOfExactOfInjectiveZero_assoc,
        HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
lemma d_comp_homotopyZeroOfExactOfInjectiveOne :
    K.d 1 2 ≫ homotopyZeroOfExactOfInjectiveOne e he hK₀ hK f comm =
      f.f 1 - homotopyZeroOfExactOfInjectiveZero e he hK₀ f comm ≫ L.d 0 1 :=
  (hK 0).comp_descToInjective _ _

/-- Inductive step of `homotopyZeroOfExactOfInjective`. -/
def homotopyZeroOfExactOfInjectiveSucc (n : ℕ)
    (g : K.X (n + 1) ⟶ L.X n) (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : f.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.X (n + 3) ⟶ L.X (n + 2) :=
  (hK (n + 1)).descToInjective (f.f (n + 2) - g' ≫ L.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
        Category.assoc, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
        add_zero, sub_self])

@[reassoc (attr := simp)]
lemma d_comp_homotopyZeroOfExactOfInjectiveSucc (n : ℕ)
    (g : K.X (n + 1) ⟶ L.X n) (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : f.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.d (n + 2) (n + 3) ≫ homotopyZeroOfExactOfInjectiveSucc hK f n g g' w =
      f.f (n + 2) - g' ≫ L.d _ _ :=
  (hK (n + 1)).comp_descToInjective _ _

/-- Let `A ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be exact and let `L` be a cochain complex of injective objects. A
morphism of complexes `f : K ⟶ L` that vanishes on `A` is homotopic to zero. -/
def homotopyZeroOfExactOfInjective : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroOfExactOfInjectiveZero e he hK₀ f comm) (by simp)
    (homotopyZeroOfExactOfInjectiveOne e he hK₀ hK f comm) (by simp) (fun n ⟨g, g', w⟩ =>
    ⟨homotopyZeroOfExactOfInjectiveSucc hK f n g g' (by simp only [w, add_comm]), by simp⟩)

/-- Let `A ⟶ K⁰ ⟶ K¹ ⟶ ⋯` be exact and let `L` be a cochain complex of injective objects. Two
morphisms of complexes `K ⟶ L` that agree on `A` are homotopic. -/
def homotopyOfExactOfInjective (f g : K ⟶ L) (h : e ≫ f.f 0 = e ≫ g.f 0) : Homotopy f g :=
  Homotopy.equivSubZero.symm
    (homotopyZeroOfExactOfInjective e he hK₀ hK (f - g) (by simp [h]))

end HomotopyZero

end CochainComplex

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]
  {L : C ⥤ D} [L.Additive] {ΓX : C ⥤ E} [ΓX.Additive] {ΓY : D ⥤ E} [ΓY.Additive]
  (r : ΓX ⟶ L ⋙ ΓY)

/-- The cochain map `Γ_X(I) ⟶ Γ_Y(J)` of a restriction datum `(I, J, ρ)`: restriction
`r : Γ_X ⟶ Γ_Y ∘ L` on `I`, followed by `Γ_Y(ρ)` for `ρ : L(I) ⟶ J`. -/
def restrictionCochainMap {F : C} (I : InjectiveResolution F) (J : InjectiveResolution (L.obj F))
    (ρ : (L.mapHomologicalComplex _).obj I.cocomplex ⟶ J.cocomplex) :
    (ΓX.mapHomologicalComplex _).obj I.cocomplex ⟶ (ΓY.mapHomologicalComplex _).obj J.cocomplex :=
  (NatTrans.mapHomologicalComplex r _).app I.cocomplex ≫ (ΓY.mapHomologicalComplex _).map ρ

/-- The restriction map `Hⁿ(Γ_X(I)) ⟶ Hⁿ(Γ_Y(J))` of a restriction datum `(I, J, ρ)`. -/
def restrictionHomologyMap {F : C} (I : InjectiveResolution F)
    (J : InjectiveResolution (L.obj F))
    (ρ : (L.mapHomologicalComplex _).obj I.cocomplex ⟶ J.cocomplex) (n : ℕ) :
    ((ΓX.mapHomologicalComplex _).obj I.cocomplex).homology n ⟶
      ((ΓY.mapHomologicalComplex _).obj J.cocomplex).homology n :=
  HomologicalComplex.homologyMap (restrictionCochainMap r I J ρ) n

variable [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- For an exact functor `L` and two restriction data `(I, J, ρ)`, `(I', J', ρ')` of the same
object, the cochain maps `ρ ≫ β` and `L(α) ≫ ρ'` from `L(I)` to `J'` are homotopic, where
`α : I ⟶ I'` and `β : J ⟶ J'` are the comparison maps of the resolutions. -/
def restrictionComparisonHomotopy {F : C} (I I' : InjectiveResolution F)
    (J J' : InjectiveResolution (L.obj F))
    (ρ : (L.mapHomologicalComplex _).obj I.cocomplex ⟶ J.cocomplex)
    (ρ' : (L.mapHomologicalComplex _).obj I'.cocomplex ⟶ J'.cocomplex)
    (hρ : L.map (I.ι.f 0) ≫ ρ.f 0 = J.ι.f 0) (hρ' : L.map (I'.ι.f 0) ≫ ρ'.f 0 = J'.ι.f 0) :
    Homotopy (ρ ≫ desc (𝟙 (L.obj F)) J' J)
      ((L.mapHomologicalComplex _).map (desc (𝟙 F) I' I) ≫ ρ') :=
  CochainComplex.homotopyOfExactOfInjective (L.map (I.ι.f 0))
    (by
      change L.map (I.ι.f 0) ≫ L.map (I.cocomplex.d 0 1) = 0
      rw [← L.map_comp, I.ι_f_zero_comp_complex_d, L.map_zero])
    (I.exact₀.map L) (fun n => (I.exact_succ n).map L) _ _ (by
      dsimp
      have h1 := congrArg (· ≫ (desc (𝟙 (L.obj F)) J' J).f 0) hρ
      have h2 : I.ι.f 0 ≫ (desc (𝟙 F) I' I).f 0 = I'.ι.f 0 := by
        rw [desc_commutes_zero]
        exact id_comp _
      have h3 := congrArg (fun x => L.map x ≫ ρ'.f 0) h2
      simp only [Category.assoc, L.map_comp] at h1 h3
      erw [h1, h3, hρ', desc_commutes_zero, id_comp])

/-- **The restriction map is independent of the restriction datum.** Let `L : C ⥤ D` be an exact
functor, `r : Γ_X ⟶ Γ_Y ∘ L` a natural transformation of additive functors and `F : C`. For two
restriction data `(I, J, ρ)` and `(I', J', ρ')` of `F` (injective resolutions `I, I'` of `F`,
`J, J'` of `L(F)`, and cochain maps `ρ : L(I) ⟶ J`, `ρ' : L(I') ⟶ J'` over `𝟙 (L F)`), the two
restriction maps `Hⁿ(Γ_X(I)) ⟶ Hⁿ(Γ_Y(J))` and `Hⁿ(Γ_X(I')) ⟶ Hⁿ(Γ_Y(J'))` agree under the
canonical identifications `homologyIso`. -/
theorem restrictionHomologyMap_comp_homologyIso_hom {F : C} (I I' : InjectiveResolution F)
    (J J' : InjectiveResolution (L.obj F))
    (ρ : (L.mapHomologicalComplex _).obj I.cocomplex ⟶ J.cocomplex)
    (ρ' : (L.mapHomologicalComplex _).obj I'.cocomplex ⟶ J'.cocomplex)
    (hρ : L.map (I.ι.f 0) ≫ ρ.f 0 = J.ι.f 0) (hρ' : L.map (I'.ι.f 0) ≫ ρ'.f 0 = J'.ι.f 0)
    (n : ℕ) :
    restrictionHomologyMap r I J ρ n ≫ (homologyIso ΓY J J' n).hom =
      (homologyIso ΓX I I' n).hom ≫ restrictionHomologyMap r I' J' ρ' n := by
  simp only [restrictionHomologyMap, homologyIso_hom, homologyMapOfHom,
    ← HomologicalComplex.homologyMap_comp]
  have e₁ : restrictionCochainMap r I J ρ ≫
        (ΓY.mapHomologicalComplex _).map (desc (𝟙 (L.obj F)) J' J) =
      (NatTrans.mapHomologicalComplex r _).app I.cocomplex ≫
        (ΓY.mapHomologicalComplex _).map (ρ ≫ desc (𝟙 (L.obj F)) J' J) := by
    rw [restrictionCochainMap, Functor.map_comp, Category.assoc]
  have e₂ : (ΓX.mapHomologicalComplex _).map (desc (𝟙 F) I' I) ≫
        restrictionCochainMap r I' J' ρ' =
      (NatTrans.mapHomologicalComplex r _).app I.cocomplex ≫
        (ΓY.mapHomologicalComplex _).map
          ((L.mapHomologicalComplex _).map (desc (𝟙 F) I' I) ≫ ρ') := by
    ext k
    simp [restrictionCochainMap, ← Functor.map_comp]
  rw [e₁, e₂]
  exact Homotopy.homologyMap_eq
    ((ΓY.mapHomotopy (restrictionComparisonHomotopy I I' J J' ρ ρ' hρ hρ')).compLeft _) n

end CategoryTheory.InjectiveResolution

namespace AlgebraicGeometry

open CategoryTheory Opposite

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (h : T ⟶ S)

/-- The restriction of global sections `r^h_G : G(S) ⟶ (h^* G)(T)`, as a natural transformation
`Γ(S, -) ⟶ Γ(T, h^* -)` of functors on abelian sheaves on the small étale site of `S`. -/
def smallEtaleRestrictionOnGlobalSectionsNatTrans :
    SmallEtale.globalSections.{u + 1} B S.obj S.property ⟶
      smallEtaleInverseImage B h AddCommGrpCat.{u + 1} ⋙
        SmallEtale.globalSections.{u + 1} B T.obj T.property where
  app G := smallEtaleRestrictionOnGlobalSections B h AddCommGrpCat.{u + 1} G
  naturality G G' φ := by
    have key := congrArg (fun ψ => ψ.hom.app (op (SmallEtale.final B S.obj S.property)))
      ((smallEtaleInverseImageAdjunction B h AddCommGrpCat.{u + 1}).unit.naturality φ)
    dsimp at key ⊢
    simp only [smallEtaleRestrictionOnGlobalSections, smallEtaleRestrictionOnSections]
    refine (Category.assoc _ _ _).symm.trans ((key =≫ _).trans ?_)
    refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).symm.trans ?_)
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (_ ≫ ·)
      (((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map φ).hom.naturality _).symm

/-- **The restriction map on étale cohomology is well defined.** Let `h : T ⟶ S` be a morphism
of schemes of a big étale site and `F` an abelian sheaf on the small étale site of `S`. For two
restriction data `(I, J, ρ)` and `(I', J', ρ')` of `(h, F)` — injective resolutions `I, I'` of `F`
and `J, J'` of `h^* F`, and cochain maps `ρ : h^* I ⟶ J`, `ρ' : h^* I' ⟶ J'` over `𝟙 (h^* F)` —
the two restriction maps `Hⁱ(Γ(S, I)) ⟶ Hⁱ(Γ(T, J))` and `Hⁱ(Γ(S, I')) ⟶ Hⁱ(Γ(T, J'))` agree
under the canonical identifications `Hⁱ(Γ(S, I)) ≅ Hⁱ(Γ(S, I'))` and
`Hⁱ(Γ(T, J)) ≅ Hⁱ(Γ(T, J'))` induced by comparison maps of the resolutions. -/
@[weil "lem_fk106_cohomology_restriction_well_defined"]
theorem smallEtaleRestrictionHomologyMap_comp_homologyIso_hom
    (F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1})
    (I I' : InjectiveResolution F)
    (J J' : InjectiveResolution ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj F))
    (ρ : ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).mapHomologicalComplex _).obj
      I.cocomplex ⟶ J.cocomplex)
    (ρ' : ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).mapHomologicalComplex _).obj
      I'.cocomplex ⟶ J'.cocomplex)
    (hρ : (smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map (I.ι.f 0) ≫ ρ.f 0 = J.ι.f 0)
    (hρ' : (smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map (I'.ι.f 0) ≫ ρ'.f 0 =
      J'.ι.f 0) (i : ℕ) :
    InjectiveResolution.restrictionHomologyMap (smallEtaleRestrictionOnGlobalSectionsNatTrans B h)
        I J ρ i ≫
        (InjectiveResolution.homologyIso (SmallEtale.globalSections.{u + 1} B T.obj T.property)
          J J' i).hom =
      (InjectiveResolution.homologyIso (SmallEtale.globalSections.{u + 1} B S.obj S.property)
          I I' i).hom ≫
        InjectiveResolution.restrictionHomologyMap
          (smallEtaleRestrictionOnGlobalSectionsNatTrans B h) I' J' ρ' i :=
  InjectiveResolution.restrictionHomologyMap_comp_homologyIso_hom _ I I' J J' ρ ρ' hρ hρ' i

end AlgebraicGeometry
