module

public import Weil.AlgebraicGeometry.ComplexPoints.EtaleSections
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# The analytic inverse image of étale sheaves

Let `Y` be a scheme locally of finite type over `ℂ`, and `Y(ℂ)` its complex points with the
analytic topology. For an abelian sheaf `G` on `Y(ℂ)`, the presheaf
`U ↦ Hom(ℤ[Φ U], G)` on the small étale site of `Y`, where `Φ U` is the sheaf of continuous
sections of `U(ℂ) → Y(ℂ)`, is an étale sheaf `ε_* G`: the sections of `G` pulled back to `U(ℂ)`.
This is the direct image along the morphism of sites `ε : Y(ℂ) → Y_et`. It preserves limits, so
it has a left adjoint `ε^*`, the analytic inverse image `F ↦ F_an`.

The stalk of `ε^* F` at a complex point `p` is the stalk of `F` at the geometric point `p`:
both fibre functors are left adjoint to skyscraper sheaves, and `ε_*` of the skyscraper sheaf at
`p` is the étale skyscraper sheaf at `p`, because the stalk of `ℤ[Φ U]` at `p` is the free abelian
group on the fibre of `U` over `p`. Since stalks at the points of `Y(ℂ)` detect isomorphisms and
étale stalks are exact, `ε^*` is exact. Since `ε_*` commutes with global sections, `ε^*` sends
constant sheaves to constant sheaves.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.analyticDirectImage`: `ε_*`, from abelian sheaves on
  `Y(ℂ)` to abelian sheaves on the small étale site of `Y`.
* `AlgebraicGeometry.Scheme.ComplexPoints.analyticInverseImage`: `ε^*`, its left adjoint, with
  the adjunction `analyticAdjunction`.
* `AlgebraicGeometry.Scheme.ComplexPoints.anPoint`, `etPoint`: the point of `Y(ℂ)` and the
  geometric point of `Y` given by a complex point.
* `AlgebraicGeometry.Scheme.ComplexPoints.etaleTop`: the final object `Y → Y` of the étale site.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.skyscraperIso`: `ε_*` of the skyscraper sheaf at `p`
  is the étale skyscraper sheaf at `p`.
* `AlgebraicGeometry.Scheme.ComplexPoints.stalkIso`: the stalk formula `(ε^* F)_p ≅ F_p`,
  natural in `F`.
* `AlgebraicGeometry.Scheme.ComplexPoints.globalSectionsIso`: `Γ(Y_et, ε_* G) ≅ Γ(Y(ℂ), G)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.constantSheafIso`: `ε^*` of the constant sheaf `M` is
  the constant sheaf `M`, naturally in `M`.
* `ε^*` is additive and preserves finite limits and finite colimits (instances).

## Implementation notes

The complex points are lifted to `Type 1`, so that abelian sheaves on `Y(ℂ)` and on the small
étale site of the universe-`0` scheme `Y` both take values in `AddCommGrpCat.{1}`. The inverse
image is obtained from the special adjoint functor theorem rather than as a sheafified colimit;
its stalks, its value on constant sheaves and its exactness then follow from uniqueness of left
adjoints, through the two isomorphisms of right adjoints `skyscraperIso` and `globalSectionsIso`.

## References

* [SGA 4, Exposé XI, §4]
* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11]
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ))

set_option hygiene false in
/-- The complex points of `Y`, lifted to `TopCat.{1}`. -/
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

set_option hygiene false in
/-- The site of open subsets of `Y(ℂ)`. -/
local notation "𝔍" => _root_.Opens.grothendieckTopology 𝔛

variable [LocallyOfFiniteType y]

/-- The direct image `ε_*` of abelian sheaves on `Y(ℂ)` to the small étale site of `Y`:
`(ε_* G)(U) = Hom(ℤ[Φ U], G)`, the sections of `G` pulled back to `U(ℂ)`. -/
noncomputable def analyticDirectImage :
    Sheaf (𝔍) AddCommGrpCat.{1} ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{1} where
  obj G := ⟨analyticDirectImagePresheaf y G, isSheaf_analyticDirectImagePresheaf y G⟩
  map φ := ⟨Functor.whiskerLeft (freeSectionsFunctor y).op (preadditiveYoneda.map φ)⟩

/-- Sectionwise, `ε_*` is the functor `Hom(ℤ[Φ U], -)`. -/
noncomputable def analyticDirectImageEvaluationIso (U : Y.Etale) :
    (analyticDirectImage y ⋙ sheafToPresheaf _ _) ⋙
        (CategoryTheory.evaluation Y.Etaleᵒᵖ AddCommGrpCat.{1}).obj (op U) ≅
      preadditiveCoyoneda.obj (op ((freeSectionsFunctor y).obj U)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

instance preservesLimitsOfSize_analyticDirectImage :
    PreservesLimitsOfSize.{1, 1} (analyticDirectImage y) := by
  have : PreservesLimitsOfSize.{1, 1} (analyticDirectImage y ⋙ sheafToPresheaf _ _) := by
    refine ⟨⟨fun {K} => ?_⟩⟩
    apply preservesLimit_of_evaluation
    intro U
    have := preservesLimits_of_natIso (analyticDirectImageEvaluationIso y U.unop).symm
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

instance isRightAdjoint_analyticDirectImage : (analyticDirectImage y).IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating
    (isCoseparator_coseparator (Sheaf (𝔍) AddCommGrpCat.{1})) _

/-- The analytic inverse image `ε^*` of étale abelian sheaves on `Y` to abelian sheaves on
`Y(ℂ)`: the left adjoint of `ε_*`. -/
noncomputable def analyticInverseImage :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{1} ⥤ Sheaf (𝔍) AddCommGrpCat.{1} :=
  (analyticDirectImage y).leftAdjoint

/-- The adjunction `ε^* ⊣ ε_*`. -/
noncomputable def analyticAdjunction : analyticInverseImage y ⊣ analyticDirectImage y :=
  Adjunction.ofIsRightAdjoint _

/-! ### Global sections -/

/-- The final object `Y → Y` of the small étale site of `Y`. -/
abbrev etaleTop (Y : Scheme.{0}) : Y.Etale := MorphismProperty.Over.mk ⊤ (𝟙 Y) inferInstance

theorem isTerminal_etaleTop (Y : Scheme.{0}) : Nonempty (IsTerminal (etaleTop Y)) :=
  have : MorphismProperty.ContainsIdentities (@AlgebraicGeometry.Etale.{0}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  ⟨MorphismProperty.Over.mkIdTerminal (@AlgebraicGeometry.Etale) Y⟩

omit [LocallyOfFiniteType y] in
/-- The complex point of `Y → Y` above a complex point of `Y`. -/
noncomputable def etaleTopPoint : ComplexPoints y → ComplexPoints ((etaleTop Y).hom ≫ y) :=
  map (𝟙 Y) (by change 𝟙 Y ≫ 𝟙 Y ≫ y = y; simp)

omit [LocallyOfFiniteType y] in
theorem etaleMap_etaleTopPoint (p : ComplexPoints y) :
    etaleMap y (etaleTop Y) (etaleTopPoint y p) = p :=
  ext (by change (p.hom ≫ 𝟙 Y) ≫ 𝟙 Y = p.hom; simp)

omit [LocallyOfFiniteType y] in
theorem etaleTopPoint_etaleMap (q : ComplexPoints ((etaleTop Y).hom ≫ y)) :
    etaleTopPoint y (etaleMap y (etaleTop Y) q) = q :=
  ext (by
    change (q.hom ≫ 𝟙 Y) ≫ 𝟙 Y = q.hom
    exact (Category.comp_id _).trans (Category.comp_id _))

omit [LocallyOfFiniteType y] in
/-- `Y → Y` has exactly one section over every open of `Y(ℂ)`. -/
noncomputable instance uniqueSectionsPresheafEtaleTop (V : (TopologicalSpace.Opens 𝔛)ᵒᵖ) :
    Unique ((sectionsPresheaf y (etaleTop Y)).obj V) where
  default := ⟨fun v => ULift.up (etaleTopPoint y v.1.down),
    continuous_uliftUp.comp ((continuous_map _ _).comp
      (continuous_uliftDown.comp continuous_subtype_val)),
    fun v => etaleMap_etaleTopPoint y _⟩
  uniq σ := Subtype.ext (funext fun v => ULift.ext _ _ (by
    change (σ.1 v).down = etaleTopPoint y v.1.down
    rw [← σ.2.2 v, etaleTopPoint_etaleMap]))

omit [LocallyOfFiniteType y] in
/-- The sheaf of sections of `Y → Y` is the terminal presheaf. -/
noncomputable def sectionsPresheafEtaleTopIso :
    sectionsPresheaf y (etaleTop Y) ≅ (Functor.const _).obj PUnit.{2} :=
  NatIso.ofComponents (fun V => Equiv.toIso
    (Equiv.ofUnique ((sectionsPresheaf y (etaleTop Y)).obj V) PUnit.{2})) (fun _ => rfl)

omit [LocallyOfFiniteType y] in
/-- `ℤ[Φ (Y → Y)]` is the constant sheaf `ℤ`. -/
noncomputable def freeSectionsEtaleTopIso :
    (freeSectionsFunctor y).obj (etaleTop Y) ≅
      (constantSheaf (𝔍) AddCommGrpCat.{1}).obj (AddCommGrpCat.free.obj PUnit.{2}) :=
  (presheafToSheaf (𝔍) AddCommGrpCat.{1}).mapIso
    (Functor.isoWhiskerRight (sectionsPresheafEtaleTopIso y) AddCommGrpCat.free ≪≫
      Functor.constComp _ _ _)

end AlgebraicGeometry.Scheme.ComplexPoints

universe u v

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {C D : Type*} [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive]

/-- For an adjunction `F ⊣ G` of additive functors, `Hom(F X, -) ≅ Hom(X, G -)` as functors to
abelian groups. -/
noncomputable def preadditiveCoyonedaObjIsoOfAdjunction (X : C) :
    preadditiveCoyoneda.obj (Opposite.op (F.obj X)) ≅
      G ⋙ preadditiveCoyoneda.obj (Opposite.op X) :=
  NatIso.ofComponents (fun Z => (adj.homAddEquiv X Z).toAddCommGrpIso) (fun g => by
    ext f
    exact adj.homEquiv_naturality_right f g)

/-- For an adjunction `F ⊣ G` of additive functors between preadditive categories with homs in
the same universe, `Hom(-, G Z) ≅ Hom(F -, Z)`, naturally in `Z`. -/
noncomputable def compPreadditiveYonedaIsoOfAdjunction :
    G ⋙ preadditiveYoneda ≅ preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op :=
  NatIso.ofComponents
    (fun Z => NatIso.ofComponents
      (fun X => (adj.homAddEquiv (Opposite.unop X) Z).symm.toAddCommGrpIso)
      (fun g => by
        ext y
        exact adj.homEquiv_naturality_left_symm g.unop y))
    (fun f => by
      ext _ x
      exact adj.homEquiv_naturality_right_symm x f)

end AlgebraicGeometry.Scheme.ComplexPoints

namespace AddCommGrpCat

/-- `Hom(ℤ[*], B) ≅ B`, naturally in the abelian group `B`. -/
noncomputable def preadditiveCoyonedaObjFreePUnitIso :
    preadditiveCoyoneda.obj (op (AddCommGrpCat.free.obj PUnit.{u + 1})) ≅ 𝟭 AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun B => (AddCommGrpCat.homAddEquiv.trans
      (FreeAbelianGroup.liftAddEquiv.symm.trans (AddEquiv.piUnique _))).toAddCommGrpIso)
    (fun g => by
      ext f
      rfl)

section FreeHom

variable (S : Type) (A : AddCommGrpCat.{1})

/-- Evaluation at the generator `s` of a homomorphism out of the free abelian group on `S`. -/
def freeHomEval (s : S) : of (free.obj (ULift.{1} S) ⟶ A) ⟶ A :=
  ofHom { toFun φ := φ (FreeAbelianGroup.of (ULift.up s)), map_zero' := rfl, map_add' _ _ := rfl }

@[simp]
theorem freeHomEval_apply (s : S) (φ : free.obj (ULift.{1} S) ⟶ A) :
    freeHomEval S A s φ = φ (FreeAbelianGroup.of (ULift.up s)) := rfl

/-- `Hom(ℤ[S], A)` with the evaluations at the generators is a product of copies of `A`. -/
def freeHomFan : Fan fun _ : S => A :=
  Fan.mk (of (free.obj (ULift.{1} S) ⟶ A)) (freeHomEval S A)

/-- The map to `Hom(ℤ[S], A)` given by a family of maps to `A` indexed by `S`. -/
def freeHomLift {B : AddCommGrpCat.{1}} (g : S → (B ⟶ A)) : B ⟶ of (free.obj (ULift.{1} S) ⟶ A) :=
  ofHom (homAddEquiv.symm.toAddMonoidHom.comp (FreeAbelianGroup.liftAddEquiv.toAddMonoidHom.comp
    (AddMonoidHom.pi fun u : ULift.{1} S => (g u.down).hom)))

theorem freeHomLift_apply {B : AddCommGrpCat.{1}} (g : S → (B ⟶ A)) (b : B) (u : ULift.{1} S) :
    freeHomLift S A g b (FreeAbelianGroup.of u) = g u.down b :=
  FreeAbelianGroup.lift_apply_of _ _

/-- `Hom(ℤ[S], A)` is the product of copies of `A` indexed by `S`. -/
def isLimitFreeHomFan : IsLimit (freeHomFan S A) :=
  Fan.IsLimit.mk _ (fun c => freeHomLift S A c.proj)
    (fun c s => by
      ext b
      exact freeHomLift_apply S A c.proj b ⟨s⟩)
    (fun c m hm => by
      ext b : 2
      refine AddCommGrpCat.Hom.ext (FreeAbelianGroup.lift_ext _ _ fun u => ?_)
      exact (ConcreteCategory.congr_hom (hm u.down) b).trans
        (freeHomLift_apply S A c.proj b u).symm)

/-- `Hom(ℤ[S], A) ≅ ∏_S A`. -/
noncomputable def freeHomIsoPi : of (free.obj (ULift.{1} S) ⟶ A) ≅ ∏ᶜ fun _ : S => A :=
  (isLimitFreeHomFan S A).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
theorem freeHomIsoPi_hom_π (s : S) :
    (freeHomIsoPi S A).hom ≫ Pi.π _ s = freeHomEval S A s :=
  (isLimitFreeHomFan S A).conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨s⟩

end FreeHom

end AddCommGrpCat

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

set_option hygiene false in
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

set_option hygiene false in
local notation "𝔍" => _root_.Opens.grothendieckTopology 𝔛

/-- `Γ_et ∘ ε_* ≅ Γ_an`: the étale global sections of `ε_* G` are the sections of `G` over
`Y(ℂ)`. -/
noncomputable def globalSectionsIso :
    analyticDirectImage y ⋙ (sheafSections Y.smallEtaleTopology AddCommGrpCat.{1}).obj
        (op (etaleTop Y)) ≅
      (sheafSections (𝔍) AddCommGrpCat.{1}).obj (op ⊤) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) ≪≫
    preadditiveCoyoneda.mapIso (freeSectionsEtaleTopIso y).op.symm ≪≫
    preadditiveCoyonedaObjIsoOfAdjunction
      (constantSheafAdj (𝔍) AddCommGrpCat.{1} isTerminalTop) _ ≪≫
    Functor.isoWhiskerLeft _ AddCommGrpCat.preadditiveCoyonedaObjFreePUnitIso ≪≫
    Functor.rightUnitor _

/-- `ε^*(constant M) ≅ constant M`, naturally in `M`. -/
noncomputable def constantSheafIso :
    constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1} ⋙ analyticInverseImage y ≅
      constantSheaf (𝔍) AddCommGrpCat.{1} :=
  Adjunction.leftAdjointUniq
    ((constantSheafAdj _ _ (isTerminal_etaleTop Y).some).comp (analyticAdjunction y))
    ((constantSheafAdj _ _ isTerminalTop).ofNatIsoRight (globalSectionsIso y).symm)

/-! ### Stalks -/

omit [LocallyOfFiniteType y] in
/-- The point of the site of open subsets of `Y(ℂ)` given by a complex point `p`. -/
abbrev anPoint (p : ComplexPoints y) :=
  _root_.Opens.pointGrothendieckTopology (X := 𝔛) (ULift.up p)

omit [LocallyOfFiniteType y] in
/-- The geometric point of the small étale site of `Y` given by a complex point `p`. -/
noncomputable abbrev etPoint (p : ComplexPoints y) := Scheme.pointSmallEtale p.hom

/-- The stalk at `p` of the sheaf of sections of `U(ℂ) → Y(ℂ)` is the fibre of `U` at the
geometric point `p`, naturally in `U`. -/
noncomputable def sectionsFunctorCompSheafFiberIso (p : ComplexPoints y) :
    sectionsFunctor y ⋙ (anPoint y p).sheafFiber (A := Type 1) ≅
      (etPoint y p).fiber ⋙ uliftFunctor.{1, 0} :=
  NatIso.ofComponents (fun U => (sectionsFiberEquiv y p U).toIso) (fun f => by
    ext z
    exact sectionsFiberEquiv_naturality y p f z)

/-- The stalk at `p` of `ℤ[Φ U]` is the free abelian group on the fibre of `U` at the geometric
point `p`, naturally in `U`. -/
noncomputable def freeSectionsFunctorCompSheafFiberIso (p : ComplexPoints y) :
    freeSectionsFunctor y ⋙ (anPoint y p).sheafFiber (A := AddCommGrpCat.{1}) ≅
      (etPoint y p).fiber ⋙ uliftFunctor.{1, 0} ⋙ AddCommGrpCat.free.{1} :=
  Functor.isoWhiskerLeft (sectionsFunctor y ⋙ sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free.{1})
      ((anPoint y p).presheafToSheafCompSheafFiberIso AddCommGrpCat.{1}) ≪≫
    Functor.isoWhiskerLeft (sectionsFunctor y ⋙ sheafToPresheaf _ _)
      ((anPoint y p).presheafFiberCompIso AddCommGrpCat.free.{1}) ≪≫
    Functor.isoWhiskerRight (sectionsFunctorCompSheafFiberIso y p) AddCommGrpCat.free.{1}

/-- Filtered colimits indexed by small categories in universe `0` are exact in
`AddCommGrpCat.{1}`. -/
instance ab5OfSize_zero_addCommGrpCat : AB5OfSize.{0, 0} AddCommGrpCat.{1} :=
  AB5OfSize_shrink.{0, 0, 1, 1} _

instance additive_sheafFiber_anPoint (p : ComplexPoints y) :
    ((anPoint y p).sheafFiber (A := AddCommGrpCat.{1})).Additive :=
  Functor.additive_of_preserves_binary_products _

omit [LocallyOfFiniteType y] in
set_option backward.isDefEq.respectTransparency false in
/-- The étale skyscraper presheaf at `p` is `U ↦ Hom(ℤ[fibre of U at p], -)`. -/
noncomputable def skyscraperPresheafFunctorIso (p : ComplexPoints y) :
    preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj
        ((etPoint y p).fiber ⋙ uliftFunctor.{1, 0} ⋙ AddCommGrpCat.free.{1}).op ≅
      (etPoint y p).skyscraperPresheafFunctor (A := AddCommGrpCat.{1}) :=
  NatIso.ofComponents
    (fun A => NatIso.ofComponents
      (fun U => AddCommGrpCat.freeHomIsoPi ((etPoint y p).fiber.obj U.unop) A)
      (fun {U V} f => by
        refine Pi.hom_ext _ _ fun s => ?_
        ext φ
        simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.op_obj,
          Functor.comp_map, Functor.op_map, uliftFunctor_map, AddCommGrpCat.free_map,
          TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Category.assoc, AddCommGrpCat.freeHomIsoPi_hom_π,
          AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
          GrothendieckTopology.Point.skyscraperPresheafFunctor_obj_map, Pi.map'_comp_π,
          Category.comp_id]
        exact congrArg φ.hom (FreeAbelianGroup.lift_apply_of _ _)))
    (fun {A B} g => by
      refine NatTrans.ext (funext fun U => Pi.hom_ext _ _ fun s => ?_)
      ext φ
      simp
      rfl)

/-- `ε_*` of the skyscraper sheaf at `p` is the étale skyscraper sheaf at the geometric point
`p`. -/
noncomputable def skyscraperIso (p : ComplexPoints y) :
    (anPoint y p).skyscraperSheafFunctor (A := AddCommGrpCat.{1}) ⋙ analyticDirectImage y ≅
      (etPoint y p).skyscraperSheafFunctor (A := AddCommGrpCat.{1}) :=
  ((fullyFaithfulSheafToPresheaf _ _).whiskeringRight _).preimageIso
    (Functor.isoWhiskerRight
        (compPreadditiveYonedaIsoOfAdjunction
          ((anPoint y p).skyscraperSheafAdjunction (A := AddCommGrpCat.{1})))
        ((Functor.whiskeringLeft _ _ _).obj (freeSectionsFunctor y).op) ≪≫
      Functor.isoWhiskerLeft preadditiveYoneda
        ((Functor.whiskeringLeft _ _ _).mapIso
          (NatIso.op (freeSectionsFunctorCompSheafFiberIso y p)).symm) ≪≫
      skyscraperPresheafFunctorIso y p)

/-- **The stalk formula** `(ε^* F)_p ≅ F_p`, naturally in the étale sheaf `F`: the stalk of
`ε^* F` at a complex point `p` is the stalk of `F` at the geometric point `p`. -/
noncomputable def stalkIso (p : ComplexPoints y) :
    analyticInverseImage y ⋙ (anPoint y p).sheafFiber (A := AddCommGrpCat.{1}) ≅
      (etPoint y p).sheafFiber :=
  Adjunction.leftAdjointUniq ((analyticAdjunction y).comp (anPoint y p).skyscraperSheafAdjunction)
    ((etPoint y p).skyscraperSheafAdjunction.ofNatIsoRight (skyscraperIso y p).symm)

/-! ### Exactness -/

instance isLeftAdjoint_analyticInverseImage : (analyticInverseImage y).IsLeftAdjoint :=
  (analyticAdjunction y).isLeftAdjoint

instance preservesFiniteColimits_analyticInverseImage :
    PreservesFiniteColimits (analyticInverseImage y) := inferInstance

instance additive_analyticDirectImage : (analyticDirectImage y).Additive where
  map_add {G G'} {f g} := by
    ext U φ
    exact Preadditive.comp_add _ _ _ φ f g

instance additive_analyticInverseImage : (analyticInverseImage y).Additive :=
  (analyticAdjunction y).left_adjoint_additive

/-- `ε^*` is left exact: finite limits are checked on stalks, and the stalk of `ε^* F` at `p` is
the stalk of `F` at the geometric point `p`, which is left exact in `F`. -/
instance preservesFiniteLimits_analyticInverseImage :
    PreservesFiniteLimits (analyticInverseImage y) := by
  refine ⟨fun K _ _ => ⟨fun {K'} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  refine ((_root_.Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology
    𝔛).jointlyReflectIsomorphisms AddCommGrpCat.{1}).jointlyReflectsLimit (fun Φ => ?_)
  have key (x : ULift.{1} (ComplexPoints y)) :
      IsLimit ((_root_.Opens.pointGrothendieckTopology x).sheafFiber.mapCone
        ((analyticInverseImage y).mapCone c)) :=
    IsLimit.mapConeEquiv (stalkIso y x.down).symm (isLimitOfPreserves _ hc)
  have h := (ObjectProperty.ofObj_iff _ _).1 Φ.property
  rw [← h.choose_spec]
  exact key _

end AlgebraicGeometry.Scheme.ComplexPoints
