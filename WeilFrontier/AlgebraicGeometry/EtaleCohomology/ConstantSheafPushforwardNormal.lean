module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import Weil.Attr

/-!
# The unit `M_X ⟶ i_* i^* M_X` along a dense open of a normal integral scheme

Let `X` be a normal integral scheme, `i : U ⟶ X` the inclusion of a nonempty open subscheme and
`M` a set, an abelian group or a `Λ`-module. Then the unit `M_X ⟶ i_* i^* M_X` of the adjunction
`i^* ⊣ i_*` on sheaves of the small étale sites, at the constant sheaf `M_X`, is an isomorphism;
since `i^* M_X ≅ M_U`, this says that `i_* M_U` is the constant sheaf `M_X`.

For sheaves of sets the input is the Stacks project's identification of the canonical comparison
`M_X ⟶ i_* M_U` as an isomorphism
(`Stacks.EtaleCohomology.isIso_constantSheafPushforwardComparison_opensIota`). The comparison is
the unit followed by `i_*` of the identification `i^* M_X ≅ M_U`: two families of morphisms
`M_X ⟶ i_* M_U` natural in the set `M` agree as soon as they agree for `M` a point, and the sheaf
`i_* (pt_U)` has a single global section. For abelian groups and `Λ`-modules the statement is
transported along the forgetful functors, which commute with inverse images (the comma categories
computing the left Kan extension along base change are filtered), with direct images, with
sheafification and with constant sheaves, and which reflect isomorphisms.

## Main definitions

* `AlgebraicGeometry.Scheme.etaleSheafPullbackConstantSheafIso`: the inverse image of a
  constant sheaf along a morphism of schemes is the constant sheaf, for any coefficients.

## Main results

* `AlgebraicGeometry.Scheme.unit_app_constantSheaf_comp_map_sheafPullbackConstantSheafIso`: the
  unit at a constant sheaf of sets, followed by `f_*` of `f^* M_X ≅ M_Y`, is the canonical
  comparison `M_X ⟶ f_* M_Y`.
* `AlgebraicGeometry.Scheme.isIso_unit_app_constantSheaf_of_sheafCompose`: the unit at a constant
  sheaf is invertible as soon as it is after a change of coefficients reflecting isomorphisms.
* `AlgebraicGeometry.Scheme.isIso_unit_app_constantSheaf_opensι_types`,
  `AlgebraicGeometry.Scheme.isIso_unit_app_constantSheaf_opensι_addCommGrpCat`,
  `AlgebraicGeometry.Scheme.isIso_unit_app_constantSheaf_opensι_moduleCat`: the unit
  `M_X ⟶ i_* i^* M_X` is an isomorphism for a nonempty open `U` of a normal integral scheme `X`,
  for sets, abelian groups and `Λ`-modules.

## Implementation notes

The statements are on the small étale site `X.smallEtaleTopology` of `X.Etale`, the site on which
the Stacks project's comparison is proved. Sets, abelian groups and modules live in the universe
`max (u + 1) v` for `X : Scheme.{u}`, as for the comparison.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Lemma 59.73.13 (Tag 09Z5)](https://stacks.math.columbia.edu/tag/09Z5)
-/

/- Stated on Mathlib's
`Scheme.smallEtaleTopology` because the reused StacksFrontier comparison lives there. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology

universe u v

namespace AlgebraicGeometry.Scheme

/-- Base change of the small étale sites along a morphism of schemes. -/
local notation "EB" => Stacks.EtaleCohomology.smallEtaleBaseChange

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The canonical comparison `M_X ⟶ f_* M_Y` is natural in the set `M`. -/
theorem constantSheafPushforwardComparison_naturality {E E' : Type (max (u + 1) v)}
    (g : E ⟶ E') :
    (constantSheaf X.smallEtaleTopology _).map g ≫ constantSheafPushforwardComparison.{u, v} f E' =
      constantSheafPushforwardComparison.{u, v} f E ≫
        (smallEtaleDirectImage.{u, v} f).map ((constantSheaf Y.smallEtaleTopology _).map g) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (((smallEtaleDirectImage.{u, v} f).obj _).property)
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
  change toSheafify _ _ ≫ sheafifyMap _ ((Functor.const _).map g) ≫ sheafifyLift _ _ _ =
    toSheafify _ _ ≫ sheafifyLift _ _ _ ≫ _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, toSheafify_sheafifyLift,
    ← Category.assoc, toSheafify_sheafifyLift]
  exact congrArg (Functor.whiskerLeft (EB f).op)
    (toSheafify_naturality Y.smallEtaleTopology ((Functor.const _).map g))

/-- The constant sheaf on a point has at most one section over every object. -/
theorem subsingleton_constantSheaf_punit_obj.{w, u₁, v₁} {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type w)] (V : Cᵒᵖ) :
    Subsingleton (((constantSheaf J (Type w)).obj PUnit).obj.obj V) := by
  have h1 : IsTerminal ((Functor.const Cᵒᵖ).obj (PUnit : Type w)) :=
    IsTerminal.ofUniqueHom (fun _ => { app := fun _ => TypeCat.ofHom fun _ => PUnit.unit })
      (fun _ _ => by ext; rfl)
  have h2 := h1.isTerminalObj (presheafToSheaf J (Type w))
  have h3 := (h2.isTerminalObj (sheafToPresheaf J (Type w))).isTerminalObj
    ((CategoryTheory.evaluation Cᵒᵖ (Type w)).obj V)
  exact ⟨fun x y => @Subsingleton.elim _
    (@Unique.instSubsingleton _ (Types.isTerminalEquivUnique _ h3)) x y⟩

/-- `X`, with the identity, is a terminal object of the small étale site of `X`. -/
def isTerminalEtaleMkIdSelf (X : Scheme.{u}) : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  have : IsIso (Scheme.Etale.mk (𝟙 X)).hom := inferInstanceAs (IsIso (𝟙 X))
  isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 X))

section Pullback

variable (A : Type*) [Category* A] [HasWeakSheafify X.smallEtaleTopology A]
  [HasWeakSheafify Y.smallEtaleTopology A]
  [∀ P : X.Etaleᵒᵖ ⥤ A, (EB f).op.HasLeftKanExtension P]

/-- **The inverse image of a constant sheaf is the constant sheaf**: `f^* M_X ≅ M_Y` for
`f : Y ⟶ X`, naturally in `M`. Both functors are left adjoint to the sections over the base
change of the terminal object `X`, which is terminal in the small étale site of `Y`. -/
def etaleSheafPullbackConstantSheafIso :
    constantSheaf X.smallEtaleTopology A ⋙
        (EB f).sheafPullback A X.smallEtaleTopology Y.smallEtaleTopology ≅
      constantSheaf Y.smallEtaleTopology A :=
  ((constantSheafAdj _ A (isTerminalEtaleMkIdSelf X)).comp
    ((EB f).sheafAdjunctionContinuous A _ _)).leftAdjointUniq
    (constantSheafAdj _ A ((isTerminalEtaleMkIdSelf X).isTerminalObj (EB f)))

end Pullback

/-- The unit of `f^* ⊣ f_*` at the constant sheaf `M_X` of sets, followed by `f_*` of
`f^* M_X ≅ M_Y`, is the canonical comparison `M_X ⟶ f_* M_Y`. -/
theorem unit_app_constantSheaf_comp_map_sheafPullbackConstantSheafIso
    (E : Type (max (u + 1) v)) :
    ((EB f).sheafAdjunctionContinuous (Type (max (u + 1) v))
        X.smallEtaleTopology Y.smallEtaleTopology).unit.app
        ((constantSheaf X.smallEtaleTopology _).obj E) ≫
      (smallEtaleDirectImage.{u, v} f).map
        ((etaleSheafPullbackConstantSheafIso f (Type (max (u + 1) v))).hom.app E) =
      constantSheafPushforwardComparison.{u, v} f E := by
  let a := constantSheafAdj X.smallEtaleTopology (Type (max (u + 1) v))
    (isTerminalEtaleMkIdSelf X)
  have key : ∀ {F F' : Sheaf Y.smallEtaleTopology (Type (max (u + 1) v))}
      (ψ : (constantSheaf X.smallEtaleTopology _).obj E ⟶ (smallEtaleDirectImage.{u, v} f).obj F)
      (ψ' : (constantSheaf X.smallEtaleTopology _).obj PUnit ⟶
        (smallEtaleDirectImage.{u, v} f).obj F')
      (k : F' ⟶ F) (e : E)
      (_ : (constantSheaf X.smallEtaleTopology _).map (CategoryTheory.homOfElement e) ≫ ψ =
        ψ' ≫ (smallEtaleDirectImage.{u, v} f).map k),
      a.homEquiv _ _ ψ e =
        ((smallEtaleDirectImage.{u, v} f).map k).hom.app (op (Scheme.Etale.mk (𝟙 X)))
        (a.homEquiv _ _ ψ' PUnit.unit) := by
    intro F F' ψ ψ' k e h
    have h1 := ConcreteCategory.congr_hom
      (a.homEquiv_naturality_left (CategoryTheory.homOfElement e) ψ) PUnit.unit
    have h2 := ConcreteCategory.congr_hom
      (a.homEquiv_naturality_right ψ' ((smallEtaleDirectImage.{u, v} f).map k)) PUnit.unit
    rw [h] at h1
    exact h1.symm.trans h2
  apply (a.homEquiv _ _).injective
  ext e
  let adj := (EB f).sheafAdjunctionContinuous (Type (max (u + 1) v))
    X.smallEtaleTopology Y.smallEtaleTopology
  let θ := etaleSheafPullbackConstantSheafIso f (Type (max (u + 1) v))
  let β : ∀ E' : Type (max (u + 1) v), (constantSheaf X.smallEtaleTopology _).obj E' ⟶
      (smallEtaleDirectImage.{u, v} f).obj ((constantSheaf Y.smallEtaleTopology _).obj E') :=
    fun E' => adj.unit.app ((constantSheaf X.smallEtaleTopology _).obj E') ≫
      (smallEtaleDirectImage.{u, v} f).map (θ.hom.app E')
  have hβ : (constantSheaf X.smallEtaleTopology _).map (CategoryTheory.homOfElement e) ≫ β E =
      β PUnit ≫ (smallEtaleDirectImage.{u, v} f).map
        ((constantSheaf Y.smallEtaleTopology _).map (CategoryTheory.homOfElement e)) := by
    have hθ := θ.hom.naturality (CategoryTheory.homOfElement e)
    simp only [β]
    rw [← Category.assoc, ← adj.unit_naturality, Category.assoc, Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun φ => _ ≫ (smallEtaleDirectImage.{u, v} f).map φ) hθ
  have h1 := key (β E) (β PUnit)
    ((constantSheaf Y.smallEtaleTopology _).map (CategoryTheory.homOfElement e)) e hβ
  have h2 := key (constantSheafPushforwardComparison.{u, v} f E)
    (constantSheafPushforwardComparison.{u, v} f PUnit)
    ((constantSheaf Y.smallEtaleTopology _).map (CategoryTheory.homOfElement e)) e
    (constantSheafPushforwardComparison_naturality f _)
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  exact @Subsingleton.elim _
    (subsingleton_constantSheaf_punit_obj.{max (u + 1) v} Y.smallEtaleTopology _) _ _

/-- The unit of `f^* ⊣ f_*` at a constant sheaf of sets is an isomorphism when the canonical
comparison `M_X ⟶ f_* M_Y` is. -/
theorem isIso_unit_app_constantSheaf_of_isIso_comparison (E : Type (max (u + 1) v))
    [IsIso (constantSheafPushforwardComparison.{u, v} f E)] :
    IsIso (((EB f).sheafAdjunctionContinuous (Type (max (u + 1) v))
      X.smallEtaleTopology Y.smallEtaleTopology).unit.app
        ((constantSheaf X.smallEtaleTopology _).obj E)) := by
  have h := unit_app_constantSheaf_comp_map_sheafPullbackConstantSheafIso f E
  have : IsIso (((EB f).sheafAdjunctionContinuous (Type (max (u + 1) v))
      X.smallEtaleTopology Y.smallEtaleTopology).unit.app
        ((constantSheaf X.smallEtaleTopology _).obj E) ≫
      (smallEtaleDirectImage.{u, v} f).map
        ((etaleSheafPullbackConstantSheafIso f (Type (max (u + 1) v))).hom.app E)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((smallEtaleDirectImage.{u, v} f).map
    ((etaleSheafPullbackConstantSheafIso f (Type (max (u + 1) v))).hom.app E))

/-- **FK I.4, sets.** For a nonempty open `U` of a normal integral scheme `X` and a set `M`, the
unit `M_X ⟶ i_* i^* M_X` of the inverse image adjunction along `i : U ⟶ X` is an isomorphism. -/
@[weil "lem_fk104_pushforward_constant_from_dense_open_normal_constant"]
theorem isIso_unit_app_constantSheaf_opensι_types [IsIntegral X] [IsNormal X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) (E : Type (max (u + 1) v)) :
    IsIso (((EB U.ι).sheafAdjunctionContinuous (Type (max (u + 1) v))
      X.smallEtaleTopology U.toScheme.smallEtaleTopology).unit.app
        ((constantSheaf X.smallEtaleTopology _).obj E)) :=
  have := isIso_constantSheafPushforwardComparison_opensIota.{u, v} U hU E
  isIso_unit_app_constantSheaf_of_isIso_comparison U.ι E

section Coefficients

variable (A B : Type*) [Category* A] [Category* B] (Φ : A ⥤ B)
  [HasWeakSheafify X.smallEtaleTopology A] [HasWeakSheafify Y.smallEtaleTopology A]
  [HasWeakSheafify X.smallEtaleTopology B] [HasWeakSheafify Y.smallEtaleTopology B]
  [∀ P : X.Etaleᵒᵖ ⥤ A, (EB f).op.HasLeftKanExtension P]
  [∀ P : X.Etaleᵒᵖ ⥤ B, (EB f).op.HasLeftKanExtension P]
  [Φ.PreservesLeftKanExtensions (EB f).op]
  [X.smallEtaleTopology.HasSheafCompose Φ] [Y.smallEtaleTopology.HasSheafCompose Φ]
  [X.smallEtaleTopology.PreservesSheafification Φ] [Y.smallEtaleTopology.PreservesSheafification Φ]
  [(sheafCompose X.smallEtaleTopology Φ).ReflectsIsomorphisms]

/-- The unit of `f^* ⊣ f_*` at the constant sheaf `M_X` with coefficients in `A` is an
isomorphism when the unit at `(Φ M)_X` is, for a change of coefficients `Φ : A ⥤ B` commuting
with inverse images and sheafification and reflecting isomorphisms of sheaves. -/
theorem isIso_unit_app_constantSheaf_of_sheafCompose (M : A)
    (h : IsIso (((EB f).sheafAdjunctionContinuous B
      X.smallEtaleTopology Y.smallEtaleTopology).unit.app
        ((constantSheaf X.smallEtaleTopology B).obj (Φ.obj M)))) :
    IsIso (((EB f).sheafAdjunctionContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).unit.app
        ((constantSheaf X.smallEtaleTopology A).obj M)) := by
  have h1 := coefficientSheafPullbackTwoSquare_unit
    (EB f) X.smallEtaleTopology
    Y.smallEtaleTopology Φ ((constantSheaf X.smallEtaleTopology A).obj M)
  have h2 : IsIso (((EB f).sheafAdjunctionContinuous B
      X.smallEtaleTopology Y.smallEtaleTopology).unit.app
        ((sheafCompose X.smallEtaleTopology Φ).obj
          ((constantSheaf X.smallEtaleTopology A).obj M))) :=
    (NatTrans.isIso_app_iff_of_iso
      ((EB f).sheafAdjunctionContinuous
        B X.smallEtaleTopology Y.smallEtaleTopology).unit
      ((constantCommuteCompose X.smallEtaleTopology Φ).app M)).2 h
  have h3 : IsIso ((coefficientSheafPullbackTwoSquare
      (EB f)
      X.smallEtaleTopology Y.smallEtaleTopology Φ).natTrans.app
        ((constantSheaf X.smallEtaleTopology A).obj M)) := inferInstance
  have : IsIso ((sheafCompose X.smallEtaleTopology Φ).map
      (((EB f).sheafAdjunctionContinuous A
        X.smallEtaleTopology Y.smallEtaleTopology).unit.app
          ((constantSheaf X.smallEtaleTopology A).obj M))) := by
    rw [h1]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 (Functor.map_isIso _ _)
  exact isIso_of_reflects_iso _ (sheafCompose X.smallEtaleTopology Φ)

end Coefficients

/-- A functor preserving filtered colimits preserves the left Kan extensions along the opposite
of base change of small étale sites: the comma categories computing them are filtered. -/
theorem preservesLeftKanExtensions_smallEtaleBaseChange_op {A B : Type*} [Category* A]
    [Category* B] (Φ : A ⥤ B) [PreservesFilteredColimitsOfSize.{u, u + 1} Φ]
    [∀ P : X.Etaleᵒᵖ ⥤ A, (EB f).op.HasPointwiseLeftKanExtension P] :
    Φ.PreservesLeftKanExtensions (EB f).op := by
  intro P
  have : ∀ V : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (EB f).op V) :=
    fun V => IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (EB f) V.unop)
  infer_instance

/-- **FK I.4, abelian groups.** For a nonempty open `U` of a normal integral scheme `X` and an
abelian group `M`, the unit `M_X ⟶ i_* i^* M_X` is an isomorphism of abelian sheaves. -/
@[weil "lem_fk104_pushforward_constant_from_dense_open_normal_constant"]
theorem isIso_unit_app_constantSheaf_opensι_addCommGrpCat [IsIntegral X] [IsNormal X]
    (U : X.Opens) (hU : (U : Set X).Nonempty) (M : AddCommGrpCat.{max (u + 1) v}) :
    IsIso (((EB U.ι).sheafAdjunctionContinuous
      AddCommGrpCat.{max (u + 1) v} X.smallEtaleTopology U.toScheme.smallEtaleTopology).unit.app
        ((constantSheaf X.smallEtaleTopology _).obj M)) := by
  have : (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}).PreservesLeftKanExtensions
      (EB U.ι).op :=
    have : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
      preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
    preservesLeftKanExtensions_smallEtaleBaseChange_op U.ι _
  exact isIso_unit_app_constantSheaf_of_sheafCompose U.ι _ _
    (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) M
    (isIso_unit_app_constantSheaf_opensι_types U hU _)

/-- **FK I.4, `Λ`-modules.** For a nonempty open `U` of a normal integral scheme `X`, a ring `Λ`
and a `Λ`-module `M`, the unit `M_X ⟶ i_* i^* M_X` is an isomorphism of sheaves of
`Λ`-modules. -/
@[weil "lem_fk104_pushforward_constant_from_dense_open_normal_constant"]
theorem isIso_unit_app_constantSheaf_opensι_moduleCat [IsIntegral X] [IsNormal X]
    (U : X.Opens) (hU : (U : Set X).Nonempty) (Λ : Type v) [Ring Λ]
    (M : ModuleCat.{max (u + 1) v} Λ) :
    IsIso (((EB U.ι).sheafAdjunctionContinuous
      (ModuleCat.{max (u + 1) v} Λ) X.smallEtaleTopology U.toScheme.smallEtaleTopology).unit.app
        ((constantSheaf X.smallEtaleTopology _).obj M)) := by
  have : (forget₂ (ModuleCat.{max (u + 1) v} Λ)
      AddCommGrpCat.{max (u + 1) v}).PreservesLeftKanExtensions
      (EB U.ι).op :=
    have : PreservesColimitsOfSize.{u, u + 1}
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) v, v, u, u + 1} Λ
    preservesLeftKanExtensions_smallEtaleBaseChange_op U.ι _
  have := Stacks.ModuleSheaf.preservesSheafification_forget₂.{max (u + 1) v} Λ X.smallEtaleTopology
  have := Stacks.ModuleSheaf.preservesSheafification_forget₂.{max (u + 1) v} Λ
    U.toScheme.smallEtaleTopology
  have := Stacks.ModuleSheaf.hasSheafCompose_forget₂.{max (u + 1) v} Λ X.smallEtaleTopology
  have := Stacks.ModuleSheaf.hasSheafCompose_forget₂.{max (u + 1) v} Λ
    U.toScheme.smallEtaleTopology
  exact isIso_unit_app_constantSheaf_of_sheafCompose U.ι _ _
    (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) M
    (isIso_unit_app_constantSheaf_opensι_addCommGrpCat U hU _)

end AlgebraicGeometry.Scheme
