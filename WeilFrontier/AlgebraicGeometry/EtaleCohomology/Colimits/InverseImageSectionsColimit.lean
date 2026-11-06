module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.InverseImageCokernelOfRepresentablePair
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import WeilFrontier.CategoryTheory.Sites.CokernelEquivalenceRelationEffective
public import WeilFrontier.Defs.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleObject
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Sections of presheaf images along a projective system of schemes

Let `X = lim X_α` be a projective system of schemes with limit, `α₀` an index and
`r₁, r₂ : R ⇉ H` morphisms of étale `X_{α₀}`-schemes such that the pair of represented sheaves
`h_R ⇉ h_H` is an equivalence relation. Let `𝒢 = Coker(h_R ⇉ h_H)` with its canonical map
`π : h_H ⟶ 𝒢`, let `𝒢_α = p_{α α₀}^* 𝒢` and `p_{α₀}^* 𝒢` be its inverse images, and let
`𝒯_α ⊆ 𝒢_α`, `𝒯 ⊆ p_{α₀}^* 𝒢` be the presheaf images (`CategoryTheory.Subfunctor.range`) of
the inverse images of `π`. For `α₁ ≥ α₀` and a quasi-compact quasi-separated étale
`X_{α₁}`-scheme `U₁` with base changes `U_α` and `U`, the restriction maps induce a bijection
`colim_{α ≥ α₁} 𝒯_α(U_α) ≅ 𝒯(U)`.

The proof describes the sections of the presheaf images through morphisms into `H`: a section of
`p^* h_H` over `V` is the restriction of the image of `id_H` under the unit of `p^* ⊣ p_*` along
a unique morphism `V ⟶ T ×_{X₀} H`, so every section of `𝒯_α(U_α)` is the restriction of
`p^*(π(id_H))` along a morphism `U_α ⟶ X_α ×_{X_{α₀}} H`, and two such restrictions agree exactly
when the two morphisms are related by `R` (the equivalence relation is effective). Restriction
along `U_β ⟶ U_α` and `U ⟶ U_α`, read through `p_{βα}^* p_{α α₀}^* ≅ p_{β α₀}^*`, is base change
of these morphisms. The statement then follows from the description of morphisms out of `U` into
schemes locally of finite presentation over `X_{α₀}` (Stacks 01ZC): they come from a stage, and
two morphisms at a stage which agree on `U` agree at a later stage.

## Main definitions

* `AlgebraicGeometry.presheafImageStageSections` — the system `α ↦ 𝒯_α(U_α)`, indexed by
  `(Over α₁)ᵒᵖ`, with the restriction maps.
* `AlgebraicGeometry.presheafImageStageSectionsCocone` — its cocone with apex `𝒯(U)`, given by
  restriction along `U ⟶ U_α`.

## Main results

* `AlgebraicGeometry.nonempty_isColimit_presheafImageStageSectionsCocone` — the restriction maps
  induce a bijection `colim_{α ≥ α₁} 𝒯_α(U_α) ≅ 𝒯(U)`.
* `AlgebraicGeometry.smallEtaleInverseImageSection_universalSection_eq_iff` — effectiveness of
  the base-changed equivalence relation on sections of `p^* Coker(h_R ⇉ h_H)`.
* `AlgebraicGeometry.exists_etaleStage_etaleLimitTransition_comp_eq`,
  `AlgebraicGeometry.exists_etaleStageTransition_comp_eq` — morphisms out of `U` into a scheme
  locally of finite presentation come from a stage, and equalities descend (Stacks 01ZC).

## Implementation notes

The projective system is a functor `D : I ⥤ B.Scheme` into the schemes of a big étale site with a
cone `c`, satisfying `AlgebraicGeometry.IsProjectiveSystemWithLimit` after the inclusion into all
schemes; the stages `α ≥ α₁` are the objects of `Over α₁`, so the colimit is over
`(Over α₁)ᵒᵖ`, which is filtered. Sheaves are on StacksFrontier's small étale sites
`AlgebraicGeometry.SmallEtale` with values in `Type (u + 1)`, the represented sheaves are
`GrothendieckTopology.uliftYoneda`, and the étale schemes are arbitrary étale schemes of the
site; the quasi-compactness and quasi-separatedness of `U₁`, automatic for an object of
Freitag–Kiehl's `Et(X_{α₁})`, is assumed explicitly. The equivalence relation hypothesis is the
source's, on the represented sheaves; it is equivalent to `r₁, r₂` being an internal equivalence
relation (`AlgebraicGeometry.isEquivalenceRelation_smallEtaleYoneda_map_iff`). The bijection is
stated as the cocone being a colimit cocone in the category of sets.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.4.17 2),
  claim a).
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

section Restriction

variable {S T T' : B.Scheme}

/-- The unit of `p^* ⊣ p_*` on sections: `F(W) ⟶ (p^* F)(T ×_S W)`. -/
abbrev smallEtaleInverseImageUnitApp (p : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    (W : SmallEtale B S.obj S.property) :
    F.obj.obj (op W) ⟶ ((smallEtaleInverseImage B p (Type (u + 1))).obj F).obj.obj
      (op ((smallEtaleBaseChange B p).obj W)) :=
  ((smallEtaleInverseImageAdjunction B p (Type (u + 1))).unit.app F).hom.app (op W)

/-- Restriction of sections of inverse images along a morphism over the base. -/
def smallEtaleInverseImageRestrict (p : T ⟶ S) (p' : T' ⟶ S) (φ : T' ⟶ T) (hφ : φ ≫ p = p')
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {V : SmallEtale B T.obj T.property} {V' : SmallEtale B T'.obj T'.property}
    (e : V' ⟶ (smallEtaleBaseChange B φ).obj V) :
    ((smallEtaleInverseImage B p (Type (u + 1))).obj F).obj.obj (op V) ⟶
      ((smallEtaleInverseImage B p' (Type (u + 1))).obj F).obj.obj (op V') :=
  smallEtaleInverseImageUnitApp B φ ((smallEtaleInverseImage B p (Type (u + 1))).obj F) V ≫
    ((smallEtaleInverseImageComp B (Type (u + 1)) φ p p' hφ).hom.app F).hom.app
      (op ((smallEtaleBaseChange B φ).obj V)) ≫
    ((smallEtaleInverseImage B p' (Type (u + 1))).obj F).obj.map e.op

/-- The core compatibility of the units with `θ`. -/
lemma smallEtaleInverseImageComp_unitApp (p : T ⟶ S) (p' : T' ⟶ S) (φ : T' ⟶ T)
    (hφ : φ ≫ p = p') (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    (W : SmallEtale B S.obj S.property) (σ : F.obj.obj (op W)) :
    ((smallEtaleInverseImageComp B (Type (u + 1)) φ p p' hφ).hom.app F).hom.app
        (op ((smallEtaleBaseChange B φ).obj ((smallEtaleBaseChange B p).obj W)))
        (smallEtaleInverseImageUnitApp B φ _ _ (smallEtaleInverseImageUnitApp B p F W σ)) =
      ((smallEtaleInverseImage B p' (Type (u + 1))).obj F).obj.map
        ((smallEtaleBaseChange_factoredCompIso B _ _ _ φ p p' hφ).hom.app W).op
        (smallEtaleInverseImageUnitApp B p' F W σ) := by
  have h := unit_conjugateEquiv_symm
    (smallEtaleInverseImageAdjunction B p' (Type (u + 1)))
    ((smallEtaleInverseImageAdjunction B p (Type (u + 1))).comp
      (smallEtaleInverseImageAdjunction B φ (Type (u + 1))))
    (smallEtaleDirectImageComp B (Type (u + 1)) φ p p' hφ).inv F
  have h' := congrArg (fun g => g.hom.app (op W) σ) h
  simp only [Adjunction.comp_unit_app] at h'
  exact h'.symm

/-- The section of `p^* F` over `V` obtained from a section `σ` of `F` over `W` and a morphism
`h : V ⟶ T ×_S W`: the restriction along `h` of the image of `σ` under the unit. -/
def smallEtaleInverseImageSection (p : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {W : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    (h : V ⟶ (smallEtaleBaseChange B p).obj W) (σ : F.obj.obj (op W)) :
    ((smallEtaleInverseImage B p (Type (u + 1))).obj F).obj.obj (op V) :=
  ((smallEtaleInverseImage B p (Type (u + 1))).obj F).obj.map h.op
    (smallEtaleInverseImageUnitApp B p F W σ)

lemma smallEtaleInverseImageRestrict_section (p : T ⟶ S) (p' : T' ⟶ S) (φ : T' ⟶ T)
    (hφ : φ ≫ p = p') (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {W : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    {V' : SmallEtale B T'.obj T'.property} (e : V' ⟶ (smallEtaleBaseChange B φ).obj V)
    (h : V ⟶ (smallEtaleBaseChange B p).obj W) (σ : F.obj.obj (op W)) :
    smallEtaleInverseImageRestrict B p p' φ hφ F e (smallEtaleInverseImageSection B p F h σ) =
      smallEtaleInverseImageSection B p' F
        (e ≫ (smallEtaleBaseChange B φ).map h ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ _ φ p p' hφ).hom.app W) σ := by
  simp only [smallEtaleInverseImageRestrict, smallEtaleInverseImageSection, types_comp_apply]
  have h1 := NatTrans.naturality_apply
    ((smallEtaleInverseImageAdjunction B φ (Type (u + 1))).unit.app
      ((smallEtaleInverseImage B p (Type (u + 1))).obj F)).hom h.op
    (smallEtaleInverseImageUnitApp B p F W σ)
  erw [h1]
  have h2 := NatTrans.naturality_apply
    ((smallEtaleInverseImageComp B (Type (u + 1)) φ p p' hφ).hom.app F).hom
    ((smallEtaleBaseChange B φ).map h).op
    (smallEtaleInverseImageUnitApp B φ _ _ (smallEtaleInverseImageUnitApp B p F W σ))
  erw [h2]
  rw [smallEtaleInverseImageComp_unitApp]
  simp only [← Functor.map_comp_apply, ← op_comp]

lemma smallEtaleInverseImageSection_comp (p : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {W : SmallEtale B S.obj S.property} {V V' : SmallEtale B T.obj T.property}
    (g : V' ⟶ V) (h : V ⟶ (smallEtaleBaseChange B p).obj W) (σ : F.obj.obj (op W)) :
    ((smallEtaleInverseImage B p (Type (u + 1))).obj F).obj.map g.op
        (smallEtaleInverseImageSection B p F h σ) =
      smallEtaleInverseImageSection B p F (g ≫ h) σ := by
  simp only [smallEtaleInverseImageSection, op_comp, Functor.map_comp_apply]

lemma smallEtaleInverseImageSection_comp_baseChange_map (p : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1)))
    {W W' : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    (h : V ⟶ (smallEtaleBaseChange B p).obj W') (a : W' ⟶ W) (σ : F.obj.obj (op W)) :
    smallEtaleInverseImageSection B p F (h ≫ (smallEtaleBaseChange B p).map a) σ =
      smallEtaleInverseImageSection B p F h (F.obj.map a.op σ) := by
  simp only [smallEtaleInverseImageSection, smallEtaleInverseImageUnitApp]
  have := NatTrans.naturality_apply
    ((smallEtaleInverseImageAdjunction B p (Type (u + 1))).unit.app F).hom a.op σ
  erw [this]
  simp only [op_comp, Functor.map_comp_apply]
  rfl

lemma smallEtaleInverseImage_map_section (p : T ⟶ S)
    {F F' : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))} (ψ : F ⟶ F')
    {W : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    (h : V ⟶ (smallEtaleBaseChange B p).obj W) (σ : F.obj.obj (op W)) :
    ((smallEtaleInverseImage B p (Type (u + 1))).map ψ).hom.app (op V)
        (smallEtaleInverseImageSection B p F h σ) =
      smallEtaleInverseImageSection B p F' h (ψ.hom.app (op W) σ) := by
  simp only [smallEtaleInverseImageSection, smallEtaleInverseImageUnitApp]
  rw [NatTrans.naturality_apply]
  congr 1
  have := (smallEtaleInverseImageAdjunction B p (Type (u + 1))).unit.naturality ψ
  have h' := congrArg (fun g => g.hom.app (op W) σ) this
  exact h'.symm

end Restriction

section Yoneda

variable {S T : B.Scheme}

/-- The universal section `id_Z` of the represented sheaf `h_Z` over `Z`. -/
abbrev smallEtaleYonedaId {X : B.Scheme} (Z : SmallEtale B X.obj X.property) :
    ((SmallEtale.topology B X.obj X.property).uliftYoneda.{u + 1}.obj Z).obj.obj (op Z) :=
  (SmallEtale.topology B X.obj X.property).uliftYonedaEquiv (𝟙 _)

/-- The section of `p^* h_Z` over `V` attached to a morphism `h : V ⟶ T ×_S Z`. -/
abbrev smallEtaleInverseImageYonedaSection (p : T ⟶ S) (Z : SmallEtale B S.obj S.property)
    {V : SmallEtale B T.obj T.property} (h : V ⟶ (smallEtaleBaseChange B p).obj Z) :
    ((smallEtaleInverseImage B p (Type (u + 1))).obj
      ((SmallEtale.topology B S.obj S.property).uliftYoneda.{u + 1}.obj Z)).obj.obj (op V) :=
  smallEtaleInverseImageSection B p _ h (smallEtaleYonedaId B Z)

lemma smallEtaleInverseImageUliftYonedaIso_inv_app_id (p : T ⟶ S)
    (Z : SmallEtale B S.obj S.property) :
    ((smallEtaleInverseImageUliftYonedaIso.{u + 1} B p).app Z).inv.hom.app
        (op ((smallEtaleBaseChange B p).obj Z)) (smallEtaleYonedaId B _) =
      smallEtaleInverseImageUnitApp B p _ Z (smallEtaleYonedaId B Z) := by
  have := smallEtaleInverseImageUliftYonedaIso_hom_app_comp.{u + 1} B p Z _
    ((smallEtaleInverseImageUliftYonedaIso.{u + 1} B p).app Z).inv
  erw [Iso.hom_inv_id, Adjunction.homEquiv_id] at this
  rw [← Category.id_comp ((smallEtaleInverseImageAdjunction B p (Type (u + 1))).unit.app _),
    GrothendieckTopology.uliftYonedaEquiv_comp] at this
  rw [← Category.id_comp ((smallEtaleInverseImageUliftYonedaIso.{u + 1} B p).app Z).inv,
    GrothendieckTopology.uliftYonedaEquiv_comp] at this
  exact this.symm

lemma smallEtaleInverseImageYonedaSection_eq (p : T ⟶ S) (Z : SmallEtale B S.obj S.property)
    {V : SmallEtale B T.obj T.property} (h : V ⟶ (smallEtaleBaseChange B p).obj Z) :
    smallEtaleInverseImageYonedaSection B p Z h =
      ((smallEtaleInverseImageUliftYonedaIso.{u + 1} B p).app Z).inv.hom.app (op V)
        ((SmallEtale.topology B T.obj T.property).uliftYonedaEquiv
          ((SmallEtale.topology B T.obj T.property).uliftYoneda.{u + 1}.map h)) := by
  simp only [smallEtaleInverseImageYonedaSection, smallEtaleInverseImageSection]
  rw [← smallEtaleInverseImageUliftYonedaIso_inv_app_id]
  erw [← NatTrans.naturality_apply]
  congr 1

lemma bijective_smallEtaleInverseImageYonedaSection (p : T ⟶ S)
    (Z : SmallEtale B S.obj S.property) (V : SmallEtale B T.obj T.property) :
    Function.Bijective (smallEtaleInverseImageYonedaSection B p Z (V := V)) := by
  have e : smallEtaleInverseImageYonedaSection B p Z (V := V) =
      (((smallEtaleInverseImageUliftYonedaIso.{u + 1} B p).app Z).inv.hom.app (op V)) ∘
        (SmallEtale.topology B T.obj T.property).uliftYonedaEquiv ∘
          (SmallEtale.topology B T.obj T.property).uliftYoneda.{u + 1}.map :=
    funext fun h => smallEtaleInverseImageYonedaSection_eq B p Z h
  rw [e]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp (Equiv.bijective _)
    ((GrothendieckTopology.fullyFaithfulUliftYoneda _).map_bijective _ _))
  rw [← CategoryTheory.isIso_iff_bijective]
  infer_instance

lemma smallEtaleInverseImage_map_yonedaSection (p : T ⟶ S)
    {Z Z' : SmallEtale B S.obj S.property} (r : Z ⟶ Z')
    {V : SmallEtale B T.obj T.property} (h : V ⟶ (smallEtaleBaseChange B p).obj Z) :
    ((smallEtaleInverseImage B p (Type (u + 1))).map
        ((SmallEtale.topology B S.obj S.property).uliftYoneda.{u + 1}.map r)).hom.app (op V)
        (smallEtaleInverseImageYonedaSection B p Z h) =
      smallEtaleInverseImageYonedaSection B p Z' (h ≫ (smallEtaleBaseChange B p).map r) := by
  simp only [smallEtaleInverseImageYonedaSection]
  rw [smallEtaleInverseImage_map_section, smallEtaleInverseImageSection_comp_baseChange_map]
  congr 1

end Yoneda

section EquivalenceRelation

variable {C : Type*} [Category C]

/-- An internal equivalence relation `a, b : R ⟶ H` induces an equivalence relation on each
`Hom(V, H)`: `h ~ h'` if `(h, h') = (ρ ≫ a, ρ ≫ b)` for some `ρ : V ⟶ R`. -/
lemma _root_.CategoryTheory.EquivalenceRelation.equivalence_exists_comp {R H : C} {a b : R ⟶ H}
    (E : EquivalenceRelation a b) (V : C) :
    _root_.Equivalence (fun h h' : V ⟶ H => ∃ ρ : V ⟶ R, ρ ≫ a = h ∧ ρ ≫ b = h') where
  refl h := ⟨h ≫ E.r, by simp, by simp⟩
  symm := by
    rintro _ _ ⟨ρ, rfl, rfl⟩
    exact ⟨ρ ≫ E.s, by rw [Category.assoc, E.symmetry₁], by rw [Category.assoc, E.symmetry₂]⟩
  trans := by
    rintro _ _ _ ⟨ρ, rfl, h⟩ ⟨ρ', h', rfl⟩
    let ℓ := PullbackCone.IsLimit.lift E.isLimit ρ ρ' (h.trans h'.symm)
    refine ⟨ℓ ≫ E.t, ?_, ?_⟩
    · rw [Category.assoc, E.transitivity₁, ← Category.assoc,
        PullbackCone.IsLimit.lift_fst]
    · rw [Category.assoc, E.transitivity₂, ← Category.assoc,
        PullbackCone.IsLimit.lift_snd]

end EquivalenceRelation

section Components

variable {X Y Z : B.Scheme}

/-- The component `V ⟶ W` of a morphism `V ⟶ T ×_S W` into a base change. -/
abbrev smallEtaleBaseChangeComponent {S T : B.Scheme} (p : T ⟶ S)
    {W : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    (h : V ⟶ (smallEtaleBaseChange B p).obj W) : V.obj.left ⟶ W.obj.left :=
  h.hom.left ≫ smallEtaleBaseChangePullbackFst B p W

lemma smallEtaleBaseChangeComponent_comp {S T : B.Scheme} (p : T ⟶ S)
    {W : SmallEtale B S.obj S.property} {V V' : SmallEtale B T.obj T.property}
    (g : V' ⟶ V) (h : V ⟶ (smallEtaleBaseChange B p).obj W) :
    smallEtaleBaseChangeComponent B p (g ≫ h) =
      g.hom.left ≫ smallEtaleBaseChangeComponent B p h :=
  Category.assoc _ _ _

lemma smallEtaleBaseChangeComponent_comp_map {S T : B.Scheme} (p : T ⟶ S)
    {W W' : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    (h : V ⟶ (smallEtaleBaseChange B p).obj W) (a : W ⟶ W') :
    smallEtaleBaseChangeComponent B p (h ≫ (smallEtaleBaseChange B p).map a) =
      smallEtaleBaseChangeComponent B p h ≫ a.hom.left := by
  change (h.hom.left ≫ ((smallEtaleBaseChange B p).map a).hom.left) ≫ _ = _
  rw [Category.assoc, smallEtaleBaseChange_map_hom_left_fst, Category.assoc]

lemma smallEtaleBaseChangeComponent_transport (φ : X ⟶ Y) (p : Y ⟶ Z) (p' : X ⟶ Z)
    (hφ : φ ≫ p = p') {W : SmallEtale B Z.obj Z.property} {V : SmallEtale B Y.obj Y.property}
    {V' : SmallEtale B X.obj X.property} (e : V' ⟶ (smallEtaleBaseChange B φ).obj V)
    (h : V ⟶ (smallEtaleBaseChange B p).obj W) :
    smallEtaleBaseChangeComponent B p'
        (e ≫ (smallEtaleBaseChange B φ).map h ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ _ φ p p' hφ).hom.app W) =
      e.hom.left ≫ smallEtaleBaseChangePullbackFst B φ V ≫
        smallEtaleBaseChangeComponent B p h := by
  change (e.hom.left ≫ ((smallEtaleBaseChange B φ).map h).hom.left ≫
    ((smallEtaleBaseChange_factoredCompIso B _ _ _ φ p p' hφ).hom.app W).hom.left) ≫ _ = _
  simp only [Category.assoc, smallEtaleBaseChange_factoredCompIso_hom_app_left_pullbackFst,
    smallEtaleBaseChange_map_hom_left_fst_assoc]

lemma smallEtaleBaseChangeComponent_comp_hom {S T : B.Scheme} (p : T ⟶ S)
    {W : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    (h : V ⟶ (smallEtaleBaseChange B p).obj W) :
    smallEtaleBaseChangeComponent B p h ≫ W.obj.hom = V.obj.hom ≫ p := by
  have h1 : smallEtaleBaseChangePullbackFst B p W ≫ W.obj.hom =
      ((smallEtaleBaseChange B p).obj W).obj.hom ≫ p :=
    pullback.condition
  rw [smallEtaleBaseChangeComponent, Category.assoc, h1, ← Category.assoc]
  congr 1
  exact Over.w h.hom

/-- The morphism `V ⟶ T ×_S W` of étale `T`-schemes with a given component `V ⟶ W` over `S`. -/
def smallEtaleBaseChangeHomOfComponent {S T : B.Scheme} (p : T ⟶ S)
    {W : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    (k : V.obj.left ⟶ W.obj.left) (hk : k ≫ W.obj.hom = V.obj.hom ≫ p) :
    V ⟶ (smallEtaleBaseChange B p).obj W :=
  ObjectProperty.homMk (Over.homMk (pullback.lift k V.obj.hom hk) (pullback.lift_snd _ _ _))

lemma smallEtaleBaseChangeComponent_homOfComponent {S T : B.Scheme} (p : T ⟶ S)
    {W : SmallEtale B S.obj S.property} {V : SmallEtale B T.obj T.property}
    (k : V.obj.left ⟶ W.obj.left) (hk : k ≫ W.obj.hom = V.obj.hom ≫ p) :
    smallEtaleBaseChangeComponent B p (smallEtaleBaseChangeHomOfComponent B p k hk) = k :=
  pullback.lift_fst _ _ _

/-- The first component of the inverse of the comparison `X ×_Y (Y ×_Z U) ≅ X ×_Z U`. -/
lemma smallEtaleBaseChange_factoredCompIso_inv_fst_fst (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) (U : SmallEtale B Z.obj Z.property) :
    ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).inv.app U).hom.left ≫
        smallEtaleBaseChangePullbackFst B f ((smallEtaleBaseChange B g).obj U) ≫
          smallEtaleBaseChangePullbackFst B g U =
      smallEtaleBaseChangePullbackFst B fg U := by
  rw [← smallEtaleBaseChange_factoredCompIso_hom_app_left_pullbackFst B f g fg hfg U,
    ← Category.assoc]
  change (((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).inv.app U ≫
    (smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app U).hom.left) ≫ _ = _
  rw [Iso.inv_hom_id_app]
  exact Category.id_comp _

/-- The second component of the inverse of the comparison `X ×_Y (Y ×_Z U) ≅ X ×_Z U`. -/
lemma smallEtaleBaseChange_factoredCompIso_inv_fst_hom (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) (U : SmallEtale B Z.obj Z.property) :
    ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).inv.app U).hom.left ≫
        smallEtaleBaseChangePullbackFst B f ((smallEtaleBaseChange B g).obj U) ≫
          ((smallEtaleBaseChange B g).obj U).obj.hom =
      ((smallEtaleBaseChange B fg).obj U).obj.hom ≫ f := by
  have h1 : smallEtaleBaseChangePullbackFst B f ((smallEtaleBaseChange B g).obj U) ≫
      ((smallEtaleBaseChange B g).obj U).obj.hom =
        ((smallEtaleBaseChange B f).obj ((smallEtaleBaseChange B g).obj U)).obj.hom ≫ f :=
    pullback.condition
  rw [h1, ← Category.assoc]
  congr 1
  exact Over.w ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).inv.app U).hom

end Components

section Presentation

variable {X₀ T : B.Scheme} {R H : SmallEtale B X₀.obj X₀.property} (r₁ r₂ : R ⟶ H)

/-- The cokernel `Coker(h_R ⇉ h_H)` of the pair of represented sheaves. -/
abbrev smallEtalePairCokernel : Sheaf (SmallEtale.topology B X₀.obj X₀.property) (Type (u + 1)) :=
  Sheaf.pairCokernel ((SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}.map r₁)
    ((SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}.map r₂)

/-- The canonical map `π : h_H ⟶ Coker(h_R ⇉ h_H)`. -/
abbrev smallEtalePairCokernelπ :
    (SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}.obj H ⟶
      smallEtalePairCokernel B r₁ r₂ :=
  Sheaf.pairCokernelπ ((SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}.map r₁)
    ((SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}.map r₂)

/-- The section `π(id_H)` of the cokernel over `H`. -/
abbrev smallEtalePairCokernelUniversalSection :
    (smallEtalePairCokernel B r₁ r₂).obj.obj (op H) :=
  (smallEtalePairCokernelπ B r₁ r₂).hom.app (op H) (smallEtaleYonedaId B H)

variable (p : T ⟶ X₀)

lemma smallEtaleInverseImage_map_pairCokernelπ_yonedaSection
    {V : SmallEtale B T.obj T.property} (h : V ⟶ (smallEtaleBaseChange B p).obj H) :
    ((smallEtaleInverseImage B p (Type (u + 1))).map (smallEtalePairCokernelπ B r₁ r₂)).hom.app
        (op V) (smallEtaleInverseImageYonedaSection B p H h) =
      smallEtaleInverseImageSection B p _ h (smallEtalePairCokernelUniversalSection B r₁ r₂) :=
  smallEtaleInverseImage_map_section B p _ h _

/-- The sections of the presheaf image of `p^* π` are the restrictions of `p^*(π(id_H))` along
morphisms `V ⟶ T ×_{X₀} H`. -/
lemma mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff
    {V : SmallEtale B T.obj T.property}
    (x : ((smallEtaleInverseImage B p (Type (u + 1))).obj
      (smallEtalePairCokernel B r₁ r₂)).obj.obj (op V)) :
    x ∈ (Subfunctor.range ((smallEtaleInverseImage B p (Type (u + 1))).map
        (smallEtalePairCokernelπ B r₁ r₂)).hom).obj (op V) ↔
      ∃ h : V ⟶ (smallEtaleBaseChange B p).obj H,
        smallEtaleInverseImageSection B p _ h (smallEtalePairCokernelUniversalSection B r₁ r₂) =
          x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨h, rfl⟩ := (bijective_smallEtaleInverseImageYonedaSection B p H V).2 y
    exact ⟨h, (smallEtaleInverseImage_map_pairCokernelπ_yonedaSection B r₁ r₂ p h).symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨_, smallEtaleInverseImage_map_pairCokernelπ_yonedaSection B r₁ r₂ p h⟩

lemma smallEtaleInverseImageSection_universalSection_comp_eq
    {V : SmallEtale B T.obj T.property} (ρ : V ⟶ (smallEtaleBaseChange B p).obj R) :
    smallEtaleInverseImageSection B p _ (ρ ≫ (smallEtaleBaseChange B p).map r₁)
        (smallEtalePairCokernelUniversalSection B r₁ r₂) =
      smallEtaleInverseImageSection B p _ (ρ ≫ (smallEtaleBaseChange B p).map r₂)
        (smallEtalePairCokernelUniversalSection B r₁ r₂) := by
  rw [smallEtaleInverseImageSection_comp_baseChange_map,
    smallEtaleInverseImageSection_comp_baseChange_map]
  congr 1
  simp only [smallEtalePairCokernelUniversalSection]
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  erw [GrothendieckTopology.uliftYonedaEquiv_naturality,
    GrothendieckTopology.uliftYonedaEquiv_naturality]
  rw [Category.comp_id, Category.comp_id]
  have := Sheaf.pairCokernelπ_condition
    ((SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}.map r₁)
    ((SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}.map r₂)
  have h1 := congrArg (fun g => g.hom.app (op R) (smallEtaleYonedaId B R)) this
  simp only at h1
  erw [← GrothendieckTopology.uliftYonedaEquiv_comp, ← GrothendieckTopology.uliftYonedaEquiv_comp]
    at h1
  erw [← GrothendieckTopology.uliftYonedaEquiv_comp, ← GrothendieckTopology.uliftYonedaEquiv_comp]
  exact h1

/-- The pair `p^* h_R ⇉ p^* h_H` relates `p^*(h)` and `p^*(h')` exactly when `(h, h')` is the image
of a morphism `V ⟶ T ×_{X₀} R`. -/
lemma pairRel_smallEtaleInverseImage_yonedaSection_iff {V : SmallEtale B T.obj T.property}
    (h h' : V ⟶ (smallEtaleBaseChange B p).obj H) :
    Sheaf.PairRel ((smallEtaleInverseImage B p (Type (u + 1))).map
        ((SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}.map r₁))
      ((smallEtaleInverseImage B p (Type (u + 1))).map
        ((SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}.map r₂)) (op V)
      (smallEtaleInverseImageYonedaSection B p H h)
      (smallEtaleInverseImageYonedaSection B p H h') ↔
      ∃ ρ : V ⟶ (smallEtaleBaseChange B p).obj R,
        ρ ≫ (smallEtaleBaseChange B p).map r₁ = h ∧ ρ ≫ (smallEtaleBaseChange B p).map r₂ = h' := by
  have hinjH := (bijective_smallEtaleInverseImageYonedaSection B p H V).1
  constructor
  · rintro ⟨y, hy₁, hy₂⟩
    obtain ⟨ρ, rfl⟩ := (bijective_smallEtaleInverseImageYonedaSection B p R V).2 y
    rw [smallEtaleInverseImage_map_yonedaSection] at hy₁ hy₂
    exact ⟨ρ, hinjH hy₁, hinjH hy₂⟩
  · rintro ⟨ρ, rfl, rfl⟩
    exact ⟨smallEtaleInverseImageYonedaSection B p R ρ,
      smallEtaleInverseImage_map_yonedaSection B p r₁ ρ,
      smallEtaleInverseImage_map_yonedaSection B p r₂ ρ⟩

/-- **Effectiveness of the equivalence relation after inverse image.** If the base change
`T ×_{X₀} R ⇉ T ×_{X₀} H` is an equivalence relation, two restrictions of `p^*(π(id_H))` along
`h, h' : V ⟶ T ×_{X₀} H` agree if and only if `(h, h')` comes from a morphism
`V ⟶ T ×_{X₀} R`. -/
lemma smallEtaleInverseImageSection_universalSection_eq_iff
    [hE : IsEquivalenceRelation ((smallEtaleBaseChange B p).map r₁)
      ((smallEtaleBaseChange B p).map r₂)]
    {V : SmallEtale B T.obj T.property} (h h' : V ⟶ (smallEtaleBaseChange B p).obj H) :
    smallEtaleInverseImageSection B p _ h (smallEtalePairCokernelUniversalSection B r₁ r₂) =
        smallEtaleInverseImageSection B p _ h' (smallEtalePairCokernelUniversalSection B r₁ r₂) ↔
      ∃ ρ : V ⟶ (smallEtaleBaseChange B p).obj R,
        ρ ≫ (smallEtaleBaseChange B p).map r₁ = h ∧ ρ ≫ (smallEtaleBaseChange B p).map r₂ = h' := by
  obtain ⟨E⟩ := hE.nonempty_equivalenceRelation
  let L := smallEtaleInverseImage B p (Type (u + 1))
  let y := (SmallEtale.topology B X₀.obj X₀.property).uliftYoneda.{u + 1}
  have : PreservesColimitsOfSize.{0, 0} L :=
    (smallEtaleInverseImageAdjunction B p (Type (u + 1))).leftAdjoint_preservesColimits
  have hc := (isColimitMapCoconeCoforkEquiv L _).1
    (isColimitOfPreserves L (Sheaf.isColimitPairCokernelCofork (y.map r₁) (y.map r₂)))
  have hinj : ∀ U, Function.Injective
      (fun r : ((L.obj (y.obj R)).obj.obj U) =>
        ((L.map (y.map r₁)).hom.app U r, (L.map (y.map r₂)).hom.app U r)) := by
    intro U
    induction U using Opposite.rec with | op U => ?_
    intro a b hab
    obtain ⟨ρ, rfl⟩ := (bijective_smallEtaleInverseImageYonedaSection B p R U).2 a
    obtain ⟨ρ', rfl⟩ := (bijective_smallEtaleInverseImageYonedaSection B p R U).2 b
    simp only [Prod.mk.injEq] at hab
    erw [smallEtaleInverseImage_map_yonedaSection, smallEtaleInverseImage_map_yonedaSection,
      smallEtaleInverseImage_map_yonedaSection, smallEtaleInverseImage_map_yonedaSection] at hab
    have hinjH := (bijective_smallEtaleInverseImageYonedaSection B p H U).1
    rw [E.right_cancellation ρ ρ' (hinjH hab.1) (hinjH hab.2)]
  have heqv : ∀ U, _root_.Equivalence (Sheaf.PairRel (L.map (y.map r₁)) (L.map (y.map r₂)) U) := by
    intro U
    induction U using Opposite.rec with | op U => ?_
    have hsurj := (bijective_smallEtaleInverseImageYonedaSection B p H U).2
    have hR := E.equivalence_exists_comp U
    refine ⟨fun x => ?_, fun {x x'} hx => ?_, fun {x x' x''} hx hx' => ?_⟩
    · obtain ⟨g, rfl⟩ := hsurj x
      exact (pairRel_smallEtaleInverseImage_yonedaSection_iff B r₁ r₂ p g g).2 (hR.refl g)
    · obtain ⟨g, rfl⟩ := hsurj x
      obtain ⟨g', rfl⟩ := hsurj x'
      exact (pairRel_smallEtaleInverseImage_yonedaSection_iff B r₁ r₂ p g' g).2
        (hR.symm ((pairRel_smallEtaleInverseImage_yonedaSection_iff B r₁ r₂ p g g').1 hx))
    · obtain ⟨g, rfl⟩ := hsurj x
      obtain ⟨g', rfl⟩ := hsurj x'
      obtain ⟨g'', rfl⟩ := hsurj x''
      exact (pairRel_smallEtaleInverseImage_yonedaSection_iff B r₁ r₂ p g g'').2
        (hR.trans ((pairRel_smallEtaleInverseImage_yonedaSection_iff B r₁ r₂ p g g').1 hx)
          ((pairRel_smallEtaleInverseImage_yonedaSection_iff B r₁ r₂ p g' g'').1 hx'))
  have key := Sheaf.cofork_π_app_eq_iff_of_isColimit _ _ hinj heqv hc
    (smallEtaleInverseImageYonedaSection B p H h) (smallEtaleInverseImageYonedaSection B p H h')
  erw [smallEtaleInverseImage_map_pairCokernelπ_yonedaSection,
    smallEtaleInverseImage_map_pairCokernelπ_yonedaSection] at key
  rw [key]
  exact pairRel_smallEtaleInverseImage_yonedaSection_iff B r₁ r₂ p h h'

/-- The presheaf image `𝒯 ⊆ p^* Coker(h_R ⇉ h_H)` of the inverse image `p^* π` of the canonical
map `π : h_H ⟶ Coker(h_R ⇉ h_H)`. -/
abbrev smallEtaleInverseImagePairCokernelImage :
    Subfunctor ((smallEtaleInverseImage B p (Type (u + 1))).obj
      (smallEtalePairCokernel B r₁ r₂)).obj :=
  Subfunctor.range ((smallEtaleInverseImage B p (Type (u + 1))).map
    (smallEtalePairCokernelπ B r₁ r₂)).hom

lemma smallEtaleInverseImageSection_congr {W : SmallEtale B X₀.obj X₀.property}
    {F : Sheaf (SmallEtale.topology B X₀.obj X₀.property) (Type (u + 1))}
    {V : SmallEtale B T.obj T.property} {h h' : V ⟶ (smallEtaleBaseChange B p).obj W}
    (hh : smallEtaleBaseChangeComponent B p h = smallEtaleBaseChangeComponent B p h')
    (σ : F.obj.obj (op W)) :
    smallEtaleInverseImageSection B p F h σ = smallEtaleInverseImageSection B p F h' σ := by
  rw [smallEtaleBaseChange_hom_ext_fst B p hh]

lemma smallEtaleInverseImageRestrict_mem {T' : B.Scheme} (p' : T' ⟶ X₀) (φ : T' ⟶ T)
    (hφ : φ ≫ p = p') {V : SmallEtale B T.obj T.property} {V' : SmallEtale B T'.obj T'.property}
    (e : V' ⟶ (smallEtaleBaseChange B φ).obj V) {x}
    (hx : x ∈ (smallEtaleInverseImagePairCokernelImage B r₁ r₂ p).obj (op V)) :
    smallEtaleInverseImageRestrict B p p' φ hφ _ e x ∈
      (smallEtaleInverseImagePairCokernelImage B r₁ r₂ p').obj (op V') := by
  obtain ⟨h, rfl⟩ := (mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff B r₁ r₂ p x).1 hx
  rw [smallEtaleInverseImageRestrict_section]
  exact (mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff B r₁ r₂ p' _).2 ⟨_, rfl⟩

end Presentation

section Stages

variable {I : Type u} [SmallCategory I] (D : I ⥤ B.Scheme) (c : Cone D) {i₁ : I}
  (U₁ : SmallEtale B (D.obj i₁).obj (D.obj i₁).property)

/-- The base change `U_a = U₁ ×_{X_{i₁}} X_a` of `U₁` to a stage `a ⟶ i₁`. -/
abbrev etaleStageBaseChange (a : Over i₁) : SmallEtale B (D.obj a.left).obj
    (D.obj a.left).property :=
  (smallEtaleBaseChange B (D.map a.hom)).obj U₁

/-- The base change `U = U₁ ×_{X_{i₁}} X` of `U₁` to the limit. -/
abbrev etaleLimitBaseChange : SmallEtale B c.pt.obj c.pt.property :=
  (smallEtaleBaseChange B (c.π.app i₁)).obj U₁

lemma over_map_left_comp_map_hom {a b : Over i₁} (t : b ⟶ a) :
    D.map t.left ≫ D.map a.hom = D.map b.hom := by
  rw [← D.map_comp, Over.w t]

/-- The comparison `U_b ⟶ X_b ×_{X_a} U_a` for a morphism `b ⟶ a` of stages. -/
abbrev etaleStageBaseChangeTransition {a b : Over i₁} (t : b ⟶ a) :
    etaleStageBaseChange B D U₁ b ⟶
      (smallEtaleBaseChange B (D.map t.left)).obj (etaleStageBaseChange B D U₁ a) :=
  (smallEtaleBaseChange_factoredCompIso B _ _ _ (D.map t.left) (D.map a.hom) (D.map b.hom)
    (over_map_left_comp_map_hom B D t)).inv.app U₁

/-- The comparison `U ⟶ X ×_{X_a} U_a` for a stage `a`. -/
abbrev etaleLimitBaseChangeTransition (a : Over i₁) :
    etaleLimitBaseChange B D c U₁ ⟶
      (smallEtaleBaseChange B (c.π.app a.left)).obj (etaleStageBaseChange B D U₁ a) :=
  (smallEtaleBaseChange_factoredCompIso B _ _ _ (c.π.app a.left) (D.map a.hom) (c.π.app i₁)
    (c.w a.hom)).inv.app U₁

/-- The transition morphism of schemes `U_b ⟶ U_a`. -/
def etaleStageTransition {a b : Over i₁} (t : b ⟶ a) :
    (etaleStageBaseChange B D U₁ b).obj.left ⟶ (etaleStageBaseChange B D U₁ a).obj.left :=
  (etaleStageBaseChangeTransition B D U₁ t).hom.left ≫
    smallEtaleBaseChangePullbackFst B (D.map t.left) (etaleStageBaseChange B D U₁ a)

/-- The projection of schemes `U ⟶ U_a`. -/
def etaleLimitTransition (a : Over i₁) :
    (etaleLimitBaseChange B D c U₁).obj.left ⟶ (etaleStageBaseChange B D U₁ a).obj.left :=
  (etaleLimitBaseChangeTransition B D c U₁ a).hom.left ≫
    smallEtaleBaseChangePullbackFst B (c.π.app a.left) (etaleStageBaseChange B D U₁ a)

@[reassoc]
lemma etaleStageTransition_eq {a b : Over i₁} (t : b ⟶ a) :
    (etaleStageBaseChangeTransition B D U₁ t).hom.left ≫
        smallEtaleBaseChangePullbackFst B (D.map t.left) (etaleStageBaseChange B D U₁ a) =
      etaleStageTransition B D U₁ t :=
  rfl

@[reassoc]
lemma etaleLimitTransition_eq (a : Over i₁) :
    (etaleLimitBaseChangeTransition B D c U₁ a).hom.left ≫
        smallEtaleBaseChangePullbackFst B (c.π.app a.left) (etaleStageBaseChange B D U₁ a) =
      etaleLimitTransition B D c U₁ a :=
  rfl

@[reassoc (attr := simp)]
lemma etaleStageTransition_fst {a b : Over i₁} (t : b ⟶ a) :
    etaleStageTransition B D U₁ t ≫ smallEtaleBaseChangePullbackFst B (D.map a.hom) U₁ =
      smallEtaleBaseChangePullbackFst B (D.map b.hom) U₁ := by
  rw [etaleStageTransition, Category.assoc]
  exact smallEtaleBaseChange_factoredCompIso_inv_fst_fst B _ _ _ _ U₁

@[reassoc (attr := simp)]
lemma etaleStageTransition_hom {a b : Over i₁} (t : b ⟶ a) :
    etaleStageTransition B D U₁ t ≫ (etaleStageBaseChange B D U₁ a).obj.hom =
      (etaleStageBaseChange B D U₁ b).obj.hom ≫ D.map t.left := by
  have := smallEtaleBaseChange_factoredCompIso_inv_fst_hom B _ _ _
      (over_map_left_comp_map_hom B D t) U₁
  rw [← Category.assoc] at this
  exact this

@[reassoc (attr := simp)]
lemma etaleLimitTransition_fst (a : Over i₁) :
    etaleLimitTransition B D c U₁ a ≫ smallEtaleBaseChangePullbackFst B (D.map a.hom) U₁ =
      smallEtaleBaseChangePullbackFst B (c.π.app i₁) U₁ := by
  rw [etaleLimitTransition, Category.assoc]
  exact smallEtaleBaseChange_factoredCompIso_inv_fst_fst B _ _ _ _ U₁

@[reassoc (attr := simp)]
lemma etaleLimitTransition_hom (a : Over i₁) :
    etaleLimitTransition B D c U₁ a ≫ (etaleStageBaseChange B D U₁ a).obj.hom =
      (etaleLimitBaseChange B D c U₁).obj.hom ≫ c.π.app a.left := by
  have := smallEtaleBaseChange_factoredCompIso_inv_fst_hom B _ _ _ (c.w a.hom) U₁
  rw [← Category.assoc] at this
  exact this

lemma etaleStageBaseChange_hom_ext {X : B.Scheme} {a : Over i₁}
    {f g : X ⟶ (etaleStageBaseChange B D U₁ a).obj.left}
    (h₁ : f ≫ smallEtaleBaseChangePullbackFst B (D.map a.hom) U₁ =
      g ≫ smallEtaleBaseChangePullbackFst B (D.map a.hom) U₁)
    (h₂ : f ≫ (etaleStageBaseChange B D U₁ a).obj.hom = g ≫
        (etaleStageBaseChange B D U₁ a).obj.hom) :
    f = g :=
  pullback.hom_ext h₁ h₂

lemma etaleStageTransition_id (a : Over i₁) : etaleStageTransition B D U₁ (𝟙 a) = 𝟙 _ := by
  apply etaleStageBaseChange_hom_ext
  · rw [etaleStageTransition_fst, Category.id_comp]
  · rw [etaleStageTransition_hom, Category.id_comp, Over.id_left, D.map_id, Category.comp_id]

lemma etaleStageTransition_comp {a b m : Over i₁} (t : m ⟶ b) (t' : b ⟶ a) :
    etaleStageTransition B D U₁ (t ≫ t') = etaleStageTransition B D U₁ t
        ≫ etaleStageTransition B D U₁ t' := by
  apply etaleStageBaseChange_hom_ext
  · rw [etaleStageTransition_fst, Category.assoc, etaleStageTransition_fst,
      etaleStageTransition_fst]
  · rw [etaleStageTransition_hom, Category.assoc, etaleStageTransition_hom, ← Category.assoc,
      etaleStageTransition_hom, Category.assoc, Over.comp_left, D.map_comp]

@[reassoc]
lemma etaleLimitTransition_comp_stageTransition {a b : Over i₁} (t : b ⟶ a) :
    etaleLimitTransition B D c U₁ b ≫ etaleStageTransition B D U₁ t =
        etaleLimitTransition B D c U₁ a := by
  apply etaleStageBaseChange_hom_ext
  · rw [Category.assoc, etaleStageTransition_fst, etaleLimitTransition_fst,
      etaleLimitTransition_fst]
  · rw [Category.assoc, etaleStageTransition_hom, ← Category.assoc, etaleLimitTransition_hom,
      etaleLimitTransition_hom, Category.assoc, c.w]

end Stages

section Functor

variable {I : Type u} [SmallCategory I] (D : I ⥤ B.Scheme) (c : Cone D) {i₀ : I}
  {R H : SmallEtale B (D.obj i₀).obj (D.obj i₀).property} (r₁ r₂ : R ⟶ H) {i₁ : I} (g₁ : i₁ ⟶ i₀)
  (U₁ : SmallEtale B (D.obj i₁).obj (D.obj i₁).property)

lemma over_map_left_comp_map_comp {a b : Over i₁} (t : b ⟶ a) :
    D.map t.left ≫ D.map (a.hom ≫ g₁) = D.map (b.hom ≫ g₁) := by
  rw [← D.map_comp, ← Category.assoc, Over.w t]

lemma etaleStageTransition_comp_hom_map {a b : Over i₁} (t : b ⟶ a) :
    etaleStageTransition B D U₁ t ≫ (etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map (a.hom ≫ g₁) =
      (etaleStageBaseChange B D U₁ b).obj.hom ≫ D.map (b.hom ≫ g₁) := by
  rw [← Category.assoc, etaleStageTransition_hom, Category.assoc, over_map_left_comp_map_comp]

lemma etaleLimitTransition_comp_hom_map (a : Over i₁) :
    etaleLimitTransition B D c U₁ a ≫ (etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map (a.hom ≫ g₁) =
      (etaleLimitBaseChange B D c U₁).obj.hom ≫ c.π.app i₀ := by
  rw [← Category.assoc, etaleLimitTransition_hom, Category.assoc, c.w]

/-- The sections `𝒯_a(U_a)` of the presheaf image of `π_a` over `U_a`, for a stage `a ⟶ i₁`. -/
abbrev presheafImageStage (a : Over i₁) : Type (u + 1) :=
  (smallEtaleInverseImagePairCokernelImage B r₁ r₂ (D.map (a.hom ≫ g₁))).obj
    (op (etaleStageBaseChange B D U₁ a))

/-- The sections `𝒯(U)` of the presheaf image of `π_X` over `U`. -/
abbrev presheafImageLimit : Type (u + 1) :=
  (smallEtaleInverseImagePairCokernelImage B r₁ r₂ (c.π.app i₀)).obj
    (op (etaleLimitBaseChange B D c U₁))

/-- Restriction `𝒯_a(U_a) ⟶ 𝒯_b(U_b)` along `U_b ⟶ U_a`, for `b ⟶ a`. -/
def presheafImageStageRestrict {a b : Over i₁} (t : b ⟶ a) :
    presheafImageStage B D r₁ r₂ g₁ U₁ a → presheafImageStage B D r₁ r₂ g₁ U₁ b := fun x =>
  ⟨smallEtaleInverseImageRestrict B (D.map (a.hom ≫ g₁)) (D.map (b.hom ≫ g₁))
      (D.map t.left) (over_map_left_comp_map_comp B D g₁ t) _
      (etaleStageBaseChangeTransition B D U₁ t) x.1,
    smallEtaleInverseImageRestrict_mem B r₁ r₂ _ _ _ _ _ x.2⟩

/-- Restriction `𝒯_a(U_a) ⟶ 𝒯(U)` along `U ⟶ U_a`. -/
def presheafImageLimitRestrict (a : Over i₁) :
    presheafImageStage B D r₁ r₂ g₁ U₁ a → presheafImageLimit B D c r₁ r₂ U₁ := fun x =>
  ⟨smallEtaleInverseImageRestrict B (D.map (a.hom ≫ g₁)) (c.π.app i₀)
      (c.π.app a.left) (c.w _) _ (etaleLimitBaseChangeTransition B D c U₁ a) x.1,
    smallEtaleInverseImageRestrict_mem B r₁ r₂ _ _ _ _ _ x.2⟩

lemma presheafImageStageRestrict_val {a b : Over i₁} (t : b ⟶ a)
    (x : presheafImageStage B D r₁ r₂ g₁ U₁ a) :
    (presheafImageStageRestrict B D r₁ r₂ g₁ U₁ t x).1 =
      smallEtaleInverseImageRestrict B (D.map (a.hom ≫ g₁)) (D.map (b.hom ≫ g₁))
        (D.map t.left) (over_map_left_comp_map_comp B D g₁ t) _
        (etaleStageBaseChangeTransition B D U₁ t) x.1 :=
  rfl

lemma presheafImageLimitRestrict_val (a : Over i₁) (x : presheafImageStage B D r₁ r₂ g₁ U₁ a) :
    (presheafImageLimitRestrict B D c r₁ r₂ g₁ U₁ a x).1 =
      smallEtaleInverseImageRestrict B (D.map (a.hom ≫ g₁)) (c.π.app i₀)
        (c.π.app a.left) (c.w _) _ (etaleLimitBaseChangeTransition B D c U₁ a) x.1 :=
  rfl

lemma presheafImageStageRestrict_section {a b : Over i₁} (t : b ⟶ a)
    (h : etaleStageBaseChange B D U₁ a ⟶ (smallEtaleBaseChange B (D.map (a.hom ≫ g₁))).obj H) (hx) :
    (presheafImageStageRestrict B D r₁ r₂ g₁ U₁ t
        ⟨smallEtaleInverseImageSection B _ _ h (smallEtalePairCokernelUniversalSection B r₁ r₂),
          hx⟩).1 =
      smallEtaleInverseImageSection B _ _
        (etaleStageBaseChangeTransition B D U₁ t ≫ (smallEtaleBaseChange B (D.map t.left)).map h ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ _ _ _ _
            (over_map_left_comp_map_comp B D g₁ t)).hom.app H)
        (smallEtalePairCokernelUniversalSection B r₁ r₂) :=
  smallEtaleInverseImageRestrict_section B _ _ _ _ _ _ _ _

lemma presheafImageLimitRestrict_section (a : Over i₁)
    (h : etaleStageBaseChange B D U₁ a ⟶ (smallEtaleBaseChange B (D.map (a.hom ≫ g₁))).obj H) (hx) :
    (presheafImageLimitRestrict B D c r₁ r₂ g₁ U₁ a
        ⟨smallEtaleInverseImageSection B _ _ h (smallEtalePairCokernelUniversalSection B r₁ r₂),
          hx⟩).1 =
      smallEtaleInverseImageSection B _ _
        (etaleLimitBaseChangeTransition B D c U₁ a ≫ (smallEtaleBaseChange B
            (c.π.app a.left)).map h ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ _ _ _ _ (c.w (a.hom ≫ g₁))).hom.app H)
        (smallEtalePairCokernelUniversalSection B r₁ r₂) :=
  smallEtaleInverseImageRestrict_section B _ _ _ _ _ _ _ _

lemma presheafImageStageRestrict_id (a : Over i₁) (x : presheafImageStage B D r₁ r₂ g₁ U₁ a) :
    presheafImageStageRestrict B D r₁ r₂ g₁ U₁ (𝟙 a) x = x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨h, rfl⟩ := (mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff B r₁ r₂ _ x).1 hx
  apply Subtype.ext
  rw [presheafImageStageRestrict_section]
  apply smallEtaleInverseImageSection_congr
  rw [smallEtaleBaseChangeComponent_transport, etaleStageTransition_eq_assoc,
      etaleStageTransition_id,
    Category.id_comp]

lemma presheafImageStageRestrict_comp {a b m : Over i₁} (t : m ⟶ b) (t' : b ⟶ a)
    (x : presheafImageStage B D r₁ r₂ g₁ U₁ a) :
    presheafImageStageRestrict B D r₁ r₂ g₁ U₁ (t ≫ t') x =
      presheafImageStageRestrict B D r₁ r₂ g₁ U₁ t
        (presheafImageStageRestrict B D r₁ r₂ g₁ U₁ t' x) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨h, rfl⟩ := (mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff B r₁ r₂ _ x).1 hx
  apply Subtype.ext
  have e := presheafImageStageRestrict_section B D r₁ r₂ g₁ U₁ t' h hx
  rw [presheafImageStageRestrict_section, presheafImageStageRestrict_val, e,
    smallEtaleInverseImageRestrict_section]
  apply smallEtaleInverseImageSection_congr
  rw [smallEtaleBaseChangeComponent_transport, smallEtaleBaseChangeComponent_transport,
    smallEtaleBaseChangeComponent_transport, etaleStageTransition_eq_assoc,
        etaleStageTransition_eq_assoc,
    etaleStageTransition_eq_assoc, etaleStageTransition_comp, Category.assoc]

lemma presheafImageLimitRestrict_stageRestrict {a b : Over i₁} (t : b ⟶ a)
    (x : presheafImageStage B D r₁ r₂ g₁ U₁ a) :
    presheafImageLimitRestrict B D c r₁ r₂ g₁ U₁ b
        (presheafImageStageRestrict B D r₁ r₂ g₁ U₁ t x) =
      presheafImageLimitRestrict B D c r₁ r₂ g₁ U₁ a x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨h, rfl⟩ := (mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff B r₁ r₂ _ x).1 hx
  apply Subtype.ext
  have e := presheafImageStageRestrict_section B D r₁ r₂ g₁ U₁ t h hx
  rw [presheafImageLimitRestrict_section, presheafImageLimitRestrict_val, e,
    smallEtaleInverseImageRestrict_section]
  apply smallEtaleInverseImageSection_congr
  rw [smallEtaleBaseChangeComponent_transport, smallEtaleBaseChangeComponent_transport,
    smallEtaleBaseChangeComponent_transport, etaleStageTransition_eq_assoc,
        etaleLimitTransition_eq_assoc,
    etaleLimitTransition_eq_assoc, etaleLimitTransition_comp_stageTransition_assoc]

/-- **The system `α ↦ 𝒯_α(U_α)`.** For a stage `a ⟶ i₁` of the projective system, the sections
over `U_a = U₁ ×_{X_{i₁}} X_a` of the presheaf image `𝒯_a` of
`π_a = p_{a i₀}^* π : p_{a i₀}^* h_H ⟶ 𝒢_a = p_{a i₀}^* 𝒢`, with the restriction maps of the
sheaves `𝒢_a` along `U_b ⟶ U_a`, read through `p_{b a}^* 𝒢_a ≅ 𝒢_b`. -/
@[weil "lem_fk104_presheaf_image_sections_colimit"]
def presheafImageStageSections : (Over i₁)ᵒᵖ ⥤ Type (u + 1) where
  obj a := presheafImageStage B D r₁ r₂ g₁ U₁ a.unop
  map t := TypeCat.ofHom (presheafImageStageRestrict B D r₁ r₂ g₁ U₁ t.unop)
  map_id a := by
    ext x
    exact congrArg Subtype.val (presheafImageStageRestrict_id B D r₁ r₂ g₁ U₁ a.unop x)
  map_comp t t' := by
    ext x
    exact congrArg Subtype.val (presheafImageStageRestrict_comp B D r₁ r₂ g₁ U₁ t'.unop t.unop x)

/-- **The restriction maps `𝒯_α(U_α) ⟶ 𝒯(U)`.** The cocone over `α ↦ 𝒯_α(U_α)` with apex the
sections over `U = U₁ ×_{X_{i₁}} X` of the presheaf image `𝒯` of `π_X = p_{i₀}^* π`, given by
restriction of sections of `𝒢_a` along `U ⟶ U_a`, read through `p_a^* 𝒢_a ≅ 𝒢`. -/
@[weil "lem_fk104_presheaf_image_sections_colimit"]
def presheafImageStageSectionsCocone : Cocone (presheafImageStageSections B D r₁ r₂ g₁ U₁) where
  pt := presheafImageLimit B D c r₁ r₂ U₁
  ι :=
    { app a := TypeCat.ofHom (presheafImageLimitRestrict B D c r₁ r₂ g₁ U₁ a.unop)
      naturality a b t := by
        ext x
        exact presheafImageLimitRestrict_stageRestrict B D c r₁ r₂ g₁ U₁ t.unop x }

end Functor


section Descent

variable {I : Type u} [SmallCategory I] (D : I ⥤ B.Scheme) (c : Cone D) {i₁ : I}
  (U₁ : SmallEtale B (D.obj i₁).obj (D.obj i₁).property)

/-- `U₁` as a scheme over `X_{i₁}`. -/
abbrev etaleStageOver : Over ((D ⋙ B.inclusion).obj i₁) := Over.mk (B.inclusion.map U₁.obj.hom)

/-- The comparison of `U_a` with the stage `X_a ×_{X_{i₁}} U₁` of the diagram of base changes. -/
def etaleStageBaseChangeIso (a : Over i₁) :
    B.inclusion.obj (etaleStageBaseChange B D U₁ a).obj.left ≅
      pullback ((D ⋙ B.inclusion).map a.hom) (etaleStageOver B D U₁).hom :=
  PreservesPullback.iso B.inclusion U₁.obj.hom (D.map a.hom) ≪≫
    pullbackSymmetry (B.inclusion.map U₁.obj.hom) (B.inclusion.map (D.map a.hom))

/-- The comparison of `U` with the apex `X ×_{X_{i₁}} U₁` of the cone of base changes. -/
def etaleLimitBaseChangeIso :
    B.inclusion.obj (etaleLimitBaseChange B D c U₁).obj.left ≅
      pullback ((B.inclusion.mapCone c).π.app i₁) (etaleStageOver B D U₁).hom :=
  PreservesPullback.iso B.inclusion U₁.obj.hom (c.π.app i₁) ≪≫
    pullbackSymmetry (B.inclusion.map U₁.obj.hom) (B.inclusion.map (c.π.app i₁))

@[reassoc]
lemma etaleStageBaseChangeIso_hom_fst (a : Over i₁) :
    (etaleStageBaseChangeIso B D U₁ a).hom ≫
        pullback.fst ((D ⋙ B.inclusion).map a.hom) (etaleStageOver B D U₁).hom =
      B.inclusion.map (etaleStageBaseChange B D U₁ a).obj.hom := by
  have h : (PreservesPullback.iso B.inclusion U₁.obj.hom (D.map a.hom) ≪≫
      pullbackSymmetry (B.inclusion.map U₁.obj.hom) (B.inclusion.map (D.map a.hom))).hom ≫
        pullback.fst (B.inclusion.map (D.map a.hom)) (B.inclusion.map U₁.obj.hom) =
      B.inclusion.map (pullback.snd U₁.obj.hom (D.map a.hom)) := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
      PreservesPullback.iso_hom_snd]
  exact h

@[reassoc]
lemma etaleStageBaseChangeIso_hom_snd (a : Over i₁) :
    (etaleStageBaseChangeIso B D U₁ a).hom ≫
        pullback.snd ((D ⋙ B.inclusion).map a.hom) (etaleStageOver B D U₁).hom =
      B.inclusion.map (smallEtaleBaseChangePullbackFst B (D.map a.hom) U₁) := by
  have h : (PreservesPullback.iso B.inclusion U₁.obj.hom (D.map a.hom) ≪≫
      pullbackSymmetry (B.inclusion.map U₁.obj.hom) (B.inclusion.map (D.map a.hom))).hom ≫
        pullback.snd (B.inclusion.map (D.map a.hom)) (B.inclusion.map U₁.obj.hom) =
      B.inclusion.map (pullback.fst U₁.obj.hom (D.map a.hom)) := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
      PreservesPullback.iso_hom_fst]
  exact h

@[reassoc]
lemma etaleLimitBaseChangeIso_hom_fst :
    (etaleLimitBaseChangeIso B D c U₁).hom ≫
        pullback.fst ((B.inclusion.mapCone c).π.app i₁) (etaleStageOver B D U₁).hom =
      B.inclusion.map (etaleLimitBaseChange B D c U₁).obj.hom := by
  have h : (PreservesPullback.iso B.inclusion U₁.obj.hom (c.π.app i₁) ≪≫
      pullbackSymmetry (B.inclusion.map U₁.obj.hom) (B.inclusion.map (c.π.app i₁))).hom ≫
        pullback.fst (B.inclusion.map (c.π.app i₁)) (B.inclusion.map U₁.obj.hom) =
      B.inclusion.map (pullback.snd U₁.obj.hom (c.π.app i₁)) := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
      PreservesPullback.iso_hom_snd]
  exact h

@[reassoc]
lemma etaleLimitBaseChangeIso_hom_snd :
    (etaleLimitBaseChangeIso B D c U₁).hom ≫
        pullback.snd ((B.inclusion.mapCone c).π.app i₁) (etaleStageOver B D U₁).hom =
      B.inclusion.map (smallEtaleBaseChangePullbackFst B (c.π.app i₁) U₁) := by
  have h : (PreservesPullback.iso B.inclusion U₁.obj.hom (c.π.app i₁) ≪≫
      pullbackSymmetry (B.inclusion.map U₁.obj.hom) (B.inclusion.map (c.π.app i₁))).hom ≫
        pullback.snd (B.inclusion.map (c.π.app i₁)) (B.inclusion.map U₁.obj.hom) =
      B.inclusion.map (pullback.fst U₁.obj.hom (c.π.app i₁)) := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
      PreservesPullback.iso_hom_fst]
  exact h

lemma etaleStageBaseChangeIso_hom_comp_map {a b : Over i₁} (t : b ⟶ a) :
    (etaleStageBaseChangeIso B D U₁ b).hom ≫
        baseChangeTransition ((D ⋙ B.inclusion).map a.hom) ((D ⋙ B.inclusion).map b.hom)
          ((D ⋙ B.inclusion).map t.left) (by rw [← Functor.map_comp, Over.w t])
          (etaleStageOver B D U₁) =
      B.inclusion.map (etaleStageTransition B D U₁ t) ≫ (etaleStageBaseChangeIso B D U₁ a).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, baseChangeTransition_fst,
      ← Category.assoc (etaleStageBaseChangeIso B D U₁ b).hom, etaleStageBaseChangeIso_hom_fst,
      etaleStageBaseChangeIso_hom_fst, ← Functor.map_comp, etaleStageTransition_hom,
          Functor.map_comp]
    rfl
  · rw [Category.assoc, Category.assoc, baseChangeTransition_snd,
      etaleStageBaseChangeIso_hom_snd, etaleStageBaseChangeIso_hom_snd,
      ← Functor.map_comp, etaleStageTransition_fst]

lemma etaleLimitBaseChangeIso_hom_comp_π (a : Over i₁) :
    (etaleLimitBaseChangeIso B D c U₁).hom ≫
        baseChangeTransition ((D ⋙ B.inclusion).map a.hom) ((B.inclusion.mapCone c).π.app i₁)
          ((B.inclusion.mapCone c).π.app a.left) ((B.inclusion.mapCone c).w a.hom)
          (etaleStageOver B D U₁) =
      B.inclusion.map (etaleLimitTransition B D c U₁ a) ≫
          (etaleStageBaseChangeIso B D U₁ a).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, baseChangeTransition_fst,
      ← Category.assoc (etaleLimitBaseChangeIso B D c U₁).hom, etaleLimitBaseChangeIso_hom_fst,
      etaleStageBaseChangeIso_hom_fst, ← Functor.map_comp, etaleLimitTransition_hom,
          Functor.map_comp]
    rfl
  · rw [Category.assoc, Category.assoc, baseChangeTransition_snd,
      etaleLimitBaseChangeIso_hom_snd, etaleStageBaseChangeIso_hom_snd,
      ← Functor.map_comp, etaleLimitTransition_fst]

lemma etaleLimitBaseChangeIso_hom_comp_π_assoc (a : Over i₁) {Z : Scheme.{u}}
    (h : pullback ((D ⋙ B.inclusion).map a.hom) (etaleStageOver B D U₁).hom ⟶ Z) :
    (etaleLimitBaseChangeIso B D c U₁).hom ≫
        baseChangeTransition ((D ⋙ B.inclusion).map a.hom) ((B.inclusion.mapCone c).π.app i₁)
          ((B.inclusion.mapCone c).π.app a.left) ((B.inclusion.mapCone c).w a.hom)
          (etaleStageOver B D U₁) ≫ h =
      B.inclusion.map (etaleLimitTransition B D c U₁ a) ≫ (etaleStageBaseChangeIso B D U₁ a).hom
          ≫ h := by
  have e := etaleLimitBaseChangeIso_hom_comp_π B D c U₁ a
  calc _ = ((etaleLimitBaseChangeIso B D c U₁).hom ≫
        baseChangeTransition ((D ⋙ B.inclusion).map a.hom) ((B.inclusion.mapCone c).π.app i₁)
          ((B.inclusion.mapCone c).π.app a.left) ((B.inclusion.mapCone c).w a.hom)
          (etaleStageOver B D U₁)) ≫ h := (Category.assoc _ _ _).symm
    _ = _ := by rw [e, Category.assoc]

lemma etaleStageBaseChangeIso_hom_comp_map_assoc {a b : Over i₁} (t : b ⟶ a) {Z : Scheme.{u}}
    (h : pullback ((D ⋙ B.inclusion).map a.hom) (etaleStageOver B D U₁).hom ⟶ Z) :
    (etaleStageBaseChangeIso B D U₁ b).hom ≫
        baseChangeTransition ((D ⋙ B.inclusion).map a.hom) ((D ⋙ B.inclusion).map b.hom)
          ((D ⋙ B.inclusion).map t.left) (by rw [← Functor.map_comp, Over.w t])
          (etaleStageOver B D U₁) ≫ h =
      B.inclusion.map (etaleStageTransition B D U₁ t) ≫ (etaleStageBaseChangeIso B D U₁ a).hom
          ≫ h := by
  have e := etaleStageBaseChangeIso_hom_comp_map B D U₁ t
  calc _ = ((etaleStageBaseChangeIso B D U₁ b).hom ≫
        baseChangeTransition ((D ⋙ B.inclusion).map a.hom) ((D ⋙ B.inclusion).map b.hom)
          ((D ⋙ B.inclusion).map t.left) (by rw [← Functor.map_comp, Over.w t])
          (etaleStageOver B D U₁)) ≫ h := (Category.assoc _ _ _).symm
    _ = _ := by rw [e, Category.assoc]

lemma etaleStageBaseChange_fst_hom (a : Over i₁) :
    smallEtaleBaseChangePullbackFst B (D.map a.hom) U₁ ≫ U₁.obj.hom =
      (etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map a.hom :=
  pullback.condition

lemma etaleLimitBaseChange_fst_hom :
    smallEtaleBaseChangePullbackFst B (c.π.app i₁) U₁ ≫ U₁.obj.hom =
      (etaleLimitBaseChange B D c U₁).obj.hom ≫ c.π.app i₁ :=
  pullback.condition

variable {i₀ : I} (g₁ : i₁ ⟶ i₀)

/-- The structure morphism `X_a ×_{X_{i₁}} U₁ ⟶ X_{i₀}` of the diagram of base changes. -/
abbrev etaleStageStructureMap :
    baseChangeDiagram (D ⋙ B.inclusion) i₁ (etaleStageOver B D U₁) ⟶
      (Functor.const (Over i₁)).obj ((D ⋙ B.inclusion).obj i₀) :=
  baseChangeStructureMap (D ⋙ B.inclusion) i₁ (etaleStageOver B D U₁) ≫
    (Functor.const (Over i₁)).map ((D ⋙ B.inclusion).map g₁)

lemma etaleStageBaseChangeIso_hom_comp_structureMap (a : Over i₁) :
    (etaleStageBaseChangeIso B D U₁ a).hom ≫
        ((pullback.snd ((D ⋙ B.inclusion).map a.hom) (etaleStageOver B D U₁).hom ≫
          (etaleStageOver B D U₁).hom) ≫ (D ⋙ B.inclusion).map g₁) =
      B.inclusion.map ((etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map (a.hom ≫ g₁)) := by
  change (etaleStageBaseChangeIso B D U₁ a).hom ≫
      (pullback.snd ((D ⋙ B.inclusion).map a.hom) (etaleStageOver B D U₁).hom ≫
        B.inclusion.map U₁.obj.hom) ≫ B.inclusion.map (D.map g₁) = _
  rw [← Category.assoc, ← Category.assoc, etaleStageBaseChangeIso_hom_snd, ← Functor.map_comp,
    ← Functor.map_comp, etaleStageBaseChange_fst_hom, Category.assoc, ← D.map_comp]

variable [IsCofiltered I] (hlim : IsLimit (B.inclusion.mapCone c))
  (haff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ B.inclusion).map f))
  [CompactSpace (B.inclusion.obj U₁.obj.left)]

include hlim haff in
/-- **Morphisms out of `U` come from a stage** (Stacks 01ZC, FK I.4.16 2), surjectivity): an
`X_{i₀}`-morphism from `U` to a scheme `W` locally of finite presentation over `X_{i₀}` factors
through `U ⟶ U_a` for some stage `a`. -/
theorem exists_etaleStage_etaleLimitTransition_comp_eq [QuasiSeparatedSpace
    (B.inclusion.obj U₁.obj.left)]
    {W : Scheme.{u}} (q : W ⟶ (D ⋙ B.inclusion).obj i₀) [LocallyOfFinitePresentation q]
    (k : B.inclusion.obj (etaleLimitBaseChange B D c U₁).obj.left ⟶ W)
    (hk : k ≫ q = B.inclusion.map ((etaleLimitBaseChange B D c U₁).obj.hom ≫ c.π.app i₀)) :
    ∃ (a : Over i₁) (g : B.inclusion.obj (etaleStageBaseChange B D U₁ a).obj.left ⟶ W),
      B.inclusion.map (etaleLimitTransition B D c U₁ a) ≫ g = k ∧
        g ≫ q = B.inclusion.map ((etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map (a.hom ≫ g₁)) := by
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ B.inclusion).map f) := haff
  have : CompactSpace (etaleStageOver B D U₁).left :=
    inferInstanceAs (CompactSpace (B.inclusion.obj U₁.obj.left))
  have : QuasiSeparatedSpace (etaleStageOver B D U₁).left :=
    inferInstanceAs (QuasiSeparatedSpace (B.inclusion.obj U₁.obj.left))
  have : ∀ {a b : Over i₁} (e : a ⟶ b),
      IsAffineHom ((baseChangeDiagram (D ⋙ B.inclusion) i₁ (etaleStageOver B D U₁)).map e) :=
    fun e => isAffineHom_baseChangeDiagram_map _ _ _ e
  have : ∀ a, CompactSpace ((baseChangeDiagram (D ⋙ B.inclusion) i₁
      (etaleStageOver B D U₁)).obj a) :=
    fun a => compactSpace_baseChangeDiagram_obj _ _ _ a
  have : ∀ a, QuasiSeparatedSpace
      ((baseChangeDiagram (D ⋙ B.inclusion) i₁ (etaleStageOver B D U₁)).obj a) :=
    fun a => quasiSeparatedSpace_baseChangeDiagram_obj _ _ _ a
  obtain ⟨a, g', hg'₁, hg'₂⟩ := Scheme.exists_π_app_comp_eq_of_essentiallySmall _ _
    (baseChangeConeIsLimit (D ⋙ B.inclusion) hlim i₁ (etaleStageOver B D U₁))
    (etaleStageStructureMap B D U₁ g₁) q ((etaleLimitBaseChangeIso B D c U₁).inv ≫ k) (by
      refine NatTrans.ext (funext fun a => ?_)
      have e : (etaleLimitBaseChangeIso B D c U₁).hom ≫
          (baseChangeTransition ((D ⋙ B.inclusion).map a.hom) ((B.inclusion.mapCone c).π.app i₁)
            ((B.inclusion.mapCone c).π.app a.left) ((B.inclusion.mapCone c).w a.hom)
            (etaleStageOver B D U₁) ≫ ((pullback.snd ((D ⋙ B.inclusion).map a.hom)
              (etaleStageOver B D U₁).hom ≫ (etaleStageOver B D U₁).hom) ≫
                  (D ⋙ B.inclusion).map g₁)) =
          (etaleLimitBaseChangeIso B D c U₁).hom ≫ (((etaleLimitBaseChangeIso B D c U₁).inv ≫ k)
              ≫ q) := by
        rw [etaleLimitBaseChangeIso_hom_comp_π_assoc,
          etaleStageBaseChangeIso_hom_comp_structureMap, Category.assoc, Iso.hom_inv_id_assoc, hk,
          ← Functor.map_comp]
        congr 1
        rw [← Category.assoc, etaleLimitTransition_hom, Category.assoc, c.w]
      exact (cancel_epi (etaleLimitBaseChangeIso B D c U₁).hom).1 e)
  refine ⟨a, (etaleStageBaseChangeIso B D U₁ a).hom ≫ g', ?_, ?_⟩
  · have e := etaleLimitBaseChangeIso_hom_comp_π B D c U₁ a
    have e' : (baseChangeTransition ((D ⋙ B.inclusion).map a.hom)
        ((B.inclusion.mapCone c).π.app i₁) ((B.inclusion.mapCone c).π.app a.left)
        ((B.inclusion.mapCone c).w a.hom) (etaleStageOver B D U₁)) ≫ g' =
          (etaleLimitBaseChangeIso B D c U₁).inv ≫ k := hg'₁
    exact (etaleLimitBaseChangeIso_hom_comp_π_assoc B D c U₁ a g').symm.trans
      ((congrArg ((etaleLimitBaseChangeIso B D c U₁).hom ≫ ·) e').trans (Iso.hom_inv_id_assoc _ _))
  · exact (Category.assoc _ _ _).trans ((congrArg ((etaleStageBaseChangeIso B D U₁ a).hom
      ≫ ·) hg'₂).trans
      (etaleStageBaseChangeIso_hom_comp_structureMap B D U₁ g₁ a))

include hlim haff in
/-- **Equalities of morphisms descend** (Stacks 01ZC, FK I.4.16 2), injectivity): two
`X_{i₀}`-morphisms from `U_a` to a scheme `W` locally of finite type over `X_{i₀}` which agree
on `U` already agree on `U_b` for some stage `b ⟶ a`. -/
theorem exists_etaleStageTransition_comp_eq {a : Over i₁} {W : Scheme.{u}}
    (q : W ⟶ (D ⋙ B.inclusion).obj i₀) [LocallyOfFiniteType q]
    (α β : B.inclusion.obj (etaleStageBaseChange B D U₁ a).obj.left ⟶ W)
    (hα : α ≫ q = B.inclusion.map ((etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map (a.hom ≫ g₁)))
    (hβ : β ≫ q = B.inclusion.map ((etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map (a.hom ≫ g₁)))
    (hab : B.inclusion.map (etaleLimitTransition B D c U₁ a) ≫ α =
      B.inclusion.map (etaleLimitTransition B D c U₁ a) ≫ β) :
    ∃ (b : Over i₁) (t : b ⟶ a), B.inclusion.map (etaleStageTransition B D U₁ t) ≫ α =
      B.inclusion.map (etaleStageTransition B D U₁ t) ≫ β := by
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ B.inclusion).map f) := haff
  have : CompactSpace (etaleStageOver B D U₁).left :=
    inferInstanceAs (CompactSpace (B.inclusion.obj U₁.obj.left))
  have : ∀ {a b : Over i₁} (e : a ⟶ b),
      IsAffineHom ((baseChangeDiagram (D ⋙ B.inclusion) i₁ (etaleStageOver B D U₁)).map e) :=
    fun e => isAffineHom_baseChangeDiagram_map _ _ _ e
  have : ∀ a, CompactSpace ((baseChangeDiagram (D ⋙ B.inclusion) i₁
      (etaleStageOver B D U₁)).obj a) :=
    fun a => compactSpace_baseChangeDiagram_obj _ _ _ a
  have hs (γ : B.inclusion.obj (etaleStageBaseChange B D U₁ a).obj.left ⟶ W)
      (hγ : γ ≫ q = B.inclusion.map ((etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map (a.hom
          ≫ g₁))) :
      (etaleStageStructureMap B D U₁ g₁).app a = ((etaleStageBaseChangeIso B D U₁ a).inv ≫ γ)
          ≫ q := by
    refine (cancel_epi (etaleStageBaseChangeIso B D U₁ a).hom).1 ?_
    refine (etaleStageBaseChangeIso_hom_comp_structureMap B D U₁ g₁ a).trans (hγ.symm.trans ?_)
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  have hπ (γ : B.inclusion.obj (etaleStageBaseChange B D U₁ a).obj.left ⟶ W) :
      (etaleLimitBaseChangeIso B D c U₁).hom ≫
        (baseChangeTransition ((D ⋙ B.inclusion).map a.hom) ((B.inclusion.mapCone c).π.app i₁)
          ((B.inclusion.mapCone c).π.app a.left) ((B.inclusion.mapCone c).w a.hom)
          (etaleStageOver B D U₁) ≫ (etaleStageBaseChangeIso B D U₁ a).inv ≫ γ) =
        B.inclusion.map (etaleLimitTransition B D c U₁ a) ≫ γ :=
    (etaleLimitBaseChangeIso_hom_comp_π_assoc B D c U₁ a _).trans
      (congrArg (B.inclusion.map (etaleLimitTransition B D c U₁ a) ≫ ·) (Iso.hom_inv_id_assoc _ _))
  obtain ⟨b, t, ht⟩ := Scheme.exists_hom_comp_eq_comp_of_essentiallySmall _ _
    (baseChangeConeIsLimit (D ⋙ B.inclusion) hlim i₁ (etaleStageOver B D U₁))
    (etaleStageStructureMap B D U₁ g₁) q ((etaleStageBaseChangeIso B D U₁ a).inv ≫ α)
    ((etaleStageBaseChangeIso B D U₁ a).inv ≫ β) (hs α hα) (hs β hβ)
    ((cancel_epi (etaleLimitBaseChangeIso B D c U₁).hom).1 ((hπ α).trans (hab.trans (hπ β).symm)))
  have hm (γ : B.inclusion.obj (etaleStageBaseChange B D U₁ a).obj.left ⟶ W) :
      (etaleStageBaseChangeIso B D U₁ b).hom ≫
        (baseChangeTransition ((D ⋙ B.inclusion).map a.hom) ((D ⋙ B.inclusion).map b.hom)
          ((D ⋙ B.inclusion).map t.left) (by rw [← Functor.map_comp, Over.w t])
          (etaleStageOver B D U₁) ≫ (etaleStageBaseChangeIso B D U₁ a).inv ≫ γ) =
        B.inclusion.map (etaleStageTransition B D U₁ t) ≫ γ :=
    (etaleStageBaseChangeIso_hom_comp_map_assoc B D U₁ t _).trans
      (congrArg (B.inclusion.map (etaleStageTransition B D U₁ t) ≫ ·) (Iso.hom_inv_id_assoc _ _))
  exact ⟨b, t, (hm α).symm.trans ((congrArg ((etaleStageBaseChangeIso B D U₁ b).hom ≫ ·) ht).trans
    (hm β))⟩

end Descent

section Main

variable {I : Type u} [SmallCategory I] (D : I ⥤ B.Scheme) (c : Cone D) {i₀ : I}
  {R H : SmallEtale B (D.obj i₀).obj (D.obj i₀).property} (r₁ r₂ : R ⟶ H) {i₁ : I} (g₁ : i₁ ⟶ i₀)
  (U₁ : SmallEtale B (D.obj i₁).obj (D.obj i₁).property)

/-- **The sections of the presheaf images along a projective system** (Freitag–Kiehl, proof of
I.4.17 2), claim a)). Let `X = lim X_α` be a projective system of schemes with limit, `α₀` an
index, `r₁, r₂ : R ⇉ H` morphisms of étale `X_{α₀}`-schemes representing an equivalence relation,
`𝒢 = Coker(h_R ⇉ h_H)` with its canonical map `π`, and `𝒯_α ⊆ 𝒢_α = p_{α α₀}^* 𝒢`,
`𝒯 ⊆ p_{α₀}^* 𝒢` the presheaf images of the inverse images of `π`. For `α₁ ≥ α₀` and a
quasi-compact quasi-separated étale `X_{α₁}`-scheme `U₁` with base changes `U_α` (`α ≥ α₁`) and
`U`, the restriction maps induce a bijection `colim_{α ≥ α₁} 𝒯_α(U_α) ≅ 𝒯(U)`: the cocone
`presheafImageStageSectionsCocone` is a colimit cocone. -/
@[weil "lem_fk104_presheaf_image_sections_colimit"]
theorem nonempty_isColimit_presheafImageStageSectionsCocone
    (hX : IsProjectiveSystemWithLimit (D ⋙ B.inclusion) (B.inclusion.mapCone c))
    (hrel : IsEquivalenceRelation ((smallEtaleYoneda B (D.obj i₀).obj (D.obj i₀).property).map r₁)
      ((smallEtaleYoneda B (D.obj i₀).obj (D.obj i₀).property).map r₂))
    [CompactSpace (B.inclusion.obj U₁.obj.left)]
    [QuasiSeparatedSpace (B.inclusion.obj U₁.obj.left)] :
    Nonempty (IsColimit (presheafImageStageSectionsCocone B D c r₁ r₂ g₁ U₁)) := by
  have := hX.isCofiltered
  have haff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ B.inclusion).map f) :=
    fun f => hX.isAffineHom_map f
  obtain ⟨hlim⟩ := hX.nonempty_isLimit
  have : IsEquivalenceRelation r₁ r₂ :=
      (isEquivalenceRelation_smallEtaleYoneda_map_iff r₁ r₂).1 hrel
  have : IsEquivalenceRelation ((smallEtaleBaseChange B (c.π.app i₀)).map r₁)
      ((smallEtaleBaseChange B (c.π.app i₀)).map r₂) :=
    isEquivalenceRelation_smallEtaleBaseChange B _ r₁ r₂
  have : Etale (B.inclusion.map H.obj.hom) := H.property
  have : Etale (B.inclusion.map R.obj.hom) := R.property
  let ι := B.inclusion
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨h, rfl⟩ := (mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff B r₁ r₂ _ x).1 hx
    obtain ⟨a, g, hg₁, hg₂⟩ := exists_etaleStage_etaleLimitTransition_comp_eq B D c U₁ g₁ hlim haff
      (ι.map H.obj.hom) (ι.map (smallEtaleBaseChangeComponent B _ h)) (by
        rw [← Functor.map_comp, smallEtaleBaseChangeComponent_comp_hom])
    have hg₀ : ι.preimage g ≫ H.obj.hom =
        (etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map (a.hom ≫ g₁) :=
      ι.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hg₂])
    refine ⟨op a, ⟨_, (mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff B r₁ r₂ _ _).2
      ⟨smallEtaleBaseChangeHomOfComponent B _ (ι.preimage g) hg₀, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change _ = (presheafImageLimitRestrict B D c r₁ r₂ g₁ U₁ a ⟨_, _⟩).1
    rw [presheafImageLimitRestrict_section]
    apply smallEtaleInverseImageSection_congr
    rw [smallEtaleBaseChangeComponent_transport, etaleLimitTransition_eq_assoc,
      smallEtaleBaseChangeComponent_homOfComponent]
    apply ι.map_injective
    rw [Functor.map_comp ι (etaleLimitTransition B D c U₁ a), Functor.map_preimage, hg₁]
  · intro i
    induction i using Opposite.rec with | op a => ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨h, rfl⟩ := (mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff B r₁ r₂ _ x).1 hx
    obtain ⟨h', rfl⟩ := (mem_range_smallEtaleInverseImage_map_pairCokernelπ_iff B r₁ r₂ _ y).1 hy
    have hxy' := congrArg Subtype.val hxy
    change (presheafImageLimitRestrict B D c r₁ r₂ g₁ U₁ a ⟨_, hx⟩).1 =
      (presheafImageLimitRestrict B D c r₁ r₂ g₁ U₁ a ⟨_, hy⟩).1 at hxy'
    rw [presheafImageLimitRestrict_section, presheafImageLimitRestrict_section] at hxy'
    obtain ⟨ρ, hρ₁, hρ₂⟩ :=
      (smallEtaleInverseImageSection_universalSection_eq_iff B r₁ r₂ (c.π.app i₀) _ _).1 hxy'
    have c₁ : smallEtaleBaseChangeComponent B _ ρ ≫ r₁.hom.left =
        etaleLimitTransition B D c U₁ a ≫ smallEtaleBaseChangeComponent B _ h := by
      rw [← smallEtaleBaseChangeComponent_comp_map, hρ₁, smallEtaleBaseChangeComponent_transport,
        etaleLimitTransition_eq_assoc]
    have c₂ : smallEtaleBaseChangeComponent B _ ρ ≫ r₂.hom.left =
        etaleLimitTransition B D c U₁ a ≫ smallEtaleBaseChangeComponent B _ h' := by
      rw [← smallEtaleBaseChangeComponent_comp_map, hρ₂, smallEtaleBaseChangeComponent_transport,
        etaleLimitTransition_eq_assoc]
    have hhH := smallEtaleBaseChangeComponent_comp_hom B _ h
    have hhH' := smallEtaleBaseChangeComponent_comp_hom B _ h'
    have hr₁ : r₁.hom.left ≫ H.obj.hom = R.obj.hom := Over.w r₁.hom
    have hr₂ : r₂.hom.left ≫ H.obj.hom = R.obj.hom := Over.w r₂.hom
    obtain ⟨b, gR, hgR₁, hgR₂⟩ :=
        exists_etaleStage_etaleLimitTransition_comp_eq B D c U₁ g₁ hlim haff
      (ι.map R.obj.hom) (ι.map (smallEtaleBaseChangeComponent B _ ρ)) (by
        rw [← Functor.map_comp, smallEtaleBaseChangeComponent_comp_hom])
    let m := IsCofiltered.min a b
    let ma : m ⟶ a := IsCofiltered.minToLeft a b
    let mb : m ⟶ b := IsCofiltered.minToRight a b
    have hβ (n : Over i₁) (t : n ⟶ b) (r : R ⟶ H) (hr : r.hom.left ≫ H.obj.hom = R.obj.hom) :
        (ι.map (etaleStageTransition B D U₁ t) ≫ gR ≫ ι.map r.hom.left) ≫ ι.map H.obj.hom =
          ι.map ((etaleStageBaseChange B D U₁ n).obj.hom ≫ D.map (n.hom ≫ g₁)) := by
      rw [Category.assoc, Category.assoc, ← Functor.map_comp, hr, hgR₂, ← Functor.map_comp,
        etaleStageTransition_comp_hom_map]
    have hα (n : Over i₁) (t : n ⟶ a) (k : (etaleStageBaseChange B D U₁ a).obj.left ⟶ H.obj.left)
        (hk : k ≫ H.obj.hom = (etaleStageBaseChange B D U₁ a).obj.hom ≫ D.map (a.hom ≫ g₁)) :
        ι.map (etaleStageTransition B D U₁ t ≫ k) ≫ ι.map H.obj.hom =
          ι.map ((etaleStageBaseChange B D U₁ n).obj.hom ≫ D.map (n.hom ≫ g₁)) := by
      rw [← Functor.map_comp, Category.assoc, hk, etaleStageTransition_comp_hom_map]
    obtain ⟨n₁, t₁, ht₁⟩ := exists_etaleStageTransition_comp_eq B D c U₁ g₁ hlim haff
      (ι.map H.obj.hom)
      (ι.map (etaleStageTransition B D U₁ ma ≫ smallEtaleBaseChangeComponent B _ h))
      (ι.map (etaleStageTransition B D U₁ mb) ≫ gR ≫ ι.map r₁.hom.left)
      (hα m ma _ hhH) (hβ m mb r₁ hr₁) (by
        rw [← Functor.map_comp, etaleLimitTransition_comp_stageTransition_assoc, ← c₁,
          ← Category.assoc, ← Functor.map_comp, etaleLimitTransition_comp_stageTransition,
          ← Category.assoc (B.inclusion.map (etaleLimitTransition B D c U₁ b)) gR, hgR₁,
          ← Functor.map_comp])
    obtain ⟨n₂, t₂, ht₂⟩ := exists_etaleStageTransition_comp_eq B D c U₁ g₁ hlim haff
      (ι.map H.obj.hom)
      (ι.map (etaleStageTransition B D U₁ (t₁ ≫ ma) ≫ smallEtaleBaseChangeComponent B _ h'))
      (ι.map (etaleStageTransition B D U₁ (t₁ ≫ mb)) ≫ gR ≫ ι.map r₂.hom.left)
      (hα n₁ (t₁ ≫ ma) _ hhH') (hβ n₁ (t₁ ≫ mb) r₂ hr₂) (by
        rw [← Functor.map_comp, etaleLimitTransition_comp_stageTransition_assoc, ← c₂,
          ← Category.assoc, ← Functor.map_comp, etaleLimitTransition_comp_stageTransition,
          ← Category.assoc (B.inclusion.map (etaleLimitTransition B D c U₁ b)) gR, hgR₁,
          ← Functor.map_comp])
    have hρn : ι.preimage (ι.map (etaleStageTransition B D U₁ (t₂ ≫ t₁ ≫ mb)) ≫ gR) ≫ R.obj.hom =
        (etaleStageBaseChange B D U₁ n₂).obj.hom ≫ D.map (n₂.hom ≫ g₁) := by
      apply ι.map_injective
      rw [Functor.map_comp, Functor.map_preimage, Category.assoc, hgR₂, ← Functor.map_comp,
        etaleStageTransition_comp_hom_map]
    let ρn := smallEtaleBaseChangeHomOfComponent B (D.map (n₂.hom ≫ g₁)) _ hρn
    have E₁ : ι.map (etaleStageTransition B D U₁ (t₂ ≫ t₁ ≫ mb)) ≫ gR ≫ ι.map r₁.hom.left =
        ι.map (etaleStageTransition B D U₁ (t₂ ≫ t₁ ≫ ma)
            ≫ smallEtaleBaseChangeComponent B _ h) := by
      simp only [etaleStageTransition_comp, Functor.map_comp, Category.assoc] at ht₁ ⊢
      rw [ht₁]
    have E₂ : ι.map (etaleStageTransition B D U₁ (t₂ ≫ t₁ ≫ mb)) ≫ gR ≫ ι.map r₂.hom.left =
        ι.map (etaleStageTransition B D U₁ (t₂ ≫ t₁ ≫ ma)
            ≫ smallEtaleBaseChangeComponent B _ h') := by
      simp only [etaleStageTransition_comp, Functor.map_comp, Category.assoc] at ht₂ ⊢
      rw [ht₂]
    refine ⟨op n₂, (t₂ ≫ t₁ ≫ ma).op, ?_⟩
    apply Subtype.ext
    change (presheafImageStageRestrict B D r₁ r₂ g₁ U₁ (t₂ ≫ t₁ ≫ ma) ⟨_, hx⟩).1 =
      (presheafImageStageRestrict B D r₁ r₂ g₁ U₁ (t₂ ≫ t₁ ≫ ma) ⟨_, hy⟩).1
    rw [presheafImageStageRestrict_section, presheafImageStageRestrict_section]
    calc _ = smallEtaleInverseImageSection B _ _ (ρn ≫ (smallEtaleBaseChange B _).map r₁)
          (smallEtalePairCokernelUniversalSection B r₁ r₂) := by
          apply smallEtaleInverseImageSection_congr
          rw [smallEtaleBaseChangeComponent_transport, etaleStageTransition_eq_assoc,
            smallEtaleBaseChangeComponent_comp_map, smallEtaleBaseChangeComponent_homOfComponent]
          apply ι.map_injective
          rw [Functor.map_comp ι (ι.preimage _) r₁.hom.left, Functor.map_preimage, Category.assoc,
            E₁]
      _ = smallEtaleInverseImageSection B _ _ (ρn ≫ (smallEtaleBaseChange B _).map r₂)
          (smallEtalePairCokernelUniversalSection B r₁ r₂) :=
        smallEtaleInverseImageSection_universalSection_comp_eq B r₁ r₂ _ ρn
      _ = _ := by
          apply smallEtaleInverseImageSection_congr
          rw [smallEtaleBaseChangeComponent_transport, etaleStageTransition_eq_assoc,
            smallEtaleBaseChangeComponent_comp_map, smallEtaleBaseChangeComponent_homOfComponent]
          apply ι.map_injective
          rw [Functor.map_comp ι (ι.preimage _) r₂.hom.left, Functor.map_preimage, Category.assoc,
            E₂]

end Main

end AlgebraicGeometry
