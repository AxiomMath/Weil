module

public import StacksFrontier.CategoryTheory.Sites.SectionGluingByZero
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Weil.AlgebraicGeometry.Morphisms.FlatMono
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Pushforward
public import Weil.Attr
public import Weil.AlgebraicGeometry.Sites.EtaleHomExt

/-!
# Existence and uniqueness of the canonical homomorphism `f_! F ⟶ g_* (j_! F)`

Let `j : X ⟶ Z` be an open immersion and `g : Z ⟶ Y` a separated morphism such that
`f = j ≫ g` is étale, and let `F` be a sheaf of `Λ`-modules on the small étale site of `X`.
There is exactly one canonical homomorphism `c : f_! F ⟶ g_* (j_! F)` for `(j, g, F)`
(`AlgebraicGeometry.IsCanonicalExtensionByZeroToPushforward`).

For an étale `φ : U ⟶ X` the graph `γ_φ : U ⟶ U ×_Y Z` is an open and closed immersion, so
`U ×_Y Z` is the disjoint union of the image `W_φ` of `γ_φ` and its complement `W'_φ`, and
every decomposition as in the definition of a canonical homomorphism is this one. As `j_! F` is
a sheaf, a section over `U ×_Y Z` is determined by its restrictions along `γ_φ` and to
`W'_φ`, and the pair `([φ, s], 0)` glues to a section `σ_φ(s)`. The base change of a morphism
`v : U' ⟶ U` pulls the graph of `φ` back to the graph of `φ ∘ v`, so the `σ_φ` are compatible
with restriction and form a morphism `F ⟶ f^{-1} g_* (j_! F)`. Its transpose under the
adjunction `f_! ⊣ f^{-1}` is the canonical homomorphism, and a morphism `f_! F ⟶ g_* (j_! F)`
is canonical exactly when its transpose is this morphism, which gives uniqueness.

## Main results

* `AlgebraicGeometry.existsUnique_isCanonicalExtensionByZeroToPushforward`: there is exactly
  one canonical homomorphism `f_! F ⟶ g_* (j_! F)`.

## Implementation notes

The source assumes `Z` separated; only the separatedness of `g` is used, and without it the
graph need not be closed. The source builds the canonical homomorphism from a morphism out of
the presheaf `P_f F` and the universal property of sheafification; here the same sections
`σ_φ(s)` define the transposed morphism `F ⟶ f^{-1} g_* (j_! F)` directly, and the adjunction
`f_! ⊣ f^{-1}` (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroAdj`) replaces the two
universal properties, the generators `[φ, s]` of `f_! F` being the images of the unit.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8, p. 85.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology

universe r u

namespace AlgebraicGeometry

section Graph

variable {U U' Y Z : Scheme.{u}} (a : U ⟶ Y) (g : Z ⟶ Y) (h : U ⟶ Z) (hh : h ≫ g = a)
  (v : U' ⟶ U) (a' : U' ⟶ Y) (h' : U' ⟶ Z) (ha : v ≫ a = a') (hv : v ≫ h = h')

private theorem lift_comp_eq_comp_lift (b : pullback a' g ⟶ pullback a g)
    (hb₁ : b ≫ pullback.fst a g = pullback.fst a' g ≫ v)
    (hb₂ : b ≫ pullback.snd a g = pullback.snd a' g) :
    (pullback.lift (𝟙 U') h' (by simp [← ha, ← hv, hh]) : U' ⟶ pullback a' g) ≫ b =
      v ≫ pullback.lift (𝟙 U) h (by simp [hh]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, hb₁, pullback.lift_fst_assoc, pullback.lift_fst,
      Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, hb₂, pullback.lift_snd, hv]

/-- The preimage of the graph of `h : U ⟶ Z` under the base change `U' ×_Y Z ⟶ U ×_Y Z` of
`v : U' ⟶ U` is the graph of `v ≫ h`. -/
private theorem preimage_range_graph (b : pullback a' g ⟶ pullback a g)
    (hb₁ : b ≫ pullback.fst a g = pullback.fst a' g ≫ v)
    (hb₂ : b ≫ pullback.snd a g = pullback.snd a' g) :
    b ⁻¹' Set.range (pullback.lift (𝟙 U) h (by simp [hh])) =
      Set.range (pullback.lift (𝟙 U') h' (by simp [← ha, ← hv, hh]) :
        U' ⟶ pullback a' g) := by
  subst ha hv
  have sq₁ : IsPullback b (pullback.fst (v ≫ a) g) (pullback.fst a g) v :=
    IsPullback.of_right (h₁₂ := pullback.snd a g) (v₁₃ := g) (h₂₂ := a)
      (by rw [hb₂]; exact (IsPullback.of_hasPullback (v ≫ a) g).flip) hb₁
      (IsPullback.of_hasPullback a g).flip
  have sq₂ : IsPullback (pullback.lift (𝟙 U') (v ≫ h) (by simp [hh]) :
        U' ⟶ pullback (v ≫ a) g) v b (pullback.lift (𝟙 U) h (by simp [hh])) :=
    IsPullback.of_right (h₁₂ := pullback.fst (v ≫ a) g) (v₁₃ := v) (h₂₂ := pullback.fst a g)
      (by rw [pullback.lift_fst, pullback.lift_fst]; exact IsPullback.id_horiz v)
      (lift_comp_eq_comp_lift a g h hh v _ _ rfl rfl b hb₁ hb₂) sq₁.flip
  have hsurj : Function.Surjective sq₂.isoPullback.hom :=
    sq₂.isoPullback.hom.homeomorph.surjective
  rw [← sq₂.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hsurj.range_eq, Set.image_univ, Scheme.Pullback.range_fst]

private theorem baseChange_map_left_fst {Z Y : Scheme.{u}} (g : Z ⟶ Y) {V V' : Y.Etale}
    (m : V' ⟶ V) :
    ((smallEtaleBaseChange g).map m).left ≫ pullback.fst V.hom g =
      pullback.fst V'.hom g ≫ m.left :=
  pullback.lift_fst _ _ _

private theorem baseChange_map_left_snd {Z Y : Scheme.{u}} (g : Z ⟶ Y) {V V' : Y.Etale}
    (m : V' ⟶ V) :
    ((smallEtaleBaseChange g).map m).left ≫ pullback.snd V.hom g = pullback.snd V'.hom g :=
  pullback.lift_snd _ _ _

end Graph

open Scheme.Etale

section Construction

variable {X Z Y : Scheme.{u}} (j : X ⟶ Z) (g : Z ⟶ Y) (f : X ⟶ Y)
  [IsOpenImmersion j] [Etale f] [IsSeparated g] (fac : j ≫ g = f)

private theorem isOpenImmersion_and_isClosedImmersion_graphToBaseChange_left (U : X.Etale) :
    IsOpenImmersion (graphToBaseChange j g f fac U).left ∧
      IsClosedImmersion (graphToBaseChange j g f fac U).left := by
  subst fac
  have : Etale U.hom := U.prop
  rw [graphToBaseChange_left]
  exact isOpenImmersion_and_isClosedImmersion_pullbackLift_id_of_eq j g U.hom _
    (Category.assoc _ _ _).symm _

/-- The image of the graph `γ_φ`, an open subscheme of `U ×_Y Z`. -/
private def graphOpens (U : X.Etale) :
    ((smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U)).left.Opens :=
  have := (isOpenImmersion_and_isClosedImmersion_graphToBaseChange_left j g f fac U).1
  (graphToBaseChange j g f fac U).left.opensRange

/-- The complement of the image of the graph `γ_φ`, an open subscheme of `U ×_Y Z`. -/
private def graphComplOpens (U : X.Etale) :
    ((smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U)).left.Opens :=
  ⟨(Set.range (graphToBaseChange j g f fac U).left)ᶜ, by
    have := (isOpenImmersion_and_isClosedImmersion_graphToBaseChange_left j g f fac U).2
    exact (graphToBaseChange j g f fac U).left.isClosedEmbedding.isClosed_range.isOpen_compl⟩

private theorem isCompl_graphOpens_graphComplOpens (U : X.Etale) :
    IsCompl (graphOpens j g f fac U) (graphComplOpens j g f fac U) := by
  constructor
  · rw [disjoint_iff, ← SetLike.coe_set_eq]
    exact Set.inter_compl_self _
  · rw [codisjoint_iff, ← SetLike.coe_set_eq]
    exact Set.union_compl_self _

private instance mono_graphToBaseChange (U : X.Etale) : Mono (graphToBaseChange j g f fac U) :=
  have := (isOpenImmersion_and_isClosedImmersion_graphToBaseChange_left j g f fac U).1
  ⟨fun _ _ h ↦ Scheme.Etale.hom_ext ((cancel_mono (graphToBaseChange j g f fac U).left).1
    (congrArg (fun k ↦ k.left) h))⟩

private instance mono_ofOpensι {T : Z.Etale} (W : T.left.Opens) : Mono (ofOpensι T W) :=
  ⟨fun _ _ h ↦ Scheme.Etale.hom_ext ((cancel_mono W.ι).1 (congrArg (fun k ↦ k.left) h))⟩

private theorem ofTwoArrows_mem (U : X.Etale) :
    Sieve.ofTwoArrows (graphToBaseChange j g f fac U)
        (ofOpensι _ (graphComplOpens j g f fac U)) ∈
      Z.smallEtaleTopology ((smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U)) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ?_
  by_cases hp : p ∈ Set.range (graphToBaseChange j g f fac U).left
  · exact ⟨WalkingPair.left, hp⟩
  · refine ⟨WalkingPair.right, ?_⟩
    change p ∈ Set.range (graphComplOpens j g f fac U).ι
    rw [Scheme.Opens.range_ι]
    exact hp

/-- Every section of a sheaf over an empty object of the small étale site vanishes. -/
private theorem eq_zero_of_isEmpty {A : Type*} [Category A] [Preadditive A]
    {T : Z.Etale} [IsEmpty T.left] {H : Z.Etaleᵒᵖ ⥤ A}
    (hH : Presheaf.IsSheaf Z.smallEtaleTopology H) {E : A} (x : E ⟶ H.obj (op T)) : x = 0 :=
  Presheaf.eq_zero_of_isEmptyCover _ hH (by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff.{u, 0}]
    exact Set.eq_univ_of_forall fun p ↦ isEmptyElim p) x

private theorem isEmpty_of_comp_eq (U : X.Etale) {S : Z.Etale}
    (a : S ⟶ (smallEtaleCompose j).obj U) (b : S ⟶ ofOpens _ (graphComplOpens j g f fac U))
    (hab : a ≫ graphToBaseChange j g f fac U = b ≫ ofOpensι _ _) : IsEmpty S.left := by
  refine ⟨fun p ↦ ?_⟩
  have h := congrArg (fun k ↦ k.left p) hab
  have : (b.left ≫ (graphComplOpens j g f fac U).ι) p ∈ graphComplOpens j g f fac U := by
    exact (b.left p).2
  exact this ⟨_, h⟩

omit [IsSeparated g] in
private theorem graphToBaseChange_comp_baseChange_map {U U' : X.Etale} (v : U' ⟶ U) :
    graphToBaseChange j g f fac U' ≫ (smallEtaleBaseChange g).map ((smallEtaleCompose f).map v) =
      (smallEtaleCompose j).map v ≫ graphToBaseChange j g f fac U := by
  ext1
  exact lift_comp_eq_comp_lift (U.hom ≫ f) g (U.hom ≫ j) (by simp [← fac]) v.left
    (U'.hom ≫ f) (U'.hom ≫ j) (by simp [← MorphismProperty.Over.w v])
    (by simp [← MorphismProperty.Over.w v])
    ((smallEtaleBaseChange g).map ((smallEtaleCompose f).map v)).left
    (baseChange_map_left_fst g _) (baseChange_map_left_snd g _)

private theorem mapsTo_graphComplOpens {U U' : X.Etale} (v : U' ⟶ U) (p)
    (hp : p ∈ graphComplOpens j g f fac U') :
    ((smallEtaleBaseChange g).map ((smallEtaleCompose f).map v)).left p ∈
      graphComplOpens j g f fac U := by
  intro hq
  apply hp
  have := preimage_range_graph (U.hom ≫ f) g (U.hom ≫ j) (by simp [← fac]) v.left
    (U'.hom ≫ f) (U'.hom ≫ j) (by simp [← MorphismProperty.Over.w v])
    (by simp [← MorphismProperty.Over.w v])
    ((smallEtaleBaseChange g).map ((smallEtaleCompose f).map v)).left
    (baseChange_map_left_fst g _) (baseChange_map_left_snd g _)
  rw [graphToBaseChange_left]
  exact this.subset hq

omit [IsOpenImmersion j] [Etale f] [IsSeparated g] in
private theorem range_comp_subset_range_ι {T T' : Scheme.{u}} (m : T' ⟶ T) (W : T.Opens)
    (W' : T'.Opens) (hm : ∀ p ∈ W', m p ∈ W) : Set.range (W'.ι ≫ m) ⊆ Set.range W.ι := by
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact hm _ p.2

/-- A morphism `m : T' ⟶ T` of the small étale site mapping an open `W' ⊆ T'` into an open
`W ⊆ T` restricts to a morphism `W' ⟶ W`. -/
private def ofOpensMap {T T' : Z.Etale} (m : T' ⟶ T) (W : T.left.Opens) (W' : T'.left.Opens)
    (hm : ∀ p ∈ W', m.left p ∈ W) : ofOpens T' W' ⟶ ofOpens T W :=
  let l : W'.toScheme ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι (W'.ι ≫ m.left) (range_comp_subset_range_ι m.left W W' hm)
  have hl : l ≫ W.ι = W'.ι ≫ m.left := IsOpenImmersion.lift_fac _ _ _
  MorphismProperty.Over.homMk l
    (by
      change l ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
      rw [← Category.assoc, hl, Category.assoc]
      exact congrArg (W'.ι ≫ ·) (MorphismProperty.Over.w m)) trivial

omit [IsOpenImmersion j] [Etale f] [IsSeparated g] in
private theorem ofOpensMap_comp_ofOpensι {T T' : Z.Etale} (m : T' ⟶ T) (W : T.left.Opens)
    (W' : T'.left.Opens) (hm : ∀ p ∈ W', m.left p ∈ W) :
    ofOpensMap m W W' hm ≫ ofOpensι T W = ofOpensι T' W' ≫ m := by
  ext1
  have : IsOpenImmersion W.ι := inferInstance
  exact IsOpenImmersion.lift_fac W.ι (W'.ι ≫ m.left) _

variable (Λ : Type r) [Ring Λ] (F : EtaleModules.{u, r} Λ X)

/-- The section `σ_φ(s)` of `j_! F` over `U ×_Y Z`: it restricts along `γ_φ` to `[φ, s]` and to
zero on the complement of the image of `γ_φ`. -/
private def graphSection (U : X.Etale) :
    F.obj.obj (op U) ⟶ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.obj
      (op ((smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U))) :=
  Presheaf.glueSectionByZero _ _ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).property
    (graphToBaseChange j g f fac U) (ofOpensι _ (graphComplOpens j g f fac U))
    (ofTwoArrows_mem j g f fac U)
    (((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app F).hom.app (op U))
    (Presheaf.glueSectionByZero_compat _ _ _ _ fun S a b hab ↦ by
      have := isEmpty_of_comp_eq j g f fac U a b hab
      exact eq_zero_of_isEmpty ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).property _)

private theorem graphSection_graph (U : X.Etale) :
    graphSection j g f fac Λ F U ≫ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map
        (graphToBaseChange j g f fac U).op =
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app F).hom.app (op U) :=
  Presheaf.glueSectionByZero_graph _ _ _ _ _ _ _ _

private theorem graphSection_compl (U : X.Etale) :
    graphSection j g f fac Λ F U ≫ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map
        (ofOpensι _ (graphComplOpens j g f fac U)).op = 0 :=
  Presheaf.glueSectionByZero_compl _ _ _ _ _ _ _ _

private theorem eq_graphSection (U : X.Etale)
    (x : F.obj.obj (op U) ⟶ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.obj
      (op ((smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U))))
    (h₁ : x ≫ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map
        (graphToBaseChange j g f fac U).op =
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app F).hom.app (op U))
    (h₂ : x ≫ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map
        (ofOpensι _ (graphComplOpens j g f fac U)).op = 0) :
    x = graphSection j g f fac Λ F U :=
  Presheaf.glueSectionByZero_unique _ _ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).property
    _ _ (ofTwoArrows_mem j g f fac U)
    (by rw [h₁, graphSection_graph]) (by rw [h₂, graphSection_compl])

private theorem graphSection_naturality {U U' : X.Etale} (v : U' ⟶ U) :
    graphSection j g f fac Λ F U ≫ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map
        ((smallEtaleBaseChange g).map ((smallEtaleCompose f).map v)).op =
      F.obj.map v.op ≫ graphSection j g f fac Λ F U' := by
  apply Presheaf.glueSectionByZero_unique _ _
    ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).property _ _ (ofTwoArrows_mem j g f fac U')
  · rw [Category.assoc, Category.assoc, graphSection_graph, ← Functor.map_comp, ← op_comp,
      graphToBaseChange_comp_baseChange_map, op_comp, Functor.map_comp, ← Category.assoc,
      graphSection_graph]
    exact (((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app F).hom.naturality v.op).symm
  · rw [Category.assoc, Category.assoc, graphSection_compl, Limits.comp_zero,
      ← Functor.map_comp, ← op_comp,
      ← ofOpensMap_comp_ofOpensι _ _ _ (mapsTo_graphComplOpens j g f fac v), op_comp,
      Functor.map_comp,
      ← Category.assoc, graphSection_compl, Limits.zero_comp]

/-- The morphism `F ⟶ f^{-1} g_* (j_! F)` adjoint to the canonical homomorphism, sending `s` to
`σ_φ(s)`. -/
private def graphSectionHom :
    F ⟶ (etaleModuleRestriction.{u, r} Λ f).obj
      ((etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F)) :=
  ObjectProperty.homMk
    { app := fun U ↦ graphSection j g f fac Λ F U.unop
      naturality := fun _ _ v ↦ (graphSection_naturality j g f fac Λ F v.unop).symm }

omit [IsOpenImmersion j] [Etale f] [IsSeparated g] in
private theorem range_iso_comp_ι {T T' : Scheme.{u}} {W : T.Opens} (e : T' ≅ W.toScheme) :
    Set.range (e.hom ≫ W.ι) = W := by
  have hsurj : Function.Surjective e.hom := e.hom.homeomorph.surjective
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
    Set.image_univ, Scheme.Opens.range_ι]

/-- The decomposition of `U ×_Y Z` into the image of `γ_φ` and its complement is one of the
decompositions of the definition of a canonical homomorphism. -/
private theorem exists_iso_graphOpens (U : X.Etale) :
    ∃ e : U.left ≅ (graphOpens j g f fac U).toScheme,
      e.hom ≫ (graphOpens j g f fac U).ι = (graphToBaseChange j g f fac U).left := by
  have := (isOpenImmersion_and_isClosedImmersion_graphToBaseChange_left j g f fac U).1
  exact ⟨(graphToBaseChange j g f fac U).left.isoOpensRange,
    (graphToBaseChange j g f fac U).left.isoOpensRange_hom_ι⟩

/-- In any decomposition `U ×_Y Z = W ⊔ W'` with `γ_φ` an isomorphism onto `W`, the open `W'` is
the complement of the image of `γ_φ`. -/
private theorem eq_graphComplOpens (U : X.Etale)
    (W W' : ((smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U)).left.Opens)
    (hWW' : IsCompl W W') (e : U.left ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (graphToBaseChange j g f fac U).left) :
    W' = graphComplOpens j g f fac U := by
  have hW : W = graphOpens j g f fac U := by
    ext1
    change (W : Set _) = Set.range (graphToBaseChange j g f fac U).left
    rw [← he]
    exact (range_iso_comp_ι e).symm
  subst hW
  exact hWW'.right_unique (isCompl_graphOpens_graphComplOpens j g f fac U)

omit [IsSeparated g] in
private theorem homEquiv_hom_app
    (c : (etaleModuleExtensionByZero.{u, r} Λ f).obj F ⟶
      (etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F))
    (U : X.Etale) :
    ((etaleModuleExtensionByZeroAdj.{u, r} Λ f).homEquiv _ _ c).hom.app (op U) =
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ f).unit.app F).hom.app (op U) ≫
        c.hom.app (op ((smallEtaleCompose f).obj U)) := by
  rw [Adjunction.homEquiv_unit]
  rfl

private theorem graphSectionHom_hom_app (U : X.Etale) :
    (graphSectionHom j g f fac Λ F).hom.app (op U) = graphSection j g f fac Λ F U :=
  rfl

/-- A morphism `f_! F ⟶ g_* (j_! F)` is a canonical homomorphism if and only if its transpose
under `f_! ⊣ f^{-1}` is `graphSectionHom`. -/
private theorem isCanonical_iff
    (c : (etaleModuleExtensionByZero.{u, r} Λ f).obj F ⟶
      (etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F)) :
    IsCanonicalExtensionByZeroToPushforward Λ j g f fac F c ↔
      (etaleModuleExtensionByZeroAdj.{u, r} Λ f).homEquiv _ _ c =
        graphSectionHom j g f fac Λ F := by
  constructor
  · intro hc
    ext1
    refine NatTrans.ext (funext fun U ↦ ?_)
    obtain ⟨U⟩ := U
    obtain ⟨e, he⟩ := exists_iso_graphOpens j g f fac U
    rw [homEquiv_hom_app, graphSectionHom_hom_app]
    refine eq_graphSection j g f fac Λ F U
      (((etaleModuleExtensionByZeroAdj.{u, r} Λ f).unit.app F).hom.app (op U) ≫
        c.hom.app (op ((smallEtaleCompose f).obj U))) ?_ ?_
    · ext s
      exact (hc U s _ _ (isCompl_graphOpens_graphComplOpens j g f fac U) ⟨e, he⟩).2
    · ext s
      exact (hc U s _ _ (isCompl_graphOpens_graphComplOpens j g f fac U) ⟨e, he⟩).1
  · intro hc U s W W' hWW' ⟨e, he⟩
    have h₀ := congrArg (fun φ ↦ φ.hom.app (op U)) hc
    simp only [homEquiv_hom_app, graphSectionHom_hom_app] at h₀
    obtain rfl := eq_graphComplOpens j g f fac U W W' hWW' e he
    constructor
    · have h₁ := congrArg (fun φ ↦ φ.hom s) (graphSection_compl j g f fac Λ F U)
      rw [← h₀] at h₁
      exact h₁
    · have h₁ := congrArg (fun φ ↦ φ.hom s) (graphSection_graph j g f fac Λ F U)
      rw [← h₀] at h₁
      exact h₁

end Construction

/-- **Existence and uniqueness of the canonical homomorphism** (FK I.8, p. 85). Let
`j : X ⟶ Z` be an open immersion and `g : Z ⟶ Y` a separated morphism with `f = j ≫ g`
étale, and let `F` be a sheaf of `Λ`-modules on the small étale site of `X`. There is exactly
one canonical homomorphism `f_! F ⟶ g_* (j_! F)` for `(j, g, F)`. -/
@[weil "lem_fk108_extension_by_zero_to_pushforward_map_exists_unique"]
theorem existsUnique_isCanonicalExtensionByZeroToPushforward (Λ : Type r) [Ring Λ]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) (g : Z ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion j] [Etale f]
    [IsSeparated g] (fac : j ≫ g = f) (F : EtaleModules.{u, r} Λ X) :
    ∃! c : (etaleModuleExtensionByZero.{u, r} Λ f).obj F ⟶
        (etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F),
      IsCanonicalExtensionByZeroToPushforward Λ j g f fac F c := by
  let e := (etaleModuleExtensionByZeroAdj.{u, r} Λ f).homEquiv F
    ((etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F))
  refine ⟨e.symm (graphSectionHom j g f fac Λ F),
    (isCanonical_iff j g f fac Λ F _).2 (e.apply_symm_apply _), fun c hc ↦ ?_⟩
  exact e.injective (((isCanonical_iff j g f fac Λ F c).1 hc).trans (e.apply_symm_apply _).symm)

end AlgebraicGeometry
