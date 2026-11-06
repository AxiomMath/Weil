module

public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import WeilFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import WeilFrontier.Defs.AlgebraicGeometry.Etale.SupportSections
public import WeilFrontier.AlgebraicGeometry.Etale.SheafMinusSectionsSubsheaf
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableEtaleSheaf
public import Weil.Attr

/-!
# The sheaf of sections avoiding finitely many global sections is representable

Let `X` be a scheme, `G` a presheaf of sets on the small étale site of `X`, and
`ε : Z̃ ≅ G` an isomorphism from the sheaf represented by an object `Z` whose structure
morphism `p : Z ⟶ X` is separated. A global section `e ∈ G(X)` corresponds under `ε` to a
section `z_e : X ⟶ Z` of `p`; since `p` is étale and separated, the image `z_e(X)` is open and
closed in `Z`. For a finite set `E ⊆ G(X)` let `Z' ⊆ Z` be the complement of
`⋃_{e ∈ E} z_e(X)`. Then `Z'` is open and closed, and `ε` restricts to an isomorphism from the
sheaf represented by the open subscheme `Z'` onto the subpresheaf `G°_E ⊆ G` of sections which
on no connected component agree with an element of `E`. In particular `G°_E` is representable
when `Z` is noetherian and separated.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sectionOfIso`: the section `z_e : X ⟶ Z` corresponding to
  `e ∈ G(X)`.
* `AlgebraicGeometry.SmallEtale.avoidingOpens`: the open subscheme `Z'` of `Z`.
* `AlgebraicGeometry.SmallEtale.sectionsAvoidingSubfunctorOfIso`: `G°_E` as a subpresheaf of a
  presheaf `G` represented by `Z` (no sheaf or difference-loci hypothesis, unlike
  `AlgebraicGeometry.SmallEtale.sectionsAvoidingSubfunctor`).
* `AlgebraicGeometry.SmallEtale.representedSheafAvoidingIso`: the isomorphism `Z̃' ≅ G°_E`.

## Main results

* `AlgebraicGeometry.SmallEtale.isClopen_avoidingOpens`: `Z'` is open and closed in `Z`.
* `AlgebraicGeometry.SmallEtale.range_subset_avoidingOpens_iff`: a morphism `a : U ⟶ Z` has
  image in `Z'` if and only if `ε(a) ∈ G°_E(U)`.
* `AlgebraicGeometry.SmallEtale.representedSheafAvoidingIso_hom_app`: the isomorphism
  `Z̃' ≅ G°_E` is the restriction of `ε`.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_sectionsAvoidingSubfunctorOfIso`: `G°_E` is
  representable.

## Implementation notes

The source assumes `X` connected and all schemes noetherian and separated. Connectedness of `X`
is not used. Of the noetherian hypothesis only the openness of connected components of étale
`X`-schemes is used, which holds for `X` locally noetherian; the characterization of `Z'` is
stated for any object `U` whose underlying space is locally connected. Of separatedness only
that of `p` is used. The proof differs from the source's in the converse direction: rather
than comparing residue field embeddings at a geometric point, it uses that the section `z_e` is
an open immersion, so a morphism `U ⟶ Z` over `X` with image inside `z_e(X)` factors as
`z_e ∘ π`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- A morphism of the small étale site is determined by the underlying morphism of schemes. -/
theorem toScheme_map_injective {U V : SmallEtale B X hX} {f g : U ⟶ V}
    (h : (SmallEtale.toScheme B X hX).map f = (SmallEtale.toScheme B X hX).map g) : f = g := by
  apply (SmallEtale.inclusion B X hX).map_injective
  apply Over.OverMorphism.ext
  exact B.inclusion.map_injective h

/-- The scheme morphism underlying the morphism `U ⟶ X` to the final object is the structure
morphism of `U`. -/
theorem toScheme_map_finalIsTerminal_from (U : SmallEtale B X hX) :
    (SmallEtale.toScheme B X hX).map ((SmallEtale.finalIsTerminal B X hX).from U) =
      B.inclusion.map U.obj.hom := by
  have h := toScheme_map_comp_inclusion_map_hom ((SmallEtale.finalIsTerminal B X hX).from U)
  rw [show B.inclusion.map (SmallEtale.final B X hX).obj.hom = 𝟙 _ from
    B.inclusion.map_id _] at h
  exact (Category.comp_id _).symm.trans h

theorem range_toScheme_map_comp_subset {U V W : SmallEtale B X hX} (f : U ⟶ V) (a : V ⟶ W) :
    Set.range ((SmallEtale.toScheme B X hX).map (f ≫ a)).base ⊆
      Set.range ((SmallEtale.toScheme B X hX).map a).base := by
  rintro _ ⟨x, rfl⟩
  exact ⟨((SmallEtale.toScheme B X hX).map f).base x, by
    rw [Functor.map_comp, Scheme.Hom.comp_apply]⟩

/-- A morphism from the final object of the small étale site is a section of the structure
morphism. -/
theorem toScheme_map_comp_inclusion_map_hom_of_final {Z : SmallEtale B X hX}
    (z : SmallEtale.final B X hX ⟶ Z) :
    (SmallEtale.toScheme B X hX).map z ≫ B.inclusion.map Z.obj.hom = 𝟙 _ :=
  (toScheme_map_comp_inclusion_map_hom z).trans (B.inclusion.map_id _)

/-- The structure morphism of an object of the small étale site is unramified. -/
theorem unramified_of_smallEtale (Z : SmallEtale B X hX) :
    Unramified (B.inclusion.map Z.obj.hom) := by
  have : Etale (B.inclusion.map Z.obj.hom) := Z.property
  exact (unramified_iff_locallyOfFiniteType_and_formallyUnramified _).2
    ⟨inferInstance, inferInstance⟩

/-- The image of a morphism from the final object into an object with separated structure
morphism is open and closed. -/
theorem isClopen_range_toScheme_map_of_final {Z : SmallEtale B X hX}
    [IsSeparated (B.inclusion.map Z.obj.hom)] (z : SmallEtale.final B X hX ⟶ Z) :
    IsClopen (Set.range ((SmallEtale.toScheme B X hX).map z).base) := by
  have := unramified_of_smallEtale Z
  exact @Unramified.isClopen_range_section _ _ (B.inclusion.map Z.obj.hom) this ‹_› _
    (toScheme_map_comp_inclusion_map_hom_of_final z)

/-- A morphism `b : V ⟶ Z` whose image lies in the image of a section `z : X ⟶ Z` is the
composite of `z` with the structure morphism of `V`. -/
theorem eq_from_comp_of_range_subset {Z V : SmallEtale B X hX}
    (z : SmallEtale.final B X hX ⟶ Z) (b : V ⟶ Z)
    (h : Set.range ((SmallEtale.toScheme B X hX).map b).base ⊆
      Set.range ((SmallEtale.toScheme B X hX).map z).base) :
    b = (SmallEtale.finalIsTerminal B X hX).from V ≫ z := by
  have hu := unramified_of_smallEtale Z
  have hs := toScheme_map_comp_inclusion_map_hom_of_final z
  have : IsOpenImmersion ((SmallEtale.toScheme B X hX).map z) :=
    @Unramified.section_isOpenImmersion _ _ (B.inclusion.map Z.obj.hom) hu _ hs
  apply toScheme_map_injective
  set l := IsOpenImmersion.lift ((SmallEtale.toScheme B X hX).map z)
    ((SmallEtale.toScheme B X hX).map b) h
  have hl : l ≫ (SmallEtale.toScheme B X hX).map z = (SmallEtale.toScheme B X hX).map b :=
    IsOpenImmersion.lift_fac _ _ _
  have hl' : l = B.inclusion.map V.obj.hom := by
    have h1 : l ≫ (SmallEtale.toScheme B X hX).map z ≫ B.inclusion.map Z.obj.hom = l := by
      rw [hs]; exact Category.comp_id _
    rw [← h1, ← Category.assoc, hl]
    exact toScheme_map_comp_inclusion_map_hom b
  rw [Functor.map_comp, toScheme_map_finalIsTerminal_from, ← hl', hl]

variable {G : (SmallEtale B X hX)ᵒᵖ ⥤ Type u} {Z : SmallEtale B X hX}

/-- The section `z_e : X ⟶ Z` corresponding to a global section `e ∈ G(X)` under an
isomorphism `ε : Z̃ ≅ G`. -/
def sectionOfIso (ε : (representedSheaf Z).obj ≅ G) (e : G.obj (op (SmallEtale.final B X hX))) :
    SmallEtale.final B X hX ⟶ Z :=
  ε.inv.app (op (SmallEtale.final B X hX)) e

theorem hom_app_sectionOfIso (ε : (representedSheaf Z).obj ≅ G)
    (e : G.obj (op (SmallEtale.final B X hX))) :
    ε.hom.app (op (SmallEtale.final B X hX)) (sectionOfIso ε e) = e :=
  ε.inv_hom_id_app_apply _ e

/-- Under `ε`, the restriction `e|_U` of a global section corresponds to `z_e ∘ π` for the
structure morphism `π : U ⟶ X`. -/
theorem hom_app_from_comp_sectionOfIso (ε : (representedSheaf Z).obj ≅ G)
    (e : G.obj (op (SmallEtale.final B X hX))) (U : SmallEtale B X hX) :
    ε.hom.app (op U) ((SmallEtale.finalIsTerminal B X hX).from U ≫ sectionOfIso ε e) =
      globalRestrict G U e := by
  have h := NatTrans.naturality_apply ε.hom ((SmallEtale.finalIsTerminal B X hX).from U).op
    (sectionOfIso ε e)
  rw [hom_app_sectionOfIso] at h
  exact h

/-- Under `ε`, restriction of `ε(a)` along `f` corresponds to `a ∘ f`. -/
theorem hom_app_comp (ε : (representedSheaf Z).obj ≅ G) {U V : SmallEtale B X hX}
    (f : V ⟶ U) (a : U ⟶ Z) :
    ε.hom.app (op V) (f ≫ a) = G.map f.op (ε.hom.app (op U) a) :=
  NatTrans.naturality_apply ε.hom f.op a

theorem hom_app_injective (ε : (representedSheaf Z).obj ≅ G) (U : SmallEtale B X hX) :
    Function.Injective (ε.hom.app (op U)) := fun a b h ↦ by
  simpa using congrArg (ε.inv.app (op U)) h

variable [IsSeparated (B.inclusion.map Z.obj.hom)]

/-- **The complement `Z'` of the images of the sections `z_e`, `e ∈ E`**, an open subscheme of
`Z` for a finite set `E` of global sections. -/
def avoidingOpens (ε : (representedSheaf Z).obj ≅ G)
    {E : Set (G.obj (op (SmallEtale.final B X hX)))} (hE : E.Finite) :
    ((SmallEtale.toScheme B X hX).obj Z).Opens :=
  ⟨(⋃ e ∈ E, Set.range ((SmallEtale.toScheme B X hX).map (sectionOfIso ε e)).base)ᶜ,
    (hE.isClosed_biUnion fun e _ ↦
      (isClopen_range_toScheme_map_of_final (sectionOfIso ε e)).isClosed).isOpen_compl⟩

theorem mem_avoidingOpens_iff (ε : (representedSheaf Z).obj ≅ G)
    {E : Set (G.obj (op (SmallEtale.final B X hX)))} (hE : E.Finite)
    (y : (SmallEtale.toScheme B X hX).obj Z) :
    y ∈ avoidingOpens ε hE ↔
      ∀ e ∈ E, y ∉ Set.range ((SmallEtale.toScheme B X hX).map (sectionOfIso ε e)).base := by
  change y ∈ (⋃ e ∈ E, _)ᶜ ↔ _
  simp

/-- **`Z'` is open and closed in `Z`.** -/
@[weil "lem_fk103_sheaf_minus_sections_representable"]
theorem isClopen_avoidingOpens (ε : (representedSheaf Z).obj ≅ G)
    {E : Set (G.obj (op (SmallEtale.final B X hX)))} (hE : E.Finite) :
    IsClopen (avoidingOpens ε hE : Set ((SmallEtale.toScheme B X hX).obj Z)) :=
  ⟨(isOpen_biUnion fun e _ ↦
      (isClopen_range_toScheme_map_of_final (sectionOfIso ε e)).isOpen).isClosed_compl,
    (avoidingOpens ε hE).isOpen⟩

/-- **Morphisms into `Z'` correspond to sections of `G°_E`.** For an object `U` whose
underlying space is locally connected, a morphism `a : U ⟶ Z` has image in `Z'` if and only if
`ε(a)` agrees with no `e ∈ E` on any connected component of `U`. -/
@[weil "lem_fk103_sheaf_minus_sections_representable"]
theorem range_subset_avoidingOpens_iff (ε : (representedSheaf Z).obj ≅ G)
    {E : Set (G.obj (op (SmallEtale.final B X hX)))} (hE : E.Finite) {U : SmallEtale B X hX}
    [LocallyConnectedSpace ((SmallEtale.toScheme B X hX).obj U)] (a : U ⟶ Z) :
    Set.range ((SmallEtale.toScheme B X hX).map a).base ⊆ avoidingOpens ε hE ↔
      ε.hom.app (op U) a ∈ sectionsAvoiding G E U := by
  rw [mem_sectionsAvoiding_iff]
  constructor
  · rintro h W ⟨x, hW⟩ e he heq
    have hxW : x ∈ W := by
      change x ∈ (W : Set _)
      rw [hW]
      exact mem_connectedComponent
    rw [← hom_app_comp, ← hom_app_from_comp_sectionOfIso] at heq
    have hfac := hom_app_injective ε _ heq
    have hpt : ((SmallEtale.toScheme B X hX).map (openObjectι B X hX U W ≫ a)).base ⟨x, hxW⟩ =
        ((SmallEtale.toScheme B X hX).map a).base x := by
      rw [Functor.map_comp, openObjectι_map]
      rfl
    have hmem := (mem_avoidingOpens_iff ε hE _).1 (h ⟨x, rfl⟩) e he
    apply hmem
    rw [← hpt, hfac, Functor.map_comp]
    exact ⟨_, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    refine (mem_avoidingOpens_iff ε hE _).2 ?_
    rintro e he hx
    set s := (SmallEtale.toScheme B X hX).map (sectionOfIso ε e)
    have hQ : IsClopen (((SmallEtale.toScheme B X hX).map a).base ⁻¹' Set.range s.base) :=
      (isClopen_range_toScheme_map_of_final (sectionOfIso ε e)).preimage
        ((SmallEtale.toScheme B X hX).map a).base.hom.continuous
    let W : ((SmallEtale.toScheme B X hX).obj U).Opens :=
      ⟨connectedComponent x, isOpen_connectedComponent⟩
    have hsub : Set.range ((SmallEtale.toScheme B X hX).map (openObjectι B X hX U W ≫ a)).base ⊆
        Set.range s.base := by
      rintro _ ⟨w, rfl⟩
      have hw : w.1 ∈ ((SmallEtale.toScheme B X hX).map a).base ⁻¹' Set.range s.base :=
        hQ.connectedComponent_subset hx w.2
      rw [Functor.map_comp, openObjectι_map]
      exact hw
    have hfac := eq_from_comp_of_range_subset _ _ hsub
    refine h W ⟨x, rfl⟩ e he ?_
    rw [← hom_app_comp, hfac, hom_app_from_comp_sectionOfIso]

/-- **The subpresheaf `G°_E ⊆ G`** of sections which on no connected component agree with an
element of a finite set `E` of global sections, for `G` representable by an object with
separated structure morphism over a locally noetherian scheme. -/
def sectionsAvoidingSubfunctorOfIso [IsLocallyNoetherian X] (ε : (representedSheaf Z).obj ≅ G)
    {E : Set (G.obj (op (SmallEtale.final B X hX)))} (hE : E.Finite) : Subfunctor G where
  obj U := sectionsAvoiding G E U.unop
  map {U V} f σ hσ := by
    obtain ⟨a, rfl⟩ : ∃ a : U.unop ⟶ Z, ε.hom.app U a = σ :=
      ⟨ε.inv.app U σ, ε.inv_hom_id_app_apply _ σ⟩
    rw [Set.mem_preimage]
    have h := (range_subset_avoidingOpens_iff ε hE a).2 hσ
    change G.map f.unop.op (ε.hom.app (op U.unop) a) ∈ _
    rw [← hom_app_comp ε f.unop a]
    refine (range_subset_avoidingOpens_iff ε hE (f.unop ≫ a)).1 ?_
    exact (range_toScheme_map_comp_subset f.unop a).trans h

@[simp]
theorem sectionsAvoidingSubfunctorOfIso_obj [IsLocallyNoetherian X]
    (ε : (representedSheaf Z).obj ≅ G) {E : Set (G.obj (op (SmallEtale.final B X hX)))}
    (hE : E.Finite) (U : (SmallEtale B X hX)ᵒᵖ) :
    (sectionsAvoidingSubfunctorOfIso ε hE).obj U = sectionsAvoiding G E U.unop :=
  rfl

/-- The object `Z'` of the small étale site. -/
abbrev avoidingObject (ε : (representedSheaf Z).obj ≅ G)
    {E : Set (G.obj (op (SmallEtale.final B X hX)))} (hE : E.Finite) : SmallEtale B X hX :=
  openObject B X hX Z (avoidingOpens ε hE)

instance mono_openObjectι (U : SmallEtale B X hX)
    (W : ((SmallEtale.toScheme B X hX).obj U).Opens) : Mono (openObjectι B X hX U W) :=
  ⟨fun g h hgh ↦ toScheme_map_injective <| by
    have := congrArg (SmallEtale.toScheme B X hX).map hgh
    simp only [Functor.map_comp, openObjectι_map] at this
    exact (cancel_mono _).1 this⟩

/-- **`ε` restricts to an isomorphism `Z̃' ≅ G°_E`.** -/
@[weil "lem_fk103_sheaf_minus_sections_representable"]
def representedSheafAvoidingIso [IsLocallyNoetherian X] (ε : (representedSheaf Z).obj ≅ G)
    {E : Set (G.obj (op (SmallEtale.final B X hX)))} (hE : E.Finite) :
    (representedSheaf (avoidingObject ε hE)).obj ≅
      (sectionsAvoidingSubfunctorOfIso ε hE).toFunctor :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    { toFun a := ⟨ε.hom.app U (a ≫ openObjectι B X hX Z (avoidingOpens ε hE)),
        (range_subset_avoidingOpens_iff ε hE _).1
          ((range_toScheme_map_comp_subset (show U.unop ⟶ _ from a) _).trans
            (openObjectι_range B X hX Z _).subset)⟩
      invFun σ := factorThroughOpenObject B X hX U.unop Z (ε.inv.app U σ.1) _
        ((range_subset_avoidingOpens_iff ε hE _).2 (by simpa using σ.2))
      left_inv a := by
        apply (cancel_mono (openObjectι B X hX Z (avoidingOpens ε hE))).1
        exact (factorThroughOpenObject_fac B X hX _ _ _ _ _).trans (ε.hom_inv_id_app_apply _ _)
      right_inv σ := by
        apply Subtype.ext
        exact (congrArg (ε.hom.app U) (factorThroughOpenObject_fac B X hX _ _ _ _ _)).trans
          (ε.inv_hom_id_app_apply _ _) }) (fun {U V} f ↦ by
    ext a
    apply Subtype.ext
    change ε.hom.app V ((f.unop ≫ a) ≫ _) = G.map f (ε.hom.app U (a ≫ _))
    exact (congrArg (ε.hom.app V) (Category.assoc f.unop (show U.unop ⟶ _ from a) _)).trans
      (hom_app_comp ε f.unop _))

/-- The isomorphism `Z̃' ≅ G°_E` is the restriction of `ε`: it sends `a : U ⟶ Z'` to
`ε(ι ∘ a)` for the inclusion `ι : Z' ⟶ Z`. -/
@[weil "lem_fk103_sheaf_minus_sections_representable"]
theorem representedSheafAvoidingIso_hom_app [IsLocallyNoetherian X]
    (ε : (representedSheaf Z).obj ≅ G) {E : Set (G.obj (op (SmallEtale.final B X hX)))}
    (hE : E.Finite) (U : SmallEtale B X hX) (a : U ⟶ avoidingObject ε hE) :
    ((representedSheafAvoidingIso ε hE).hom.app (op U) a : G.obj (op U)) =
      ε.hom.app (op U) (a ≫ openObjectι B X hX Z (avoidingOpens ε hE)) :=
  rfl

/-- **`G°_E` is representable** when the representing object `Z` is noetherian and separated. -/
@[weil "lem_fk103_sheaf_minus_sections_representable"]
theorem isRepresentableInEt_sectionsAvoidingSubfunctorOfIso [IsLocallyNoetherian X]
    (ε : (representedSheaf Z).obj ≅ G) {E : Set (G.obj (op (SmallEtale.final B X hX)))}
    (hE : E.Finite) (hZ : IsNoetherianSeparated B X hX Z) :
    IsRepresentableInEt (sectionsAvoidingSubfunctorOfIso ε hE).toFunctor := by
  refine ⟨avoidingObject ε hE, ⟨?_, ?_⟩, ⟨representedSheafAvoidingIso ε hE⟩⟩
  · have := hZ.1
    change IsNoetherian (avoidingOpens ε hE : Scheme)
    exact (isNoetherian_iff _).2 ⟨inferInstance, isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  · have := hZ.2
    change (avoidingOpens ε hE : Scheme).IsSeparated
    exact ⟨by rw [← Limits.terminal.comp_from (avoidingOpens ε hE).ι]; infer_instance⟩

end AlgebraicGeometry.SmallEtale
