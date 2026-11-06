module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import WeilFrontier.Defs.AlgebraicGeometry.Morphisms.UniversallyInjective
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Base change along a purely inseparable morphism is an equivalence of étale categories

Let `B` be a big étale site and `f : T ⟶ S` a morphism of its underlying category. If `f` is
of finite type and separated, base change `U ↦ U ×_S T` sends a noetherian separated étale
`S`-scheme to a noetherian separated étale `T`-scheme, so it is a functor
`Et(S) ⥤ Et(T)` between the categories of noetherian separated étale schemes.

When `f` is purely inseparable (finite, universally injective and surjective) and `S` is locally
noetherian, this functor is an equivalence of categories.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.baseChange` — base change
  `Et(S) ⥤ Et(T)`, `U ↦ U ×_S T`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.toEtale` — the fully faithful functor from
  `Et(S)` to the small étale category `S.Etale` of all étale `S`-schemes.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isEquivalence_baseChange` — base change
  along a finite, universally injective, surjective morphism with locally noetherian target is
  an equivalence `Et(S) ≌ Et(T)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isEquivalence_baseChange_of_isPurelyInseparable`
  — the same statement for a purely inseparable morphism.

## Implementation notes

The equivalence is deduced from the equivalence of the categories of all étale schemes,
`Stacks.Etale.etalePullback_isEquivalence` (Stacks, Tag 04DZ), rather than through the
representability of direct images of representable sheaves. Base change in `Et(S)` is compared
with base change of étale schemes by the canonical isomorphisms of fibre products. An étale
`S`-scheme whose base change is noetherian and separated is itself noetherian and separated: it
is quasi-compact and separated as the image of a universally closed surjection, and locally
noetherian because `S` is. The local noetherianity of `S` is needed: for `S` the spectrum of
a non-noetherian ring with a nilpotent ideal of definition and `T` its reduction a point, the
object `T` of `Et(T)` is the base change of `S` alone, which is not noetherian. In the source
every scheme is noetherian.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S T : B.Scheme} (f : T ⟶ S)

section BaseChange

variable [LocallyOfFiniteType (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
  [IsSeparated (B.inclusion.map f)]

/-- The base change of a noetherian separated étale `S`-scheme along a separated morphism of
finite type is noetherian and separated. -/
lemma isNoetherianSeparated_baseChange (U : SmallNoetherianSeparatedEtale B S.obj S.property) :
    SmallEtale.IsNoetherianSeparated B T.obj T.property
      ((smallEtaleBaseChange B f).obj ((inclusion B S.obj S.property).obj U)) := by
  let a : U.obj.obj.left ⟶ S := U.obj.obj.hom
  have hP := (IsPullback.of_hasPullback a f).map B.inclusion
  let p := B.inclusion.map (pullback.fst a f)
  have : LocallyOfFiniteType p := MorphismProperty.of_isPullback hP.flip inferInstance
  have : QuasiCompact p := MorphismProperty.of_isPullback hP.flip inferInstance
  have : IsSeparated p := MorphismProperty.of_isPullback hP.flip inferInstance
  have hU : IsNoetherian (B.inclusion.obj U.obj.obj.left) := U.property.1
  have hU' : (B.inclusion.obj U.obj.obj.left).IsSeparated := U.property.2
  have : IsLocallyNoetherian (B.inclusion.obj (pullback a f)) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace (B.inclusion.obj (pullback a f)) :=
    QuasiCompact.compactSpace_of_compactSpace p
  refine ⟨(⟨⟩ : IsNoetherian (B.inclusion.obj (pullback a f))), ⟨?_⟩⟩
  change IsSeparated (terminal.from (B.inclusion.obj (pullback a f)))
  rw [Subsingleton.elim (terminal.from _) (p ≫ terminal.from _)]
  infer_instance

/-- **Base change of noetherian separated étale schemes.** For a separated morphism of finite
type `f : T ⟶ S`, the functor `Et(S) ⥤ Et(T)` sending `U` to `U ×_S T` and `h` to
`h ×_S id_T`. -/
@[weil "thm_fk103_purely_inseparable_etale_site_equivalence"]
noncomputable def baseChange :
    SmallNoetherianSeparatedEtale B S.obj S.property ⥤
      SmallNoetherianSeparatedEtale B T.obj T.property :=
  (SmallEtale.IsNoetherianSeparated B T.obj T.property).lift
    (inclusion B S.obj S.property ⋙ smallEtaleBaseChange B f)
    (isNoetherianSeparated_baseChange f)

end BaseChange

section ToEtale

variable (B) (X : Scheme.{u}) (hX : B.Contains X)

/-- The functor from `Et(X)` to the category `X.Etale` of all schemes étale over `X`. -/
noncomputable def toEtale : SmallNoetherianSeparatedEtale B X hX ⥤ X.Etale :=
  MorphismProperty.Comma.lift (toOver B X hX) (fun U ↦ etale_structureMorphism U)
    (fun _ ↦ trivial) (fun _ ↦ trivial)

@[simp]
lemma toEtale_obj_left (U : SmallNoetherianSeparatedEtale B X hX) :
    ((toEtale B X hX).obj U).left = (toScheme B X hX).obj U :=
  rfl

@[simp]
lemma toEtale_obj_hom (U : SmallNoetherianSeparatedEtale B X hX) :
    ((toEtale B X hX).obj U).hom = structureMorphism U :=
  rfl

@[simp]
lemma toEtale_map_left {U V : SmallNoetherianSeparatedEtale B X hX} (h : U ⟶ V) :
    ((toEtale B X hX).map h).left = (toScheme B X hX).map h :=
  rfl

/-- `Et(X)` is a full subcategory of the category of all schemes étale over `X`. -/
noncomputable def fullyFaithfulToEtale : (toEtale B X hX).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := Scheme.Etale.forget X) (fullyFaithfulToOver B X hX)

instance : (toEtale B X hX).Full := (fullyFaithfulToEtale B X hX).full

instance : (toEtale B X hX).Faithful := (fullyFaithfulToEtale B X hX).faithful

end ToEtale

/-- Base change of étale schemes along a morphism `φ : X ⟶ Y`, as a functor
`Y.Etale ⥤ X.Etale`. -/
noncomputable abbrev schemeEtalePullback {X Y : Scheme.{u}} (φ : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  letI : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) φ :=
    ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) φ :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ φ

section Comparison

variable [LocallyOfFiniteType (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
  [IsSeparated (B.inclusion.map f)]

/-- The component at `U` of `baseChangeCompToEtaleIso`: the canonical isomorphism between the
fibre product `U ×_S T` formed in `B` and the one formed in all schemes. -/
noncomputable def baseChangeCompToEtaleIsoApp
    (U : SmallNoetherianSeparatedEtale B S.obj S.property) :
    (toEtale B T.obj T.property).obj ((baseChange f).obj U) ≅
      (schemeEtalePullback (B.inclusion.map f)).obj ((toEtale B S.obj S.property).obj U) :=
  MorphismProperty.Over.isoMk (PreservesPullback.iso B.inclusion U.obj.obj.hom f)
    (PreservesPullback.iso_hom_snd _ _ _)

lemma baseChangeCompToEtaleIsoApp_hom_left
    (U : SmallNoetherianSeparatedEtale B S.obj S.property) :
    (baseChangeCompToEtaleIsoApp f U).hom.left =
      (PreservesPullback.iso B.inclusion U.obj.obj.hom f).hom :=
  rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
  [IsSeparated (B.inclusion.map f)] in
lemma pullback_fst_comp_toScheme_map_condition
    {U V : SmallNoetherianSeparatedEtale B S.obj S.property} (g : U ⟶ V) :
    (pullback.fst (structureMorphism U) (B.inclusion.map f) ≫
        (toScheme B S.obj S.property).map g) ≫ structureMorphism V =
      pullback.snd (structureMorphism U) (B.inclusion.map f) ≫ B.inclusion.map f := by
  rw [Category.assoc, toScheme_map_comp_structureMorphism]
  exact pullback.condition

omit [LocallyOfFiniteType (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
  [IsSeparated (B.inclusion.map f)] in
lemma inclusion_map_pullback_map_comp_iso_hom
    {U V : SmallNoetherianSeparatedEtale B S.obj S.property} (g : U ⟶ V) :
    B.inclusion.map ((Over.pullback f).map g.hom.hom).left ≫
        (PreservesPullback.iso B.inclusion V.obj.obj.hom f).hom =
      (PreservesPullback.iso B.inclusion U.obj.obj.hom f).hom ≫
        pullback.lift (pullback.fst (structureMorphism U) (B.inclusion.map f) ≫
          (toScheme B S.obj S.property).map g)
          (pullback.snd (structureMorphism U) (B.inclusion.map f))
          (pullback_fst_comp_toScheme_map_condition f g) := by
  apply pullback.hom_ext
  · have h : ((Over.pullback f).map g.hom.hom).left ≫ pullback.fst V.obj.obj.hom f =
        pullback.fst U.obj.obj.hom f ≫ g.hom.hom.left := by
      simp only [Over.pullback_obj_left, Over.pullback_map_left]; erw [pullback.lift_fst]
    rw [Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp, h, Category.assoc,
      pullback.lift_fst, ← Category.assoc, PreservesPullback.iso_hom_fst, Functor.map_comp]
    rfl
  · have h : ((Over.pullback f).map g.hom.hom).left ≫ pullback.snd V.obj.obj.hom f =
        pullback.snd U.obj.obj.hom f := by
      simp only [Over.pullback_obj_left, Over.pullback_map_left]; erw [pullback.lift_snd]
    rw [Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp, h, Category.assoc,
      pullback.lift_snd, PreservesPullback.iso_hom_snd]

/-- Base change in `Et(S)` agrees with base change of étale `S`-schemes. -/
noncomputable def baseChangeCompToEtaleIso :
    baseChange f ⋙ toEtale B T.obj T.property ≅
      toEtale B S.obj S.property ⋙ schemeEtalePullback (B.inclusion.map f) :=
  NatIso.ofComponents (baseChangeCompToEtaleIsoApp f)
    (fun {U V} g ↦ by
      apply MorphismProperty.Over.Hom.ext
      erw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
        baseChangeCompToEtaleIsoApp_hom_left, baseChangeCompToEtaleIsoApp_hom_left]
      exact inclusion_map_pullback_map_comp_iso_hom f g)

end Comparison

/-- Base change of étale schemes along a finite (more generally integral), universally injective,
surjective morphism is an equivalence (Stacks, Tag 04DZ). -/
lemma isEquivalence_schemeEtalePullback {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsIntegralHom φ]
    [UniversallyInjective φ] [Surjective φ] : (schemeEtalePullback φ).IsEquivalence :=
  Stacks.Etale.etalePullback_isEquivalence φ

section Equivalence

variable [IsFinite (B.inclusion.map f)] [UniversallyInjective (B.inclusion.map f)]
  [Surjective (B.inclusion.map f)]

lemma full_baseChange : (baseChange f).Full := by
  have := isEquivalence_schemeEtalePullback (B.inclusion.map f)
  have : (baseChange f ⋙ toEtale B T.obj T.property).Full :=
    Functor.Full.of_iso (baseChangeCompToEtaleIso f).symm
  exact Functor.Full.of_comp_faithful _ (toEtale B T.obj T.property)

lemma faithful_baseChange : (baseChange f).Faithful := by
  have := isEquivalence_schemeEtalePullback (B.inclusion.map f)
  have : (baseChange f ⋙ toEtale B T.obj T.property).Faithful :=
    Functor.Faithful.of_iso (baseChangeCompToEtaleIso f).symm
  exact Functor.Faithful.of_comp _ (toEtale B T.obj T.property)

lemma essSurj_baseChange [IsLocallyNoetherian S.obj] : (baseChange f).EssSurj := by
  have := isEquivalence_schemeEtalePullback (B.inclusion.map f)
  refine ⟨fun V ↦ ?_⟩
  let φ := B.inclusion.map f
  let P := schemeEtalePullback φ
  let V' := (toEtale B T.obj T.property).obj V
  let W := P.objPreimage V'
  let e : P.obj W ≅ V' := P.objObjPreimageIso V'
  let i : pullback W.hom φ ≅ (toScheme B T.obj T.property).obj V :=
    (Scheme.Etale.forget T.obj ⋙ Over.forget T.obj).mapIso e
  let p : (toScheme B T.obj T.property).obj V ⟶ W.left := i.inv ≫ pullback.fst W.hom φ
  have : Surjective (pullback.fst W.hom φ) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback W.hom φ).flip inferInstance
  have : UniversallyClosed (pullback.fst W.hom φ) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback W.hom φ).flip inferInstance
  have : CompactSpace W.left := by
    have h := isCompact_univ.image p.continuous
    rw [Set.image_univ, Set.range_eq_univ.mpr (inferInstance : Surjective p).surj] at h
    exact ⟨h⟩
  let w : W.left ⟶ S.obj := W.hom
  have : Etale w := W.prop
  have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian w
  have : IsNoetherian W.left := ⟨⟩
  have : W.left.IsSeparated := Scheme.isSeparated_of_surjective_universallyClosed p
  have hW : B.Contains W.left := (Scheme.size_le_of_locallyOfFiniteType w).trans_lt S.property
  let U := mk (hS := S.property) W.left hW W.hom
  let eU : (toEtale B S.obj S.property).obj U ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
  exact ⟨U, ⟨(fullyFaithfulToEtale B T.obj T.property).preimageIso
    ((baseChangeCompToEtaleIso f).app U ≪≫ P.mapIso eU ≪≫ e)⟩⟩

/-- **Base change along a purely inseparable morphism is an equivalence of étale categories.**
Let `f : T ⟶ S` be finite, universally injective and surjective, with `S` locally noetherian.
Then base change `Et(S) ⥤ Et(T)`, `U ↦ U ×_S T`, is an equivalence of categories. -/
theorem isEquivalence_baseChange [IsLocallyNoetherian S.obj] : (baseChange f).IsEquivalence where
  faithful := faithful_baseChange f
  full := full_baseChange f
  essSurj := essSurj_baseChange f

end Equivalence

/-- **Base change along a purely inseparable morphism is an equivalence of étale categories.**
Let `f : T ⟶ S` be a purely inseparable morphism with `S` locally noetherian. Then the functor
`Et(S) ⥤ Et(T)`, `U ↦ U ×_S T`, `h ↦ h ×_S id_T`, is an equivalence of categories. -/
@[weil "thm_fk103_purely_inseparable_etale_site_equivalence"]
theorem isEquivalence_baseChange_of_isPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable) [IsLocallyNoetherian S.obj] :
    letI := hf.isFinite
    (baseChange f).IsEquivalence :=
  letI := hf.isFinite
  letI := hf.universallyInjective
  letI := hf.surjective
  isEquivalence_baseChange f

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end
