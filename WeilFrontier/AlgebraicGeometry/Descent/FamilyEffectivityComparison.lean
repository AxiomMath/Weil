module

public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import WeilFrontier.Defs.AlgebraicGeometry.Descent.Scheme.NaturalDescentDatumScheme
public import Weil.Attr

/-!
# Effective descent data for schemes relative to one morphism

Let `f : T ⟶ S` be a morphism of schemes and write `p₁, p₂ : T ×_S T ⟶ T` for the two
projections. A descent datum `(Y, σ)` relative to `f`, with `σ : p₁^* Y ≅ p₂^* Y`, is
*effective* if there are an `S`-scheme `X` and an isomorphism `λ : X_T ≅ Y` of `T`-schemes with
`σ ∘ p₁^* λ = p₂^* λ ∘ σ_X`, where `σ_X` is the natural descent datum of `X_T = X ×_S T`; that
is, `(Y, σ)` is isomorphic to `X_T` with its natural descent datum.

Effectivity is not redefined: it is `AlgebraicGeometry.DescentData.IsEffective`, membership in
the essential image of the canonical descent datum functor `Over S ⥤ DescentDatum f`. This file
proves that it is the condition above.

## Main results

* `AlgebraicGeometry.DescentDatum.isEffective_iff_exists_baseChangeTransition` : a descent datum
  `D` relative to `f` is effective if and only if there are an `S`-scheme `X` and an isomorphism
  `λ : X_T ≅ D.over` of `T`-schemes with `σ ∘ p₁^* λ = p₂^* λ ∘ σ_X`.
* `AlgebraicGeometry.DescentDatum.comm_baseChangeTransition_iff` : a morphism `g : Y ⟶ Y'` of
  the underlying `T`-schemes of two descent data commutes with the gluing isomorphisms in
  base-change form, `σ' ∘ p₁^* g = p₂^* g ∘ σ`, if and only if it commutes with their gluing
  actions `Y ×_S T ⟶ Y`.
* `AlgebraicGeometry.DescentDatum.comm_baseChangeTransition` : a morphism of descent data
  commutes with the gluing isomorphisms in base-change form.

## Implementation notes

The base change `p_k^* λ = λ ×_{T, p_k} (T ×_S T)` is `(Over.pullback p_k).map λ.hom`, and the
gluing isomorphism `σ` in base-change form is
`AlgebraicGeometry.DescentDatum.baseChangeTransition`. The comparison goes through the gluing
action `AlgebraicGeometry.DescentData.actOn`, the second component of the gluing isomorphism
on the literal fibre product `Y ×_S T`.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace DescentDatum

variable {T S : Scheme.{u}} {f : T ⟶ S}

/-- The base change `p^* g` of a morphism of `T`-schemes, followed by the projection to the
target, is the projection to the source followed by `g`. -/
@[reassoc (attr := simp)]
lemma overPullback_map_left_fst {W : Scheme.{u}} (p : W ⟶ T) {Y Z : Over T} (g : Y ⟶ Z) :
    ((Over.pullback p).map g).left ≫ pullback.fst Z.hom p = pullback.fst Y.hom p ≫ g.left :=
  pullback.lift_fst _ _ _

/-- The base change `p^* g` of a morphism of `T`-schemes lies over `W`. -/
@[reassoc (attr := simp)]
lemma overPullback_map_left_snd {W : Scheme.{u}} (p : W ⟶ T) {Y Z : Over T} (g : Y ⟶ Z) :
    ((Over.pullback p).map g).left ≫ pullback.snd Z.hom p = pullback.snd Y.hom p :=
  pullback.lift_snd _ _ _

/-- The gluing isomorphism in base-change form, followed by the projection to the scheme, is the
gluing action, read through `p₁^* Y ≅ Y ×_S T`. -/
@[reassoc]
lemma baseChangeTransition_hom_left_fst (D : DescentDatum f) :
    (baseChangeTransition D).hom.left ≫ pullback.fst D.over.hom (pullback.snd f f) =
      (pullbackRightPullbackFstIso f f D.over.hom).hom ≫ DescentData.actOn D := by
  rw [baseChangeTransition_hom_left, pullbackBaseChangeIso_hom_fst]
  rfl

/-- The gluing isomorphism in base-change form lies over `T ×_S T`. -/
@[reassoc (attr := simp)]
lemma baseChangeTransition_hom_left_snd (D : DescentDatum f) :
    (baseChangeTransition D).hom.left ≫ pullback.snd D.over.hom (pullback.snd f f) =
      pullback.snd D.over.hom (pullback.fst f f) :=
  Over.w (baseChangeTransition D).hom

/-- The comparison `p₁^* Y ≅ Y ×_S T` is natural in the `T`-scheme `Y`. -/
@[reassoc]
lemma pullbackRightPullbackFstIso_hom_naturality {D E : DescentDatum f}
    (g : D.over ⟶ E.over) :
    ((Over.pullback (pullback.fst f f)).map g).left ≫
        (pullbackRightPullbackFstIso f f E.over.hom).hom =
      (pullbackRightPullbackFstIso f f D.over.hom).hom ≫
        DescentData.actOnMap (D := D) (E := E) g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst, overPullback_map_left_fst,
      Category.assoc, DescentData.actOnMap_fst, pullbackRightPullbackFstIso_hom_fst_assoc]
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, overPullback_map_left_snd_assoc,
      Category.assoc, DescentData.actOnMap_snd, pullbackRightPullbackFstIso_hom_snd]

/-- **Compatibility with the gluing isomorphisms in base-change form.** A morphism `g` of the
underlying `T`-schemes of two descent data satisfies `σ' ∘ p₁^* g = p₂^* g ∘ σ` if and only if it
commutes with their gluing actions. -/
theorem comm_baseChangeTransition_iff {D E : DescentDatum f} (g : D.over ⟶ E.over) :
    (Over.pullback (pullback.fst f f)).map g ≫ (baseChangeTransition E).hom =
        (baseChangeTransition D).hom ≫ (Over.pullback (pullback.snd f f)).map g ↔
      DescentData.actOn D ≫ g.left = DescentData.actOnMap (D := D) (E := E) g ≫
        DescentData.actOn E := by
  have e₁ : ((Over.pullback (pullback.fst f f)).map g ≫ (baseChangeTransition E).hom).left ≫
      pullback.fst E.over.hom (pullback.snd f f) =
        (pullbackRightPullbackFstIso f f D.over.hom).hom ≫
          DescentData.actOnMap (D := D) (E := E) g ≫ DescentData.actOn E := by
    rw [Over.comp_left, Category.assoc, baseChangeTransition_hom_left_fst,
      pullbackRightPullbackFstIso_hom_naturality_assoc]
  have e₂ : ((baseChangeTransition D).hom ≫ (Over.pullback (pullback.snd f f)).map g).left ≫
      pullback.fst E.over.hom (pullback.snd f f) =
        (pullbackRightPullbackFstIso f f D.over.hom).hom ≫ DescentData.actOn D ≫ g.left := by
    rw [Over.comp_left, Category.assoc, overPullback_map_left_fst,
      baseChangeTransition_hom_left_fst_assoc]
  constructor
  · intro h
    rw [← cancel_epi (pullbackRightPullbackFstIso f f D.over.hom).hom, ← e₁, ← e₂, h]
  · intro h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [e₁, e₂, h]
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
        baseChangeTransition_hom_left_snd, overPullback_map_left_snd, overPullback_map_left_snd,
        baseChangeTransition_hom_left_snd]

/-- A morphism of descent data commutes with the gluing actions. -/
@[reassoc]
lemma actOn_comp_hom_left {D E : DescentDatum f} (g : D ⟶ E) :
    DescentData.actOn D ≫ (g.hom ()).left =
      DescentData.actOnMap (D := D) (E := E) (g.hom ()) ≫ DescentData.actOn E := by
  have hcomm : prod.map ((Over.map f).map (g.hom ())) (𝟙 (Over.mk f)) ≫
      DescentData.gluingAction E = DescentData.gluingAction D ≫ (Over.map f).map (g.hom ()) := by
    simpa only [Category.assoc, prod.map_snd] using
      congrArg (fun k ↦ k ≫ prod.snd) (g.comm () ())
  rw [← cancel_epi (DescentData.sourceProdIso D).hom, ← Category.assoc,
    DescentData.sourceProdIso_hom_actOn, ← Category.assoc,
    DescentData.sourceProdIso_hom_actOnMap, Category.assoc, DescentData.sourceProdIso_hom_actOn]
  simpa using (congrArg Over.Hom.left hcomm).symm

/-- A morphism of descent data relative to `f` satisfies `σ' ∘ p₁^* g = p₂^* g ∘ σ`. -/
theorem comm_baseChangeTransition {D E : DescentDatum f} (g : D ⟶ E) :
    (Over.pullback (pullback.fst f f)).map (g.hom ()) ≫ (baseChangeTransition E).hom =
      (baseChangeTransition D).hom ≫ (Over.pullback (pullback.snd f f)).map (g.hom ()) :=
  (comm_baseChangeTransition_iff (g.hom ())).2 (actOn_comp_hom_left g)

/-- **Effective descent data.** A descent datum `(Y, σ)` relative to `f : T ⟶ S` is effective,
i.e. isomorphic to the canonical descent datum of an `S`-scheme, if and only if there are an
`S`-scheme `X` and an isomorphism `λ : X_T ≅ Y` of `T`-schemes with
`σ ∘ p₁^* λ = p₂^* λ ∘ σ_X`, where `σ_X` is the natural descent datum of `X_T`. -/
@[weil "def_fka3_effective_descent_datum_scheme"]
theorem isEffective_iff_exists_baseChangeTransition (D : DescentDatum f) :
    DescentData.IsEffective D ↔
      ∃ (X : Over S) (l : (Over.pullback f).obj X ≅ D.over),
        (Over.pullback (pullback.fst f f)).map l.hom ≫ (baseChangeTransition D).hom =
          (naturalDescentIso f X).hom ≫ (Over.pullback (pullback.snd f f)).map l.hom := by
  rw [← DescentData.isFamilyEffective_iff_isEffective]
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    refine ⟨X, (DescentData.evaluation ()).mapIso e, ?_⟩
    rw [← baseChangeTransition_naturalDescentDatum]
    exact comm_baseChangeTransition e.hom
  · rintro ⟨X, l, h⟩
    rw [← baseChangeTransition_naturalDescentDatum] at h
    have hl := (comm_baseChangeTransition_iff (D := naturalDescentDatum f X) (E := D) l.hom).1 h
    exact ⟨X, ⟨DescentData.isoOfActOn (D := naturalDescentDatum f X) (E := D) l hl⟩⟩

end DescentDatum

end AlgebraicGeometry
