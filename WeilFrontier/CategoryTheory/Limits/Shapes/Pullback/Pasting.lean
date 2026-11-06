module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Weil.Attr

/-!
# Base change to the kernel pair of a morphism

Let `f : T ⟶ S` be a morphism and `X` an object over `S`, with structure morphism `g : X ⟶ S`.
Write `X_T = X ×_S T` and `X_{T ×_S T} = X ×_S (T ×_S T)`, and `π_X : X_T ⟶ X` for the first
projection. The two projections `p₁, p₂ : T ×_S T ⟶ T` induce morphisms
`id_X × p_k : X_{T ×_S T} ⟶ X_T`, and together these give a morphism
`X_{T ×_S T} ⟶ X_T ×_X X_T`, the fibre product being taken over `π_X` on both sides.
This morphism is an isomorphism over `X`. On `Z`-valued points it sends `(x, t₁, t₂)` to
`((x, t₁), (x, t₂))`.

## Main definitions

* `CategoryTheory.Limits.pullbackToPullbackFstFst`: the morphism
  `X ×_S (T ×_S T) ⟶ (X ×_S T) ×_X (X ×_S T)`.
* `CategoryTheory.Limits.pullbackIsoPullbackFstFst`: the same morphism, as an isomorphism.

## Main results

* `CategoryTheory.Limits.isIso_pullbackToPullbackFstFst`: the morphism is an isomorphism.
* `CategoryTheory.Limits.pullbackToPullbackFstFst_fst_fst`: it is a morphism over `X`.

## Implementation notes

The statement is proved in an arbitrary category with pullbacks; the category of schemes
is the case of interest.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X S T : C} (g : X ⟶ S) (f : T ⟶ S)

-- `pullback.lift_fst` and its relatives do not fire as `simp` lemmas in this module,
-- so they are added locally.
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

/-- The morphism `(id_X × p₁, id_X × p₂) : X ×_S (T ×_S T) ⟶ (X ×_S T) ×_X (X ×_S T)`,
where `p₁, p₂` are the projections of `T ×_S T` and the fibre product on the right is taken
over the first projection `X ×_S T ⟶ X` on both sides. -/
def pullbackToPullbackFstFst :
    pullback g (pullback.fst f f ≫ f) ⟶ pullback (pullback.fst g f) (pullback.fst g f) :=
  pullback.lift
    (pullback.map g (pullback.fst f f ≫ f) g f (𝟙 X) (pullback.fst f f) (𝟙 S) (by simp)
      (by simp))
    (pullback.map g (pullback.fst f f ≫ f) g f (𝟙 X) (pullback.snd f f) (𝟙 S) (by simp)
      (by simp [pullback.condition]))
    (by simp [pullback.map])

/-- The morphism `pullbackToPullbackFstFst` is a morphism over `X`. -/
@[weil "lem_fka3_double_fibre_product_iso", reassoc (attr := simp)]
lemma pullbackToPullbackFstFst_fst_fst :
    pullbackToPullbackFstFst g f ≫ pullback.fst _ _ ≫ pullback.fst g f =
      pullback.fst g (pullback.fst f f ≫ f) := by
  simp [pullbackToPullbackFstFst, pullback.map]

@[reassoc (attr := simp)]
lemma pullbackToPullbackFstFst_fst_snd :
    pullbackToPullbackFstFst g f ≫ pullback.fst _ _ ≫ pullback.snd g f =
      pullback.snd g (pullback.fst f f ≫ f) ≫ pullback.fst f f := by
  simp [pullbackToPullbackFstFst, pullback.map]

@[reassoc (attr := simp)]
lemma pullbackToPullbackFstFst_snd_fst :
    pullbackToPullbackFstFst g f ≫ pullback.snd _ _ ≫ pullback.fst g f =
      pullback.fst g (pullback.fst f f ≫ f) := by
  simp [pullbackToPullbackFstFst, pullback.map]

@[reassoc (attr := simp)]
lemma pullbackToPullbackFstFst_snd_snd :
    pullbackToPullbackFstFst g f ≫ pullback.snd _ _ ≫ pullback.snd g f =
      pullback.snd g (pullback.fst f f ≫ f) ≫ pullback.snd f f := by
  simp [pullbackToPullbackFstFst, pullback.map]

/-- The inverse of `pullbackToPullbackFstFst`, sending `((x, t₁), (x, t₂))` to `(x, t₁, t₂)`. -/
def pullbackFstFstToPullback :
    pullback (pullback.fst g f) (pullback.fst g f) ⟶ pullback g (pullback.fst f f ≫ f) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst g f)
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd g f) (pullback.snd _ _ ≫ pullback.snd g f)
      (by
        rw [Category.assoc, Category.assoc, ← pullback.condition]
        exact pullback.condition_assoc _))
    (by simp [pullback.condition])

/-- The morphism `(id_X × p₁, id_X × p₂) : X ×_S (T ×_S T) ⟶ (X ×_S T) ×_X (X ×_S T)`
is an isomorphism. -/
@[weil "lem_fka3_double_fibre_product_iso"]
instance isIso_pullbackToPullbackFstFst : IsIso (pullbackToPullbackFstFst g f) := by
  refine ⟨⟨pullbackFstFstToPullback g f, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · simp [pullbackFstFstToPullback]
    · apply pullback.hom_ext <;> simp [pullbackFstFstToPullback]
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [pullbackFstFstToPullback]
    · apply pullback.hom_ext
      · simp [pullbackFstFstToPullback, pullback.condition]
      · simp [pullbackFstFstToPullback]

/-- The isomorphism `X ×_S (T ×_S T) ≅ (X ×_S T) ×_X (X ×_S T)` over `X`, given by
`(id_X × p₁, id_X × p₂)`. Its compatibility with the projections to `X` is
`pullbackToPullbackFstFst_fst_fst`. -/
def pullbackIsoPullbackFstFst :
    pullback g (pullback.fst f f ≫ f) ≅ pullback (pullback.fst g f) (pullback.fst g f) :=
  asIso (pullbackToPullbackFstFst g f)

@[simp]
lemma pullbackIsoPullbackFstFst_hom :
    (pullbackIsoPullbackFstFst g f).hom = pullbackToPullbackFstFst g f := rfl

end CategoryTheory.Limits

end

end
