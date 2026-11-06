module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum
public import Weil.Defs.AlgebraicGeometry.Descent.Scheme.SingleMorphism
public import Weil.Attr

/-!
# The natural descent datum of a base change

Let `f : T ⟶ S` be a morphism of schemes and `X` a scheme over `S`. Write `p₁, p₂ : T ×_S T ⟶ T`
for the two projections and `X_T = X ×_S T` for the base change. For `k = 1, 2` there is the
canonical isomorphism of iterated fibre products
`ε_k : p_k^* (X_T) = (X ×_S T) ×_{T, p_k} (T ×_S T) ≅ X ×_S (T ×_S T)`, given on points by
`((x, t), w) ↦ (x, w)`, where `t = p_k(w)`. The *natural descent datum* of `X_T` is
`σ_X = ε₂⁻¹ ∘ ε₁ : p₁^* (X_T) ≅ p₂^* (X_T)`.

## Main definitions

* `AlgebraicGeometry.naturalDescentDatum f X` : the natural descent datum of `X_T` relative to
  `f`, a descent datum relative to `f` whose underlying `T`-scheme is `X ×_S T`.
* `AlgebraicGeometry.naturalDescentIso f X` : the isomorphism `σ_X = ε₂⁻¹ ∘ ε₁` of schemes over
  `T ×_S T`.
* `AlgebraicGeometry.naturalDescentPullbackIso f X` : the same isomorphism on the underlying
  fibre products.

## Main results

* `AlgebraicGeometry.DescentDatum.baseChangeTransition_naturalDescentDatum` : the gluing
  isomorphism of `naturalDescentDatum f X`, read in base-change form, is `σ_X`.

## Implementation notes

The natural descent datum is the value at `X` of the canonical descent datum functor
`AlgebraicGeometry.canonicalFamilyDescentFunctor` of the one-member family `f`, so its cocycle
condition and its functoriality in `X` come with it. Its underlying `T`-scheme is literally the
pullback `X ×_S T` (with the factors in this order), which is why the family form is used
rather than `AlgebraicGeometry.DescentDatum.canonical`, whose underlying scheme is only
isomorphic to it. Since `p₁ ≫ f = p₂ ≫ f`, the two targets of `ε₁` and `ε₂` are fibre products
over equal morphisms and are identified by `CategoryTheory.Limits.pullback.congrHom`.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {T S : Scheme.{u}}

/-- **The natural descent datum** of the base change `X_T = X ×_S T` relative to `f : T ⟶ S`:
the canonical descent datum of the `S`-scheme `X`, whose gluing isomorphism preserves the
projection to `X`. -/
@[weil "def_fka3_natural_descent_datum_scheme"]
abbrev naturalDescentDatum (f : T ⟶ S) (X : Over S) : DescentDatum f :=
  (canonicalFamilyDescentFunctor fun _ : Unit ↦ f).functor.obj X

/-- The underlying `T`-scheme of the natural descent datum of `X_T` is `X_T`. -/
@[simp]
lemma naturalDescentDatum_over (f : T ⟶ S) (X : Over S) :
    (naturalDescentDatum f X).over = (Over.pullback f).obj X := rfl

/-- The isomorphism `σ_X = ε₂⁻¹ ∘ ε₁ : p₁^* (X_T) ≅ p₂^* (X_T)` of underlying schemes, where
`ε_k : (X ×_S T) ×_{T, p_k} (T ×_S T) ≅ X ×_S (T ×_S T)` is the canonical isomorphism of
iterated fibre products. -/
def naturalDescentPullbackIso (f : T ⟶ S) (X : Over S) :
    pullback (pullback.snd X.hom f) (pullback.fst f f) ≅
      pullback (pullback.snd X.hom f) (pullback.snd f f) :=
  pullbackLeftPullbackSndIso X.hom f (pullback.fst f f) ≪≫
    pullback.congrHom rfl pullback.condition ≪≫
    (pullbackLeftPullbackSndIso X.hom f (pullback.snd f f)).symm

/-- `σ_X` preserves the point of `X`: on points it is `((x, p₁ w), w) ↦ ((x, p₂ w), w)`. -/
@[reassoc (attr := simp)]
lemma naturalDescentPullbackIso_hom_fst_fst (f : T ⟶ S) (X : Over S) :
    (naturalDescentPullbackIso f X).hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [naturalDescentPullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullback.map]
  rw [pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

/-- `σ_X` preserves the point of `T ×_S T`. -/
@[reassoc (attr := simp)]
lemma naturalDescentPullbackIso_hom_snd (f : T ⟶ S) (X : Over S) :
    (naturalDescentPullbackIso f X).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [naturalDescentPullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.map]
  rw [pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- **The isomorphism `σ_X = ε₂⁻¹ ∘ ε₁`** of schemes over `T ×_S T`, from `p₁^* (X_T)` to
`p₂^* (X_T)`, where `ε_k : (X ×_S T) ×_{T, p_k} (T ×_S T) ≅ X ×_S (T ×_S T)` is the canonical
isomorphism of iterated fibre products. -/
@[weil "def_fka3_natural_descent_datum_scheme"]
def naturalDescentIso (f : T ⟶ S) (X : Over S) :
    Over.mk (pullback.snd (pullback.snd X.hom f) (pullback.fst f f)) ≅
      Over.mk (pullback.snd (pullback.snd X.hom f) (pullback.snd f f)) :=
  Over.isoMk (naturalDescentPullbackIso f X) (naturalDescentPullbackIso_hom_snd f X)

@[simp]
lemma naturalDescentIso_hom_left (f : T ⟶ S) (X : Over S) :
    (naturalDescentIso f X).hom.left = (naturalDescentPullbackIso f X).hom := rfl

namespace DescentDatum

/-- The component in `Y` of an isomorphism `p₁^* Y ≅ p₂^* Y` conjugated from
`Y ×_S T ≅ T ×_S Y`. -/
@[reassoc]
lemma pullbackBaseChangeIso_hom_fst {f : T ⟶ S} (Y : Over T)
    (φ : pullback (Y.hom ≫ f) f ≅ pullback f (Y.hom ≫ f)) :
    (pullbackBaseChangeIso Y φ).hom ≫ pullback.fst Y.hom (pullback.snd f f) =
      (pullbackRightPullbackFstIso f f Y.hom).hom ≫ φ.hom ≫ pullback.snd f (Y.hom ≫ f) := by
  simp only [pullbackBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, pullbackLeftPullbackSndIso_inv_snd_snd]

/-- A morphism into `p₂^* (X_T) = (X ×_S T) ×_{T, p₂} (T ×_S T)` is determined by its components
in `X` and in `T ×_S T`. -/
lemma pullback_snd_hom_ext {f : T ⟶ S} {X : Over S} {W : Scheme.{u}}
    {a b : W ⟶ pullback (pullback.snd X.hom f) (pullback.snd f f)}
    (h₁ : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _)
    (h₂ : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _) : a = b := by
  apply pullback.hom_ext _ h₂
  apply pullback.hom_ext h₁
  rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h₂]

/-- **The natural descent datum in base-change form is `σ_X = ε₂⁻¹ ∘ ε₁`.** -/
@[weil "def_fka3_natural_descent_datum_scheme"]
theorem baseChangeTransition_naturalDescentDatum (f : T ⟶ S) (X : Over S) :
    baseChangeTransition (naturalDescentDatum f X) = naturalDescentIso f X := by
  ext1
  apply Over.OverMorphism.ext
  apply pullback_snd_hom_ext
  · have h := CanonicalDatum.datum_gluing_proj (fun _ : Unit ↦ f) X () ()
    have key := pullbackBaseChangeIso_hom_fst_assoc
      (naturalDescentDatum f X).over (naturalDescentDatum f X).transitionPullbackIso
        (pullback.fst X.hom f)
    rw [baseChangeTransition_hom_left, naturalDescentIso_hom_left]
    refine (key.trans ?_).trans (naturalDescentPullbackIso_hom_fst_fst f X).symm
    exact (congrArg (_ ≫ ·) h).trans (pullbackRightPullbackFstIso_hom_fst_assoc _ _ _ _)
  · rw [baseChangeTransition_hom_left, naturalDescentIso_hom_left]
    exact (Over.w (baseChangeTransition (naturalDescentDatum f X)).hom).trans
      (naturalDescentPullbackIso_hom_snd f X).symm

end DescentDatum

end AlgebraicGeometry
