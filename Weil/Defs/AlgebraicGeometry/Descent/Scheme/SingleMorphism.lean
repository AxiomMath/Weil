module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphism
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumSectionsPushout
public import Weil.Attr

/-!
# Descent data for schemes relative to one morphism, in base-change form

Let `f : T ⟶ S` be a morphism of schemes and `Y` a scheme over `T`. Write `p₁, p₂ : T ×_S T ⟶ T`
for the two projections. A descent datum on `Y` with respect to `f` is an isomorphism
`σ : p₁^* Y ≅ p₂^* Y` of schemes over `T ×_S T` satisfying the cocycle condition
`p₁₃^* σ = p₂₃^* σ ∘ p₁₂^* σ` on `T ×_S T ×_S T`.

The category of such data is `AlgebraicGeometry.DescentDatum f`, the one-member family case of
`AlgebraicGeometry.DescentData`. There the gluing isomorphism is an isomorphism
`Y ×_S T ≅ T ×_S Y` of schemes over `T ×_S T`, products being taken in `Over S`. This file
identifies that presentation with the one above.

## Main definitions

* `AlgebraicGeometry.DescentDatum.equivSigma` : a descent datum relative to `f` is the same as a
  scheme `Y` over `T`, a gluing isomorphism over `T ×_S T` and the cocycle condition, and
  nothing more.
* `AlgebraicGeometry.DescentDatum.baseChangeTransition` : the gluing isomorphism of a descent
  datum read as an isomorphism `p₁^* Y ≅ p₂^* Y` of schemes over `T ×_S T`, where
  `p_i^* Y = Y ×_{T, p_i} (T ×_S T)` is the literal fibre product.

* `AlgebraicGeometry.DescentDatum.pullbackBaseChangeIso` : an isomorphism `Y ×_S T ≅ T ×_S Y`
  conjugated by the canonical isomorphisms `p₁^* Y ≅ Y ×_S T` and `T ×_S Y ≅ p₂^* Y` of iterated
  fibre products.

## Main results

* `AlgebraicGeometry.DescentDatum.pullbackBaseChangeIso_hom_snd` : if the isomorphism
  `Y ×_S T ≅ T ×_S Y` preserves both components of the base `T ×_S T`, its conjugate
  `p₁^* Y ≅ p₂^* Y` lies over `T ×_S T`.
* `AlgebraicGeometry.DescentDatum.baseChangeTransition_hom_left` : the underlying morphism of
  `baseChangeTransition` is the conjugate of the gluing isomorphism on literal fibre products.

## Implementation notes

The descent datum itself is not redefined: `AlgebraicGeometry.DescentDatum f` is the object.
Its cocycle condition is stated on the left-associated triple product `(Y ×_S T) ×_S T` in
`Over S`, with `CategoryTheory.Limits.prodMapLastTwo` and
`CategoryTheory.Limits.prodMapFirstThird` inserting the unchanged factor; these are the pullbacks
`p₁₂^* σ`, `p₂₃^* σ` and `p₁₃^* σ` read through the canonical isomorphisms of iterated fibre
products, which is how the source asks the condition to be read.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace DescentDatum

variable {T S : Scheme.{u}} {f : T ⟶ S}

/-- **Descent data relative to one morphism.** A descent datum relative to `f : T ⟶ S` is
exactly a scheme `Y` over `T`, an isomorphism `Y ×_S T ≅ T ×_S Y` of schemes over `T ×_S T`, and
the cocycle condition on the triple fibre product. -/
@[weil "def_fka3_descent_datum_scheme"]
def equivSigma (f : T ⟶ S) :
    DescentDatum f ≃ Σ Y : Over T,
      {σ : Over.mk (prod.map (structureMap f Y) (𝟙 (Over.mk f))) ≅
          Over.mk (prod.map (𝟙 (Over.mk f)) (structureMap f Y)) //
        prod.map σ.hom.left (𝟙 (Over.mk f)) ≫ prodMapLastTwo σ.hom.left =
          prodMapFirstThird σ.hom.left} where
  toFun D := ⟨D.over, D.transition, D.cocycle_triangle⟩
  invFun p := mk' p.1 p.2.1 p.2.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma equivSigma_apply_fst (D : DescentDatum f) : (equivSigma f D).1 = D.over := rfl

@[simp]
lemma equivSigma_apply_snd_coe (D : DescentDatum f) :
    (equivSigma f D).2.val = D.transition := rfl

/-- An isomorphism `Y ×_S T ≅ T ×_S Y` lying over `T ×_S T`, conjugated to the base changes
`p₁^* Y ≅ p₂^* Y`. -/
abbrev pullbackBaseChangeIso (Y : Over T) (φ : pullback (Y.hom ≫ f) f ≅ pullback f (Y.hom ≫ f)) :
    pullback Y.hom (pullback.fst f f) ≅ pullback Y.hom (pullback.snd f f) :=
  pullbackRightPullbackFstIso f f Y.hom ≪≫ φ ≪≫
    (pullbackLeftPullbackSndIso f f Y.hom).symm ≪≫ pullbackSymmetry (pullback.snd f f) Y.hom

lemma pullbackBaseChangeIso_hom_snd (Y : Over T)
    (φ : pullback (Y.hom ≫ f) f ≅ pullback f (Y.hom ≫ f))
    (h₀ : φ.hom ≫ pullback.fst f (Y.hom ≫ f) = pullback.fst (Y.hom ≫ f) f ≫ Y.hom)
    (h₁ : φ.hom ≫ pullback.snd f (Y.hom ≫ f) ≫ Y.hom = pullback.snd (Y.hom ≫ f) f) :
    (pullbackBaseChangeIso Y φ).hom ≫ pullback.snd Y.hom (pullback.snd f f) =
      pullback.snd Y.hom (pullback.fst f f) := by
  apply pullback.hom_ext
  · simp only [pullbackBaseChangeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSymmetry_hom_comp_snd_assoc, pullbackLeftPullbackSndIso_inv_fst]
    rw [h₀, pullbackRightPullbackFstIso_hom_fst_assoc, pullback.condition]
  · simp [h₁]

variable (D : DescentDatum f)

/-- **The descent datum in base-change form.** The gluing isomorphism of a descent datum relative
to `f : T ⟶ S`, as an isomorphism `σ : p₁^* Y ≅ p₂^* Y` of schemes over `T ×_S T`, where
`p₁, p₂ : T ×_S T ⟶ T` are the projections and `p_i^* Y = Y ×_{T, p_i} (T ×_S T)`. -/
@[weil "def_fka3_descent_datum_scheme"]
def baseChangeTransition :
    Over.mk (pullback.snd D.over.hom (pullback.fst f f)) ≅
      Over.mk (pullback.snd D.over.hom (pullback.snd f f)) :=
  Over.isoMk (pullbackBaseChangeIso D.over D.transitionPullbackIso)
    (pullbackBaseChangeIso_hom_snd D.over D.transitionPullbackIso
      D.transitionPullbackIso_hom_comp_pullbackFst D.transitionPullbackIso_hom_comp_pullbackSnd)

@[simp]
lemma baseChangeTransition_hom_left :
    (baseChangeTransition D).hom.left =
      (pullbackBaseChangeIso D.over D.transitionPullbackIso).hom := rfl

end DescentDatum

end AlgebraicGeometry
