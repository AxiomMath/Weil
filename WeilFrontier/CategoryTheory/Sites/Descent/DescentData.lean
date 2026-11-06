module

public import WeilFrontier.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import WeilFrontier.Defs.AlgebraicGeometry.Descent.QuasiCoherent.DescentDatumSheaf
public import Weil.Attr

/-!
# A descent datum is the identity along the diagonal

Let `(𝒩, σ)` be a descent datum on quasi-coherent sheaves with respect to a morphism of
schemes `f : T ⟶ S`, with `σ : p₁^* 𝒩 ≅ p₂^* 𝒩` on `T ×_S T`. Pulling `σ` back along the
diagonal `δ : T ⟶ T ×_S T` gives an endomorphism `δ^⋆ σ` of `𝒩`, and this endomorphism is the
identity.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentDatum.diagonalPullHom_sigma`: `δ^⋆ σ = 𝟙 𝒩`.

## Implementation notes

A descent datum is an object of Mathlib's `Pseudofunctor.DescentData`, which records a
transition morphism over every `S`-scheme mapping twice to `T`, compatibly with pullback
(`Pseudofunctor.DescentData.pullHom_hom`), and equal to the identity when the two maps agree
(`Pseudofunctor.DescentData.hom_self`). The pullback of `σ` along the diagonal is therefore
the transition morphism for the pair `(𝟙 T, 𝟙 T)`, which is the identity. The derivation of
the diagonal identity from the cocycle condition for isomorphisms, which is the argument of
the reference, is `Pseudofunctor.DescentData'.pullHom'_self_eq_id_of_iso`, used when a
descent datum is built from an isomorphism satisfying the cocycle condition alone
(`AlgebraicGeometry.QuasicoherentDescentDatum.mk'`).

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

namespace AlgebraicGeometry.QuasicoherentDescentDatum

variable {T S : Scheme.{u}} {f : T ⟶ S}

/-- For a descent datum `(𝒩, σ)` with respect to `f : T ⟶ S`, the pullback `δ^⋆ σ : 𝒩 ⟶ 𝒩` of
`σ : p₁^* 𝒩 ≅ p₂^* 𝒩` along the diagonal `δ : T ⟶ T ×_S T` is the identity of `𝒩`. -/
@[weil "lem_fka3_descent_datum_diagonal_identity"]
theorem diagonalPullHom_sigma (D : QuasicoherentDescentDatum f) :
    Scheme.Modules.diagonalPullHom f (D.sigma (selfPullback f)).hom = 𝟙 D.module := by
  unfold Scheme.Modules.diagonalPullHom
  rw [sigma_hom,
    D.obj.pullHom_hom (pullback.diagonal f) _ _ rfl _ _ _ _ (𝟙 T) (𝟙 T) (by simp) (by simp),
    D.obj.hom_self _ _ (by simp)]
  · exact (Category.id_comp _).trans ((Scheme.Modules.pullbackId T).inv_hom_id_app _)
  · exact (selfPullback f).hp₁
  · exact (selfPullback f).hp₂

end AlgebraicGeometry.QuasicoherentDescentDatum
