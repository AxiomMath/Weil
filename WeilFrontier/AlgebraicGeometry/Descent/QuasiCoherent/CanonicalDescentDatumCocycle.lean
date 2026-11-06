module

public import WeilFrontier.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import WeilFrontier.Defs.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import WeilFrontier.Defs.AlgebraicGeometry.Descent.QuasiCoherent.DescentDatumSheaf
public import Weil.Attr

/-!
# The canonical descent datum satisfies the cocycle condition

Let `f : T ⟶ S` be a morphism of schemes and `M` a quasi-coherent `𝒪_S`-module. The canonical
isomorphism `σ_M = c₂⁻¹ ∘ c₁ : p₁^* f^* M ≅ p₂^* f^* M` on `T ×_S T` satisfies the cocycle
condition `p₁₃^* σ_M = p₂₃^* σ_M ∘ p₁₂^* σ_M` on `T ×_S T ×_S T`, so that `(f^* M, σ_M)` is a
descent datum on `f^* M` with respect to `f`.

## Main results

* `AlgebraicGeometry.isCocycle_canonicalDescentIso`: `σ_M` satisfies the cocycle condition over
  any chosen triple fibre product of `T ×_S T`.
* `AlgebraicGeometry.canonicalDescentDatum_sigma`: the canonical descent datum of `M`, viewed
  as a descent datum with respect to `f`, has underlying module `f^* M` and isomorphism `σ_M`.

## Implementation notes

The cocycle identity is a consequence of the coherence of the composite pullback isomorphisms
of the pseudofunctor of sheaves of modules: it is built into Mathlib's
`CategoryTheory.Pseudofunctor.toDescentData`, of which the canonical descent datum is a value.
We read the cocycle condition off that descent datum over the binary fibre product.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
  CategoryTheory.Pseudofunctor.DescentData'

universe u

namespace AlgebraicGeometry

variable {T S : Scheme.{u}} (f : T ⟶ S)
  (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)

/-- The canonical descent datum of `M`, as a descent datum with respect to `f`, has underlying
module `f^* M` and, on `T ×_S T`, the isomorphism `σ_M`. -/
@[weil "lem_fka3_canonical_descent_datum_cocycle"]
theorem canonicalDescentDatum_sigma :
    QuasicoherentDescentDatum.module (canonicalDescentDatum.{0} f M) =
        (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.obj M.obj ∧
      QuasicoherentDescentDatum.sigma (canonicalDescentDatum.{0} f M) (selfPullback f) =
        canonicalDescentIso f M :=
  ⟨rfl, canonicalDescentDatum_iso_fst_snd.{0} f M⟩

/-- The canonical isomorphism `σ_M : p₁^* f^* M ≅ p₂^* f^* M` satisfies the cocycle condition
`p₁₃^* σ_M = p₂₃^* σ_M ∘ p₁₂^* σ_M` over any chosen triple fibre product of `T ×_S T`. -/
@[weil "lem_fka3_canonical_descent_datum_cocycle"]
theorem isCocycle_canonicalDescentIso
    (sq₃ : ChosenPullback₃ (selfPullback f) (selfPullback f) (selfPullback f)) :
    IsCocycle (F := modulePullbackPseudofunctor) (selfPullback f) sq₃
      (canonicalDescentIso f M).hom := by
  have h := QuasicoherentDescentDatum.isCocycle_sigma (canonicalDescentDatum.{0} f M)
    (selfPullback f) sq₃
  rwa [(canonicalDescentDatum_sigma f M).2] at h

end AlgebraicGeometry
