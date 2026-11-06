module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import Weil.Attr

/-!
# The canonical descent datum of a pulled-back quasi-coherent module

Let `f : T ⟶ S` be a morphism of schemes and `M` a quasi-coherent `𝒪_S`-module. Write
`p₁, p₂ : T ×_S T ⟶ T` for the two projections and `q = f ∘ p₁ = f ∘ p₂`. The composite
pullback isomorphisms `c_i : p_i^* f^* M ≅ q^* M` of the pullback pseudofunctor give the
*canonical descent datum* `σ_M = c₂⁻¹ ∘ c₁ : p₁^* f^* M ≅ p₂^* f^* M` on `f^* M`.

## Main definitions

* `AlgebraicGeometry.canonicalDescentIso f M` is the isomorphism `σ_M`, defined literally as
  `c₂⁻¹ ∘ c₁`.
* `AlgebraicGeometry.canonicalDescentDatum f M` is the descent datum `(f^* M, σ_M)` with
  respect to the one-member family `{f}`, as an object of
  `AlgebraicGeometry.QuasicoherentDescentData`; it is the value at `M` of
  `AlgebraicGeometry.canonicalDescentFunctor`.

## Main results

* `AlgebraicGeometry.canonicalDescentDatum_obj` : the component of the datum is `f^* M`.
* `AlgebraicGeometry.canonicalDescentDatum_hom_fst_snd` : the transition of the datum over
  `T ×_S T`, from the first to the second projection, is `σ_M`.
* `AlgebraicGeometry.canonicalDescentDatum_hom` : over an arbitrary `Y` with two maps
  `g₁ g₂ : Y ⟶ T` agreeing over `S`, the transition is the analogous composite of composite
  pullback isomorphisms.

## Implementation notes

The descent datum is Mathlib's invariant `Pseudofunctor.DescentData` for the pseudofunctor
of sheaves of modules, whose transitions are given over every scheme mapping to two members of
the family; the binary fibre product presentation of the source is recovered from the
transition over `T ×_S T` with its two projections, which is `σ_M`. The one-member family is
indexed by `PUnit.{w + 1}` for an arbitrary universe `w`, so that the results requiring a large
index type (full faithfulness of the canonical descent functor for fpqc families) apply.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w u

namespace AlgebraicGeometry

variable {T S : Scheme.{u}} (f : T ⟶ S)
  (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)

/-- The canonical descent datum `σ_M = c₂⁻¹ ∘ c₁ : p₁^* f^* M ≅ p₂^* f^* M` on the pullback
`f^* M`, where `p₁, p₂` are the projections of `T ×_S T` and
`c_i : p_i^* f^* M ≅ (f ∘ p_i)^* M` are the composite pullback isomorphisms
(using `f ∘ p₁ = f ∘ p₂`). -/
@[weil "def_fka3_canonical_descent_datum"]
noncomputable def canonicalDescentIso :
    (modulePullbackPseudofunctor.map (pullback.fst f f).op.toLoc).toFunctor.obj
        ((modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.obj M.obj) ≅
      (modulePullbackPseudofunctor.map (pullback.snd f f).op.toLoc).toFunctor.obj
        ((modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.obj M.obj) :=
  ((Cat.Hom.toNatIso (modulePullbackPseudofunctor.mapComp' f.op.toLoc
      (pullback.fst f f).op.toLoc (pullback.fst f f ≫ f).op.toLoc rfl)).app M.obj).symm ≪≫
    (Cat.Hom.toNatIso (modulePullbackPseudofunctor.mapComp' f.op.toLoc
      (pullback.snd f f).op.toLoc (pullback.fst f f ≫ f).op.toLoc
      (by rw [pullback.condition]; rfl))).app M.obj

/-- The canonical descent datum `(f^* M, σ_M)` of a quasi-coherent module `M` with respect to
`f`, as a quasi-coherent descent datum for the one-member family `{f}`: the value at `M` of
the canonical descent functor. -/
@[weil "def_fka3_canonical_descent_datum"]
noncomputable abbrev canonicalDescentDatum :
    QuasicoherentDescentData (fun _ : PUnit.{w + 1} ↦ f) :=
  (canonicalDescentFunctor (fun _ : PUnit.{w + 1} ↦ f)).obj M

/-- The component of the canonical descent datum is the pullback `f^* M`. -/
theorem canonicalDescentDatum_obj (i : PUnit.{w + 1}) :
    (canonicalDescentDatum.{w} f M).obj.obj i =
      (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.obj M.obj :=
  rfl

/-- Over an arbitrary scheme `Y` with maps `g₁ g₂ : Y ⟶ T` that agree over `S`, the transition
of the canonical descent datum is `(g₁^* f^* M ≅ q^* M ≅ g₂^* f^* M)`, built from the composite
pullback isomorphisms. -/
theorem canonicalDescentDatum_hom {Y : Scheme.{u}} (q : Y ⟶ S) (g₁ g₂ : Y ⟶ T)
    (h₁ : g₁ ≫ f = q) (h₂ : g₂ ≫ f = q) :
    (canonicalDescentDatum.{w} f M).obj.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) g₁ g₂
        h₁ h₂ =
      (modulePullbackPseudofunctor.mapComp' f.op.toLoc g₁.op.toLoc q.op.toLoc
          (by rw [← h₁]; rfl)).inv.toNatTrans.app M.obj ≫
        (modulePullbackPseudofunctor.mapComp' f.op.toLoc g₂.op.toLoc q.op.toLoc
          (by rw [← h₂]; rfl)).hom.toNatTrans.app M.obj :=
  rfl

/-- The transition of the canonical descent datum over `T ×_S T`, from the first projection to
the second, is `σ_M`. -/
theorem canonicalDescentDatum_hom_fst_snd :
    (canonicalDescentDatum.{w} f M).obj.hom (pullback.fst f f ≫ f)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) (pullback.fst f f) (pullback.snd f f) rfl
        pullback.condition.symm =
      (canonicalDescentIso f M).hom :=
  rfl

/-- `σ_M` is the isomorphism of the canonical descent datum over `T ×_S T`. -/
theorem canonicalDescentDatum_iso_fst_snd :
    (canonicalDescentDatum.{w} f M).obj.iso (pullback.fst f f ≫ f)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) (pullback.fst f f) (pullback.snd f f) rfl
        pullback.condition.symm =
      canonicalDescentIso f M :=
  Iso.ext (canonicalDescentDatum_hom_fst_snd.{w} f M)

end AlgebraicGeometry
