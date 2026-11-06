module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteTypeTwiceDimension
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomologyBijective
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import WeilFrontier.Defs.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import Weil.Attr

/-!
# Restriction to a closed fibre of dimension at most one in degrees at least three

Let `A` be a strictly Henselian local ring with residue field `k`, `f : X ⟶ Spec A` a morphism of
finite type, `X₀ = X ×_{Spec A} Spec k` its closed fibre and `i : X₀ ⟶ X` the inclusion. If
`dim X₀ ≤ 1`, then for every `n ≥ 1` the restriction map
`i^* : H^q(X, ℤ/n) ⟶ H^q(X₀, i^*(ℤ/n))` is surjective for every `q ≥ 3`: its target vanishes.
Indeed `X₀` is of finite type over the separably closed field `k` and of dimension at most one,
and `i^*(ℤ/n)` is a torsion sheaf, so its cohomology vanishes in degrees `q ≥ 3`
(`AlgebraicGeometry.SmallEtale.subsingleton_sheafH_of_isTorsionSheaf_of_topologicalKrullDim_le`,
with cohomological dimension zero for a separably closed field).

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_closedFibre_of_three_le`: `H^q(X₀, G) = 0` for `q ≥ 3`
  and every abelian sheaf `G` on `X₀` killed by some `n ≥ 1`.
* `AlgebraicGeometry.surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_three_le`: the
  restriction `H^q(X, F) ⟶ H^q(X₀, i^* F)` is surjective for `q ≥ 3` and every abelian sheaf `F`
  on `X` killed by some `n ≥ 1`.
* `AlgebraicGeometry.surjective_smallEtaleCohomologyRestrictionMap_closedFibre_zmod_of_three_le`:
  the case `F = (ℤ/n)_X`.

## Implementation notes

The hypotheses are weaker than in the source: of `A` only that it is local with separably closed
residue field is used (no Henselian property, no noetherian hypothesis), `f` is locally of finite
type and quasi-compact rather than projective, and `n` need not be invertible in `A`. The target
sheaf is the inverse image `i^*(ℤ/n)_X`, which is the constant sheaf `(ℤ/n)_{X₀}` by
`AlgebraicGeometry.smallEtaleInverseImageConstantSheafIso`; only its being killed by `n` is used.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [IsLocalRing A]
  [IsSepClosed (ResidueField A)] (X : B.Scheme) (f : X.obj ⟶ Spec (.of A))
  [LocallyOfFiniteType f] [QuasiCompact f]
  (hX₀ : B.Contains (Stacks.EtaleCohomology.closedFibre A f))

/-- **Cohomology of the closed fibre vanishes in degrees at least three.** Let `A` be a local ring
with separably closed residue field, `f : X ⟶ Spec A` locally of finite type and quasi-compact,
with closed fibre `X₀` of dimension at most one. For every abelian sheaf `G` on `X₀` killed by
some `n ≥ 1`, `H^q(X₀, G) = 0` for every `q ≥ 3`. -/
theorem subsingleton_sheafH_closedFibre_of_three_le
    (hdim : topologicalKrullDim (Stacks.EtaleCohomology.closedFibre A f) ≤ 1)
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Stacks.EtaleCohomology.closedFibre A f) hX₀)
      AddCommGrpCat.{u + 1})]
    (G : Sheaf (SmallEtale.topology B (Stacks.EtaleCohomology.closedFibre A f) hX₀)
      AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n) (hG : n • 𝟙 G = 0) (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{w} G q) := by
  let π : Stacks.EtaleCohomology.closedFibre A f ⟶ Spec (.of (ResidueField A)) :=
    Stacks.EtaleCohomology.closedFibreProjection A f
  have : LocallyOfFiniteType π := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (Stacks.EtaleCohomology.isPullback_closedFibre A f) ‹_›
  have : QuasiCompact π := MorphismProperty.of_isPullback (P := @QuasiCompact)
    (Stacks.EtaleCohomology.isPullback_closedFibre A f) ‹_›
  have hT : SmallEtale.IsTorsionSheaf B _ hX₀ G := by
    intro U x
    refine ⟨⊤, (SmallEtale.topology B _ hX₀).top_mem U, fun V g _ => ⟨n, hn, ?_⟩⟩
    have h := congrArg (fun φ : G ⟶ G => φ.hom.app (Opposite.op V) (G.obj.map g.op x)) hG
    have e : (n • 𝟙 G).hom = n • 𝟙 G.obj := (sheafToPresheaf _ AddCommGrpCat.{u + 1}).map_nsmul
    simp only at h
    rw [e, NatTrans.app_nsmul] at h
    change (n • 𝟙 (G.obj.obj (Opposite.op V))).hom _ =
      (0 : G.obj.obj (Opposite.op V) ⟶ G.obj.obj (Opposite.op V)).hom _ at h
    simpa using h
  refine SmallEtale.subsingleton_sheafH_of_isTorsionSheaf_of_topologicalKrullDim_le
    (ResidueField A) B hX₀ π 1 (by exact_mod_cast hdim) G hT q ?_
  have h0 := Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed (ResidueField A)
  rw [nonpos_iff_eq_zero.mp h0, add_zero]
  exact_mod_cast hq

/-- **Restriction to a closed fibre of dimension at most one is surjective in degrees at least
three.** Let `A` be a local ring with separably closed residue field, `f : X ⟶ Spec A` locally of
finite type and quasi-compact, and `i : X₀ ⟶ X` the inclusion of the closed fibre, with
`dim X₀ ≤ 1`. For every abelian sheaf `F` on `X` killed by some `n ≥ 1`, the restriction map
`i^* : H^q(X, F) ⟶ H^q(X₀, i^* F)` is surjective for every `q ≥ 3`. -/
theorem surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_three_le
    (hdim : topologicalKrullDim (Stacks.EtaleCohomology.closedFibre A f) ≤ 1)
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Stacks.EtaleCohomology.closedFibre A f) hX₀)
      AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) {n : ℕ}
    (hn : 0 < n) (hF : n • 𝟙 F = 0) (q : ℕ) (hq : 3 ≤ q) :
    Function.Surjective (smallEtaleCohomologyRestrictionMap.{w} B
      (B.closedFibreInclusion A X f hX₀) F q) := by
  let L := smallEtaleInverseImage B (B.closedFibreInclusion A X f hX₀) AddCommGrpCat.{u + 1}
  have hG : n • 𝟙 (L.obj F) = 0 := by
    rw [← L.map_id, ← Functor.map_nsmul, hF, Functor.map_zero]
  have := subsingleton_sheafH_closedFibre_of_three_le B A X f hX₀ hdim (L.obj F) hn hG q hq
  exact fun y => ⟨0, Subsingleton.elim _ _⟩

/-- **Freitag–Kiehl I.6.1, assertion b), `i > 2`.** Let `A` be a strictly Henselian local ring,
`f : X ⟶ Spec A` locally of finite type and quasi-compact (for instance projective), and
`i : X₀ ⟶ X` the inclusion of the closed fibre, with `dim X₀ ≤ 1`. For every `n ≥ 1` the
restriction map `i^* : H^q(X, ℤ/n) ⟶ H^q(X₀, i^*(ℤ/n))` is surjective for every `q ≥ 3`. -/
@[weil "lem_fk106_dim_le_1_hi_surjective_i_gt_2"]
theorem surjective_smallEtaleCohomologyRestrictionMap_closedFibre_zmod_of_three_le
    (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A] (f : X.obj ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hX₀ : B.Contains (Stacks.EtaleCohomology.closedFibre A f))
    (hdim : topologicalKrullDim (Stacks.EtaleCohomology.closedFibre A f) ≤ 1)
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Stacks.EtaleCohomology.closedFibre A f) hX₀)
      AddCommGrpCat.{u + 1})]
    (n : ℕ) [NeZero n] (q : ℕ) (hq : 3 ≤ q) :
    Function.Surjective (smallEtaleCohomologyRestrictionMap.{w} B
      (B.closedFibreInclusion A X f hX₀)
      ((constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) q) := by
  refine surjective_smallEtaleCohomologyRestrictionMap_closedFibre_of_three_le B A X f hX₀ hdim _
    (Nat.pos_of_ne_zero (NeZero.ne n)) ?_ q hq
  have h : n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) = 0 := by
    ext x
    simp
  let C := constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}
  have : C.Additive := Functor.additive_of_preserves_binary_products _
  rw [← C.map_id, ← Functor.map_nsmul, h, Functor.map_zero]

end AlgebraicGeometry
