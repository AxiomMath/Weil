module

public import Weil.AlgebraicGeometry.Morphisms.Etale
public import Weil.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Fibre products in the étale category `Et(S)`

Let `h : U ⟶ W` and `k : V ⟶ W` be morphisms of the étale category `Et(S)` of noetherian
separated étale `S`-schemes, and let `u : U ⟶ S` be the structure morphism of `U`. Then the
fibre product of schemes `U ×_W V` is noetherian and separated, and `pr₁ ≫ u : U ×_W V ⟶ S` is
étale. Hence `U ×_W V` is an object of `Et(S)`, and with its two projections it is a fibre product
of `h` and `k` in `Et(S)`. In particular `Et(S)` has fibre products, and the functor to schemes
preserves them.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.pullbackObj` — the object `U ×_W V` of
  `Et(S)`, with projections `pullbackFst` and `pullbackSnd`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isNoetherian_isSeparated_etale_pullback` —
  `U ×_W V` is noetherian and separated, and `pr₁ ≫ u` is étale.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isPullback_pullbackFst_pullbackSnd` — the
  object `U ×_W V` with its projections is a fibre product of `h` and `k` in `Et(S)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.hasPullbacks` and
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.preservesPullbacks_toScheme`.

## Implementation notes

`Et(S)` is `AlgebraicGeometry.SmallNoetherianSeparatedEtale B S hS`, whose objects lie below
the size cutoff of the big étale site `B`; the scheme `U ×_W V` lies below the cutoff again
(`AlgebraicGeometry.Scheme.size_pullback_lt`), so it is literally an object of `Et(S)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying scheme of an object of `Et(S)` lies below the cutoff of `B`. -/
lemma contains_toScheme_obj (U : SmallNoetherianSeparatedEtale B S hS) :
    B.Contains ((toScheme B S hS).obj U) :=
  U.obj.obj.left.property

variable {U V W : SmallNoetherianSeparatedEtale B S hS} (h : U ⟶ W) (k : V ⟶ W)

/-- **Fibre products in `Et(S)`, the scheme part** (FK I.2). For morphisms `h : U ⟶ W` and
`k : V ⟶ W` of `Et(S)`, the fibre product `U ×_W V` is a noetherian separated scheme, and
`pr₁ ≫ u : U ×_W V ⟶ S` is étale, where `u` is the structure morphism of `U`. -/
@[weil "lem_fk102_etale_fibre_product_in_et"]
theorem isNoetherian_isSeparated_etale_pullback :
    IsNoetherian (pullback ((toScheme B S hS).map h) ((toScheme B S hS).map k)) ∧
      (pullback ((toScheme B S hS).map h) ((toScheme B S hS).map k)).IsSeparated ∧
      Etale (pullback.fst ((toScheme B S hS).map h) ((toScheme B S hS).map k) ≫
        structureMorphism U) := by
  refine ⟨?_, isSeparated_pullback_of_isSeparated _ _, inferInstance⟩
  have : IsLocallyNoetherian
      (pullback ((toScheme B S hS).map h) ((toScheme B S hS).map k)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst ((toScheme B S hS).map h) ((toScheme B S hS).map k))
  have : CompactSpace ↥(pullback ((toScheme B S hS).map h) ((toScheme B S hS).map k)) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst ((toScheme B S hS).map h) ((toScheme B S hS).map k))
  exact {}

/-- The object `U ×_W V` of `Et(S)`, with structure morphism `pr₁ ≫ u`. -/
noncomputable def pullbackObj : SmallNoetherianSeparatedEtale B S hS :=
  have := (isNoetherian_isSeparated_etale_pullback h k).1
  have := (isNoetherian_isSeparated_etale_pullback h k).2.1
  have := (isNoetherian_isSeparated_etale_pullback h k).2.2
  mk (pullback ((toScheme B S hS).map h) ((toScheme B S hS).map k))
    (Scheme.size_pullback_lt _ _ (contains_toScheme_obj U) (contains_toScheme_obj V))
    (pullback.fst ((toScheme B S hS).map h) ((toScheme B S hS).map k) ≫ structureMorphism U)

@[simp]
lemma toScheme_obj_pullbackObj :
    (toScheme B S hS).obj (pullbackObj h k) =
      pullback ((toScheme B S hS).map h) ((toScheme B S hS).map k) :=
  rfl

@[simp]
lemma structureMorphism_pullbackObj :
    structureMorphism (pullbackObj h k) =
      pullback.fst ((toScheme B S hS).map h) ((toScheme B S hS).map k) ≫ structureMorphism U :=
  rfl

/-- The first projection `U ×_W V ⟶ U` in `Et(S)`. -/
noncomputable def pullbackFst : pullbackObj h k ⟶ U :=
  (homEquiv _ _).symm ⟨pullback.fst ((toScheme B S hS).map h) ((toScheme B S hS).map k), rfl⟩

/-- The second projection `U ×_W V ⟶ V` in `Et(S)`. -/
noncomputable def pullbackSnd : pullbackObj h k ⟶ V :=
  (homEquiv _ _).symm ⟨pullback.snd ((toScheme B S hS).map h) ((toScheme B S hS).map k), by
    rw [structureMorphism_pullbackObj, ← toScheme_map_comp_structureMorphism k,
      ← toScheme_map_comp_structureMorphism h, pullback.condition_assoc]
    rfl⟩

@[simp]
lemma toScheme_map_pullbackFst :
    (toScheme B S hS).map (pullbackFst h k) =
      pullback.fst ((toScheme B S hS).map h) ((toScheme B S hS).map k) :=
  rfl

@[simp]
lemma toScheme_map_pullbackSnd :
    (toScheme B S hS).map (pullbackSnd h k) =
      pullback.snd ((toScheme B S hS).map h) ((toScheme B S hS).map k) :=
  rfl

/-- **Fibre products in `Et(S)`** (FK I.2). For morphisms `h : U ⟶ W` and `k : V ⟶ W` of
`Et(S)`, the object `U ×_W V` of `Et(S)`, with its two projections, is a fibre product of `h` and
`k` in `Et(S)`. -/
@[weil "lem_fk102_etale_fibre_product_in_et"]
theorem isPullback_pullbackFst_pullbackSnd :
    IsPullback (pullbackFst h k) (pullbackSnd h k) h k := by
  refine ⟨⟨hom_ext (by
    simp only [Functor.map_comp, toScheme_map_pullbackFst, toScheme_map_pullbackSnd]
    exact pullback.condition)⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => (homEquiv _ _).symm ⟨pullback.lift ((toScheme B S hS).map s.fst)
      ((toScheme B S hS).map s.snd) (by simp only [← Functor.map_comp, s.condition]), ?_⟩)
    ?_ ?_ ?_⟩⟩
  · exact (pullback.lift_fst_assoc _ _ _ _).trans (toScheme_map_comp_structureMorphism s.fst)
  · intro s; exact hom_ext (pullback.lift_fst _ _ _)
  · intro s; exact hom_ext (pullback.lift_snd _ _ _)
  · intro s m h₁ h₂
    apply hom_ext
    refine pullback.hom_ext ?_ ?_
    · change (toScheme B S hS).map m ≫ (toScheme B S hS).map (pullbackFst h k) = _
      rw [← Functor.map_comp, h₁]
      exact (pullback.lift_fst _ _ _).symm
    · change (toScheme B S hS).map m ≫ (toScheme B S hS).map (pullbackSnd h k) = _
      rw [← Functor.map_comp, h₂]
      exact (pullback.lift_snd _ _ _).symm

instance hasPullback : HasPullback h k :=
  (isPullback_pullbackFst_pullbackSnd h k).hasPullback

/-- `Et(S)` has fibre products. -/
instance hasPullbacks : HasPullbacks (SmallNoetherianSeparatedEtale B S hS) :=
  hasPullbacks_of_hasLimit_cospan _

/-- The functor from `Et(S)` to schemes preserves fibre products. -/
instance preservesPullbacks_toScheme :
    PreservesLimitsOfShape WalkingCospan (toScheme B S hS) := by
  refine ⟨fun {F} => ?_⟩
  have : PreservesLimit (cospan (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr))
      (toScheme B S hS) := by
    let f := F.map WalkingCospan.Hom.inl
    let g := F.map WalkingCospan.Hom.inr
    have hP := isPullback_pullbackFst_pullbackSnd f g
    have hQ : IsPullback ((toScheme B S hS).map (pullbackFst f g))
        ((toScheme B S hS).map (pullbackSnd f g)) ((toScheme B S hS).map f)
        ((toScheme B S hS).map g) := by
      rw [toScheme_map_pullbackFst, toScheme_map_pullbackSnd]
      exact IsPullback.of_hasPullback _ _
    exact preservesLimit_of_preserves_limit_cone hP.isLimit
      ((isLimitMapConePullbackConeEquiv _ hP.w).symm hQ.isLimit)
  exact preservesLimit_of_iso_diagram _ (diagramIsoCospan F).symm

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
