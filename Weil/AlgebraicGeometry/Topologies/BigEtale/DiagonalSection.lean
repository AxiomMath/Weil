module

public import Weil.Defs.AlgebraicGeometry.Topologies.BigEtale.DiagonalSection
public import Weil.Attr

/-!
# The diagonal of an étale morphism is open and closed

Let `f : U ⟶ V` be an étale morphism of a big étale site, and regard `U ×_V U` as the base change
of the étale `V`-scheme `U` along `f`, an object of the small étale site of `U`. The diagonal
`Δ : U ⟶ U ×_V U` is a section of the étale second projection `U ×_V U ⟶ U`, hence étale, hence
open. When `f` is separated it is moreover a section of a separated morphism, hence a closed
immersion. So the diagonal `Δ(U)` is open and closed in `U ×_V U`, and the diagonal section
`s_f` (equal to `1` on the connected components meeting `Δ(U)` and to `0` on the others) is the
indicator function of `Δ(U)`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.smallEtaleBaseChangeToSelf`: the second projection
  `U ×_V U ⟶ U`, as a morphism of the small étale site of `U` to its final object.

## Main results

* `AlgebraicGeometry.BigEtaleSite.isClopen_range_smallEtaleDiagonal`: for `f` étale and
  separated, the diagonal `Δ(U)` is open and closed in `U ×_V U`.
* `AlgebraicGeometry.BigEtaleSite.diagonalSection_eq_indicator`: the diagonal section is the
  indicator function of `Δ(U)`.

## Implementation notes

The source assumes `U` and `V` noetherian and separated; only the separatedness of `f` (which
follows from that of `U`) is used for closedness, and noetherianity enters only through the
discreteness of the space of connected components of `U ×_V U`, which the definition of the
diagonal section takes as a hypothesis.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {U V : B.Scheme} (f : U ⟶ V) [Etale (B.inclusion.map f)]

/-- The structure morphism `U ×_V U ⟶ U` (second projection), as a morphism of the small étale
site of `U` to its final object. -/
noncomputable def smallEtaleBaseChangeToSelf :
    (smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f) ⟶ SmallEtale.ofEtaleHom B (𝟙 U) :=
  ObjectProperty.homMk (Over.homMk (pullback.snd f f) (by simp))

/-- The diagonal is a section of the second projection. -/
@[reassoc (attr := simp)]
lemma smallEtaleDiagonal_comp_baseChangeToSelf :
    smallEtaleDiagonal B f ≫ smallEtaleBaseChangeToSelf B f = 𝟙 _ := by
  apply (BigEtaleOver.IsEtaleOver B U.obj U.property).ι.map_injective
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- The second projection `U ×_V U ⟶ U` is étale. -/
instance etale_toScheme_map_smallEtaleBaseChangeToSelf :
    Etale ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleBaseChangeToSelf B f)) :=
  ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f)).property

/-- The diagonal of an étale morphism is étale. -/
instance etale_toScheme_map_smallEtaleDiagonal :
    Etale ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f)) := by
  refine MorphismProperty.of_postcomp @Etale (W' := @Etale) _
    ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleBaseChangeToSelf B f)) inferInstance ?_
  rw [← CategoryTheory.Functor.map_comp, smallEtaleDiagonal_comp_baseChangeToSelf]
  infer_instance

/-- The second projection `U ×_V U ⟶ U` of a separated morphism is separated. -/
instance isSeparated_toScheme_map_smallEtaleBaseChangeToSelf [IsSeparated (B.inclusion.map f)] :
    IsSeparated ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleBaseChangeToSelf B f)) :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f f).map B.inclusion)
    (‹IsSeparated (B.inclusion.map f)›)

/-- The diagonal of a separated étale morphism is a closed immersion. -/
instance isClosedImmersion_toScheme_map_smallEtaleDiagonal [IsSeparated (B.inclusion.map f)] :
    IsClosedImmersion ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f)) := by
  have : IsClosedImmersion ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f) ≫
      (SmallEtale.toScheme B U.obj U.property).map (smallEtaleBaseChangeToSelf B f)) := by
    rw [← CategoryTheory.Functor.map_comp, smallEtaleDiagonal_comp_baseChangeToSelf]
    infer_instance
  exact IsClosedImmersion.of_comp _
    ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleBaseChangeToSelf B f))

/-- **The diagonal of a separated étale morphism is open and closed**: for `f : U ⟶ V` étale and
separated, `Δ(U)` is open and closed in `U ×_V U`. -/
@[weil "lem_fk105_etale_diagonal_open_closed"]
theorem isClopen_range_smallEtaleDiagonal [IsSeparated (B.inclusion.map f)] :
    IsClopen (Set.range ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f))) :=
  ⟨(IsClosedImmersion.isClosedEmbedding _).isClosed_range,
    ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f)).isOpenMap.isOpen_range⟩

variable (Λ : Type w) [AddCommGroup Λ] [One Λ]
  [DiscreteTopology (_root_.ConnectedComponents
    ((SmallEtale.toScheme B U.obj U.property).obj
      ((smallEtaleBaseChange B f).obj (SmallEtale.ofEtaleHom B f))))]

/-- For `f : U ⟶ V` étale and separated, **the diagonal section `s_f` is the indicator function
of the diagonal** `Δ(U) ⊆ U ×_V U`. -/
@[weil "lem_fk105_etale_diagonal_open_closed"]
theorem diagonalSection_eq_indicator [IsSeparated (B.inclusion.map f)] :
    ⇑(show LocallyConstant _ Λ from diagonalSection B f Λ) =
      Set.indicator
        (Set.range ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f))) 1 := by
  funext z
  by_cases hz :
    z ∈ Set.range ((SmallEtale.toScheme B U.obj U.property).map (smallEtaleDiagonal B f))
  · obtain ⟨x, rfl⟩ := hz
    rw [Set.indicator_of_mem (Set.mem_range_self x)]
    exact diagonalSection_apply_diagonal B f Λ x
  · rw [Set.indicator_of_notMem hz]
    refine diagonalSection_apply_of_disjoint B f Λ z ?_
    rw [Set.disjoint_iff]
    rintro y ⟨hyz, hy⟩
    apply hz
    have h := (isClopen_range_smallEtaleDiagonal B f).connectedComponent_subset hy
    rw [← connectedComponent_eq hyz] at h
    exact h mem_connectedComponent

end AlgebraicGeometry.BigEtaleSite
