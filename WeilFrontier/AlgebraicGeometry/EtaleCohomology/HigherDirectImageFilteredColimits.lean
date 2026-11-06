module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageFilteredColimits
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.Attr

/-!
# Higher direct images commute with filtered colimits

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes (for instance a
morphism of noetherian separated schemes), and let `(F_ν)_{ν ∈ I}` be a filtered system of abelian
sheaves on the small étale site of `X`, with colimit `F` and coprojections `ι_ν`. Then for every
`i ≥ 0` the maps `R^i f_*(ι_ν)` induce an isomorphism `colim_ν R^i f_* F_ν ≅ R^i f_* F`, the
colimit being taken in the category of abelian sheaves on the small étale site of `Y`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.preservesColimitsOfShape_higherDirectImage`: the higher direct
  image `R^i f_*` on the size-bounded small étale sites preserves filtered colimits.
* `AlgebraicGeometry.BigEtaleSite.isIso_colimit_post_higherDirectImage`: the canonical map
  `colim_ν R^i f_* F_ν ⟶ R^i f_* (colim_ν F_ν)` is an isomorphism.

## Implementation notes

On Mathlib's small étale sites this is
`Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs`
([Stacks, Tag 09Z1]); it is transported to the size-bounded sites `SmallEtale` along the
equivalences of sheaf categories `AlgebraicGeometry.SmallEtale.sheafEquiv`, which identify the two
higher direct images (`AlgebraicGeometry.BigEtaleSite.etaleAbelianHigherDirectImageIso`).

The source assumes `X` and `Y` noetherian and separated; only quasi-compactness and
quasi-separatedness of `f` are used, and both hold for a morphism from a noetherian scheme.
Coefficients are `AddCommGrpCat.{max (u + 1) v}` and the index categories lie in
`Type (max (u + 1) v)`, the sizes at which the comparison with Mathlib's small étale site is
available.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify X.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasInjectiveResolutions (Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasInjectiveResolutions
    (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})]

/-- **Higher direct images commute with filtered colimits.** For a quasi-compact and
quasi-separated morphism `f` of a big étale site, the higher direct image `R^i f_*` of abelian
sheaves on the small étale sites preserves filtered colimits. -/
theorem preservesColimitsOfShape_higherDirectImage
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)] (i : ℕ)
    (I : Type (max (u + 1) v)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (higherDirectImage.{max (u + 1) v} B f i) := by
  set EX := SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{max (u + 1) v}
  set EY := SmallEtale.sheafEquiv B Y.obj Y.property AddCommGrpCat.{max (u + 1) v}
  have h₀ : PreservesColimitsOfShape I
      (Stacks.EtaleCohomology.etaleAbelianHigherDirectImage.{u, v} (B.inclusion.map f) i) :=
    Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs
      (B.inclusion.map f) i I
  have h₁ : PreservesColimitsOfShape I
      (EX.inverse ⋙ higherDirectImage.{max (u + 1) v} B f i ⋙ EY.functor) :=
    preservesColimitsOfShape_of_natIso (etaleAbelianHigherDirectImageIso.{u, v} B f i)
  have h₂ : PreservesColimitsOfShape I
      ((EX.functor ⋙ EX.inverse) ⋙ higherDirectImage.{max (u + 1) v} B f i ⋙ EY.functor ⋙
        EY.inverse) := by
    have h₃ : PreservesColimitsOfShape I
        (EX.functor ⋙ (EX.inverse ⋙ higherDirectImage.{max (u + 1) v} B f i ⋙ EY.functor) ⋙
          EY.inverse) := inferInstance
    exact h₃
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerRight EX.unitIso.symm _ ≪≫ Functor.leftUnitor _ ≪≫
      Functor.isoWhiskerLeft _ EY.unitIso.symm ≪≫ Functor.rightUnitor _ :
      (EX.functor ⋙ EX.inverse) ⋙ higherDirectImage.{max (u + 1) v} B f i ⋙
        EY.functor ⋙ EY.inverse ≅ higherDirectImage.{max (u + 1) v} B f i)

/-- **Higher direct images commute with filtered colimits** (FK I.4). Let `f` be a quasi-compact
and quasi-separated morphism of a big étale site, for instance a morphism of noetherian separated
schemes, and `F` a filtered system of abelian sheaves on the small étale site of its source. For
every `i`, the canonical map `colim_ν R^i f_* F_ν ⟶ R^i f_* (colim_ν F_ν)`, whose `ν`-th component
is `R^i f_*(ι_ν)` for the coprojection `ι_ν`, is an isomorphism of abelian sheaves on the small
étale site of the target. -/
@[weil "lem_fk104_higher_direct_image_commutes_filtered_colimits"]
theorem isIso_colimit_post_higherDirectImage
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)] (i : ℕ)
    {I : Type (max (u + 1) v)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    IsIso (colimit.post F (higherDirectImage.{max (u + 1) v} B f i)) := by
  have := preservesColimitsOfShape_higherDirectImage.{v} B f i I
  infer_instance

end AlgebraicGeometry.BigEtaleSite
