module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Morphisms.Immersion
public import WeilFrontier.Defs.AlgebraicGeometry.Flatness.Flattening.CompactificationDominates

/-!
# Any two compactifications are dominated by a third

Let `f : X ⟶ S` be a morphism of schemes and let `c₁ = (X̄₁, j₁, f̄₁)` and `c₂ = (X̄₂, j₂, f̄₂)`
be compactifications of `f`. Let `P = X̄₁ ×_S X̄₂` and let `ι = (j₁, j₂) : X ⟶ P`. Since `j₁`
is an immersion and the projection `P ⟶ X̄₁` is separated, `ι` is an immersion; when `j₁` is
quasi-compact, so is `ι`, and `ι` is then an open immersion into its scheme-theoretic image
`X̄ ⊆ P`. The scheme `X̄` is proper over `S` (a closed subscheme of `P`, which is proper over
`X̄₁`, itself proper over `S`), so `(X̄, ι, X̄ ⟶ S)` is a compactification of `f`, and the two
projections restricted to `X̄` show that it dominates both `c₁` and `c₂`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.Compactification.exists_dominates_and_dominates`: if the open
  immersion of `c₁` is quasi-compact, there is a compactification of `f` dominating both `c₁`
  and `c₂`.
* `AlgebraicGeometry.Scheme.Hom.Compactification.exists_dominates_and_dominates_of_isNoetherian`:
  the same for a noetherian source, as in the source.

## Implementation notes

The source works with noetherian schemes; noetherianity is used only to make the immersion
`ι` quasi-compact, which already follows from the quasi-compactness of `j₁` (the projection
`P ⟶ X̄₁` being separated). The main result assumes only that.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8, p. 86.
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

namespace Compactification

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Two compactifications `c₁`, `c₂` of `f`, the first with quasi-compact open immersion, are
both dominated by a third compactification: the scheme-theoretic image of `X` in the fibre
product of the two ambient schemes over the base. -/
@[weil "lem_fk108_compactifications_common_domination"]
theorem exists_dominates_and_dominates (c₁ c₂ : f.Compactification)
    [QuasiCompact c₁.immersion] :
    ∃ c : f.Compactification, c.Dominates c₁ ∧ c.Dominates c₂ := by
  let m : X ⟶ pullback c₁.toBase c₂.toBase :=
    pullback.lift c₁.immersion c₂.immersion (by simp)
  have hm₁ : m ≫ pullback.fst _ _ = c₁.immersion := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd _ _ = c₂.immersion := pullback.lift_snd _ _ _
  have : IsImmersion (m ≫ pullback.fst _ _) := by rw [hm₁]; infer_instance
  have : IsImmersion m := IsImmersion.of_comp m (pullback.fst _ _)
  have : QuasiCompact (m ≫ pullback.fst _ _) := by rw [hm₁]; infer_instance
  have : QuasiCompact m := QuasiCompact.of_comp m (pullback.fst _ _)
  have hmS : m.toImage ≫ m.imageι ≫ pullback.fst _ _ ≫ c₁.toBase = f := by
    rw [m.toImage_imageι_assoc, reassoc_of% hm₁, immersion_comp_toBase]
  let c : f.Compactification :=
    mk m.image m.toImage (m.imageι ≫ pullback.fst _ _ ≫ c₁.toBase) hmS
  refine ⟨c, ⟨homMk (c₂ := c₁) (m.imageι ≫ pullback.fst _ _) ?_ ?_⟩,
    ⟨homMk (c₂ := c₂) (m.imageι ≫ pullback.snd _ _) ?_ ?_⟩⟩
  · change m.toImage ≫ m.imageι ≫ pullback.fst _ _ = c₁.immersion
    rw [m.toImage_imageι_assoc, hm₁]
  · change (m.imageι ≫ pullback.fst _ _) ≫ c₁.toBase = m.imageι ≫ pullback.fst _ _ ≫ c₁.toBase
    rw [Category.assoc]
  · change m.toImage ≫ m.imageι ≫ pullback.snd _ _ = c₂.immersion
    rw [m.toImage_imageι_assoc, hm₂]
  · change (m.imageι ≫ pullback.snd _ _) ≫ c₂.toBase = m.imageι ≫ pullback.fst _ _ ≫ c₁.toBase
    rw [Category.assoc, pullback.condition]

/-- Two compactifications of a morphism with noetherian source are both dominated by a third
compactification. -/
theorem exists_dominates_and_dominates_of_isNoetherian [IsNoetherian X]
    (c₁ c₂ : f.Compactification) :
    ∃ c : f.Compactification, c.Dominates c₁ ∧ c.Dominates c₂ :=
  have : QuasiCompact c₁.immersion := quasiCompact_of_noetherianSpace_source (X := X) _
  exists_dominates_and_dominates c₁ c₂

end Compactification

end Scheme.Hom

end AlgebraicGeometry
