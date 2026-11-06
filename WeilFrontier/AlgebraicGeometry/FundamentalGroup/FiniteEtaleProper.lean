module

public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import Weil.Attr

/-!
# Base change of covering spaces

Let `p : Y ⟶ X` be a covering space, i.e. a finite étale morphism, and let `g : X' ⟶ X` be a
morphism of schemes. Finite morphisms and étale morphisms are both stable under base change, so
the projection `Y ×_X X' ⟶ X'` is finite étale: it is a covering space of `X'`. This covering
space is the image of `Y` under the base-change functor
`AlgebraicGeometry.finiteEtaleBaseChange g : Cov(X) ⥤ Cov(X')`.

## Main results

* `AlgebraicGeometry.Scheme.CoveringSpace.isFinite_pullback_snd`,
  `AlgebraicGeometry.Scheme.CoveringSpace.etale_pullback_snd` — the projection
  `Y ×_X X' ⟶ X'` is finite and étale.
* `AlgebraicGeometry.Scheme.CoveringSpace.finiteEtaleBaseChange_obj_hom` — the base change of
  `Y` along `g`, as a covering space of `X'`, has the projection `Y ×_X X' ⟶ X'` as its structure
  morphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.CoveringSpace

variable {X X' : Scheme.{u}}

/-- **Base change of a covering space is finite.** For a covering space `p : Y ⟶ X` and a
morphism `g : X' ⟶ X`, the projection `Y ×_X X' ⟶ X'` is finite. -/
@[weil "lem_fka1_covering_base_change"]
theorem isFinite_pullback_snd (Y : X.CoveringSpace) (g : X' ⟶ X) :
    IsFinite (pullback.snd Y.hom g) :=
  inferInstance

/-- **Base change of a covering space is étale.** For a covering space `p : Y ⟶ X` and a
morphism `g : X' ⟶ X`, the projection `Y ×_X X' ⟶ X'` is étale. -/
@[weil "lem_fka1_covering_base_change"]
theorem etale_pullback_snd (Y : X.CoveringSpace) (g : X' ⟶ X) :
    Etale (pullback.snd Y.hom g) :=
  inferInstance

/-- **Base change of covering spaces.** For a covering space `p : Y ⟶ X` and a morphism
`g : X' ⟶ X`, the covering space `(finiteEtaleBaseChange g).obj Y` of `X'` is the projection
`Y ×_X X' ⟶ X'`. -/
@[weil "lem_fka1_covering_base_change"]
theorem finiteEtaleBaseChange_obj_hom (Y : X.CoveringSpace) (g : X' ⟶ X) :
    ((finiteEtaleBaseChange g).obj Y).hom = pullback.snd Y.hom g :=
  rfl

/-- The covering space `(finiteEtaleBaseChange g).obj Y` is the covering space `mk` of the
projection `Y ×_X X' ⟶ X'`. -/
theorem finiteEtaleBaseChange_obj_eq_mk (Y : X.CoveringSpace) (g : X' ⟶ X) :
    (finiteEtaleBaseChange g).obj Y = mk (pullback.snd Y.hom g) :=
  rfl

end AlgebraicGeometry.Scheme.CoveringSpace
