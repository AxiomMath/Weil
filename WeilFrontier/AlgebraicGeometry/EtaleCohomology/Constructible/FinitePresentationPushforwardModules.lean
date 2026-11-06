module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FinitePresentationPushforwardModules

/-!
# Generic constructibility of a finite direct image

Let `f : X ⟶ Y` be a finite morphism of schemes with `Y` locally Noetherian, and `G` a
constructible sheaf of abelian groups on the small étale site of `X`. Then the direct image
`f_* G` is constructible on the small étale site of `Y`. In particular, when `Y` is nonempty
(for instance integral), there is a nonempty étale `U ⟶ Y` such that the restriction
`(f_* G)|_U` is constructible: one may take `U = Y`.

## Main results

* `AlgebraicGeometry.isConstructibleAbelianSheaf_smallPushforward_of_isFinite`: the direct image
  of a constructible abelian sheaf along a finite morphism to a locally Noetherian scheme is
  constructible.
* `exists_etale_isConstructibleAbelianSheaf_smallEtaleInverseImage_smallPushforward`: for a
  finite surjective morphism of integral schemes with Noetherian target, the restriction of
  `f_* G` to some nonempty étale `U ⟶ Y` is constructible.

## Implementation notes

[FreitagKiehl] prove the generic statement first, by a generic factorization of `f` into a purely
inseparable morphism followed by a finite disjoint union of copies of an étale `U ⟶ Y`, and then
deduce the global statement. Here the global statement is Stacks, Tag 095R, for a finite morphism
of finite presentation; over a locally Noetherian base a finite morphism is of finite
presentation, so the generic statement holds with `U = Y` and the restriction along the identity.
The integrality and surjectivity hypotheses are not needed for this argument; integrality of `Y`
is only used to make `U = Y` nonempty. The Noetherian hypothesis on `Y` is the standing
convention of [FreitagKiehl], I.2.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- **The direct image of a constructible abelian sheaf along a finite morphism.** Let
`f : X ⟶ Y` be a finite morphism to a locally Noetherian scheme and `G` a constructible abelian
sheaf on the small étale site of `X`. Then `f_* G` is constructible. -/
@[weil "lem_fk104_finite_pushforward_constructible"]
theorem isConstructibleAbelianSheaf_smallPushforward_of_isFinite
    [IsFinite (B.inclusion.map f)] [IsLocallyNoetherian Y.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : IsConstructibleAbelianSheaf B X G) :
    IsConstructibleAbelianSheaf B Y ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj G) := by
  have : IsLocallyNoetherian (B.inclusion.obj Y) := ‹IsLocallyNoetherian Y.obj›
  exact isConstructibleAbelianSheaf_pushforward_of_isFinite_of_finitePresentation B f
    ⟨inferInstance, inferInstance, inferInstance⟩ G hG

/-- **Generic constructibility of a finite direct image.** Let `f : X ⟶ Y` be a finite
surjective morphism of integral schemes, `Y` Noetherian, and `G` a constructible abelian sheaf on
the small étale site of `X`. There is a nonempty étale `e : U ⟶ Y` such that the restriction
`e^* (f_* G)` of `f_* G` to `U` is constructible. -/
@[weil "lem_fk104_finite_pushforward_constructible_generic"]
theorem exists_etale_isConstructibleAbelianSheaf_smallEtaleInverseImage_smallPushforward
    [IsFinite (B.inclusion.map f)] [Surjective (B.inclusion.map f)] [IsIntegral X.obj]
    [IsIntegral Y.obj] [IsNoetherian Y.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : IsConstructibleAbelianSheaf B X G) :
    ∃ (U : B.Scheme) (e : U ⟶ Y), Etale (B.inclusion.map e) ∧ Nonempty U.obj ∧
      IsConstructibleAbelianSheaf B U ((smallEtaleInverseImage B e AddCommGrpCat.{u + 1}).obj
        ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj G)) := by
  refine ⟨Y, 𝟙 Y, ?_, ‹IsIntegral Y.obj›.nonempty, ?_⟩
  · rw [CategoryTheory.Functor.map_id]
    infer_instance
  · exact isConstructibleAbelianSheaf_smallEtaleInverseImage B (𝟙 Y) _
      (isConstructibleAbelianSheaf_smallPushforward_of_isFinite B f G hG)

end AlgebraicGeometry

end
