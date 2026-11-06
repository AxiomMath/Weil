module

public import Weil.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ClosedFibreCohomologyRestriction
public import Weil.Attr

/-!
# Restriction of global sections of `ℤ/n`-sheaves to the closed fibre

Let `A` be a henselian local ring, `f : X ⟶ Spec A` a proper morphism and `j : X₀ ⟶ X` the
inclusion of the closed fibre. For every sheaf `M` of `ℤ/n`-modules on the small étale site of
`X`, restriction `j^* : H⁰(X, M) ⟶ H⁰(X₀, j^* M)` of its underlying abelian sheaf is bijective.
This is the case of the underlying abelian sheaf of `M` in
`AlgebraicGeometry.bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero`.

## Main results

* `AlgebraicGeometry.bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero_moduleCat_zmod`

## Implementation notes

The hypotheses are weaker than in the source: `A` henselian rather than noetherian and strictly
henselian, `f` proper rather than projective, no bound on the dimension of the closed fibre and
no condition on `n`. The source's reduction to constructible sheaves is not needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Stacks.EtaleCohomology

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (A : Type u) [CommRing A] [HenselianLocalRing A] (X : B.Scheme)
  (f : X.obj ⟶ Spec (.of A)) (hZ : B.Contains (closedFibre A f))

/-- **Restriction of global sections of a `ℤ/n`-sheaf to the closed fibre is bijective.** Let `A`
be a henselian local ring, `f : X ⟶ Spec A` proper and `j : X₀ ⟶ X` the inclusion of the closed
fibre. For every sheaf `M` of `ℤ/n`-modules on the small étale site of `X`, the restriction map
`H⁰(X, M) ⟶ H⁰(X₀, j^* M)` of its underlying abelian sheaf is bijective. -/
@[weil "lem_fk106_h0_restriction_bijective"]
theorem bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero_moduleCat_zmod
    [IsProper f]
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (closedFibre A f) hZ) AddCommGrpCat.{u + 1})]
    (n : ℕ) (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ZMod n))) :
    Function.Bijective (smallEtaleCohomologyRestrictionMap B (closedFibreHom B A X f hZ)
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M) 0) :=
  bijective_smallEtaleCohomologyRestrictionMap_closedFibre_zero B A X f hZ _

end AlgebraicGeometry
