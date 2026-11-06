module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Injectivity
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import Weil.Attr

/-!
# The direct image of an injective abelian étale sheaf is injective

Let `f : X ⟶ Y` be a morphism of schemes of a big étale site `B`. The direct image
`f_* : Sh(X_ét, Ab) ⥤ Sh(Y_ét, Ab)` carries injective objects to injective objects.

Indeed `f_*` is right adjoint to the inverse image `f^*`, which is exact; in particular `f^*`
preserves monomorphisms. For a monomorphism `G ⟶ G'` of abelian sheaves on `Y_ét` and an
injective sheaf `J` on `X_ét`, the restriction map `Hom(G', f_* J) ⟶ Hom(G, f_* J)` is identified
by adjunction with `Hom(f^* G', J) ⟶ Hom(f^* G, J)`, which is surjective because
`f^* G ⟶ f^* G'` is a monomorphism and `J` is injective.

## Main results

* `AlgebraicGeometry.BigEtaleSite.injective_smallPushforward_obj`: the direct image of an
  injective abelian sheaf on the small étale site of `X` is injective.

## Implementation notes

The coefficients are `AddCommGrpCat.{u + 1}` for the scheme universe `u`, as for the exactness
of the inverse image. The direct image is `AlgebraicGeometry.BigEtaleSite.smallPushforward`,
restriction along base change. The proof is
`AlgebraicGeometry.injective_smallEtalePushforward`, which argues on underlying presheaves
(restriction along a representably flat functor is right adjoint to an exact left Kan
extension); the argument through the exactness of `f^*` above, via
`CategoryTheory.Adjunction.map_injective` applied to
`AlgebraicGeometry.smallEtaleInverseImageAdjunction`, gives the same result.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03QB](https://stacks.math.columbia.edu/tag/03QB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- **The direct image preserves injectives.** For a morphism `f : X ⟶ Y` of a big étale site
and an injective abelian sheaf `J` on the small étale site of `X`, the direct image `f_* J` is
an injective abelian sheaf on the small étale site of `Y`. -/
@[weil "lem_fk102_direct_image_preserves_injectives"]
theorem injective_smallPushforward_obj
    (J : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) [Injective J] :
    Injective ((B.smallPushforward f AddCommGrpCat.{u + 1}).obj J) :=
  injective_smallEtalePushforward B f J

end AlgebraicGeometry.BigEtaleSite
