module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import Weil.Attr

/-!
# Naturality of the restriction map on étale cohomology

Let `h : Y ⟶ X` be a morphism of schemes of a big étale site and `φ : F ⟶ G` a morphism of
abelian sheaves on the small étale site of `X`. The restriction maps
`h^* : Hⁱ(X, -) ⟶ Hⁱ(Y, h^* -)` (`AlgebraicGeometry.smallEtaleCohomologyRestrictionMap`) are
natural in the sheaf: `Hⁱ(Y, h^* φ) ∘ h^* = h^* ∘ Hⁱ(X, φ)` as homomorphisms
`Hⁱ(X, F) →+ Hⁱ(Y, h^* G)`.

## Main results

* `AlgebraicGeometry.sheafHMap_comp_smallEtaleCohomologyRestrictionMap`: the naturality square,
  as an identity of group homomorphisms.

## Implementation notes

Cohomology is `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf; the map
induced by `φ` is `CategoryTheory.Sheaf.H.map`, composition with `Ext.mk₀ φ`. Since the
restriction map is the action of the exact functor `h^*` on `Ext`, naturality is the
functoriality of that action (`AlgebraicGeometry.smallEtaleCohomologyRestrictionMap_map`); the
argument through injective resolutions and restriction data is not needed in this setting.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Abelian

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (h : Y ⟶ X)
  [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]

/-- **Naturality of the restriction map in the sheaf.** For a morphism `φ : F ⟶ G` of abelian
sheaves on the small étale site of `X` and `i : ℕ`,
`Hⁱ(Y, h^* φ) ∘ h^* = h^* ∘ Hⁱ(X, φ) : Hⁱ(X, F) →+ Hⁱ(Y, h^* G)`. -/
@[weil "lem_fk106_cohomology_restriction_natural"]
theorem sheafHMap_comp_smallEtaleCohomologyRestrictionMap
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (i : ℕ) :
    (Sheaf.H.map.{w} ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map φ) i).comp
        (smallEtaleCohomologyRestrictionMap.{w} B h F i) =
      (smallEtaleCohomologyRestrictionMap.{w} B h G i).comp (Sheaf.H.map.{w} φ i) := by
  ext x
  exact (smallEtaleCohomologyRestrictionMap_map B h φ i x).symm

end AlgebraicGeometry
