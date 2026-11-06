module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality

/-!
# Direct image commutes with restriction to an étale scheme

Let `f : X ⟶ Y` be étale, `g : Z ⟶ Y` an arbitrary morphism, and `X' = X ×_Y Z`, with
projections `f' : X' ⟶ Z` (again étale) and `g' : X' ⟶ X`. For every sheaf `H` on the small
étale site of `Z` there is an isomorphism `(g_* H)|_X ≅ g'_* (H|_{X'})` of sheaves on the small
étale site of `X`, natural in `H`.

On an étale `X`-scheme `U ⟶ X` both sides take the value of `H` at the same `Z`-scheme: the
left side at `U ×_Y Z`, the right side at `U ×_X X'`, and the canonical isomorphism
`U ×_X (X ×_Y Z) ≅ U ×_Y Z` of `Z`-schemes identifies them, compatibly with restriction maps
and with morphisms of sheaves.

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.smallRestriction`: the restriction `H ↦ H|_X` of sheaves on
  the small étale site of `Y` to the small étale site of an étale `Y`-scheme `X`.
* `AlgebraicGeometry.BigEtaleSite.smallPushforwardRestrictionIso`: the natural isomorphism
  `(g_* H)|_X ≅ g'_* (H|_{X'})`.

## Implementation notes

The étale morphism `f : X ⟶ Y` is an object `X` of the small étale site of `Y`; the fibre
product `X' = X ×_Y Z` with its projection to `Z` is its base change `smallEtaleBaseChange B g`,
an object of the small étale site of `Z`, and `g'` is the first projection
`AlgebraicGeometry.baseChangedEtaleProjection`. Restriction to `X` is the direct image along
composition with `f`, `AlgebraicGeometry.smallEtalePostcompose`. The sheaves take values in an
arbitrary category.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u u₀ v₀

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u})

/-- The restriction `H ↦ H|_X` of sheaves on the small étale site of `Y` to the small étale site
of an étale `Y`-scheme `X`: `H|_X (U ⟶ X) = H (U ⟶ X ⟶ Y)`. -/
abbrev smallRestriction {Y : B.Scheme} (X : SmallEtale B Y.1 Y.property) (A : Type u₀)
    [Category.{v₀} A] :
    Sheaf (SmallEtale.topology B Y.1 Y.property) A ⥤
      Sheaf (SmallEtale.topology B X.obj.left.1 X.obj.left.property) A :=
  (smallEtalePostcompose B Y.1 Y.property X).sheafPushforwardContinuous A
    (SmallEtale.topology B X.obj.left.1 X.obj.left.property)
    (SmallEtale.topology B Y.1 Y.property)

/-- **Direct image commutes with restriction to an étale scheme.** For an étale `Y`-scheme `X`
and an arbitrary morphism `g : Z ⟶ Y`, with `X' = X ×_Y Z` (étale over `Z`) and
`g' : X' ⟶ X` the projection, `(g_* H)|_X ≅ g'_* (H|_{X'})`, naturally in the sheaf `H` on the
small étale site of `Z`. -/
@[weil "lem_fk108_etale_trivial_base_change"]
def smallPushforwardRestrictionIso {Y Z : B.Scheme} (g : Z ⟶ Y)
    (X : SmallEtale B Y.1 Y.property) (A : Type u₀) [Category.{v₀} A] :
    B.smallPushforward g A ⋙ smallRestriction B X A ≅
      smallRestriction B ((smallEtaleBaseChange B g).obj X) A ⋙
        B.smallPushforward (baseChangedEtaleProjection B g X) A :=
  (smallEtaleRestrictionPushforwardBaseChangeIso B g X A).symm

end AlgebraicGeometry.BigEtaleSite
