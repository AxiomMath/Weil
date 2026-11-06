module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import Weil.Attr

/-!
# Restriction on étale cohomology commutes with connecting maps

Let `h : Y ⟶ X` be a morphism of schemes of a big étale site and
`0 → F₁ → F₂ → F₃ → 0` a short exact sequence of abelian sheaves on the small étale site of `X`.
The inverse image `h^*` is exact, so `0 → h^* F₁ → h^* F₂ → h^* F₃ → 0` is again short exact,
and both sequences have connecting maps `δ : Hⁱ(X, F₃) → Hⁱ⁺¹(X, F₁)` and
`δ_Y : Hⁱ(Y, h^* F₃) → Hⁱ⁺¹(Y, h^* F₁)` (postcomposition with the extension class of the
sequence). The restriction maps `AlgebraicGeometry.smallEtaleCohomologyRestrictionMap` satisfy
`h^* ∘ δ = δ_Y ∘ h^*` in every degree.

## Main results

* `AlgebraicGeometry.smallEtaleCohomologyRestrictionMap_comp_postcomp_extClass`: the identity
  `h^* ∘ δ = δ_Y ∘ h^*` of group homomorphisms `Hⁱ(X, F₃) →+ Hʲ(Y, h^* F₁)`, `i + 1 = j`.

## Implementation notes

Cohomology is `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf, and the
connecting map of the long exact sequence is postcomposition with
`CategoryTheory.ShortComplex.ShortExact.extClass`. With the restriction map defined as the
action of the exact inverse image on `Ext`, the identity follows from the compatibility of an
exact functor with extension classes and the associativity of the `Ext` composition, instead of
the comparison of horseshoe resolutions through restriction data used in the source.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian

universe w u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (h : Y ⟶ X)
  [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]

/-- **Restriction commutes with connecting maps.** For a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of abelian sheaves on the small étale site of `X` and `i + 1 = j`, the
restriction maps `h^*` intertwine the connecting map `Hⁱ(X, F₃) → Hʲ(X, F₁)` with the connecting
map `Hⁱ(Y, h^* F₃) → Hʲ(Y, h^* F₁)` of the inverse-image sequence: `h^* ∘ δ = δ_Y ∘ h^*`. -/
@[weil "lem_fk106_cohomology_restriction_connecting"]
theorem smallEtaleCohomologyRestrictionMap_comp_postcomp_extClass
    {S : ShortComplex (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j) :
    (smallEtaleCohomologyRestrictionMap B h S.X₁ j).comp (hS.extClass.postcomp _ hij) =
      ((hS.map_of_exact (smallEtaleInverseImage B h AddCommGrpCat.{u + 1})).extClass.postcomp
        _ hij).comp (smallEtaleCohomologyRestrictionMap B h S.X₃ i) := by
  ext x
  exact smallEtaleCohomologyRestrictionMap_comp_extClass B h hS i j hij x

end AlgebraicGeometry
