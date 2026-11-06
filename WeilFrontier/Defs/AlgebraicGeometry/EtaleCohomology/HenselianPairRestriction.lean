module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.InverseImage
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageAbelian
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PowerOfPair
public import Weil.Attr

/-!
# The restriction map on étale cohomology

Let `h : Y ⟶ X` be a morphism of schemes of a big étale site and `F` an abelian sheaf on the
small étale site of `X`. The restriction map `h^* : Hⁱ(X, F) ⟶ Hⁱ(Y, h^* F)` is defined here on
the cohomology `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf `ℤ`: an
`Ext`-class `ℤ_X ⟶ F[i]` is sent by the exact inverse-image functor `h^*` to a class
`h^* ℤ_X ⟶ (h^* F)[i]`, which is precomposed with the canonical isomorphism `ℤ_Y ≅ h^* ℤ_X`
(`AlgebraicGeometry.smallEtaleInverseImageConstantSheafIso`).

When cohomology is computed by injective resolutions, the same map is the map induced on
cohomology by `Γ(X, I•) ⟶ Γ(Y, h^* I•) ⟶ Γ(Y, J•)` for a restriction datum `(I•, J•, ρ)`
(`CategoryTheory.InjectiveResolution.restrictionHomologyMap` with the restriction of global
sections `AlgebraicGeometry.smallEtaleRestrictionOnGlobalSectionsNatTrans`); that map does not
depend on the datum (`AlgebraicGeometry.smallEtaleRestrictionHomologyMap_comp_homologyIso_hom`).

## Main definitions

* `AlgebraicGeometry.smallEtaleCohomologyRestrictionMap`: the restriction map
  `Hⁱ(X, F) →+ Hⁱ(Y, h^* F)`.

## Main results

* `AlgebraicGeometry.smallEtaleCohomologyRestrictionMap_apply`: the defining formula.
* `AlgebraicGeometry.smallEtaleCohomologyRestrictionMap_comp_mk₀`,
  `AlgebraicGeometry.smallEtaleCohomologyRestrictionMap_map`: naturality in the sheaf.
* `AlgebraicGeometry.smallEtaleCohomologyRestrictionMap_comp_extClass`: compatibility with the
  connecting maps of a short exact sequence.

## Implementation notes

The definition is the form, on the small étale sites `AlgebraicGeometry.SmallEtale` of a big
étale site, of `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` (stated there on the small
étale sites `X.smallEtaleTopology`): the same formula, with the inverse image
`AlgebraicGeometry.smallEtaleInverseImage` and its constant-sheaf comparison. Coefficients are
abelian groups in the universe `u + 1`, where the inverse image is defined and exact.

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

/-- **The restriction map on étale cohomology.** For a morphism `h : Y ⟶ X` of schemes of a big
étale site and an abelian sheaf `F` on the small étale site of `X`, the map
`Hⁱ(X, F) →+ Hⁱ(Y, h^* F)`: the exact inverse image `h^*` applied to an `Ext`-class out of the
constant sheaf `ℤ_X`, precomposed with the isomorphism `ℤ_Y ≅ h^* ℤ_X`. -/
@[weil "def_fk106_cohomology_restriction_map"]
def smallEtaleCohomologyRestrictionMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) (i : ℕ) :
    Sheaf.H.{w} F i →+ Sheaf.H.{w} ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj F) i :=
  ((Ext.mk₀ (smallEtaleInverseImageConstantSheafIso B h AddCommGrpCat.{u + 1}
      (AddCommGrpCat.of (ULift ℤ))).inv).precomp
        ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).obj F) (Nat.zero_add i)).comp
    ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).mapExtAddHom
      ((constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) F i)

/-- The restriction map is the action of the exact inverse image on `Ext`, precomposed with the
constant-sheaf comparison. -/
theorem smallEtaleCohomologyRestrictionMap_apply
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) (i : ℕ)
    (x : Sheaf.H.{w} F i) :
    smallEtaleCohomologyRestrictionMap B h F i x =
      (Ext.mk₀ (smallEtaleInverseImageConstantSheafIso B h AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift ℤ))).inv).comp
          (x.mapExactFunctor (smallEtaleInverseImage B h AddCommGrpCat.{u + 1}))
          (Nat.zero_add i) := rfl

/-- **Naturality of restriction.** Restricting the image of a class under a morphism of sheaves
`φ : F ⟶ G` gives the image of its restriction under `h^* φ`. -/
theorem smallEtaleCohomologyRestrictionMap_comp_mk₀
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (i : ℕ) (x : Sheaf.H.{w} F i) :
    smallEtaleCohomologyRestrictionMap B h G i (x.comp (Ext.mk₀ φ) (add_zero i)) =
      (smallEtaleCohomologyRestrictionMap B h F i x).comp
        (Ext.mk₀ ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map φ)) (add_zero i) := by
  rw [smallEtaleCohomologyRestrictionMap_apply, smallEtaleCohomologyRestrictionMap_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add i)]

/-- **Naturality of restriction**, with the map on cohomology `CategoryTheory.Sheaf.H.map`:
`Hⁱ(Y, h^* φ) ∘ h^* = h^* ∘ Hⁱ(X, φ)`. -/
theorem smallEtaleCohomologyRestrictionMap_map
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (i : ℕ) (x : Sheaf.H.{w} F i) :
    smallEtaleCohomologyRestrictionMap B h G i (Sheaf.H.map φ i x) =
      Sheaf.H.map ((smallEtaleInverseImage B h AddCommGrpCat.{u + 1}).map φ) i
        (smallEtaleCohomologyRestrictionMap B h F i x) := by
  simpa only [Sheaf.H.map_apply] using smallEtaleCohomologyRestrictionMap_comp_mk₀ B h φ i x

/-- **Restriction commutes with connecting maps.** For a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of abelian sheaves on the small étale site of `X`, restricting the image
of a class under the connecting map `Hⁱ(X, F₃) ⟶ Hʲ(X, F₁)` (`i + 1 = j`) gives the image of its
restriction under the connecting map of the inverse-image sequence. -/
theorem smallEtaleCohomologyRestrictionMap_comp_extClass
    {S : ShortComplex (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (i j : ℕ) (hij : i + 1 = j) (x : Sheaf.H.{w} S.X₃ i) :
    smallEtaleCohomologyRestrictionMap B h S.X₁ j (x.comp hS.extClass hij) =
      (smallEtaleCohomologyRestrictionMap B h S.X₃ i x).comp
        (hS.map_of_exact (smallEtaleInverseImage B h AddCommGrpCat.{u + 1})).extClass hij := by
  rw [smallEtaleCohomologyRestrictionMap_apply, smallEtaleCohomologyRestrictionMap_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    ← Ext.comp_assoc _ _ _ (zero_add i) hij (by omega)]

end AlgebraicGeometry
