module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.AbelianHypercohomology
public import WeilFrontier.Defs.Topology.Sheaves.Functors
public import Weil.Attr

/-!
# Cohomology of a topological space with coefficients in a complex of abelian sheaves

Let `Z` be a topological space. The global-section functor `Γ(Z, -) : Sh(Z, Ab) ⥤ Ab`,
`F ↦ F(Z)`, is additive and `Sh(Z, Ab)` has enough injectives, so it has a right derived
functor `RΓ(Z, -) : D⁺(Z) ⥤ D⁺(Ab)` on bounded below derived categories. For a bounded below
complex `K` of abelian sheaves on `Z` the cohomology of `Z` with coefficients in `K` is
`H^v(Z, K) = H^v(RΓ(Z, K))`, and for an abelian sheaf `F` it is `H^v(Z, F) = H^v(Z, F[0])`.

Concretely, if `K ⟶ J` is a quasi-isomorphism to a bounded below complex of injective sheaves,
then `H^v(Z, K) ≅ H^v(Γ(Z, J))`; and for a choice of injective resolutions `K ↦ I(K)`
(an injective-resolution functor `ρ`) the functor `K ↦ H^v(Γ(Z, I(K)))` is isomorphic to
`H^v(Z, -)`.

## Main definitions

* `TopCat.Sheaf.globalSections`: the global-section functor `Γ(Z, -) : Sh(Z, Ab) ⥤ Ab`.
* `TopCat.Sheaf.derivedGlobalSections`: its right derived functor `RΓ(Z, -) : D⁺(Z) ⥤ D⁺(Ab)`.
* `TopCat.Sheaf.hypercohomology`: `H^v(Z, -) : D⁺(Z) ⥤ Ab`, `K ↦ H^v(RΓ(Z, K))`.
* `TopCat.Sheaf.cohomology`: `H^v(Z, -) : Sh(Z, Ab) ⥤ Ab`, `F ↦ H^v(Z, F[0])`.
* `TopCat.Sheaf.hypercohomologyIsoHomologyOfQuasiIso`: `H^v(Z, K) ≅ H^v(Γ(Z, J))` for a
  quasi-isomorphism `K ⟶ J` to a bounded below complex of injective sheaves.
* `TopCat.Sheaf.hypercohomologyIso`: for an injective-resolution functor `ρ`, the isomorphism
  between `K ↦ H^v(Γ(Z, I(K)))` and `H^v(Z, -)`.
* `TopCat.Sheaf.cohomologyIsoRightDerived`: for `n : ℕ`, `H^n(Z, -)` on sheaves is the `n`-th
  right derived functor of `Γ(Z, -)`.
* `TopCat.Sheaf.cohomologyIsoHomologyOfInjectiveResolution`: `H^n(Z, F) ≅ H^n(Γ(Z, I))` for an
  injective resolution `F ⟶ I` of a sheaf.

## Implementation notes

Abelian sheaves on `Z` are `TopCat.Sheaf AddCommGrpCat Z`, that is, abelian sheaves on the site
of open subsets of `Z`, and `Γ(Z, -)` is evaluation at the open set `⊤`. The derived functor and
the hypercohomology groups are those of a site, `Stacks.Cohomology.derivedSectionsPlus` and
`Stacks.Cohomology.hypercohomologyFunctor`, over the object `⊤`; they are formed with the
standard derived categories `HasDerivedCategory.standard`, which is therefore used in this file.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.11.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

attribute [local instance] HasDerivedCategory.standard

variable (Z : TopCat.{u})

/-- The global-section functor `Γ(Z, -) : Sh(Z, Ab) ⥤ Ab`, `F ↦ F(Z)`. -/
noncomputable abbrev globalSections : Z.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj (op ⊤)

/-- The global-section functor is additive. -/
instance globalSections_additive : (globalSections Z).Additive where
  map_add := rfl

/-- The total right derived functor `RΓ(Z, -) : D⁺(Z) ⥤ D⁺(Ab)` of the global-section
functor. -/
@[weil "def_fk111_space_cohomology"]
noncomputable abbrev derivedGlobalSections :
    DerivedCategory.Plus (Z.Sheaf AddCommGrpCat.{u}) ⥤ DerivedCategory.Plus AddCommGrpCat.{u} :=
  Stacks.Cohomology.derivedSectionsPlus (Opens.grothendieckTopology Z) ⊤

lemma derivedGlobalSections_eq :
    derivedGlobalSections Z = (globalSections Z).rightDerivedFunctorPlus :=
  rfl

/-- The cohomology `H^v(Z, K) = H^v(RΓ(Z, K))` of `Z` with coefficients in a bounded below
complex `K` of abelian sheaves, as a functor `D⁺(Z) ⥤ Ab`. -/
@[weil "def_fk111_space_cohomology"]
noncomputable abbrev hypercohomology (v : ℤ) :
    DerivedCategory.Plus (Z.Sheaf AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  Stacks.Cohomology.hypercohomologyFunctor (Opens.grothendieckTopology Z) ⊤ v

/-- `H^v(Z, -) = H^v ∘ RΓ(Z, -)`. -/
lemma hypercohomology_eq (v : ℤ) :
    hypercohomology Z v =
      derivedGlobalSections Z ⋙ DerivedCategory.Plus.homologyFunctor _ v :=
  rfl

/-- `H^v(Z, K) = H^v(RΓ(Z, K))`. -/
lemma hypercohomology_obj (v : ℤ) (K : DerivedCategory.Plus (Z.Sheaf AddCommGrpCat.{u})) :
    (hypercohomology Z v).obj K =
      (DerivedCategory.Plus.homologyFunctor _ v).obj ((derivedGlobalSections Z).obj K) :=
  rfl

/-- The cohomology `H^v(Z, F) = H^v(Z, F[0])` of `Z` with coefficients in an abelian sheaf `F`,
as a functor `Sh(Z, Ab) ⥤ Ab`. -/
@[weil "def_fk111_space_cohomology"]
noncomputable abbrev cohomology (v : ℤ) : Z.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙ hypercohomology Z v

/-- `H^v(Z, F) = H^v(Z, F[0])`. -/
lemma cohomology_obj (v : ℤ) (F : Z.Sheaf AddCommGrpCat.{u}) :
    (cohomology Z v).obj F =
      (hypercohomology Z v).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F) :=
  rfl

/-- For `n : ℕ`, the cohomology `H^n(Z, -)` of abelian sheaves is the `n`-th right derived
functor of the global-section functor. -/
noncomputable def cohomologyIsoRightDerived (n : ℕ) :
    cohomology Z n ≅ (globalSections Z).rightDerived n :=
  Stacks.Cohomology.hypercohomologySingleFunctorIso (Opens.grothendieckTopology Z) ⊤ n

variable {Z} in
/-- For an injective resolution `F ⟶ I` of an abelian sheaf and `n : ℕ`,
`H^n(Z, F) ≅ H^n(Γ(Z, I))`. -/
@[weil "def_fk111_space_cohomology"]
noncomputable def cohomologyIsoHomologyOfInjectiveResolution {F : Z.Sheaf AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (n : ℕ) :
    (cohomology Z n).obj F ≅
      (((globalSections Z).mapHomologicalComplex _).obj I.cocomplex).homology n :=
  (cohomologyIsoRightDerived Z n).app F ≪≫ I.isoRightDerivedObj (globalSections Z) n

variable {Z}

/-- If `K ⟶ J` is a quasi-isomorphism from a bounded below complex `K` of abelian sheaves to a
bounded below complex `J` of injective sheaves, then `H^v(Z, K) ≅ H^v(Γ(Z, J))`. -/
@[weil "def_fk111_space_cohomology"]
noncomputable def hypercohomologyIsoHomologyOfQuasiIso
    {K J : CochainComplex.Plus (Z.Sheaf AddCommGrpCat.{u})} (f : K ⟶ J) [QuasiIso f.hom]
    [∀ n, Injective (J.obj.X n)] (v : ℤ) :
    (hypercohomology Z v).obj (DerivedCategory.Plus.Q.obj K) ≅
      (((globalSections Z).mapHomologicalComplex _).obj J.obj).homology v :=
  have : ∀ n, Injective (((HomotopyCategory.Plus.quotient _).obj J).obj.as.X n) :=
    fun n ↦ inferInstanceAs (Injective (J.obj.X n))
  have hf : IsIso (DerivedCategory.Q.map f.hom) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let e : DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj K) ≅
      DerivedCategory.Plus.ι.obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj J)) :=
    @asIso _ _ _ _ (DerivedCategory.Q.map f.hom) hf ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app J.obj
  (hypercohomology Z v).mapIso (DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimageIso e) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ v).mapIso
      (asIso ((globalSections Z).rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient _).obj J))).symm ≪≫
    (DerivedCategory.homologyFunctorFactorsh _ v).app
      ((HomotopyCategory.quotient _ _).obj
        (((globalSections Z).mapHomologicalComplex _).obj J.obj)) ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ v).app
      (((globalSections Z).mapHomologicalComplex _).obj J.obj)

variable {c : CochainComplex.ChoiceOfInjectiveResolutions (Z.Sheaf AddCommGrpCat.{u})}
  (ρ : CochainComplex.InjectiveResolutionFunctor c)

/-- For an injective-resolution functor `ρ`, choosing injective resolutions `K ⟶ I(K)`, the
functor `K ↦ H^v(Γ(Z, I(K)))` is isomorphic to `H^v(Z, -)`. -/
@[weil "def_fk111_space_cohomology"]
noncomputable def hypercohomologyIso (v : ℤ) :
    ρ.classicalRightDerived (globalSections Z) v ≅
      DerivedCategory.PlusComplexes.toPlus _ ⋙ hypercohomology Z v :=
  ρ.classicalRightDerivedIso (globalSections Z) v

end TopCat.Sheaf
