module

public import Weil.Attr
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.EtaleDerivedCategories
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The inverse image on derived categories of étale sheaves

Let `F : C₁ ⥤ C₂` be an additive functor between abelian categories which preserves homology
(for instance an exact functor). Applied termwise, `F` induces a functor
`K(F) : K(C₁) ⥤ K(C₂)` on homotopy categories of cochain complexes, which sends
quasi-isomorphisms to quasi-isomorphisms. Consequently there is exactly one functor
`G : D(C₁) ⥤ D(C₂)` with `Q₁ ⋙ G = K(F) ⋙ Q₂`, an equality of functors, where `Q₁`, `Q₂` are the
localization functors from the homotopy categories; it is isomorphic to Mathlib's
`CategoryTheory.Functor.mapDerivedCategory`.

For a morphism of schemes `f : X ⟶ Y` and a ring `Λ`, the inverse image `f^*` of étale sheaves
of `Λ`-modules is additive and exact, so this applies to `F = f^*` and gives the inverse image
`f^* : D(Y, Λ) ⥤ D(X, Λ)` on derived categories of étale sheaves of `Λ`-modules.

## Main results

* `CategoryTheory.Functor.quasiIso_le_inverseImage_mapHomotopyCategory`: `K(F)` preserves
  quasi-isomorphisms.
* `CategoryTheory.Functor.existsUnique_Qh_comp_eq_mapHomotopyCategory_comp_Qh`: there is a unique
  functor `G` on derived categories with `Qh ⋙ G = K(F) ⋙ Qh`.
* `CategoryTheory.Functor.nonempty_iso_mapDerivedCategory_of_Qh_comp_eq`: any such `G` is
  isomorphic to `F.mapDerivedCategory`.
* `Stacks.EtaleCohomology.etaleModuleInverseImage_quasiIso_le_inverseImage_mapHomotopyCategory`,
  `Stacks.EtaleCohomology.existsUnique_etaleDerivedCategory_functor_Qh_comp_eq`: the case of the
  inverse image `f^*` of étale sheaves of `Λ`-modules; the functor is isomorphic to
  `(etaleModuleInverseImage Λ f).mapDerivedCategory`
  (`Stacks.EtaleCohomology.nonempty_iso_mapDerivedCategory_etaleModuleInverseImage`).

## Implementation notes

The derived category is Mathlib's `DerivedCategory` for the instance
`CategoryTheory.HasDerivedCategory.standard`, which is how `D(X, Λ)` is defined
(`Stacks.EtaleCohomology.EtaleDerivedCategory`). For this instance the derived category is the
localized category constructed from the category of complexes, and the localization functor is
strict enough that the source's equality of functors `f^* ∘ Q_Y = Q_X ∘ K(f^*)` and the
uniqueness of `f^*` hold as equalities of functors, not only up to isomorphism. The identity
`HomotopyCategory.quotient ⋙ DerivedCategory.Qh = DerivedCategory.Q` this uses holds by the
construction of `DerivedCategory.Qh` as a functor out of a quotient category.

The ring `Λ` is only assumed to be a ring; for a commutative ring the functor
`(etaleModuleInverseImage Λ f).mapDerivedCategory` is
`Stacks.EtaleCohomology.etaleModuleDerivedInverseImage Λ f`.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II][FK]
-/

/- Stated on Mathlib's small étale site (`EtaleModules`, `X.smallEtaleTopology`), the site on which
`EtaleDerivedCategory` and StacksFrontier's
`etaleModuleInverseImage` / `etaleModuleDerivedInverseImage` are defined; this library's
`AlgebraicGeometry.smallEtaleModuleSheafInverseImage` lives on
StacksFrontier's `SmallEtale` and is not used here. The strict equality
`quotient ⋙ Qh = Q` needs the body of Mathlib's `@[no_expose]` `HomologicalComplexUpToQuasiIso.Qh`,
hence the private `import all` of `Mathlib.Algebra.Homology.Localization`. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Abelian C₁] [Abelian C₂] (F : C₁ ⥤ C₂) [F.Additive] [F.PreservesHomology]

/-- An additive functor preserving homology maps quasi-isomorphisms of the homotopy category of
cochain complexes to quasi-isomorphisms. -/
theorem quasiIso_le_inverseImage_mapHomotopyCategory :
    HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ) ≤
      (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ)).inverseImage
        (F.mapHomotopyCategory (ComplexShape.up ℤ)) := by
  rintro ⟨K⟩ ⟨L⟩ f hf
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map_surjective f
  have := (HomologicalComplex.mem_quasiIso_iff _).1
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 hf)
  change HomotopyCategory.quasiIso C₂ _ ((F.mapHomotopyCategory _).map
    ((HomotopyCategory.quotient C₁ _).map g))
  rw [Functor.mapHomotopyCategory_map]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
    ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)

/-- The composite of the quotient functor to the homotopy category and the localization functor
`Qh` is the localization functor `Q` from complexes, as an equality of functors. -/
theorem _root_.DerivedCategory.quotient_comp_Qh_eq (C : Type u₁) [Category.{v₁} C] [Abelian C] :
    HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh =
      (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) := by
  unfold DerivedCategory.Qh HomologicalComplexUpToQuasiIso.Qh
  exact Quotient.lift_spec _ _ _

/-- Two functors out of the derived category which agree after composition with `Qh` are
equal. -/
theorem _root_.DerivedCategory.functor_eq_of_Qh_comp_eq {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {E : Type*} [Category* E] (G₁ G₂ : DerivedCategory C ⥤ E)
    (h : DerivedCategory.Qh ⋙ G₁ = DerivedCategory.Qh ⋙ G₂) : G₁ = G₂ := by
  apply Localization.Construction.uniq (W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  change DerivedCategory.Q ⋙ G₁ = DerivedCategory.Q ⋙ G₂
  rw [← DerivedCategory.quotient_comp_Qh_eq, Functor.assoc, Functor.assoc, h]

/-- **The functor induced on derived categories.** For an additive functor `F` preserving
homology there is a unique functor `G : D(C₁) ⥤ D(C₂)` with `Qh ⋙ G = K(F) ⋙ Qh`, an equality of
functors, where `K(F)` is `F` applied termwise on the homotopy category. -/
theorem existsUnique_Qh_comp_eq_mapHomotopyCategory_comp_Qh :
    ∃! G : DerivedCategory C₁ ⥤ DerivedCategory C₂,
      DerivedCategory.Qh ⋙ G = F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh := by
  have hinv : (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)).IsInvertedBy
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := fun K L g hg => by
    have := (HomologicalComplex.mem_quasiIso_iff _).1 hg
    exact Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso C₂ _) _
      ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)
  obtain ⟨G, hG⟩ : ∃ G : DerivedCategory C₁ ⥤ DerivedCategory C₂,
      DerivedCategory.Q ⋙ G = F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    ⟨Localization.Construction.lift _ hinv, Localization.Construction.fac _ hinv⟩
  have hfac : DerivedCategory.Qh ⋙ G =
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh := by
    apply Quotient.lift_unique'
    change HomotopyCategory.quotient C₁ _ ⋙ _ = HomotopyCategory.quotient C₁ _ ⋙ _
    rw [← Functor.assoc, DerivedCategory.quotient_comp_Qh_eq, hG, ← Functor.assoc,
      show HomotopyCategory.quotient C₁ (ComplexShape.up ℤ) ⋙ F.mapHomotopyCategory _ =
        F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient C₂ _ from Quotient.lift_spec _ _ _,
      Functor.assoc, DerivedCategory.quotient_comp_Qh_eq]
  exact ⟨G, hfac, fun G' hG' =>
    DerivedCategory.functor_eq_of_Qh_comp_eq _ _ (hG'.trans hfac.symm)⟩

omit [F.PreservesHomology] in
/-- A functor `G` on derived categories with `Qh ⋙ G = K(F) ⋙ Qh` is isomorphic to
`F.mapDerivedCategory`. -/
theorem nonempty_iso_mapDerivedCategory_of_Qh_comp_eq
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (hG : DerivedCategory.Qh ⋙ G = F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :
    Nonempty (G ≅ F.mapDerivedCategory) :=
  ⟨((whiskeringLeft _ _ _).obj DerivedCategory.Qh).preimageIso
    (eqToIso hG ≪≫ F.mapDerivedCategoryFactorsh.symm)⟩

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

universe u r

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **The termwise inverse image preserves quasi-isomorphisms.** For a morphism of schemes
`f : X ⟶ Y` and a ring `Λ`, the functor `K(f^*)` induced on homotopy categories of complexes of
étale sheaves of `Λ`-modules by the inverse image `f^*` sends quasi-isomorphisms to
quasi-isomorphisms. -/
@[weil "lem_fka2_inverse_image_derived"]
theorem etaleModuleInverseImage_quasiIso_le_inverseImage_mapHomotopyCategory :
    HomotopyCategory.quasiIso (EtaleModules.{u, r} Λ Y) (ComplexShape.up ℤ) ≤
      (HomotopyCategory.quasiIso (EtaleModules.{u, r} Λ X) (ComplexShape.up ℤ)).inverseImage
        ((etaleModuleInverseImage.{u, r} Λ f).mapHomotopyCategory (ComplexShape.up ℤ)) :=
  (etaleModuleInverseImage.{u, r} Λ f).quasiIso_le_inverseImage_mapHomotopyCategory

/-- **The inverse image on derived categories of étale sheaves.** For a morphism of schemes
`f : X ⟶ Y` and a ring `Λ`, there is a unique functor `G : D(Y, Λ) ⥤ D(X, Λ)` with
`Q_Y ⋙ G = K(f^*) ⋙ Q_X`, an equality of functors, where `Q_X`, `Q_Y` are the localization
functors from the homotopy categories and `K(f^*)` is the inverse image applied termwise. -/
@[weil "lem_fka2_inverse_image_derived"]
theorem existsUnique_etaleDerivedCategory_functor_Qh_comp_eq :
    ∃! G : EtaleDerivedCategory.{u, r} Λ Y ⥤ EtaleDerivedCategory.{u, r} Λ X,
      DerivedCategory.Qh ⋙ G =
        (etaleModuleInverseImage.{u, r} Λ f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh :=
  (etaleModuleInverseImage.{u, r} Λ f).existsUnique_Qh_comp_eq_mapHomotopyCategory_comp_Qh

/-- The functor of `existsUnique_etaleDerivedCategory_functor_Qh_comp_eq` is isomorphic to the
functor `(etaleModuleInverseImage Λ f).mapDerivedCategory` induced by the exact functor `f^*`. -/
theorem nonempty_iso_mapDerivedCategory_etaleModuleInverseImage
    (G : EtaleDerivedCategory.{u, r} Λ Y ⥤ EtaleDerivedCategory.{u, r} Λ X)
    (hG : DerivedCategory.Qh ⋙ G =
      (etaleModuleInverseImage.{u, r} Λ f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) :
    Nonempty (G ≅ (etaleModuleInverseImage.{u, r} Λ f).mapDerivedCategory) :=
  (etaleModuleInverseImage.{u, r} Λ f).nonempty_iso_mapDerivedCategory_of_Qh_comp_eq G hG

end Stacks.EtaleCohomology
