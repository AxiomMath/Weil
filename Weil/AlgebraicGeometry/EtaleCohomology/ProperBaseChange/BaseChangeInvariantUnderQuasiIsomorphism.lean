module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHolds
public import Weil.Attr

/-!
# Base change is invariant under quasi-isomorphism

Let `f : X ⟶ S` and `g : T ⟶ S` be morphisms of schemes and `u : F₁ ⟶ F₂` a quasi-isomorphism of
complexes of abelian sheaves on the small étale site of `X`. Then base change holds for
`(f, g, F₁)` if and only if it holds for `(f, g, F₂)`.

Base change holding for `(f, g, F)` means that the canonical base change map
`g^*(Rf_* F) ⟶ Rf'_*(g'^* F)` is an isomorphism in the derived category of `T`. This map is a
natural transformation of functors on the derived category of `X`, and a quasi-isomorphism
becomes an isomorphism there; an isomorphism of objects transports invertibility of the
component of a natural transformation.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianBaseChangeHolds_iff_of_quasiIso` — base change holds for
  `(f, g, F₁)` if and only if it holds for `(f, g, F₂)`, for a quasi-isomorphism `F₁ ⟶ F₂`.

## Implementation notes

The source states the result for bounded below complexes, where base change is defined through
choices of injective resolutions. With base change defined by the canonical base change map in the
derived category (`Stacks.EtaleCohomology.EtaleAbelianBaseChangeHolds`, which agrees with the
formulation by resolutions for bounded below complexes by
`Stacks.EtaleCohomology.etaleAbelianBaseChangeHolds_iff_forall_injectiveResolution`), no
boundedness is needed, and the result is stated for arbitrary complexes.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6, p. 61][FreitagKiehl1988]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

universe u v

namespace Stacks.EtaleCohomology

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

/-- **Base change is invariant under quasi-isomorphism.** For a quasi-isomorphism `u : F₁ ⟶ F₂`
of complexes of abelian sheaves on the small étale site of `X`, base change holds for
`(f, g, F₁)` if and only if it holds for `(f, g, F₂)`. -/
@[weil "lem_fk106_base_change_invariant_under_quasi_isomorphism"]
theorem etaleAbelianBaseChangeHolds_iff_of_quasiIso
    {F₁ F₂ : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (u : F₁ ⟶ F₂) [QuasiIso u] :
    EtaleAbelianBaseChangeHolds.{u, v} f g F₁ ↔ EtaleAbelianBaseChangeHolds.{u, v} f g F₂ := by
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map u)) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff u).2 inferInstance
  exact NatTrans.isIso_app_iff_of_iso _ (asIso (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map u)))

end Stacks.EtaleCohomology

end
