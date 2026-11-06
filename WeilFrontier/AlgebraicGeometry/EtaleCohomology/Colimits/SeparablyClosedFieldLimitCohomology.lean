module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSystemCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.LocalAcyclicity.ConstantRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSmallEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtalePresentedSystem

/-!
# Étale cohomology of the finite subextensions of a separable closure

Let `κ` be a field, `K` a separable closure of `κ` and `M` an abelian group. The finite
subextensions `L` of `K / κ` form a directed set, and the schemes `Spec L` with the morphisms
`Spec L' → Spec L` (`L ⊆ L'`) form a projective system with limit `Spec K`. The constant
sections `M → H⁰(Spec L, M)` induce a bijection `M ≅ colim_L H⁰(Spec L, M)`, and
`colim_L Hᵛ(Spec L, M) = 0` for `v > 0`.

## Main definitions

* `AlgebraicGeometry.Scheme.constantSheafCohomologyMap`: the map `Hᵖ(X, M) → Hᵖ(Y, M)` induced
  by a morphism `Y ⟶ X` on the cohomology of the constant sheaf.
* `AlgebraicGeometry.Scheme.constantSectionCohomology`: the constant sections
  `M → H⁰(X, M)`.

## Main results

* `AlgebraicGeometry.isProjectiveSystemWithLimit_finiteSubextensionCone`: `Spec K` is the
  limit of the projective system `Spec L`.
* `AlgebraicGeometry.etaleCohomology_constantSheaf_colimit_finiteSubextension`: the colimit of
  `Hᵛ(Spec L, M)` over the finite subextensions is `M` for `v = 0` (through the constant
  sections) and zero for `v > 0`.

## Implementation notes

The colimit statements are elementwise. For `v = 0`: the constant sections are compatible with the
transition maps, each `M → H⁰(Spec L, M)` is injective, and every class in `H⁰(Spec L, M)` becomes
a constant section in some `H⁰(Spec L', M)`, `L ⊆ L'`; for a directed system this is the
bijectivity of `M → colim_L H⁰(Spec L, M)`. For `v > 0`: every class in `Hᵛ(Spec L, M)` vanishes
in some `Hᵛ(Spec L', M)`. The transition maps are compatible with composition.

Cohomology is `CategoryTheory.Sheaf.H` on Mathlib's small étale site
`AlgebraicGeometry.Scheme.smallEtaleTopology`, with coefficients in `AddCommGrpCat.{u + 1}` for
fields in `Type u`; the identification of the inverse image of a constant sheaf with the constant
sheaf is `Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`. The directed set of finite
subextensions and the projective system `L ↦ Spec L` with its limit cone are
`Stacks.Chow.FiniteSubextension`, `Stacks.Chow.finiteSubextensionDiagram` and
`Stacks.Chow.finiteSubextensionCone`. No finiteness of `M` is needed.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7.
-/

/- FK state the lemma for a finite abelian group `M`; no finiteness is used here (stronger than FK's
statement). Stated on Mathlib's small étale site because the colimit theorem
`AlgebraicGeometry.IsProjectiveSystemWithLimit.cohomology_colimit` is stated there. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

open Stacks.Chow

variable (κ K : Type u) [Field κ] [Field K] [Algebra κ K]

/-- For an algebraic extension `K / κ`, the schemes `Spec L` of the finite subextensions `L` of
`K / κ` form a projective system with limit `Spec K`. -/
theorem isProjectiveSystemWithLimit_finiteSubextensionCone [Algebra.IsAlgebraic κ K] :
    IsProjectiveSystemWithLimit (finiteSubextensionDiagram κ K) (finiteSubextensionCone κ K) := by
  have : IsFiltered (FiniteSubextension κ K) := isFiltered_of_directed_le_nonempty _
  have : ∀ L : (FiniteSubextension κ K)ᵒᵖ, IsNoetherian ((finiteSubextensionDiagram κ K).obj L) :=
    fun L => inferInstanceAs (IsNoetherian (Spec (.of L.unop.1)))
  have : ∀ L : (FiniteSubextension κ K)ᵒᵖ, ((finiteSubextensionDiagram κ K).obj L).IsSeparated :=
    fun L => inferInstanceAs (Spec (.of L.unop.1)).IsSeparated
  have : ∀ {L L' : (FiniteSubextension κ K)ᵒᵖ} (f : L ⟶ L'),
      IsAffineHom ((finiteSubextensionDiagram κ K).map f) := fun f =>
    inferInstanceAs (IsAffineHom (Spec.map _))
  have : IsNoetherian (finiteSubextensionCone κ K).pt :=
    inferInstanceAs (IsNoetherian (Spec (.of K)))
  have : (finiteSubextensionCone κ K).pt.IsSeparated := inferInstanceAs (Spec (.of K)).IsSeparated
  exact .of_isLimit (isLimit_finiteSubextensionCone κ K)

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- The map `Hᵖ(X, M) → Hᵖ(Y, M)` on the étale cohomology of the constant sheaf `M` induced by a
morphism `k : Y ⟶ X`: restriction along `k`, followed by the identification of the inverse image
of the constant sheaf `M` on `X` with the constant sheaf `M` on `Y`. -/
def constantSheafCohomologyMap (k : Y ⟶ X) (M : AddCommGrpCat.{u + 1}) (p : ℕ) :
    Sheaf.H.{u + 1} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) p →+
      Sheaf.H.{u + 1} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) p :=
  etaleCohomologyMapTo k ((etaleAbelianInverseImageConstantIso.{u, u + 1} k).hom.app M) p

variable (X) in
/-- The constant sections `M → H⁰(X, M)`: an element `m` of `M` gives the global section `m` of
the constant sheaf `M`, read in `H⁰(X, M) = Γ(X, M)`. -/
def constantSectionCohomology (M : AddCommGrpCat.{u + 1}) :
    M →+ Sheaf.H.{u + 1} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) 0 :=
  (Sheaf.H.equiv₀ _ (isTerminalEtaleMkId X)).symm.toAddMonoidHom.comp
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (isTerminalEtaleMkId X)).unit.app M).hom

private lemma constantSectionCohomology_eq_mk₀ (M : AddCommGrpCat.{u + 1}) (m : M) :
    constantSectionCohomology X M m =
      Abelian.Ext.mk₀ ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.ofHom (uliftZMultiplesHom M m))) := by
  apply (Sheaf.H.equiv₀ _ (isTerminalEtaleMkId X)).injective
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} (isTerminalEtaleMkId X)
  let g := AddCommGrpCat.ofHom (uliftZMultiplesHom M m)
  have h1 : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g)) =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g :=
    Abelian.Ext.addEquiv₀.apply_symm_apply _
  have h2 : adj.homEquiv _ _ ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g) =
      g ≫ adj.unit.app M := by
    rw [← Category.comp_id ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g),
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id]
  simp only [constantSectionCohomology, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
    Function.comp_apply, AddEquiv.apply_symm_apply, Sheaf.H.equiv₀, AddEquiv.trans_apply]
  rw [h1]
  change _ = AddCommGrpCat.uliftZMultiplesAddEquiv _ (adj.homEquiv _ _ _)
  rw [h2]
  simp only [AddCommGrpCat.uliftZMultiplesAddEquiv, AddEquiv.trans_apply]
  rw [eq_comm, AddEquiv.symm_apply_eq]
  ext n
  change (adj.unit.app M).hom (g.hom n) = (uliftZMultiplesHom _ ((adj.unit.app M).hom m)) n
  simp [g, uliftZMultiplesHom_apply_apply, map_zsmul]

/-- The constant sections are compatible with the maps induced by morphisms of schemes. -/
theorem constantSheafCohomologyMap_constantSectionCohomology (k : Y ⟶ X)
    (M : AddCommGrpCat.{u + 1}) (m : M) :
    constantSheafCohomologyMap k M 0 (constantSectionCohomology X M m) =
      constantSectionCohomology Y M m := by
  rw [constantSectionCohomology_eq_mk₀, constantSectionCohomology_eq_mk₀,
    constantSheafCohomologyMap, etaleCohomologyMapTo_apply, etaleCohomologyRestrictionMap_apply,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀]
  congr 1
  have := (etaleAbelianInverseImageConstantIso.{u, u + 1} k).hom.naturality
    (AddCommGrpCat.ofHom (uliftZMultiplesHom M m))
  simp only [Functor.comp_map] at this
  rw [Category.assoc]
  erw [this]
  rw [Iso.app_inv, Iso.inv_hom_id_app_assoc]

/-- The maps induced on the cohomology of a constant sheaf are compatible with composition. -/
theorem constantSheafCohomologyMap_comp (k₁ : Z ⟶ Y) (k₂ : Y ⟶ X) (k : Z ⟶ X) (hk : k = k₁ ≫ k₂)
    (M : AddCommGrpCat.{u + 1}) (p : ℕ)
    (x : Sheaf.H.{u + 1} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) p) :
    constantSheafCohomologyMap k₁ M p (constantSheafCohomologyMap k₂ M p x) =
      constantSheafCohomologyMap k M p x :=
  etaleCohomologyMapTo_comp k₁ k₂ k hk _ _ _ (by
    rw [etaleAbelianInverseImageConstantIso_comp.{u, u + 1} k₂ k₁ k hk, Iso.hom_inv_id_app_assoc])
    p x

/-- The map attached to a morphism and a map of sheaves `w` is the map attached to the morphism
and the identity, followed by the map induced by `w`. -/
private lemma etaleCohomologyMapTo_eq_map (k : Y ⟶ X)
    {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ B) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p) :
    etaleCohomologyMapTo k w p x = Sheaf.H.map w p (etaleCohomologyMapTo k (𝟙 _) p x) := by
  simp only [etaleCohomologyMapTo, AddMonoidHom.coe_comp, Function.comp_apply,
    Sheaf.H.map_id_apply]

/-- The map on cohomology induced by an isomorphism of sheaves is injective. -/
private lemma injective_H_map_of_isIso {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : A ⟶ B) [IsIso f] (p : ℕ) : Function.Injective (Sheaf.H.map.{u + 1} f p) :=
  fun a b h => by
    have := congrArg (Sheaf.H.map.{u + 1} (inv f) p) h
    rwa [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, IsIso.hom_inv_id,
      Sheaf.H.map_id_apply, Sheaf.H.map_id_apply] at this

/-- Over a separably closed field the constant sections `M → H⁰(Spec Ω, M)` are bijective. -/
theorem bijective_constantSectionCohomology_of_isSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (M : AddCommGrpCat.{u + 1}) :
    Function.Bijective (constantSectionCohomology (Spec (.of Ω)) M) := by
  have := isIso_constantSheafAdj_unit_app_of_isSepClosed Ω M
  exact (Sheaf.H.equiv₀ _ (isTerminalEtaleMkId _)).symm.bijective.comp
    (ConcreteCategory.bijective_of_isIso _)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Stacks.Chow AlgebraicGeometry.Scheme

variable {κ K : Type u} [Field κ] [Field K] [Algebra κ K]

/-- **Étale cohomology of the finite subextensions of a separable closure.** Let `κ` be a field,
`K` a separable closure of `κ` and `M` an abelian group. Over the directed set of finite
subextensions `L` of `K / κ`, with the maps `Hᵖ(Spec L, M) → Hᵖ(Spec L', M)` (`L ⊆ L'`):

* these maps form a directed system, and the constant sections `M → H⁰(Spec L, M)` are
  compatible with them;
* the constant sections induce a bijection `M ≅ colim_L H⁰(Spec L, M)`: each of them is
  injective, and every class in some `H⁰(Spec L, M)` becomes a constant section in some
  `H⁰(Spec L', M)`;
* `colim_L Hᵖ(Spec L, M) = 0` for `p > 0`: every class in some `Hᵖ(Spec L, M)` vanishes in some
  `Hᵖ(Spec L', M)`. -/
@[weil "lem_fk107_separably_closed_field_limit_cohomology"]
theorem etaleCohomology_constantSheaf_colimit_finiteSubextension [IsSepClosure κ K]
    (M : AddCommGrpCat.{u + 1}) :
    (∀ (L₁ L₂ L₃ : FiniteSubextension κ K) (h₁₂ : L₁ ≤ L₂) (h₂₃ : L₂ ≤ L₃) (p : ℕ)
        (x : Sheaf.H.{u + 1} ((constantSheaf
          ((finiteSubextensionDiagram κ K).obj (op L₁)).smallEtaleTopology
            AddCommGrpCat.{u + 1}).obj M) p),
        constantSheafCohomologyMap ((finiteSubextensionDiagram κ K).map (homOfLE h₂₃).op) M p
            (constantSheafCohomologyMap
              ((finiteSubextensionDiagram κ K).map (homOfLE h₁₂).op) M p x) =
          constantSheafCohomologyMap
            ((finiteSubextensionDiagram κ K).map (homOfLE (h₁₂.trans h₂₃)).op) M p x) ∧
    (∀ (L₁ L₂ : FiniteSubextension κ K) (h : L₁ ≤ L₂) (m : M),
        constantSheafCohomologyMap ((finiteSubextensionDiagram κ K).map (homOfLE h).op) M 0
            (constantSectionCohomology _ M m) = constantSectionCohomology _ M m) ∧
    (∀ (L : FiniteSubextension κ K) (m : M),
        constantSectionCohomology ((finiteSubextensionDiagram κ K).obj (op L)) M m = 0 → m = 0) ∧
    (∀ (L : FiniteSubextension κ K)
        (x : Sheaf.H.{u + 1} ((constantSheaf
          ((finiteSubextensionDiagram κ K).obj (op L)).smallEtaleTopology
            AddCommGrpCat.{u + 1}).obj M) 0),
        ∃ (L' : FiniteSubextension κ K) (h : L ≤ L') (m : M),
          constantSheafCohomologyMap ((finiteSubextensionDiagram κ K).map (homOfLE h).op) M 0 x =
            constantSectionCohomology _ M m) ∧
    (∀ (p : ℕ), 0 < p → ∀ (L : FiniteSubextension κ K)
        (x : Sheaf.H.{u + 1} ((constantSheaf
          ((finiteSubextensionDiagram κ K).obj (op L)).smallEtaleTopology
            AddCommGrpCat.{u + 1}).obj M) p),
        ∃ (L' : FiniteSubextension κ K) (h : L ≤ L'),
          constantSheafCohomologyMap
            ((finiteSubextensionDiagram κ K).map (homOfLE h).op) M p x = 0) := by
  have hsys := isProjectiveSystemWithLimit_finiteSubextensionCone κ K
  have : IsSepClosed K := IsSepClosure.sep_closed κ
  have : StrictlyHenselianLocalRing K := StrictlyHenselianLocalRing.of_isSepClosed K
  -- A class on `Spec L` that vanishes on `Spec K` vanishes on some `Spec L'`.
  have key : ∀ (p : ℕ) (L : FiniteSubextension κ K)
      (x : Sheaf.H.{u + 1} ((constantSheaf
        ((finiteSubextensionDiagram κ K).obj (op L)).smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj M) p),
      constantSheafCohomologyMap ((finiteSubextensionCone κ K).π.app (op L)) M p x = 0 →
      ∃ (L' : FiniteSubextension κ K) (h : L ≤ L'),
        constantSheafCohomologyMap
          ((finiteSubextensionDiagram κ K).map (homOfLE h).op) M p x = 0 := by
    intro p L x hx
    let F₀ := (constantSheaf ((finiteSubextensionDiagram κ K).obj (op L)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).obj M
    obtain ⟨-, -, h3⟩ := hsys.cohomology_colimit L F₀ p
    have h1 :
        etaleCohomologyMapTo ((finiteSubextensionCone κ K).π.app (op L)) (𝟙 _) p x = 0 := by
      rw [constantSheafCohomologyMap, etaleCohomologyMapTo_eq_map] at hx
      exact injective_H_map_of_isIso _ p (hx.trans (map_zero _).symm)
    have hx' := h3 L le_rfl
      (etaleCohomologyMapTo ((finiteSubextensionDiagram κ K).map (homOfLE (le_refl L)).op)
        (𝟙 _) p x) (by
        rw [etaleCohomologyMapTo_comp _ _ ((finiteSubextensionCone κ K).π.app (op L))
          ((finiteSubextensionCone κ K).w _).symm _ _ (𝟙 _) (by
            rw [CategoryTheory.Functor.map_id]; erw [Category.id_comp]
            exact Iso.hom_inv_id_app _ _)]
        exact h1)
    obtain ⟨L', hL', _, hz⟩ := hx'
    refine ⟨L', hL', ?_⟩
    rw [etaleCohomologyMapTo_comp _ _ ((finiteSubextensionDiagram κ K).map (homOfLE hL').op)
      (by rw [← (finiteSubextensionDiagram κ K).map_comp]; rfl) _ _ (𝟙 _) (by
        rw [CategoryTheory.Functor.map_id]; erw [Category.id_comp]
        exact Iso.hom_inv_id_app _ _)] at hz
    rw [constantSheafCohomologyMap, etaleCohomologyMapTo_eq_map, hz, map_zero]
  refine ⟨fun L₁ L₂ L₃ h₁₂ h₂₃ p x => ?_, fun L₁ L₂ h m => ?_, fun L m hm => ?_,
    fun L x => ?_, fun p hp L x => ?_⟩
  · exact constantSheafCohomologyMap_comp _ _ _
      (by rw [← (finiteSubextensionDiagram κ K).map_comp]; rfl) M p x
  · exact constantSheafCohomologyMap_constantSectionCohomology _ M m
  · have h := constantSheafCohomologyMap_constantSectionCohomology
      ((finiteSubextensionCone κ K).π.app (op L)) M m
    rw [hm, map_zero] at h
    exact (bijective_constantSectionCohomology_of_isSepClosed K M).1
      (h.symm.trans (map_zero _).symm)
  · obtain ⟨m, hm⟩ := (bijective_constantSectionCohomology_of_isSepClosed K M).2
      (constantSheafCohomologyMap ((finiteSubextensionCone κ K).π.app (op L)) M 0 x)
    obtain ⟨L', hL', hz⟩ := key 0 L (x - constantSectionCohomology _ M m) (by
      rw [map_sub, constantSheafCohomologyMap_constantSectionCohomology]
      exact sub_eq_zero.mpr hm.symm)
    refine ⟨L', hL', m, ?_⟩
    rw [map_sub, constantSheafCohomologyMap_constantSectionCohomology] at hz
    exact sub_eq_zero.mp hz
  · have : Subsingleton (Sheaf.H.{u + 1} ((constantSheaf (Spec (.of K)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj M) p) :=
      Stacks.StrictlyHenselian.subsingleton_etaleCohomology_smallEtaleTopology K _ p hp
    exact key p L x (@Subsingleton.elim _ this _ _)

end AlgebraicGeometry
