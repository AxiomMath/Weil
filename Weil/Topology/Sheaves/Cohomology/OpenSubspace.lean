module

public import Weil.Topology.Sheaves.Cohomology.FiniteAcyclicCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Cohomology of a constant sheaf over an open subspace

Let `X` be a topological space, `U ⊆ X` an open subset and `A` an abelian group. The cohomology
`Hⁿ(U, A_X)` of the constant sheaf `A_X` over the open `U` (Mathlib's `Sheaf.H'`, an `Ext` group
out of the free abelian sheaf on `U`) vanishes exactly when the sheaf cohomology `Hⁿ(U, A_U)` of
the constant sheaf on the topological space `U` vanishes.

The proof composes three identifications:
* cohomology over `U` is the cohomology of the restriction to the slice site `Over U`;
* the restriction of a constant sheaf to the slice is the constant sheaf of the slice;
* sheaves on `Over U` and on the space `U` are equivalent (`Opens.sheafEquivOver`), the
  equivalence preserves `Ext` groups and takes constant sheaves to constant sheaves.

## Main definitions

* `TopCat.SheafCohomology.constantSheafOverEquivIso`: the equivalence
  `Opens.sheafEquivOver` takes the constant sheaf of the slice over `U` to the constant sheaf
  of the space `U`.

## Main results

* `TopCat.SheafCohomology.subsingleton_H'_constantSheaf_iff`: `Hⁿ(U, A_X) = 0` iff
  `Hⁿ(U, A_U) = 0`.
* `TopCat.SheafCohomology.subsingleton_ext_congr`: vanishing of `Ext` is invariant under
  isomorphisms of both arguments.

## Implementation notes

The `Ext` groups on `X` are taken in an arbitrary universe `w'`; the comparison with the slice
is made in universe `u` and the universe is changed with `Abelian.Ext.chgUniv`.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite Abelian

universe w' u

namespace TopCat.SheafCohomology

variable {X : TopCat.{u}} (U : Opens X)

/-- The terminal object of the slice `Over U` corresponding to `⊤ : Opens U`. -/
def overTopIsTerminal : IsTerminal (U.overEquivalence.inverse.obj ⊤) :=
  Stacks.Cohomology.TerminalCohomology.topIsTerminal.isTerminalObj U.overEquivalence.inverse ⊤

/-- The equivalence between sheaves on the slice over `U` and sheaves on the subspace `U`
commutes with global sections. -/
def sheafEquivOverSectionsIso :
    U.sheafEquivOver.functor ⋙ (sheafSections (Opens.grothendieckTopology U)
        AddCommGrpCat.{u}).obj (op ⊤) ≅
      (sheafSections ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}).obj
        (op (U.overEquivalence.inverse.obj ⊤)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The equivalence between sheaves on the slice over `U` and sheaves on the subspace `U`
takes constant sheaves to constant sheaves. -/
def constantSheafOverEquivIso :
    constantSheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} ⋙
        U.sheafEquivOver.functor ≅
      constantSheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u} := by
  let adj₁ := (constantSheafAdj (Opens.grothendieckTopology U) AddCommGrpCat.{u}
    Stacks.Cohomology.TerminalCohomology.topIsTerminal).comp U.sheafEquivOver.symm.toAdjunction
  let adj₂ := adj₁.ofNatIsoRight (sheafEquivOverSectionsIso U)
  exact (Functor.isoWhiskerRight
      (adj₂.leftAdjointUniq (constantSheafAdj _ AddCommGrpCat.{u} (overTopIsTerminal U))).symm
      U.sheafEquivOver.functor) ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ U.sheafEquivOver.counitIso ≪≫ Functor.rightUnitor _


/-- `Ext` groups between isomorphic objects are in bijection, so one vanishes iff the other
does. -/
theorem subsingleton_ext_congr {C : Type*} [Category* C] [Abelian C] [HasExt.{w'} C]
    {Y₁ Y₂ Z₁ Z₂ : C} (i : Y₁ ≅ Y₂) (j : Z₁ ≅ Z₂) (n : ℕ) :
    Subsingleton (Ext.{w'} Y₁ Z₁ n) ↔ Subsingleton (Ext.{w'} Y₂ Z₂ n) := by
  have key : ∀ {Y₁ Y₂ Z₁ Z₂ : C} (i : Y₁ ≅ Y₂) (j : Z₁ ≅ Z₂),
      Subsingleton (Ext.{w'} Y₁ Z₁ n) → Subsingleton (Ext.{w'} Y₂ Z₂ n) := by
    intro Y₁ Y₂ Z₁ Z₂ i j h
    let φ : Ext.{w'} Y₂ Z₂ n → Ext.{w'} Y₁ Z₁ n := fun c ↦
      ((Ext.mk₀ i.hom).comp c (zero_add n)).comp (Ext.mk₀ j.inv) (add_zero n)
    refine Function.Injective.subsingleton (f := φ) (fun c d hcd ↦ ?_)
    have hφ : ∀ c, ((Ext.mk₀ i.inv).comp (φ c) (zero_add n)).comp (Ext.mk₀ j.hom)
        (add_zero n) = c := by
      intro c
      simp only [φ, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id,
        Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp]
    rw [← hφ c, ← hφ d, hcd]
  exact ⟨key i j, key i.symm j.symm⟩


/-- The cohomology of the constant sheaf `A` on `X` over an open `U` vanishes in degree `n`
exactly when the cohomology of the constant sheaf `A` on the subspace `U` does. -/
theorem subsingleton_H'_constantSheaf_iff (A : AddCommGrpCat.{u})
    [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasExt.{w'} (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of U))
      AddCommGrpCat.{u})] (n : ℕ) :
    Subsingleton ((((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        A).cohomologyPresheaf n).obj (op U)) ↔
      Subsingleton (Sheaf.H.{w'} ((constantSheaf (Opens.grothendieckTopology (TopCat.of U))
        AddCommGrpCat.{u}).obj A) n) := by
  let J := Opens.grothendieckTopology X
  let F := (constantSheaf J AddCommGrpCat.{u}).obj A
  have : HasExt.{u} (CategoryTheory.Sheaf J AddCommGrpCat.{u}) := inferInstance
  have : HasExt.{u} (CategoryTheory.Sheaf (J.over U) AddCommGrpCat.{u}) := inferInstance
  have := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{u, u, u} J U
  have := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u, u, u} J U
  -- change of universe of the `Ext` groups on `X`
  have e₁ := Ext.chgUniv.{u, w'}
    (X := (presheafToSheaf J AddCommGrpCat.{u}).obj
      ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).obj U)) (Y := F) (n := n)
  -- cohomology over `U` is cohomology of the restriction to the slice
  have e₂ := Stacks.Cohomology.OverObjectCohomology.h'AddEquivHOverSheafPullback.{u} J U F n
  -- the restriction of a constant sheaf is constant
  have i₁ := (Stacks.ConstantSheaf.overPullbackConstantSheafIso J AddCommGrpCat.{u} U).app A
  -- the slice and the subspace have equivalent sheaf categories
  let E := U.sheafEquivOver (A := AddCommGrpCat.{u})
  have := Functor.additive_of_preserves_binary_products E.functor
  have i₂ := (constantSheafOverEquivIso U).app (AddCommGrpCat.of (ULift ℤ))
  have i₃ := (constantSheafOverEquivIso U).app A
  calc _ ↔ Subsingleton (Ext.{u} ((presheafToSheaf J AddCommGrpCat.{u}).obj
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).obj U)) F n) :=
        e₁.subsingleton_congr
    _ ↔ Subsingleton (Sheaf.H.{u} (F.over U) n) := e₂.toEquiv.subsingleton_congr
    _ ↔ Subsingleton (Ext.{u}
          ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)))
          ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj A) n) :=
        subsingleton_ext_congr (Iso.refl _) i₁.symm n
    _ ↔ Subsingleton (Ext.{w'}
          (E.functor.obj ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift ℤ))))
          (E.functor.obj ((constantSheaf (J.over U) AddCommGrpCat.{u}).obj A)) n) :=
        (Equiv.ofBijective _
          (E.functor.mapExt_bijective_of_preservesInjectiveObjects _ _ n)).subsingleton_congr
    _ ↔ _ := subsingleton_ext_congr i₂ i₃ n

end TopCat.SheafCohomology
