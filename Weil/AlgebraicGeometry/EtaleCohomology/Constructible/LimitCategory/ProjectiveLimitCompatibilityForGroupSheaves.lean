module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.AffineTransitionLimit
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.AbelianLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageExact

/-!
# Constructible abelian sheaves on a projective limit come from a finite level

Let `X = lim X_α` be a projective system of schemes with limit, `n ≥ 0` an integer and `F` a
constructible abelian sheaf on the small étale site of `X` with `n F = 0`. Then there are an index
`α` and a constructible abelian sheaf `F_α` on the small étale site of `X_α` with `n F_α = 0` and
`p_α^* F_α ≅ F`, where `p_α : X ⟶ X_α` is the projection. For `n = 0` the condition `n F = 0` is
empty.

## Main results

* `IsProjectiveSystemWithLimit.exists_isConstructibleAbelianSheaf_inverseImage_iso`:
  a constructible abelian sheaf killed by `n` on the limit of a projective system of schemes with
  limit is the inverse image of a constructible abelian sheaf killed by `n` on some stage.

## Implementation notes

The schemes of the system live in a big étale site `B`, abelian sheaves are sheaves of
`AddCommGrpCat.{u + 1}` on the small étale sites `SmallEtale.topology B X`, and `n F = 0` is the
equation `n • 𝟙 F = 0` of endomorphisms. The index set is a preorder `I`, the system a functor
`Iᵒᵖ ⥤ B.Scheme`.

The source transports the group structure of `F` to a descended sheaf of sets. Here the
existence of some constructible abelian `F_α` with `p_α^* F_α ≅ F` is [Stacks, Tag 09YU],
clause (2) (`AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleAbelianSheaf_unconditional`),
and the condition `n F_α = 0` is obtained by replacing `F_α` with the cokernel of `n` on it:
that cokernel is constructible, killed by `n`, and, inverse image being additive and right exact,
its inverse image is the cokernel of `n = 0` on `F`, which is `F`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

attribute [local instance] SmallEtale.isRightAdjointPushforward_addCommGrpCat

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme)
  (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Constructible abelian sheaves killed by `n` descend to a finite level.** Let `X = lim X_α`
be a projective system of schemes with limit, `n` a natural number and `F` a constructible abelian
sheaf on the small étale site of `X` with `n F = 0`. There are an index `α` and a constructible
abelian sheaf `F_α` on the small étale site of `X_α` with `n F_α = 0` and `p_α^* F_α ≅ F`, where
`p_α : X ⟶ X_α` is the projection. -/
@[weil "lem_fk104_projective_limit_compatibility_for_group_sheaves"]
theorem IsProjectiveSystemWithLimit.exists_isConstructibleAbelianSheaf_inverseImage_iso
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c) (n : ℕ)
    (F : Sheaf (SmallEtale.topology B c.pt hX) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B (B.obj c.pt hX) F) (hn : n • 𝟙 F = 0) :
    ∃ (α : I) (Fα : Sheaf (SmallEtale.topology B (Dg.obj (op α)).obj (Dg.obj (op α)).property)
        AddCommGrpCat.{u + 1}),
      IsConstructibleAbelianSheaf B (Dg.obj (op α)) Fα ∧ n • 𝟙 Fα = 0 ∧
        Nonempty ((smallEtaleInverseImage B
          (ObjectProperty.homMk (c.π.app (op α)) : B.obj c.pt hX ⟶ Dg.obj (op α))
          AddCommGrpCat.{u + 1}).obj Fα ≅ F) := by
  have := hD.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  have : Nonempty I := IsFiltered.nonempty
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  obtain ⟨hc⟩ := hD.nonempty_isLimit
  have hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj := fun p =>
    have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p); inferInstance
  have hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj := fun p =>
    have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p); inferInstance
  obtain ⟨α, Fα, hFα, ⟨e⟩⟩ :=
    smallEtaleStagesEssSurj_isConstructibleAbelianSheaf_unconditional B Dg c hX hc
      (fun e => hD.isAffineHom_map e) hqc hqs F hF
  let P := smallEtaleInverseImage B
    (ObjectProperty.homMk (c.π.app (op α)) : B.obj c.pt hX ⟶ Dg.obj (op α))
    AddCommGrpCat.{u + 1}
  have : P.Additive := additive_smallEtaleSheafPullback_addCommGrp.{0} B _
  have : PreservesColimitsOfSize.{0, 0} P :=
    (smallEtaleInverseImageAdjunction B _ AddCommGrpCat.{u + 1}).leftAdjoint_preservesColimits
  refine ⟨α, cokernel (n • 𝟙 Fα), isConstructibleAbelianSheaf_cokernel B _ _ hFα hFα, ?_, ⟨?_⟩⟩
  · rw [← cancel_epi (cokernel.π (n • 𝟙 Fα)), comp_zero, Preadditive.comp_nsmul,
      Category.comp_id, ← Category.id_comp (cokernel.π _), ← Preadditive.nsmul_comp,
      cokernel.condition]
  · have h3 : P.map (n • 𝟙 Fα) = n • 𝟙 (P.obj Fα) := by
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    have hw : (n • 𝟙 (P.obj Fα)) ≫ e.hom = e.hom ≫ (n • 𝟙 F) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp,
        Category.comp_id]
    exact PreservesCokernel.iso P (n • 𝟙 Fα) ≪≫ cokernelIsoOfEq h3 ≪≫
      cokernel.mapIso _ _ e e hw ≪≫ cokernelIsoOfEq hn ≪≫ cokernelZeroIsoTarget

end AlgebraicGeometry

end
