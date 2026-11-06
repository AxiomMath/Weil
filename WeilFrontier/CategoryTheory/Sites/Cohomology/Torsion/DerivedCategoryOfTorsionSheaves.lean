module

public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheafCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Weil.Attr

/-!
# Torsion sheaves are closed under colimits

Let `J` be a Grothendieck topology on a category `C`. A colimit of abelian sheaves on `J` is the
sheafification of the objectwise colimit presheaf. A section of the objectwise colimit of torsion
sheaves is a finite sum of images of sections of the members of the diagram, each of which is
locally killed by a positive integer, so it is locally killed by a positive integer. The map from
a presheaf to its sheafification is locally surjective, and a sheaf receiving a locally surjective
map from a presheaf whose sections are locally torsion is a torsion sheaf. Hence the colimit in
the category of abelian sheaves of any small diagram of torsion sheaves is a torsion sheaf, and
the full subcategory of torsion sheaves has all small colimits (in particular all direct sums),
computed in the category of abelian sheaves.

## Main results

* `Stacks.Torsion.isLocallyTorsion_colimit`: a colimit of locally torsion abelian presheaves is
  locally torsion.
* `Stacks.Torsion.torsionSheafProperty_isClosedUnderColimitsOfShape`: torsion sheaves are closed
  under colimits of every shape for which abelian groups have colimits.
* `AlgebraicGeometry.SmallEtale.isTorsionSheaf_colimit`: on the small étale site of a scheme, the
  colimit of a small diagram of torsion sheaves is a torsion sheaf.
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.hasColimitsOfSize` and
  `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.createsColimitsOfSize`: the category of
  torsion sheaves has all small colimits, and its inclusion into abelian sheaves creates them.

## Implementation notes

Torsion sheaves are the local notion `Stacks.Torsion.torsionSheafProperty`, and its presheaf form
is `Stacks.Torsion.IsLocallyTorsion`; with them no stalks are needed, and the argument works on
every site whose sheafification inverts exactly the locally
bijective maps (`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`), which holds for
the small étale site.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u u' v'

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A section of an abelian presheaf is locally torsion if it is killed by a positive integer on
the members of a covering sieve. -/
private def IsLocallyTorsionSection (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    {U : C} (x : P.obj (op U)) : Prop :=
  ∃ R : Sieve U, R ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), R f → ∃ n : ℕ, 0 < n ∧ n • P.map f.op x = 0

variable {P : Cᵒᵖ ⥤ AddCommGrpCat.{w}}

private lemma isLocallyTorsionSection_add {U : C} {x y : P.obj (op U)}
    (hx : IsLocallyTorsionSection J P x) (hy : IsLocallyTorsionSection J P y) :
    IsLocallyTorsionSection J P (x + y) := by
  obtain ⟨R₁, hR₁, h₁⟩ := hx
  obtain ⟨R₂, hR₂, h₂⟩ := hy
  refine ⟨R₁ ⊓ R₂, J.intersection_covering hR₁ hR₂, fun V f hf ↦ ?_⟩
  obtain ⟨n₁, hn₁, e₁⟩ := h₁ V f hf.1
  obtain ⟨n₂, hn₂, e₂⟩ := h₂ V f hf.2
  refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, ?_⟩
  simp only [map_add, smul_add, mul_smul, e₂, smul_zero, add_zero]
  rw [smul_comm, e₁, smul_zero]

/-- The subgroup of locally torsion sections of an abelian presheaf over an object. -/
private def locallyTorsionAddSubgroup (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (U : C) : AddSubgroup (P.obj (op U)) where
  carrier := {x | IsLocallyTorsionSection J P x}
  zero_mem' := ⟨⊤, J.top_mem U, fun _ _ _ ↦ ⟨1, one_pos, by simp⟩⟩
  add_mem' := isLocallyTorsionSection_add
  neg_mem' := by
    rintro x ⟨R, hR, h⟩
    refine ⟨R, hR, fun V f hf ↦ ?_⟩
    obtain ⟨n, hn, e⟩ := h V f hf
    exact ⟨n, hn, by rw [map_neg, smul_neg, e, neg_zero]⟩

/-- **Colimits of locally torsion presheaves.** The colimit of a diagram of locally torsion
abelian presheaves is locally torsion: the sections over an object of the colimit are generated
by the images of the sections of the members of the diagram, and the locally torsion sections
form a subgroup. -/
theorem isLocallyTorsion_colimit {K : Type u'} [Category.{v'} K]
    [HasColimitsOfShape K AddCommGrpCat.{w}] (D : K ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hD : ∀ k, IsLocallyTorsion J (D.obj k)) : IsLocallyTorsion J (colimit D) := by
  intro U x
  let L := locallyTorsionAddSubgroup J (colimit D) U
  have hc := isColimitOfPreserves ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U))
    (colimit.isColimit D)
  let π : (colimit D).obj (op U) ⟶ AddCommGrpCat.of ((colimit D).obj (op U) ⧸ L) :=
    AddCommGrpCat.ofHom (QuotientAddGroup.mk' L)
  have hπ : π = 0 := hc.hom_ext fun k ↦ by
    ext y
    change QuotientAddGroup.mk' L ((colimit.ι D k).app (op U) y) = 0
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    obtain ⟨R, hR, h⟩ := hD k U y
    refine ⟨R, hR, fun V f hf ↦ ?_⟩
    obtain ⟨n, hn, e⟩ := h V f hf
    refine ⟨n, hn, ?_⟩
    rw [← NatTrans.naturality_apply (colimit.ι D k) f.op y, ← map_nsmul, e, map_zero]
  have hx : QuotientAddGroup.mk' L x = 0 :=
    congrArg (fun g ↦ g x) (congrArg AddCommGrpCat.Hom.hom hπ)
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hx
  exact hx

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Torsion sheaves are closed under colimits.** The colimit in the category of abelian sheaves
of a diagram of torsion sheaves is a torsion sheaf, for every shape for which abelian groups have
colimits: it is the sheafification of the objectwise colimit presheaf, which is locally torsion,
and sheafification is locally surjective. -/
instance torsionSheafProperty_isClosedUnderColimitsOfShape (K : Type u') [Category.{v'} K]
    [HasColimitsOfShape K AddCommGrpCat.{w}] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (torsionSheafProperty J : ObjectProperty (Sheaf J AddCommGrpCat.{w})) K where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    let E := colimit.cocone (p.diag ⋙ sheafToPresheaf J AddCommGrpCat.{w})
    let e : (Sheaf.sheafifyCocone E).pt ≅ X :=
      (Sheaf.isColimitSheafifyCocone E (colimit.isColimit _)).coconePointUniqueUpToIso
        p.isColimit
    refine torsionSheafProperty_of_iso J e ?_
    exact @isLocallyTorsion_of_isLocallySurjective _ _ J _ _ (toSheafify J E.pt)
      (J.W_toSheafify E.pt).isLocallySurjective
      (isLocallyTorsion_colimit _ fun k ↦ p.prop_diag_obj k)

end Stacks.Torsion

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Torsion sheaves are closed under small colimits.** On the small étale site of a scheme,
the torsion sheaves are closed under colimits of small diagrams in the abelian sheaves. -/
@[weil "lem_fk104_torsion_sheaves_closed_under_colimits"]
instance isTorsionSheaf_isClosedUnderColimitsOfShape (K : Type u) [Category.{u} K] :
    (IsTorsionSheaf.{u} B S hS).IsClosedUnderColimitsOfShape K :=
  inferInstance

variable {B S hS} in
/-- **The colimit of torsion sheaves is a torsion sheaf.** On the small étale site of a scheme,
the colimit in the category of abelian sheaves of a small diagram of torsion sheaves is a torsion
sheaf. -/
@[weil "lem_fk104_torsion_sheaves_closed_under_colimits"]
theorem isTorsionSheaf_colimit {K : Type u} [Category.{u} K]
    (D : K ⥤ Sheaf (topology B S hS) AddCommGrpCat.{u})
    (hD : ∀ k, IsTorsionSheaf.{u} B S hS (D.obj k)) : IsTorsionSheaf.{u} B S hS (colimit D) :=
  ObjectProperty.prop_colimit _ D hD

namespace TorsionSheafCategory

/-- **The category of torsion sheaves has all small colimits.** -/
@[weil "lem_fk104_torsion_sheaves_closed_under_colimits"]
instance hasColimitsOfSize : HasColimitsOfSize.{u, u} (TorsionSheafCategory B S hS) :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- **Colimits of torsion sheaves are computed in the abelian sheaves**: the inclusion of the
torsion sheaves into the abelian sheaves creates small colimits. -/
@[weil "lem_fk104_torsion_sheaves_closed_under_colimits"]
noncomputable instance createsColimitsOfSize : CreatesColimitsOfSize.{u, u} (ι B S hS) :=
  ⟨inferInstance⟩

/-- The category of torsion sheaves has all small direct sums. -/
instance hasCoproducts : HasCoproducts.{u} (TorsionSheafCategory B S hS) :=
  fun _ ↦ HasColimitsOfSize.has_colimits_of_shape _

end TorsionSheafCategory

end AlgebraicGeometry.SmallEtale

end
