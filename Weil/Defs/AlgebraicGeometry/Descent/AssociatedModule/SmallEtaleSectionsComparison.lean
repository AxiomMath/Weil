module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSectionsComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf

/-!
# The étale presheaf of a quasi-coherent module

Let `M` be a quasi-coherent `𝒪_S`-module. Its étale presheaf `M_et` is the presheaf of abelian
groups on the étale site of `S` given by `M_et(u : U ⟶ S) = Γ(U, u^* M)`; for a morphism
`h : U ⟶ V` over `S` (so `h ≫ v = u`) the restriction `Γ(V, v^* M) ⟶ Γ(U, u^* M)` is the
pull-back of sections along `h` followed by the canonical isomorphism `h^* v^* M ≅ u^* M`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.quasicoherentPresheaf`: `M_et` on the small étale site
  `AlgebraicGeometry.SmallEtale B S hS`. It is the abelian presheaf underlying
  `AlgebraicGeometry.SmallEtale.sectionsPresheafOfModules` ([Stacks, Tag 03DS]).
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.quasicoherentPresheaf`: `M_et` on the
  étale category `Et(S)` of noetherian separated étale `S`-schemes, as an
  `AlgebraicGeometry.EtalePresheaf`; it is the restriction of the previous one.

## Main results

* `AlgebraicGeometry.SmallEtale.quasicoherentPresheaf_obj`,
  `AlgebraicGeometry.SmallEtale.quasicoherentPresheaf_map`: the sections over `u : U ⟶ S` are
  `Γ(U, u^* M)` and the restriction maps are `AlgebraicGeometry.pullbackSectionsMap`, which is
  the unit of the pull-back/push-forward adjunction followed by the canonical isomorphism
  `h^* v^* M ≅ u^* M`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.quasicoherentPresheaf_obj`,
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.quasicoherentPresheaf_map`: the same on
  `Et(S)`, in terms of the structure morphisms of its objects.
* `AlgebraicGeometry.SmallEtale.toEtaleSite_op_comp_smallEtaleAssociatedSheaf`: on the small
  étale site, `M_et` is the restriction of `AlgebraicGeometry.smallEtaleAssociatedSheaf`, the
  same presheaf on Mathlib's `AlgebraicGeometry.Scheme.Etale`.

## Implementation notes

No new object is constructed: both definitions are abbreviations for the pull-back-sections
presheaf of [Stacks, Tag 03DS] read on the relevant site. The sheaf property of `M_et`
([Stacks, Tag 03DT]) is `AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules`.
The module structure over the structure sheaf of the site is
`AlgebraicGeometry.SmallEtale.sectionsPresheafOfModules`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : S.Modules) [F.IsQuasicoherent]

namespace SmallEtale

/-- **The étale presheaf `M_et` of a quasi-coherent module `M`**, on the small étale site of
`S`: the presheaf of abelian groups `(u : U ⟶ S) ↦ Γ(U, u^* M)`, with restriction given by
pulling sections back. It is the abelian presheaf underlying
`AlgebraicGeometry.SmallEtale.sectionsPresheafOfModules`. -/
@[weil "def_fk102_etale_sheaf_of_quasicoherent"]
abbrev quasicoherentPresheaf : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (sectionsPresheafOfModules B S hS F).presheaf

/-- The sections of `M_et` over `u : U ⟶ S` are `Γ(U, u^* M)`. -/
@[weil "def_fk102_etale_sheaf_of_quasicoherent"]
lemma quasicoherentPresheaf_obj (U : SmallEtale B S hS) :
    (quasicoherentPresheaf B S hS F).obj (op U) =
      AddCommGrpCat.of Γ((Scheme.Modules.pullback ((toOver B S hS).obj U).hom).obj F, ⊤) :=
  rfl

/-- The restriction of `M_et` along `h : U ⟶ V` is the pull-back of sections along `h`
followed by the canonical isomorphism `h^* v^* M ≅ u^* M`. -/
@[weil "def_fk102_etale_sheaf_of_quasicoherent"]
lemma quasicoherentPresheaf_map {U V : SmallEtale B S hS} (h : U ⟶ V) :
    (quasicoherentPresheaf B S hS F).map h.op = pullbackSectionsMap F ((toOver B S hS).map h) :=
  rfl

/-- `M_et` on the small étale site is the restriction of
`AlgebraicGeometry.smallEtaleAssociatedSheaf`, the same presheaf on Mathlib's étale site
`AlgebraicGeometry.Scheme.Etale`. -/
lemma toEtaleSite_op_comp_smallEtaleAssociatedSheaf :
    (toEtaleSite B S hS).op ⋙ (smallEtaleAssociatedSheaf S F).obj =
      quasicoherentPresheaf B S hS F :=
  rfl

/-- `M_et` is a sheaf on the small étale site ([Stacks, Tag 03DT]). -/
@[weil "prop_fk102_quasicoherent_etale_is_sheaf"]
lemma isSheaf_quasicoherentPresheaf :
    Presheaf.IsSheaf (topology B S hS) (quasicoherentPresheaf B S hS F) :=
  isSheaf_sectionsPresheafOfModules B S hS F

end SmallEtale

namespace SmallNoetherianSeparatedEtale

/-- **The étale presheaf `M_et` of a quasi-coherent module `M`**, on the étale category `Et(S)`
of noetherian separated étale `S`-schemes: `(u : U ⟶ S) ↦ Γ(U, u^* M)`, the restriction of
`AlgebraicGeometry.SmallEtale.quasicoherentPresheaf`. -/
@[weil "def_fk102_etale_sheaf_of_quasicoherent"]
abbrev quasicoherentPresheaf : EtalePresheaf B S hS AddCommGrpCat.{u} :=
  (inclusion B S hS).op ⋙ SmallEtale.quasicoherentPresheaf B S hS F

/-- The sections of `M_et` over an object `u : U ⟶ S` of `Et(S)` are `Γ(U, u^* M)`. -/
@[weil "def_fk102_etale_sheaf_of_quasicoherent"]
lemma quasicoherentPresheaf_obj (U : SmallNoetherianSeparatedEtale B S hS) :
    (quasicoherentPresheaf B S hS F).obj (op U) =
      AddCommGrpCat.of Γ((Scheme.Modules.pullback (structureMorphism U)).obj F, ⊤) :=
  rfl

/-- The restriction of `M_et` along a morphism `h : U ⟶ V` of `Et(S)` is the pull-back of
sections along `h` followed by the canonical isomorphism `h^* v^* M ≅ u^* M`. -/
@[weil "def_fk102_etale_sheaf_of_quasicoherent"]
lemma quasicoherentPresheaf_map {U V : SmallNoetherianSeparatedEtale B S hS} (h : U ⟶ V) :
    (quasicoherentPresheaf B S hS F).map h.op =
      pullbackSectionsMap F (Over.homMk (U := Over.mk (structureMorphism U))
        (V := Over.mk (structureMorphism V)) ((toScheme B S hS).map h)
        (toScheme_map_comp_structureMorphism h)) :=
  rfl

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
