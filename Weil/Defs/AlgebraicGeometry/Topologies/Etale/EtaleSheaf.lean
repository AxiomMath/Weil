module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import Weil.CategoryTheory.Sites.IsSheafFor

/-!
# Étale sheaves on `Et(S)`

Let `S` be a scheme and `Et(S)` the category of étale `S`-schemes which are noetherian and
separated. A presheaf `F` of sets or of abelian groups on `Et(S)` is an *étale sheaf* if
* a) for every object `W` and every finite family `(iₖ : Uₖ ⟶ W)ₖ` of open immersions with
  pairwise disjoint images covering `W`, the map `F(W) → ∏ₖ F(Uₖ)` is bijective, and
* b) for every surjective morphism `φ : U ⟶ V` the map `φ^* : F(V) → F(U)` is injective, with
  image the sections `s` such that `a^* s = b^* s` whenever `φ ∘ a = φ ∘ b`.

Sheaves form a full subcategory of the category of presheaves.

We take the category of étale sheaves to be the category of sheaves for the Grothendieck
topology `AlgebraicGeometry.SmallNoetherianSeparatedEtale.topology` on `Et(S)` (restricted from
the small étale site), and identify its objects with the presheaves satisfying a) and b).

## Main definitions

* `AlgebraicGeometry.EtaleSheaf B S hS A`: the category `Sh(Et(S), A)` of étale sheaves on
  `Et(S)` with values in `A`.
* `AlgebraicGeometry.Scheme.EtaleSheaf X A`: the same for a bare scheme `X`.
* `AlgebraicGeometry.EtaleSheaf.fullyFaithfulToEtalePresheaf`: `Sh(Et(S), A)` is a full
  subcategory of the category of presheaves on `Et(S)`.
* `AlgebraicGeometry.EtaleSheaf.ofIsEtaleSheaf`,
  `AlgebraicGeometry.EtaleSheaf.ofIsEtaleSheafForget`:
  the étale sheaf of sets (resp. abelian groups) defined by a presheaf satisfying a) and b).

## Main results

* `AlgebraicGeometry.EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf`: for `S` locally
  noetherian, a presheaf of sets on `Et(S)` is a sheaf for the topology if and only if it
  satisfies a) and b) (`AlgebraicGeometry.EtalePresheaf.IsEtaleSheaf`).
* `AlgebraicGeometry.EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf_forget`: the same for
  presheaves of abelian groups, whose conditions a) and b) are those of the underlying presheaf
  of sets.

## Implementation notes

For the empty family in a), the condition says that `F(∅)` is a point; this is the sheaf
condition for the empty covering of the empty scheme. The comparison with the small étale site
`AlgebraicGeometry.SmallEtale` and with Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`
is `AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv` and
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquivEtale`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Étale sheaves on `Et(S)`.** The category `Sh(Et(S), A)` of sheaves with values in `A`
on the étale category `Et(S)`, for the topology restricted from the small étale site. For
`A` the category of sets or of abelian groups, its objects are the presheaves satisfying FK's
conditions a) and b) (`AlgebraicGeometry.EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf`,
`AlgebraicGeometry.EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf_forget`). -/
@[weil "def_fk102_etale_sheaf"]
abbrev EtaleSheaf (A : Type v) [Category.{w} A] :=
  Sheaf (SmallNoetherianSeparatedEtale.topology B S hS) A

/-- Étale sheaves with values in `A` on the étale category `Et(X)` of a bare scheme `X`. -/
@[weil "def_fk102_etale_sheaf"]
abbrev Scheme.EtaleSheaf (X : Scheme.{u}) (A : Type v) [Category.{w} A] :=
  AlgebraicGeometry.EtaleSheaf (BigEtaleSite.containing X) X
    (BigEtaleSite.contains_containing X) A

namespace EtaleSheaf

/-- **Étale sheaves form a full subcategory of presheaves.** The forgetful functor from étale
sheaves to presheaves on `Et(S)` is fully faithful. -/
@[weil "def_fk102_etale_sheaf"]
def fullyFaithfulToEtalePresheaf (A : Type v) [Category.{w} A] :
    (sheafToPresheaf (SmallNoetherianSeparatedEtale.topology B S hS) A).FullyFaithful :=
  fullyFaithfulSheafToPresheaf _ _

end EtaleSheaf

namespace EtalePresheaf

variable {B S hS} [IsLocallyNoetherian S]

/-- **Étale sheaves of sets** (FK I.2.4). For `S` locally noetherian, a presheaf of sets on
`Et(S)` is a sheaf for the étale topology if and only if it satisfies FK's conditions a)
(finite disjoint unions) and b) (descent along surjective morphisms). -/
@[weil "def_fk102_etale_sheaf"]
theorem isSheaf_topology_iff_isEtaleSheaf (F : EtalePresheaf B S hS (Type v)) :
    Presheaf.IsSheaf (SmallNoetherianSeparatedEtale.topology B S hS) F ↔ IsEtaleSheaf F := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact SmallNoetherianSeparatedEtale.isSheaf_iff_isEtaleSheaf B S hS F

/-- **Étale sheaves of abelian groups** (FK I.2.4). For `S` locally noetherian, a presheaf of
abelian groups on `Et(S)` is a sheaf for the étale topology if and only if its underlying
presheaf of sets satisfies FK's conditions a) and b). -/
@[weil "def_fk102_etale_sheaf"]
theorem isSheaf_topology_iff_isEtaleSheaf_forget (F : EtalePresheaf B S hS AddCommGrpCat.{v}) :
    Presheaf.IsSheaf (SmallNoetherianSeparatedEtale.topology B S hS) F ↔
      IsEtaleSheaf (F ⋙ forget AddCommGrpCat) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget_addCommGrpCat]
  exact SmallNoetherianSeparatedEtale.isSheaf_iff_isEtaleSheaf B S hS _

end EtalePresheaf

namespace EtaleSheaf

variable {B S hS} [IsLocallyNoetherian S]

/-- The étale sheaf of sets defined by a presheaf satisfying FK's conditions a) and b). -/
abbrev ofIsEtaleSheaf (F : EtalePresheaf B S hS (Type v)) (hF : EtalePresheaf.IsEtaleSheaf F) :
    EtaleSheaf B S hS (Type v) :=
  ⟨F, (EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf F).mpr hF⟩

/-- The étale sheaf of abelian groups defined by a presheaf whose underlying presheaf of sets
satisfies FK's conditions a) and b). -/
abbrev ofIsEtaleSheafForget (F : EtalePresheaf B S hS AddCommGrpCat.{v})
    (hF : EtalePresheaf.IsEtaleSheaf (F ⋙ forget AddCommGrpCat)) :
    EtaleSheaf B S hS AddCommGrpCat.{v} :=
  ⟨F, (EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf_forget F).mpr hF⟩

/-- An étale sheaf of sets satisfies FK's conditions a) and b). -/
theorem isEtaleSheaf (F : EtaleSheaf B S hS (Type v)) : EtalePresheaf.IsEtaleSheaf F.obj :=
  (EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf F.obj).mp F.property

/-- The underlying presheaf of sets of an étale sheaf of abelian groups satisfies FK's
conditions a) and b). -/
theorem isEtaleSheaf_forget (F : EtaleSheaf B S hS AddCommGrpCat.{v}) :
    EtalePresheaf.IsEtaleSheaf (F.obj ⋙ forget AddCommGrpCat) :=
  (EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf_forget F.obj).mp F.property

end EtaleSheaf

end AlgebraicGeometry

end
