module

public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.Attr

/-!
# The category of torsion sheaves on the small étale site

For a scheme `S`, the category `𝒯(S)` of torsion sheaves is the full subcategory of the category
of abelian sheaves on the small étale site of `S` whose objects are the torsion sheaves
(`AlgebraicGeometry.SmallEtale.IsTorsionSheaf`): the abelian sheaves every section of which is
locally annihilated by a positive integer. For a locally noetherian `S` these are exactly the
abelian sheaves whose groups of sections over every noetherian separated étale `S`-scheme are
torsion groups.

## Main definitions

* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory`: the full subcategory `𝒯(S)` of torsion
  sheaves, which is `Stacks.Torsion.TorsionSheaf` for the small étale topology.

## Main results

* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.fullyFaithfulι`: the inclusion of `𝒯(S)`
  into the abelian sheaves is fully faithful.
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.mem_essImage_ι_iff`: for a locally
  noetherian `S`, an abelian sheaf is isomorphic to an object of `𝒯(S)` if and only if its
  sections over every noetherian separated étale `S`-scheme form a torsion group.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The category of torsion sheaves** `𝒯(S)`: the full subcategory of the abelian sheaves on
the small étale site of `S` whose objects are the torsion sheaves. -/
@[weil "not_fk104_torsion_sheaf_category"]
abbrev TorsionSheafCategory : Type (u + 1) :=
  Stacks.Torsion.TorsionSheaf.{u} (topology B S hS)

namespace TorsionSheafCategory

/-- The inclusion of the torsion sheaves into the abelian sheaves. -/
abbrev ι : TorsionSheafCategory B S hS ⥤ Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  (IsTorsionSheaf.{u} B S hS).ι

/-- The inclusion of `𝒯(S)` into the abelian sheaves is fully faithful. -/
@[weil "not_fk104_torsion_sheaf_category"]
def fullyFaithfulι : (ι B S hS).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- **Objects of `𝒯(S)`.** For a locally noetherian `S`, an abelian sheaf on the small étale site
of `S` is isomorphic to a torsion sheaf if and only if its sections over every noetherian
separated étale `S`-scheme form a torsion group. -/
@[weil "not_fk104_torsion_sheaf_category"]
theorem mem_essImage_ι_iff [IsLocallyNoetherian S]
    (F : Sheaf (topology B S hS) AddCommGrpCat.{u}) :
    (ι B S hS).essImage F ↔ ∀ U : SmallNoetherianSeparatedEtale B S hS,
      IsAddTorsion (F.obj.obj (op ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U))) := by
  rw [← isTorsionSheaf_iff_forall_isAddTorsion]
  exact ⟨fun ⟨G, ⟨e⟩⟩ ↦ (IsTorsionSheaf.{u} B S hS).prop_of_iso e G.property,
    fun hF ↦ ⟨⟨F, hF⟩, ⟨Iso.refl _⟩⟩⟩

end TorsionSheafCategory

end AlgebraicGeometry.SmallEtale

end
