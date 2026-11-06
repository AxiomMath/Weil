module

public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheafCategory
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Weil.Attr

/-!
# The category of torsion sheaves is abelian

Let `S` be a scheme. Torsion sheaves on the small étale site of `S` form a Serre class in the
abelian category of abelian sheaves: a subsheaf, a quotient sheaf and an extension of torsion
sheaves are torsion sheaves. In particular a finite direct sum of torsion sheaves is a torsion
sheaf, and the kernel and the cokernel (in the abelian sheaves) of a morphism of torsion sheaves
are torsion sheaves. Consequently the full subcategory `𝒯(S)` of torsion sheaves is abelian, its
inclusion into the abelian sheaves preserves finite limits and finite colimits (so kernels and
cokernels in `𝒯(S)` are those of the abelian sheaves), and a short complex in `𝒯(S)` is exact
if and only if it is exact as a short complex of abelian sheaves.

## Main results

* `AlgebraicGeometry.SmallEtale.IsTorsionSheaf.of_mono`: a subsheaf of a torsion sheaf is torsion.
* `AlgebraicGeometry.SmallEtale.IsTorsionSheaf.of_epi`: a quotient of a torsion sheaf is torsion.
* `AlgebraicGeometry.SmallEtale.IsTorsionSheaf.biproduct`: a finite direct sum of torsion sheaves
  is torsion.
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.abelian`: `𝒯(S)` is an abelian category.
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.preservesFiniteLimits_ι`,
  `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.preservesFiniteColimits_ι`: kernels and
  cokernels in `𝒯(S)` are computed in the abelian sheaves.
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.exact_map_ι_iff`: exactness in `𝒯(S)` is
  exactness in the abelian sheaves.

## Implementation notes

Torsion sheaves are the locally torsion sheaves `Stacks.Torsion.torsionSheafProperty`; their
closure properties are the Serre class `Stacks.Torsion.torsionSheafProperty_isSerreClass`, proved
with sections and covering sieves rather than with stalks. For a locally noetherian `S` the
torsion sheaves are those whose sections over every noetherian separated étale `S`-scheme form a
torsion group (`AlgebraicGeometry.SmallEtale.isTorsionSheaf_iff_forall_isAddTorsion`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace IsTorsionSheaf

/-- **A subsheaf of a torsion sheaf is a torsion sheaf.** -/
@[weil "lem_fk104_torsion_sheaf_category_abelian"]
theorem of_mono {F G : Sheaf (topology B S hS) AddCommGrpCat.{u}} (f : F ⟶ G) [Mono f]
    (hG : IsTorsionSheaf B S hS G) : IsTorsionSheaf B S hS F :=
  (IsTorsionSheaf B S hS).prop_of_mono f hG

/-- **A quotient sheaf of a torsion sheaf is a torsion sheaf.** -/
@[weil "lem_fk104_torsion_sheaf_category_abelian"]
theorem of_epi {F G : Sheaf (topology B S hS) AddCommGrpCat.{u}} (f : F ⟶ G) [Epi f]
    (hF : IsTorsionSheaf B S hS F) : IsTorsionSheaf B S hS G :=
  (IsTorsionSheaf B S hS).prop_of_epi f hF

/-- **A finite direct sum of torsion sheaves is a torsion sheaf.** -/
@[weil "lem_fk104_torsion_sheaf_category_abelian"]
theorem biproduct {ι : Type*} [Finite ι] (F : ι → Sheaf (topology B S hS) AddCommGrpCat.{u})
    [HasBiproduct F] (hF : ∀ i, IsTorsionSheaf B S hS (F i)) :
    IsTorsionSheaf B S hS (⨁ F) :=
  (IsTorsionSheaf B S hS).prop_of_iso (biproduct.isoProduct F).symm
    ((IsTorsionSheaf B S hS).prop_product hF)

/-- The kernel of a morphism of torsion sheaves is a torsion sheaf. -/
theorem kernel {F G : Sheaf (topology B S hS) AddCommGrpCat.{u}} (f : F ⟶ G)
    (hF : IsTorsionSheaf B S hS F) : IsTorsionSheaf B S hS (Limits.kernel f) :=
  of_mono (Limits.kernel.ι f) hF

/-- The cokernel of a morphism of torsion sheaves is a torsion sheaf. -/
theorem cokernel {F G : Sheaf (topology B S hS) AddCommGrpCat.{u}} (f : F ⟶ G)
    (hG : IsTorsionSheaf B S hS G) : IsTorsionSheaf B S hS (Limits.cokernel f) :=
  of_epi (Limits.cokernel.π f) hG

end IsTorsionSheaf

namespace TorsionSheafCategory

variable (B S hS)

/-- **The category `𝒯(S)` of torsion sheaves is abelian.** It is the abelian structure of the
full subcategory of a Serre class. -/
@[weil "lem_fk104_torsion_sheaf_category_abelian"]
noncomputable instance abelian : Abelian (TorsionSheafCategory B S hS) :=
  inferInstance

/-- **Kernels in `𝒯(S)` are those of the abelian sheaves**: the inclusion preserves finite
limits. -/
@[weil "lem_fk104_torsion_sheaf_category_abelian"]
instance preservesFiniteLimits_ι : PreservesFiniteLimits (ι B S hS) :=
  inferInstance

/-- **Cokernels in `𝒯(S)` are those of the abelian sheaves**: the inclusion preserves finite
colimits. -/
@[weil "lem_fk104_torsion_sheaf_category_abelian"]
instance preservesFiniteColimits_ι : PreservesFiniteColimits (ι B S hS) :=
  inferInstance

/-- **Exact sequences in `𝒯(S)` are those of the abelian sheaves.** -/
@[weil "lem_fk104_torsion_sheaf_category_abelian"]
theorem exact_map_ι_iff (T : ShortComplex (TorsionSheafCategory B S hS)) :
    (T.map (ι B S hS)).Exact ↔ T.Exact :=
  T.exact_map_iff_of_faithful (ι B S hS)

end TorsionSheafCategory

end AlgebraicGeometry.SmallEtale

end
