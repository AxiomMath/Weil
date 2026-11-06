module

public import StacksFrontier.AlgebraicGeometry.Limits.SeparatedCoproduct
public import StacksFrontier.AlgebraicGeometry.Topologies.BoundedSmallEtaleDisjointUnion
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# Finite disjoint unions in the étale category `Et(S)`

Let `U₁, …, Uₙ` (`n ≥ 0`) be objects of the étale category `Et(S)` of noetherian separated
étale `S`-schemes, with structure morphisms `uₖ : Uₖ ⟶ S`. The disjoint union
`U = U₁ ⊔ ⋯ ⊔ Uₙ`, with the morphism `U ⟶ S` equal to `uₖ` on `Uₖ`, is again an object of
`Et(S)`, and each inclusion `Uₖ ⟶ U` is a morphism of `Et(S)` whose underlying morphism of
schemes is an open immersion.

The scheme `U` is the coproduct `∐ Uₖ` in the category of schemes. It is étale over `S` since
étaleness is local on the source; it is noetherian because it is covered by the finitely many
open subschemes `Uₖ`, each noetherian; and it is separated since a disjoint union of separated
schemes is separated.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.sigmaObj`: the disjoint union of a finite
  family of objects of `Et(S)`, as an object of `Et(S)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.sigmaι`: the inclusion of a member into the
  disjoint union, as a morphism of `Et(S)`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.toScheme_obj_sigmaObj`: the underlying scheme
  of the disjoint union is the coproduct of the underlying schemes.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.structureMorphism_sigmaObj`: its structure
  morphism is the morphism induced by the structure morphisms of the members.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.toScheme_map_sigmaι`: on underlying schemes,
  the inclusion of a member is the coproduct injection.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isOpenImmersion_toScheme_map_sigmaι`: the
  inclusion of a member is an open immersion.

## Implementation notes

The family is indexed by an arbitrary finite type `ι` in the universe of the schemes, which
contains the case `ι = Fin n` of the source. The object is built from the disjoint union
`AlgebraicGeometry.SmallEtale.sigmaObj` in the small étale category, which is available for
countable families; finiteness is used only to see that the union is noetherian.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- A finite disjoint union of noetherian schemes is noetherian. -/
theorem Scheme.isNoetherian_sigma {ι : Type u} [Finite ι] (X : ι → Scheme.{u})
    [hX : ∀ i, IsNoetherian (X i)] : IsNoetherian (∐ X) := by
  rw [isNoetherian_iff]
  refine ⟨(isLocallyNoetherian_iff_openCover (sigmaOpenCover X)).mpr fun i ↦ ?_, ?_⟩
  · change IsLocallyNoetherian (X i)
    exact (hX i).toIsLocallyNoetherian
  · exact (sigmaMk X).compactSpace

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {ι : Type u} [Finite ι] (U : ι → SmallNoetherianSeparatedEtale B S hS)

/-- **The disjoint union of finitely many objects of `Et(S)`**, as an object of `Et(S)`: the
coproduct `∐ Uₖ` of the underlying schemes, with the structure morphism equal to `uₖ` on `Uₖ`. -/
@[weil "lem_fk102_etale_disjoint_union_in_et"]
noncomputable def sigmaObj : SmallNoetherianSeparatedEtale B S hS :=
  ⟨SmallEtale.sigmaObj B S hS (mk_le_aleph0 (α := ι)) fun i ↦ (U i).obj,
    Scheme.isNoetherian_sigma (fun i ↦ (toScheme B S hS).obj (U i)),
    Scheme.isSeparated_sigma _ fun i ↦ inferInstanceAs ((toScheme B S hS).obj (U i)).IsSeparated⟩

/-- **The inclusion of a member of a finite disjoint union**, as a morphism of `Et(S)`. -/
@[weil "lem_fk102_etale_disjoint_union_in_et"]
noncomputable def sigmaι (i : ι) : U i ⟶ sigmaObj U :=
  ObjectProperty.homMk (SmallEtale.sigmaι B S hS (mk_le_aleph0 (α := ι)) (fun i ↦ (U i).obj) i)

/-- The underlying scheme of a finite disjoint union in `Et(S)` is the coproduct of the
underlying schemes. -/
@[weil "lem_fk102_etale_disjoint_union_in_et"]
theorem toScheme_obj_sigmaObj :
    (toScheme B S hS).obj (sigmaObj U) = ∐ fun i ↦ (toScheme B S hS).obj (U i) :=
  rfl

/-- The structure morphism of a finite disjoint union in `Et(S)` is the morphism from the
coproduct induced by the structure morphisms of the members. -/
@[weil "lem_fk102_etale_disjoint_union_in_et"]
theorem structureMorphism_sigmaObj :
    structureMorphism (sigmaObj U) = Sigma.desc fun i ↦ structureMorphism (U i) :=
  rfl

/-- On underlying schemes, the inclusion of a member of a finite disjoint union in `Et(S)` is
the coproduct injection. -/
@[weil "lem_fk102_etale_disjoint_union_in_et"]
theorem toScheme_map_sigmaι (i : ι) :
    (toScheme B S hS).map (sigmaι U i) = Sigma.ι (fun i ↦ (toScheme B S hS).obj (U i)) i :=
  rfl

/-- The structure morphism of a finite disjoint union restricts to `uₖ` on the member `Uₖ`. -/
@[reassoc (attr := simp)]
theorem toScheme_map_sigmaι_comp_structureMorphism (i : ι) :
    (toScheme B S hS).map (sigmaι U i) ≫ structureMorphism (sigmaObj U) = structureMorphism (U i) :=
  toScheme_map_comp_structureMorphism _

/-- **The inclusion of a member of a finite disjoint union in `Et(S)` is an open immersion.** -/
@[weil "lem_fk102_etale_disjoint_union_in_et"]
instance isOpenImmersion_toScheme_map_sigmaι (i : ι) :
    IsOpenImmersion ((toScheme B S hS).map (sigmaι U i)) :=
  (sigmaOpenCover fun i ↦ (toScheme B S hS).obj (U i)).map_prop i

/-- The inclusion of a member of a finite disjoint union in `Et(S)` is a monomorphism. -/
instance mono_sigmaι (i : ι) : Mono (sigmaι U i) :=
  (toScheme B S hS).mono_of_mono_map inferInstance

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
