module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Abelian sheaves on the small étale site have enough injectives

Let `X` be a scheme. Every sheaf of abelian groups on the small étale site of `X` admits a
monomorphism into an injective object of the category of abelian sheaves.

## Main results

* `AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat`: for
  `X : Scheme.{u}` and any universe `w` with `UnivLE.{u, w}`, abelian sheaves on the small étale
  site of `X` with values in `AddCommGrpCat.{w}` form a Grothendieck abelian category.
* `AlgebraicGeometry.Scheme.exists_mono_injective_sheaf_smallEtaleTopology`: every abelian sheaf
  `F` on the small étale site of `X` admits a monomorphism `F ⟶ I` with `I` injective.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale X` with the topology
`AlgebraicGeometry.Scheme.smallEtaleTopology X`; its objects are all schemes étale over `X`, not
only the noetherian separated ones. The coefficients are `AddCommGrpCat.{w}` for any
universe `w` at least the morphism universe `u` of the site (`UnivLE.{u, w}`); this covers both
`w = u` and the coefficient universe `u + 1` of cohomology. The category of abelian sheaves is
Grothendieck abelian, since the site has the affine étale schemes as a dense subsite which is
essentially small at `u`, hence at `w`; Grothendieck abelian categories have enough
injectives. This replaces the argument through an explicit set of generators `ℤ_U` and the AB5
criterion: both are the content of the Grothendieck abelian structure.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §2.
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) [UnivLE.{u, w}]

/-- The small affine étale site of `S : Scheme.{u}` is essentially small at every universe
`w ≥ u`. -/
theorem essentiallySmall_affineEtale : EssentiallySmall.{w} S.AffineEtale := by
  obtain ⟨_, _⟩ := (essentiallySmall_iff.{u} S.AffineEtale).1 inferInstance
  exact (essentiallySmall_iff.{w} _).2 ⟨Small.trans_univLE.{u} _, inferInstance⟩

/-- Abelian presheaves with values in `AddCommGrpCat.{w}`, `w ≥ u`, on the small affine étale
site of `S : Scheme.{u}` admit a sheafification. -/
theorem hasSheafify_affineEtale_addCommGrpCat :
    HasSheafify (AffineEtale.topology S) AddCommGrpCat.{w} :=
  have := essentiallySmall_affineEtale.{u, w} S
  hasSheafifyEssentiallySmallSite.{u, w, u + 1, w + 1, w} _ _

instance isEquivalence_sheafPushforwardContinuous_affineEtale_addCommGrpCat :
    ((AffineEtale.Spec S).sheafPushforwardContinuous AddCommGrpCat.{w}
      (AffineEtale.topology S) S.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense.{u} _ _ _ _

/-- Abelian presheaves with values in `AddCommGrpCat.{w}`, `w ≥ u`, on the small étale site of
`S : Scheme.{u}` admit a sheafification. -/
instance hasSheafify_smallEtaleTopology_addCommGrpCat :
    HasSheafify S.smallEtaleTopology AddCommGrpCat.{w} :=
  have := hasSheafify_affineEtale_addCommGrpCat.{u, w} S
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (AffineEtale.topology S) S.smallEtaleTopology (AffineEtale.Spec S)

/-- Abelian sheaves with values in `AddCommGrpCat.{w}`, `w ≥ u`, on the small étale site of
`S : Scheme.{u}` form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat :
    IsGrothendieckAbelian.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{w}) := by
  have := essentiallySmall_affineEtale.{u, w} S
  have := hasSheafify_affineEtale_addCommGrpCat.{u, w} S
  have : IsGrothendieckAbelian.{w} (Sheaf (AffineEtale.topology S) AddCommGrpCat.{w}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  exact IsGrothendieckAbelian.of_equivalence ((AffineEtale.Spec S).sheafPushforwardContinuous _
    (AffineEtale.topology S) S.smallEtaleTopology).asEquivalence.symm

/-- Abelian sheaves with values in `AddCommGrpCat.{w}`, `w ≥ u`, on the small étale site of
`S : Scheme.{u}` have all `w`-small colimits. -/
instance hasColimitsOfSize_sheaf_smallEtaleTopology_addCommGrpCat :
    Limits.HasColimitsOfSize.{w, w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{w}) :=
  IsGrothendieckAbelian.hasColimits _

/-- Every sheaf of abelian groups on the small étale site of a scheme `X` is a subobject of an
injective abelian sheaf: there is a monomorphism from it into an injective object. The
coefficients are `AddCommGrpCat.{w}` for any universe `w` with `UnivLE.{u, w}`. -/
@[weil "lem_fk102_etale_sheaves_enough_injectives"]
theorem exists_mono_injective_sheaf_smallEtaleTopology (X : Scheme.{u})
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{w}) :
    ∃ (I : Sheaf (smallEtaleTopology X) AddCommGrpCat.{w}) (f : F ⟶ I), Injective I ∧ Mono f :=
  ⟨Injective.under F, Injective.ι F, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme

end
