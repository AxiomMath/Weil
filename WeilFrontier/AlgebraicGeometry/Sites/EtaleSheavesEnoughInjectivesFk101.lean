module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleCategoryEssentiallySmall
public import WeilFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Abelian sheaves on the étale category of a ring have enough injectives

Let `A` be a commutative ring and `Et(A)` its étale category, realised as the small affine étale
site `AlgebraicGeometry.Scheme.AffineEtale (Spec A)` with the étale topology
`AlgebraicGeometry.Scheme.AffineEtale.topology (Spec A)`. The abelian category `Sh(A)` of
sheaves of abelian groups on `Et(A)` has enough injectives: every sheaf of abelian groups is a
subsheaf of an injective sheaf.

## Main results

* `AlgebraicGeometry.Scheme.AffineEtale.isGrothendieckAbelian_sheaf_addCommGrpCat`: for
  `A : CommRingCat.{u}` and a universe `w` with `UnivLE.{u, w}`, abelian sheaves on `Et(A)` with
  values in `AddCommGrpCat.{w}` form a Grothendieck abelian category.
* `AlgebraicGeometry.Scheme.AffineEtale.enoughInjectives_sheaf_addCommGrpCat`: this category has
  enough injectives.
* `AlgebraicGeometry.Scheme.AffineEtale.exists_mono_injective_sheaf`: every abelian sheaf `F`
  on `Et(A)` admits a monomorphism `F ⟶ I` into an injective abelian sheaf `I`.

## Implementation notes

The site `Et(A)` is essentially small, so the category of abelian sheaves on it is
Grothendieck abelian (`CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`):
filtered colimits are exact and the free abelian sheaves on representables generate. Grothendieck
abelian categories have enough injectives (`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`).
This is the argument through Grothendieck's AB5-and-generator criterion, packaged by the
Grothendieck abelian structure. The coefficients `AddCommGrpCat.{w}` are allowed in any universe
`w` at least the universe `u` of `A`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme.AffineEtale

variable (A : CommRingCat.{u}) [UnivLE.{u, w}]

/-- Abelian sheaves with values in `AddCommGrpCat.{w}`, `w ≥ u`, on the étale category of a ring
`A : CommRingCat.{u}` form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_sheaf_addCommGrpCat :
    letI := Scheme.hasSheafify_affineEtale_addCommGrpCat.{u, w} (Spec A)
    IsGrothendieckAbelian.{w} (Sheaf (topology (Spec A)) AddCommGrpCat.{w}) :=
  letI := Scheme.essentiallySmall_affineEtale.{u, w} (Spec A)
  letI := Scheme.hasSheafify_affineEtale_addCommGrpCat.{u, w} (Spec A)
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- The abelian category of sheaves of abelian groups (in `AddCommGrpCat.{w}`, `w ≥ u`) on the
étale category of a ring `A : CommRingCat.{u}` has enough injectives. -/
@[weil "thm_fk101_etale_sheaves_enough_injectives"]
theorem enoughInjectives_sheaf_addCommGrpCat :
    letI := Scheme.hasSheafify_affineEtale_addCommGrpCat.{u, w} (Spec A)
    EnoughInjectives (Sheaf (topology (Spec A)) AddCommGrpCat.{w}) :=
  letI := Scheme.hasSheafify_affineEtale_addCommGrpCat.{u, w} (Spec A)
  letI := isGrothendieckAbelian_sheaf_addCommGrpCat.{u, w} A
  IsGrothendieckAbelian.enoughInjectives

/-- Every sheaf of abelian groups on the étale category of a ring `A` is a subsheaf of an
injective sheaf: there is a monomorphism `F ⟶ I` with `I` injective in the category of abelian
sheaves. -/
@[weil "thm_fk101_etale_sheaves_enough_injectives"]
theorem exists_mono_injective_sheaf (F : Sheaf (topology (Spec A)) AddCommGrpCat.{w}) :
    ∃ (I : Sheaf (topology (Spec A)) AddCommGrpCat.{w}) (f : F ⟶ I), Injective I ∧ Mono f :=
  letI := Scheme.hasSheafify_affineEtale_addCommGrpCat.{u, w} (Spec A)
  letI := enoughInjectives_sheaf_addCommGrpCat.{u, w} A
  ⟨Injective.under F, Injective.ι F, inferInstance, inferInstance⟩

/-- For coefficients in the universe of `A`, the enough-injectives property is an instance. -/
instance (A : CommRingCat.{u}) :
    EnoughInjectives (Sheaf (topology (Spec A)) AddCommGrpCat.{u}) :=
  IsGrothendieckAbelian.enoughInjectives

end AlgebraicGeometry.Scheme.AffineEtale

end
