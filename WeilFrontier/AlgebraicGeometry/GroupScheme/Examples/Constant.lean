module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.GroupScheme.Examples.Constant
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import WeilFrontier.Defs.CategoryTheory.Yoneda

/-!
# The constant group scheme represents the constant sheaf

Let `X` be a scheme and `F` a finite group, with constant group scheme `F̃_X = ∐_{σ ∈ F} X`
(`AlgebraicGeometry.sigmaConstOver X F` with its group law
`AlgebraicGeometry.sigmaConstOver.instGrpObj`). The presheaf `h_{F̃_X}` on the étale category
`Et(X)` represented by `F̃_X` is a presheaf of groups, the group structure on
`Hom_X(U, F̃_X)` being induced by the multiplication of `F̃_X`. It is isomorphic, as a presheaf
of groups, to the constant presheaf `F_X` of locally constant maps `|U| → F` with pointwise
multiplication.

A morphism of `X`-schemes `g : U ⟶ F̃_X` is the same as a partition of `U` into the open and
closed subsets `U_σ = g⁻¹(copy σ)`, i.e. a locally constant map `k : |U| → F`, and under this
bijection the product of two morphisms is the pointwise product of the locally constant maps.

## Main definitions

* `AlgebraicGeometry.representablePresheafGrp` — the presheaf of groups `h_G` on `Et(S)`
  represented by a group object `G` of `S`-schemes.

## Main results

* `AlgebraicGeometry.representablePresheafGrp_comp_forget` — the underlying presheaf of sets
  of `h_G` is the representable presheaf `AlgebraicGeometry.representablePresheaf`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.representablePresheafGrpSigmaConstOverIso` —
  `h_{F̃_X} ≅ F_X` as presheaves of groups on `Et(X)`.

## Implementation notes

The isomorphism is obtained by restricting to `Et(X)` the isomorphism of group-valued functors
of points on all `X`-schemes between the constant group scheme of the Stacks project and the
locally constant maps (`AlgebraicGeometry.constantGroupSchemePointsIsoLocallyConstantMaps`),
transported along the identification of group objects
`AlgebraicGeometry.constantGroupScheme.isoGrpSigmaConstOver`. Both presheaves are sheaves for
the étale topology, so this is an isomorphism of sheaves of groups, the category of sheaves
being a full subcategory of presheaves.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03YW](https://stacks.math.columbia.edu/tag/03YW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

open SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf of groups `h_G : U ↦ Hom_S(U, G)` on `Et(S)` represented by a group object `G`
of `S`-schemes, the group structure on `Hom_S(U, G)` being induced by the multiplication of
`G`. -/
abbrev representablePresheafGrp (G : Over S) [GrpObj G] : EtalePresheaf B S hS GrpCat.{u} :=
  (toOver B S hS).op ⋙ yonedaGrpObj G

/-- The underlying presheaf of sets of `h_G` is the presheaf `h_G` represented by `G`. -/
lemma representablePresheafGrp_comp_forget (G : Over S) [GrpObj G] :
    representablePresheafGrp B S hS G ⋙ forget GrpCat = representablePresheaf B S hS G :=
  rfl

namespace SmallNoetherianSeparatedEtale

variable (F : Type u) [Finite F] [Group F]

/-- The universe lift `GrpCat.{u} ⥤ GrpCat.{u}` is isomorphic to the identity. -/
def grpCatUliftFunctorIsoId : GrpCat.uliftFunctor.{u, u} ≅ 𝟭 GrpCat.{u} :=
  NatIso.ofComponents (fun G ↦ (MulEquiv.ulift (α := G)).toGrpIso) (fun _ ↦ rfl)

/-- The group-valued functor of points of `F̃_X` on all `X`-schemes is the functor of locally
constant `F`-valued maps. -/
def yonedaGrpObjSigmaConstOverIso :
    yonedaGrpObj (sigmaConstOver S F) ≅ locallyConstantMapsOver F S :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ grpCatUliftFunctorIsoId.symm ≪≫
    Functor.isoWhiskerRight (yonedaGrp.mapIso constantGroupScheme.isoGrpSigmaConstOver)
      GrpCat.uliftFunctor.{u, u} ≪≫
    constantGroupSchemePointsIsoLocallyConstantMaps F S

/-- On `Et(S)`, the functor of locally constant maps on `S`-schemes restricts to the presheaf of
groups `F_S`. -/
def toOverOpCompLocallyConstantMapsOverIso :
    (toOver B S hS).op ⋙ locallyConstantMapsOver F S ≅ locallyConstantPresheafGrp B S hS F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- **The constant group scheme represents the constant sheaf.** For a finite group `F`, the
presheaf of groups `h_{F̃_X}` on `Et(X)` represented by the constant group scheme
`F̃_X = ∐_{σ ∈ F} X`, with the group structure induced by the multiplication of `F̃_X`, is
isomorphic to the presheaf of groups `F_X` of locally constant maps `|U| → F` with pointwise
multiplication. -/
@[weil "lem_fk102_constant_group_scheme_represents"]
def representablePresheafGrpSigmaConstOverIso :
    representablePresheafGrp B S hS (sigmaConstOver S F) ≅ locallyConstantPresheafGrp B S hS F :=
  Functor.isoWhiskerLeft (toOver B S hS).op (yonedaGrpObjSigmaConstOverIso S F) ≪≫
    toOverOpCompLocallyConstantMapsOverIso B S hS F

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
