module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheaf
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtaleSheaf
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity

/-!
# The presheaf of divisors on `Et(S)` is an étale sheaf

Let `S` be a locally noetherian Jacobson scheme (for instance a smooth curve over a field) and
`Et(S)` its category of noetherian separated étale `S`-schemes. A divisor on an object `U` of
`Et(S)` is a finitely supported `ℤ`-valued function on the closed points of `U`. For a morphism
`ψ : V ⟶ U` of `Et(S)` and a divisor `D` on `U`, the function `D ∘ ψ` on the closed points of `V`
is again a divisor: `ψ` is étale, so it maps closed points to closed points, and its fibres over
the finitely many points of the support of `D` are finite, `V` being quasi-compact. This makes
`U ↦ Div(U)` a presheaf of abelian groups on `Et(S)`, and it is an étale sheaf: it is isomorphic
to the sheaf `⨁_x i_{x,*} ℤ` of divisors.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorPullback`: the pull-back
  `D ↦ D ∘ ψ` of divisors along a morphism of `Et(S)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorPresheaf`: the presheaf of divisors
  `U ↦ (closedPoints U →₀ ℤ)` on `Et(S)`, with restriction maps `D ↦ D ∘ ψ`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorPresheafCompUliftIso`: its
  identification with the sheaf `AlgebraicGeometry.SmallNoetherianSeparatedEtale.divisorSheaf`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.finite_support_comp_divisor`: the function
  `D ∘ ψ` is finitely supported.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isSheaf_divisorPresheaf`: the presheaf of
  divisors is an étale sheaf of abelian groups.

## Implementation notes

No curve hypothesis is needed: the argument uses only that `S` is locally noetherian and
Jacobson. The sheaf property is obtained from the identification with the coproduct of
skyscraper sheaves rather than by checking the gluing condition along coverings directly.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of `Et(S)` maps closed points to closed points, for `S` Jacobson. -/
theorem toScheme_map_mem_closedPoints [JacobsonSpace S]
    {V U : SmallNoetherianSeparatedEtale B S hS} (ψ : V ⟶ U)
    (y : closedPoints ((toScheme B S hS).obj V)) :
    (toScheme B S hS).map ψ y.1 ∈ closedPoints ((toScheme B S hS).obj U) :=
  Scheme.Etale.hom_left_mem_closedPoints
    ((SmallEtale.toEtaleSite B S hS).map ((inclusion B S hS).map ψ)) y

/-- The map of closed points induced by a morphism of `Et(S)`, for `S` Jacobson. -/
def closedPointsMap [JacobsonSpace S] {V U : SmallNoetherianSeparatedEtale B S hS} (ψ : V ⟶ U) :
    closedPoints ((toScheme B S hS).obj V) → closedPoints ((toScheme B S hS).obj U) :=
  fun y ↦ ⟨(toScheme B S hS).map ψ y.1, toScheme_map_mem_closedPoints ψ y⟩

@[simp]
theorem closedPointsMap_coe [JacobsonSpace S] {V U : SmallNoetherianSeparatedEtale B S hS}
    (ψ : V ⟶ U) (y : closedPoints ((toScheme B S hS).obj V)) :
    (closedPointsMap ψ y).1 = (toScheme B S hS).map ψ y.1 := rfl

/-- **The pull-back of a divisor along a morphism of `Et(S)` is a divisor**: for
`ψ : V ⟶ U` and a finitely supported function `D` on the closed points of `U`, the function
`D ∘ ψ` on the closed points of `V` is finitely supported. -/
@[weil "lem_fk105_divisor_sheaf_well_defined"]
theorem finite_support_comp_divisor [JacobsonSpace S] {V U : SmallNoetherianSeparatedEtale B S hS}
    (ψ : V ⟶ U) (D : closedPoints ((toScheme B S hS).obj U) →₀ ℤ) :
    (Function.support (D ∘ closedPointsMap ψ)).Finite := by
  have hfib : ∀ z ∈ D.support, (closedPointsMap ψ ⁻¹' {z}).Finite := by
    intro z _
    have h := ((toScheme B S hS).map ψ).finite_preimage_singleton_of_isClosed
      ((_root_.mem_closedPoints_iff).1 z.2)
    refine (h.preimage (Subtype.val_injective.injOn)).subset ?_
    intro y hy
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
    rw [← hy]
    rfl
  refine ((D.support.finite_toSet.biUnion hfib)).subset ?_
  intro y hy
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
  exact ⟨_, Finsupp.mem_support_iff.2 hy, rfl⟩

/-- **Pull-back of divisors** along a morphism `ψ : V ⟶ U` of `Et(S)`: `D ↦ D ∘ ψ`. -/
def divisorPullback [JacobsonSpace S] {V U : SmallNoetherianSeparatedEtale B S hS} (ψ : V ⟶ U) :
    (closedPoints ((toScheme B S hS).obj U) →₀ ℤ) →+ (closedPoints ((toScheme B S hS).obj V) →₀ ℤ)
    where
  toFun D := Finsupp.ofSupportFinite (D ∘ closedPointsMap ψ) (finite_support_comp_divisor ψ D)
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

@[simp]
theorem divisorPullback_apply [JacobsonSpace S] {V U : SmallNoetherianSeparatedEtale B S hS}
    (ψ : V ⟶ U) (D : closedPoints ((toScheme B S hS).obj U) →₀ ℤ)
    (y : closedPoints ((toScheme B S hS).obj V)) :
    divisorPullback ψ D y = D (closedPointsMap ψ y) := rfl

variable (B S hS) in
/-- **The presheaf of divisors on `Et(S)`**: `U ↦ (closedPoints U →₀ ℤ)`, the free abelian group
on the closed points of `U`, with restriction maps the pull-back `D ↦ D ∘ ψ`. -/
@[weil "lem_fk105_divisor_sheaf_well_defined"]
def divisorPresheaf [JacobsonSpace S] : EtalePresheaf B S hS AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (closedPoints ((toScheme B S hS).obj U.unop) →₀ ℤ)
  map ψ := AddCommGrpCat.ofHom (divisorPullback ψ.unop)
  map_id U := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun D ↦ Finsupp.ext fun y ↦ ?_)
    change D (closedPointsMap (𝟙 U.unop) y) = D y
    congr 1
  map_comp ψ χ := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun D ↦ Finsupp.ext fun y ↦ ?_)
    change D (closedPointsMap (χ.unop ≫ ψ.unop) y) =
      D (closedPointsMap ψ.unop (closedPointsMap χ.unop y))
    congr 1

variable [IsLocallyNoetherian S]

variable (B S hS) in
/-- The presheaf of divisors on `Et(S)`, with its values lifted to the universe of the sheaf
`divisorSheaf`, is the underlying presheaf of `divisorSheaf`. -/
def divisorPresheafCompUliftIso [JacobsonSpace S] :
    divisorPresheaf B S hS ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) v, u} ≅
      (divisorSheaf.{u, v} B S hS).obj :=
  NatIso.ofComponents
    (fun U ↦
      (AddEquiv.ulift.trans (divisorSheafSectionsAddEquiv.{u, v} U.unop).symm).toAddCommGrpIso)
    (by
      intro U V ψ
      ext ⟨D⟩
      apply (divisorSheafSectionsAddEquiv.{u, v} V.unop).injective
      ext y
      change divisorSheafSectionsAddEquiv.{u, v} V.unop
          ((divisorSheafSectionsAddEquiv.{u, v} V.unop).symm (divisorPullback ψ.unop D)) y =
        divisorSheafSectionsAddEquiv.{u, v} V.unop ((divisorSheaf.{u, v} B S hS).obj.map ψ.unop.op
          ((divisorSheafSectionsAddEquiv.{u, v} U.unop).symm D)) y
      rw [AddEquiv.apply_symm_apply, divisorSheafSectionsAddEquiv_map]
      erw [AddEquiv.apply_symm_apply]
      rfl)

/-- **The presheaf of divisors is an étale sheaf**: for `S` a locally noetherian Jacobson scheme
(for instance a smooth curve over a field), the presheaf `U ↦ (closedPoints U →₀ ℤ)` on `Et(S)`
with restriction maps `D ↦ D ∘ ψ` is a sheaf of abelian groups for the étale topology. -/
@[weil "lem_fk105_divisor_sheaf_well_defined"]
theorem isSheaf_divisorPresheaf [JacobsonSpace S] :
    Presheaf.IsSheaf (topology B S hS) (divisorPresheaf B S hS) :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ AddCommGrpCat.uliftFunctor.{u + 1, u}
    ((Presheaf.isSheaf_of_iso_iff (divisorPresheafCompUliftIso.{0} B S hS)).2
      (divisorSheaf.{u, 0} B S hS).property)

/-- FK's conditions a) and b) of an étale sheaf hold for the presheaf of divisors. -/
theorem isEtaleSheaf_divisorPresheaf [JacobsonSpace S] :
    EtalePresheaf.IsEtaleSheaf (divisorPresheaf B S hS ⋙ forget AddCommGrpCat) :=
  (EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf_forget _).1 isSheaf_divisorPresheaf

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end

/-! ### The sheaf of divisors as a sum of skyscraper sheaves -/

/-!
# The sheaf of divisors as a sum of skyscraper sheaves

Let `X` be a scheme locally of finite type over an algebraically closed field `K` (for instance a
smooth curve over `K`). Every closed point `x` of `X` has residue field `K`, so it is the image of a
unique `K`-point `x : Spec K ⟶ X` (`AlgebraicGeometry.pointOfClosedPoint`, a bijection by
`AlgebraicGeometry.pointEquivClosedPoint`). The sheaf of divisors `𝒟_X` on the étale site of `X`
is the direct sum, over the closed points, of the direct images `x_* ℤ` of the constant sheaf `ℤ`
on `Spec K` along these `K`-points:
`𝒟_X ≅ ⨁_{x closed} x_* ℤ`.

The sheaf of divisors is the coproduct `⨁_x i_{x,*} ℤ` of the direct images along the inclusions
`i_x : Spec κ(x) ⟶ X` of the points (`Stacks.EtaleCohomology.closedPointDivisorSheaf`); its
sections are the divisors
(`AlgebraicGeometry.Scheme.Etale.closedPointDivisorSheafSectionsAddEquiv`).
The `K`-point `x` is `i_x` precomposed with the isomorphism `Spec K ≅ Spec κ(x)`, and the direct
image of a constant sheaf along an isomorphism of schemes is the constant sheaf, which gives the
isomorphism summand by summand.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianDirectImageEquivOfIso`: the direct image along an
  isomorphism of schemes is an equivalence of categories of abelian étale sheaves.
* `AlgebraicGeometry.pointOfClosedPointSkyscraper`: the skyscraper `x_* ℤ` along the `K`-point
  of a closed point.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDirectImageConstantSheafIsoOfIso`: the direct image of a
  constant sheaf along an isomorphism of schemes is the constant sheaf.
* `AlgebraicGeometry.closedPointDivisorSheafIsoSigmaPointOfClosedPointSkyscraper`:
  `⨁_x i_{x,*} ℤ ≅ ⨁_x x_* ℤ` on Mathlib's small étale site of `X`.
* `SmallNoetherianSeparatedEtale.divisorSheafIsoSigmaPointOfClosedPointSkyscraperEt`:
  `𝒟_X ≅ ⨁_x x_* ℤ` in the category of abelian sheaves on the étale site `Et(X)` of noetherian
  separated étale `X`-schemes.

## Implementation notes

The sheaf of divisors is defined as the coproduct of skyscraper sheaves, and the identification
of its sections with finitely supported functions on closed points is a theorem; so the argument
by which the presheaf of divisors is shown to be a direct sum of skyscraper presheaves, and its
sheafification to be itself, is replaced by the comparison of the two families of skyscrapers.
No curve or smoothness hypothesis is needed: `X` locally of finite type over `K` suffices.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.EtaleCohomology

universe u v

namespace Stacks.EtaleCohomology

/-- The direct image along the identity is the identity. -/
def etaleAbelianDirectImageIdIsoUniv (X : Scheme.{u}) :
    etaleAbelianDirectImage.{u, v} (𝟙 X) ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X) _ _

/-- The direct image along an isomorphism of schemes is an equivalence of categories of abelian
sheaves on the small étale sites, with inverse the direct image along the inverse. -/
def etaleAbelianDirectImageEquivOfIso {Y' Y : Scheme.{u}} (e : Y' ≅ Y) :
    Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ≌
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  CategoryTheory.Equivalence.mk (etaleAbelianDirectImage.{u, v} e.hom)
    (etaleAbelianDirectImage.{u, v} e.inv)
    ((etaleAbelianDirectImageIdIsoUniv.{u, v} Y').symm ≪≫
      (etaleAbelianDirectImageCompIso'.{u, v} e.hom e.inv (𝟙 Y') e.hom_inv_id.symm).symm)
    (etaleAbelianDirectImageCompIso'.{u, v} e.inv e.hom (𝟙 Y) e.inv_hom_id.symm ≪≫
      etaleAbelianDirectImageIdIsoUniv.{u, v} Y)

/-- **The direct image of a constant sheaf along an isomorphism of schemes is the constant
sheaf.** -/
def etaleAbelianDirectImageConstantSheafIsoOfIso {Y' Y : Scheme.{u}} (e : Y' ≅ Y)
    (M : AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianDirectImage.{u, v} e.hom).obj
        ((constantSheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj M) ≅
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj M :=
  let E := etaleAbelianDirectImageEquivOfIso.{u, v} e
  let α : etaleAbelianInverseImage.{u, v} e.hom ≅ E.inverse :=
    (etaleAbelianInverseImageDirectImageAdj.{u, v} e.hom).leftAdjointUniq E.symm.toAdjunction
  E.functor.mapIso (((etaleAbelianInverseImageConstantIso.{u, v} e.hom).app M).symm ≪≫
      α.app _) ≪≫ E.counitIso.app _

/-- **The direct image of a constant sheaf along a morphism factoring through an isomorphism**:
if `p = e.hom ≫ i` with `e : Y' ≅ Y`, then `p_* M ≅ i_* M` for the constant sheaves `M` on the
small étale sites of `Y'` and `Y`. -/
def etaleAbelianDirectImageConstantSheafIsoOfFactor {Y' Y X : Scheme.{u}} (e : Y' ≅ Y)
    (i : Y ⟶ X) (p : Y' ⟶ X) (hp : p = e.hom ≫ i) (M : AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianDirectImage.{u, v} p).obj
        ((constantSheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj M) ≅
      (etaleAbelianDirectImage.{u, v} i).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj M) :=
  ((etaleAbelianDirectImageCompIso'.{u, v} e.hom i p hp).app _).symm ≪≫
    (etaleAbelianDirectImage.{u, v} i).mapIso
      (etaleAbelianDirectImageConstantSheafIsoOfIso.{u, v} e M)

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- The skyscraper `x_* ℤ` along the `K`-point `x : Spec K ⟶ X` of a closed point of a scheme
locally of finite type over an algebraically closed field `K`, is the skyscraper
`i_{x,*} ℤ` along `Spec κ(x) ⟶ X`. -/
def pointOfClosedPointDirectImageConstantIso (x : closedPoints X) :
    (etaleAbelianDirectImage.{u, v} (pointOfClosedPoint f x.1 x.2)).obj
        ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift ℤ))) ≅
      closedPointSkyscraper.{u, v} X x :=
  etaleAbelianDirectImageConstantSheafIsoOfFactor.{u, v}
    (Scheme.Spec.mapIso (residueFieldIsoBase f x.1 x.2).op) (X.fromSpecResidueField x.1)
    (pointOfClosedPoint f x.1 x.2) rfl _

/-- **The skyscraper `x_* ℤ` at a closed point**, along the `K`-point
`x : Spec K ⟶ X` (`AlgebraicGeometry.pointOfClosedPoint`) of a closed point of a scheme locally
of finite type over an algebraically closed field `K`: the direct image of the constant sheaf `ℤ`
on the small étale site of `Spec K`. -/
abbrev pointOfClosedPointSkyscraper (x : closedPoints X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (etaleAbelianDirectImage.{u, v} (pointOfClosedPoint f x.1 x.2)).obj
    ((constantSheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (AddCommGrpCat.of (ULift ℤ)))

/-- The coproduct `⨁_x x_* ℤ` of the skyscrapers along the `K`-points of the closed points
exists. -/
instance hasCoproduct_pointOfClosedPointSkyscraper :
    HasCoproduct (pointOfClosedPointSkyscraper.{u, v} f) :=
  Scheme.hasColimit_sheaf_smallEtaleTopology.{u, v} X _

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- **The sheaf of divisors is the sum of the skyscrapers at the closed points**: for `X` locally
of finite type over an algebraically closed field `K`, the sheaf of divisors
`⨁_x i_{x,*} ℤ` on the small étale site of `X` is isomorphic to `⨁_{x closed} x_* ℤ`, where
`x : Spec K ⟶ X` is the `K`-point of the closed point `x` and `ℤ` is the constant sheaf on
`Spec K`. -/
@[weil "lem_fk105_divisor_sheaf_sum_of_skyscrapers"]
def closedPointDivisorSheafIsoSigmaPointOfClosedPointSkyscraper :
    closedPointDivisorSheaf.{u, v} X ≅ ∐ pointOfClosedPointSkyscraper.{u, v} f :=
  HasColimit.isoOfNatIso
    (Discrete.natIso fun x ↦ (pointOfClosedPointDirectImageConstantIso.{u, v} f x.as).symm)

/-- The isomorphism `closedPointDivisorSheafIsoSigmaPointOfClosedPointSkyscraper` maps the
summand at `x` to the summand at `x`. -/
@[reassoc (attr := simp)]
theorem ι_closedPointDivisorSheafIsoSigmaPointOfClosedPointSkyscraper_hom (x : closedPoints X) :
    closedPointDivisorSheaf.ι.{u, v} X x ≫
        (closedPointDivisorSheafIsoSigmaPointOfClosedPointSkyscraper.{u, v} f).hom =
      (pointOfClosedPointDirectImageConstantIso.{u, v} f x).inv ≫
        Sigma.ι (pointOfClosedPointSkyscraper.{u, v} f) x := by
  simp only [closedPointDivisorSheafIsoSigmaPointOfClosedPointSkyscraper, closedPointDivisorSheaf.ι]
  exact HasColimit.isoOfNatIso_ι_hom _ (Discrete.mk x)

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (hX : B.Contains X)

/-- The skyscraper `x_* ℤ` along the `K`-point of a closed point, as a sheaf on the étale site
`Et(X)`. -/
abbrev pointOfClosedPointSkyscraperEt (x : closedPoints X) :
    haveI := LocallyOfFiniteType.isLocallyNoetherian f
    Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v} :=
  haveI := LocallyOfFiniteType.isLocallyNoetherian f
  (sheafEquivEtale B X hX AddCommGrpCat.{max (u + 1) v}).inverse.obj
    (pointOfClosedPointSkyscraper.{u, v} f x)

/-- The coproduct `⨁_x x_* ℤ` in the category of abelian sheaves on `Et(X)` exists. -/
instance hasCoproduct_pointOfClosedPointSkyscraperEt :
    HasCoproduct (pointOfClosedPointSkyscraperEt.{u, v} f B hX) :=
  haveI := LocallyOfFiniteType.isLocallyNoetherian f
  let E := sheafEquivEtale B X hX AddCommGrpCat.{max (u + 1) v}
  haveI : PreservesColimitsOfSize.{u, u} E.inverse :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits
  haveI : HasColimit (Discrete.functor (pointOfClosedPointSkyscraper.{u, v} f) ⋙ E.inverse) :=
    inferInstance
  hasColimit_of_iso (Discrete.compNatIsoDiscrete _ E.inverse).symm

/-- **The sheaf of divisors `𝒟_X` on `Et(X)` is the sum of the skyscrapers at the closed points**
(FK I.5): for `X` locally of finite type over an algebraically closed field `K` (for instance a
smooth curve over `K`), `𝒟_X ≅ ⨁_{x closed} x_* ℤ` in the category of abelian sheaves on
`Et(X)`, where `x : Spec K ⟶ X` is the `K`-point of the closed point `x` and `ℤ` is the
constant sheaf on `Spec K`. -/
@[weil "lem_fk105_divisor_sheaf_sum_of_skyscrapers"]
def divisorSheafIsoSigmaPointOfClosedPointSkyscraperEt :
    haveI := LocallyOfFiniteType.isLocallyNoetherian f
    divisorSheaf.{u, v} B X hX ≅ ∐ pointOfClosedPointSkyscraperEt.{u, v} f B hX :=
  haveI := LocallyOfFiniteType.isLocallyNoetherian f
  let E := sheafEquivEtale B X hX AddCommGrpCat.{max (u + 1) v}
  haveI : PreservesColimitsOfSize.{u, u} E.inverse :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits
  haveI : PreservesColimitsOfShape (Discrete (closedPoints X)) E.inverse :=
    PreservesColimitsOfSize.preservesColimitsOfShape
  haveI : PreservesColimit (Discrete.functor (pointOfClosedPointSkyscraper.{u, v} f)) E.inverse :=
    PreservesColimitsOfShape.preservesColimit
  E.inverse.mapIso (closedPointDivisorSheafIsoSigmaPointOfClosedPointSkyscraper.{u, v} f) ≪≫
    PreservesCoproduct.iso E.inverse (pointOfClosedPointSkyscraper.{u, v} f)

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry
