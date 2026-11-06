module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.AffineSheavesEquivalence
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleComparison
public import WeilFrontier.Defs.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology

/-!
# Étale cohomology of an affine scheme is the étale cohomology of its ring

Let `A` be a noetherian ring and `X = Spec A`. For an abelian sheaf `F` on the étale site of `X`,
let `F₀` be its restriction to the étale category `Et(A)` of étale `A`-algebras, so that
`F₀(B) = F(Spec B)`. Then `H^i(Spec A, F) ≅ H^i(A, F₀)` for all `i ≥ 0`, naturally in `F`.

Here `H^i(Spec A, -)` is the cohomology of the small étale site of `Spec A` and `H^i(A, -)` the
cohomology of the affine étale site `Scheme.AffineEtale.topology (Spec A)`, both Mathlib's
`CategoryTheory.Sheaf.H`. The restriction `F ↦ F₀` is
`AlgebraicGeometry.affineSheafEquiv` applied to the restriction of `F` to the category `Et(X)` of
noetherian separated étale `X`-schemes.

## Main definitions

* `AlgebraicGeometry.affineCohomologySheafEquiv`: the equivalence `F ↦ F₀` from abelian sheaves
  on the small étale site of `Spec A` to abelian sheaves on `Et(A)`.
* `AlgebraicGeometry.affineCohomologyAddEquiv`: `H^n(Spec A, F) ≃+ H^n(A, F₀)`.
* `AlgebraicGeometry.etaleSheafAffineCohomologyAddEquiv`: the same for a sheaf `F` on `Et(X)`,
  with `H^n(Spec A, F)` the cohomology of its extension to the small étale site.

## Main results

* `AlgebraicGeometry.affineCohomologyAddEquiv_map`,
  `AlgebraicGeometry.etaleSheafAffineCohomologyAddEquiv_map`: the isomorphisms are natural in
  the sheaf.

## Implementation notes

The source transports an injective resolution along the equivalence `F ↦ F₀`. Here the
comparison of cohomology along an exact equivalence carrying the constant sheaf `ℤ` to the
constant sheaf is used instead (`Stacks.ExtAdjunction.functorHComparisonIso`); the compatibility
with constant sheaves comes from the fact that both the small étale site of `Spec A` in this
library and `Et(A)` are dense subsites of Mathlib's small étale site of `Spec A`, and
restriction to a dense subsite preserves constant sheaves
(`Stacks.Cohomology.DenseSubsite.constantSheafRestrictionIso`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.2
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (B : BigEtaleSite.{u})
  (hS : B.Contains (Spec A))

/-- The restriction `F ↦ F₀` from abelian sheaves on the small étale site of `Spec A` to abelian
sheaves on the étale category `Et(A)` of the ring `A`, as an equivalence: restriction to the
noetherian separated étale `Spec A`-schemes followed by `AlgebraicGeometry.affineSheafEquiv`. -/
def affineCohomologySheafEquiv :
    Sheaf (SmallEtale.topology B (Spec A) hS) AddCommGrpCat.{u} ≌
      Sheaf (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u} :=
  (SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS AddCommGrpCat.{u}).symm.trans
    (affineSheafEquiv B hS AddCommGrpCat.{u})

@[simp]
lemma affineCohomologySheafEquiv_functor_obj
    (F : Sheaf (SmallEtale.topology B (Spec A) hS) AddCommGrpCat.{u}) :
    (affineCohomologySheafEquiv B hS).functor.obj F =
      (affineSheafEquiv B hS AddCommGrpCat.{u}).functor.obj
        ((SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS AddCommGrpCat.{u}).inverse.obj
          F) :=
  rfl

/-- The functor of `affineSheafEquiv` is isomorphic to the restriction through Mathlib's small
étale site. -/
def affineSheafEquivFunctorIsoAux :
    (affineSheafEquivAux B hS AddCommGrpCat.{u}).functor ≅
      (affineSheafEquiv B hS AddCommGrpCat.{u}).functor :=
  Functor.fullyFaithfulCancelRight (sheafToPresheaf _ AddCommGrpCat.{u})
    (affineSheafEquivAuxFunctorIso B hS AddCommGrpCat.{u})

/-- `F ↦ F₀` is, up to isomorphism, the transport to Mathlib's small étale site followed by
restriction along `Scheme.AffineEtale.Spec`. -/
def affineCohomologySheafEquivFunctorIso :
    (affineCohomologySheafEquiv B hS).functor ≅
      (SmallEtale.sheafEquiv B (Spec A) hS AddCommGrpCat.{u}).functor ⋙
        (Scheme.AffineEtale.Spec (Spec A)).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Scheme.AffineEtale.topology (Spec A)) (Spec A).smallEtaleTopology :=
  Functor.isoWhiskerLeft _ (affineSheafEquivFunctorIsoAux B hS).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS AddCommGrpCat.{u}).counitIso
        (SmallEtale.sheafEquiv B (Spec A) hS AddCommGrpCat.{u}).functor ≪≫
        Functor.leftUnitor _) _

/-- Transport to Mathlib's small étale site carries the constant sheaf to the constant sheaf. -/
def constantSheafSmallEtaleSheafEquivIso :
    constantSheaf (SmallEtale.topology B (Spec A) hS) AddCommGrpCat.{u} ⋙
        (SmallEtale.sheafEquiv B (Spec A) hS AddCommGrpCat.{u}).functor ≅
      constantSheaf (Spec A).smallEtaleTopology AddCommGrpCat.{u} :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.DenseSubsite.constantSheafRestrictionIso.{u}
        (SmallEtale.topology B (Spec A) hS) (Spec A).smallEtaleTopology
        (SmallEtale.toEtaleSite B (Spec A) hS)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (SmallEtale.sheafEquiv B (Spec A) hS AddCommGrpCat.{u}).counitIso ≪≫
    Functor.rightUnitor _

/-- `F ↦ F₀` carries the constant sheaf to the constant sheaf. -/
def constantSheafAffineCohomologySheafEquivIso :
    constantSheaf (SmallEtale.topology B (Spec A) hS) AddCommGrpCat.{u} ⋙
        (affineCohomologySheafEquiv B hS).functor ≅
      constantSheaf (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft _ (affineCohomologySheafEquivFunctorIso B hS) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constantSheafSmallEtaleSheafEquivIso B hS) _ ≪≫
    Stacks.Cohomology.DenseSubsite.constantSheafRestrictionIso.{u}
      (Scheme.AffineEtale.topology (Spec A)) (Spec A).smallEtaleTopology
      (Scheme.AffineEtale.Spec (Spec A))

instance affineCohomologySheafEquiv_functor_additive :
    (affineCohomologySheafEquiv B hS).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance affineCohomologySheafEquiv_inverse_additive :
    (affineCohomologySheafEquiv B hS).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

section Cohomology

variable [HasExt.{w} (Sheaf (SmallEtale.topology B (Spec A) hS) AddCommGrpCat.{u})]
  [HasExt.{w} (Sheaf (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u})]

/-- The cohomology comparison along `F ↦ F₀`, as an isomorphism of functors. -/
def functorHAffineCohomologyIso (n : ℕ) :
    (affineCohomologySheafEquiv B hS).functor ⋙
        Sheaf.functorH.{w} (Scheme.AffineEtale.topology (Spec A)) n ≅
      Sheaf.functorH.{w} (SmallEtale.topology B (Spec A) hS) n :=
  Stacks.ExtAdjunction.functorHComparisonIso (constantSheafAffineCohomologySheafEquivIso B hS)
    (affineCohomologySheafEquiv B hS).toAdjunction n

/-- **The étale cohomology of `Spec A` is the étale cohomology of `A`.** For a noetherian ring `A`
and an abelian sheaf `F` on the small étale site of `Spec A`, `H^n(Spec A, F) ≅ H^n(A, F₀)`,
where `F₀` is the restriction of `F` to the étale category `Et(A)`. -/
@[weil "lem_fk102_affine_cohomology_comparison"]
def affineCohomologyAddEquiv (F : Sheaf (SmallEtale.topology B (Spec A) hS) AddCommGrpCat.{u})
    (n : ℕ) :
    F.H n ≃+ ((affineSheafEquiv B hS AddCommGrpCat.{u}).functor.obj
      ((SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS AddCommGrpCat.{u}).inverse.obj
        F)).H n :=
  ((functorHAffineCohomologyIso B hS n).app F).symm.addCommGroupIsoToAddEquiv

/-- **Naturality** of `AlgebraicGeometry.affineCohomologyAddEquiv` in the sheaf. -/
@[weil "lem_fk102_affine_cohomology_comparison"]
theorem affineCohomologyAddEquiv_map
    {F G : Sheaf (SmallEtale.topology B (Spec A) hS) AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    (x : F.H n) :
    affineCohomologyAddEquiv B hS G n (Sheaf.H.map φ n x) =
      Sheaf.H.map ((affineSheafEquiv B hS AddCommGrpCat.{u}).functor.map
        ((SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS
          AddCommGrpCat.{u}).inverse.map φ)) n
        (affineCohomologyAddEquiv B hS F n x) := by
  have := congrArg (fun f ↦ f.hom x)
    ((functorHAffineCohomologyIso B hS n).inv.naturality φ)
  exact this

/-- **The étale cohomology of `Spec A` is the étale cohomology of `A`**, for a sheaf `F` on the
étale category `Et(Spec A)`: `H^n(Spec A, F) ≅ H^n(A, F₀)`, where `H^n(Spec A, F)` is the
cohomology of the extension of `F` to the small étale site. -/
@[weil "lem_fk102_affine_cohomology_comparison"]
def etaleSheafAffineCohomologyAddEquiv (F : EtaleSheaf B (Spec A) hS AddCommGrpCat.{u})
    (n : ℕ) :
    ((SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS AddCommGrpCat.{u}).functor.obj
      F).H n ≃+ ((affineSheafEquiv B hS AddCommGrpCat.{u}).functor.obj F).H n :=
  (affineCohomologyAddEquiv B hS _ n).trans
    ((Sheaf.functorH.{w} (Scheme.AffineEtale.topology (Spec A)) n).mapIso
      ((affineSheafEquiv B hS AddCommGrpCat.{u}).functor.mapIso
        ((SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS
          AddCommGrpCat.{u}).unitIso.app F).symm)).addCommGroupIsoToAddEquiv

/-- **Naturality** of `AlgebraicGeometry.etaleSheafAffineCohomologyAddEquiv` in the sheaf. -/
@[weil "lem_fk102_affine_cohomology_comparison"]
theorem etaleSheafAffineCohomologyAddEquiv_map
    {F G : EtaleSheaf B (Spec A) hS AddCommGrpCat.{u}} (φ : F ⟶ G) (n : ℕ)
    (x : ((SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS
      AddCommGrpCat.{u}).functor.obj F).H n) :
    etaleSheafAffineCohomologyAddEquiv B hS G n
        (Sheaf.H.map ((SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS
          AddCommGrpCat.{u}).functor.map φ) n x) =
      Sheaf.H.map ((affineSheafEquiv B hS AddCommGrpCat.{u}).functor.map φ) n
        (etaleSheafAffineCohomologyAddEquiv B hS F n x) := by
  change Sheaf.H.map _ n (affineCohomologyAddEquiv B hS _ n (Sheaf.H.map _ n x)) =
    Sheaf.H.map _ n (Sheaf.H.map _ n (affineCohomologyAddEquiv B hS _ n x))
  rw [affineCohomologyAddEquiv_map, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
    Functor.mapIso_hom, Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  congr 3
  exact (SmallNoetherianSeparatedEtale.sheafEquiv B (Spec A) hS
    AddCommGrpCat.{u}).unitIso.inv.naturality φ

end Cohomology

end AlgebraicGeometry
