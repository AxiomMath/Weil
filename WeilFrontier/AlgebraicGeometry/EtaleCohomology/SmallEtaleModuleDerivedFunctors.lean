module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization

/-!
# The direct image of étale sheaves of `Λ`-modules is additive and left exact

Let `f : X ⟶ Y` be a morphism of schemes and `Λ` a ring. For a sheaf `𝓕` of `Λ`-modules on the
small étale site of `X`, the direct image `f_* 𝓕`, with sections `(f_* 𝓕)(U) = 𝓕(X ×_Y U)`, is a
sheaf of `Λ`-modules on the small étale site of `Y`; the resulting functor
`f_* : Sh(X, Λ) ⥤ Sh(Y, Λ)` is additive and left exact. In fact it preserves every limit that
exists in the coefficient category, since limits of sheaves are computed sectionwise.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImage_additive_preservesFiniteLimits`: the direct
  image `Stacks.EtaleCohomology.etaleModuleDirectImage` of sheaves of `Λ`-modules on the small
  étale sites is additive and left exact.
* `AlgebraicGeometry.BigEtaleSite.smallPushforward_additive_preservesFiniteLimits`: the same
  for the direct image `AlgebraicGeometry.BigEtaleSite.smallPushforward` between the small
  étale sites of a big étale site.

## Implementation notes

A sheaf of `Λ`-modules is a sheaf with values in `ModuleCat Λ`, so the `Λ`-module structure
of `f_* 𝓕` and the `Λ`-linearity of `f_* φ` are part of the data of the direct image
functor; the endomorphism `λ_{f_* 𝓕}` is `f_* (λ_𝓕)`, as both act on the sections
`𝓕(X ×_Y U)` by `λ`. Left exactness is
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous`, proved directly in
`ModuleCat Λ` rather than through the underlying abelian sheaves.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II][FK]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u r v₁

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- **Direct image of étale sheaves of `Λ`-modules is additive and left exact.** For a
morphism of schemes `f : X ⟶ Y`, the direct image `f_*` from sheaves of `Λ`-modules on the
small étale site of `X` to those on the small étale site of `Y` is an additive functor
preserving finite limits. -/
@[weil "lem_fka2_lambda_direct_image_left_exact"]
theorem etaleModuleDirectImage_additive_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleDirectImage.{u, r} Λ f).Additive ∧
      PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ f) :=
  ⟨inferInstance, inferInstance⟩

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- **Direct image of étale sheaves of `Λ`-modules is additive and left exact**, on the small
étale sites of a big étale site: for a morphism `f : T ⟶ S`, the direct image
`smallPushforward` of sheaves of `Λ`-modules is additive and preserves finite limits. -/
@[weil "lem_fka2_lambda_direct_image_left_exact"]
theorem smallPushforward_additive_preservesFiniteLimits {S T : B.Scheme} (f : T ⟶ S) :
    (B.smallPushforward f (ModuleCat.{v₁} Λ)).Additive ∧
      PreservesFiniteLimits (B.smallPushforward f (ModuleCat.{v₁} Λ)) :=
  ⟨{ map_add := rfl }, inferInstance⟩

end AlgebraicGeometry.BigEtaleSite
