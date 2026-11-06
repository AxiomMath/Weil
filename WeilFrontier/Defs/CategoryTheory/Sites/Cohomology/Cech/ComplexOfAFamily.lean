module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstCocycles

/-!
# The Čech complex of a covering in the étale category

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes, let `U` be an
object of `Et(S)`, let `𝔘 = (Uᵢ → U)_{i ∈ I}` be a family of morphisms of `Et(S)` with target
`U`, and let `F` be a presheaf of abelian groups on `Et(S)`. For a tuple
`ν = (ν₀, …, ν_p) ∈ I^{p+1}` the iterated fibre product `U_ν = U_{ν₀} ×_U ⋯ ×_U U_{ν_p}` is
again an object of `Et(S)`, and the *Čech complex* `Č^•(𝔘, F)` has degree-`p` term
`∏_{ν ∈ I^{p+1}} F(U_ν)` and differential
`(d^p s)_{ν₀ … ν_{p+1}} = ∑_j (-1)^j ∂_j^* (s_{ν₀ … ν̂_j … ν_{p+1}})`, where
`∂_j : U_ν ⟶ U_{ν₀ … ν̂_j … ν_{p+1}}` is the projection omitting the `j`-th factor.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplex`: the Čech complex
  `Č^•(𝔘, F)` of a presheaf `F` on `Et(S)` along a family `𝔘` with fixed target.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isNoetherianSeparated_pullback`: a fibre
  product, in the small étale category, of noetherian separated objects is noetherian and
  separated.
* The instance `HasPullbacks (SmallNoetherianSeparatedEtale B S hS)`: `Et(S)` has fibre
  products, computed in the small étale category; consequently every slice `Over U` has
  finite limits, so all the iterated fibre products `U_ν` exist.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplex_X`: the degree-`p` term is the
  product of the sections of `F` over the iterated fibre products.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplex_d_apply`: the alternating-sum
  formula for the differential.

## Implementation notes

The construction is `Stacks.CechSite.cechComplex` applied to the category `Et(S)`: a family of
morphisms with target `U` is a `CategoryTheory.PreZeroHypercover U`, and the iterated fibre
product `U_ν` is the product, in the slice `Over U`, of the objects `Over.mk (E.f (ν j))`.
The complex is indexed by `ℕ`, which encodes the convention `Č^p = 0`, `d^p = 0` for `p < 0`.
The definition needs neither that the index set is finite nor that the family is jointly
surjective, so these hypotheses of the source are not imposed; it is stated for presheaves
with values in any preadditive category with products, abelian groups being the case
`AddCommGrpCat`. The face projection `∂_j` is `Stacks.CechSite.faceProjection`, indexed by
`Fin.succAbove j`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a w v' u' u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

/-- A scheme admitting a quasi-compact morphism locally of finite type to a noetherian scheme is
noetherian. -/
lemma isNoetherian_of_hom {P V : Scheme.{u}} (p : P ⟶ V) [LocallyOfFiniteType p]
    [QuasiCompact p] [IsNoetherian V] : IsNoetherian P := by
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace P :=
    ⟨by simpa using (quasiCompact_iff p).mp ‹_› _ isOpen_univ isCompact_univ⟩
  exact ⟨⟩

/-- A scheme admitting a separated morphism to a separated scheme is separated. -/
lemma isSeparated_of_hom {P V : Scheme.{u}} (p : P ⟶ V) [IsSeparated p] [V.IsSeparated] :
    P.IsSeparated := by
  refine ⟨?_⟩
  rw [show terminal.from P = p ≫ terminal.from V from terminal.hom_ext _ _]
  infer_instance

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fibre product, in the small étale category of `S`, of noetherian separated objects is
noetherian and separated. -/
lemma isNoetherianSeparated_pullback {V V' W : SmallEtale B S hS} (f : V ⟶ W) (g : V' ⟶ W)
    (hV : SmallEtale.IsNoetherianSeparated B S hS V)
    (hV' : SmallEtale.IsNoetherianSeparated B S hS V')
    (hW : SmallEtale.IsNoetherianSeparated B S hS W) :
    SmallEtale.IsNoetherianSeparated B S hS (pullback f g) := by
  obtain ⟨_, _⟩ := hV
  obtain ⟨_, _⟩ := hV'
  obtain ⟨_, _⟩ := hW
  let T := SmallEtale.toScheme B S hS
  have h : IsPullback (T.map (pullback.fst f g)) (T.map (pullback.snd f g)) (T.map f)
      (T.map g) :=
    (IsPullback.of_hasPullback f g).map T
  have : QuasiCompact (T.map (pullback.fst f g)) :=
    MorphismProperty.of_isPullback h.flip inferInstance
  have : IsSeparated (T.map (pullback.fst f g)) :=
    MorphismProperty.of_isPullback h.flip inferInstance
  exact ⟨isNoetherian_of_hom (T.map (pullback.fst f g)),
    isSeparated_of_hom (T.map (pullback.fst f g))⟩

/-- The inclusion of `Et(S)` into the small étale category creates fibre products. -/
noncomputable instance createsPullbacksInclusion :
    CreatesLimitsOfShape WalkingCospan (inclusion B S hS) where
  CreatesLimit := fun {F} => by
    let D := F ⋙ inclusion B S hS
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    exact createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _))
      (isNoetherianSeparated_pullback B S hS _ _ (F.obj .left).property
        (F.obj .right).property (F.obj .one).property)

/-- **Fibre products in `Et(S)`.** The étale category of noetherian separated étale
`S`-schemes has fibre products. -/
instance hasPullbacks_of_createsPullbacks :
    HasPullbacks (SmallNoetherianSeparatedEtale B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (inclusion B S hS)

/-- Every slice of `Et(S)` has finite limits; in particular all finite iterated fibre products
over an object exist. -/
instance hasFiniteLimits_over (U : SmallNoetherianSeparatedEtale B S hS) :
    HasFiniteLimits (Over U) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

variable {B S hS}

section CechComplex

variable {U : SmallNoetherianSeparatedEtale B S hS} (E : PreZeroHypercover.{w} U)

/-- **The Čech complex `Č^•(𝔘, F)`.** For a family `E = (Uᵢ ⟶ U)_{i}` of morphisms of `Et(S)`
with target `U` and a presheaf `F` on `Et(S)` (with values in abelian groups or, more generally,
in a preadditive category with products), the cochain complex with degree-`p` term
`∏_{ν : Fin (p + 1) → I} F(U_{ν₀} ×_U ⋯ ×_U U_{ν_p})` and the alternating-sum differential. -/
@[weil "def_fk102_cech_complex_covering"]
noncomputable abbrev cechComplex {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
    [Preadditive A] (F : EtalePresheaf B S hS A) : CochainComplex A ℕ :=
  Stacks.CechSite.cechComplex E F

/-- The degree-`p` term of the Čech complex is the product, over all `(p+1)`-tuples `ν` of
indices, of the sections of `F` over the iterated fibre product `U_{ν₀} ×_U ⋯ ×_U U_{ν_p}`. -/
lemma cechComplex_X {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    (F : EtalePresheaf B S hS A) (p : ℕ) :
    (cechComplex E F).X p =
      ∏ᶜ (fun ν : Fin (p + 1) → E.I₀ ↦
        F.obj (op ((∏ᶜ (fun j ↦ Over.mk (E.f (ν j))) : Over U).left))) :=
  rfl

/-- **The Čech differential.** For a presheaf of abelian groups `F`, the component at a tuple
`ν = (ν₀, …, ν_{p+1})` of `d^p s` is `∑_j (-1)^j ∂_j^* (s_{ν₀ … ν̂_j … ν_{p+1}})`, where
`∂_j` is the projection omitting the `j`-th factor. -/
@[weil "def_fk102_cech_complex_covering"]
lemma cechComplex_d_apply [HasProducts.{w} AddCommGrpCat.{a}]
    (F : EtalePresheaf B S hS AddCommGrpCat.{a}) (p : ℕ) (s : (cechComplex E F).X p)
    (ν : Fin (p + 2) → E.I₀) :
    Pi.π (Stacks.CechSite.cochainFactor E F (p + 1)) ν ((cechComplex E F).d p (p + 1) s) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        F.map (Stacks.CechSite.faceProjection E ν j).left.op
          (Pi.π (Stacks.CechSite.cochainFactor E F p) (fun b ↦ ν (j.succAbove b)) s) :=
  Stacks.CechSite.pi_π_differential_apply E F p s ν

end CechComplex

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
