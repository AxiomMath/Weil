module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Limits
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AssociatedModuleOnCoarserTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcSmallEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage

/-!
# The sheaf of rational functions on the étale site

Let `X` be a scheme with scheme of generic points `j_X : η_X ⟶ X`
(`AlgebraicGeometry.Scheme.genericPointsMorphism`). The *sheaf of rational functions* of `X`
is the direct image `𝓡_X = j_{X*}((𝒪_{η_X})_et)` of the étale structure sheaf of `η_X`: it is
the sheaf of commutative rings on the small étale site of `X` whose sections over an étale
`X`-scheme `U` are the global functions on the generic fibre `U ×_X η_X`,
`𝓡_X(U) = Γ(U ×_X η_X, 𝒪)`, the restriction maps being pull-back of functions along the base
changes of morphisms of étale `X`-schemes.

## Main definitions

* `AlgebraicGeometry.SmallEtale.rationalFunctionsPresheaf`: the presheaf of commutative rings
  `U ↦ Γ(U ×_X η_X, 𝒪)` on the small étale site `AlgebraicGeometry.SmallEtale B X hX`.
* `AlgebraicGeometry.SmallEtale.sheafRationalFunctions`: the sheaf of rational functions
  `𝓡_X`, a sheaf of commutative rings on the small étale site of `X`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.rationalFunctionsPresheaf`: its restriction
  to the étale category `Et(X)` of noetherian separated étale `X`-schemes.

## Main results

* `AlgebraicGeometry.SmallEtale.sheafRationalFunctions_obj`: `𝓡_X(U) = Γ(U ×_X η_X, 𝒪)`.
* `AlgebraicGeometry.SmallEtale.sheafRationalFunctions_map`: the restriction along
  `f : U ⟶ V` is pull-back of functions along `f ×_X η_X : U ×_X η_X ⟶ V ×_X η_X`.
* `AlgebraicGeometry.SmallEtale.isSheaf_rationalFunctionsPresheaf`: the sheaf property.
* `AlgebraicGeometry.SmallEtale.toEtaleSite_op_comp_rationalFunctionsPresheaf`: on Mathlib's
  small étale site `X.Etale`, the same presheaf is the direct image along `j_X`
  (precomposition with base change `Stacks.EtaleCohomology.smallEtaleBaseChange`) of the
  presheaf of global functions on the small étale site of `η_X`; `𝓡_X` is its restriction to
  `AlgebraicGeometry.SmallEtale B X hX`.

## Implementation notes

The scheme `η_X` need not lie below the size cutoff of the big étale site `B`, so the direct
image is not formed through a small étale site of `η_X` inside `B`; instead `𝓡_X` is defined by
its sections formula, which is the value of the direct image (the direct image of a presheaf is
precomposition with base change). The sheaf property is descent of functions: the functor
`U ↦ U ×_X η_X` from the small étale site of `X` to schemes over `η_X` is continuous for the
fpqc topology, and global functions form an fpqc sheaf of rings. No noetherian hypothesis is
needed for the construction.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

namespace SmallEtale

/-- The functor `U ↦ U ×_X η_X` from the small étale site of `X` to the schemes over the scheme
of generic points `η_X`. -/
abbrev genericFibreFunctor : SmallEtale B X hX ⥤ Over X.genericPointsScheme :=
  toOver B X hX ⋙ Over.pullback X.genericPointsMorphism

instance : (genericFibreFunctor B X hX).IsContinuous (topology B X hX)
    (Scheme.fpqcTopology.{u}.over X.genericPointsScheme) :=
  Functor.isContinuous_comp _ _ _ (Scheme.fpqcTopology.{u}.over X) _

/-- The presheaf of commutative rings `U ↦ Γ(U ×_X η_X, 𝒪)` on the small étale site of `X`,
with restriction maps given by pull-back of functions. -/
abbrev rationalFunctionsPresheaf : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u} :=
  (genericFibreFunctor B X hX ⋙ Over.forget _).op ⋙ Scheme.Γ

/-- The presheaf of rings underlying `rationalFunctionsPresheaf` is the structure presheaf of
the site `U ↦ U ×_X η_X` over `η_X`. -/
lemma rationalFunctionsPresheaf_comp_forget₂ :
    rationalFunctionsPresheaf B X hX ⋙ forget₂ CommRingCat RingCat =
      Stacks.Sites.structurePresheaf X.genericPointsScheme (genericFibreFunctor B X hX) :=
  rfl

/-- The presheaf `U ↦ Γ(U ×_X η_X, 𝒪)` is a sheaf of commutative rings on the small étale site
of `X` (descent of functions along the étale covering `U_i ×_X η_X ⟶ U ×_X η_X`). -/
theorem isSheaf_rationalFunctionsPresheaf :
    Presheaf.IsSheaf (topology B X hX) (rationalFunctionsPresheaf B X hX) := by
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat) ?_
  rw [rationalFunctionsPresheaf_comp_forget₂]
  exact Stacks.EtaleCohomology.isSheaf_structurePresheaf_of_isContinuous _ _ _

/-- **The sheaf of rational functions** `𝓡_X = j_{X*}((𝒪_{η_X})_et)` of a scheme `X`: the sheaf
of commutative rings on the small étale site of `X` whose sections over an étale `X`-scheme `U`
are the global functions on `U ×_X η_X`, where `j_X : η_X ⟶ X` is the scheme of generic
points, with restriction maps given by pull-back of functions. -/
@[weil "def_fk105_sheaf_rational_functions"]
def sheafRationalFunctions : Sheaf (topology B X hX) CommRingCat.{u} :=
  ⟨rationalFunctionsPresheaf B X hX, isSheaf_rationalFunctionsPresheaf B X hX⟩

/-- The sections of `𝓡_X` over an étale `X`-scheme `u : U ⟶ X` are the global functions on the
generic fibre `U ×_X η_X`. -/
@[weil "def_fk105_sheaf_rational_functions"]
lemma sheafRationalFunctions_obj (U : SmallEtale B X hX) :
    (sheafRationalFunctions B X hX).obj.obj (op U) =
      Γ(pullback ((toOver B X hX).obj U).hom X.genericPointsMorphism, ⊤) :=
  rfl

/-- The restriction map of `𝓡_X` along a morphism `f : U ⟶ V` of étale `X`-schemes is the
pull-back of functions along `f ×_X η_X : U ×_X η_X ⟶ V ×_X η_X`. -/
@[weil "def_fk105_sheaf_rational_functions"]
lemma sheafRationalFunctions_map {U V : SmallEtale B X hX} (f : U ⟶ V) :
    (sheafRationalFunctions B X hX).obj.map f.op =
      CommRingCat.ofHom (pullback.map ((toOver B X hX).obj U).hom X.genericPointsMorphism
        ((toOver B X hX).obj V).hom X.genericPointsMorphism ((toOver B X hX).map f).left
        (𝟙 _) (𝟙 _) (by simpa using (Over.w ((toOver B X hX).map f)).symm)
        (by simp)).appTop.hom :=
  rfl

/-- On Mathlib's small étale site `X.Etale`, the presheaf `U ↦ Γ(U ×_X η_X, 𝒪)` is the direct
image along `j_X : η_X ⟶ X` of the presheaf of global functions on the small étale site of
`η_X`; the sheaf of rational functions is its restriction to the small étale site
`AlgebraicGeometry.SmallEtale B X hX`. -/
lemma toEtaleSite_op_comp_rationalFunctionsPresheaf :
    (toEtaleSite B X hX).op ⋙
        (Stacks.EtaleCohomology.smallEtaleBaseChange X.genericPointsMorphism).op ⋙
          (Scheme.Etale.forget _ ⋙ Over.forget _).op ⋙ Scheme.Γ =
      rationalFunctionsPresheaf B X hX :=
  rfl

end SmallEtale

namespace SmallNoetherianSeparatedEtale

/-- **The sheaf of rational functions on `Et(X)`**: the restriction of
`AlgebraicGeometry.SmallEtale.sheafRationalFunctions` to the étale category of noetherian
separated étale `X`-schemes, `U ↦ Γ(U ×_X η_X, 𝒪)`. -/
@[weil "def_fk105_sheaf_rational_functions"]
abbrev rationalFunctionsPresheaf : EtalePresheaf B X hX CommRingCat.{u} :=
  (inclusion B X hX).op ⋙ (SmallEtale.sheafRationalFunctions B X hX).obj

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry
