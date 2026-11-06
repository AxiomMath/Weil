module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeMorphism
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperComplete
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PicardRestrictionPullback
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Lifting invertible modules along the adic reductions of a scheme

Let `A` be a ring, `I ⊆ A` an ideal and `X` a scheme over `Spec A`. Write
`X_n = X ×_{Spec A} Spec (A / I ^ (n + 1))` for the adic reductions of `X`, so that `X_0` is the
fibre over `V(I)`. The canonical map `X_n ⟶ X_{n+1}` is the base change of
`Spec (A / I ^ (n + 1)) ⟶ Spec (A / I ^ (n + 2))`, whose ideal `I ^ (n + 1) / I ^ (n + 2)` has
square zero, so it is a first-order thickening. The exact sequence
`Pic(X_{n+1}) → Pic(X_n) → H²(X_n, ℐ)` of a first-order thickening and Grothendieck's vanishing
theorem then show: if the underlying space of `X_0` is Noetherian of dimension at most one, every
invertible `𝒪_{X_n}`-module is the restriction of an invertible `𝒪_{X_{n+1}}`-module.

## Main results

* `AlgebraicGeometry.isFirstOrderThickening_adicBaseChangeSucc`: the map `X_n ⟶ X_{n+1}` is a
  first-order thickening, being the base change of
  `AlgebraicGeometry.isFirstOrderThickening_adicThickeningSucc` along the cartesian square
  `AlgebraicGeometry.isPullback_adicBaseChangeSucc`.
* `AlgebraicGeometry.surjective_schemePullbackClass_adicBaseChangeSucc`: restriction
  `Pic(X_{n+1}) → Pic(X_n)` is surjective when `X_0` is a Noetherian space of dimension `≤ 1`.
* `AlgebraicGeometry.exists_isInvertible_pullback_adicBaseChangeSucc_iso`: the same statement for
  invertible modules, over a Noetherian local ring `A` with `I` its maximal ideal and `X` of
  finite type over `A`, the special fibre having dimension at most one.

## Implementation notes

The reduction `X ⊗_A A / 𝔪 ^ m` (`m ≥ 1`) is `AlgebraicGeometry.adicBaseChange A 𝔪 f (m - 1)`,
so the index is shifted by one relative to the source. The source's hypotheses that `A` be
strictly Henselian and `X` projective over `A` are not used: only that the special fibre is a
Noetherian scheme of dimension at most one, which holds as soon as `X` is of finite type over the
Noetherian ring `A`.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.1, proof, p. 64]
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.Thickenings (IsFirstOrderThickening)

attribute [local implicit_reducible] TopCat.Sheaf

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

section Thickening

variable {A : Type u} [CommRing A] (I : Ideal A)

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The canonical map `X_n ⟶ X_{n+1}` between consecutive adic reductions is a first-order
thickening. -/
theorem isFirstOrderThickening_adicBaseChangeSucc (n : ℕ) :
    IsFirstOrderThickening (adicBaseChangeSucc A I f n) :=
  Stacks.Thickenings.isFirstOrderThickening_of_isPullback (isPullback_adicBaseChangeSucc A I f n)
    (isFirstOrderThickening_adicThickeningSucc A I n)

/-- The underlying map of a first-order thickening is a homeomorphism. -/
theorem isHomeomorph_of_isFirstOrderThickening {Y Y' : Scheme.{u}} {i : Y ⟶ Y'}
    (hi : IsFirstOrderThickening i) : IsHomeomorph i := by
  have h := hi.isThickening
  have := h.1
  exact isHomeomorph_iff_isEmbedding_surjective.2 ⟨i.isClosedEmbedding.isEmbedding, h.2⟩

/-- Every adic reduction `X_n` has the underlying space of `X_0` up to homeomorphism; in
particular it is Noetherian, of the same dimension, when `X_0` is. -/
theorem noetherianSpace_adicBaseChange_and_topologicalKrullDim_eq
    [NoetherianSpace (adicBaseChange A I f 0)] (n : ℕ) :
    NoetherianSpace (adicBaseChange A I f n) ∧
      topologicalKrullDim (adicBaseChange A I f n) =
        topologicalKrullDim (adicBaseChange A I f 0) := by
  induction n with
  | zero => exact ⟨inferInstance, rfl⟩
  | succ n ih =>
    obtain ⟨hN, hd⟩ := ih
    have hh := isHomeomorph_of_isFirstOrderThickening
      (isFirstOrderThickening_adicBaseChangeSucc I f n)
    exact ⟨noetherianSpace_of_surjective _ hh.continuous hh.surjective,
      (hh.topologicalKrullDim_eq).symm.trans hd⟩

/-- **Lifting Picard classes along the adic reductions.** If the underlying space of
`X_0 = X ×_{Spec A} Spec (A / I)` is Noetherian of dimension at most one, restriction
`Pic(X_{n+1}) → Pic(X_n)` is surjective for every `n`. -/
theorem surjective_schemePullbackClass_adicBaseChangeSucc
    [NoetherianSpace (adicBaseChange A I f 0)]
    (hdim : topologicalKrullDim (adicBaseChange A I f 0) ≤ 1) (n : ℕ) :
    Function.Surjective (Stacks.Picard.schemePullbackClass (adicBaseChangeSucc A I f n)) := by
  obtain ⟨hN, hd⟩ := noetherianSpace_adicBaseChange_and_topologicalKrullDim_eq I f n
  refine Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_of_forall_eq_zero _
    (isFirstOrderThickening_adicBaseChangeSucc I f n) fun x => ?_
  have := Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
    (X := adicBaseChange A I f n) (d := 1) (p := 2) (hd.trans_le hdim) (by norm_num)
    (Stacks.Thickenings.idealAddSheafOnSub (adicBaseChangeSucc A I f n))
  exact Subsingleton.elim _ _

end Thickening

section Local

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f]

/-- For `X` of finite type over a Noetherian ring `A`, the fibre `X_0` over `V(I)` is a
Noetherian space. -/
theorem noetherianSpace_adicBaseChange_zero : NoetherianSpace (adicBaseChange A I f 0) := by
  have : IsLocallyNoetherian (adicBaseChange A I f 0) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (adicThickeningι A I 0))
  have : CompactSpace (adicBaseChange A I f 0) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (adicThickeningι A I 0))
  have : IsNoetherian (adicBaseChange A I f 0) := ⟨⟩
  infer_instance

/-- **Invertible modules lift along the infinitesimal neighbourhoods of the special fibre.**
Let `A` be a Noetherian local ring with maximal ideal `𝔪`, `X` a scheme of finite type over `A`
whose special fibre `X_s = X ⊗_A A / 𝔪` has dimension at most one, and `n ≥ 0`. Then every
invertible module on `X_{n+1} = X ⊗_A A / 𝔪 ^ (n + 1)` is isomorphic to the restriction of an
invertible module on `X_{n+2} = X ⊗_A A / 𝔪 ^ (n + 2)`. -/
@[weil "lem_fk106_pic_thickening_surjective"]
theorem exists_isInvertible_pullback_adicBaseChangeSucc_iso [IsLocalRing A]
    (hdim : topologicalKrullDim (adicBaseChange A (IsLocalRing.maximalIdeal A) f 0) ≤ 1)
    (n : ℕ) (M : (adicBaseChange A (IsLocalRing.maximalIdeal A) f n).Modules)
    (hM : Stacks.SheafOfModules.IsInvertible
      (adicBaseChange A (IsLocalRing.maximalIdeal A) f n).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf
        (adicBaseChange A (IsLocalRing.maximalIdeal A) f n).toRingedSpace) M) :
    ∃ (L : (adicBaseChange A (IsLocalRing.maximalIdeal A) f (n + 1)).Modules)
      (_ : Stacks.SheafOfModules.IsInvertible
        (adicBaseChange A (IsLocalRing.maximalIdeal A) f (n + 1)).toRingedSpace.presheaf
        (Stacks.RingedSpace.structureIsSheaf
          (adicBaseChange A (IsLocalRing.maximalIdeal A) f (n + 1)).toRingedSpace) L),
      Nonempty ((Scheme.Modules.pullback
        (adicBaseChangeSucc A (IsLocalRing.maximalIdeal A) f n)).obj L ≅ M) := by
  have := noetherianSpace_adicBaseChange_zero (IsLocalRing.maximalIdeal A) f
  obtain ⟨x, hx⟩ := surjective_schemePullbackClass_adicBaseChangeSucc
    (IsLocalRing.maximalIdeal A) f hdim n
    (Stacks.SheafOfModules.picardClass _ _ M hM)
  refine ⟨(Stacks.Picard.picardRepresentative _ x).obj,
    (Stacks.Picard.picardRepresentative _ x).property, ?_⟩
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 hx

end Local

end AlgebraicGeometry

end
