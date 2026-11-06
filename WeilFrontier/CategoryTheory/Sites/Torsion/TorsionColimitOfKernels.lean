module

public import StacksFrontier.CategoryTheory.Sites.Torsion.TorsionColimitOfKernels
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import Weil.Attr

/-!
# A torsion étale sheaf is the colimit of its `n`-torsion subsheaves

Let `𝓖` be a torsion abelian sheaf on the small étale site of a scheme `S`, and for a positive
integer `n` let `𝓖[n] = ker (n : 𝓖 ⟶ 𝓖)` be the subsheaf of sections killed by `n`. For `n ∣ m`
the subsheaf `𝓖[n]` is contained in `𝓖[m]`; the positive integers ordered by divisibility form a
directed set; and the inclusions `𝓖[n] ⟶ 𝓖` exhibit `𝓖` as the colimit of the `𝓖[n]` over this
directed set.

## Main results

* `Stacks.Torsion.mono_torsionKernelsMap`: for `n ∣ m` the transition map `𝓖[n] ⟶ 𝓖[m]` is a
  monomorphism, compatible with the inclusions into `𝓖`.
* `AlgebraicGeometry.SmallEtale.isColimit_torsionKernelsCocone_of_isTorsionSheaf`: a torsion
  sheaf on the small étale site is the colimit of its `n`-torsion subsheaves, over the positive
  integers ordered by divisibility.

## Implementation notes

The positive integers are the submonoid `nonZeroDivisors ℕ`, and the divisibility order on them
is `Stacks.Torsion.DvdIndex (nonZeroDivisors ℕ)`, whose directedness is an instance. The system
`n ↦ 𝓖[n]` and its cocone of inclusions are `Stacks.Torsion.torsionKernels` and
`Stacks.Torsion.torsionKernelsCocone`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝓕 : Sheaf J AddCommGrpCat.{w})

/-- **`𝓕[n] ⊆ 𝓕[m]` for `n ∣ m`**: the transition map between the kernels of multiplication by
`n` and by `m` is a monomorphism. -/
@[weil "lem_fk104_torsion_sheaf_is_colimit_of_n_torsion"]
theorem mono_torsionKernelsMap {n m : ℕ} (h : n ∣ m) : Mono (torsionKernelsMap 𝓕 h) :=
  mono_of_mono_fac (torsionKernelsMap_ι 𝓕 h)

end Stacks.Torsion

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The positive integers, ordered by divisibility, form a directed set. -/
@[weil "lem_fk104_torsion_sheaf_is_colimit_of_n_torsion"]
theorem isDirected_dvdIndex_nonZeroDivisors :
    IsDirected (Stacks.Torsion.DvdIndex (nonZeroDivisors ℕ)) (· ≤ ·) :=
  inferInstance

/-- **A torsion sheaf is the colimit of its `n`-torsion subsheaves.** For a torsion abelian
sheaf `𝓖` on the small étale site of `S`, the inclusions `𝓖[n] ⟶ 𝓖` of the kernels of
multiplication by the positive integers `n` exhibit `𝓖` as the colimit of the `𝓖[n]`, over the
positive integers ordered by divisibility. -/
@[weil "lem_fk104_torsion_sheaf_is_colimit_of_n_torsion"]
theorem isColimit_torsionKernelsCocone_of_isTorsionSheaf
    (𝓖 : Sheaf (topology B S hS) AddCommGrpCat.{u}) (h𝓖 : IsTorsionSheaf B S hS 𝓖) :
    Nonempty (IsColimit (Stacks.Torsion.torsionKernelsCocone 𝓖 (nonZeroDivisors ℕ))) := by
  have : HasFilteredColimitsOfSize.{0, 0} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
    hasFilteredColimitsOfSize_shrink
  have : AB5OfSize.{0, 0} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
    AB5OfSize_shrink.{0, 0, u, u} _
  refine Stacks.Torsion.isColimitTorsionKernelsCocone 𝓖 _ (fun V x => ?_)
  obtain ⟨R, hR, hRx⟩ := h𝓖 V x
  refine ⟨R, hR, fun W f hf => ?_⟩
  obtain ⟨n, hn, hx⟩ := hRx W f hf
  exact ⟨n, mem_nonZeroDivisors_of_ne_zero hn.ne', hx⟩

end AlgebraicGeometry.SmallEtale

end
