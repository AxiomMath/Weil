module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekPresentation

/-!
# Constructible abelian étale sheaves are killed by a positive integer

Let `X` be a quasi-compact and quasi-separated scheme (for instance a Noetherian one) and let `F`
be a constructible sheaf of abelian groups on the small étale site of `X`. Then there is an
integer `n ≥ 1` with `n • s = 0` for every étale `U ⟶ X` and every section `s ∈ F(U)`: the sheaf
`F` is a sheaf of `ℤ/nℤ`-modules.

## Main results

* `AlgebraicGeometry.exists_nsmul_eq_zero_of_isConstructibleAbelianSheaf`: a constructible abelian
  sheaf on the small étale site of a quasi-compact quasi-separated scheme is annihilated, section
  by section, by a positive integer.

## Implementation notes

The statement is derived from
`AlgebraicGeometry.exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf`, which states
the annihilation as `N • 𝟙 F = 0` in the category of sheaves. That proof goes through
a global constructible stratification and the finiteness of geometric stalks, rather than through
an epimorphism from a representable sheaf as in [FreitagKiehl]; the conclusion is the same.

The hypothesis is quasi-compactness and quasi-separatedness of `X` rather than the Noetherian
hypothesis of [FreitagKiehl]; a Noetherian scheme satisfies both
(`AlgebraicGeometry.exists_nsmul_eq_zero_of_isConstructibleAbelianSheaf_of_noetherianSpace`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 09YT](https://stacks.math.columbia.edu/tag/09YT)
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **A constructible abelian étale sheaf is killed by a positive integer.** If `X` is
quasi-compact and quasi-separated and `F` is a constructible sheaf of abelian groups on the small
étale site of `X`, there is an integer `n ≥ 1` with `n • s = 0` for every object `U` of the site
and every section `s ∈ F(U)`. -/
@[weil "lem_fk104_constructible_abelian_killed_by_integer"]
theorem exists_nsmul_eq_zero_of_isConstructibleAbelianSheaf
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    ∃ n : ℕ, 0 < n ∧ ∀ (U : (SmallEtale B X.obj X.property)ᵒᵖ) (s : F.obj.obj U), n • s = 0 := by
  obtain ⟨n, hn, h⟩ := exists_nsmul_id_eq_zero_of_isConstructibleAbelianSheaf B X
    ‹_› ‹_› F hF
  refine ⟨n, hn, fun U s => ?_⟩
  have := congrArg (fun f : F ⟶ F => (f.hom.app U) s) h
  exact this

/-- **The Noetherian case.** A constructible sheaf of abelian groups on the small étale site of a
scheme with Noetherian underlying space is killed by a positive integer. -/
theorem exists_nsmul_eq_zero_of_isConstructibleAbelianSheaf_of_noetherianSpace
    [TopologicalSpace.NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    ∃ n : ℕ, 0 < n ∧ ∀ (U : (SmallEtale B X.obj X.property)ᵒᵖ) (s : F.obj.obj U), n • s = 0 :=
  exists_nsmul_eq_zero_of_isConstructibleAbelianSheaf B X F hF

end AlgebraicGeometry

end
