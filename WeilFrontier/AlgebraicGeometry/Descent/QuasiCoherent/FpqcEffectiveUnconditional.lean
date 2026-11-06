module

public import WeilFrontier.AlgebraicGeometry.Descent.QuasiCoherent.EffectiveDescentDatumSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import Weil.Attr

/-!
# Fpqc descent of quasi-coherent sheaves along a single morphism

Let `f : T ⟶ S` be a faithfully flat (flat and surjective) quasi-compact morphism of schemes.
Every descent datum `(𝒩, σ)` on a quasi-coherent `𝒪_T`-module with respect to `f` is effective:
there is a quasi-coherent `𝒪_S`-module `ℳ` with an isomorphism `φ : f^* ℳ ≅ 𝒩` compatible with
`σ` and the canonical descent datum of `ℳ`.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentDatum.isEffective_of_flat_of_surjective`: every
  quasi-coherent descent datum along a flat, surjective, quasi-compact morphism is effective.
* `AlgebraicGeometry.QuasicoherentDescentDatum.nonempty_descent_of_flat_of_surjective`: such a
  descent datum admits a descent `(ℳ, φ)`.

## Implementation notes

The single morphism `f` is the one-member family `PreZeroHypercover.singleton f`, which lies in
the fpqc precoverage by `AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage`; the result
is then the effectivity half of fpqc descent for quasi-coherent modules,
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`, for an arbitrary fpqc
covering family.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.5][FK88]
* [Grothendieck, *Technique de descente et théorèmes d'existence en géométrie algébrique I*,
  FGA Exp. 190, Thm. 1]
* [SGA 1, Exp. VIII, Thm. 1.1]
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace QuasicoherentDescentDatum

variable {T S : Scheme.{u}} (f : T ⟶ S) [Flat f] [Surjective f] [QuasiCompact f]

/-- **Fpqc descent of quasi-coherent sheaves.** For a faithfully flat (flat and surjective)
quasi-compact morphism of schemes `f : T ⟶ S`, every descent datum `(𝒩, σ)` on a
quasi-coherent `𝒪_T`-module with respect to `f` is effective. -/
@[weil "prop_fka3_fpqc_descent_quasi_coherent"]
theorem isEffective_of_flat_of_surjective (D : QuasicoherentDescentDatum f) : D.IsEffective :=
  QuasicoherentDescentData.isEffective_fpqcPrecoverage (PreZeroHypercover.singleton.{0} f)
    (by
      rw [PreZeroHypercover.presieve₀_singleton]
      exact f.singleton_mem_fpqcPrecoverage) D

/-- For a faithfully flat quasi-compact morphism `f : T ⟶ S`, every quasi-coherent descent
datum `(𝒩, σ)` with respect to `f` admits a descent `(ℳ, φ)`. -/
theorem nonempty_descent_of_flat_of_surjective (D : QuasicoherentDescentDatum f) :
    Nonempty (Descent D) :=
  (isEffective_iff_nonempty_descent D).1 (isEffective_of_flat_of_surjective f D)

end QuasicoherentDescentDatum

end AlgebraicGeometry
