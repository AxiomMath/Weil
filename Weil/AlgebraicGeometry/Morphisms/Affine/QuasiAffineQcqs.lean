module

public import Weil.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import Weil.Attr

/-!
# Quasi-affine morphisms are quasi-compact and separated

A quasi-affine morphism of schemes `g : Y ⟶ T` is quasi-compact and separated, hence in
particular quasi-separated. Quasi-compactness and separatedness are the instances
`AlgebraicGeometry.quasiCompact_of_isQuasiAffineHom` and
`AlgebraicGeometry.isSeparated_of_isQuasiAffineHom` (Stacks Project, Tag 01SL).

## Main results

* `AlgebraicGeometry.IsQuasiAffineHom.quasiCompact_and_isSeparated`: a quasi-affine morphism is
  quasi-compact and separated.
* `AlgebraicGeometry.IsQuasiAffineHom.quasiSeparated`: a quasi-affine morphism is
  quasi-separated.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
* [Stacks Project, Tag 01SL](https://stacks.math.columbia.edu/tag/01SL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {Y T : Scheme.{u}}

/-- A quasi-affine morphism of schemes is quasi-compact and separated. -/
@[weil "lem_fka3_quasi_affine_qcqs"]
theorem IsQuasiAffineHom.quasiCompact_and_isSeparated (g : Y ⟶ T) [IsQuasiAffineHom g] :
    QuasiCompact g ∧ IsSeparated g :=
  ⟨inferInstance, inferInstance⟩

/-- A quasi-affine morphism of schemes is quasi-separated. -/
@[weil "lem_fka3_quasi_affine_qcqs"]
theorem IsQuasiAffineHom.quasiSeparated (g : Y ⟶ T) [IsQuasiAffineHom g] :
    QuasiSeparated g :=
  inferInstance

end AlgebraicGeometry

end
