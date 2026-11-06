module

public import WeilFrontier.AlgebraicGeometry.Morphisms.QuasiFinite
public import Weil.Attr

/-!
# Étale morphisms are quasi-finite

An étale morphism of schemes `f : X ⟶ Y` with noetherian source is quasi-finite: it is locally
of finite type, quasi-compact, and each fibre `f ⁻¹' {y}` is finite. In Mathlib's language,
`f` is locally of finite type, locally quasi-finite and quasi-compact.

## Main results

- `AlgebraicGeometry.Etale.locallyOfFiniteType_and_locallyQuasiFinite_and_quasiCompact`: an
  étale morphism with noetherian source is locally of finite type, locally quasi-finite and
  quasi-compact.
- `AlgebraicGeometry.Etale.locallyOfFiniteType_and_quasiCompact_and_finite_preimage_singleton`:
  the same in fibrewise form, as Freitag–Kiehl define quasi-finiteness.

## Implementation notes

Freitag–Kiehl work with noetherian schemes throughout, which is where quasi-compactness of `f`
comes from; here only the underlying space of the source is assumed noetherian. The
proof does not go through affine charts and fibre algebras: an étale morphism is unramified,
hence locally quasi-finite (Stacks, Tag 03WS), and a morphism with noetherian source is
quasi-compact.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FK88]
* [Stacks Project, Tag 03WS](https://stacks.math.columbia.edu/tag/03WS)
-/

@[expose] public section

open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- An étale morphism with noetherian source is quasi-finite: locally of finite type, locally
quasi-finite and quasi-compact. -/
@[weil "lem_fk102_etale_morphism_quasi_finite"]
theorem Etale.locallyOfFiniteType_and_locallyQuasiFinite_and_quasiCompact [Etale f]
    [NoetherianSpace X] :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ∧ QuasiCompact f :=
  ⟨(locallyQuasiFinite_of_etale f).1, (locallyQuasiFinite_of_etale f).2, inferInstance⟩

/-- An étale morphism with noetherian source is locally of finite type, quasi-compact and has
finite fibres; this is quasi-finiteness in the fibrewise form. -/
@[weil "lem_fk102_etale_morphism_quasi_finite"]
theorem Etale.locallyOfFiniteType_and_quasiCompact_and_finite_preimage_singleton [Etale f]
    [NoetherianSpace X] :
    LocallyOfFiniteType f ∧ QuasiCompact f ∧ ∀ y, (f ⁻¹' {y}).Finite :=
  (locallyOfFiniteType_and_locallyQuasiFinite_and_quasiCompact_iff f).mp
    (Etale.locallyOfFiniteType_and_locallyQuasiFinite_and_quasiCompact f)

end AlgebraicGeometry

end
