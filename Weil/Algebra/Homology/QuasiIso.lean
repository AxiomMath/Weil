module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.QuasiIso
public import Weil.Attr

/-!
# Quasi-isomorphisms are invariant under homotopy

If `f` and `g` are homotopic morphisms of homological complexes, then `f` is a
quasi-isomorphism if and only if `g` is: homotopic morphisms induce equal maps
on homology in every degree (`Homotopy.homologyMap_eq`).

## Main results

* `Homotopy.quasiIso_iff`: for a homotopy `h : Homotopy f g`,
  `QuasiIso f ↔ QuasiIso g`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A.
-/

@[expose] public section

open CategoryTheory Limits

namespace Homotopy

variable {ι : Type*} {C : Type*} [Category C] [Preadditive C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

/-- Homotopic morphisms are quasi-isomorphisms in a given degree simultaneously. -/
lemma quasiIsoAt_iff (h : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt f i ↔ QuasiIsoAt g i := by
  rw [quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff_isIso_homologyMap, h.homologyMap_eq i]

/-- If `f` and `g` are homotopic morphisms of complexes, then `f` is a quasi-isomorphism
if and only if `g` is. -/
@[weil "lem_fka2_quasi_isomorphism_homotopy_invariant"]
lemma quasiIso_iff (h : Homotopy f g) [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso f ↔ QuasiIso g := by
  simp only [_root_.quasiIso_iff, h.quasiIsoAt_iff]

end Homotopy

end
