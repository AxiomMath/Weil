module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Weil.Attr

/-!
# Cohomology of a shifted cochain complex

For a cochain complex `K` indexed by `ℤ` and integers `i n m` with `n + i = m`, the shifted
complex `K⟦i⟧` has `(K⟦i⟧)^n = K^m` and differential `(-1)^i d_K`. A morphism and its negative
have the same kernel and image, so the `n`-th cohomology of `K⟦i⟧` is the `m`-th cohomology of
`K`, as subquotients of `K^m`, and for a morphism of complexes `f` the morphism
`H^n(f⟦i⟧)` is `H^m(f)`. In particular `H^0(K⟦i⟧) = H^i(K)`, naturally in `K`.

## Main definitions

* `CochainComplex.homologyShiftIso`: the natural isomorphism
  `shiftFunctor i ⋙ homologyFunctor n ≅ homologyFunctor m` for `n + i = m`.
* `CochainComplex.homologyZeroShiftIso`: the case `n = 0`, `H^0(K⟦i⟧) ≅ H^i(K)`.

## Main results

* `CochainComplex.liftCycles_shift_homologyπ_homologyShiftIso`: the isomorphism sends the class of
  a cycle `z` of `K⟦i⟧` in degree `n` to the class of the same cycle `z`, viewed in `K^m`:
  the two cohomology objects are the same subquotient of `K^m`.
* `CochainComplex.homologyMap_shift_comp_homologyShiftIso`: under these identifications
  `H^n(f⟦i⟧) = H^m(f)`.

## Implementation notes

Mathlib's homology is defined through short complexes, so cohomology objects are determined only
up to canonical isomorphism; the equality of subquotients is therefore stated as the compatibility
of the canonical isomorphism with the classes of cycles
(`liftCycles_shift_homologyπ_homologyShiftIso`), and the equality `H^n(T^i f) = H^{n+i}(f)` as its
naturality. The isomorphism is `HomologicalComplex.homologyFunctor`'s shift isomorphism
`CochainComplex.ShiftSequence.shiftIso`, with the indices written in the order `n + i = m`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Category ComplexShape

namespace CochainComplex

variable {C : Type*} [Category C] [Preadditive C] [CategoryWithHomology C]

/-- For `n + i = m`, the natural isomorphism `H^n(K⟦i⟧) ≅ H^m(K)` of functors on cochain
complexes. -/
@[weil "lem_fka2_h0_shift_eq_hi"]
noncomputable abbrev homologyShiftIso (i n m : ℤ) (h : n + i = m) :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) i ⋙
      HomologicalComplex.homologyFunctor C (up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (up ℤ) m :=
  (HomologicalComplex.homologyFunctor C (up ℤ) 0).shiftIso i n m (by omega)

/-- The isomorphism `homologyShiftIso` identifies the class of a cycle `z : A ⟶ (K⟦i⟧)^n` in
`H^n(K⟦i⟧)` with the class of the same morphism `z`, viewed as a cycle of `K` in degree `m`
through `(K⟦i⟧)^n = K^m`: the two cohomology objects are the same subquotient of `K^m`. -/
@[weil "lem_fka2_h0_shift_eq_hi"]
lemma liftCycles_shift_homologyπ_homologyShiftIso (K : CochainComplex C ℤ) {A : C}
    (i n m : ℤ) (h : n + i = m) (z : A ⟶ (K⟦i⟧).X n)
    (hz : z ≫ (K⟦i⟧).d n (n + 1) = 0)
    (hz' : (z ≫ (K.shiftFunctorObjXIso i n m (by omega)).hom) ≫ K.d m (m + 1) = 0) :
    (K⟦i⟧).liftCycles z (n + 1) (by simp) hz ≫ (K⟦i⟧).homologyπ n ≫
        (homologyShiftIso i n m h).hom.app K =
      K.liftCycles (z ≫ (K.shiftFunctorObjXIso i n m (by omega)).hom) (m + 1) (by simp) hz' ≫
        K.homologyπ m := by
  erw [liftCycles_shift_homologyπ_assoc K z (n + 1) (by simp) hz m (by omega) (m + 1)
    (by simp)]
  erw [Iso.inv_hom_id_app, comp_id]
  rfl

/-- For a morphism of cochain complexes `f`, under the identifications `homologyShiftIso`,
`H^n(f⟦i⟧) = H^m(f)` when `n + i = m`. -/
@[weil "lem_fka2_h0_shift_eq_hi"]
lemma homologyMap_shift_comp_homologyShiftIso {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (i n m : ℤ) (h : n + i = m) :
    HomologicalComplex.homologyMap (f⟦i⟧') n ≫ (homologyShiftIso i n m h).hom.app L =
      (homologyShiftIso i n m h).hom.app K ≫ HomologicalComplex.homologyMap f m :=
  (homologyShiftIso i n m h).hom.naturality f

/-- The natural isomorphism `H^0(K⟦i⟧) ≅ H^i(K)`. -/
@[weil "lem_fka2_h0_shift_eq_hi"]
noncomputable abbrev homologyZeroShiftIso (i : ℤ) :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) i ⋙
      HomologicalComplex.homologyFunctor C (up ℤ) 0 ≅
      HomologicalComplex.homologyFunctor C (up ℤ) i :=
  homologyShiftIso i 0 i (zero_add i)

end CochainComplex

end
