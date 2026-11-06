module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import WeilFrontier.Defs.AlgebraicGeometry.ResidueField
public import Weil.Attr

/-!
# The underlying point of an algebraic point is closed

Let `X` be a scheme over a field `κ` and let `k` be an algebraic extension of `κ` (for instance
an algebraic closure). For every `κ`-morphism `a : Spec k ⟶ X`, the underlying point `|a|` is a
closed point of `X`. Indeed `a` induces an embedding `κ(|a|) ⟶ k` compatible with the maps from
`κ`, so `κ(|a|)` is algebraic over `κ`, and a point whose residue field is algebraic over that of
its image is closed as soon as its image is closed; every point of `Spec κ` is closed.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isClosed_singleton_underlyingPoint`: for a field `κ`, a
  morphism `f : X ⟶ Spec κ`, an algebraic extension `k` of `κ` and a morphism
  `a : Spec k ⟶ X` over `Spec κ`, the point `|a|` is closed in `X`.

## Implementation notes

The source assumes `X` of finite type over `κ` and `k` an algebraic closure of `κ`, and deduces
closedness from finiteness of `κ(|a|)` over `κ`. Neither hypothesis is needed: algebraicity of
`κ(|a|)` over `κ` already gives closedness, for any scheme over `κ` and any algebraic extension
`k` of `κ`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, II.4][FreitagKiehl]
* [Stacks Project, Tag 01TE](https://stacks.math.columbia.edu/tag/01TE)
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {κ k : Type u} [Field κ] [Field k] [Algebra κ k] {X : Scheme.{u}}

/-- A point `x` of a scheme `X` over `Spec κ` whose residue field admits an embedding into an
algebraic extension `k` of `κ`, compatible with the maps from `κ`, has a residue field
algebraic over the residue field of its image in `Spec κ`. -/
private lemma isAlgebraic_residueField_of_hom [Algebra.IsAlgebraic κ k]
    (f : X ⟶ Spec (.of κ)) (x : X) (φ : X.residueField x ⟶ .of k)
    (ha : (Spec.map φ ≫ X.fromSpecResidueField x) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap κ k))) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic ((Spec (.of κ)).residueField (f x)) (X.residueField x) := by
  obtain ⟨ι, hι⟩ : ∃ ι : CommRingCat.of κ ⟶ (Spec (.of κ)).residueField (f x),
      Spec.map ι = (Spec (.of κ)).fromSpecResidueField (f x) := by
    have : (PrimeSpectrum.asIdeal (R := κ) (f x)).IsPrime := PrimeSpectrum.isPrime _
    exact ⟨_, (Spec.map_comp _ _).trans
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of κ) (f x))⟩
  have hcomp : ι ≫ f.residueFieldMap x ≫ φ = CommRingCat.ofHom (algebraMap κ k) := by
    apply Spec.map_injective
    rw [← ha, Category.assoc, ← SpecMap_residueFieldMap_fromSpecResidueField, ← hι,
      Spec.map_comp, Spec.map_comp, Category.assoc]
  let _ : Algebra κ ((Spec (.of κ)).residueField (f x)) := ι.hom.toAlgebra
  let _ : Algebra ((Spec (.of κ)).residueField (f x)) k :=
    (f.residueFieldMap x ≫ φ).hom.toAlgebra
  let _ : Algebra (X.residueField x) k := φ.hom.toAlgebra
  let _ : Algebra ((Spec (.of κ)).residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower κ ((Spec (.of κ)).residueField (f x)) k :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hcomp).symm
  have : IsScalarTower ((Spec (.of κ)).residueField (f x)) (X.residueField x) k :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic ((Spec (.of κ)).residueField (f x)) k :=
    Algebra.IsAlgebraic.tower_top (K := κ) _
  exact Algebra.IsAlgebraic.tower_bot_of_injective (A := k) φ.hom.injective

/-- **The underlying point of an algebraic point is closed.** Let `X` be a scheme over a field
`κ` via `f : X ⟶ Spec κ`, and `k` an algebraic extension of `κ`. For every `κ`-morphism
`a : Spec k ⟶ X`, the underlying point `|a|` is a closed point of `X`. -/
@[weil "lem_fk204_underlying_point_closed"]
theorem isClosed_singleton_underlyingPoint [Algebra.IsAlgebraic κ k]
    (f : X ⟶ Spec (.of κ)) (a : Spec (.of k) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap κ k))) :
    IsClosed ({a.underlyingPoint} : Set X) := by
  refine isClosed_of_isAlgebraic_residueField f a.underlyingPoint
    ?_ ?_
  · obtain ⟨φ, hφ⟩ := a.exists_eq_map_comp_fromSpecResidueField
    exact isAlgebraic_residueField_of_hom f _ φ ((congrArg (· ≫ f) hφ).trans ha)
  rw [show ({f a.underlyingPoint} : Set (Spec (.of κ))) = Set.univ from
    Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _]
  exact isClosed_univ

end Scheme.Hom

end AlgebraicGeometry
