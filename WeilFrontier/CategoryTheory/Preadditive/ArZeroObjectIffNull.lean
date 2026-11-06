module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.Preadditive.ArZeroMorphismCriterion
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.NullSystem

/-!
# Zero objects of the Artin–Rees category

Let `𝒫` be the category of projective systems of `l`-power torsion `Λ`-modules and
`q : 𝒫 ⥤ AR` the canonical functor to the Artin–Rees category. A projective system `T` is a
zero object of the A–R category if and only if it is a null system, that is, `ε^t_T = 0` for
some `t ≥ 0`: indeed `T` is a zero object iff `id_T = q(id_T)` vanishes in `Hom_AR(T, T)`, iff
`id_T ∘ ε^t_T = ε^t_T = 0` for some `t`.

## Main results

* `CategoryTheory.ProjectiveSystem.ArCategory.isZero_of_iff_isNull`: `T` is a zero object of
  the A–R category if and only if `T` is a null system.
* `CategoryTheory.ProjectiveSystem.isZero_toArCategory_obj_iff_isNull`: the same statement for
  `q(T)`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- **Zero objects of the A–R category**: a projective system `T` is a zero object of the A–R
category if and only if `T` is a null system. -/
@[weil "lem_fk112_ar_zero_object_iff_null"]
theorem ArCategory.isZero_of_iff_isNull (T : ProjectiveSystem.{v} Λ l) :
    IsZero (ArCategory.of T) ↔ isNull T := by
  have h := toArCategory_map_eq_zero_iff (𝟙 T)
  rw [Functor.map_id] at h
  simp only [Category.comp_id] at h
  exact (IsZero.iff_id_eq_zero _).trans (h.trans (isNull_iff T).symm)

/-- `q(T)` is a zero object of the A–R category if and only if `T` is a null system. -/
theorem isZero_toArCategory_obj_iff_isNull (T : ProjectiveSystem.{v} Λ l) :
    IsZero ((toArCategory Λ l).obj T) ↔ isNull T :=
  ArCategory.isZero_of_iff_isNull T

end ProjectiveSystem

end CategoryTheory
