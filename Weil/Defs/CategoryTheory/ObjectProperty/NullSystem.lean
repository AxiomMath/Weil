module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.ObjectProperty.ShiftNaturalMap
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Null systems

A projective system `F = (F_n, u_n)` of `l`-power torsion `Λ`-modules is a *null system* if
there is `t ≥ 0` such that the natural map `ε^t_F : F[t] ⟶ F` is zero, that is, every
composite `u_{n+1} ∘ ⋯ ∘ u_{n+t} : F_{n+t} ⟶ F_n` of `t` transition maps vanishes, for one `t`
independent of `n`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.isNull`: the property of a projective system of being a null
  system.

## Main results

* `CategoryTheory.ProjectiveSystem.isNull_iff_app`: `F` is null iff for some `t` every
  component `ε^t_{F,n}` is zero.
* `CategoryTheory.ProjectiveSystem.natMap_eq_zero_of_le`: if `ε^t_F = 0` then `ε^s_F = 0` for
  all `s ≥ t`.
* `CategoryTheory.ProjectiveSystem.isNull_of_isZero`: a zero object is null.
* `CategoryTheory.ProjectiveSystem.isNull_of_mono`: a subobject of a null system is null.
* `CategoryTheory.ProjectiveSystem.isNull_of_epi`: a quotient of a null system is null.
* `CategoryTheory.ProjectiveSystem.isNull_of_iso`: being null is invariant under isomorphism.

## Implementation notes

The shift `[r]` is an equivalence of categories with inverse `[-r]`
(`CategoryTheory.ProjectiveSystem.shiftEquivalence`); it is used to see that `f[t]` is an
epimorphism when `f` is.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- A projective system `F` is a *null system* if there is `t ≥ 0` such that the natural map
`ε^t_F : F[t] ⟶ F` is the zero map. -/
@[weil "def_fk112_null_system"]
def isNull : ObjectProperty (ProjectiveSystem.{v} Λ l) := fun F => ∃ t : ℕ, natMap F t = 0

lemma isNull_iff (F : ProjectiveSystem.{v} Λ l) : isNull F ↔ ∃ t : ℕ, natMap F t = 0 :=
  Iff.rfl

lemma natMap_eq_zero_iff (F : ProjectiveSystem.{v} Λ l) (t : ℕ) :
    natMap F t = 0 ↔ ∀ n : ℤ, app (natMap F t) n = 0 :=
  ⟨fun h n => by rw [h]; rfl, fun h => hom_ext fun n => by rw [h n]; rfl⟩

/-- `F` is null iff for some `t` all components `ε^t_{F,n} : F_{n+t} ⟶ F_n` vanish. -/
lemma isNull_iff_app (F : ProjectiveSystem.{v} Λ l) :
    isNull F ↔ ∃ t : ℕ, ∀ n : ℤ, app (natMap F t) n = 0 := by
  simp only [isNull_iff, natMap_eq_zero_iff]

/-- For `t ≤ s`, the component `ε^s_{F,n}` factors through `ε^t_{F,n}`. -/
lemma natMap_app_eq_comp_of_le (F : ProjectiveSystem.{v} Λ l) {t s : ℕ} (hts : t ≤ s) (n : ℤ) :
    app (natMap F s) n =
      F.obj.map (homOfLE (by omega : n + t ≤ n + s)).op ≫ app (natMap F t) n := by
  rw [natMap_app, natMap_app, ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- If `ε^t_F = 0` then `ε^s_F = 0` for every `s ≥ t`. -/
lemma natMap_eq_zero_of_le {F : ProjectiveSystem.{v} Λ l} {t s : ℕ} (h : natMap F t = 0)
    (hts : t ≤ s) : natMap F s = 0 := by
  rw [natMap_eq_zero_iff] at h ⊢
  intro n
  rw [natMap_app_eq_comp_of_le F hts n, h n]
  exact comp_zero

/-- A projective system that is a zero object is null. -/
lemma isNull_of_isZero {F : ProjectiveSystem.{v} Λ l} (hF : IsZero F) : isNull F :=
  ⟨0, hF.eq_of_tgt _ _⟩

/-- A subobject of a null system is null. -/
lemma isNull_of_mono {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) [Mono f] (hG : isNull G) :
    isNull F := by
  obtain ⟨t, ht⟩ := hG
  refine ⟨t, ?_⟩
  rw [← cancel_mono f, ← natMap_naturality, ht, comp_zero, zero_comp]

/-- The shift `[r]` is an equivalence of categories, with inverse `[-r]`. -/
def shiftEquivalence (r : ℤ) : ProjectiveSystem.{v} Λ l ≌ ProjectiveSystem.{v} Λ l :=
  Equivalence.mk (shift r) (shift (-r))
    (shiftZero.symm ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫ shiftAdd r (-r))
    ((shiftAdd (-r) r).symm ≪≫ eqToIso (by rw [neg_add_cancel]) ≪≫ shiftZero)

instance (r : ℤ) : (shift.{v} (Λ := Λ) (l := l) r).IsEquivalence :=
  (shiftEquivalence r).isEquivalence_functor

/-- A quotient of a null system is null. -/
lemma isNull_of_epi {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) [Epi f] (hF : isNull F) :
    isNull G := by
  obtain ⟨t, ht⟩ := hF
  refine ⟨t, ?_⟩
  rw [← cancel_epi ((shift (t : ℤ)).map f), natMap_naturality, ht, zero_comp, comp_zero]

/-- Being a null system is invariant under isomorphism. -/
lemma isNull_of_iso {F G : ProjectiveSystem.{v} Λ l} (e : F ≅ G) (hF : isNull F) : isNull G :=
  isNull_of_epi e.hom hF

instance : (isNull.{v} (Λ := Λ) (l := l)).IsClosedUnderIsomorphisms :=
  ⟨fun e hF => isNull_of_iso e hF⟩

end ProjectiveSystem

end CategoryTheory
