module

public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Order.Category.Preord

/-!
# Shifts of projective systems

For an integer `r`, the *shift* `[r]` of the category of projective systems
`(F_n, u_n)_{n ∈ ℤ}` of `l`-power torsion `Λ`-modules sends `F = (F_n, u_n)` to
`F[r] = (F_{n+r}, u_{n+r})_{n ∈ ℤ}` and a morphism `f = (f_n)` to `f[r] = (f_{n+r})`. If `F`
vanishes in degrees `≤ n₀`, then `F[r]` vanishes in degrees `≤ n₀ - r`, so `F[r]` is again a
projective system of the same kind.

## Main definitions

* `CategoryTheory.ProjectiveSystem.translate r`: the translation `n ↦ n + r` of the index
  category `ℤᵒᵖ`.
* `CategoryTheory.ProjectiveSystem.shift r`: the shift functor `[r]` on
  `CategoryTheory.ProjectiveSystem Λ l`, given by precomposition with `translate r`.

## Main results

* `CategoryTheory.ProjectiveSystem.shift_term`, `CategoryTheory.ProjectiveSystem.shift_map_app`:
  `F[r]_n = F_{n+r}` and `f[r]_n = f_{n+r}`.
* `CategoryTheory.ProjectiveSystem.shift_transition`: the transition maps of `F[r]` are the
  maps `u_{n+r}` of `F`.
* `CategoryTheory.ProjectiveSystem.isZero_shift_term`: `F[r]` vanishes in degrees `≤ n₀ - r`.
* `CategoryTheory.ProjectiveSystem.shiftZero`, `CategoryTheory.ProjectiveSystem.shiftAdd`:
  `[0] ≅ 𝟭` and `[r + s] ≅ [s] ⋙ [r]`.

## Implementation notes

A projective system is a functor `ℤᵒᵖ ⥤ ModuleCat Λ`, so the shift is the whiskering of the
inclusion of projective systems into the functor category with the translation `translate r`
of `ℤᵒᵖ`, lifted back to the full subcategory. The term `F[r]_{n-1} = F_{n-1+r}` is not
definitionally `F_{n+r-1}`, so the transition maps of `F[r]` agree with those of `F` only up to
the canonical identification `eqToHom`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

/-- The translation `n ↦ n + r` of the index category `ℤᵒᵖ` of projective systems. -/
def translate (r : ℤ) : ℤᵒᵖ ⥤ ℤᵒᵖ :=
  (Monotone.functor (f := fun n : ℤ => n + r) fun _ _ h => by simpa using h).op

@[simp]
lemma translate_obj (r : ℤ) (n : ℤᵒᵖ) : (translate r).obj n = op (n.unop + r) := rfl

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- Precomposition with `translate r` preserves projective systems of `l`-power torsion
modules: `F[r]` vanishes in degrees `≤ n₀ - r` when `F` vanishes in degrees `≤ n₀`. -/
lemma isTorsionBounded_translate_comp (r : ℤ) {F : ℤᵒᵖ ⥤ ModuleCat.{v} Λ}
    (hF : isTorsionBounded.{v} Λ l F) : isTorsionBounded.{v} Λ l (translate r ⋙ F) := by
  obtain ⟨htors, n₀, hn₀⟩ := hF
  exact ⟨fun n => htors (n + r), n₀ - r, fun n hn => hn₀ (n + r) (by omega)⟩

/-- The shift `[r]` of projective systems: it sends `F = (F_n, u_n)` to
`F[r] = (F_{n+r}, u_{n+r})_{n ∈ ℤ}` and a morphism `f = (f_n)` to `f[r] = (f_{n+r})`. -/
@[weil "def_fk112_shifted_system"]
def shift (r : ℤ) : ProjectiveSystem.{v} Λ l ⥤ ProjectiveSystem.{v} Λ l :=
  (isTorsionBounded.{v} Λ l).lift
    ((isTorsionBounded.{v} Λ l).ι ⋙ (Functor.whiskeringLeft _ _ _).obj (translate r))
    fun F => isTorsionBounded_translate_comp r F.property

@[simp]
lemma shift_obj_obj (r : ℤ) (F : ProjectiveSystem.{v} Λ l) :
    ((shift r).obj F).obj = translate r ⋙ F.obj := rfl

/-- The `n`-th term of `F[r]` is `F_{n+r}`. -/
lemma shift_term (r : ℤ) (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    ((shift r).obj F).term n = F.term (n + r) := rfl

/-- The `n`-th component of `f[r]` is `f_{n+r}`. -/
@[simp]
lemma shift_map_app (r : ℤ) {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) (n : ℤ) :
    app ((shift r).map f) n = app f (n + r) := rfl

/-- The transition map `F[r]_n ⟶ F[r]_{n-1}` is `u_{n+r} : F_{n+r} ⟶ F_{n+r-1}`, followed by
the identification `F_{n+r-1} = F_{n-1+r}`. -/
lemma shift_transition (r : ℤ) (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    ((shift r).obj F).transition n =
      (F.transition (n + r) ≫ eqToHom (congrArg F.term (by omega)) :
        F.term (n + r) ⟶ F.term (n - 1 + r)) := by
  have h : op (n + r - 1) = op (n - 1 + r) := congrArg op (by omega)
  rw [show (eqToHom (congrArg F.term (by omega)) : F.term (n + r - 1) ⟶ F.term (n - 1 + r)) =
      F.obj.map (eqToHom h) from (eqToHom_map _ _).symm]
  simp only [transition, ← Functor.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- `F[r]` vanishes in degrees `≤ n₀ - r` when `F` vanishes in degrees `≤ n₀`. -/
lemma isZero_shift_term (r : ℤ) {F : ProjectiveSystem.{v} Λ l} {n₀ : ℤ}
    (hF : ∀ n ≤ n₀, IsZero (F.term n)) (n : ℤ) (hn : n ≤ n₀ - r) :
    IsZero (((shift r).obj F).term n) :=
  hF (n + r) (by omega)

/-- The translation `n ↦ n + 0` of `ℤᵒᵖ` is the identity, up to canonical isomorphism. -/
def translateZero : translate 0 ≅ 𝟭 ℤᵒᵖ :=
  NatIso.ofComponents (fun n => eqToIso (by simp)) fun _ => Subsingleton.elim _ _

/-- Translating by `r + s` is translating by `s`, then by `r`, up to canonical isomorphism. -/
def translateAdd (r s : ℤ) : translate (r + s) ≅ translate s ⋙ translate r :=
  NatIso.ofComponents (fun n => eqToIso (by simp [add_assoc, add_comm s r]))
    fun _ => Subsingleton.elim _ _

/-- The shift `[0]` is the identity functor, up to canonical isomorphism. -/
def shiftZero : shift.{v} (Λ := Λ) (l := l) 0 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F => (isTorsionBounded.{v} Λ l).isoMk (Functor.isoWhiskerRight translateZero F.obj))
    fun f => hom_ext fun _ => (f.hom.naturality _).symm

/-- The shift `[r + s]` is the shift `[r]` followed by the shift `[s]`, up to canonical
isomorphism. -/
def shiftAdd (r s : ℤ) : shift.{v} (Λ := Λ) (l := l) (r + s) ≅ shift r ⋙ shift s :=
  NatIso.ofComponents
    (fun F => (isTorsionBounded.{v} Λ l).isoMk (Functor.isoWhiskerRight (translateAdd r s) F.obj))
    fun f => hom_ext fun _ => (f.hom.naturality _).symm

@[simp]
lemma shiftZero_hom_app_app (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    app (shiftZero.hom.app F) n = eqToHom (by simp [shift_term]) :=
  eqToHom_map _ (by simp)

@[simp]
lemma shiftZero_inv_app_app (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    app (shiftZero.inv.app F) n = eqToHom (by simp [shift_term]) :=
  eqToHom_map _ (by simp)

@[simp]
lemma shiftAdd_hom_app_app (r s : ℤ) (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    app ((shiftAdd r s).hom.app F) n = eqToHom (by simp [shift_term, add_assoc, add_comm s r]) :=
  eqToHom_map _ (by simp [add_assoc, add_comm s r])

@[simp]
lemma shiftAdd_inv_app_app (r s : ℤ) (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    app ((shiftAdd r s).inv.app F) n = eqToHom (by simp [shift_term, add_assoc, add_comm s r]) :=
  eqToHom_map _ (by simp [add_assoc, add_comm s r])

end ProjectiveSystem

end CategoryTheory
