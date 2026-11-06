module

public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.LTorsionProjectiveSystem
public import Weil.Attr

/-!
# Shifted projective systems of `l`-torsion sheaves

Let `F = (F_n, u_n)_{n ∈ ℤ}` be a projective system of `l`-torsion sheaves on the small étale site
of a scheme `S` and `r ∈ ℤ`. The *shifted system* is `F[r] = (F_{n+r}, u_{n+r})_{n ∈ ℤ}`, again a
projective system of `l`-torsion sheaves, and a morphism `f = (f_n)_n` has the shift
`f[r] = (f_{n+r})_n`. Shifting is a functor `P_S ⥤ P_S`.

Since a projective system is a functor `ℤᵒᵖ ⥤ Sheaf _ AddCommGrpCat`, the shift is precomposition
with the opposite of the translation functor `n ↦ n + r` of the ordered set `ℤ`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsLTorsionProjectiveSystem.translate`: the translation functor
  `n ↦ n + r` of `ℤ`.
* `AlgebraicGeometry.SmallEtale.IsLTorsionProjectiveSystem.shiftFunctor`: the shift
  `F ↦ (F_{n+r})_n` on all `ℤ`-indexed projective systems in a category `C`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shift`: the shift functor
  `F ↦ F[r]`, `f ↦ f[r]` on the category `P_S` of projective systems of `l`-torsion sheaves.

## Main results

* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shift_obj_obj_obj`,
  `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shift_map_hom_app`: the components of
  `F[r]` and `f[r]` are `F_{n+r}` and `f_{n+r}` (by definition).
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.transition_shift`: the transition maps of
  `F[r]` are the `u_{n+r}`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftZeroIso`,
  `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftAddIso`: `F[0] ≅ F` and
  `F[r][s] ≅ F[r + s]`, naturally in `F`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

namespace IsLTorsionProjectiveSystem

/-- The translation functor `n ↦ n + r` of the ordered set `ℤ`. -/
abbrev translate (r : ℤ) : ℤ ⥤ ℤ :=
  Monotone.functor (f := fun n : ℤ ↦ n + r) fun _ _ h ↦ by dsimp only; omega

variable {C : Type*} [Category C]

/-- The shift `F ↦ (F_{n+r})_n` of `ℤ`-indexed projective systems in `C`: precomposition with the
opposite of the translation `n ↦ n + r`. -/
abbrev shiftFunctor (r : ℤ) : (ℤᵒᵖ ⥤ C) ⥤ (ℤᵒᵖ ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj (translate r).op

/-- The shift by `0` of `ℤ`-indexed projective systems is the identity. -/
def shiftFunctorZeroIso : shiftFunctor (C := C) 0 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents
      (fun n ↦ F.mapIso (eqToIso (show op (n.unop + 0) = n by simp)))
      fun φ ↦ by
        dsimp
        rw [← F.map_comp, ← F.map_comp]
        rfl)
    fun f ↦ by
      ext n
      exact (f.naturality _).symm

/-- Shifting `ℤ`-indexed projective systems twice is shifting by the sum. -/
def shiftFunctorAddIso (r s : ℤ) :
    shiftFunctor (C := C) r ⋙ shiftFunctor s ≅ shiftFunctor (r + s) :=
  NatIso.ofComponents
    (fun F ↦ NatIso.ofComponents
      (fun n ↦ F.mapIso (eqToIso (show op (n.unop + s + r) = op (n.unop + (r + s)) by
        congr 1; omega)))
      fun φ ↦ by
        dsimp
        rw [← F.map_comp, ← F.map_comp]
        rfl)
    fun f ↦ by
      ext n
      exact (f.naturality _).symm

/-- The shift of a projective system of `l`-torsion sheaves is again one. -/
theorem shiftFunctor_obj {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}
    {F : ℤᵒᵖ ⥤ Sheaf (topology B S hS) AddCommGrpCat.{w}}
    (hF : IsLTorsionProjectiveSystem.{w} B S hS l F) (r : ℤ) :
    IsLTorsionProjectiveSystem.{w} B S hS l ((shiftFunctor r).obj F) := by
  obtain ⟨h₁, n₀, h₂⟩ := hF
  exact ⟨fun n ↦ h₁ (n + r), n₀ - r, fun n hn ↦ h₂ (n + r) (by omega)⟩

end IsLTorsionProjectiveSystem

namespace LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

variable (B S hS l) in
/-- **The shifted system.** For `r ∈ ℤ`, the shift functor on the category `P_S` of projective
systems of `l`-torsion sheaves: it sends `F = (F_n, u_n)_n` to `F[r] = (F_{n+r}, u_{n+r})_n` and a
morphism `f = (f_n)_n` to `f[r] = (f_{n+r})_n`. -/
@[weil "def_fk112_shifted_system_sheaves"]
def shift (r : ℤ) : LTorsionProjectiveSystem.{w} B S hS l ⥤ LTorsionProjectiveSystem.{w} B S hS l :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ IsLTorsionProjectiveSystem.shiftFunctor r)
    fun F ↦ F.property.shiftFunctor_obj r

@[simp]
theorem shift_obj_obj_obj (r : ℤ) (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    ((shift B S hS l r).obj F).obj.obj (op n) = F.obj.obj (op (n + r)) :=
  rfl

@[simp]
theorem shift_map_hom_app (r : ℤ) {F G : LTorsionProjectiveSystem.{w} B S hS l} (f : F ⟶ G)
    (n : ℤ) : ((shift B S hS l r).map f).hom.app (op n) = f.hom.app (op (n + r)) :=
  rfl

/-- The transition map `F[r]_n ⟶ F[r]_{n-1}` is the map `F_{n+r} ⟶ F_{n-1+r}` of `F`. -/
theorem transition_shift (r : ℤ) (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    ((shift B S hS l r).obj F).transition n =
      F.obj.map (homOfLE (show n - 1 + r ≤ n + r by omega)).op :=
  rfl

/-- The transition maps of `F[r]` are the transition maps `u_{n+r}` of `F`, followed by the
identification `F_{n+r-1} = F_{n-1+r}`. -/
theorem transition_shift_eq (r : ℤ) (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    ((shift B S hS l r).obj F).transition n =
      F.transition (n + r) ≫
        F.obj.map (eqToHom (show op (n + r - 1) = op (n - 1 + r) by congr 1; omega)) := by
  rw [transition_shift, transition, IsLTorsionProjectiveSystem.transitionMap, ← F.obj.map_comp]
  rfl

/-- The shift by `r` followed by the inclusion into all `ℤ`-indexed systems is the inclusion
followed by the shift. -/
def shiftCompιIso (r : ℤ) :
    shift.{w} B S hS l r ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ IsLTorsionProjectiveSystem.shiftFunctor r :=
  Iso.refl _

/-- The shift by `0` is the identity: `F[0] ≅ F`, naturally in `F`. -/
def shiftZeroIso : shift.{w} B S hS l 0 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (IsLTorsionProjectiveSystem.shiftFunctorZeroIso.app F.obj))
    fun f ↦ hom_ext fun _ ↦ (f.hom.naturality _).symm

/-- Shifting twice is shifting by the sum: `F[r][s] ≅ F[r + s]`, naturally in `F`. -/
def shiftAddIso (r s : ℤ) :
    shift.{w} B S hS l r ⋙ shift B S hS l s ≅ shift B S hS l (r + s) :=
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _
      ((IsLTorsionProjectiveSystem.shiftFunctorAddIso r s).app F.obj))
    fun f ↦ hom_ext fun _ ↦ (f.hom.naturality _).symm

@[simp]
theorem shiftZeroIso_hom_app_hom_app (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    ((shiftZeroIso.{w}).hom.app F).hom.app (op n) =
      F.obj.map (eqToHom (show op (n + 0) = op n by simp)) := by
  rfl

@[simp]
theorem shiftAddIso_hom_app_hom_app (r s : ℤ) (F : LTorsionProjectiveSystem.{w} B S hS l)
    (n : ℤ) :
    ((shiftAddIso.{w} r s).hom.app F).hom.app (op n) =
      F.obj.map (eqToHom (show op (n + s + r) = op (n + (r + s)) by congr 1; omega)) := by
  rfl

end LTorsionProjectiveSystem

end AlgebraicGeometry.SmallEtale

end
