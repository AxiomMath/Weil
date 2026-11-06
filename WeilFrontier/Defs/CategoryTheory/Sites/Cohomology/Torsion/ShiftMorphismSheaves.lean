module

public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.ShiftedSystemSheaves
public import Weil.Attr

/-!
# The natural morphism `F[r] ⟶ F` of a projective system of `l`-torsion sheaves

Let `F = (F_n, u_n)_{n ∈ ℤ}` be a projective system of `l`-torsion sheaves on the small étale
site of a scheme `S` and `r ≥ 0`. The *natural morphism* `ε_r = ε_r^F : F[r] ⟶ F` has components
`ε_{r,n} = u_{n+1} ∘ u_{n+2} ∘ ⋯ ∘ u_{n+r} : F_{n+r} ⟶ F_n`, and `ε_0 = id`. These morphisms are
natural in `F`, so they form a natural transformation from the shift functor `[r]` to the identity
of the category `P_S` of projective systems of `l`-torsion sheaves.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsLTorsionProjectiveSystem.translateι`: the natural
  transformation from the translation `n ↦ n + r` of `ℤᵒᵖ` to the identity, given by `n ≤ n + r`.
* `AlgebraicGeometry.SmallEtale.IsLTorsionProjectiveSystem.shiftFunctorι`: the natural
  transformation `F[r] ⟶ F` for all `ℤ`-indexed projective systems in a category `C`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftι`: the natural morphism
  `ε_r : [r] ⟶ 𝟭` on `P_S`; its component at `F` is `ε_r^F : F[r] ⟶ F`.

## Main results

* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftι_app_hom_app`: `ε_{r,n}` is the map
  `F_{n+r} ⟶ F_n` of the functor `F` along `n ≤ n + r`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftι_zero`: `ε_0` is the canonical
  isomorphism `F[0] ≅ F`, and `shiftι_zero_app_hom_app`: `ε_{0,n}` is the identity of `F_n`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftι_succ_app_hom_app`:
  `ε_{r+1,n} = ε_{r,n} ∘ u_{n+r+1}`, so that `ε_{r,n} = u_{n+1} ∘ ⋯ ∘ u_{n+r}`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftι_one_app_hom_app`:
  `ε_{1,n} = u_{n+1}`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftι_naturality`:
  `f ∘ ε_r^F = ε_r^G ∘ f[r]`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.shiftι_app_shift_comp_shiftι_app`:
  `ε_r^F ∘ ε_s^{F[r]} = ε_{r+s}^F`, up to the identification `F[r][s] ≅ F[r+s]`.

## Implementation notes

The natural morphism is the whiskering of `translateι r` with `F`, so that its naturality in `n`
and in `F` holds by construction, and the identification with the composite
`u_{n+1} ∘ ⋯ ∘ u_{n+r}` is the recursion `shiftι_succ_app_hom_app`. Since `F_{n+r+1-1}` is not
definitionally `F_{n+r}`, the recursion carries the canonical identification `eqToHom`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

namespace IsLTorsionProjectiveSystem

/-- For `r ≥ 0`, the natural transformation from the translation `n ↦ n + r` of `ℤᵒᵖ` to the
identity, whose component at `n` is the morphism `op (n + r) ⟶ op n` given by `n ≤ n + r`. -/
def translateι (r : ℕ) : (translate (r : ℤ)).op ⟶ 𝟭 ℤᵒᵖ where
  app n := (homOfLE (by simp : n.unop ≤ n.unop + r)).op
  naturality _ _ _ := Subsingleton.elim _ _

@[simp]
theorem translate_obj (r n : ℤ) : (translate r).obj n = n + r :=
  rfl

variable {C : Type*} [Category C]

/-- For `r ≥ 0`, the natural transformation `F[r] ⟶ F` of `ℤ`-indexed projective systems in `C`:
its component at `n` is the map `F_{n+r} ⟶ F_n` of `F` along `n ≤ n + r`. -/
def shiftFunctorι (r : ℕ) : shiftFunctor (C := C) (r : ℤ) ⟶ 𝟭 _ :=
  (Functor.whiskeringLeft _ _ C).map (translateι r)

@[simp]
theorem shiftFunctorι_app_app (r : ℕ) (F : ℤᵒᵖ ⥤ C) (n : ℤᵒᵖ) :
    ((shiftFunctorι r).app F).app n =
      F.map (homOfLE (by simp : n.unop ≤ n.unop + r)).op :=
  rfl

end IsLTorsionProjectiveSystem

namespace LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

variable (B S hS l) in
/-- **The natural morphism `ε_r : F[r] ⟶ F`.** For `r ≥ 0`, the natural transformation from the
shift functor `[r]` to the identity of the category `P_S` of projective systems of `l`-torsion
sheaves. Its component at `F = (F_n, u_n)_n` is `ε_r^F : F[r] ⟶ F`, with components
`ε_{r,n} = u_{n+1} ∘ ⋯ ∘ u_{n+r} : F_{n+r} ⟶ F_n` (`shiftι_app_hom_app`,
`shiftι_succ_app_hom_app`), and `ε_0 = id` (`shiftι_zero`). -/
@[weil "def_fk112_shift_morphism_sheaves"]
def shiftι (r : ℕ) : shift.{w} B S hS l (r : ℤ) ⟶ 𝟭 _ where
  app F := ObjectProperty.homMk ((IsLTorsionProjectiveSystem.shiftFunctorι r).app F.obj)
  naturality _ _ f := hom_ext fun _ ↦ (f.hom.naturality _).symm

/-- The component `ε_{r,n} : F_{n+r} ⟶ F_n` is the map of `F` along `n ≤ n + r`. -/
theorem shiftι_app_hom_app (r : ℕ) (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    ((shiftι B S hS l r).app F).hom.app (op n) =
      F.obj.map (homOfLE (by simp : n ≤ n + r)).op :=
  rfl

/-- The natural morphism is natural: `f ∘ ε_r^F = ε_r^G ∘ f[r]`. -/
@[reassoc]
theorem shiftι_naturality {F G : LTorsionProjectiveSystem.{w} B S hS l} (f : F ⟶ G) (r : ℕ) :
    (shift B S hS l (r : ℤ)).map f ≫ (shiftι B S hS l r).app G =
      (shiftι B S hS l r).app F ≫ f :=
  (shiftι B S hS l r).naturality f

/-- `ε_{0,n}` is the identity of `F_n`, up to the identification `F_{n+0} = F_n`. -/
@[simp]
theorem shiftι_zero_app_hom_app (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    ((shiftι B S hS l 0).app F).hom.app (op n) =
      eqToHom (congrArg (fun m : ℤ ↦ F.obj.obj (op m))
        (show n + ((0 : ℕ) : ℤ) = n by simp)) := by
  rw [shiftι_app_hom_app, ← eqToHom_map F.obj
    (congrArg op (show n + ((0 : ℕ) : ℤ) = n by simp))]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- `ε_0` is the canonical isomorphism `[0] ≅ 𝟭`. -/
theorem shiftι_zero : shiftι.{w} B S hS l 0 = shiftZeroIso.hom := by
  refine NatTrans.ext (funext fun F ↦ hom_ext fun n ↦ ?_)
  rw [shiftι_app_hom_app, shiftZeroIso_hom_app_hom_app]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- The recursion `ε_{r+1,n} = ε_{r,n} ∘ u_{n+r+1}`, where `u_{n+r+1} : F_{n+r+1} ⟶ F_{n+r}` (up to
the identification `F_{n+r+1-1} = F_{n+r}`). With `shiftι_zero_app_hom_app` it identifies
`ε_{r,n}` with the composite `u_{n+1} ∘ ⋯ ∘ u_{n+r}`. -/
theorem shiftι_succ_app_hom_app (r : ℕ) (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    ((shiftι B S hS l (r + 1)).app F).hom.app (op n) =
      F.transition (n + (r + 1 : ℕ)) ≫
        eqToHom (congrArg (fun m : ℤ ↦ F.obj.obj (op m))
          (show n + ((r + 1 : ℕ) : ℤ) - 1 = n + r by push_cast; ring)) ≫
          ((shiftι B S hS l r).app F).hom.app (op n) := by
  rw [shiftι_app_hom_app, shiftι_app_hom_app, transition,
    IsLTorsionProjectiveSystem.transitionMap,
    ← eqToHom_map F.obj (congrArg op (show n + ((r + 1 : ℕ) : ℤ) - 1 = n + r by push_cast; ring)),
    ← F.obj.map_comp, ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- `ε_{1,n} = u_{n+1} : F_{n+1} ⟶ F_n` (up to the identification `F_{n+1-1} = F_n`). -/
theorem shiftι_one_app_hom_app (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    ((shiftι B S hS l 1).app F).hom.app (op n) =
      F.transition (n + (1 : ℕ)) ≫
        eqToHom (congrArg (fun m : ℤ ↦ F.obj.obj (op m))
          (show n + ((1 : ℕ) : ℤ) - 1 = n by push_cast; ring)) := by
  rw [shiftι_app_hom_app, transition, IsLTorsionProjectiveSystem.transitionMap,
    ← eqToHom_map F.obj (congrArg op (show n + ((1 : ℕ) : ℤ) - 1 = n by push_cast; ring)),
    ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- Components of the composite: `ε_{r,n} ∘ ε_{s,n}^{F[r]} = ε_{r+s,n}`, up to the identification
`F_{n+s+r} = F_{n+(r+s)}`. -/
@[reassoc]
theorem shiftι_app_shift_comp_shiftι_app_hom_app (F : LTorsionProjectiveSystem.{w} B S hS l)
    (r s : ℕ) (n : ℤ) :
    ((shiftι B S hS l s).app ((shift B S hS l (r : ℤ)).obj F)).hom.app (op n) ≫
        ((shiftι B S hS l r).app F).hom.app (op n) =
      eqToHom (congrArg (fun m : ℤ ↦ F.obj.obj (op m))
        (show n + (s : ℤ) + r = n + ((r + s : ℕ) : ℤ) by push_cast; ring)) ≫
        ((shiftι B S hS l (r + s)).app F).hom.app (op n) := by
  rw [shiftι_app_hom_app, shiftι_app_hom_app, shiftι_app_hom_app,
    ← eqToHom_map F.obj
      (congrArg op (show n + (s : ℤ) + r = n + ((r + s : ℕ) : ℤ) by push_cast; ring))]
  exact ((F.obj.map_comp _ _).symm.trans (congrArg F.obj.map (Subsingleton.elim _ _))).trans
    (F.obj.map_comp _ _)

/-- `ε_r^F ∘ ε_s^{F[r]} = ε_{r+s}^F`, up to the canonical isomorphism `F[r][s] ≅ F[r+s]`. -/
@[reassoc]
theorem shiftι_app_shift_comp_shiftι_app (F : LTorsionProjectiveSystem.{w} B S hS l)
    (r s : ℕ) :
    (shiftι B S hS l s).app ((shift B S hS l (r : ℤ)).obj F) ≫ (shiftι B S hS l r).app F =
      (shiftAddIso (r : ℤ) (s : ℤ)).hom.app F ≫
        eqToHom (by rw [Nat.cast_add]) ≫ (shiftι B S hS l (r + s)).app F := by
  refine hom_ext fun n ↦ ?_
  have key : ∀ (m : ℤ) (h : (r : ℤ) + s = m) (φ : (shift.{w} B S hS l m).obj F ⟶ F),
      (∀ k : ℤ, φ.hom.app (op k) = F.obj.map (homOfLE (by omega : k ≤ k + m)).op) →
      ((shiftAddIso (r : ℤ) (s : ℤ)).hom.app F ≫
        eqToHom (by rw [h]) ≫ φ).hom.app (op n) =
        F.obj.map (homOfLE (by omega : n ≤ n + s + r)).op := by
    rintro m rfl φ hφ
    simp only [eqToHom_refl, Category.id_comp]
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, shiftAddIso_hom_app_hom_app,
      hφ]
    exact (F.obj.map_comp _ _).symm.trans (congrArg F.obj.map (Subsingleton.elim _ _))
  rw [key _ (by push_cast; ring) _ (fun k ↦ shiftι_app_hom_app _ F k),
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, shiftι_app_hom_app,
    shiftι_app_hom_app]
  exact (F.obj.map_comp _ _).symm.trans (congrArg F.obj.map (Subsingleton.elim _ _))

end LTorsionProjectiveSystem

end AlgebraicGeometry.SmallEtale

end
