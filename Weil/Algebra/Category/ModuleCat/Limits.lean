module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.ObjectProperty.ShiftNaturalMap
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# The limit of a shifted projective system

Let `F = (F_n, u_n)` be a projective system of `l`-power torsion `Λ`-modules and `r ≥ 0`. The
natural map `ε^r_F : F[r] ⟶ F` induces an isomorphism of `Λ`-modules
`lim_n F_{n+r} ≅ lim_n F_n`, `(y_n)_n ↦ (ε^r_{F,n}(y_n))_n`. Its inverse sends a compatible
family `(x_n)_n` to `(x_{n+r})_n`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.sectionsTranslateEquiv`: for any functor
  `G : ℤᵒᵖ ⥤ ModuleCat Λ` and `r ≥ 0`, the linear equivalence between the module of compatible
  families of `translate r ⋙ G` and that of `G`, induced by the maps `G_{n+r} ⟶ G_n`.
* `CategoryTheory.ProjectiveSystem.limitShiftEquiv`: the linear equivalence
  `lim_n F[r]_n ≃ lim_n F_n` induced by `ε^r_F`.

## Main results

* `CategoryTheory.ProjectiveSystem.limitShiftEquiv_apply`: the equivalence is
  `(y_n)_n ↦ (ε^r_{F,n}(y_n))_n`.
* `CategoryTheory.ProjectiveSystem.limitShiftEquiv_symm_apply`: its inverse is
  `(x_n)_n ↦ (x_{n+r})_n`.

## Implementation notes

The projective limit `lim_n F_n` is the `Λ`-module `ModuleCat.sectionsSubmodule F.obj`
of compatible families `(x_n)_n`, the concrete model of the limit in `ModuleCat Λ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

open ModuleCat (sectionsSubmodule)

variable {Λ : Type u} [CommRing Λ]

/-- For a functor `G : ℤᵒᵖ ⥤ ModuleCat Λ` and `r ≥ 0`, the compatible families of
`translate r ⋙ G` (that is, of `(G_{n+r})_n`) are in linear bijection with those of `G`, by
`(y_n)_n ↦ (G(n ≤ n + r)(y_n))_n`, with inverse `(x_n)_n ↦ (x_{n+r})_n`. -/
def sectionsTranslateEquiv (G : ℤᵒᵖ ⥤ ModuleCat.{v} Λ) (r : ℕ) :
    sectionsSubmodule (translate (r : ℤ) ⋙ G) ≃ₗ[Λ] sectionsSubmodule G where
  toFun y := ⟨fun j => G.map ((translateι r).app j) (y.1 j), by
    intro j j' f
    have hy := y.2 f
    change G.map f (G.map ((translateι r).app j) (y.1 j)) = G.map ((translateι r).app j') (y.1 j')
    rw [← hy]
    change (G.map ((translateι r).app j) ≫ G.map f) (y.1 j) =
      (G.map ((translate (r : ℤ)).map f) ≫ G.map ((translateι r).app j')) (y.1 j)
    rw [← G.map_comp, ← G.map_comp]
    exact congrArg (fun g => (G.map g) (y.1 j)) (Subsingleton.elim _ _)⟩
  map_add' y z := by ext j; exact map_add (G.map _).hom _ _
  map_smul' c y := by ext j; exact map_smul (G.map _).hom _ _
  invFun x := ⟨fun j => x.1 ((translate (r : ℤ)).obj j), fun f => x.2 ((translate (r : ℤ)).map f)⟩
  left_inv y := by
    ext j
    change G.map ((translateι r).app ((translate (r : ℤ)).obj j))
      (y.1 ((translate (r : ℤ)).obj j)) = y.1 j
    have hf : ((translateι r).app ((translate (r : ℤ)).obj j)) =
        (translate (r : ℤ)).map ((translateι r).app j) := Subsingleton.elim _ _
    rw [hf]
    exact y.2 ((translateι r).app j)
  right_inv x := by
    ext j
    exact x.2 ((translateι r).app j)

@[simp]
lemma sectionsTranslateEquiv_apply_coe (G : ℤᵒᵖ ⥤ ModuleCat.{v} Λ) (r : ℕ)
    (y : sectionsSubmodule (translate (r : ℤ) ⋙ G)) (j : ℤᵒᵖ) :
    (sectionsTranslateEquiv G r y).1 j = G.map ((translateι r).app j) (y.1 j) := rfl

@[simp]
lemma sectionsTranslateEquiv_symm_apply_coe (G : ℤᵒᵖ ⥤ ModuleCat.{v} Λ) (r : ℕ)
    (x : sectionsSubmodule G) (j : ℤᵒᵖ) :
    ((sectionsTranslateEquiv G r).symm x).1 j = x.1 ((translate (r : ℤ)).obj j) := rfl

variable {l : Λ}

/-- For a projective system `F` and `r ≥ 0`, the isomorphism of `Λ`-modules
`lim_n F_{n+r} ≅ lim_n F_n` induced by the natural map `ε^r_F : F[r] ⟶ F`: it sends a compatible
family `(y_n)_n` of `F[r]` to `(ε^r_{F,n}(y_n))_n` (see `limitShiftEquiv_apply`). -/
@[weil "lem_fk112_limit_shift_invariant"]
def limitShiftEquiv (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    sectionsSubmodule ((shift (r : ℤ)).obj F).obj ≃ₗ[Λ] sectionsSubmodule F.obj :=
  sectionsTranslateEquiv F.obj r

/-- The isomorphism `limitShiftEquiv F r` is `(y_n)_n ↦ (ε^r_{F,n}(y_n))_n`. -/
@[weil "lem_fk112_limit_shift_invariant"]
lemma limitShiftEquiv_apply (F : ProjectiveSystem.{v} Λ l) (r : ℕ)
    (y : sectionsSubmodule ((shift (r : ℤ)).obj F).obj) (n : ℤ) :
    (limitShiftEquiv F r y).1 (op n) = app (natMap F r) n (y.1 (op n)) := rfl

/-- The inverse of `limitShiftEquiv F r` is `(x_n)_n ↦ (x_{n+r})_n`. -/
lemma limitShiftEquiv_symm_apply (F : ProjectiveSystem.{v} Λ l) (r : ℕ)
    (x : sectionsSubmodule F.obj) (n : ℤ) :
    ((limitShiftEquiv F r).symm x).1 (op n) = x.1 (op (n + r)) := rfl

end ProjectiveSystem

end CategoryTheory
