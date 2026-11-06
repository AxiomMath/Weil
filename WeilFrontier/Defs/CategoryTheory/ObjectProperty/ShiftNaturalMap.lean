module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ShiftedSystem

/-!
# The natural map of a shifted projective system

For a projective system `F = (F_n, u_n)_{n ∈ ℤ}` of `l`-power torsion `Λ`-modules and an integer
`r ≥ 0`, the *natural map* `ε^r_F : F[r] ⟶ F` has components
`ε^r_{F,n} = u_{n+1} ∘ u_{n+2} ∘ ⋯ ∘ u_{n+r} : F_{n+r} ⟶ F_n`, the identity for `r = 0`.
These maps are natural in `F`, so they form a natural transformation `[r] ⟶ 𝟭`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.translateι r`: the natural transformation
  `translate r ⟶ 𝟭` of `ℤᵒᵖ`, given by `n ≤ n + r`.
* `CategoryTheory.ProjectiveSystem.shiftNatTrans r`: the natural transformation `[r] ⟶ 𝟭`.
* `CategoryTheory.ProjectiveSystem.natMap F r`: the natural map `ε^r_F : F[r] ⟶ F`.

## Main results

* `CategoryTheory.ProjectiveSystem.natMap_app`: `ε^r_{F,n}` is the map `F_{n+r} ⟶ F_n` of the
  functor `F` along `n ≤ n + r`.
* `CategoryTheory.ProjectiveSystem.natMap_zero_app`: `ε^0_{F,n}` is the identity of `F_n`.
* `CategoryTheory.ProjectiveSystem.natMap_succ_app`: `ε^{r+1}_{F,n} = ε^r_{F,n} ∘ u_{n+r+1}`,
  so that `ε^r_{F,n} = u_{n+1} ∘ ⋯ ∘ u_{n+r}`.
* `CategoryTheory.ProjectiveSystem.natMap_one_app`: `ε^1_{F,n} = u_{n+1}`.
* `CategoryTheory.ProjectiveSystem.natMap_naturality`: `f ∘ ε^r_F = ε^r_G ∘ f[r]`.
* `CategoryTheory.ProjectiveSystem.natMap_shift_comp_natMap_app`:
  `ε^r_{F,n} ∘ ε^s_{F[r],n} = ε^{r+s}_{F,n}`.

## Implementation notes

The natural map is the whiskering of `translateι r : translate r ⟶ 𝟭` with `F`, so that its
naturality in `n` and in `F` holds by construction, and the identification with the composite
`u_{n+1} ∘ ⋯ ∘ u_{n+r}` is the recursion `natMap_succ_app`. Since `F_{n+r+1-1}` is not
definitionally `F_{n+r}`, the recursion carries the canonical identification `eqToHom`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

/-- For `r ≥ 0`, the natural transformation `translate r ⟶ 𝟭` of `ℤᵒᵖ`, whose component at
`n` is the morphism `op (n + r) ⟶ op n` given by `n ≤ n + r`. -/
def translateι (r : ℕ) : translate (r : ℤ) ⟶ 𝟭 ℤᵒᵖ where
  app n := (homOfLE (by simp : n.unop ≤ n.unop + r)).op
  naturality _ _ _ := Subsingleton.elim _ _

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The natural map `ε^r_F : F[r] ⟶ F` of a projective system `F = (F_n, u_n)`, for `r ≥ 0`:
its component `ε^r_{F,n} : F_{n+r} ⟶ F_n` is `u_{n+1} ∘ u_{n+2} ∘ ⋯ ∘ u_{n+r}`, the identity
for `r = 0` (see `natMap_zero_app` and `natMap_succ_app`). -/
@[weil "def_fk112_shift_natural_map"]
def natMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) : (shift (r : ℤ)).obj F ⟶ F :=
  ObjectProperty.homMk (Functor.whiskerRight (translateι r) F.obj)

/-- The component `ε^r_{F,n} : F_{n+r} ⟶ F_n` is the map of `F` along `n ≤ n + r`. -/
lemma natMap_app (F : ProjectiveSystem.{v} Λ l) (r : ℕ) (n : ℤ) :
    app (natMap F r) n = F.obj.map (homOfLE (by simp : n ≤ n + r)).op := rfl

/-- `ε^0_{F,n}` is the identity of `F_n`, up to the identification `F_{n+0} = F_n`. -/
@[simp]
lemma natMap_zero_app (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    app (natMap F 0) n = eqToHom (congrArg F.term (by simp)) := by
  rw [natMap_app, ← eqToHom_map F.obj (congrArg op (by simp))]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- `ε^0_F` is the canonical isomorphism `F[0] ≅ F`. -/
lemma natMap_zero (F : ProjectiveSystem.{v} Λ l) :
    natMap F 0 = shiftZero.hom.app F :=
  hom_ext fun n => by rw [natMap_zero_app, shiftZero_hom_app_app]; rfl

/-- The recursion `ε^{r+1}_{F,n} = ε^r_{F,n} ∘ u_{n+r+1}`, where `u_{n+r+1} : F_{n+r+1} ⟶ F_{n+r}`
(up to the identification `F_{n+r+1-1} = F_{n+r}`). With `natMap_zero_app` it identifies
`ε^r_{F,n}` with the composite `u_{n+1} ∘ ⋯ ∘ u_{n+r}`. -/
lemma natMap_succ_app (F : ProjectiveSystem.{v} Λ l) (r : ℕ) (n : ℤ) :
    app (natMap F (r + 1)) n =
      (F.transition (n + (r + 1 : ℕ)) ≫ eqToHom (congrArg F.term (by push_cast; ring)) :
        F.term (n + (r + 1 : ℕ)) ⟶ F.term (n + r)) ≫ app (natMap F r) n := by
  rw [natMap_app, natMap_app, transition,
    ← eqToHom_map F.obj (congrArg op (by push_cast; ring)), ← F.obj.map_comp,
    ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- `ε^1_{F,n} = u_{n+1} : F_{n+1} ⟶ F_n` (up to the identification `F_{n+1-1} = F_n`). -/
lemma natMap_one_app (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    app (natMap F 1) n =
      (F.transition (n + (1 : ℕ)) ≫ eqToHom (congrArg F.term (by push_cast; ring)) :
        F.term (n + (1 : ℕ)) ⟶ F.term n) := by
  rw [natMap_app, transition, ← eqToHom_map F.obj (congrArg op (by push_cast; ring)),
    ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- The natural map is natural: `f ∘ ε^r_F = ε^r_G ∘ f[r]`. -/
@[reassoc]
lemma natMap_naturality {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) (r : ℕ) :
    (shift (r : ℤ)).map f ≫ natMap G r = natMap F r ≫ f :=
  hom_ext fun _ => (f.hom.naturality _).symm

/-- For `r ≥ 0`, the natural transformation `[r] ⟶ 𝟭` whose component at `F` is the natural map
`ε^r_F : F[r] ⟶ F`. -/
def shiftNatTrans (r : ℕ) : shift.{v} (Λ := Λ) (l := l) (r : ℤ) ⟶ 𝟭 _ where
  app F := natMap F r
  naturality _ _ f := natMap_naturality f r

@[simp]
lemma shiftNatTrans_app (r : ℕ) (F : ProjectiveSystem.{v} Λ l) :
    (shiftNatTrans r).app F = natMap F r := rfl

/-- Components of the composite: `ε^r_{F,n} ∘ ε^s_{F[r],n} = ε^{r+s}_{F,n}`, up to the
identification `F_{n+s+r} = F_{n+(r+s)}`. -/
@[reassoc]
lemma natMap_shift_comp_natMap_app (F : ProjectiveSystem.{v} Λ l) (r s : ℕ) (n : ℤ) :
    app (natMap ((shift (r : ℤ)).obj F) s) n ≫ app (natMap F r) n =
      (eqToHom (congrArg F.term (by push_cast; ring)) :
        F.term (n + s + r) ⟶ F.term (n + (r + s : ℕ))) ≫ app (natMap F (r + s)) n := by
  rw [natMap_app, natMap_app, natMap_app, ← eqToHom_map F.obj (congrArg op (by push_cast; ring))]
  exact ((F.obj.map_comp _ _).symm.trans (congrArg F.obj.map (Subsingleton.elim _ _))).trans
    (F.obj.map_comp _ _)

end ProjectiveSystem

end CategoryTheory
