module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Weil.Attr

/-!
# Projective systems of torsion modules

Let `Λ` be a commutative ring and `l ∈ Λ`. A *projective system of `l`-power torsion
`Λ`-modules* is a family `(F_n, u_n)_{n ∈ ℤ}` of `Λ`-modules `F_n`, every element of which is
annihilated by some power of `l`, together with `Λ`-linear maps `u_n : F_n → F_{n-1}`, such that
`F_n = 0` for all `n ≤ n₀`, for some integer `n₀`. Morphisms are families of linear maps
commuting with the transition maps. In the situation of Freitag–Kiehl, `Λ = ℤ_l` and `l` is the
prime `l`.

We model such a system as a functor `ℤᵒᵖ ⥤ ModuleCat Λ`: the transition map `u_n` is the image
of the morphism `op n ⟶ op (n - 1)` given by `n - 1 ≤ n`, and every other image is a composite of
these. The category of projective systems is the full subcategory of the functor category cut
out by the two conditions, so its morphisms are natural transformations; by
`CategoryTheory.ProjectiveSystem.homMk` a morphism is the same thing as a family of linear maps
commuting with the maps `u_n`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.isTorsionBounded Λ l`: the property of a functor
  `ℤᵒᵖ ⥤ ModuleCat Λ` that all its values are `l`-power torsion and that it vanishes in all
  sufficiently negative degrees.
* `CategoryTheory.ProjectiveSystem Λ l`: the category of such systems.
* `CategoryTheory.ProjectiveSystem.LAdic l`: the case `Λ = ℤ_[l]`, with `l` itself.
* `CategoryTheory.ProjectiveSystem.transition`: the transition map `u_n : F_n ⟶ F_{n-1}`.

## Main results

* `CategoryTheory.ProjectiveSystem.homMk`: a morphism of projective systems built from
  components commuting with the transition maps `u_n`.
* `CategoryTheory.ProjectiveSystem.hom_ext`: morphisms are determined by their components.

## Implementation notes

The source fixes `Λ = ℤ_l`; the definition is stated for any commutative ring `Λ` and any
element `l`, and `CategoryTheory.ProjectiveSystem.LAdic` is the source's category. A degree `F_n`
being zero is expressed as `IsZero`, the categorical form of `F_n = 0`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable (Λ : Type u) [CommRing Λ] (l : Λ)

/-- A functor `F : ℤᵒᵖ ⥤ ModuleCat Λ` is a projective system of `l`-power torsion modules,
bounded below, if every `F_n` is `l`-power torsion and `F_n = 0` for all `n ≤ n₀`, for some
`n₀`. -/
@[weil "def_fk112_projective_system_torsion_modules"]
def isTorsionBounded : ObjectProperty (ℤᵒᵖ ⥤ ModuleCat.{v} Λ) := fun F =>
  (∀ n : ℤ, Module.IsTorsion' (F.obj (op n)) (Submonoid.powers l)) ∧
    ∃ n₀ : ℤ, ∀ n ≤ n₀, IsZero (F.obj (op n))

end ProjectiveSystem

/-- The category of projective systems `(F_n, u_n)_{n ∈ ℤ}` of `l`-power torsion `Λ`-modules
vanishing in all sufficiently negative degrees. -/
@[weil "def_fk112_projective_system_torsion_modules"]
abbrev ProjectiveSystem (Λ : Type u) [CommRing Λ] (l : Λ) :=
  (ProjectiveSystem.isTorsionBounded.{v} Λ l).FullSubcategory

namespace ProjectiveSystem

/-- The category of projective systems of `l`-power torsion `ℤ_[l]`-modules. -/
@[weil "def_fk112_projective_system_torsion_modules"]
abbrev LAdic (l : ℕ) [Fact l.Prime] := ProjectiveSystem.{v} ℤ_[l] (l : ℤ_[l])

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The `n`-th term `F_n` of a projective system. -/
abbrev term (F : ProjectiveSystem.{v} Λ l) (n : ℤ) : ModuleCat.{v} Λ := F.obj.obj (op n)

/-- The transition map `u_n : F_n ⟶ F_{n-1}` of a projective system. -/
def transition (F : ProjectiveSystem.{v} Λ l) (n : ℤ) : F.term n ⟶ F.term (n - 1) :=
  F.obj.map (homOfLE (Int.sub_le_self n zero_le_one)).op

lemma isTorsion' (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    Module.IsTorsion' (F.term n) (Submonoid.powers l) :=
  F.property.1 n

lemma exists_pow_smul_eq_zero (F : ProjectiveSystem.{v} Λ l) (n : ℤ) (x : F.term n) :
    ∃ k : ℕ, l ^ k • x = 0 := by
  obtain ⟨⟨a, k, rfl⟩, h⟩ := F.isTorsion' n (x := x)
  exact ⟨k, h⟩

lemma exists_isZero (F : ProjectiveSystem.{v} Λ l) : ∃ n₀ : ℤ, ∀ n ≤ n₀, IsZero (F.term n) :=
  F.property.2

/-- The component `f_n : F_n ⟶ G_n` of a morphism of projective systems. -/
abbrev app {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) (n : ℤ) : F.term n ⟶ G.term n :=
  f.hom.app (op n)

@[reassoc]
lemma app_transition {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) (n : ℤ) :
    app f n ≫ G.transition n = F.transition n ≫ app f (n - 1) :=
  (f.hom.naturality _).symm

@[simp]
lemma id_app (F : ProjectiveSystem.{v} Λ l) (n : ℤ) : app (𝟙 F) n = 𝟙 (F.term n) := rfl

@[simp, reassoc]
lemma comp_app {F G H : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) (g : G ⟶ H) (n : ℤ) :
    app (f ≫ g) n = app f n ≫ app g n := rfl

@[ext]
lemma hom_ext {F G : ProjectiveSystem.{v} Λ l} {f g : F ⟶ G} (h : ∀ n, app f n = app g n) :
    f = g := by
  ext1
  ext1
  funext n
  exact h n.unop

/-- The map `F_n ⟶ F_m` of a functor `ℤᵒᵖ ⥤ C`, for `m ≤ n`, is the composite of the maps
`F_{k} ⟶ F_{k-1}`: naturality along adjacent degrees implies naturality. -/
lemma naturality_of_adjacent {C : Type*} [Category C] {F G : ℤᵒᵖ ⥤ C}
    (f : ∀ n : ℤ, F.obj (op n) ⟶ G.obj (op n))
    (hf : ∀ n : ℤ, f n ≫ G.map (homOfLE (Int.sub_le_self n zero_le_one)).op =
      F.map (homOfLE (Int.sub_le_self n zero_le_one)).op ≫ f (n - 1))
    (m n : ℤ) (hmn : m ≤ n) :
    F.map (homOfLE hmn).op ≫ f m = f n ≫ G.map (homOfLE hmn).op := by
  have key : ∀ (k j : ℤ) (h : j ≤ k), j = k - 1 →
      f k ≫ G.map (homOfLE h).op = F.map (homOfLE h).op ≫ f j := by
    rintro k j h rfl
    exact hf k
  induction n, hmn using Int.leInduction with
  | base => simp
  | succ n hmn ih =>
    have e : (homOfLE (Int.le_add_one hmn)).op =
        (homOfLE (Int.le_add_one (le_refl n))).op ≫ (homOfLE hmn).op := Subsingleton.elim _ _
    rw [e, F.map_comp, G.map_comp, Category.assoc, ih, ← Category.assoc, ← Category.assoc,
      key (n + 1) n _ (by omega)]

/-- A morphism of projective systems from components `f_n : F_n ⟶ G_n` with
`u^G_n ∘ f_n = f_{n-1} ∘ u^F_n` for all `n`. -/
def homMk {F G : ProjectiveSystem.{v} Λ l} (f : ∀ n : ℤ, F.term n ⟶ G.term n)
    (hf : ∀ n : ℤ, f n ≫ G.transition n = F.transition n ≫ f (n - 1)) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun n => f n.unop
      naturality := by
        rintro ⟨n⟩ ⟨m⟩ h
        have hmn : m ≤ n := leOfHom h.unop
        obtain rfl : h = (homOfLE hmn).op := Subsingleton.elim _ _
        exact naturality_of_adjacent (F := F.obj) (G := G.obj) f hf m n hmn }

@[simp]
lemma homMk_app {F G : ProjectiveSystem.{v} Λ l} (f : ∀ n : ℤ, F.term n ⟶ G.term n)
    (hf : ∀ n : ℤ, f n ≫ G.transition n = F.transition n ≫ f (n - 1)) (n : ℤ) :
    app (homMk f hf) n = f n := rfl

end ProjectiveSystem

end CategoryTheory
