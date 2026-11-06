module

public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.LTorsionSheaf
public import Weil.Attr

/-!
# Projective systems of `l`-torsion sheaves

Let `S` be a scheme and `l` a natural number. A *projective system of `l`-torsion sheaves* on the
small étale site of `S` is a family `(F_n, u_n)_{n ∈ ℤ}` of `l`-torsion abelian sheaves `F_n`
(`AlgebraicGeometry.SmallEtale.IsLTorsionSheaf`) with transition maps `u_n : F_n ⟶ F_{n-1}`,
such that `F_n = 0` for all `n` below some `n₀`. A morphism `f : F ⟶ G` is a family of morphisms
`f_n : F_n ⟶ G_n` commuting with the transition maps.

We encode such a system as a functor `ℤᵒᵖ ⥤ Sheaf (SmallEtale.topology B S hS) AddCommGrpCat`:
for `m ≤ n` the map `F_n ⟶ F_m` is the composite of the transition maps, and the transition map
`u_n` is the image of `n - 1 ≤ n`. The projective systems of `l`-torsion sheaves are then the full
subcategory of this functor category cut out by the property
`AlgebraicGeometry.SmallEtale.IsLTorsionProjectiveSystem`; its morphisms are natural
transformations, which are exactly the families commuting with the transition maps
(`AlgebraicGeometry.SmallEtale.IsLTorsionProjectiveSystem.naturality_iff`).

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsLTorsionProjectiveSystem`: the property of a `ℤ`-indexed
  projective system of abelian sheaves of having `l`-torsion components, zero below some index.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem`: the category `P_S` of projective
  systems of `l`-torsion sheaves.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.transition`: the transition map
  `u_n : F_n ⟶ F_{n-1}`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.homMk`: a morphism of systems from a
  family of morphisms commuting with the transition maps.

## Main results

* `AlgebraicGeometry.SmallEtale.IsLTorsionProjectiveSystem.naturality_iff`: a family of morphisms
  between the components of two `ℤ`-indexed systems is natural if and only if it commutes with
  the transition maps `u_n`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.isLTorsionSheaf_obj`,
  `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.exists_isZero_obj`: the components are
  `l`-torsion and vanish below some index.

## Implementation notes

Freitag and Kiehl index by `ℤ` so that the shifted system `F[r] = (F_{n+r})_n` is again a
projective system for every `r ∈ ℤ`; we keep the `ℤ`-indexing for the same reason. The vanishing
`F_n = 0` is stated as `IsZero (F_n)`, the categorical meaning of a zero sheaf.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Projective systems of `l`-torsion sheaves.** A `ℤ`-indexed projective system
`F : ℤᵒᵖ ⥤ Sheaf (topology B S hS) AddCommGrpCat` of abelian sheaves on the small étale site of
`S` is a projective system of `l`-torsion sheaves if every component `F_n` is an `l`-torsion
sheaf and there is `n₀` with `F_n = 0` for all `n < n₀`. -/
@[weil "def_fk112_projective_system_l_torsion_sheaves"]
def IsLTorsionProjectiveSystem (l : ℕ) :
    ObjectProperty (ℤᵒᵖ ⥤ Sheaf (topology B S hS) AddCommGrpCat.{w}) :=
  fun F ↦ (∀ n : ℤ, IsLTorsionSheaf.{w} B S hS l (F.obj (op n))) ∧
    ∃ n₀ : ℤ, ∀ n : ℤ, n < n₀ → IsZero (F.obj (op n))

/-- **The category `P_S` of projective systems of `l`-torsion sheaves** on the small étale site
of `S`, the full subcategory of `ℤᵒᵖ ⥤ Sheaf (topology B S hS) AddCommGrpCat` of the systems
satisfying `IsLTorsionProjectiveSystem`. Its morphisms are the families of morphisms of sheaves
commuting with the transition maps (`IsLTorsionProjectiveSystem.naturality_iff`). -/
@[weil "def_fk112_projective_system_l_torsion_sheaves"]
abbrev LTorsionProjectiveSystem (l : ℕ) :=
  (IsLTorsionProjectiveSystem.{w} B S hS l).FullSubcategory

variable {B S hS}

namespace IsLTorsionProjectiveSystem

variable {C : Type*} [Category C]

/-- The transition map `F_n ⟶ F_{n-1}` of a `ℤ`-indexed projective system. -/
abbrev transitionMap (F : ℤᵒᵖ ⥤ C) (n : ℤ) : F.obj (op n) ⟶ F.obj (op (n - 1)) :=
  F.map (homOfLE (Int.sub_le_self n zero_le_one)).op

/-- **Morphisms of `ℤ`-indexed projective systems.** A family of morphisms
`f_n : F_n ⟶ G_n` is a natural transformation if and only if it commutes with the transition
maps: `u_n^G ∘ f_n = f_{n-1} ∘ u_n^F` for all `n`. -/
@[weil "def_fk112_projective_system_l_torsion_sheaves"]
theorem naturality_iff {F G : ℤᵒᵖ ⥤ C} (f : ∀ n : ℤ, F.obj (op n) ⟶ G.obj (op n)) :
    (∀ ⦃X Y : ℤᵒᵖ⦄ (φ : X ⟶ Y), F.map φ ≫ f Y.unop = f X.unop ≫ G.map φ) ↔
      ∀ n : ℤ, transitionMap F n ≫ f (n - 1) = f n ≫ transitionMap G n := by
  refine ⟨fun h n ↦ h _, fun h ↦ ?_⟩
  have step : ∀ a b : ℤ, ∀ (e : a = b - 1) (hab : a ≤ b),
      F.map (homOfLE hab).op ≫ f a = f b ≫ G.map (homOfLE hab).op := by
    intro a b e hab
    subst e
    exact h b
  have key : ∀ m n : ℤ, ∀ hmn : m ≤ n,
      F.map (homOfLE hmn).op ≫ f m = f n ≫ G.map (homOfLE hmn).op := by
    intro m n hmn
    induction n, hmn using Int.leInduction with
    | base => simp
    | succ n hmn ih =>
      have hc : (homOfLE (hmn.trans (Int.le_add_one le_rfl)) : m ⟶ n + 1) =
          homOfLE hmn ≫ homOfLE (Int.le_add_one le_rfl) := rfl
      rw [hc, op_comp, F.map_comp, G.map_comp, Category.assoc, ih, ← Category.assoc,
        step n (n + 1) (by omega), Category.assoc]
  intro X Y φ
  have hφ : φ = (homOfLE (leOfHom φ.unop)).op := rfl
  rw [hφ]
  exact key Y.unop X.unop (leOfHom φ.unop)

end IsLTorsionProjectiveSystem

namespace LTorsionProjectiveSystem

variable {l : ℕ}

/-- The transition map `u_n : F_n ⟶ F_{n-1}` of a projective system of `l`-torsion sheaves. -/
abbrev transition (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    F.obj.obj (op n) ⟶ F.obj.obj (op (n - 1)) :=
  IsLTorsionProjectiveSystem.transitionMap F.obj n

/-- The components of a projective system of `l`-torsion sheaves are `l`-torsion sheaves. -/
theorem isLTorsionSheaf_obj (F : LTorsionProjectiveSystem.{w} B S hS l) (n : ℤ) :
    IsLTorsionSheaf.{w} B S hS l (F.obj.obj (op n)) :=
  F.property.1 n

/-- A projective system of `l`-torsion sheaves vanishes below some index. -/
theorem exists_isZero_obj (F : LTorsionProjectiveSystem.{w} B S hS l) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n < n₀ → IsZero (F.obj.obj (op n)) :=
  F.property.2

/-- The object of `LTorsionProjectiveSystem` given by a `ℤ`-indexed system of `l`-torsion sheaves
vanishing below some index. -/
abbrev mk (F : ℤᵒᵖ ⥤ Sheaf (topology B S hS) AddCommGrpCat.{w})
    (hF : ∀ n : ℤ, IsLTorsionSheaf.{w} B S hS l (F.obj (op n)))
    (h₀ : ∃ n₀ : ℤ, ∀ n : ℤ, n < n₀ → IsZero (F.obj (op n))) :
    LTorsionProjectiveSystem.{w} B S hS l :=
  ⟨F, hF, h₀⟩

/-- A morphism of projective systems of `l`-torsion sheaves from a family of morphisms
`f_n : F_n ⟶ G_n` with `u_n^G ∘ f_n = f_{n-1} ∘ u_n^F` for all `n`. -/
def homMk {F G : LTorsionProjectiveSystem.{w} B S hS l}
    (f : ∀ n : ℤ, F.obj.obj (op n) ⟶ G.obj.obj (op n))
    (hf : ∀ n : ℤ, F.transition n ≫ f (n - 1) = f n ≫ G.transition n) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun X ↦ f X.unop
      naturality := (IsLTorsionProjectiveSystem.naturality_iff f).mpr hf }

@[simp]
theorem homMk_hom_app {F G : LTorsionProjectiveSystem.{w} B S hS l}
    (f : ∀ n : ℤ, F.obj.obj (op n) ⟶ G.obj.obj (op n))
    (hf : ∀ n : ℤ, F.transition n ≫ f (n - 1) = f n ≫ G.transition n) (n : ℤ) :
    (homMk f hf).hom.app (op n) = f n :=
  rfl

/-- A morphism of projective systems commutes with the transition maps. -/
@[reassoc]
theorem transition_comp {F G : LTorsionProjectiveSystem.{w} B S hS l} (f : F ⟶ G) (n : ℤ) :
    F.transition n ≫ f.hom.app (op (n - 1)) = f.hom.app (op n) ≫ G.transition n :=
  f.hom.naturality _

/-- Two morphisms of projective systems are equal when all their components are. -/
@[ext]
theorem hom_ext {F G : LTorsionProjectiveSystem.{w} B S hS l} {f g : F ⟶ G}
    (h : ∀ n : ℤ, f.hom.app (op n) = g.hom.app (op n)) : f = g := by
  ext1
  apply NatTrans.ext
  funext X
  exact h X.unop

end LTorsionProjectiveSystem

end AlgebraicGeometry.SmallEtale

end
