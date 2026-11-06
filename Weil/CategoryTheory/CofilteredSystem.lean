module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.ObjectProperty.ShiftNaturalMap
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Systems of modules of finite length satisfy the Mittag-Leffler condition

Let `F = (F_n, u_n)` be a projective system of `Λ`-modules. If every `F_n` has finite length,
then `F` satisfies the Mittag-Leffler condition: for every `n` the images
`im(ε^r_{F,n} : F_{n+r} → F_n)` form a descending chain of submodules of `F_n`, which is
stationary because `F_n` is Artinian.

More generally, any cofiltered system of Artinian modules is Mittag-Leffler: the ranges of the
maps into a fixed term have a minimal element, and minimality together with cofilteredness shows
that this minimal range is contained in every other one.

## Main results

* `CategoryTheory.Functor.isMittagLeffler_of_isArtinian`: a cofiltered system
  `J ⥤ ModuleCat R` of Artinian modules satisfies the Mittag-Leffler condition.
* `CategoryTheory.ProjectiveSystem.isMittagLeffler_of_isFiniteLength`: a projective system all
  of whose terms have finite length satisfies the Mittag-Leffler condition.
* `CategoryTheory.ProjectiveSystem.exists_range_natMap_eq_of_isFiniteLength`: the same in the
  form of the source: for every `n` there is `t` such that the images of `ε^r_{F,n}` and
  `ε^t_{F,n}` in `F_n` agree for all `r ≥ t`.

## Implementation notes

The Mittag-Leffler condition is Mathlib's `CategoryTheory.Functor.IsMittagLeffler` of the
underlying system of sets `F ⋙ forget`; the range of a linear map is the set-theoretic range of
the underlying function. The source writes the condition with indices `m ≥ t ≥ n`; here the
shifts `r = m - n` and `t - n` are the natural numbers indexing the natural maps `ε^r_F`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

public section

universe v u w w'

open Opposite

namespace CategoryTheory

namespace Functor

/-- A cofiltered system of Artinian modules satisfies the Mittag-Leffler condition: the ranges
of the maps into a fixed term have a minimal element, which is contained in every other range. -/
theorem isMittagLeffler_of_isArtinian {J : Type w} [Category.{w'} J] [IsCofilteredOrEmpty J]
    {R : Type u} [Ring R] (F : J ⥤ ModuleCat.{v} R) (hF : ∀ j, IsArtinian R (F.obj j)) :
    (F ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler := by
  intro j
  obtain ⟨_, ⟨⟨i, f⟩, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule R (F.obj j))).has_min
    (Set.range fun p : Σ i, i ⟶ j => LinearMap.range (F.map p.2).hom) ⟨_, ⟨⟨j, 𝟙 j⟩, rfl⟩⟩
  refine ⟨i, f, fun k g => ?_⟩
  obtain ⟨l, a, b, hab⟩ := IsCofiltered.cospan f g
  have hle : LinearMap.range (F.map (a ≫ f)).hom ≤ LinearMap.range (F.map f).hom := by
    rw [F.map_comp, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  have heq : LinearMap.range (F.map (a ≫ f)).hom = LinearMap.range (F.map f).hom :=
    hle.eq_of_not_lt (hmin _ ⟨⟨l, a ≫ f⟩, rfl⟩)
  have hle' : LinearMap.range (F.map f).hom ≤ LinearMap.range (F.map g).hom := by
    rw [← heq, hab, F.map_comp, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨z, hz⟩ := hle' ⟨y, rfl⟩
  exact ⟨z, hz⟩

end Functor

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- A projective system all of whose terms `F_n` have finite length satisfies the
Mittag-Leffler condition. -/
@[weil "lem_fk112_finite_length_mittag_leffler"]
theorem isMittagLeffler_of_isFiniteLength (F : ProjectiveSystem.{v} Λ l)
    (hF : ∀ n : ℤ, IsFiniteLength Λ (F.term n)) :
    (F.obj ⋙ forget (ModuleCat.{v} Λ)).IsMittagLeffler :=
  Functor.isMittagLeffler_of_isArtinian F.obj fun n =>
    ((isFiniteLength_iff_isNoetherian_isArtinian).1 (hF n.unop)).2

/-- A projective system all of whose terms `F_n` have finite length satisfies the
Mittag-Leffler condition, in the form of the source: for every `n` there is `t` such that
`im(ε^r_{F,n} : F_{n+r} → F_n) = im(ε^t_{F,n} : F_{n+t} → F_n)` for all `r ≥ t`. -/
@[weil "lem_fk112_finite_length_mittag_leffler"]
theorem exists_range_natMap_eq_of_isFiniteLength (F : ProjectiveSystem.{v} Λ l)
    (hF : ∀ n : ℤ, IsFiniteLength Λ (F.term n)) (n : ℤ) :
    ∃ t : ℕ, ∀ r : ℕ, t ≤ r →
      LinearMap.range (app (natMap F r) n).hom = LinearMap.range (app (natMap F t) n).hom := by
  have : IsArtinian Λ (F.term n) := ((isFiniteLength_iff_isNoetherian_isArtinian).1 (hF n)).2
  have range_map_comp_le : ∀ {X Y : ℤᵒᵖ} (p : X ⟶ Y) (q : Y ⟶ op n),
      LinearMap.range (F.obj.map (p ≫ q)).hom ≤ LinearMap.range (F.obj.map q).hom := by
    intro X Y p q
    rw [F.obj.map_comp, ModuleCat.hom_comp]
    exact LinearMap.range_comp_le_range _ _
  let f : ℕ →o (Submodule Λ (F.term n))ᵒᵈ :=
    { toFun := fun r => OrderDual.toDual (LinearMap.range (app (natMap F r) n).hom)
      monotone' := by
        intro a b hab
        change LinearMap.range (app (natMap F b) n).hom ≤
          LinearMap.range (app (natMap F a) n).hom
        rw [natMap_app, natMap_app,
          show (homOfLE (by simp : n ≤ n + (b : ℕ))).op =
            (homOfLE (by simp [hab] : n + (a : ℕ) ≤ n + (b : ℕ))).op ≫
              (homOfLE (by simp : n ≤ n + (a : ℕ))).op from Subsingleton.elim _ _]
        exact range_map_comp_le _ _ }
  obtain ⟨t, ht⟩ := IsArtinian.monotone_stabilizes f
  exact ⟨t, fun r hr => congrArg OrderDual.ofDual (ht r hr).symm⟩

end ProjectiveSystem

end CategoryTheory
