module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.ObjectProperty.ShiftNaturalMap

/-!
# Naturality of the natural map of a shifted projective system

For a projective system `F = (F_n, u_n)_{n ∈ ℤ}` of `l`-power torsion `Λ`-modules and `r ≥ 0`,
the natural map `ε^r_F : F[r] ⟶ F` is a morphism of projective systems, and for every morphism
`f : F ⟶ G` one has `f ∘ ε^r_F = ε^r_G ∘ f[r]`. Componentwise in degree `n` this is the identity
`f_n ∘ u^F_{n+1} ∘ ⋯ ∘ u^F_{n+r} = u^G_{n+1} ∘ ⋯ ∘ u^G_{n+r} ∘ f_{n+r}`.

## Main results

* `CategoryTheory.ProjectiveSystem.natMap_comp_eq_shift_map_comp_natMap`:
  `f ∘ ε^r_F = ε^r_G ∘ f[r]`.
* `CategoryTheory.ProjectiveSystem.natMap_comp_app`: its degree-`n` component.

## Implementation notes

That `ε^r_F` is a morphism `F[r] ⟶ F` of projective systems is the type of
`CategoryTheory.ProjectiveSystem.natMap`, which is the whiskering of the translation
`n ≤ n + r` of `ℤᵒᵖ` with `F`; naturality in `F` is then the naturality of `f` as a natural
transformation of functors `ℤᵒᵖ ⥤ ModuleCat Λ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

public section

universe v u

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- For `r ≥ 0`, the natural map `ε^r_F : F[r] ⟶ F` is natural in `F`:
`f ∘ ε^r_F = ε^r_G ∘ f[r]` for every morphism `f : F ⟶ G` of projective systems. -/
@[weil "lem_fk112_shift_natural_map_natural", reassoc]
theorem natMap_comp_eq_shift_map_comp_natMap {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G)
    (r : ℕ) : natMap F r ≫ f = (shift (r : ℤ)).map f ≫ natMap G r :=
  (natMap_naturality f r).symm

/-- The degree-`n` component of the naturality of `ε^r`:
`f_n ∘ ε^r_{F,n} = ε^r_{G,n} ∘ f_{n+r}`. -/
@[reassoc]
theorem natMap_comp_app {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) (r : ℕ) (n : ℤ) :
    app (natMap F r) n ≫ app f n = app f (n + r) ≫ app (natMap G r) n :=
  f.hom.naturality _

end ProjectiveSystem

end CategoryTheory
