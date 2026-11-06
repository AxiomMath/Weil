module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.ObjectProperty.ShiftNaturalMap

/-!
# Composites of natural maps of shifted projective systems

For a projective system `F = (F_n, u_n)_{n ∈ ℤ}` of `l`-power torsion `Λ`-modules and integers
`r, s ≥ 0`, the natural maps `ε^r_F : F[r] ⟶ F` compose as
`ε^r_F ∘ ε^s_{F[r]} = ε^{r+s}_F`, where `F[r][s]` is identified with `F[r+s]` by the canonical
isomorphism `shiftAdd`. In degree `n` both sides are the composite
`u_{n+1} ∘ ⋯ ∘ u_{n+r+s} : F_{n+r+s} ⟶ F_n`.

## Main results

* `CategoryTheory.ProjectiveSystem.natMap_shift_comp_natMap`:
  `ε^s_{F[r]} ≫ ε^r_F = ε^{r+s}_F`, up to the identification `F[r][s] ≅ F[r+s]`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The component of `eqToHom` is `eqToHom`. -/
lemma app_eqToHom {F G : ProjectiveSystem.{v} Λ l} (h : F = G) (n : ℤ) :
    app (eqToHom h) n = eqToHom (by rw [h]) := by
  subst h
  rfl

/-- The natural maps compose: `ε^r_F ∘ ε^s_{F[r]} = ε^{r+s}_F`, where the source `F[r][s]` of
the left side is identified with the source `F[r+s]` of the right side by the canonical
isomorphism `shiftAdd` (and `F[↑r + ↑s] = F[↑(r + s)]`). -/
@[weil "lem_fk112_shift_natural_map_composite", reassoc]
theorem natMap_shift_comp_natMap (F : ProjectiveSystem.{v} Λ l) (r s : ℕ) :
    natMap ((shift (r : ℤ)).obj F) s ≫ natMap F r =
      (shiftAdd (r : ℤ) (s : ℤ)).inv.app F ≫
        eqToHom (congrArg (fun k : ℤ => (shift k).obj F) (Nat.cast_add r s).symm) ≫
          natMap F (r + s) := by
  refine hom_ext fun n => ?_
  rw [comp_app, natMap_shift_comp_natMap_app, comp_app, comp_app, shiftAdd_inv_app_app,
    app_eqToHom, eqToHom_trans_assoc]
  rfl


end ProjectiveSystem

end CategoryTheory
