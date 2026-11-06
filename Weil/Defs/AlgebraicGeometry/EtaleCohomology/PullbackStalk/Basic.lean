module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional

/-!
# The canonical map from a stalk to the stalk of an inverse image

Let `p : P ⟶ Q` be a morphism in a big étale site, `w` a geometric point of `P`, and `F` a sheaf
of sets on the small étale site of `Q`. The unit `η : F ⟶ p_* p^* F` of the adjunction
`p^* ⊣ p_*`, taken on stalks at `p ∘ w`, followed by the natural map
`ε_w : (p_* p^* F)_{p ∘ w} ⟶ (p^* F)_w` from the stalk of a direct image to the stalk at a point
of the fibre, is the *canonical stalk map*

  `c_w = ε_w ∘ η_{p ∘ w} : F_{p ∘ w} ⟶ (p^* F)_w`.

It is the inverse of the identification of stalks of inverse images of Stacks, Tag 03Q1
(`AlgebraicGeometry.smallEtalePullbackStalkIsoUniv`); in particular it is bijective.

## Main definitions

* `AlgebraicGeometry.inverseImageStalkMap`: the map `c_w : F_{p ∘ w} ⟶ (p^* F)_w`.

## Main results

* `AlgebraicGeometry.inverseImageStalkMap_eq_inv_app`: `c_w` is the inverse of the comparison
  `(p^* F)_w ≅ F_{p ∘ w}` of Tag 03Q1.

## Implementation notes

Geometric points are spectra of algebraically closed fields, and sheaves take values in
`Type (max (u + 1) v)`, where `u` is the universe of the big étale site.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FK]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {P Q : B.Scheme} (p : P ⟶ Q)

/-- **The canonical stalk map `c_w : F_{p ∘ w} ⟶ (p^* F)_w`.** For a geometric point `w` of `P`
and a sheaf of sets `F` on the small étale site of `Q`, the composite of the unit
`F ⟶ p_* p^* F` on stalks at `p ∘ w` with the natural map
`ε_w : (p_* p^* F)_{p ∘ w} ⟶ (p^* F)_w` (`AlgebraicGeometry.directImageStalkToFibreStalk`). -/
@[weil "def_fk103_inverse_image_stalk_map"]
def inverseImageStalkMap (w : GeometricPoint P.1)
    (F : Sheaf (SmallEtale.topology B Q.1 Q.property) (Type (max (u + 1) v))) :
    etaleStalk B Q.1 Q.property (w.map (B.inclusion.map p)) F.obj →
      etaleStalk B P.1 P.property w
        ((smallEtaleInverseImage B p (Type (max (u + 1) v))).obj F).obj :=
  fun z => directImageStalkToFibreStalk B p w _ rfl
    ((smallEtaleInverseImage B p (Type (max (u + 1) v))).obj F).obj
    ((etaleStalkFunctor.{u, max (u + 1) v} B Q.1 Q.property (w.map (B.inclusion.map p))).map
      ((smallEtaleInverseImageAdjunction B p (Type (max (u + 1) v))).unit.app F) z)

/-- **`c_w` is the inverse of the comparison of Tag 03Q1.** The canonical stalk map is the
inverse of the identification `(p^* F)_w ≅ F_{p ∘ w}` of
`AlgebraicGeometry.smallEtalePullbackStalkIsoUniv`. -/
theorem inverseImageStalkMap_eq_inv_app (w : GeometricPoint P.1)
    (F : Sheaf (SmallEtale.topology B Q.1 Q.property) (Type (max (u + 1) v))) :
    inverseImageStalkMap B p w F = (smallEtalePullbackStalkIsoUniv.{u, v} B p w).inv.app F := by
  funext z
  simp only [inverseImageStalkMap]
  rw [directImageStalkToFibreStalk_eq_pushforwardEtaleStalkComponentUniv]
  exact pushforwardEtaleStalkComponent_unit_univ B p w F z

end AlgebraicGeometry

end
