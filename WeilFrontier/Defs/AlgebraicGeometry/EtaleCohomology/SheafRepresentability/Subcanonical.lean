module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import Weil.Attr

/-!
# The sheaf represented by an object of the small étale site

Let `S` be a scheme and `Y` an object of the small étale site of `S`. The sheaf represented by
`Y`, written `Ỹ`, is the presheaf `U ↦ Hom_S(U, Y)` on the small étale site, with restriction
along a morphism `h : V ⟶ U` given by precomposition `a ↦ a ∘ h`. It is a sheaf because the
small étale topology is subcanonical.

## Main definitions

* `AlgebraicGeometry.SmallEtale.representedSheaf`: the sheaf `Ỹ` represented by `Y`, the value
  at `Y` of the Yoneda embedding `AlgebraicGeometry.smallEtaleYoneda` of the small étale site
  into its topos.

## Main results

* `AlgebraicGeometry.SmallEtale.representedSheaf_obj`: the sections of `Ỹ` over `U` are the
  morphisms `U ⟶ Y`.
* `AlgebraicGeometry.SmallEtale.representedSheaf_map`: restriction along `h : V ⟶ U` is
  precomposition with `h`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §3.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The sheaf `Ỹ` on the small étale site of `S` represented by an object `Y`: its sections
over `U` are the morphisms `U ⟶ Y` of the small étale site, and restriction is precomposition.
-/
@[weil "not_fk103_represented_sheaf"]
noncomputable abbrev representedSheaf (Y : SmallEtale B S hS) : smallEtaleTopos.{u, u} B S hS :=
  (smallEtaleYoneda B S hS).obj Y

/-- The sections of the represented sheaf `Ỹ` over `U` are the morphisms `U ⟶ Y`. -/
@[weil "not_fk103_represented_sheaf"]
theorem representedSheaf_obj (Y U : SmallEtale B S hS) :
    (representedSheaf Y).obj.obj (op U) = (U ⟶ Y) :=
  rfl

/-- Restriction in the represented sheaf `Ỹ` along `h : V ⟶ U` is precomposition with `h`. -/
@[weil "not_fk103_represented_sheaf"]
theorem representedSheaf_map (Y : SmallEtale B S hS) {U V : SmallEtale B S hS} (h : V ⟶ U)
    (a : (representedSheaf Y).obj.obj (op U)) :
    (representedSheaf Y).obj.map h.op a = h ≫ (show U ⟶ Y from a) :=
  rfl

end AlgebraicGeometry.SmallEtale

end
