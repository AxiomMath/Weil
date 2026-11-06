module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import Weil.Attr
public import Weil.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk

/-!
# Finite morphisms have finite geometric fibres

Let `f : X ⟶ Y` be a finite morphism of schemes and `y : Spec k ⟶ Y` a morphism from the
spectrum of a field. Then there are only finitely many `x : Spec k ⟶ X` with `x ≫ f = y`.
In particular, a geometric point of `Y` has only finitely many lifts to `X` with the same
field of values.

## Main results

* `AlgebraicGeometry.IsFinite.finite_lifts_spec_field`: finitely many lifts of a morphism
  from the spectrum of any field through a finite morphism.
* `AlgebraicGeometry.IsFinite.finite_geometricPoint_lifts`: finitely many lifts of a geometric
  point through a finite morphism.

## Implementation notes

The statement is proved for an arbitrary field `k`, which contains the source's case of a
separably closed field as well as the algebraically closed geometric points of
`AlgebraicGeometry.GeometricPoint`. The lifts are the sections of the base change
`X ×_Y Spec k ⟶ Spec k`, a finite morphism to the spectrum of a field, whose sections
correspond to `k`-algebra maps from a finite-dimensional `k`-algebra to `k`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace IsFinite

/-- Through a finite morphism `f : X ⟶ Y`, a morphism `y : Spec k ⟶ Y` from the spectrum of a
field has only finitely many lifts `x : Spec k ⟶ X` with `x ≫ f = y`. -/
@[weil "lem_fk103_finite_geometric_fibre_finite"]
theorem finite_lifts_spec_field {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (k : Type u) [Field k] (y : Spec (.of k) ⟶ Y) :
    Finite {x : Spec (.of k) ⟶ X // x ≫ f = y} :=
  finite_lifts_of_isFinite f y

/-- Through a finite morphism, a geometric point has only finitely many lifts with the same
field of values. -/
theorem finite_geometricPoint_lifts {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (y : GeometricPoint Y) :
    Finite {x : y.source ⟶ X // x ≫ f = y.hom} :=
  finite_lifts_spec_field f y.residueField y.hom

end IsFinite

end AlgebraicGeometry

end

/-! ### Stalks of direct images along purely inseparable morphisms -/

/-!
# Stalks of direct images along purely inseparable morphisms

Let `f : X ⟶ Y` be a purely inseparable morphism (finite, universally injective and
surjective), `x` a geometric point of `X` and `y = f ∘ x`. Then `x` is the only geometric point
of `X` with the residue field of `y` lying over `y`, so the stalk of a direct image `f_* F` at
`y`, which for a finite morphism is the product of the stalks of `F` at the lifts of `y`, is the
stalk of `F` at `x`: the natural map `ε_x : (f_* F)_y ⟶ F_x` is bijective.

## Main results

* `AlgebraicGeometry.bijective_directImageStalkToFibreStalk_of_isPurelyInseparable`: for a
  purely inseparable `f` and a sheaf of sets `F` on the small étale site of `X`, the map
  `ε_x : (f_* F)_y ⟶ F_x` is bijective.

## Implementation notes

Geometric points are spectra of algebraically closed fields, and sheaves of sets take values in
`Type (max (u + 1) v)`, where `u` is the universe of the schemes. The proof reduces to the
bijectivity of the comparison map to the product of stalks over the lifts of `y`
(`AlgebraicGeometry.finitePushforwardStalkToProduct_bijective_univ`, Tag 03QP), over a
one-element index set by
`AlgebraicGeometry.Scheme.Hom.isPurelyInseparable_iff_existsUnique_comp_eq`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FK]
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- **Stalks of direct images along a purely inseparable morphism.** For a purely inseparable
morphism `f : X ⟶ Y`, a geometric point `x` of `X` with `f ∘ x = y` and a sheaf of sets `F` on
the small étale site of `X`, the natural map `ε_x : (f_* F)_y ⟶ F_x` is bijective. -/
@[weil "lem_fk103_purely_inseparable_direct_image_stalk_iso"]
theorem bijective_directImageStalkToFibreStalk_of_isPurelyInseparable
    (hf : (B.inclusion.map f).IsPurelyInseparable)
    (x : GeometricPoint X.1) (y : GeometricPoint Y.1) (h : x.map (B.inclusion.map f) = y)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    Function.Bijective (directImageStalkToFibreStalk B f x y h F.obj) := by
  subst h
  have : IsFinite (B.inclusion.map f) := hf.1
  rw [directImageStalkToFibreStalk_eq_pushforwardEtaleStalkComponentUniv]
  let x₀ : {g : (x.map (B.inclusion.map f)).source ⟶ X.1 //
      g ≫ B.inclusion.map f = (x.map (B.inclusion.map f)).hom} := ⟨x.hom, rfl⟩
  obtain ⟨_, -, huniq⟩ :=
    (Scheme.Hom.isPurelyInseparable_iff_existsUnique_comp_eq _).mp hf x.residueField
      (x.hom ≫ B.inclusion.map f)
  let : Unique {g : (x.map (B.inclusion.map f)).source ⟶ X.1 //
      g ≫ B.inclusion.map f = (x.map (B.inclusion.map f)).hom} :=
    { default := x₀
      uniq := fun g => Subtype.ext ((huniq g.1 g.2).trans (huniq x.hom rfl).symm) }
  have hb := (Equiv.piUnique _).bijective.comp
    (finitePushforwardStalkToProduct_bijective_univ B f (x.map (B.inclusion.map f)) F)
  have he : (Equiv.piUnique _) ∘ finitePushforwardStalkToProductUniv.{u, v} B f
      (x.map (B.inclusion.map f)) F =
      pushforwardEtaleStalkComponentUniv.{u, v} B f x (x.map (B.inclusion.map f)) rfl F := rfl
  exact he ▸ hb

end AlgebraicGeometry

end
