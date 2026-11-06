module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic

/-!
# The adjunction unit on stalks along a purely inseparable morphism

Let `f : X ⟶ Y` be a morphism in a big étale site, `x` a geometric point of `X`, `y = f ∘ x`,
and `G` a sheaf of sets on the small étale site of `Y`, with unit `η : G ⟶ f_* f^* G`. The
canonical stalk map `c_x : G_y ⟶ (f^* G)_x` is by definition the composite of the stalk map
`η_y` with the natural map `ε_x : (f_* f^* G)_y ⟶ (f^* G)_x`, and it is bijective. Hence
`c_x⁻¹ ∘ ε_x ∘ η_y` is the identity of `G_y`.

When `f` is purely inseparable, `x` is the unique geometric point of `X` over `y` and `ε_x` is
itself a bijection; the composite of the three bijections `η_y`, `ε_x` and `c_x⁻¹` is then the
identity, and in particular `η_y` is a bijection.

## Main results

* `AlgebraicGeometry.inverseImageStalkMap_symm_directImageStalkToFibreStalk_unit`: for every
  morphism, `c_x⁻¹ (ε_x (η_y z)) = z`.
* `AlgebraicGeometry.unit_stalk_trans_directImageStalkToFibreStalk_trans_inverseImageStalkMap_symm`:
  for a purely inseparable morphism, the composite of the bijections `η_y`, `ε_x` and `c_x⁻¹`
  is the identity of `G_y`.

## Implementation notes

The point `y` is written as the image `f ∘ x` of `x`; for a purely inseparable `f` every
geometric point of `Y` is of this form for a unique `x`
(`AlgebraicGeometry.Scheme.Hom.isPurelyInseparable_iff_existsUnique_comp_eq`). The identity
`c_x⁻¹ ∘ ε_x ∘ η_y = id` holds for an arbitrary morphism, since `c_x` is the composite
`ε_x ∘ η_y` and is bijective for every morphism.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FK]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- For any morphism `f`, a geometric point `x` of `X` and a sheaf of sets `G` on the small
étale site of `Y`, the stalk map of the unit `η_y`, followed by `ε_x` and by the inverse of the
bijection `c_x`, is the identity of `G_y`. -/
theorem inverseImageStalkMap_symm_directImageStalkToFibreStalk_unit (x : GeometricPoint X.1)
    (G : Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (max (u + 1) v)))
    (z : etaleStalk B Y.1 Y.property (x.map (B.inclusion.map f)) G.obj) :
    (Equiv.ofBijective _ (inverseImageStalkMap_bijective.{u, v} B f x G)).symm
      (directImageStalkToFibreStalk B f x _ rfl
        ((smallEtaleInverseImage B f (Type (max (u + 1) v))).obj G).obj
        ((etaleStalkFunctor.{u, max (u + 1) v} B Y.1 Y.property (x.map (B.inclusion.map f))).map
          ((smallEtaleInverseImageAdjunction B f (Type (max (u + 1) v))).unit.app G) z)) = z :=
  (Equiv.ofBijective _ (inverseImageStalkMap_bijective.{u, v} B f x G)).symm_apply_apply z

/-- **The adjunction unit on stalks along a purely inseparable morphism.** Let `f` be purely
inseparable, `x` a geometric point of `X` over `y = f ∘ x`, and `G` a sheaf of sets on the small
étale site of `Y`. The stalk map `η_y : G_y ⟶ (f_* f^* G)_y` of the unit is a bijection, and its
composite with the bijection `ε_x : (f_* f^* G)_y ⟶ (f^* G)_x` and the inverse of the bijection
`c_x : G_y ⟶ (f^* G)_x` is the identity of `G_y`. -/
@[weil "lem_fk103_purely_inseparable_adjunction_stalks_compatible"]
theorem unit_stalk_trans_directImageStalkToFibreStalk_trans_inverseImageStalkMap_symm
    (hf : (B.inclusion.map f).IsPurelyInseparable) (x : GeometricPoint X.1)
    (G : Sheaf (SmallEtale.topology B Y.1 Y.property) (Type (max (u + 1) v))) :
    ∃ hη : Function.Bijective
        ((etaleStalkFunctor.{u, max (u + 1) v} B Y.1 Y.property (x.map (B.inclusion.map f))).map
          ((smallEtaleInverseImageAdjunction B f (Type (max (u + 1) v))).unit.app G)),
      ((Equiv.ofBijective _ hη).trans
        ((Equiv.ofBijective _
          (bijective_directImageStalkToFibreStalk_of_isPurelyInseparable.{u, v} B f hf x _ rfl
            ((smallEtaleInverseImage B f (Type (max (u + 1) v))).obj G))).trans
          (Equiv.ofBijective _ (inverseImageStalkMap_bijective.{u, v} B f x G)).symm)) =
        Equiv.refl _ := by
  have hε := bijective_directImageStalkToFibreStalk_of_isPurelyInseparable.{u, v} B f hf x _ rfl
    ((smallEtaleInverseImage B f (Type (max (u + 1) v))).obj G)
  have hc := inverseImageStalkMap_bijective.{u, v} B f x G
  refine ⟨(Function.Bijective.of_comp_iff' hε _).mp hc, ?_⟩
  ext z
  exact inverseImageStalkMap_symm_directImageStalkToFibreStalk_unit B f x G z

end AlgebraicGeometry

end
