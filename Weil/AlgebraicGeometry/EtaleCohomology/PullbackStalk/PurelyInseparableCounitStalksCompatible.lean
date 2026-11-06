module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.AdjunctionCounit
public import Weil.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic

/-!
# The counit on stalks

Let `f : X ⟶ Y` be a morphism in a big étale site, `x` a geometric point of `X` and
`y = f ∘ x`, and let `F` be a sheaf of sets on the small étale site of `X` with counit
`θ : f^* f_* F ⟶ F`. Then the stalk map `θ_x : (f^* f_* F)_x ⟶ F_x`, preceded by the canonical
stalk map `c_x : (f_* F)_y ⟶ (f^* f_* F)_x`, is the natural map `ε_x : (f_* F)_y ⟶ F_x` from
the stalk of the direct image to the stalk at the point `x` of the fibre:

  `θ_x ∘ c_x = ε_x`.

Indeed `c_x = ε_x^{f^* f_* F} ∘ (η_{f_* F})_y`, the map `ε_x` is natural in the sheaf, and
`f_* θ ∘ η_{f_* F} = id` is the defining property of the counit.

For a purely inseparable `f` all three maps are bijections
(`AlgebraicGeometry.inverseImageStalkMap_bijective`,
`AlgebraicGeometry.bijective_directImageStalkToFibreStalk_of_isPurelyInseparable`).

## Main results

* `AlgebraicGeometry.etaleStalkFunctor_map_comp_inverseImageStalkMap_of_isSmallEtaleCounit`:
  `θ_x ∘ c_x = ε_x` for any counit `θ`.
* `AlgebraicGeometry.etaleStalkFunctor_map_counit_comp_inverseImageStalkMap`: the same for the
  counit of the adjunction `f^* ⊣ f_*`.

## Implementation notes

The identity holds for every morphism `f` of the big étale site; the source states it for a
purely inseparable `f`, where `x` is the unique geometric point over `y`. Geometric points are
spectra of algebraically closed fields, and sheaves of sets take values in
`Type (max (u + 1) v)`, where `u` is the universe of the big étale site.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FK]
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (f : X ⟶ Y)

/-- **The counit on stalks.** For a morphism `f : X ⟶ Y` of a big étale site, a geometric point
`x` of `X`, a sheaf of sets `F` on the small étale site of `X` and a counit
`θ : f^* f_* F ⟶ F`, the stalk map `θ_x` preceded by the canonical stalk map
`c_x : (f_* F)_{f ∘ x} ⟶ (f^* f_* F)_x` is the natural map `ε_x : (f_* F)_{f ∘ x} ⟶ F_x`. -/
@[weil "lem_fk103_purely_inseparable_counit_stalks_compatible"]
theorem etaleStalkFunctor_map_comp_inverseImageStalkMap_of_isSmallEtaleCounit
    (x : GeometricPoint X.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v)))
    (θ : (smallEtaleInverseImage B f (Type (max (u + 1) v))).obj
      (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)).obj F) ⟶
        F)
    (hθ : IsSmallEtaleCounit B f F θ) :
    (etaleStalkFunctor.{u, max (u + 1) v} B X.1 X.property x).map θ ∘
        inverseImageStalkMap.{u, v} B f x
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).obj F) =
      directImageStalkToFibreStalk B f x _ rfl F.obj := by
  funext z
  have hn := directImageStalkToFibreStalk_natural B f x _ rfl θ.hom
    ((etaleStalkFunctor.{u, max (u + 1) v} B Y.1 Y.property (x.map (B.inclusion.map f))).map
      ((smallEtaleInverseImageAdjunction B f (Type (max (u + 1) v))).unit.app
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).obj F)) z)
  refine hn.symm.trans ?_
  congr 1
  have h2 : (etaleStalkFunctor.{u, max (u + 1) v} B Y.1 Y.property
      (x.map (B.inclusion.map f))).map
        ((smallEtaleInverseImageAdjunction B f (Type (max (u + 1) v))).unit.app
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).obj F)) ≫
      (etaleStalkFunctor.{u, max (u + 1) v} B Y.1 Y.property
        (x.map (B.inclusion.map f))).map
        (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).map θ) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hθ, CategoryTheory.Functor.map_id]
  exact ConcreteCategory.congr_hom h2 z

/-- **The counit of `f^* ⊣ f_*` on stalks.** The stalk at `x` of the counit of the adjunction,
preceded by the canonical stalk map `c_x`, is the natural map `ε_x : (f_* F)_{f ∘ x} ⟶ F_x`. -/
theorem etaleStalkFunctor_map_counit_comp_inverseImageStalkMap (x : GeometricPoint X.1)
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (max (u + 1) v))) :
    (etaleStalkFunctor.{u, max (u + 1) v} B X.1 X.property x).map
        ((smallEtaleInverseImageAdjunction B f (Type (max (u + 1) v))).counit.app F) ∘
        inverseImageStalkMap.{u, v} B f x
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (max (u + 1) v))
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).obj F) =
      directImageStalkToFibreStalk B f x _ rfl F.obj :=
  etaleStalkFunctor_map_comp_inverseImageStalkMap_of_isSmallEtaleCounit f x F _
    (isSmallEtaleCounit_counit_app F)

end AlgebraicGeometry

end
