/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Weil.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRing
public import Weil.Attr

/-!
# The strict local ring is the Henselization along the geometric point, compatibly

Let `z : Spec k ⟶ Z` be a geometric point of a scheme `Z`, with underlying point `z₀`, let
`R = 𝒪_{Z,z₀}` and let `ζ : R → k` be the local homomorphism given by `z`. The strict local ring
`𝒪̃_{Z,z}` carries the map `R → 𝒪̃_{Z,z}` given by the Zariski open neighbourhoods of `z₀` and the
evaluation `z̃ : 𝒪̃_{Z,z} → k` at the lifts of `z`. If `(R̃, ψ)` is a Henselization of `R` with
respect to `ζ`, there is a ring isomorphism `ξ : R̃ ≃ 𝒪̃_{Z,z}` which is a homomorphism of
`R`-algebras and satisfies `z̃ ∘ ξ = ψ`.

## Main results

* `AlgebraicGeometry.exists_ringEquiv_strictLocalRing_of_isHenselizationAlong`: the comparison
  `ξ`, stated with the map `R → 𝒪̃_{Z,z}` and the evaluation `z̃` written out.

## Implementation notes

The map `R → 𝒪̃_{Z,z}` is `AlgebraicGeometry.structureSheafStalkFromLocalRing`, which is the
structure map of the `R`-algebra `𝒪̃_{Z,z}`, and the evaluation is
`AlgebraicGeometry.structureSheafStalkToGeometricField`; `ζ` is
`AlgebraicGeometry.Scheme.stalkClosedPointTo`. The result is a restatement of
`AlgebraicGeometry.exists_algEquiv_strictLocalRing`. No noetherian hypothesis is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

public section

open CategoryTheory IsLocalRing

universe u w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Z : Scheme.{u}) (hZ : B.Contains Z) (z : GeometricPoint Z)

/-- **The strict local ring is the Henselization along the geometric point.** Let `z` be a
geometric point of `Z` with underlying point `z₀`, `R = 𝒪_{Z,z₀}`, `ζ : R → k` the local
homomorphism given by `z`, and `(Rh, ψ)` a Henselization of `R` with respect to `ζ`. Then there is
a ring isomorphism `ξ : Rh ≃ 𝒪̃_{Z,z}` to the strict local ring which is a homomorphism of
`R`-algebras, for the map `R → 𝒪̃_{Z,z}` given by the Zariski open neighbourhoods of `z₀`, and
satisfies `z̃ ∘ ξ = ψ` for the evaluation `z̃ : 𝒪̃_{Z,z} → k` at the lifts of `z`. -/
@[weil "lem_fk103_strict_local_ring_compatible_henselization"]
theorem exists_ringEquiv_strictLocalRing_of_isHenselizationAlong
    {Rh : Type w} [CommRing Rh] [IsLocalRing Rh]
    [Algebra (Z.presheaf.stalk (z.hom (closedPoint z.residueField))) Rh]
    {ψ : Rh →+* z.residueField}
    (h : IsLocalRing.IsHenselizationAlong (Scheme.stalkClosedPointTo z.hom).hom Rh ψ) :
    ∃ ξ : Rh ≃+* strictLocalRing B Z hZ z,
      (∀ r, ξ (algebraMap _ Rh r) = structureSheafStalkFromLocalRing B Z hZ z r) ∧
        ∀ a, structureSheafStalkToGeometricField B Z hZ z (ξ a) = ψ a := by
  obtain ⟨θ, hθ⟩ := exists_algEquiv_strictLocalRing B Z hZ z h
  exact ⟨θ.toRingEquiv, fun r => θ.commutes r, hθ⟩

end AlgebraicGeometry
