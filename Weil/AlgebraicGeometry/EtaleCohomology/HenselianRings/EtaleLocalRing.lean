/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings
public import Weil.Defs.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import Weil.RingTheory.Henselian.Henselization.LocalEtaleOverPolynomialStrictHenselization

/-!
# The strict local ring is the Henselization along the geometric point

Let `x : Spec k → X` be a geometric point of a scheme `X`, with `k` algebraically closed, lying
over the point `x₀` of `X`. Let `A = 𝒪_{X,x₀}` be the local ring at `x₀` and let
`φ : A → κ(x₀) → k` be the map induced by `x`. The strict local ring `𝒪̃_{X,x}` is an `A`-algebra
through the germ maps of Zariski neighbourhoods of `x₀`, and it carries the evaluation map
`𝒪̃_{X,x} → k` of étale germs at `x`. This file shows that, with these two maps, `𝒪̃_{X,x}` is a
Henselization of `A` with respect to `φ`. As Henselizations along `φ` are unique up to unique
isomorphism, `𝒪̃_{X,x}` is isomorphic, as an `A`-algebra and compatibly with the maps to `k`, to
every Henselization of `A` with respect to `φ`.

## Main results

* `AlgebraicGeometry.isHenselizationAlong_strictLocalRing`: the strict local ring of `X` at `x`
  is a Henselization of `𝒪_{X,x₀}` with respect to `φ`.
* `AlgebraicGeometry.exists_algEquiv_strictLocalRing`: every Henselization of `𝒪_{X,x₀}` with
  respect to `φ` is isomorphic to the strict local ring, as an `𝒪_{X,x₀}`-algebra and
  compatibly with the maps to `k`.

## Implementation notes

The source proves the comparison by constructing a map from the colimit over étale
neighbourhoods to the colimit over the local-étale `A`-algebras augmented to `k`, and checking
that it is bijective. Here the comparison is obtained from the identification of the étale local
ring with the strict henselization of `𝒪_{X,x₀}` with residue field the separable closure of
`κ(x₀)` in `k` (Stacks 04HX), which is exactly the residue field prescribed for the Henselization
with respect to `φ`, together with the uniqueness of henselizations (Stacks 08HT).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.2
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 08HT](https://stacks.math.columbia.edu/tag/08HT)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u v w w'

namespace IsLocalRing.IsHenselizationAlong

variable {A : Type u} [CommRing A] [IsLocalRing A] {k : Type v} [Field k] {φ : A →+* k}
  [IsLocalHom φ]

/-- The identification of the residue field of a Henselization `(Ã, ψ)` of `A` with respect to
`φ` with the separable closure `κ_φ` of the residue field of `A` in `k`, induced by `ψ`. -/
def residueFieldEquiv {Ã : Type w} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã] {ψ : Ã →+* k}
    (h : IsHenselizationAlong φ Ã ψ) : residueSeparableClosure φ ≃+* ResidueField Ã :=
  haveI := h.isLocalHom_ψ
  (RingEquiv.ofBijective ((ResidueField.lift ψ).codRestrict (residueSeparableClosure φ)
    fun y => by
      obtain ⟨a, rfl⟩ := residue_surjective y
      rw [ResidueField.lift_residue_apply]
      exact (Subfield.mem_toSubring _ _).1 (h.range_ψ ▸ ⟨a, rfl⟩))
    ⟨fun y z hyz => (ResidueField.lift ψ).injective (congrArg Subtype.val hyz), fun y => by
      obtain ⟨a, ha⟩ : (y : k) ∈ ψ.range := h.range_ψ ▸ (Subfield.mem_toSubring _ _).2 y.2
      exact ⟨residue Ã a, Subtype.ext ((ResidueField.lift_residue_apply ψ a).trans ha)⟩⟩).symm

theorem coe_residueFieldEquiv_symm_residue {Ã : Type w} [CommRing Ã] [IsLocalRing Ã]
    [Algebra A Ã] {ψ : Ã →+* k} (h : IsHenselizationAlong φ Ã ψ) (a : Ã) :
    (h.residueFieldEquiv.symm (residue Ã a) : k) = ψ a := by
  have := h.isLocalHom_ψ
  exact ResidueField.lift_residue_apply ψ a

end IsLocalRing.IsHenselizationAlong

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)

/-- **The strict local ring is the Henselization along the geometric point.** Let `x` be a
geometric point of `X` with underlying point `x₀`, let `A = 𝒪_{X,x₀}` and let `φ : A → k` be the
map `A → κ(x₀) → k` given by `x`. The strict local ring `𝒪̃_{X,x}`, an `A`-algebra through the
germ maps of Zariski neighbourhoods of `x₀`, together with the evaluation of étale germs at `x`,
is a Henselization of `A` with respect to `φ`. -/
@[weil "lem_fk102_strict_local_ring_is_strict_henselization"]
theorem isHenselizationAlong_strictLocalRing :
    IsLocalRing.IsHenselizationAlong (Scheme.stalkClosedPointTo x.hom).hom
      (strictLocalRing B X hX x) (structureSheafStalkToGeometricField B X hX x) := by
  refine ⟨?_, ?_⟩
  · -- the residue field prescribed by `φ` is the separable closure of `κ(x₀)` in `k`
    let e : IsLocalRing.residueSeparableClosure (Scheme.stalkClosedPointTo x.hom).hom ≃ₐ[
        ResidueField (X.presheaf.stalk (x.hom (closedPoint x.residueField)))]
        separableClosure (ResidueField (X.presheaf.stalk (x.hom (closedPoint x.residueField))))
          x.residueField :=
      { RingEquiv.refl _ with commutes' := fun _ => rfl }
    have := IsLocalRing.IsHenselization.of_residueAlgEquiv e.symm
      (Rh := (geometricHenselizationTower X x).strictHenselization)
    let ψ := etaleLocalRingAlgEquivStrictHenselization B X hX x
    have hs := etaleLocalRing_strictHenselian B X hX x
    refine ⟨inferInstance, indEtale_etaleLocalRing B X hX x, ?_⟩
    obtain ⟨q, hq⟩ := IsHenselization.exists_residueFieldEquiv
      (R := X.presheaf.stalk (x.hom (closedPoint x.residueField)))
      (L := IsLocalRing.residueSeparableClosure (Scheme.stalkClosedPointTo x.hom).hom)
      (Rh := (geometricHenselizationTower X x).strictHenselization)
    have hloc : IsLocalHom ψ.toRingEquiv.toRingHom :=
      IsLocalHom.of_surjective ψ.toRingEquiv.toRingHom ψ.toRingEquiv.surjective
    refine ⟨q.trans (ResidueField.mapEquiv ψ.toRingEquiv), fun r => ?_⟩
    rw [RingEquiv.trans_apply, hq]
    exact (ResidueField.map_residue ψ.toRingEquiv.toRingHom _).trans
      (congrArg (residue _) (ψ.commutes r))
  · exact congrArg CommRingCat.Hom.hom (ofHom_toGeometricField_comp_fromLocalRing B X hX x)

/-- **The strict local ring is isomorphic to the Henselization along the geometric point.**
Every Henselization `(Ã, ψ)` of `A = 𝒪_{X,x₀}` with respect to `φ : A → κ(x₀) → k` is
isomorphic, as an `A`-algebra, to the strict local ring `𝒪̃_{X,x}`, by an isomorphism carrying
`ψ` to the evaluation of étale germs at `x`. -/
@[weil "lem_fk102_strict_local_ring_is_strict_henselization"]
theorem exists_algEquiv_strictLocalRing {Ã : Type w} [CommRing Ã] [IsLocalRing Ã]
    [Algebra (X.presheaf.stalk (x.hom (closedPoint x.residueField))) Ã] {ψ : Ã →+* x.residueField}
    (h : IsLocalRing.IsHenselizationAlong (Scheme.stalkClosedPointTo x.hom).hom Ã ψ) :
    ∃ e : Ã ≃ₐ[X.presheaf.stalk (x.hom (closedPoint x.residueField))] strictLocalRing B X hX x,
      ∀ a, structureSheafStalkToGeometricField B X hX x (e a) = ψ a :=
  h.exists_algEquiv (isHenselizationAlong_strictLocalRing B X hX x)

end AlgebraicGeometry
