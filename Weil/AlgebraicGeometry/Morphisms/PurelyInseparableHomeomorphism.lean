/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Weil.Defs.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Purely inseparable morphisms are homeomorphisms

A (finite) purely inseparable morphism of schemes `f : X ⟶ Y` is a homeomorphism of the
underlying topological spaces: it is continuous and bijective on points, and it is closed since
finite morphisms are universally closed (by lying over and going up for integral extensions).

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsPurelyInseparable.isHomeomorph`: a purely inseparable morphism
  is a homeomorphism on the underlying spaces.
* `AlgebraicGeometry.Scheme.Hom.IsPurelyInseparable.homeomorph`: the induced homeomorphism.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §3.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A purely inseparable morphism of schemes is a homeomorphism of the underlying topological
spaces. -/
@[weil "lem_fk103_purely_inseparable_homeomorphism"]
theorem IsPurelyInseparable.isHomeomorph (hf : f.IsPurelyInseparable) : IsHomeomorph f := by
  have : IsFinite f := hf.isFinite
  exact (isHomeomorph_iff_continuous_isClosedMap_bijective).mpr
    ⟨f.continuous, f.isClosedMap, hf.bijective⟩

/-- The homeomorphism of underlying spaces induced by a purely inseparable morphism. -/
noncomputable def IsPurelyInseparable.homeomorph (hf : f.IsPurelyInseparable) : X ≃ₜ Y :=
  hf.isHomeomorph.homeomorph f

@[simp]
theorem IsPurelyInseparable.homeomorph_apply (hf : f.IsPurelyInseparable) (x : X) :
    hf.homeomorph x = f x :=
  rfl

/-- A purely inseparable morphism of schemes is an open map. -/
theorem IsPurelyInseparable.isOpenMap (hf : f.IsPurelyInseparable) : IsOpenMap f :=
  hf.isHomeomorph.isOpenMap

end AlgebraicGeometry.Scheme.Hom
