/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Weil.Attr

/-!
# Purely inseparable morphisms of schemes

Following Freitag–Kiehl, a finite morphism of schemes `f : X ⟶ Y` is *purely inseparable* if over
each point `y` of `Y` there lies exactly one point `x` of `X`, and the residue field extension
`κ(x)/κ(y)` is purely inseparable.

By Stacks 01S4 (`AlgebraicGeometry.tfae_universallyInjective`), a morphism is injective on points
with purely inseparable residue field extensions if and only if it is universally injective.
Hence a finite purely inseparable morphism is the same as a morphism which is finite,
universally injective and surjective, and this is how we define it, so that the stability of
`IsFinite`, `UniversallyInjective` and `Surjective` under base change and composition applies.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsPurelyInseparable`: `f` is finite, universally injective and
  surjective.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPurelyInseparable_iff`: `f` is purely inseparable if and only if
  it is finite, every point of `Y` has exactly one preimage, and all residue field extensions
  `κ(x)/κ(f x)` are purely inseparable.

## Implementation notes

The notion is only defined in the source for finite morphisms; finiteness is therefore part of
the definition.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §3.
* [Stacks, Tag 01S4]
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is (finite and) *purely inseparable* if it is finite,
universally injective and surjective. By `isPurelyInseparable_iff`, this means that `f` is finite,
each point of `Y` has exactly one preimage `x`, and `κ(x)/κ(f x)` is purely inseparable. -/
@[weil "def_fk103_purely_inseparable_morphism"]
abbrev IsPurelyInseparable : Prop :=
  IsFinite f ∧ UniversallyInjective f ∧ Surjective f

/-- A morphism of schemes is purely inseparable if and only if it is finite, bijective on the
underlying points, and all residue field extensions are purely inseparable. -/
@[weil "def_fk103_purely_inseparable_morphism"]
theorem isPurelyInseparable_iff :
    f.IsPurelyInseparable ↔ IsFinite f ∧ (∀ y : Y, ∃! x : X, f x = y) ∧
      ∀ x : X, (f.residueFieldMap x).hom.IsPurelyInseparable := by
  have h := (tfae_universallyInjective f).out 1 3
  constructor
  · rintro ⟨hfin, hinj, hsurj⟩
    obtain ⟨hi, hr⟩ := h.mp hinj
    refine ⟨hfin, fun y ↦ ?_, hr⟩
    obtain ⟨x, rfl⟩ := hsurj.surj y
    exact ⟨x, rfl, fun x' hx' ↦ hi hx'⟩
  · rintro ⟨hfin, hbij, hr⟩
    have hbij' : Function.Bijective f := Function.bijective_iff_existsUnique _ |>.mpr hbij
    exact ⟨hfin, h.mpr ⟨hbij'.1, hr⟩, ⟨hbij'.2⟩⟩

variable {f}

theorem IsPurelyInseparable.isFinite (hf : f.IsPurelyInseparable) : IsFinite f := hf.1

theorem IsPurelyInseparable.universallyInjective (hf : f.IsPurelyInseparable) :
    UniversallyInjective f := hf.2.1

theorem IsPurelyInseparable.surjective (hf : f.IsPurelyInseparable) : Surjective f := hf.2.2

theorem IsPurelyInseparable.bijective (hf : f.IsPurelyInseparable) : Function.Bijective f :=
  ⟨hf.2.1.universally_injective _ _ _ .of_id_snd, hf.2.2.surj⟩

theorem IsPurelyInseparable.residueFieldMap_isPurelyInseparable (hf : f.IsPurelyInseparable)
    (x : X) : (f.residueFieldMap x).hom.IsPurelyInseparable :=
  ((isPurelyInseparable_iff f).mp hf).2.2 x

theorem isPurelyInseparable_of_instances [IsFinite f] [UniversallyInjective f] [Surjective f] :
    f.IsPurelyInseparable :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.Hom
