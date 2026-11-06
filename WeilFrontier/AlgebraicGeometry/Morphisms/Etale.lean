module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Étale morphisms of affine schemes

For a ring homomorphism `φ : B →+* A`, the morphism `Spec A ⟶ Spec B` is étale if and only if
`A` is an étale `B`-algebra.

## Main results

* `AlgebraicGeometry.etale_spec_map_iff`: `Spec.map φ` is étale iff `φ` is an étale ring
  homomorphism.
* `AlgebraicGeometry.etale_spec_map_algebraMap_iff`: the same for an algebra `A` over `B`,
  in terms of `Algebra.Etale B A`.

## Implementation notes

Étale morphisms of schemes are Mathlib's `AlgebraicGeometry.Etale` (flat, formally unramified,
locally of finite presentation), and étale ring homomorphisms are `RingHom.Etale`. For the
noetherian rings of the source these agree with the definitions by finite generation, flatness
and stalkwise unramifiedness, and the statement is then an instance of
`AlgebraicGeometry.HasRingHomProperty.Spec_iff`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

/-- `Spec A ⟶ Spec B` is étale if and only if `φ : B →+* A` is an étale ring homomorphism. -/
@[weil "lem_fk102_etale_affine_iff_etale_algebra"]
theorem etale_spec_map_iff {A B : CommRingCat.{u}} (φ : B ⟶ A) :
    Etale (Spec.map φ) ↔ φ.hom.Etale :=
  HasRingHomProperty.Spec_iff

/-- For a `B`-algebra `A`, `Spec A ⟶ Spec B` is étale if and only if `A` is an étale
`B`-algebra. -/
theorem etale_spec_map_algebraMap_iff {A B : Type u} [CommRing A] [CommRing B] [Algebra B A] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap B A))) ↔ Algebra.Etale B A := by
  rw [etale_spec_map_iff]
  exact RingHom.etale_algebraMap

end AlgebraicGeometry

end

/-! ### Base change of étale morphisms -/

/-!
# Base change of étale morphisms

Let `f : X ⟶ Y` be étale and `h : Z ⟶ Y` any morphism of schemes. The second projection
`pullback.snd f h : X ×_Y Z ⟶ Z` is étale. If moreover `X` and `Z` are noetherian, so is the
fibre product, and if `X` and `Z` are separated, so is the fibre product.

## Main results

* `AlgebraicGeometry.isNoetherian_pullback_of_etale`: `X ×_Y Z` is noetherian when `X` and `Z` are.
* `AlgebraicGeometry.isSeparated_pullback_of_isSeparated`: `X ×_Y Z` is separated when `X`
  and `Z` are.
* `AlgebraicGeometry.etale_pullback_snd`: `X ×_Y Z` is noetherian and separated and the projection
  to `Z` is étale, for `X`, `Z` noetherian separated (Freitag–Kiehl's standing convention).

## Implementation notes

Étale is Mathlib's `AlgebraicGeometry.Etale`; its stability under base change
(`AlgebraicGeometry.Etale.instSndScheme`) needs no noetherian hypothesis. The noetherian part
only uses that `f` is locally of finite type and that `X` is noetherian (so `f` is quasi-compact);
the separated part only uses that `X` and `Z` are separated. The scheme `Y` is arbitrary.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ Y)
/-- The fibre product of a morphism locally of finite type from a noetherian scheme with a
morphism from a noetherian scheme is noetherian. -/
theorem isNoetherian_pullback_of_locallyOfFiniteType [LocallyOfFiniteType f] [IsNoetherian X]
    [IsNoetherian Z] : IsNoetherian (pullback f h) := by
  have : IsLocallyNoetherian (pullback f h) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f h)
  have : CompactSpace ↥(pullback f h) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f h)
  exact {}

/-- The fibre product of an étale morphism from a noetherian scheme with a morphism from a
noetherian scheme is noetherian. -/
theorem isNoetherian_pullback_of_etale [Etale f] [IsNoetherian X] [IsNoetherian Z] :
    IsNoetherian (pullback f h) :=
  isNoetherian_pullback_of_locallyOfFiniteType f h

/-- The fibre product of two separated schemes over any base is separated. -/
theorem isSeparated_pullback_of_isSeparated [X.IsSeparated] [Z.IsSeparated] :
    (pullback f h).IsSeparated := by
  have : IsSeparated (terminal.from Z) := Scheme.IsSeparated.isSeparated_terminal_from
  constructor
  rw [Subsingleton.elim (terminal.from (pullback f h)) (pullback.snd f h ≫ terminal.from Z)]
  infer_instance

/-- **Base change of étale morphisms** (FK I.1). Let `f : X ⟶ Y` be étale and `h : Z ⟶ Y` any
morphism, with `X` and `Z` noetherian and separated. Then `X ×_Y Z` is noetherian and separated,
and the projection `X ×_Y Z ⟶ Z` is étale. -/
@[weil "lem_fk102_etale_base_change"]
theorem etale_pullback_snd [Etale f] [IsNoetherian X] [IsNoetherian Z] [X.IsSeparated]
    [Z.IsSeparated] :
    IsNoetherian (pullback f h) ∧ (pullback f h).IsSeparated ∧ Etale (pullback.snd f h) :=
  ⟨isNoetherian_pullback_of_etale f h, isSeparated_pullback_of_isSeparated f h, inferInstance⟩

end AlgebraicGeometry
