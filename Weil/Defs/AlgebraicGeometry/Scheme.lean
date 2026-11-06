module

public import Weil.Attr
public import Weil.Defs.RingTheory.Henselian.Henselization.HenselianPolynomialRing
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The henselian line over an extension of the fraction field

Let `A` be a local ring and `B = A{t}` the henselization of `A[t]` at the origin `(𝔪, t)`
(`MvPolynomial.IsHenselianPolynomialRing A (Fin 1) B`). For an `A`-algebra `L`, typically a field
extension of the fraction field `κ` of `A`, put
`X_L = Spec (B ⊗[A] L)`. An `A`-algebra map `L → L'`, for instance an inclusion `L ⊆ L'` of
extensions of `κ`, induces a morphism of schemes `X_{L'} → X_L`, and this is functorial in `L`.

## Main definitions

* `AlgebraicGeometry.henselianLineGeneric A B L`: the affine scheme `Spec (B ⊗[A] L)`.
* `AlgebraicGeometry.henselianLineGenericMap A B f`: for `f : L →ₐ[A] L'`, the morphism
  `Spec (B ⊗[A] L') ⟶ Spec (B ⊗[A] L)` induced by `id_B ⊗ f`.

## Main results

* `AlgebraicGeometry.henselianLineGenericMap_id`, `AlgebraicGeometry.henselianLineGenericMap_comp`:
  functoriality in `L`.

## Implementation notes

The source assumes `A` a noetherian local domain and `L` a field extension of its fraction
field. Neither is needed to form the scheme or the morphism: the construction is made for any
commutative ring `A`, any `A`-algebra `B` and any `A`-algebras `L`, `L'`; the statements using it
add the hypotheses `MvPolynomial.IsHenselianPolynomialRing A (Fin 1) B` and that `L` is a field
extension of `FractionRing A` (an inclusion of `FractionRing A`-extensions `L ⊆ L'` gives an
`A`-algebra map by `AlgHom.restrictScalars`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v w

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] (B : Type w) [CommRing B] [Algebra A B]

/-- **The henselian line over `L`.** For an `A`-algebra `B` (the henselian polynomial ring
`A{t}`) and an `A`-algebra `L` (a field extension of the fraction field of `A`), the affine
scheme `X_L = Spec (B ⊗[A] L)`. -/
@[weil "def_fk107_henselian_line_generic_scheme"]
noncomputable abbrev henselianLineGeneric (L : Type v) [CommRing L] [Algebra A L] : Scheme :=
  Spec (CommRingCat.of (B ⊗[A] L))

variable {A} in
/-- **The transition morphism `X_{L'} ⟶ X_L`** induced by an `A`-algebra map `f : L → L'`
(an inclusion `L ⊆ L'`): the spectrum of `id_B ⊗ f : B ⊗[A] L → B ⊗[A] L'`. -/
@[weil "def_fk107_henselian_line_generic_scheme"]
noncomputable def henselianLineGenericMap {L L' : Type v} [CommRing L] [Algebra A L]
    [CommRing L'] [Algebra A L'] (f : L →ₐ[A] L') :
    henselianLineGeneric A B L' ⟶ henselianLineGeneric A B L :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id A B) f).toRingHom)

variable {A}

theorem henselianLineGenericMap_def {L L' : Type v} [CommRing L] [Algebra A L]
    [CommRing L'] [Algebra A L'] (f : L →ₐ[A] L') :
    henselianLineGenericMap B f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B) f).toRingHom) :=
  rfl

@[simp]
theorem henselianLineGenericMap_id (L : Type v) [CommRing L] [Algebra A L] :
    henselianLineGenericMap B (AlgHom.id A L) = 𝟙 (henselianLineGeneric A B L) := by
  rw [henselianLineGenericMap, Algebra.TensorProduct.map_id]
  exact Spec.map_id _

theorem henselianLineGenericMap_comp {L L' L'' : Type v} [CommRing L] [Algebra A L]
    [CommRing L'] [Algebra A L'] [CommRing L''] [Algebra A L''] (f : L →ₐ[A] L')
    (g : L' →ₐ[A] L'') :
    henselianLineGenericMap B (g.comp f) =
      henselianLineGenericMap B g ≫ henselianLineGenericMap B f := by
  rw [henselianLineGenericMap, henselianLineGenericMap, henselianLineGenericMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  rw [Algebra.TensorProduct.map_id_comp]
  rfl

end AlgebraicGeometry
