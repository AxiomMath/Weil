module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import Weil.Attr

/-!
# Quasi-affine morphisms, in the form of Freitag–Kiehl

A morphism of schemes `g : Y ⟶ T` is quasi-affine in the sense of Freitag–Kiehl if it is
quasi-compact and, for every affine open `V ⊆ T`, the scheme `g⁻¹(V)` is isomorphic to an open
subscheme of an affine scheme. This file identifies that notion with
`AlgebraicGeometry.IsQuasiAffineHom` (Stacks Project, Tag 01SK: the inverse image of every affine
open is a quasi-affine scheme).

## Main results

* `AlgebraicGeometry.isQuasiAffineHom_iff_quasiCompact_and_exists_isOpenImmersion`: a morphism
  is quasi-affine if and only if it is quasi-compact and the inverse image of every affine open
  admits an open immersion into an affine scheme.
* `AlgebraicGeometry.IsQuasiAffineHom.exists_isOpenImmersion`: the inverse image of an affine
  open under a quasi-affine morphism admits an open immersion into an affine scheme.

## Implementation notes

"Isomorphic to an open subscheme of an affine scheme" is expressed as the existence of an open
immersion into an affine scheme; for the forward direction the affine scheme is
`Spec Γ(g⁻¹(V), ⊤)` and the open immersion is `Scheme.toSpecΓ`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
* [Stacks Project, Tag 01SK](https://stacks.math.columbia.edu/tag/01SK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {Y T : Scheme.{u}}

/-- The inverse image of an affine open under a quasi-affine morphism admits an open immersion
into an affine scheme, namely `Spec` of its global sections. -/
theorem IsQuasiAffineHom.exists_isOpenImmersion (g : Y ⟶ T) [IsQuasiAffineHom g]
    (V : T.Opens) (hV : IsAffineOpen V) :
    ∃ (Z : Scheme.{u}) (_ : IsAffine Z) (j : (g ⁻¹ᵁ V).toScheme ⟶ Z), IsOpenImmersion j := by
  have : Scheme.IsQuasiAffine (g ⁻¹ᵁ V).toScheme :=
    IsQuasiAffineHom.isQuasiAffine_preimage V hV
  exact ⟨_, inferInstance, (g ⁻¹ᵁ V).toScheme.toSpecΓ, inferInstance⟩

/-- A morphism of schemes is quasi-affine if and only if it is quasi-compact and the inverse
image of every affine open subscheme of the target is isomorphic to an open subscheme of an
affine scheme. -/
@[weil "def_fka3_quasi_affine_morphism"]
theorem isQuasiAffineHom_iff_quasiCompact_and_exists_isOpenImmersion (g : Y ⟶ T) :
    IsQuasiAffineHom g ↔ QuasiCompact g ∧ ∀ V : T.Opens, IsAffineOpen V →
      ∃ (Z : Scheme.{u}) (_ : IsAffine Z) (j : (g ⁻¹ᵁ V).toScheme ⟶ Z), IsOpenImmersion j := by
  refine ⟨fun _ ↦ ⟨inferInstance, IsQuasiAffineHom.exists_isOpenImmersion g⟩, ?_⟩
  rintro ⟨hqc, h⟩
  refine ⟨fun V hV ↦ ?_⟩
  obtain ⟨Z, _, j, _⟩ := h V hV
  have : CompactSpace (g ⁻¹ᵁ V).toScheme :=
    isCompact_iff_compactSpace.mp ((quasiCompact_iff_forall_isAffineOpen.mp hqc) V hV)
  exact Scheme.IsQuasiAffine.of_isImmersion j

end AlgebraicGeometry

end
