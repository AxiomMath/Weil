module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ShortExactLongExactSequence
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.Attr

/-!
# The long exact sequence of étale cohomology

Let `X` be a scheme and `0 → F' → F → F'' → 0` a short exact sequence of abelian sheaves on the
small étale site of `X`. Then there is a long exact sequence
`0 → H⁰(X, F') → H⁰(X, F) → H⁰(X, F'') → H¹(X, F') → ⋯ → Hⁱ(X, F) → Hⁱ(X, F'') → Hⁱ⁺¹(X, F') → ⋯`
which is functorial in the short exact sequence.

The cohomology `Hⁱ(X, -)` is `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant
sheaf `ℤ`; the connecting homomorphism is composition with the extension class of the short
exact sequence, `Stacks.Cohomology.GlobalLongExactSequence.boundary`. Exactness on an arbitrary
site is in `Stacks.Cohomology.GlobalLongExactSequence`; this file adds the naturality of the
connecting homomorphism in morphisms of short exact sequences and states the result on the small
étale site.

## Main results

* `CategoryTheory.Sheaf.H.map_boundary`: the connecting homomorphism is natural in morphisms of
  short exact sequences of abelian sheaves, on any site.
* `AlgebraicGeometry.SmallEtale.cohomology_longExact`: the long exact étale cohomology sequence
  of a short exact sequence of abelian étale sheaves.
* `AlgebraicGeometry.SmallEtale.cohomology_map_boundary`: its functoriality in the short exact
  sequence.

## Implementation notes

The functoriality of the maps `Hⁱ(X, F') → Hⁱ(X, F) → Hⁱ(X, F'')` is functoriality of
`CategoryTheory.Sheaf.H.map` (`CategoryTheory.Sheaf.H.map_comp_apply`), since a morphism of short
complexes commutes with the two maps; only the square through the connecting homomorphism needs a
proof. The source derives the sequence from the derived functors of `Γ(X, -)`; here the
cohomology groups are `Ext`-groups, identified with those derived functors by
`AlgebraicGeometry.SmallEtale.functorHIsoRightDerivedSections`, and the sequence is the covariant
`Ext` sequence.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w' w v u

namespace CategoryTheory.Sheaf.H

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

open Stacks.Cohomology.GlobalLongExactSequence in
/-- **The connecting homomorphism is natural.** For a morphism `φ : S₁ ⟶ S₂` of short exact
sequences of abelian sheaves, the square formed by the connecting homomorphisms
`Hⁿ(S₁.X₃) → Hⁿ⁺¹(S₁.X₁)`, `Hⁿ(S₂.X₃) → Hⁿ⁺¹(S₂.X₁)` and the maps induced by `φ` commutes. -/
theorem map_boundary {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{w})} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ) (x : Sheaf.H.{w'} S₁.X₃ n) :
    Sheaf.H.map φ.τ₁ (n + 1) (boundary h₁ n x) = boundary h₂ n (Sheaf.H.map φ.τ₃ n x) := by
  simp only [boundary, Ext.postcomp, AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply,
    Sheaf.H.map_apply]
  rw [Ext.comp_assoc x h₁.extClass (Ext.mk₀ φ.τ₁) rfl (add_zero 1) (by lia),
    h₁.extClass_naturality h₂ φ,
    ← Ext.comp_assoc x (Ext.mk₀ φ.τ₃) h₂.extClass (add_zero n) (zero_add 1) (by lia)]

end CategoryTheory.Sheaf.H

namespace AlgebraicGeometry.SmallEtale

open Stacks.Cohomology.GlobalLongExactSequence

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})]

/-- **The long exact sequence of étale cohomology.** For a short exact sequence
`0 → F' → F → F'' → 0` of abelian sheaves on the small étale site of a scheme `X`, the sequence
`0 → H⁰(X, F') → H⁰(X, F) → H⁰(X, F'') → H¹(X, F') → ⋯ → Hⁿ(X, F) → Hⁿ(X, F'') → Hⁿ⁺¹(X, F') → ⋯`
is exact: the first map is injective, and the sequence is exact at every `Hⁿ(X, F)`,
`Hⁿ(X, F'')` and `Hⁿ⁺¹(X, F')`, the connecting homomorphism being `boundary`. -/
@[weil "lem_fk102_etale_cohomology_long_exact"]
theorem cohomology_longExact {T : ShortComplex (Sheaf (topology B X hX) AddCommGrpCat.{u})}
    (hT : T.ShortExact) :
    Function.Injective (Sheaf.H.map.{w} T.f 0) ∧
      ∀ n : ℕ, Function.Exact (Sheaf.H.map.{w} T.f n) (Sheaf.H.map.{w} T.g n) ∧
        Function.Exact (Sheaf.H.map.{w} T.g n) (boundary hT n) ∧
        Function.Exact (boundary hT n) (Sheaf.H.map.{w} T.f (n + 1)) :=
  have := hT.mono_f
  ⟨injective_map_zero T.f, fun n ↦
    ⟨exact_map_map hT n, exact_map_boundary hT n, exact_boundary_map hT n⟩⟩

/-- **The long exact sequence of étale cohomology is functorial.** For a morphism `φ` of short
exact sequences of abelian sheaves on the small étale site of a scheme `X`, the maps induced by
`φ` commute with the maps of the two long exact sequences: with the maps induced by the short
complexes, and with the connecting homomorphisms. -/
@[weil "lem_fk102_etale_cohomology_long_exact"]
theorem cohomology_map_boundary
    {T₁ T₂ : ShortComplex (Sheaf (topology B X hX) AddCommGrpCat.{u})} (h₁ : T₁.ShortExact)
    (h₂ : T₂.ShortExact) (φ : T₁ ⟶ T₂) (n : ℕ) :
    (Sheaf.H.map.{w} φ.τ₂ n).comp (Sheaf.H.map T₁.f n) =
        (Sheaf.H.map T₂.f n).comp (Sheaf.H.map φ.τ₁ n) ∧
      (Sheaf.H.map.{w} φ.τ₃ n).comp (Sheaf.H.map T₁.g n) =
        (Sheaf.H.map T₂.g n).comp (Sheaf.H.map φ.τ₂ n) ∧
      (Sheaf.H.map.{w} φ.τ₁ (n + 1)).comp (boundary h₁ n) =
        (boundary h₂ n).comp (Sheaf.H.map φ.τ₃ n) := by
  refine ⟨?_, ?_, ?_⟩ <;> ext x
  · simp only [AddMonoidHom.comp_apply, ← Sheaf.H.map_comp_apply, φ.comm₁₂]
  · simp only [AddMonoidHom.comp_apply, ← Sheaf.H.map_comp_apply, φ.comm₂₃]
  · exact Sheaf.H.map_boundary h₁ h₂ φ n x

end AlgebraicGeometry.SmallEtale
