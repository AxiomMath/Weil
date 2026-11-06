module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Flatness.Flattening.Compactifications

/-!
# Domination of compactifications

Let `f : X ⟶ S` be a morphism of schemes and let `c₁ = (X̄₁, i, f̄₁)` and `c₂ = (X̄₂, j, f̄₂)`
be compactifications of `f`. The compactification `c₁` *dominates* `c₂` if there is a morphism
`φ : X̄₁ ⟶ X̄₂` with `i ≫ φ = j` and `f̄₁ = φ ≫ f̄₂`. Such a `φ` is exactly a morphism `c₁ ⟶ c₂`
in the category `f.Compactification` of compactifications of `f`, so domination is the
existence of a morphism there.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.Compactification.Dominates c₁ c₂`: the compactification `c₁`
  dominates `c₂`.
* `AlgebraicGeometry.Scheme.Hom.Compactification.homMk`: the morphism of compactifications
  given by a morphism of ambient schemes compatible with the open immersions and the proper
  morphisms to the base.

## Main results

* `AlgebraicGeometry.Scheme.Hom.Compactification.dominates_iff`: `c₁` dominates `c₂` if and
  only if there is `φ : X̄₁ ⟶ X̄₂` with `i ≫ φ = j` and `f̄₁ = φ ≫ f̄₂`.
* `AlgebraicGeometry.Scheme.Hom.Compactification.Dominates.refl`,
  `AlgebraicGeometry.Scheme.Hom.Compactification.Dominates.trans`: domination is a preorder.

## Implementation notes

Domination is a `Prop`; results needing the dominating morphism itself (its properness, base
change along it) take a morphism `c₁ ⟶ c₂` of compactifications, whose underlying morphism of
ambient schemes is `CompactificationOf.Hom.map`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §8.
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

namespace Compactification

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The underlying morphism of ambient schemes of a morphism of compactifications is
compatible with the open immersions. -/
@[reassoc (attr := simp)]
lemma immersion_comp_map {c₁ c₂ : f.Compactification} (φ : c₁ ⟶ c₂) :
    c₁.immersion ≫ CompactificationOf.Hom.map φ = c₂.immersion := by
  have := congrArg CommaMorphism.left φ.hom.w
  simpa [CompactificationOf.immersion, CompactificationOf.Hom.map] using this

/-- The underlying morphism of ambient schemes of a morphism of compactifications is a
morphism over the base. -/
@[reassoc (attr := simp)]
lemma map_comp_toBase {c₁ c₂ : f.Compactification} (φ : c₁ ⟶ c₂) :
    CompactificationOf.Hom.map φ ≫ c₂.toBase = c₁.toBase :=
  Over.w φ.hom.right

/-- The morphism of compactifications of `f` given by a morphism `φ` of ambient schemes with
`i ≫ φ = j` and `φ ≫ f̄₂ = f̄₁`. -/
def homMk {c₁ c₂ : f.Compactification} (φ : c₁.space ⟶ c₂.space)
    (hi : c₁.immersion ≫ φ = c₂.immersion) (hb : φ ≫ c₂.toBase = c₁.toBase) : c₁ ⟶ c₂ :=
  ObjectProperty.homMk (StructuredArrow.homMk (Over.homMk φ hb) (by ext; simpa using hi))

@[simp]
lemma map_homMk {c₁ c₂ : f.Compactification} (φ : c₁.space ⟶ c₂.space)
    (hi : c₁.immersion ≫ φ = c₂.immersion) (hb : φ ≫ c₂.toBase = c₁.toBase) :
    CompactificationOf.Hom.map (homMk φ hi hb) = φ := rfl

/-- Two morphisms of compactifications are equal when their underlying morphisms of ambient
schemes are. -/
@[ext]
lemma hom_ext {c₁ c₂ : f.Compactification} {φ ψ : c₁ ⟶ c₂}
    (h : CompactificationOf.Hom.map φ = CompactificationOf.Hom.map ψ) : φ = ψ := by
  ext
  exact h

/-- The compactification `c₁ = (X̄₁, i, f̄₁)` of `f` *dominates* the compactification
`c₂ = (X̄₂, j, f̄₂)` if there is a morphism of compactifications `c₁ ⟶ c₂`, that is, a
morphism `φ : X̄₁ ⟶ X̄₂` with `i ≫ φ = j` and `f̄₁ = φ ≫ f̄₂` (see `dominates_iff`). -/
@[weil "def_fk108_compactification_dominates"]
def Dominates (c₁ c₂ : f.Compactification) : Prop :=
  Nonempty (c₁ ⟶ c₂)

/-- The compactification `c₁ = (X̄₁, i, f̄₁)` dominates `c₂ = (X̄₂, j, f̄₂)` if and only if
there is a morphism `φ : X̄₁ ⟶ X̄₂` with `i ≫ φ = j` and `f̄₁ = φ ≫ f̄₂`. -/
@[weil "def_fk108_compactification_dominates"]
theorem dominates_iff (c₁ c₂ : f.Compactification) :
    c₁.Dominates c₂ ↔ ∃ φ : c₁.space ⟶ c₂.space,
      c₁.immersion ≫ φ = c₂.immersion ∧ c₁.toBase = φ ≫ c₂.toBase := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨CompactificationOf.Hom.map φ, immersion_comp_map φ, (map_comp_toBase φ).symm⟩
  · rintro ⟨φ, hi, hb⟩
    exact ⟨homMk φ hi hb.symm⟩

/-- A morphism of compactifications witnesses domination. -/
lemma Dominates.of_hom {c₁ c₂ : f.Compactification} (φ : c₁ ⟶ c₂) : c₁.Dominates c₂ := ⟨φ⟩

/-- A chosen morphism of compactifications witnessing domination. -/
noncomputable def Dominates.hom {c₁ c₂ : f.Compactification} (h : c₁.Dominates c₂) :
    c₁ ⟶ c₂ :=
  Classical.choice h

/-- Every compactification dominates itself. -/
@[refl]
lemma Dominates.refl (c : f.Compactification) : c.Dominates c := ⟨𝟙 c⟩

/-- Domination is transitive. -/
@[trans]
lemma Dominates.trans {c₁ c₂ c₃ : f.Compactification} (h₁₂ : c₁.Dominates c₂)
    (h₂₃ : c₂.Dominates c₃) : c₁.Dominates c₃ :=
  h₁₂.elim fun φ ↦ h₂₃.elim fun ψ ↦ ⟨φ ≫ ψ⟩

instance : IsPreorder f.Compactification Dominates where
  refl := Dominates.refl
  trans _ _ _ := Dominates.trans

end Compactification

end Scheme.Hom

end AlgebraicGeometry
