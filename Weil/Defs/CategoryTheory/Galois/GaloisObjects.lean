module

public import Weil.Attr
public import Mathlib.CategoryTheory.Galois.GaloisObjects

/-!
# Restriction of automorphisms along a morphism

Let `f : Z ⟶ Y` be a morphism in a category `C`, and let `σ` be an automorphism of `Z` and
`σ'` an automorphism of `Y`. Then `σ'` is a *restriction of `σ` along `f`* if
`σ' ∘ f = f ∘ σ`, i.e. `f ≫ σ'.hom = σ.hom ≫ f`.

For `X` a scheme and `C = Over X`, an automorphism of an object `p : Y ⟶ X` of `Over X` is
an automorphism of `Y` over `X`, and morphisms of `Over X` are `X`-morphisms; this is the
restriction relation between the automorphism groups `G(Z/X)` and `G(Y/X)` of covering
spaces.

## Main definitions

- `CategoryTheory.Aut.IsRestrictionAlong f σ σ'`: `σ'` is a restriction of `σ` along `f`.

## Main results

- `CategoryTheory.Aut.IsRestrictionAlong.mul`, `.one`, `.inv`: the relation is compatible with
  the group structures, so the pairs `(σ, σ')` related along `f` form a subgroup.
- `CategoryTheory.Aut.IsRestrictionAlong.comp`: restrictions along `f` and `g` compose to a
  restriction along `f ≫ g`.
- `CategoryTheory.Aut.IsRestrictionAlong.eq_of_epi`: restrictions along an epimorphism are
  unique.
- `CategoryTheory.Aut.isRestrictionAlong_iff_autMap_eq`: in a Galois category, with `Z`
  connected and `Y` Galois, `σ'` is a restriction of `σ` along `f` if and only if
  `σ' = PreGaloisCategory.autMap f σ`.

## Implementation notes

The relation is stated for an arbitrary category; the source's setting is `C = Over X` for a
scheme `X`. The product on `Aut` is `σ * τ = τ ≪≫ σ`, i.e. composition `σ ∘ τ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I.
-/

@[expose] public section

namespace CategoryTheory

namespace Aut

universe v u

variable {C : Type u} [Category.{v} C]

/-- `σ'` is a *restriction of `σ` along `f`*: `σ' ∘ f = f ∘ σ`. -/
@[weil "def_fka1_galois_restriction_map"]
def IsRestrictionAlong {Z Y : C} (f : Z ⟶ Y) (σ : Aut Z) (σ' : Aut Y) : Prop :=
  f ≫ σ'.hom = σ.hom ≫ f

theorem isRestrictionAlong_iff {Z Y : C} (f : Z ⟶ Y) (σ : Aut Z) (σ' : Aut Y) :
    IsRestrictionAlong f σ σ' ↔ f ≫ σ'.hom = σ.hom ≫ f :=
  Iff.rfl

namespace IsRestrictionAlong

variable {Z Y W : C} {f : Z ⟶ Y}

theorem comp_hom {σ : Aut Z} {σ' : Aut Y} (h : IsRestrictionAlong f σ σ') :
    f ≫ σ'.hom = σ.hom ≫ f :=
  h

theorem one (f : Z ⟶ Y) : IsRestrictionAlong f 1 1 := by
  change f ≫ 𝟙 Y = 𝟙 Z ≫ f
  simp

theorem mul {σ τ : Aut Z} {σ' τ' : Aut Y} (hσ : IsRestrictionAlong f σ σ')
    (hτ : IsRestrictionAlong f τ τ') : IsRestrictionAlong f (σ * τ) (σ' * τ') := by
  change f ≫ τ'.hom ≫ σ'.hom = (τ.hom ≫ σ.hom) ≫ f
  rw [← Category.assoc, comp_hom hτ, Category.assoc, comp_hom hσ, Category.assoc]

theorem inv {σ : Aut Z} {σ' : Aut Y} (h : IsRestrictionAlong f σ σ') :
    IsRestrictionAlong f σ⁻¹ σ'⁻¹ := by
  change f ≫ σ'.inv = σ.inv ≫ f
  have key (a : Z ≅ Z) (b : Y ≅ Y) (hab : f ≫ b.hom = a.hom ≫ f) : f ≫ b.inv = a.inv ≫ f := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hab, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact key σ σ' h

theorem inv_iff {σ : Aut Z} {σ' : Aut Y} :
    IsRestrictionAlong f σ⁻¹ σ'⁻¹ ↔ IsRestrictionAlong f σ σ' :=
  ⟨fun h ↦ by simpa using h.inv, inv⟩

theorem pow {σ : Aut Z} {σ' : Aut Y} (h : IsRestrictionAlong f σ σ') (n : ℕ) :
    IsRestrictionAlong f (σ ^ n) (σ' ^ n) := by
  induction n with
  | zero => simpa using one f
  | succ n ih => simpa [pow_succ] using ih.mul h

/-- Restriction of `σ` along `f` and then of `σ'` along `g` is restriction along `f ≫ g`. -/
theorem comp {g : Y ⟶ W} {σ : Aut Z} {σ' : Aut Y} {σ'' : Aut W}
    (hf : IsRestrictionAlong f σ σ') (hg : IsRestrictionAlong g σ' σ'') :
    IsRestrictionAlong (f ≫ g) σ σ'' := by
  simp only [IsRestrictionAlong] at hf hg ⊢
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

/-- Every automorphism is its own restriction along the identity. -/
theorem id (σ : Aut Z) : IsRestrictionAlong (𝟙 Z) σ σ := by
  simp [IsRestrictionAlong]

theorem id_iff {σ σ' : Aut Z} : IsRestrictionAlong (𝟙 Z) σ σ' ↔ σ' = σ := by
  simp only [IsRestrictionAlong, Category.id_comp, Category.comp_id]
  exact ⟨fun h ↦ Iso.ext h, fun h ↦ h ▸ rfl⟩

/-- Restrictions along an epimorphism are unique. -/
theorem eq_of_epi [Epi f] {σ : Aut Z} {σ' σ'' : Aut Y} (h' : IsRestrictionAlong f σ σ')
    (h'' : IsRestrictionAlong f σ σ'') : σ' = σ'' :=
  Iso.ext ((cancel_epi f).1 (h'.trans h''.symm))

/-- The pairs `(σ, σ')` with `σ'` a restriction of `σ` along `f` form a subgroup of
`Aut Z × Aut Y`. -/
def subgroup (f : Z ⟶ Y) : Subgroup (Aut Z × Aut Y) where
  carrier := {p | IsRestrictionAlong f p.1 p.2}
  one_mem' := one f
  mul_mem' h₁ h₂ := mul h₁ h₂
  inv_mem' h := inv h

theorem mem_subgroup {p : Aut Z × Aut Y} :
    p ∈ subgroup f ↔ IsRestrictionAlong f p.1 p.2 :=
  Iff.rfl

end IsRestrictionAlong

section Galois

open PreGaloisCategory

variable [GaloisCategory C] {Z Y : C} [IsConnected Z] [IsGalois Y]

/-- `autMap f σ` is a restriction of `σ` along `f`. -/
theorem isRestrictionAlong_autMap (f : Z ⟶ Y) (σ : Aut Z) :
    IsRestrictionAlong f σ (autMap f σ) :=
  comp_autMap f σ

/-- With `Z` connected and `Y` Galois, `σ` has exactly one restriction along `f`, namely
`autMap f σ`. -/
theorem isRestrictionAlong_iff_autMap_eq (f : Z ⟶ Y) (σ : Aut Z) (σ' : Aut Y) :
    IsRestrictionAlong f σ σ' ↔ autMap f σ = σ' :=
  ⟨autMap_unique f σ σ', fun h ↦ h ▸ isRestrictionAlong_autMap f σ⟩

theorem existsUnique_isRestrictionAlong (f : Z ⟶ Y) (σ : Aut Z) :
    ∃! σ' : Aut Y, IsRestrictionAlong f σ σ' :=
  ⟨autMap f σ, isRestrictionAlong_autMap f σ, fun σ' h ↦ (autMap_unique f σ σ' h).symm⟩

end Galois

end Aut

end CategoryTheory
