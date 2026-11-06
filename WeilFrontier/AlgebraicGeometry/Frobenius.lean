module

public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Absolute
public import WeilFrontier.Defs.AlgebraicGeometry.Frobenius
public import Weil.Attr

/-!
# Naturality of the Frobenius endomorphism over a finite field

Let `κ` be a finite field with `q` elements. For every morphism `g : Y ⟶ X` of schemes over `κ`,
the Frobenius endomorphisms commute with `g`: `Fr_X ∘ g = g ∘ Fr_Y`. On the underlying spaces both
sides are `g`, and on sections both send `a` to `g^#(a) ^ q = g^#(a ^ q)`.

Writing `q = p ^ f`, the Frobenius is the `f`-th iterate of the absolute Frobenius, and the
result follows from the naturality of the absolute Frobenius,
`Stacks.Frobenius.absoluteFrobenius_naturality`, by iteration.

## Main results

* `AlgebraicGeometry.Scheme.Hom.pow_comp_eq_comp_pow`: a morphism intertwining two
  endomorphisms intertwines their iterates.
* `AlgebraicGeometry.frobeniusOver_naturality`: the Frobenius over `κ` commutes with every
  morphism of schemes over `κ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter II, §3.
* [Stacks] The Stacks Project, Tag 0CC7.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism intertwining two endomorphisms intertwines their iterates. -/
lemma Scheme.Hom.pow_comp_eq_comp_pow {X Y : Scheme.{u}} {F : X ⟶ X} {G : Y ⟶ Y} (f : X ⟶ Y)
    (h : F ≫ f = f ≫ G) (n : ℕ) :
    End.asHom (End.of F ^ n) ≫ f = f ≫ End.asHom (End.of G ^ n) := by
  induction n with
  | zero =>
    change 𝟙 X ≫ f = f ≫ 𝟙 Y
    rw [Category.id_comp, Category.comp_id]
  | succ n ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def]
    change (F ≫ End.asHom (End.of F ^ n)) ≫ f = f ≫ G ≫ End.asHom (End.of G ^ n)
    rw [Category.assoc, ih, ← Category.assoc, h, Category.assoc]

variable {κ : Type u} [Field κ] [Fintype κ]

/-- **Naturality of the Frobenius.** For every morphism `g : Y ⟶ X` of schemes over a finite
field `κ`, `Fr_X ∘ g = g ∘ Fr_Y`. -/
@[weil "lem_fk203_frobenius_commutes_with_morphisms"]
theorem frobeniusOver_naturality {X Y : Over (Spec (.of κ))} (g : Y ⟶ X) :
    g ≫ frobeniusOver κ X = frobeniusOver κ Y ≫ g := by
  have : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ _⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card κ (ringChar κ)
  ext1
  rw [Over.comp_left, Over.comp_left, frobeniusOver_left_eq X (ringChar κ) n hn,
    frobeniusOver_left_eq Y (ringChar κ) n hn]
  exact (Scheme.Hom.pow_comp_eq_comp_pow g.left
    (Stacks.Frobenius.absoluteFrobenius_naturality g.left _ _ _) n).symm

end AlgebraicGeometry
