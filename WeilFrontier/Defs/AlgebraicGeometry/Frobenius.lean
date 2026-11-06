module

public import StacksFrontier.AlgebraicGeometry.Frobenius
public import Weil.Attr

/-!
# The Frobenius endomorphism of a scheme over a finite field

Let `κ` be a finite field with `q` elements and `X` a scheme over `κ`. The *Frobenius morphism*
`Fr_X : X ⟶ X` with respect to `κ` is the endomorphism of `X` which is the identity on the
underlying topological space and raises local sections of `𝒪_X` to their `q`-th powers. It is a
morphism of schemes because `p = 0` in `𝒪_X`, where `p` is the characteristic of `κ`, and it is a
morphism over `κ` because `c ^ q = c` for every `c ∈ κ`.

If `q = p ^ f`, the Frobenius morphism is the `f`-fold absolute Frobenius of `X`, that is, the
geometric Frobenius `Stacks.Frobenius.geometricFrobenius` of the Stacks Project. The definition
below is that morphism, with the characteristic and the exponent read off from `κ`.

## Main definitions

* `AlgebraicGeometry.frobeniusOver κ X`: the Frobenius endomorphism of a scheme `X` over the
  finite field `κ`, as a morphism over `Spec κ`.

## Main results

* `AlgebraicGeometry.frobeniusOver_left_base`: the Frobenius is the identity on the underlying
  topological space.
* `AlgebraicGeometry.frobeniusOver_left_appLE_apply`: on the sections over every open set, the
  Frobenius is the `q`-th power map, `q = Fintype.card κ`.
* `AlgebraicGeometry.eq_frobeniusOver_left`: these two properties characterise the Frobenius.
* `AlgebraicGeometry.geometricFrobenius_eq_frobeniusOver`: the Frobenius is the geometric
  Frobenius `Stacks.Frobenius.geometricFrobenius X p f hcard` for every presentation
  `Fintype.card κ = p ^ f`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter II, §3.
* [Stacks] The Stacks Project, Tags 03SM and 03SQ.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section Iterate

variable {X : Scheme.{u}}

/-- Equal morphisms induce equal maps on sections. -/
lemma Scheme.Hom.appLE_eq_of_eq {Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- The iterates of an endomorphism which is the identity on the underlying space are again the
identity on the underlying space. -/
lemma Scheme.Hom.pow_base_eq_id {F : X ⟶ X} (hF : F.base = 𝟙 (X : TopCat)) (n : ℕ) :
    (End.asHom (End.of F ^ n)).base = 𝟙 (X : TopCat) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, End.mul_def]
    change (F ≫ End.asHom (End.of F ^ n)).base = _
    rw [Scheme.Hom.comp_base, ih, hF]
    rfl

/-- If an endomorphism is the identity on the underlying space and the `m`-th power map on the
sections over every open set, then its `n`-th iterate is the `m ^ n`-th power map on the
sections over every open set. -/
lemma Scheme.Hom.pow_appLE_apply_of_appLE_apply {F : X ⟶ X} {m : ℕ}
    (hF : F.base = 𝟙 (X : TopCat))
    (hF' : ∀ (U : X.Opens) (e : U ≤ F ⁻¹ᵁ U) (g : Γ(X, U)), F.appLE U U e g = g ^ m)
    (n : ℕ) (U : X.Opens) (e : U ≤ (End.asHom (End.of F ^ n)) ⁻¹ᵁ U) (g : Γ(X, U)) :
    (End.asHom (End.of F ^ n)).appLE U U e g = g ^ m ^ n := by
  induction n with
  | zero =>
    rw [show m ^ 0 = 1 from rfl, pow_one,
      Scheme.Hom.appLE_eq_of_eq (show End.asHom (End.of F ^ 0) = 𝟙 X from rfl) e]
    change X.presheaf.map (homOfLE _).op g = g
    exact congrArg (fun φ ↦ φ g) (X.presheaf.map_id _)
  | succ n ih =>
    have e₁ : U ≤ (End.asHom (End.of F ^ n)) ⁻¹ᵁ U := by
      intro x hx
      change (End.asHom (End.of F ^ n)).base x ∈ U
      rw [Scheme.Hom.pow_base_eq_id hF n]
      exact hx
    have e₂ : U ≤ F ⁻¹ᵁ U := by
      intro x hx
      change F.base x ∈ U
      rw [hF]
      exact hx
    have h : (End.asHom (End.of F ^ (n + 1))) = F ≫ End.asHom (End.of F ^ n) := by
      rw [pow_succ, End.mul_def]
    rw [Scheme.Hom.appLE_eq_of_eq h e,
      ← Scheme.Hom.appLE_comp_appLE F (End.asHom (End.of F ^ n)) U U U e₁ e₂,
      CommRingCat.comp_apply, ih e₁, hF', ← pow_mul, ← pow_succ]

end Iterate

variable (κ : Type u) [Field κ] [Fintype κ]

/-- **The Frobenius endomorphism** of a scheme `X` over a finite field `κ`: the morphism over
`Spec κ` which is the identity on the underlying topological space and raises local sections to
their `q`-th powers, `q = Fintype.card κ`. It is the geometric Frobenius
`Stacks.Frobenius.geometricFrobenius`, the `f`-fold absolute Frobenius for `q = p ^ f`. -/
@[weil "def_fk203_frobenius_endomorphism_scheme"]
noncomputable def frobeniusOver (X : Over (Spec (.of κ))) : X ⟶ X :=
  haveI : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ _⟩
  Stacks.Frobenius.geometricFrobenius X (ringChar κ) (FiniteField.card κ (ringChar κ)).choose
    (FiniteField.card κ (ringChar κ)).choose_spec.2

variable {κ}

/-- The Frobenius endomorphism is the geometric Frobenius of the Stacks Project for every
presentation of the cardinality of `κ` as a power `p ^ f` of its characteristic. -/
theorem geometricFrobenius_eq_frobeniusOver (X : Over (Spec (.of κ))) (p f : ℕ)
    [Fact p.Prime] [CharP κ p] (hcard : Fintype.card κ = p ^ f) :
    Stacks.Frobenius.geometricFrobenius X p f hcard = frobeniusOver κ X := by
  have hp : p = ringChar κ := (ringChar.eq κ p).symm
  subst hp
  have hf : f = (FiniteField.card κ (ringChar κ)).choose := by
    apply Nat.pow_right_injective (Fact.out : (ringChar κ).Prime).two_le
    exact hcard.symm.trans (FiniteField.card κ (ringChar κ)).choose_spec.2
  subst hf
  rfl

/-- The underlying scheme morphism of the Frobenius is an iterate of the absolute Frobenius. -/
lemma frobeniusOver_left_eq (X : Over (Spec (.of κ))) (p f : ℕ) [Fact p.Prime] [CharP κ p]
    (hcard : Fintype.card κ = p ^ f) :
    (frobeniusOver κ X).left = End.asHom (End.of
      (Stacks.Frobenius.absoluteFrobenius X.left p
        (Stacks.Frobenius.isInCharacteristic_of_over X)) ^ f) := by
  rw [← geometricFrobenius_eq_frobeniusOver X p f hcard]
  rfl

/-- The Frobenius is a morphism over `Spec κ`. -/
@[simp]
lemma frobeniusOver_left_comp_hom (X : Over (Spec (.of κ))) :
    (frobeniusOver κ X).left ≫ X.hom = X.hom :=
  Over.w (frobeniusOver κ X)

/-- The Frobenius is the identity on the underlying topological space. -/
@[weil "def_fk203_frobenius_endomorphism_scheme", simp]
lemma frobeniusOver_left_base (X : Over (Spec (.of κ))) :
    (frobeniusOver κ X).left.base = 𝟙 (X.left : TopCat) := by
  have : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ _⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card κ (ringChar κ)
  rw [frobeniusOver_left_eq X (ringChar κ) n hn]
  exact Scheme.Hom.pow_base_eq_id (Stacks.Frobenius.absoluteFrobenius_base _ _ _) n

/-- The Frobenius fixes every point. -/
@[simp]
lemma frobeniusOver_left_apply (X : Over (Spec (.of κ))) (x : X.left) :
    (frobeniusOver κ X).left x = x := by
  rw [frobeniusOver_left_base]
  rfl

/-- Every open set is its own inverse image under the Frobenius. -/
@[simp]
lemma frobeniusOver_left_preimage (X : Over (Spec (.of κ))) (U : X.left.Opens) :
    (frobeniusOver κ X).left ⁻¹ᵁ U = U := by
  ext x
  change (frobeniusOver κ X).left x ∈ U ↔ x ∈ U
  rw [frobeniusOver_left_apply]

/-- Identifying an open set with its inverse image, the map on sections induced by the
Frobenius is the `q`-th power map, `q = Fintype.card κ`. -/
@[weil "def_fk203_frobenius_endomorphism_scheme", simp]
lemma frobeniusOver_left_appLE_apply (X : Over (Spec (.of κ))) (U : X.left.Opens)
    (e : U ≤ (frobeniusOver κ X).left ⁻¹ᵁ U) (g : Γ(X.left, U)) :
    (frobeniusOver κ X).left.appLE U U e g = g ^ Fintype.card κ := by
  have : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ _⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card κ (ringChar κ)
  have h := frobeniusOver_left_eq X (ringChar κ) n hn
  rw [hn]
  have key := Scheme.Hom.pow_appLE_apply_of_appLE_apply
    (Stacks.Frobenius.absoluteFrobenius_base X.left (ringChar κ)
      (Stacks.Frobenius.isInCharacteristic_of_over X))
    (Stacks.Frobenius.absoluteFrobenius_appLE_apply X.left (ringChar κ)
      (Stacks.Frobenius.isInCharacteristic_of_over X)) n U (h ▸ e) g
  rw [Scheme.Hom.appLE_eq_of_eq h e]
  exact key

/-- On global sections, the Frobenius is the `q`-th power map, `q = Fintype.card κ`. -/
@[simp]
lemma frobeniusOver_left_appTop_apply (X : Over (Spec (.of κ))) (g : Γ(X.left, ⊤)) :
    (frobeniusOver κ X).left.appTop g = g ^ Fintype.card κ := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact frobeniusOver_left_appLE_apply X ⊤ _ g

/-- **Characterisation of the Frobenius.** An endomorphism of a scheme over `κ` which is the
identity on the underlying topological space and the `q`-th power map on the sections over every
open set, `q = Fintype.card κ`, is the Frobenius. -/
@[weil "def_fk203_frobenius_endomorphism_scheme"]
theorem eq_frobeniusOver_left (X : Over (Spec (.of κ))) (F : X.left ⟶ X.left)
    (hF : F.base = 𝟙 (X.left : TopCat))
    (hF' : ∀ (U : X.left.Opens) (e : U ≤ F ⁻¹ᵁ U) (g : Γ(X.left, U)),
      F.appLE U U e g = g ^ Fintype.card κ) :
    F = (frobeniusOver κ X).left := by
  apply Scheme.Hom.ext (hF.trans (frobeniusOver_left_base X).symm)
  intro U
  ext g
  have e₃ : (frobeniusOver κ X).left ⁻¹ᵁ U ≤ F ⁻¹ᵁ U := by
    intro x hx
    change F.base x ∈ U
    rw [hF]
    exact (frobeniusOver_left_preimage X U).le hx
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map,
    Scheme.Hom.app_eq_appLE (f := (frobeniusOver κ X).left)]
  have i := frobeniusOver_left_preimage X U
  rw [← Scheme.Hom.appLE_map' F _ i, ← Scheme.Hom.appLE_map' (frobeniusOver κ X).left _ i,
    CommRingCat.comp_apply, CommRingCat.comp_apply, hF', frobeniusOver_left_appLE_apply]

end AlgebraicGeometry
