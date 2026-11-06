module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The category of `φ`-diagrams

Let `A` be a noetherian local ring and `φ : A → k` a ring homomorphism to a field. A
*`φ`-diagram* is a pair `(B, ψ)` where `B = (A[X₁, …, Xₙ] / I)_q` is the localization of a
quotient of a polynomial ring over `A` at a prime `q`, such that the canonical map `A → B` is a
local-étale homomorphism, and `ψ : B → k` is a local homomorphism with `ψ ∘ (A → B) = φ`. A
morphism `(B₁, ψ₁) → (B₂, ψ₂)` is an `A`-algebra homomorphism `u : B₁ → B₂` with `ψ₂ ∘ u = ψ₁`.
These form a category `HenselizationDiagram A φ`, the category `𝒟(A, φ)` whose colimit is the
Henselization of `A` with respect to `φ`.

## Main definitions

* `HenselizationDiagram A φ`: the objects, recorded by the data `(n, I, q)` of the ring
  `(A[X₁, …, Xₙ] / I)_q` together with the map `ψ`.
* `HenselizationDiagram.Ring D`: the local ring `(A[X₁, …, Xₙ] / I)_q` of an object `D`.
* `HenselizationDiagram.Hom`: morphisms, and the category instance.

## Main results

* `HenselizationDiagram.Hom.isLocalHom`: every morphism is a local homomorphism.
* `HenselizationDiagram.ker_ψ`: the kernel of `ψ` is the maximal ideal of `B`.
* `HenselizationDiagram.isLocalHom_φ`: the existence of an object forces `φ` to be local.

## Implementation notes

The source requires morphisms to be local homomorphisms. This condition is automatic: if
`ψ₂ ∘ u = ψ₁` with `ψ₁` local then `u` is local (`HenselizationDiagram.Hom.isLocalHom`), so it is
not a field of `HenselizationDiagram.Hom`. The source assumes `φ` local; the definition does not
need it, and an object exists only when `φ` is local (`HenselizationDiagram.isLocalHom_φ`).

The source's phrase "a ring of the form `(A[X₁, …, Xₙ] / I)_q`" is made precise by taking the
data `(n, I, q)` as part of the object, so that `HenselizationDiagram A φ` lives in the same
universe as `A` and `k`, and is a small category when they lie in one universe.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {k : Type v} [Field k]

/-- An object of the category `𝒟(A, φ)` of `φ`-diagrams: a natural number `n`, an ideal `I` of
`A[X₁, …, Xₙ]` and a prime `q` of `A[X₁, …, Xₙ] / I`, such that `A → B := (A[X₁, …, Xₙ] / I)_q`
is local-étale, together with a local homomorphism `ψ : B → k` with `ψ ∘ (A → B) = φ`. -/
@[weil "def_fk101_henselization_diagram"]
structure HenselizationDiagram (φ : A →+* k) where
  /-- The number of variables. -/
  n : ℕ
  /-- The ideal of the polynomial ring. -/
  I : Ideal (MvPolynomial (Fin n) A)
  /-- The prime of the quotient at which one localizes. -/
  q : Ideal (MvPolynomial (Fin n) A ⧸ I)
  [isPrime : q.IsPrime]
  /-- The canonical map `A → (A[X₁, …, Xₙ] / I)_q` is a local homomorphism. -/
  [isLocalHom_algebraMap : IsLocalHom (algebraMap A (Localization.AtPrime q))]
  /-- The canonical map `A → (A[X₁, …, Xₙ] / I)_q` is local-étale. -/
  isEtaleLocalHom :
    RingHom.IsEtaleLocalHom (A := A) (B := Localization.AtPrime q) (algebraMap A _)
  /-- The map to the field `k`. -/
  ψ : Localization.AtPrime q →+* k
  [isLocalHom_ψ : IsLocalHom ψ]
  /-- `ψ` restricts to `φ` on `A`. -/
  ψ_comp_algebraMap : ψ.comp (algebraMap A (Localization.AtPrime q)) = φ

namespace HenselizationDiagram

variable {A} {φ : A →+* k}

attribute [instance] isPrime isLocalHom_algebraMap isLocalHom_ψ

/-- The local ring `(A[X₁, …, Xₙ] / I)_q` of a `φ`-diagram. -/
abbrev Ring (D : HenselizationDiagram A φ) : Type u :=
  Localization.AtPrime D.q

theorem ψ_algebraMap (D : HenselizationDiagram A φ) (a : A) :
    D.ψ (algebraMap A D.Ring a) = φ a :=
  RingHom.congr_fun D.ψ_comp_algebraMap a

/-- The kernel of `ψ` is the maximal ideal of `B`. -/
theorem ker_ψ (D : HenselizationDiagram A φ) : RingHom.ker D.ψ = maximalIdeal D.Ring := by
  refine le_antisymm (le_maximalIdeal (RingHom.ker_ne_top D.ψ)) fun x hx => ?_
  rw [RingHom.mem_ker]
  by_contra h
  exact (mem_maximalIdeal x).1 hx (isUnit_of_map_unit D.ψ x (Ne.isUnit h))

/-- The existence of a `φ`-diagram forces `φ` to be a local homomorphism. -/
theorem isLocalHom_φ (D : HenselizationDiagram A φ) : IsLocalHom φ := by
  rw [← D.ψ_comp_algebraMap]
  infer_instance

/-- A morphism of `φ`-diagrams `(B₁, ψ₁) → (B₂, ψ₂)`: an `A`-algebra homomorphism `u : B₁ → B₂`
with `ψ₂ ∘ u = ψ₁`. -/
@[ext, weil "def_fk101_henselization_diagram"]
structure Hom (D₁ D₂ : HenselizationDiagram A φ) where
  /-- The underlying `A`-algebra homomorphism. -/
  toAlgHom : D₁.Ring →ₐ[A] D₂.Ring
  /-- Compatibility with the maps to `k`. -/
  ψ_comp : D₂.ψ.comp toAlgHom.toRingHom = D₁.ψ

@[weil "def_fk101_henselization_diagram"]
noncomputable instance instCategory : Category (HenselizationDiagram A φ) where
  Hom := Hom
  id D := ⟨AlgHom.id A D.Ring, RingHom.ext fun _ => rfl⟩
  comp f g := ⟨g.toAlgHom.comp f.toAlgHom, by
    rw [← f.ψ_comp, ← g.ψ_comp]
    rfl⟩

@[simp]
theorem id_toAlgHom (D : HenselizationDiagram A φ) : (𝟙 D : D ⟶ D).toAlgHom = AlgHom.id A D.Ring :=
  rfl

@[simp]
theorem comp_toAlgHom {D₁ D₂ D₃ : HenselizationDiagram A φ} (f : D₁ ⟶ D₂) (g : D₂ ⟶ D₃) :
    (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom :=
  rfl

variable {D₁ D₂ : HenselizationDiagram A φ}

@[simp]
theorem Hom.ψ_apply (f : D₁ ⟶ D₂) (x : D₁.Ring) : D₂.ψ (f.toAlgHom x) = D₁.ψ x :=
  RingHom.congr_fun f.ψ_comp x

/-- Morphisms of `φ`-diagrams are determined by their underlying `A`-algebra homomorphisms. -/
@[ext]
theorem hom_ext {f g : D₁ ⟶ D₂} (h : f.toAlgHom = g.toAlgHom) : f = g :=
  Hom.ext h

/-- Every morphism of `φ`-diagrams is a local homomorphism, as the source requires. -/
instance Hom.isLocalHom (f : D₁ ⟶ D₂) : IsLocalHom f.toAlgHom.toRingHom where
  map_nonunit x hx := isUnit_of_map_unit D₁.ψ x <| by
    rw [← f.ψ_apply]
    exact hx.map D₂.ψ

/-- Build a morphism of `φ`-diagrams from an `A`-algebra homomorphism compatible with `ψ`. -/
@[simps]
def homMk (u : D₁.Ring →ₐ[A] D₂.Ring) (hu : ∀ x, D₂.ψ (u x) = D₁.ψ x) : D₁ ⟶ D₂ :=
  ⟨u, RingHom.ext hu⟩

end HenselizationDiagram
