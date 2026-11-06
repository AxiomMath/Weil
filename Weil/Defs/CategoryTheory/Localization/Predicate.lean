module

public import Weil.Attr
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Factorizations of functors through the derived category

Let `A` be an abelian category, `K(A)` its homotopy category of `ℤ`-indexed cochain complexes,
`D(A)` its derived category and `Q : K(A) ⥤ D(A)` the localization functor at the
quasi-isomorphisms. For a functor `G : K(A) ⥤ E`, a factorization of `G` through `D(A)` is a
functor `G' : D(A) ⥤ E` together with an isomorphism `Q ⋙ G' ≅ G`.

Such a factorization exists if and only if `G` sends quasi-isomorphisms to isomorphisms, and it
is unique up to a unique isomorphism compatible with the given isomorphisms.

## Main definitions

* `DerivedCategory.FactorizationThroughDerived G G'`: the structure of a factorization of
  `G : K(A) ⥤ E` through `D(A)` on `G' : D(A) ⥤ E`; it is Mathlib's
  `CategoryTheory.Localization.Lifting` for the localization functor `DerivedCategory.Qh`.

## Main results

* `DerivedCategory.FactorizationThroughDerived.ofEq`: a strict equality `Qh ⋙ G' = G` gives a
  factorization.
* `DerivedCategory.FactorizationThroughDerived.isInvertedBy`: a functor which factors through
  `D(A)` sends quasi-isomorphisms to isomorphisms.
* `DerivedCategory.nonempty_factorizationThroughDerived_iff`: `G` has a factorization through
  `D(A)` if and only if it inverts the quasi-isomorphisms.
* `DerivedCategory.FactorizationThroughDerived.uniqueIso`,
  `DerivedCategory.FactorizationThroughDerived.uniqueIso_compat`,
  `DerivedCategory.FactorizationThroughDerived.ext_iso`: two factorizations of `G` are
  isomorphic by a unique isomorphism compatible with the structure isomorphisms.

## Implementation notes

The derived category is a localization of `K(A)` only up to equivalence, so the factorization
is required to commute up to a specified isomorphism `Qh ⋙ G' ≅ G` rather than strictly; a
strict factorization gives one (`DerivedCategory.FactorizationThroughDerived.ofEq`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

/- FK define a factorization by the strict equality
`G' ∘ Q = G`; following the standard meaning it is stated up to the isomorphism of
`Localization.Lifting`. -/

@[expose] public noncomputable section

open CategoryTheory

universe w v u u'

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {E : Type u'} [Category E]

/-- A factorization of a functor `G : K(A) ⥤ E` through the derived category: an isomorphism
`Qh ⋙ G' ≅ G`, where `Qh : K(A) ⥤ D(A)` is the localization functor. -/
@[weil "def_fka2_factorization_through_derived"]
abbrev FactorizationThroughDerived (G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E)
    (G' : DerivedCategory C ⥤ E) : Type _ :=
  Localization.Lifting Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) G G'

namespace FactorizationThroughDerived

variable {G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E} {G' : DerivedCategory C ⥤ E}

/-- The isomorphism `Qh ⋙ G' ≅ G` of a factorization. -/
def iso (h : FactorizationThroughDerived G G') : Qh ⋙ G' ≅ G :=
  letI := h
  Localization.Lifting.iso Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) G G'

/-- A factorization built from an isomorphism `Qh ⋙ G' ≅ G`. -/
@[instance_reducible]
def ofIso (e : Qh ⋙ G' ≅ G) : FactorizationThroughDerived G G' :=
  ⟨e⟩

@[simp]
lemma iso_ofIso (e : Qh ⋙ G' ≅ G) : (ofIso e).iso = e :=
  rfl

/-- A strict factorization `Qh ⋙ G' = G` is a factorization. -/
@[instance_reducible]
def ofEq (h : Qh ⋙ G' = G) : FactorizationThroughDerived G G' :=
  ofIso (eqToIso h)

/-- Any functor `G' : D(A) ⥤ E` is a factorization of `Qh ⋙ G'`. -/
@[instance_reducible]
def compQh (G' : DerivedCategory C ⥤ E) : FactorizationThroughDerived (Qh ⋙ G') G' :=
  ofEq rfl

/-- A functor which factors through `D(A)` sends quasi-isomorphisms to isomorphisms. -/
lemma isInvertedBy (h : FactorizationThroughDerived G G') :
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy G := by
  intro X Y f hf
  have : IsIso (Qh.map f) :=
    Localization.inverts Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) f hf
  have : IsIso ((Qh ⋙ G').map f) := by
    dsimp
    infer_instance
  exact (NatIso.isIso_map_iff h.iso f).1 this

/-- The factorization of a functor inverting quasi-isomorphisms given by
`Localization.lift`. -/
@[instance_reducible]
def lift (G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E)
    (hG : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy G) :
    FactorizationThroughDerived G (Localization.lift G hG Qh) :=
  Localization.liftingLift G hG Qh

/-- Two factorizations of `G` through `D(A)` are canonically isomorphic. -/
def uniqueIso {G'₁ G'₂ : DerivedCategory C ⥤ E} (h₁ : FactorizationThroughDerived G G'₁)
    (h₂ : FactorizationThroughDerived G G'₂) : G'₁ ≅ G'₂ :=
  letI := h₁
  letI := h₂
  Localization.liftNatIso Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) G G G'₁ G'₂
    (Iso.refl G)

/-- The canonical isomorphism between two factorizations is compatible with their structure
isomorphisms. -/
lemma uniqueIso_compat {G'₁ G'₂ : DerivedCategory C ⥤ E}
    (h₁ : FactorizationThroughDerived G G'₁) (h₂ : FactorizationThroughDerived G G'₂)
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (uniqueIso h₁ h₂).hom.app (Qh.obj X) ≫ h₂.iso.hom.app X = h₁.iso.hom.app X := by
  let := h₁
  let := h₂
  simp [uniqueIso, Localization.liftNatIso, Localization.liftNatTrans_app, iso]

/-- An isomorphism between two factorizations which is compatible with their structure
isomorphisms is the canonical one. -/
lemma ext_iso {G'₁ G'₂ : DerivedCategory C ⥤ E}
    (h₁ : FactorizationThroughDerived G G'₁) (h₂ : FactorizationThroughDerived G G'₂)
    (e : G'₁ ≅ G'₂)
    (he : ∀ X, e.hom.app (Qh.obj X) ≫ h₂.iso.hom.app X = h₁.iso.hom.app X) :
    e = uniqueIso h₁ h₂ := by
  ext1
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (fun X => ?_)
  rw [← cancel_mono (h₂.iso.hom.app X), he, uniqueIso_compat]

/-- The factorization of `G` through `D(A)` is unique up to a unique compatible isomorphism. -/
lemma existsUnique_iso {G'₁ G'₂ : DerivedCategory C ⥤ E}
    (h₁ : FactorizationThroughDerived G G'₁) (h₂ : FactorizationThroughDerived G G'₂) :
    ∃! e : G'₁ ≅ G'₂, ∀ X, e.hom.app (Qh.obj X) ≫ h₂.iso.hom.app X = h₁.iso.hom.app X :=
  ⟨uniqueIso h₁ h₂, uniqueIso_compat h₁ h₂, fun e he => ext_iso h₁ h₂ e he⟩

end FactorizationThroughDerived

/-- A functor `G : K(A) ⥤ E` has a factorization through `D(A)` if and only if it sends
quasi-isomorphisms to isomorphisms. -/
lemma nonempty_factorizationThroughDerived_iff (G : HomotopyCategory C (ComplexShape.up ℤ) ⥤ E) :
    (∃ G' : DerivedCategory C ⥤ E, Nonempty (FactorizationThroughDerived G G')) ↔
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy G :=
  ⟨fun ⟨_, ⟨h⟩⟩ => h.isInvertedBy,
    fun hG => ⟨_, ⟨FactorizationThroughDerived.lift G hG⟩⟩⟩

end DerivedCategory

end
