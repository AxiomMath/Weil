module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArIsomorphism
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArCanonicalFunctor
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.LAdicSystem
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# A–R `l`-adic systems

A projective system `F` of `l`-power torsion `Λ`-modules is *A–R `l`-adic* if it is isomorphic,
in the Artin–Rees category, to an `l`-adic system: there are an `l`-adic system `F'` and an
A–R isomorphism `F → F'`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.IsArLAdic`: the predicate that a projective system is A–R
  `l`-adic.
* `CategoryTheory.ProjectiveSystem.ArCategory.isArLAdic`: the same property, as a property of
  objects of the A–R category.

## Main results

* `CategoryTheory.ProjectiveSystem.isArLAdic_iff_exists_representsArIso`: `F` is A–R `l`-adic
  iff some `f : F[r] ⟶ F'` to an `l`-adic system `F'` represents an A–R isomorphism.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.isArLAdic`: an `l`-adic system is A–R `l`-adic.
* `CategoryTheory.ProjectiveSystem.IsArLAdic.of_arIso`, `isArLAdic_congr`: being A–R `l`-adic
  is invariant under A–R isomorphisms; in particular (`IsArLAdic.of_iso`) under isomorphisms
  of projective systems.
* `CategoryTheory.ProjectiveSystem.ArCategory.isArLAdic.isClosedUnderIsomorphisms`: the
  property of objects of the A–R category is closed under isomorphisms.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- A projective system `F` of `l`-power torsion `Λ`-modules is *A–R `l`-adic* if there are an
`l`-adic system `F'` and an A–R isomorphism `F → F'`, i.e. an isomorphism
`ArCategory.of F ≅ ArCategory.of F'` of the A–R category. -/
@[weil "def_fk112_ar_l_adic_system"]
def IsArLAdic (F : ProjectiveSystem.{v} Λ l) : Prop :=
  ∃ F' : ProjectiveSystem.{v} Λ l, IsLAdicSystem F' ∧ Nonempty (ArCategory.of F ≅ ArCategory.of F')

lemma isArLAdic_iff (F : ProjectiveSystem.{v} Λ l) :
    IsArLAdic F ↔ ∃ F' : ProjectiveSystem.{v} Λ l,
      IsLAdicSystem F' ∧ Nonempty (ArCategory.of F ≅ ArCategory.of F') :=
  Iff.rfl

/-- `F` is A–R `l`-adic iff some morphism `f : F[r] ⟶ F'` to an `l`-adic system `F'` represents
an A–R isomorphism. -/
lemma isArLAdic_iff_exists_representsArIso (F : ProjectiveSystem.{v} Λ l) :
    IsArLAdic F ↔ ∃ (F' : ProjectiveSystem.{v} Λ l) (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ F'),
      IsLAdicSystem F' ∧ RepresentsArIso r f := by
  constructor
  · rintro ⟨F', hF', ⟨e⟩⟩
    obtain ⟨r, f, hf, h⟩ := (ArCategory.isIso_iff_exists_representsArIso e.hom).1 inferInstance
    exact ⟨F', r, f, hF', h⟩
  · rintro ⟨F', r, f, hF', h⟩
    exact ⟨F', hF', ⟨h.iso⟩⟩

lemma RepresentsArIso.isArLAdic {F F' : ProjectiveSystem.{v} Λ l} {r : ℕ}
    {f : (shift (r : ℤ)).obj F ⟶ F'} (h : RepresentsArIso r f) (hF' : IsLAdicSystem F') :
    IsArLAdic F :=
  ⟨F', hF', ⟨h.iso⟩⟩

/-- An `l`-adic system is A–R `l`-adic. -/
lemma IsLAdicSystem.isArLAdic {F : ProjectiveSystem.{v} Λ l} (hF : IsLAdicSystem F) :
    IsArLAdic F :=
  ⟨F, hF, ⟨Iso.refl _⟩⟩

namespace IsArLAdic

variable {F G : ProjectiveSystem.{v} Λ l}

/-- An `l`-adic system `F'` A–R isomorphic to an A–R `l`-adic system `F`. -/
noncomputable def lAdicSystem (hF : IsArLAdic F) : ProjectiveSystem.{v} Λ l :=
  hF.choose

lemma isLAdicSystem_lAdicSystem (hF : IsArLAdic F) : IsLAdicSystem hF.lAdicSystem :=
  hF.choose_spec.1

/-- The A–R isomorphism `F ≅ hF.lAdicSystem`. -/
noncomputable def arIso (hF : IsArLAdic F) :
    ArCategory.of F ≅ ArCategory.of hF.lAdicSystem :=
  hF.choose_spec.2.some

/-- Being A–R `l`-adic is invariant under A–R isomorphisms. -/
lemma of_arIso (e : ArCategory.of F ≅ ArCategory.of G) (hG : IsArLAdic G) : IsArLAdic F :=
  ⟨hG.lAdicSystem, hG.isLAdicSystem_lAdicSystem, ⟨e ≪≫ hG.arIso⟩⟩

/-- Being A–R `l`-adic is invariant under isomorphisms of projective systems. -/
lemma of_iso (e : F ≅ G) (hG : IsArLAdic G) : IsArLAdic F :=
  of_arIso ((toArCategory Λ l).mapIso e) hG

end IsArLAdic

/-- A–R isomorphic projective systems are simultaneously A–R `l`-adic. -/
lemma isArLAdic_congr {F G : ProjectiveSystem.{v} Λ l} (e : ArCategory.of F ≅ ArCategory.of G) :
    IsArLAdic F ↔ IsArLAdic G :=
  ⟨IsArLAdic.of_arIso e.symm, IsArLAdic.of_arIso e⟩

/-- A system A–R isomorphic to an `l`-adic system is A–R `l`-adic. -/
lemma IsLAdicSystem.isArLAdic_of_arIso {F G : ProjectiveSystem.{v} Λ l}
    (e : ArCategory.of F ≅ ArCategory.of G) (hG : IsLAdicSystem G) : IsArLAdic F :=
  ⟨G, hG, ⟨e⟩⟩

namespace ArCategory

/-- The property of objects of the A–R category of being A–R `l`-adic. -/
def isArLAdic : ObjectProperty (ArCategory.{v} Λ l) :=
  fun X => IsArLAdic X.obj

@[simp]
lemma isArLAdic_of (F : ProjectiveSystem.{v} Λ l) : isArLAdic (ArCategory.of F) ↔ IsArLAdic F :=
  Iff.rfl

instance isArLAdic.isClosedUnderIsomorphisms :
    (isArLAdic : ObjectProperty (ArCategory.{v} Λ l)).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := IsArLAdic.of_arIso (F := Y.obj) (G := X.obj) e.symm hX

end ArCategory

end ProjectiveSystem

end CategoryTheory
