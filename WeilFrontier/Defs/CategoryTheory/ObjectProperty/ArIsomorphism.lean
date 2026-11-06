module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArCategory

/-!
# Artin–Rees isomorphisms

An *A–R isomorphism* is an isomorphism of the Artin–Rees category `ArCategory Λ l` of projective
systems of `l`-power torsion `Λ`-modules, that is, a morphism `φ` of that category with `IsIso φ`.
A morphism `f : F[r] ⟶ G` of projective systems *represents an A–R isomorphism* if the A–R
morphism `[r, f] : F ⟶ G` it represents is an isomorphism of the A–R category.

## Main definitions

* `CategoryTheory.ProjectiveSystem.RepresentsArIso r f`: the morphism `f : F[r] ⟶ G` represents
  an A–R isomorphism, i.e. `[r, f]` is an isomorphism of the A–R category.

## Main results

* `CategoryTheory.ProjectiveSystem.RepresentsArIso.shiftMap_comp_iff`: whether `(r, f)`
  represents an A–R isomorphism depends only on the class `[r, f]`.
* `CategoryTheory.ProjectiveSystem.ArCategory.homMk_natMap`: `[r, ε^r_F]` is the identity of `F`;
  in particular `ε^r_F` represents an A–R isomorphism (`representsArIso_natMap`).
* `CategoryTheory.ProjectiveSystem.representsArIso_natMap_comp`: an isomorphism `f : F ⟶ G` of
  projective systems, precomposed with `ε^r_F`, represents an A–R isomorphism.
* `CategoryTheory.ProjectiveSystem.RepresentsArIso.comp`: representatives of A–R isomorphisms
  compose.
* `CategoryTheory.ProjectiveSystem.ArCategory.isIso_iff_exists_representsArIso`: a morphism of
  the A–R category is an isomorphism iff one (equivalently, every) representative represents an
  A–R isomorphism.

## Implementation notes

The A–R isomorphisms themselves are not given a new name: they are the isomorphisms
`ArCategory.of F ≅ ArCategory.of G` (and the predicate `IsIso`) of the category
`ArCategory Λ l`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}



/-- A morphism `f : F[r] ⟶ G` of projective systems *represents an A–R isomorphism* if the A–R
morphism `[r, f] : F ⟶ G` is an isomorphism of the A–R category. An *A–R isomorphism* is an
isomorphism of the A–R category `ArCategory Λ l`. -/
@[weil "def_fk112_ar_isomorphism"]
def RepresentsArIso {F G : ProjectiveSystem.{v} Λ l} (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G) :
    Prop :=
  IsIso (ArCategory.homMk r f)

lemma representsArIso_iff {F G : ProjectiveSystem.{v} Λ l} (r : ℕ)
    (f : (shift (r : ℤ)).obj F ⟶ G) : RepresentsArIso r f ↔ IsIso (ArCategory.homMk r f) :=
  Iff.rfl

namespace RepresentsArIso

variable {F G H : ProjectiveSystem.{v} Λ l}

lemma isIso {r : ℕ} {f : (shift (r : ℤ)).obj F ⟶ G} (h : RepresentsArIso r f) :
    IsIso (ArCategory.homMk r f) := h

/-- The A–R isomorphism `F ≅ G` represented by `f`. -/
noncomputable def iso {r : ℕ} {f : (shift (r : ℤ)).obj F ⟶ G} (h : RepresentsArIso r f) :
    ArCategory.of F ≅ ArCategory.of G :=
  haveI := h.isIso
  asIso (ArCategory.homMk r f)

@[simp]
lemma iso_hom {r : ℕ} {f : (shift (r : ℤ)).obj F ⟶ G} (h : RepresentsArIso r f) :
    h.iso.hom = ArCategory.homMk r f := rfl

/-- Replacing `(r, f)` by the equivalent pair `(t, f ∘ (F[t] ⟶ F[r]))` does not change whether it
represents an A–R isomorphism. -/
lemma shiftMap_comp_iff {r t : ℕ} (h : r ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G) :
    RepresentsArIso t (shiftMap F h ≫ f) ↔ RepresentsArIso r f := by
  rw [representsArIso_iff, representsArIso_iff, ArCategory.homMk_shiftMap_comp]

/-- Representatives of A–R isomorphisms compose: if `f : F[r] ⟶ G` and `g : G[s] ⟶ H` represent
A–R isomorphisms, so does `g ∘ f[s] : F[r + s] ⟶ H`. -/
lemma comp {r s : ℕ} {f : (shift (r : ℤ)).obj F ⟶ G} {g : (shift (s : ℤ)).obj G ⟶ H}
    (hf : RepresentsArIso r f) (hg : RepresentsArIso s g) :
    RepresentsArIso (r + s) (shiftShift F r s ≫ (shift (s : ℤ)).map f ≫ g) := by
  have := hf.isIso
  have := hg.isIso
  rw [representsArIso_iff, ← ArCategory.homMk_comp_homMk]
  infer_instance

end RepresentsArIso

namespace ArCategory

/-- `[r, ε^r_F]` is the identity of `F` in the A–R category. -/
@[simp]
lemma homMk_natMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    ArCategory.homMk r (natMap F r) = 𝟙 (ArCategory.of F) := by
  rw [← shiftMap_comp_natMap F (Nat.zero_le r), ArCategory.homMk_shiftMap_comp,
    ArCategory.id_eq]

/-- A morphism of the A–R category is an isomorphism iff some representative of it represents an
A–R isomorphism. -/
lemma isIso_iff_exists_representsArIso {F G : ProjectiveSystem.{v} Λ l}
    (φ : ArCategory.of F ⟶ ArCategory.of G) :
    IsIso φ ↔ ∃ (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G),
      ArCategory.homMk r f = φ ∧ RepresentsArIso r f := by
  constructor
  · intro hφ
    obtain ⟨r, f, rfl⟩ := ArCategory.homMk_surjective φ
    exact ⟨r, f, rfl, hφ⟩
  · rintro ⟨r, f, rfl, h⟩
    exact h

/-- Every representative of an isomorphism of the A–R category represents an A–R isomorphism. -/
lemma representsArIso_of_isIso {F G : ProjectiveSystem.{v} Λ l} {r : ℕ}
    (f : (shift (r : ℤ)).obj F ⟶ G) [IsIso (ArCategory.homMk r f)] : RepresentsArIso r f :=
  inferInstanceAs (IsIso (ArCategory.homMk r f))

end ArCategory

/-- The natural map `ε^r_F : F[r] ⟶ F` represents an A–R isomorphism (the identity of `F`). -/
lemma representsArIso_natMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    RepresentsArIso r (natMap F r) := by
  rw [representsArIso_iff, ArCategory.homMk_natMap]
  infer_instance

/-- An isomorphism `f : F ⟶ G` of projective systems, precomposed with `ε^r_F : F[r] ⟶ F`,
represents an A–R isomorphism. -/
lemma representsArIso_natMap_comp {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) [IsIso f]
    (r : ℕ) : RepresentsArIso r (natMap F r ≫ f) := by
  refine ⟨ArCategory.homMk 0 (natMap G 0 ≫ inv f), ?_, ?_⟩
  · rw [ArCategory.homMk_comp_homMk, natMap_naturality_assoc (natMap F r ≫ f) 0, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id,
      shiftShift_comp_natMap_zero_assoc, shiftMap_comp_natMap, ArCategory.homMk_natMap]
  · rw [ArCategory.homMk_comp_homMk, Functor.map_comp, Category.assoc, ← Category.assoc
      ((shift (r : ℤ)).map (inv f)), natMap_naturality, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, shiftShift_comp_shift_map_natMap_zero_assoc, shiftMap_comp_natMap,
      ArCategory.homMk_natMap]

end ProjectiveSystem

end CategoryTheory
