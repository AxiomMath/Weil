module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.CategoryTheory.Sites.Finite

/-!
# Finite étale coverings

An *étale covering* of a scheme `U` in the sense of [FK, I.2] is a finite family
`(φᵢ : Uᵢ ⟶ U)_{i ∈ I}` of étale morphisms whose images cover `U`, i.e.
`U = ⋃ᵢ φᵢ(Uᵢ)`.

Mathlib's étale precoverage `AlgebraicGeometry.Scheme.etalePrecoverage` consists of jointly
surjective families of étale morphisms with no finiteness condition. The coverings here are
its finite members, and over a quasi-compact scheme every member of the étale precoverage is
refined by a finite subfamily, since étale morphisms are open.

## Main definitions

* `AlgebraicGeometry.Scheme.IsEtaleCovering`: the family `φ : ∀ i, V i ⟶ U` is a finite,
  jointly surjective family of étale morphisms.
* `AlgebraicGeometry.Scheme.finiteEtalePrecoverage`: the precoverage of finite jointly
  surjective families of étale morphisms, `etalePrecoverage ⊓ Precoverage.finite Scheme`.

## Main results

* `AlgebraicGeometry.Scheme.isEtaleCovering_iff_ofArrows_mem_etalePrecoverage`: for a finite
  index type, being an étale covering is membership of `Presieve.ofArrows` in Mathlib's
  étale precoverage.
* `AlgebraicGeometry.Scheme.IsEtaleCovering.ofArrows_mem_finiteEtalePrecoverage`: an étale
  covering gives a member of `finiteEtalePrecoverage`.
* `AlgebraicGeometry.Scheme.isEtaleCovering_left_iff_ofArrows_mem_smallEtaleTopology`: in the
  small étale site, a finite family of morphisms is an étale covering exactly when the sieve
  it generates covers in `smallEtaleTopology`.
* `AlgebraicGeometry.Scheme.exists_finite_isEtaleCovering`: over a quasi-compact scheme, every
  jointly surjective family of étale morphisms has a finite subfamily that is an étale covering.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A family `φ : ∀ i, V i ⟶ U` of morphisms of schemes is an *étale covering* of `U` if the
index type is finite, every `φ i` is étale, and the images of the `φ i` cover `U`. -/
@[weil "def_fk102_etale_covering"]
structure IsEtaleCovering {U : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}}
    (φ : ∀ i, V i ⟶ U) : Prop where
  /-- The family is finite. -/
  finite : Finite ι
  /-- Every member of the family is étale. -/
  etale : ∀ i, Etale (φ i)
  /-- The images of the members cover `U`. -/
  iUnion_range : ⋃ i, Set.range (φ i) = Set.univ

/-- The precoverage on schemes by finite jointly surjective families of étale morphisms. -/
def finiteEtalePrecoverage : Precoverage Scheme.{u} :=
  etalePrecoverage ⊓ Precoverage.finite Scheme.{u}

variable {U : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}} {φ : ∀ i, V i ⟶ U}

lemma isEtaleCovering_iff :
    IsEtaleCovering φ ↔
      Finite ι ∧ (∀ i, Etale (φ i)) ∧ ⋃ i, Set.range (φ i) = Set.univ :=
  ⟨fun h ↦ ⟨h.finite, h.etale, h.iUnion_range⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

lemma IsEtaleCovering.exists_mem_range (h : IsEtaleCovering φ) (x : U) :
    ∃ i, x ∈ Set.range (φ i) := by
  have : x ∈ ⋃ i, Set.range (φ i) := h.iUnion_range ▸ Set.mem_univ x
  simpa using this

lemma iUnion_range_eq_univ_iff :
    ⋃ i, Set.range (φ i) = Set.univ ↔ ∀ x : U, ∃ i, x ∈ Set.range (φ i) := by
  simp [Set.eq_univ_iff_forall]

/-- For a finite index type, a family is an étale covering if and only if the presieve it
generates is in Mathlib's étale precoverage. -/
lemma isEtaleCovering_iff_ofArrows_mem_etalePrecoverage [Finite ι] :
    IsEtaleCovering φ ↔ Presieve.ofArrows V φ ∈ etalePrecoverage U := by
  refine (isEtaleCovering_iff.trans ?_).trans (ofArrows_mem_precoverage_iff (P := @Etale)).symm
  rw [iUnion_range_eq_univ_iff]
  exact ⟨fun ⟨_, h₂, h₃⟩ ↦ ⟨h₃, h₂⟩, fun ⟨h₃, h₂⟩ ↦ ⟨inferInstance, h₂, h₃⟩⟩

lemma IsEtaleCovering.ofArrows_mem_etalePrecoverage (h : IsEtaleCovering φ) :
    Presieve.ofArrows V φ ∈ etalePrecoverage U :=
  have := h.finite
  isEtaleCovering_iff_ofArrows_mem_etalePrecoverage.mp h

lemma ofArrows_mem_finite_of_finite [Finite ι] :
    Presieve.ofArrows V φ ∈ Precoverage.finite Scheme.{u} U := by
  rw [Precoverage.mem_finite_iff]
  refine (Set.finite_range fun i ↦ (⟨V i, φ i⟩ : Σ Y, Y ⟶ U)).subset ?_
  rintro ⟨Y, g⟩ hg
  obtain ⟨i⟩ := hg
  exact ⟨i, rfl⟩

lemma IsEtaleCovering.ofArrows_mem_finiteEtalePrecoverage (h : IsEtaleCovering φ) :
    Presieve.ofArrows V φ ∈ finiteEtalePrecoverage U :=
  have := h.finite
  ⟨h.ofArrows_mem_etalePrecoverage, ofArrows_mem_finite_of_finite⟩

lemma finiteEtalePrecoverage_le_etalePrecoverage :
    finiteEtalePrecoverage.{u} ≤ etalePrecoverage :=
  inf_le_left

/-- In the small étale site of `X`, a finite family of morphisms with target `W` is an étale
covering (of the underlying schemes) if and only if the sieve it generates covers `W` in the
small étale topology. -/
lemma isEtaleCovering_left_iff_ofArrows_mem_smallEtaleTopology {X : Scheme.{u}} {W : X.Etale}
    {Z : ι → X.Etale} [Finite ι] (f : ∀ i, Z i ⟶ W) :
    IsEtaleCovering (fun i ↦ (f i).left) ↔
      Sieve.ofArrows Z f ∈ X.smallEtaleTopology W := by
  rw [ofArrows_mem_smallEtaleTopology_iff, isEtaleCovering_iff]
  exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨inferInstance, fun _ ↦ inferInstance, h⟩⟩

/-- Over a quasi-compact scheme, every jointly surjective family of étale morphisms has a finite
subfamily which is an étale covering. -/
lemma exists_finite_isEtaleCovering [CompactSpace U] [∀ i, Etale (φ i)]
    (h : ⋃ i, Set.range (φ i) = Set.univ) :
    ∃ s : Finset ι, IsEtaleCovering (fun i : s ↦ φ i) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i ↦ Set.range (φ i))
    (fun i ↦ (φ i).isOpenMap.isOpen_range) h.symm.subset
  refine ⟨s, ⟨inferInstance, fun _ ↦ inferInstance, ?_⟩⟩
  refine Set.eq_univ_of_univ_subset (hs.trans ?_)
  simp only [Set.iUnion_subset_iff]
  intro i hi
  exact Set.subset_iUnion (fun j : s ↦ Set.range (φ j)) ⟨i, hi⟩

end AlgebraicGeometry.Scheme

end
