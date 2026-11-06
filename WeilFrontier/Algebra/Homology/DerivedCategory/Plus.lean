/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Weil.Attr
public import Weil.Attr
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.InvertibilityAtShiftsReductions

/-!
# Cohomology of bounded below objects of the derived category

Let `C` be an abelian category. An object `X` of the bounded below derived category
`DerivedCategory.Plus C` has vanishing cohomology in all sufficiently negative degrees:
there is `m : ℤ` with `Hⁱ(X) = 0` for all `i < m`.

## Main results

* `DerivedCategory.Plus.exists_isZero_homology_of_lt`: for `X : DerivedCategory.Plus C`, there is
  `m` such that `(homologyFunctor C i).obj X` is zero for every `i < m`.
* `DerivedCategory.exists_isZero_homology_of_mem_plus`: the same statement for an object of
  `DerivedCategory C` lying in the bounded below subcategory.

## Implementation notes

Membership in `DerivedCategory.Plus C` is, by definition, being `≥ n` for the canonical
t-structure for some `n`; the vanishing below `n` is `DerivedCategory.Plus.isZero_homology_of_isGE`.
This agrees with the description of `D_+(A)` as the objects isomorphic to a bounded below
complex (`DerivedCategory.exists_iso_Q_obj_of_isGE`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- An object of the bounded below derived category has vanishing cohomology in all
sufficiently negative degrees. -/
@[weil "lem_fka2_dplus_cohomology_bounded_below"]
theorem Plus.exists_isZero_homology_of_lt (X : Plus C) :
    ∃ m : ℤ, ∀ i < m, IsZero ((Plus.homologyFunctor C i).obj X) := by
  obtain ⟨n, hn⟩ := X.2
  have : X.IsGE n := ⟨hn.1⟩
  exact ⟨n, fun i hi ↦ Plus.isZero_homology_of_isGE X n i hi⟩

/-- An object of `DerivedCategory C` in the bounded below subcategory has vanishing
cohomology in all sufficiently negative degrees. -/
theorem exists_isZero_homology_of_mem_plus {X : DerivedCategory C}
    (hX : (TStructure.t : Triangulated.TStructure (DerivedCategory C)).plus X) :
    ∃ m : ℤ, ∀ i < m, IsZero ((homologyFunctor C i).obj X) :=
  Plus.exists_isZero_homology_of_lt (C := C) ⟨X, hX⟩

end DerivedCategory

/-! ### The way-out lemma on the bounded below derived category -/

/-!
# The way-out lemma on the bounded below derived category

Let `C` and `D` be abelian categories and `Φ, Ψ : D⁺(C) ⥤ D⁺(D)` functors between their bounded
below derived categories which commute with the shift, carry admissible triangles to admissible
triangles, and do not lower the degree of vanishing of cohomology: if `H^ν(K) = 0` for `ν < m`,
then `H^ν(Φ K) = H^ν(Ψ K) = 0` for `ν < m`. Let `α : Φ ⟶ Ψ` be a natural transformation and `𝒞`
a class of objects of `C` such that `α` is invertible at `F[j]` for every `F ∈ 𝒞` and every
`j ∈ ℤ`. Then `α` is invertible at every `K ∈ D⁺(C)` all of whose cohomology objects lie in `𝒞`.

The proof fixes a degree `q` and shows that `H^q(α_K)` is invertible. Below the lower bound `a`
of `K` both sides vanish. Otherwise the truncation `τ_{≤q}K` has cohomology in the finite window
`[a, q]`, with the same cohomology objects as `K` there; the objects at every shift of which `α`
is invertible form a strictly full subcategory closed under extensions and shifts, which
contains every `F[j]` with `F ∈ 𝒞`, so it contains `τ_{≤q}K` by dévissage along the truncation
triangles. Finally the inclusion `τ_{≤q}K ⟶ K` is invertible on `H^q` after applying `Φ` and
`Ψ`, since the third vertex `τ_{>q}K` of its truncation triangle lies in `D^{≥q+1}` and both
functors keep it there; the naturality square of `α` then gives the claim.

A functor commuting with the shift which carries admissible triangles to admissible triangles
is triangulated (`CategoryTheory.Functor.isTriangulated_of_map_negMor₃`): admissible triangles
are the triangles whose third morphism, negated, gives a distinguished triangle, and such a
functor preserves zero morphisms and binary products, hence is additive, hence commutes with
negation of morphisms.

## Main results

* `CategoryTheory.Functor.isTriangulated_of_map_negMor₃`: a functor between pretriangulated
  categories commuting with the shift which preserves the triangles whose negated third morphism
  gives a distinguished triangle is triangulated.
* `DerivedCategory.Plus.mem_admissibleTriangles_ι_mapTriangle_iff`: a triangle of `D⁺(C)` is
  admissible in `D(C)` exactly when its negation is distinguished in `D⁺(C)`.
* `DerivedCategory.Plus.isIso_app_of_prop_homology`: the way-out lemma.

## Implementation notes

The source assumes in addition that `α` commutes with the shift and is compatible with
admissible triangles; the argument does not use these, and the statement omits them. It is
stated for arbitrary abelian categories `C` and `D` with derived categories; the source's case
is that of the categories of étale sheaves on schemes `X` and `Y`. The object `F[j]` is
`(DerivedCategory.Plus.singleFunctor C 0).obj F` shifted by `j`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.7.
* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ZeroObject

namespace CategoryTheory.Functor

variable {A : Type*} {B : Type*} [Category* A] [Category* B]
  [HasZeroObject A] [HasZeroObject B] [Preadditive A] [Preadditive B]
  [HasShift A ℤ] [HasShift B ℤ]
  [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
  [Pretriangulated A] [Pretriangulated B]
  (F : A ⥤ B) [F.CommShift ℤ]

/-- The condition that `F` carries every triangle whose negated third morphism gives a
distinguished triangle to a triangle with the same property. For the derived category these
are the admissible triangles (`DerivedCategory.mem_admissibleTriangles_iff`). -/
def MapsNegMor₃Distinguished : Prop :=
  ∀ T : Triangle A, Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distTriang A →
    Triangle.mk (F.mapTriangle.obj T).mor₁ (F.mapTriangle.obj T).mor₂
      (-(F.mapTriangle.obj T).mor₃) ∈ distTriang B

variable {F}

/-- A triangle whose third morphism is zero is distinguished after negating it. -/
lemma _root_.CategoryTheory.Pretriangulated.mk_neg_mem_distTriang_of_mor₃_eq_zero {T : Triangle A}
    (hT : T ∈ distTriang A)
    (h : T.mor₃ = 0) : Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distTriang A :=
  isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [h]))

/-- A functor with `MapsNegMor₃Distinguished` sends a zero object to a zero object. -/
lemma MapsNegMor₃Distinguished.isZero_obj_zero (hF : F.MapsNegMor₃Distinguished) :
    IsZero (F.obj 0) := by
  have h := hF (contractibleTriangle (0 : A))
    (mk_neg_mem_distTriang_of_mor₃_eq_zero (contractible_distinguished _) rfl)
  refine Triangle.isZero₃_of_isIso₁ _ h ?_
  change IsIso (F.map (𝟙 _))
  infer_instance

/-- A functor with `MapsNegMor₃Distinguished` preserves zero morphisms. -/
lemma MapsNegMor₃Distinguished.preservesZeroMorphisms (hF : F.MapsNegMor₃Distinguished) :
    F.PreservesZeroMorphisms where
  map_zero X Y := by
    have h₁ : (0 : X ⟶ Y) = 0 ≫ 𝟙 (0 : A) ≫ 0 := by simp
    have h₂ : 𝟙 (F.obj 0) = 0 := (IsZero.iff_id_eq_zero _).1 hF.isZero_obj_zero
    rw [h₁, F.map_comp, F.map_comp, F.map_id, h₂, zero_comp, comp_zero]

/-- A functor with `MapsNegMor₃Distinguished` carries a distinguished triangle whose third
morphism is zero to a distinguished triangle. -/
lemma MapsNegMor₃Distinguished.map_distinguished_of_mor₃_eq_zero
    (hF : F.MapsNegMor₃Distinguished) {T : Triangle A} (hT : T ∈ distTriang A)
    (h : T.mor₃ = 0) : F.mapTriangle.obj T ∈ distTriang B := by
  have := hF.preservesZeroMorphisms
  have h₀ : (F.mapTriangle.obj T).mor₃ = 0 := by
    change F.map T.mor₃ ≫ _ = 0
    simp [h]
  refine isomorphic_distinguished _ (hF T (mk_neg_mem_distTriang_of_mor₃_eq_zero hT h)) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_)
  simp [h₀]

set_option backward.defeqAttrib.useBackward true in
/-- A functor with `MapsNegMor₃Distinguished` preserves binary products. -/
lemma MapsNegMor₃Distinguished.preservesLimitsOfShape_walkingPair
    (hF : F.MapsNegMor₃Distinguished) :
    PreservesLimitsOfShape (Discrete WalkingPair) F := by
  have := hF.preservesZeroMorphisms
  suffices ∀ (X₁ X₃ : A), IsIso (prodComparison F X₁ X₃) by
    have := fun (X₁ X₃ : A) ↦ PreservesLimitPair.of_iso_prod_comparison F X₁ X₃
    exact ⟨fun {K} ↦ preservesLimit_of_iso_diagram F (diagramIsoPair K).symm⟩
  intro X₁ X₃
  let φ : F.mapTriangle.obj (binaryProductTriangle X₁ X₃) ⟶
      binaryProductTriangle (F.obj X₁) (F.obj X₃) :=
    { hom₁ := 𝟙 _
      hom₂ := prodComparison F X₁ X₃
      hom₃ := 𝟙 _
      comm₁ := by
        dsimp
        ext
        · simp only [Category.assoc, prodComparison_fst, prod.comp_lift, Category.comp_id,
            comp_zero, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
            ← F.map_comp, F.map_id]
        · simp only [Category.assoc, prodComparison_snd, prod.comp_lift, Category.comp_id,
            comp_zero, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd,
            ← F.map_comp, F.map_zero]
      comm₂ := by simp
      comm₃ := by simp }
  exact isIso₂_of_isIso₁₃ φ
    (hF.map_distinguished_of_mor₃_eq_zero (binaryProductTriangle_distinguished X₁ X₃) rfl)
    (binaryProductTriangle_distinguished _ _)
    (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)

/-- A functor with `MapsNegMor₃Distinguished` is additive. -/
lemma MapsNegMor₃Distinguished.additive (hF : F.MapsNegMor₃Distinguished) : F.Additive := by
  have := hF.preservesZeroMorphisms
  have := hF.preservesLimitsOfShape_walkingPair
  exact F.additive_of_preserves_binary_products

/-- **A functor commuting with the shift which preserves the triangles whose negated third
morphism gives a distinguished triangle is triangulated.** -/
theorem isTriangulated_of_map_negMor₃ (hF : F.MapsNegMor₃Distinguished) : F.IsTriangulated where
  map_distinguished T hT := by
    have := hF.additive
    have h := hF (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃))
      (isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (by simp) (by simp) (by simp)))
    refine isomorphic_distinguished _ h _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (show F.map T.mor₁ ≫ 𝟙 _ = 𝟙 _ ≫ F.map T.mor₁ by simp)
        (show F.map T.mor₂ ≫ 𝟙 _ = 𝟙 _ ≫ F.map T.mor₂ by simp) ?_)
    change (F.map T.mor₃ ≫ _) ≫ (shiftFunctor B 1).map (𝟙 _) = 𝟙 _ ≫ (-(F.map (-T.mor₃) ≫ _))
    rw [F.map_neg, Preadditive.neg_comp, neg_neg, Functor.map_id, Category.comp_id,
      Category.id_comp]
    rfl

end CategoryTheory.Functor

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **Admissible triangles of `D⁺(C)`.** A triangle of `D⁺(C)` is admissible as a triangle of
`D(C)` if and only if the triangle with its third morphism negated is distinguished in
`D⁺(C)`. -/
lemma mem_admissibleTriangles_ι_mapTriangle_iff (T : Triangle (Plus C)) :
    ι.mapTriangle.obj T ∈ admissibleTriangles C ↔
      Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distTriang (Plus C) := by
  rw [mem_admissibleTriangles_iff]
  exact (distinguished_iff_of_iso (ι.mapTriangleNegMor₃Iso T)).symm

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

/-- A functor `D⁺(C) ⥤ D⁺(D)` commuting with the shift which carries admissible triangles to
admissible triangles is triangulated. -/
theorem isTriangulated_of_map_admissibleTriangles (Φ : Plus C ⥤ Plus D) [Φ.CommShift ℤ]
    (hΦ : ∀ T : Triangle (Plus C), ι.mapTriangle.obj T ∈ admissibleTriangles C →
      ι.mapTriangle.obj (Φ.mapTriangle.obj T) ∈ admissibleTriangles D) :
    Φ.IsTriangulated := by
  refine Functor.isTriangulated_of_map_negMor₃ fun T hT => ?_
  rw [← mem_admissibleTriangles_ι_mapTriangle_iff] at hT ⊢
  exact hΦ T hT

/-- **The way-out lemma.** Let `Φ, Ψ : D⁺(C) ⥤ D⁺(D)` be functors which commute with the shift,
carry admissible triangles to admissible triangles, and satisfy: if `H^ν(K) = 0` for all
`ν < m`, then `H^ν(Φ K) = H^ν(Ψ K) = 0` for all `ν < m`. Let `α : Φ ⟶ Ψ` be a natural
transformation and `𝒞` a class of objects of `C` such that `α` is invertible at `F[j]` for every
`F ∈ 𝒞` and `j ∈ ℤ`. Then `α` is invertible at every object of `D⁺(C)` all of whose cohomology
objects lie in `𝒞`. -/
@[weil "lem_fk107_way_out_quasi_isomorphism"]
theorem isIso_app_of_prop_homology {Φ Ψ : Plus C ⥤ Plus D} [Φ.CommShift ℤ] [Ψ.CommShift ℤ]
    (hΦ : ∀ T : Triangle (Plus C), ι.mapTriangle.obj T ∈ admissibleTriangles C →
      ι.mapTriangle.obj (Φ.mapTriangle.obj T) ∈ admissibleTriangles D)
    (hΨ : ∀ T : Triangle (Plus C), ι.mapTriangle.obj T ∈ admissibleTriangles C →
      ι.mapTriangle.obj (Ψ.mapTriangle.obj T) ∈ admissibleTriangles D)
    (hΦ' : ∀ (m : ℤ) (K : Plus C), (∀ ν < m, IsZero ((homologyFunctor C ν).obj K)) →
      ∀ ν < m, IsZero ((homologyFunctor D ν).obj (Φ.obj K)))
    (hΨ' : ∀ (m : ℤ) (K : Plus C), (∀ ν < m, IsZero ((homologyFunctor C ν).obj K)) →
      ∀ ν < m, IsZero ((homologyFunctor D ν).obj (Ψ.obj K)))
    (α : Φ ⟶ Ψ) (𝒞 : ObjectProperty C)
    (hα : ∀ F : C, 𝒞 F → ∀ j : ℤ, IsIso (α.app (((singleFunctor C 0).obj F)⟦j⟧)))
    (K : Plus C) (hK : ∀ ν : ℤ, 𝒞 ((homologyFunctor C ν).obj K)) :
    IsIso (α.app K) := by
  have := isTriangulated_of_map_admissibleTriangles Φ hΦ
  have := isTriangulated_of_map_admissibleTriangles Ψ hΨ
  have hGEΦ : ∀ (L : Plus C) (m : ℤ), L.IsGE m → (Φ.obj L).IsGE m := fun L m hL =>
    (isGE_iff _ m).2 (hΦ' m L ((isGE_iff L m).1 hL))
  have hGEΨ : ∀ (L : Plus C) (m : ℤ), L.IsGE m → (Ψ.obj L).IsGE m := fun L m hL =>
    (isGE_iff _ m).2 (hΨ' m L ((isGE_iff L m).1 hL))
  obtain ⟨a, ha⟩ := K.property
  have hGE : K.IsGE a := (isGE_ι_obj_iff K a).1 ha
  have := hGE
  rw [isIso_iff]
  intro q
  by_cases haq : a ≤ q
  · have hT := TStructure.t.triangleLEGT_distinguished q K
    have hn : a + ((q - a).toNat : ℤ) = q := by
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hcut : NatTrans.isoLocusAtShifts α ((TStructure.t.truncLE q).obj K) := by
      refine prop_of_isGE_of_isLE (NatTrans.isoLocusAtShifts α) a (q - a).toNat _
        inferInstance ?_ fun p _ hp => ?_
      · rw [hn]
        infer_instance
      · have : IsIso ((homologyFunctor C p).map ((TStructure.t.truncLEι q).app K)) :=
          isIso_homologyMap_truncLEι_app K p q (by omega)
        exact (NatTrans.isoLocusAtShifts α).prop_of_iso
          ((singleFunctor C 0).mapIso
            (asIso ((homologyFunctor C p).map ((TStructure.t.truncLEι q).app K)))).symm
          (hα _ (hK p))
    have h₁ : IsIso ((homologyFunctor D q).map
        (Φ.map ((TStructure.t.truncLEι q).app K))) :=
      isIso_homologyMap_mor₁_of_isGE₃
        (Φ.mapTriangle.obj ((TStructure.t.triangleLEGT q).obj K))
        (Φ.map_distinguished _ hT) q (q + 1)
        (hGEΦ ((TStructure.t.truncGT q).obj K) (q + 1) inferInstance) (by omega)
    have h₂ : IsIso ((homologyFunctor D q).map
        (Ψ.map ((TStructure.t.truncLEι q).app K))) :=
      isIso_homologyMap_mor₁_of_isGE₃
        (Ψ.mapTriangle.obj ((TStructure.t.triangleLEGT q).obj K))
        (Ψ.map_distinguished _ hT) q (q + 1)
        (hGEΨ ((TStructure.t.truncGT q).obj K) (q + 1) inferInstance) (by omega)
    have : IsIso (α.app ((TStructure.t.truncLE q).obj K)) :=
      NatTrans.isIso_app_of_isoLocusAtShifts α hcut
    have hcomm : (homologyFunctor D q).map (Φ.map ((TStructure.t.truncLEι q).app K)) ≫
          (homologyFunctor D q).map (α.app K) =
        (homologyFunctor D q).map (α.app ((TStructure.t.truncLE q).obj K)) ≫
          (homologyFunctor D q).map (Ψ.map ((TStructure.t.truncLEι q).app K)) := by
      simpa only [Functor.map_comp, Functor.id_obj] using
        congrArg (homologyFunctor D q).map (α.naturality ((TStructure.t.truncLEι q).app K))
    have hfac : IsIso ((homologyFunctor D q).map (Φ.map ((TStructure.t.truncLEι q).app K)) ≫
        (homologyFunctor D q).map (α.app K)) := by
      rw [hcomm]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((homologyFunctor D q).map (Φ.map ((TStructure.t.truncLEι q).app K))) _
  · have h₁ := hΦ' a K ((isGE_iff K a).1 hGE) q (by omega)
    have h₂ := hΨ' a K ((isGE_iff K a).1 hGE) q (by omega)
    exact IsZero.isIso h₁ h₂ _

end DerivedCategory.Plus

end
