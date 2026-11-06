module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilFrontier.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import WeilFrontier.Algebra.Homology.DerivedCategory.TStructure
public import WeilFrontier.Defs.Algebra.Homology.Embedding.CochainComplex
public import Weil.Attr

/-!
# The long exact sequence of derived functors attached to a truncation

Let `C` be an abelian category with enough injectives, `F : C ⥤ D` an additive functor and
`R^νF = H^ν ∘ RF : D⁺(C) ⥤ D` its classical derived functors. Let `K` be a cochain complex
with `Hⁱ(K) = 0` for `i < m`, and put `H = Hᵐ(K)`. Then `K` and the complex
`K̃̃ = Kᵐ / Ker dᵐ → K^{m+1} → ⋯` (`CochainComplex.truncLECokernel`) lie in `D⁺(C)`, and there
is an exact sequence
`⋯ → R^{ν-m}F(H[0]) → R^νF(K) → R^νF(K̃̃) → R^{ν+1-m}F(H[0]) → R^{ν+1}F(K) → ⋯`.

## Main results

* `DerivedCategory.plus_Q_obj_truncLECokernel`: `K̃̃` lies in `D⁺(C)`.
* `CategoryTheory.Functor.exists_rightDerivedFunctorPlusHomology_truncLECokernel_exact`: the
  long exact sequence above.

## Implementation notes

Freitag and Kiehl obtain the sequence from the short exact sequence of complexes
`0 → H[-m] → τ_{≥ m} K → K̃̃ → 0`. We use instead the short exact sequence
`0 → τ_{≤ m} K → K → K̃̃ → 0` (`CochainComplex.shortComplexTruncLE`), whose distinguished
triangle in `D(C)` lies in `D⁺(C)`: as `Hⁱ(K) = 0` for `i < m`, the complex `τ_{≤ m} K` has
cohomology concentrated in degree `m`, so it is isomorphic in `D(C)` to `H[-m]`. The terms
`R^νF(H[-m])` are identified with `R^{ν-m}F(H[0])` through the commutation of `RF` with the
shift and the shift sequence of the cohomology functors. The derived functors are the
choice-free ones `F.rightDerivedFunctorPlusHomology`; for a choice of injective resolutions
they are isomorphic to the concrete ones
(`CochainComplex.InjectiveResolutionFunctor.classicalRightDerivedIso`). Left exactness of `F`
is not needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The complex `Kᵐ / Ker dᵐ → K^{m+1} → ⋯` lies in `D⁺(C)`. -/
@[weil "lem_fka2_derived_functor_truncation_les"]
theorem plus_Q_obj_truncLECokernel (K : CochainComplex C ℤ) (m : ℤ) :
    TStructure.t.plus (Q.obj (K.truncLECokernel m)) := by
  have : (K.truncLECokernel m).IsStrictlyGE m := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ K.isZero_truncLECokernel_X m i hi
  exact ⟨m, inferInstance⟩

/-- If `Hⁱ(K) = 0` for `i < m`, the truncation `τ_{≤ m} K` is `≥ m` in `D(C)`. -/
lemma isGE_Q_obj_truncLE (K : CochainComplex C ℤ) (m : ℤ)
    (hK : ∀ i < m, IsZero (K.homology i)) : (Q.obj (K.truncLE m)).IsGE m := by
  rw [isGE_Q_obj_iff, CochainComplex.isGE_iff]
  intro i hi
  have : QuasiIsoAt (K.ιTruncLE m) i := K.quasiIsoAt_ιTruncLE m i (by omega)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hK i hi).of_iso (asIso (HomologicalComplex.homologyMap (K.ιTruncLE m) i))

/-- If `Hⁱ(K) = 0` for `i < m`, the truncation `τ_{≤ m} K` is isomorphic in `D(C)` to
`Hᵐ(K)` placed in degree `m`. -/
lemma nonempty_Q_obj_truncLE_iso_singleFunctor (K : CochainComplex C ℤ) (m : ℤ)
    (hK : ∀ i < m, IsZero (K.homology i)) :
    Nonempty (Q.obj (K.truncLE m) ≅ (singleFunctor C m).obj (K.homology m)) := by
  have := isGE_Q_obj_truncLE K m hK
  have hiso : IsIso (HomologicalComplex.homologyMap (K.ιTruncLE m) m) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 (K.quasiIsoAt_ιTruncLE m m le_rfl)
  obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj (K.truncLE m)) m
  let eY : Y ≅ K.homology m :=
    ((singleFunctorCompHomologyFunctorIso C m).app Y).symm ≪≫
      (homologyFunctor C m).mapIso e.symm ≪≫ (homologyFunctorFactors C m).app _ ≪≫
      @asIso _ _ _ _ (HomologicalComplex.homologyMap (K.ιTruncLE m) m) hiso
  exact ⟨e ≪≫ (singleFunctor C m).mapIso eY⟩

end DerivedCategory

namespace CategoryTheory.Functor

open DerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- `R^νF(Y⟦k⟧) ≅ R^{ν'}F(Y)` for `k + ν = ν'`. -/
noncomputable def rightDerivedFunctorPlusHomologyShiftIso (Y : DerivedCategory.Plus C)
    (k ν ν' : ℤ) (h : k + ν = ν') :
    (F.rightDerivedFunctorPlusHomology ν).obj (Y⟦k⟧) ≅
      (F.rightDerivedFunctorPlusHomology ν').obj Y :=
  (Plus.homologyFunctor D ν).mapIso ((F.rightDerivedFunctorPlus.commShiftIso k).app Y) ≪≫
    ((Plus.homologyFunctor D 0).shiftIso k ν ν' h).app (F.rightDerivedFunctorPlus.obj Y)

/-- **The long exact sequence of a truncation.** Let `K` be a cochain complex with
`Hⁱ(K) = 0` for `i < m` and `H = Hᵐ(K)`. Then there are morphisms making the sequence
`⋯ → R^{ν-m}F(H[0]) → R^νF(K) → R^νF(K̃̃) → R^{ν+1-m}F(H[0]) → R^{ν+1}F(K) → ⋯` exact, where
`K̃̃ = K.truncLECokernel m` is the complex `Kᵐ / Ker dᵐ → K^{m+1} → ⋯`. -/
@[weil "lem_fka2_derived_functor_truncation_les"]
theorem exists_rightDerivedFunctorPlusHomology_truncLECokernel_exact
    (K : CochainComplex C ℤ) (m : ℤ) (hK : ∀ i < m, IsZero (K.homology i)) :
    ∃ (a : ∀ ν : ℤ, (F.rightDerivedFunctorPlusHomology (ν - m)).obj
          ((Plus.singleFunctor C 0).obj (K.homology m)) ⟶
        (F.rightDerivedFunctorPlusHomology ν).obj ⟨Q.obj K, plus_Q_obj_of_isZero_homology K m hK⟩)
      (b : ∀ ν : ℤ, (F.rightDerivedFunctorPlusHomology ν).obj
          ⟨Q.obj K, plus_Q_obj_of_isZero_homology K m hK⟩ ⟶
        (F.rightDerivedFunctorPlusHomology ν).obj
          ⟨Q.obj (K.truncLECokernel m), plus_Q_obj_truncLECokernel K m⟩)
      (δ : ∀ ν : ℤ, (F.rightDerivedFunctorPlusHomology ν).obj
          ⟨Q.obj (K.truncLECokernel m), plus_Q_obj_truncLECokernel K m⟩ ⟶
        (F.rightDerivedFunctorPlusHomology (ν + 1 - m)).obj
          ((Plus.singleFunctor C 0).obj (K.homology m)))
      (hab : ∀ ν, a ν ≫ b ν = 0) (hbδ : ∀ ν, b ν ≫ δ ν = 0)
      (hδa : ∀ ν, δ ν ≫ a (ν + 1) = 0),
      ∀ ν, (ShortComplex.mk _ _ (hab ν)).Exact ∧ (ShortComplex.mk _ _ (hbδ ν)).Exact ∧
        (ShortComplex.mk _ _ (hδa ν)).Exact := by
  let S := K.shortComplexTruncLE m
  have hS : S.ShortExact := K.shortComplexTruncLE_shortExact m
  let τ : DerivedCategory.Plus C := ⟨Q.obj (K.truncLE m), ⟨m, isGE_Q_obj_truncLE K m hK⟩⟩
  let X : DerivedCategory.Plus C := ⟨Q.obj K, plus_Q_obj_of_isZero_homology K m hK⟩
  let Y : DerivedCategory.Plus C := ⟨Q.obj (K.truncLECokernel m), plus_Q_obj_truncLECokernel K m⟩
  let f : τ ⟶ X := Plus.ι.preimage (Q.map S.f)
  let g : X ⟶ Y := Plus.ι.preimage (Q.map S.g)
  let w : Y ⟶ τ⟦(1 : ℤ)⟧ := Plus.preimageShift (X := Y) (Y := τ) (triangleOfSESδ hS)
  have hdist : Triangle.mk f g w ∈ distTriang (DerivedCategory.Plus C) := by
    change Plus.ι.mapTriangle.obj _ ∈ distTriang (DerivedCategory C)
    refine isomorphic_distinguished _ (triangleOfSES_distinguished hS) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · exact (Category.comp_id _).trans ((Plus.ι.map_preimage (X := τ) (Y := X) (Q.map S.f)).trans
        (Category.id_comp _).symm)
    · exact (Category.comp_id _).trans ((Plus.ι.map_preimage (X := X) (Y := Y) (Q.map S.g)).trans
        (Category.id_comp _).symm)
    · refine (congrArg _ ((shiftFunctor (DerivedCategory C) (1 : ℤ)).map_id _)).trans ?_
      exact (Category.comp_id _).trans ((Plus.ι_map_preimageShift (X := Y) (Y := τ)
        (triangleOfSESδ hS)).trans (Category.id_comp _).symm)
  have hT : Triangle.mk f g (-(-w)) ∈ distTriang (DerivedCategory.Plus C) := by
    rwa [neg_neg]
  obtain ⟨e₀⟩ := nonempty_Q_obj_truncLE_iso_singleFunctor K m hK
  let H₀ := (Plus.singleFunctor C 0).obj (K.homology m)
  let eτ : τ ≅ H₀⟦-m⟧ :=
    Plus.ι.preimageIso (e₀ ≪≫ ((Plus.singleFunctorιIso C m).app (K.homology m)).symm) ≪≫
      (((Plus.singleFunctors C).shiftIso (-m) m 0 (by omega)).app (K.homology m)).symm
  let e : ∀ ν : ℤ, (F.rightDerivedFunctorPlusHomology (ν - m)).obj H₀ ≅
      (F.rightDerivedFunctorPlusHomology ν).obj τ := fun ν ↦
    (F.rightDerivedFunctorPlusHomologyShiftIso H₀ (-m) ν (ν - m) (by omega)).symm ≪≫
      (F.rightDerivedFunctorPlusHomology ν).mapIso eτ.symm
  let δ' : ∀ ν : ℤ, (F.rightDerivedFunctorPlusHomology ν).obj Y ⟶
      (F.rightDerivedFunctorPlusHomology (ν + 1)).obj τ := fun ν ↦
    F.rightDerivedFunctorPlusHomologyδ (-w) ν (ν + 1) rfl
  have h₁ : ∀ ν, (F.rightDerivedFunctorPlusHomology ν).map f ≫
      (F.rightDerivedFunctorPlusHomology ν).map g = 0 := fun ν ↦
    F.rightDerivedFunctorPlusHomology_map_mor₁_comp_map_mor₂ (T := Triangle.mk f g (-w)) hT ν
  have h₂ : ∀ ν, (F.rightDerivedFunctorPlusHomology ν).map g ≫ δ' ν = 0 :=
    fun ν ↦ F.rightDerivedFunctorPlusHomology_map_mor₂_comp_δ (T := Triangle.mk f g (-w)) hT
      ν (ν + 1) rfl
  have h₃ : ∀ ν, δ' ν ≫ (F.rightDerivedFunctorPlusHomology (ν + 1)).map f = 0 :=
    fun ν ↦ F.rightDerivedFunctorPlusHomology_δ_comp_map_mor₁ (T := Triangle.mk f g (-w)) hT
      ν (ν + 1) rfl
  refine ⟨fun ν ↦ (e ν).hom ≫ (F.rightDerivedFunctorPlusHomology ν).map f,
    fun ν ↦ (F.rightDerivedFunctorPlusHomology ν).map g, fun ν ↦ δ' ν ≫ (e (ν + 1)).inv,
    fun ν ↦ by simpa using congrArg ((e ν).hom ≫ ·) (h₁ ν),
    fun ν ↦ by simpa [δ'] using congrArg (· ≫ (e (ν + 1)).inv) (h₂ ν),
    fun ν ↦ by simpa [δ'] using h₃ ν, fun ν ↦ ⟨?_, ?_, ?_⟩⟩
  · refine (ShortComplex.exact_iff_of_iso ?_).1
      (F.rightDerivedFunctorPlusHomology_exact₂_of_admissible (T := Triangle.mk f g (-w)) hT ν)
    exact ShortComplex.isoMk (e ν).symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  · refine (ShortComplex.exact_iff_of_iso ?_).1
      (F.rightDerivedFunctorPlusHomology_exact₃_of_admissible (T := Triangle.mk f g (-w)) hT
        ν (ν + 1) rfl)
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (e (ν + 1)).symm (by simp)
      (by simp [δ'])
  · refine (ShortComplex.exact_iff_of_iso ?_).1
      (F.rightDerivedFunctorPlusHomology_exact₁_of_admissible (T := Triangle.mk f g (-w)) hT
        ν (ν + 1) rfl)
    exact ShortComplex.isoMk (Iso.refl _) (e (ν + 1)).symm (Iso.refl _) (by simp [δ'])
      (by simp)

end CategoryTheory.Functor
