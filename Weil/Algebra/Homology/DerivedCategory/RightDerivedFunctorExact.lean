module

public import Weil.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Weil.Defs.Algebra.Homology.DerivedCategory.Basic
public import Weil.Defs.Algebra.Homology.HomotopyCategory.AdmissibleTriangleHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Weil.Attr

/-!
# The right derived functor of a choice of injective resolutions is exact

Let `F : C ⥤ D` be an additive functor between abelian categories, let `(I(X), i_X)` be a choice
of injective resolutions on the bounded below derived category `D⁺(C)`, let `ρ` be an
injective-resolution functor for it and `RF : D⁺(C) ⥤ D(D)` the associated derived functor.
For `X` in `D⁺(C)`, let `c^T_X : I(TX) ⟶ T(I(X))` be the morphism of the homotopy category with
`c^T_X ∘ i_{TX} = T(i_X)`, and let `θ_X : RF(TX) ⟶ T(RF(X))` be its image under `F` in `D(D)`.
We show that `RF` carries an admissible triangle `(X, Y, Z; u, v, w)` of `D(C)` with vertices in
`D⁺(C)` to the admissible triangle `(RF X, RF Y, RF Z; RF u, RF v, θ_X ∘ RF w)` of `D(D)`.

The proof: choose a morphism of complexes `g : I(X) ⟶ I(Y)` representing `ρ(u)`. The morphisms
`i_X`, `i_Y` extend to an isomorphism `γ : Z ≅ C(g)` from the given triangle to the image of the
cone triangle of `g` in `D(C)`. As the mapping cone `C(g)` is a bounded below complex of
injectives, `γ ∘ i_Z⁻¹` comes from an isomorphism `c₃ : I(Z) ≅ C(g)` of the homotopy category,
and `(id, id, F(c₃))` is an isomorphism from the triangle of the statement onto the image under
`F` of the cone triangle of `g`, which is admissible.

## Main definitions

* `DerivedCategory.PlusComplexes.shiftObj`: the shift `X[n]` of an object of `D⁺(C)`, presented
  by complexes.

## Main results

* `CochainComplex.isKInjective_mappingCone_of_injective`: the mapping cone of a morphism between
  bounded below complexes of injectives is K-injective.
* `CochainComplex.InjectiveResolutionFunctor.existsUnique_comp_eq_shift_map`: the morphism
  `c^T_X : I(X[1]) ⟶ I(X)[1]` with `c^T_X ∘ i_{X[1]} = i_X[1]` exists and is unique.
* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctor_triangle_mem_admissibleTriangles`:
  `RF` carries admissible triangles with vertices in `D⁺(C)` to admissible triangles.

## Implementation notes

The source of `RF` is the presentation `DerivedCategory.PlusComplexes C` of `D⁺(C)` by
complexes, which is not itself given a triangulated structure. An admissible triangle of `D(C)`
with vertices in `D⁺(C)` is therefore given by objects `X, Y, Z` and morphisms `u : X ⟶ Y`,
`v : Y ⟶ Z`, `w : Z ⟶ X[1]` of `PlusComplexes C`, the triangle of `D(C)` having third morphism
`w` followed by the canonical identification `Q(X[1]) ≅ Q(X)[1]`. The identifications
`F(T(I(X))) = T(F(I(X)))` and `Q(T K) = T(Q K)` are the commutation-with-shift isomorphisms of
`F` on homotopy categories and of the localization functor. The morphism `c^T_X` enters as an
argument together with its defining property; it exists and is unique by the uniqueness of
injective resolutions up to homotopy. The proof does not construct FK's explicit quasi-isomorphism
`C(u') ⟶ C(g)`: the comparison isomorphism is obtained from the axiom (TR3) of the triangulated
category `D(C)`, and the fact that morphisms of `D(C)` into K-injective complexes are morphisms
of the homotopy category.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4, p. 298.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- The mapping cone of a morphism between bounded below complexes of injective objects is
K-injective. -/
lemma isKInjective_mappingCone_of_injective {K L : CochainComplex C ℤ} (f : K ⟶ L) (a b : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyGE b] [∀ n, Injective (K.X n)] [∀ n, Injective (L.X n)] :
    (mappingCone f).IsKInjective := by
  have : ∀ n, Injective ((mappingCone f).X n) := fun n ↦
    Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl).symm
      inferInstance
  have : (mappingCone f).IsStrictlyGE (min (a - 1) b) :=
    isStrictlyGE_mappingCone f a b _
  exact isKInjective_of_injective _ (min (a - 1) b)

end CochainComplex

namespace DerivedCategory.PlusComplexes

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The shift `X[n]` of an object `X` of the bounded below derived category presented by
complexes: the shifted complex, which is again cohomologically bounded below. -/
abbrev shiftObj (X : PlusComplexes C) (n : ℤ) : PlusComplexes C :=
  (⟨(X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1⟦n⟧, by
    obtain ⟨a, ha⟩ := (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).2
    exact ⟨a - n, CochainComplex.isGE_shift _ a n (a - n) (by lia)⟩⟩ :
    {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n})

@[simp]
lemma shiftObj_val (X : PlusComplexes C) (n : ℤ) :
    ((X.shiftObj n : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 =
      (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1⟦n⟧ :=
  rfl

end DerivedCategory.PlusComplexes

namespace CochainComplex

namespace InjectiveResolutionFunctor

open DerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

/-- For `X` in `D⁺(C)` there is exactly one morphism `c^T_X : I(X[1]) ⟶ I(X)[1]` of the homotopy
category with `c^T_X ∘ i_{X[1]} = i_X[1]`. -/
lemma existsUnique_comp_eq_shift_map (X : PlusComplexes C) :
    ∃! cT : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c ((X.shiftObj 1 : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          (X.shiftObj 1 : PlusComplexes C).2).cocomplex ⟶
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex)⟦(1 : ℤ)⟧,
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c ((X.shiftObj 1 : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          (X.shiftObj 1 : PlusComplexes C).2).ι ≫ cT =
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
          (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 ≫
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι)⟦(1 : ℤ)⟧' := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let RX := c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2
  let RT := c ((X.shiftObj 1 : PlusComplexes C) :
    {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 (X.shiftObj 1 : PlusComplexes C).2
  let e : q.obj (RX.cocomplex⟦(1 : ℤ)⟧) ≅ (q.obj RX.cocomplex)⟦(1 : ℤ)⟧ :=
    (q.commShiftIso (1 : ℤ)).app RX.cocomplex
  let φ : q.obj ((X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1⟦(1 : ℤ)⟧) ⟶
      (q.obj RX.cocomplex)⟦(1 : ℤ)⟧ :=
    (q.commShiftIso (1 : ℤ)).hom.app (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 ≫
      (q.map RX.ι)⟦(1 : ℤ)⟧'
  have hT := isIso_Qh_map_quotient_map_ι (c := c) (X.shiftObj 1)
  have hinj : ∀ {K : HomotopyCategory C (ComplexShape.up ℤ)}
      (f₁ f₂ : K ⟶ (q.obj RX.cocomplex)⟦(1 : ℤ)⟧),
      Qh.map (f₁ ≫ e.inv) = Qh.map (f₂ ≫ e.inv) → f₁ = f₂ := fun f₁ f₂ h ↦ by
    rw [← cancel_mono e.inv]
    exact (IsKInjective.Qh_map_bijective _ (RX.cocomplex⟦(1 : ℤ)⟧)).1 h
  obtain ⟨f, hf⟩ := (IsKInjective.Qh_map_bijective (q.obj RT.cocomplex)
    (RX.cocomplex⟦(1 : ℤ)⟧)).2 (inv (Qh.map (q.map RT.ι)) ≫ Qh.map (φ ≫ e.inv))
  refine ⟨f ≫ e.hom, ?_, fun cT hcT ↦ ?_⟩
  · refine hinj _ φ ?_
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [Functor.map_comp, hf, IsIso.hom_inv_id_assoc]
  · refine hinj _ _ ?_
    rw [← cancel_epi (Qh.map (q.map RT.ι)), ← Functor.map_comp, ← Category.assoc, hcT]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hf, IsIso.hom_inv_id_assoc]
    simp only [φ, Category.assoc]
    rfl

/-- Let `(X, Y, Z; u, v, w)` be an admissible triangle of `D(C)` with vertices in `D⁺(C)`
(the third morphism being `w : Z ⟶ X[1]` followed by `Q(X[1]) ≅ Q(X)[1]`), and let
`c^T_X : I(X[1]) ⟶ I(X)[1]` be a morphism of the homotopy category with
`c^T_X ∘ i_{X[1]} = i_X[1]`. Then `(RF X, RF Y, RF Z; RF u, RF v, θ_X ∘ RF w)` is an admissible
triangle of `D(D)`, where `θ_X : RF(X[1]) ⟶ RF(X)[1]` is the image of `F(c^T_X)` in `D(D)`. -/
@[weil "lem_fka2_right_derived_functor_exact"]
theorem rightDerivedFunctor_triangle_mem_admissibleTriangles
    {X Y Z : PlusComplexes C} (u : X ⟶ Y) (v : Y ⟶ Z) (w : Z ⟶ X.shiftObj 1)
    (hT : Triangle.mk u.hom v.hom (w.hom ≫
        Qh.map (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
          (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1) ≫
        (Qh.commShiftIso (1 : ℤ)).hom.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1)) ∈ admissibleTriangles C)
    (cT : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c ((X.shiftObj 1 : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          (X.shiftObj 1 : PlusComplexes C).2).cocomplex ⟶
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex)⟦(1 : ℤ)⟧)
    (hcT : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c ((X.shiftObj 1 : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          (X.shiftObj 1 : PlusComplexes C).2).ι ≫ cT =
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).hom.app
          (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 ≫
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι)⟦(1 : ℤ)⟧') :
    Triangle.mk ((ρ.rightDerivedFunctor F).map u) ((ρ.rightDerivedFunctor F).map v)
      ((ρ.rightDerivedFunctor F).map w ≫
        Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map cT) ≫
        ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh).commShiftIso (1 : ℤ)).hom.app
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
            (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex)) ∈
      admissibleTriangles D := by
  -- notation
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let Fm := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let F' := Fm ⋙ Qh
  let RX := c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2
  let RY := c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2
  let RZ := c (Z : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Z.2
  -- a representative of `ρ(u)`
  obtain ⟨g, hg⟩ := q.map_surjective (ρ.map u)
  obtain ⟨a, _⟩ := RX.exists_isStrictlyGE
  obtain ⟨b, _⟩ := RY.exists_isStrictlyGE
  have : (mappingCone g).IsKInjective := isKInjective_mappingCone_of_injective g a b
  -- the comparison in `D(C)`
  have hΔ := (DerivedCategory.mem_admissibleTriangles_iff _).1 hT
  have hS := (DerivedCategory.mem_admissibleTriangles_iff _).1
    (Qh_mapTriangle_mem_admissibleTriangles
      (HomotopyCategory.standardTriangleh_mem_admissibleTriangles g))
  have hX := isIso_Qh_map_quotient_map_ι (c := c) X
  have hY := isIso_Qh_map_quotient_map_ι (c := c) Y
  have hZ := isIso_Qh_map_quotient_map_ι (c := c) Z
  have comm₁ : u.hom ≫ Qh.map (q.map RY.ι) = Qh.map (q.map RX.ι) ≫ Qh.map (q.map g) := by
    rw [hg]; exact (ρ.comm u).symm
  obtain ⟨γ, hγ₂, hγ₃⟩ : ∃ γ :
      Qh.obj (q.obj (Z : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1) ⟶
        Qh.obj (q.obj (mappingCone g)),
      v.hom ≫ γ = Qh.map (q.map RY.ι) ≫ Qh.map (q.map (mappingCone.inr g)) ∧
      (-(w.hom ≫ Qh.map ((q.commShiftIso (1 : ℤ)).hom.app
          (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1) ≫
          (Qh.commShiftIso (1 : ℤ)).hom.app
            (q.obj (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1))) ≫
        (Qh.map (q.map RX.ι))⟦(1 : ℤ)⟧' =
      γ ≫ (-((Qh.map (q.map (mappingCone.projection g) ≫
          (q.commShiftIso (1 : ℤ)).hom.app RX.cocomplex)) ≫
          (Qh.commShiftIso (1 : ℤ)).hom.app (q.obj RX.cocomplex))) :=
    Pretriangulated.complete_distinguished_triangle_morphism _ _ hΔ hS
      (Qh.map (q.map RX.ι)) (Qh.map (q.map RY.ι)) comm₁
  have hγ : IsIso γ := by
    refine isIso₃_of_isIso₁₂ (Triangle.homMk _ _ _ _ γ comm₁ hγ₂ ?_) hΔ hS hX hY
    exact hγ₃
  -- the comparison `c₃ : I(Z) ⟶ C(g)` in `K(C)`
  obtain ⟨c₃, hc₃⟩ := (IsKInjective.Qh_map_bijective (q.obj RZ.cocomplex) (mappingCone g)).2
    (inv (Qh.map (q.map RZ.ι)) ≫ γ)
  have hc₃' : IsIso (Qh.map c₃) := by rw [hc₃]; exact IsIso.comp_isIso' inferInstance hγ
  obtain ⟨d, hd⟩ := (IsKInjective.Qh_map_bijective (q.obj (mappingCone g)) RZ.cocomplex).2
    (inv (Qh.map c₃))
  have hc₃iso : IsIso c₃ := ⟨d, (IsKInjective.Qh_map_bijective _ RZ.cocomplex).1 (by simp [hd]),
    (IsKInjective.Qh_map_bijective _ (mappingCone g)).1 (by simp [hd])⟩
  have hc₃'' : Qh.map (q.map RZ.ι) ≫ Qh.map c₃ = γ := by rw [hc₃, IsIso.hom_inv_id_assoc]
  -- the second square in `K(C)`
  have sq₂ : ρ.map v ≫ c₃ = q.map (mappingCone.inr g) := by
    apply (IsKInjective.Qh_map_bijective _ (mappingCone g)).1
    rw [← cancel_epi (Qh.map (q.map RY.ι))]
    simp only [Functor.map_comp]
    rw [ρ.comm_assoc v, hc₃'']
    exact hγ₂
  -- the third square in `K(C)`
  have sq₃ : ρ.map w ≫ cT = c₃ ≫ q.map (mappingCone.projection g) ≫
      (q.commShiftIso (1 : ℤ)).hom.app RX.cocomplex := by
    rw [← cancel_mono ((q.commShiftIso (1 : ℤ)).inv.app RX.cocomplex)]
    apply (IsKInjective.Qh_map_bijective _ (RX.cocomplex⟦(1 : ℤ)⟧)).1
    rw [← cancel_epi (Qh.map (q.map RZ.ι)), ← cancel_mono (Qh.map
      ((q.commShiftIso (1 : ℤ)).hom.app RX.cocomplex) ≫
        (Qh.commShiftIso (1 : ℤ)).hom.app (q.obj RX.cocomplex))]
    simp only [Functor.map_comp, Category.assoc]
    have e : Qh.map ((q.commShiftIso (1 : ℤ)).inv.app RX.cocomplex) ≫
        Qh.map ((q.commShiftIso (1 : ℤ)).hom.app RX.cocomplex) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app]; exact Qh.map_id _
    have key₁ : Qh.map (q.map RZ.ι) ≫ Qh.map (ρ.map w) ≫ Qh.map cT =
        w.hom ≫ Qh.map ((q.commShiftIso (1 : ℤ)).hom.app
          (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 ≫ (q.map RX.ι)⟦(1 : ℤ)⟧') := by
      rw [ρ.comm_assoc w]
      exact congrArg (w.hom ≫ ·) ((Qh.map_comp _ _).symm.trans (congrArg Qh.map hcT))
    have key₂ : Qh.map ((q.commShiftIso (1 : ℤ)).hom.app
          (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 ≫ (q.map RX.ι)⟦(1 : ℤ)⟧') ≫
        (Qh.commShiftIso (1 : ℤ)).hom.app (q.obj RX.cocomplex) =
        Qh.map ((q.commShiftIso (1 : ℤ)).hom.app
          (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1) ≫
          (Qh.commShiftIso (1 : ℤ)).hom.app
            (q.obj (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1) ≫
          (Qh.map (q.map RX.ι))⟦(1 : ℤ)⟧' := by
      rw [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality]
    rw [reassoc_of% e]
    refine Eq.trans ((reassoc_of% key₁) _) (Eq.trans (congrArg (w.hom ≫ ·) key₂) ?_)
    refine Eq.trans ?_ ((reassoc_of% hc₃'') _).symm
    have h3 := hγ₃
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj, Category.assoc] at h3
    rw [← Functor.map_comp_assoc]
    exact h3
  -- the isomorphism of triangles in `D(D)`
  rw [DerivedCategory.mem_admissibleTriangles_iff]
  refine isomorphic_distinguished _ (F'.map_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished g)) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (F'.mapIso (@asIso _ _ _ _ c₃ hc₃iso))
    ?_ ?_ ?_
  · change Qh.map (Fm.map (ρ.map u)) ≫ 𝟙 (Qh.obj (Fm.obj (q.obj RY.cocomplex))) =
      𝟙 (Qh.obj (Fm.obj (q.obj RX.cocomplex))) ≫ Qh.map (Fm.map (q.map g))
    rw [Category.comp_id, Category.id_comp, hg]
  · change Qh.map (Fm.map (ρ.map v)) ≫ Qh.map (Fm.map c₃) =
      𝟙 (Qh.obj (Fm.obj (q.obj RY.cocomplex))) ≫ Qh.map (Fm.map (q.map (mappingCone.inr g)))
    rw [Category.id_comp, ← Qh.map_comp, ← Fm.map_comp, sq₂]
  · change (-(Qh.map (Fm.map (ρ.map w)) ≫ Qh.map (Fm.map cT) ≫
        (F'.commShiftIso (1 : ℤ)).hom.app (q.obj RX.cocomplex))) ≫
        (𝟙 (Qh.obj (Fm.obj (q.obj RX.cocomplex))))⟦(1 : ℤ)⟧' =
      Qh.map (Fm.map c₃) ≫ Qh.map (Fm.map (mappingCone.triangleh g).mor₃) ≫
        (F'.commShiftIso (1 : ℤ)).hom.app (q.obj RX.cocomplex)
    have h' : Qh.map (Fm.map c₃) ≫ Qh.map (Fm.map (mappingCone.triangleh g).mor₃) =
        -(Qh.map (Fm.map (ρ.map w ≫ cT))) := by
      have e₃ : c₃ ≫ (mappingCone.triangleh g).mor₃ = -(ρ.map w ≫ cT) :=
        (congrArg (c₃ ≫ ·) (mappingCone.triangleh_mor₃_eq_neg g)).trans
          ((Preadditive.comp_neg _ _).trans (congrArg (fun x ↦ -x) sq₃.symm))
      refine (Qh.map_comp _ _).symm.trans ((congrArg Qh.map (Fm.map_comp _ _).symm).trans ?_)
      rw [e₃]
      exact (congrArg Qh.map Fm.map_neg).trans Qh.map_neg
    refine Eq.trans ?_ ((reassoc_of% h') _).symm
    simp only [Functor.map_comp, Preadditive.neg_comp, Category.assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact (congrArg Neg.neg (Category.assoc _ _ _)).symm.trans (Preadditive.neg_comp _ _).symm

end InjectiveResolutionFunctor

end CochainComplex
