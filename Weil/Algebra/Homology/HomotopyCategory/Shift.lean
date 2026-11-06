module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Weil.Attr

/-!
# The componentwise extension of an additive functor commutes with shifts

Let `F : C ⥤ D` be an additive functor between preadditive categories and let
`F.mapHomologicalComplex (ComplexShape.up ℤ)` be its componentwise extension to cochain
complexes. For every cochain complex `X` and every `n : ℤ`, the complexes `F(X⟦n⟧)` and
`(F X)⟦n⟧` are equal: both have `F(X^{p+n})` in degree `p`, and their differentials
`F((-1)^n • d) = (-1)^n • F(d)` agree because `F` is additive. Likewise `F(f⟦n⟧)` and
`(F f)⟦n⟧` agree in every degree, so they are equal up to the identification of the source
and target complexes.

## Main results

* `CategoryTheory.Functor.mapHomologicalComplex_obj_shift`: `F(X⟦n⟧) = (F X)⟦n⟧`.
* `CategoryTheory.Functor.mapHomologicalComplex_map_shift`: `F(f⟦n⟧) = (F f)⟦n⟧` up to the
  `eqToHom` identifications of the previous lemma.
* `CategoryTheory.Functor.mapHomologicalComplex_map_shift_f`: the degreewise form,
  `F(f⟦n⟧)^p = ((F f)⟦n⟧)^p`.
* `CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_eq_eqToHom`:
  Mathlib's commutation isomorphism `(F.mapHomologicalComplex _).commShiftIso n` is the
  identification `eqToHom` given by `mapHomologicalComplex_obj_shift`.

## Implementation notes

The source states the result for the shift `T = T^1`; it is proved here for every shift
`T^n`, `n : ℤ`. Mathlib packages the same fact as the `CommShift` structure on
`F.mapHomologicalComplex (ComplexShape.up ℤ)` (the instance
`CategoryTheory.Functor.commShiftMapCochainComplex`), whose isomorphism is the identity in
every degree; the last lemma identifies the two.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive]

/-- The componentwise extension of an additive functor commutes with the shift on the nose:
`F(X⟦n⟧) = (F X)⟦n⟧`. -/
@[weil "lem_fka2_componentwise_extension_commutes_with_shift"]
theorem mapHomologicalComplex_obj_shift (X : CochainComplex C ℤ) (n : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (X⟦n⟧) =
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)⟦n⟧ := by
  refine HomologicalComplex.ext rfl ?_
  intro i j _
  simp [CochainComplex.shiftFunctor_obj_d']

/-- Degreewise, `F(f⟦n⟧)` and `(F f)⟦n⟧` are the same morphism `F(X^{p+n}) ⟶ F(Y^{p+n})`. -/
@[simp]
theorem mapHomologicalComplex_map_shift_f {X Y : CochainComplex C ℤ} (f : X ⟶ Y) (n p : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (f⟦n⟧')).f p =
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)⟦n⟧').f p :=
  rfl

/-- The componentwise extension of an additive functor commutes with the shift on morphisms:
`F(f⟦n⟧) = (F f)⟦n⟧`, up to the identifications of `mapHomologicalComplex_obj_shift`. -/
@[weil "lem_fka2_componentwise_extension_commutes_with_shift"]
theorem mapHomologicalComplex_map_shift {X Y : CochainComplex C ℤ} (f : X ⟶ Y) (n : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (f⟦n⟧') =
      eqToHom (F.mapHomologicalComplex_obj_shift X n) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)⟦n⟧' ≫
          eqToHom (F.mapHomologicalComplex_obj_shift Y n).symm := by
  ext p
  simp [HomologicalComplex.eqToHom_f]

/-- Mathlib's commutation isomorphism of `F.mapHomologicalComplex (ComplexShape.up ℤ)` with
the shift by `n` is the on-the-nose identification of `mapHomologicalComplex_obj_shift`. -/
theorem mapHomologicalComplex_commShiftIso_hom_app_eq_eqToHom (X : CochainComplex C ℤ)
    (n : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app X =
      eqToHom (F.mapHomologicalComplex_obj_shift X n) := by
  ext p
  simp [HomologicalComplex.eqToHom_f]

end CategoryTheory.Functor

/-! ### The shift functor is well defined -/

/-!
# The shift functors on `C(A)` and `K(A)` are additive and strictly compatible with addition

For a preadditive category `C` and `n : ℤ`, the shift functor `T^n = shiftFunctor _ n` on the
category `CochainComplex C ℤ` of cochain complexes sends `K` to the complex `K⟦n⟧` with
`K⟦n⟧.X p = K.X (p + n)` and differential `n.negOnePow • K.d`, and a morphism `f` to the
morphism with components `f.f (p + n)`. It is an additive functor, and it descends to an
additive functor on the homotopy category `HomotopyCategory C (ComplexShape.up ℤ)`, with
`T^n [f] = [T^n f]`.

Beyond the canonical isomorphisms `shiftFunctorAdd'` and `shiftFunctorZero` of the shift
structure, the composition laws hold as *equalities* of functors, on cochain complexes and on
the homotopy category: `T^j ⋙ T^i = T^(i+j)` and `T^0 = 𝟭`. Consequently
`T^(n+1) = T^n ⋙ T^1` for `n : ℕ` (so `T^n` is the `n`-fold iterate of `T = T^1`), and
`T^(-1)` is a two-sided inverse of `T^1`.

## Main results

* `CochainComplex.shiftFunctor_additive`, `HomotopyCategory.shiftFunctor_additive`:
  the shift functors are additive.
* `HomotopyCategory.quotient_comp_shiftFunctor`, `HomotopyCategory.quotient_map_shiftFunctor_map`:
  the shift on the homotopy category is induced by the shift on complexes.
* `CochainComplex.shiftFunctor_comp_shiftFunctor`, `CochainComplex.shiftFunctor_zero_eq_id`,
  `HomotopyCategory.shiftFunctor_comp_shiftFunctor`, `HomotopyCategory.shiftFunctor_zero_eq_id`:
  the equalities of functors `T^j ⋙ T^i = T^(i+j)` and `T^0 = 𝟭`.
* `CochainComplex.shiftFunctor_natCast_succ`, `CochainComplex.shiftFunctor_one_comp_neg_one`,
  `CochainComplex.shiftFunctor_neg_one_comp_one` and their `HomotopyCategory` versions.

## Implementation notes

The well-definedness of the shift on the homotopy category, i.e. that a homotopy `h` from `f`
to `g` gives the homotopy `n.negOnePow • h` from `f⟦n⟧'` to `g⟦n⟧'`, is Mathlib's
`Homotopy.shift`; Mathlib's shift on `HomotopyCategory C (ComplexShape.up ℤ)` is induced from it
on the quotient category. The equalities of functors are proved with `CategoryTheory.Functor.ext`
and `HomologicalComplex.ext`: the objects `K.X (p + i + j)` and `K.X (p + (i + j))` are equal but
not definitionally so, and the equality is transported by `eqToHom`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

variable {C : Type*} [Category C] [Preadditive C]

lemma d_comp_eqToHom_of_eq (K : CochainComplex C ℤ) {a a' b b' : ℤ} (ha : a = a')
    (hb : b = b') :
    K.d a b ≫ eqToHom (congrArg K.X hb) = eqToHom (congrArg K.X ha) ≫ K.d a' b' := by
  subst ha hb
  simp

lemma hom_f_eq_eqToHom_comp {K L : CochainComplex C ℤ} (f : K ⟶ L) {a b : ℤ} (h : a = b) :
    f.f a = eqToHom (congrArg K.X h) ≫ f.f b ≫ eqToHom (congrArg L.X h.symm) := by
  subst h
  simp

variable (C) in
/-- The shift functor `T^n` on `C(A)` is additive. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_additive (n : ℤ) :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).Additive :=
  inferInstance

lemma shiftFunctor_obj_shiftFunctor_obj (K : CochainComplex C ℤ) (i j : ℤ) :
    (K⟦j⟧)⟦i⟧ = K⟦i + j⟧ := by
  refine HomologicalComplex.ext (funext fun p => congrArg K.X (by lia)) fun p q _ => ?_
  simp only [shiftFunctor_obj_d', Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    ← Int.negOnePow_add]
  rw [d_comp_eqToHom_of_eq K (show p + i + j = p + (i + j) by lia)
    (show q + i + j = q + (i + j) by lia)]

lemma shiftFunctor_obj_zero_eq (K : CochainComplex C ℤ) : K⟦(0 : ℤ)⟧ = K := by
  refine HomologicalComplex.ext (funext fun p => congrArg K.X (by lia)) fun p q _ => ?_
  simp only [shiftFunctor_obj_d', Int.negOnePow_zero, one_smul]
  rw [d_comp_eqToHom_of_eq K (show p + 0 = p by lia) (show q + 0 = q by lia)]

variable (C)

/-- On `C(A)`, `T^i ∘ T^j = T^(i+j)` as an equality of functors. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_comp_shiftFunctor (i j : ℤ) :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) j ⋙
        CategoryTheory.shiftFunctor (CochainComplex C ℤ) i =
      CategoryTheory.shiftFunctor (CochainComplex C ℤ) (i + j) := by
  refine CategoryTheory.Functor.ext (fun K => shiftFunctor_obj_shiftFunctor_obj K i j)
    fun (K L : CochainComplex C ℤ) f => ?_
  ext p
  simp only [Functor.comp_map, HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f]
  exact hom_f_eq_eqToHom_comp f (by lia)

/-- On `C(A)`, `T^0 = Id` as an equality of functors. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_zero_eq_id :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) (0 : ℤ) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun K => shiftFunctor_obj_zero_eq K)
    fun (K L : CochainComplex C ℤ) f => ?_
  ext p
  simp only [Functor.id_map, HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f]
  exact hom_f_eq_eqToHom_comp f (by lia)

/-- On `C(A)`, `T^(n+1) = T^n ⋙ T` for `n : ℕ`: with `T^0 = Id`, `T^n` is the `n`-fold
iterate of `T = T^1`. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_natCast_succ (n : ℕ) :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) ((n + 1 : ℕ) : ℤ) =
      CategoryTheory.shiftFunctor (CochainComplex C ℤ) (n : ℤ) ⋙
        CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ) := by
  rw [shiftFunctor_comp_shiftFunctor]
  congr 1
  push_cast
  exact add_comm _ _

/-- On `C(A)`, `T^(-1)` is a left inverse of `T`. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_one_comp_neg_one :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ) ⋙
      CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ) = 𝟭 _ := by
  rw [shiftFunctor_comp_shiftFunctor, neg_add_cancel, shiftFunctor_zero_eq_id]

/-- On `C(A)`, `T^(-1)` is a right inverse of `T`. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_neg_one_comp_one :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ) ⋙
      CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ) = 𝟭 _ := by
  rw [shiftFunctor_comp_shiftFunctor, add_neg_cancel, shiftFunctor_zero_eq_id]

end CochainComplex

namespace HomotopyCategory

variable (C : Type*) [Category C] [Preadditive C]

/-- The shift functor `T^n` on `K(A)` is additive. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_additive (n : ℤ) :
    (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n).Additive :=
  inferInstance

/-- The shift on `K(A)` is induced by the shift on `C(A)`: `[-] ∘ T^n = T^n ∘ [-]` as an equality
of functors. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem quotient_comp_shiftFunctor (n : ℤ) :
    quotient C (ComplexShape.up ℤ) ⋙ shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n =
      shiftFunctor (CochainComplex C ℤ) n ⋙ quotient C (ComplexShape.up ℤ) := by
  with_unfolding_all rfl

variable {C} in
/-- `T^n [f] = [T^n f]`, up to the identifications `T^n [K] = [T^n K]` of objects. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem quotient_map_shiftFunctor_map {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    ((quotient C (ComplexShape.up ℤ)).map f)⟦n⟧' =
      eqToHom (shift_quotient_obj K n) ≫ (quotient C (ComplexShape.up ℤ)).map (f⟦n⟧') ≫
        eqToHom (shift_quotient_obj L n).symm :=
  Functor.congr_hom (quotient_comp_shiftFunctor C n) f

/-- On `K(A)`, `T^i ∘ T^j = T^(i+j)` as an equality of functors. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_comp_shiftFunctor (i j : ℤ) :
    shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) j ⋙
        shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) i =
      shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (i + j) := by
  apply Quotient.lift_unique'
  change quotient C (ComplexShape.up ℤ) ⋙ _ = quotient C (ComplexShape.up ℤ) ⋙ _
  rw [← Functor.assoc, quotient_comp_shiftFunctor, Functor.assoc, quotient_comp_shiftFunctor,
    ← Functor.assoc, CochainComplex.shiftFunctor_comp_shiftFunctor, quotient_comp_shiftFunctor]

/-- On `K(A)`, `T^0 = Id` as an equality of functors. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_zero_eq_id :
    shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (0 : ℤ) = 𝟭 _ := by
  apply Quotient.lift_unique'
  change quotient C (ComplexShape.up ℤ) ⋙ _ = quotient C (ComplexShape.up ℤ) ⋙ _
  rw [quotient_comp_shiftFunctor, CochainComplex.shiftFunctor_zero_eq_id, Functor.id_comp,
    Functor.comp_id]

/-- On `K(A)`, `T^(n+1) = T^n ⋙ T` for `n : ℕ`. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_natCast_succ (n : ℕ) :
    shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) ((n + 1 : ℕ) : ℤ) =
      shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (n : ℤ) ⋙
        shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ) := by
  rw [shiftFunctor_comp_shiftFunctor]
  congr 1
  push_cast
  exact add_comm _ _

/-- On `K(A)`, `T^(-1)` is a left inverse of `T`. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_one_comp_neg_one :
    shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ) ⋙
      shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (-1 : ℤ) = 𝟭 _ := by
  rw [shiftFunctor_comp_shiftFunctor, neg_add_cancel, shiftFunctor_zero_eq_id]

/-- On `K(A)`, `T^(-1)` is a right inverse of `T`. -/
@[weil "lem_fka2_shift_functor_well_defined"]
theorem shiftFunctor_neg_one_comp_one :
    shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (-1 : ℤ) ⋙
      shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ) = 𝟭 _ := by
  rw [shiftFunctor_comp_shiftFunctor, add_neg_cancel, shiftFunctor_zero_eq_id]

end HomotopyCategory
