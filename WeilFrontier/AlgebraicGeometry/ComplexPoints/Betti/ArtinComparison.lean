/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Betti.Inputs
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonColimits
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonFinite
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonProductProjectiveLines
public import WeilFrontier.CategoryTheory.Abelian.EffaceableComparisonDegreeZero
public import WeilFrontier.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase

/-!
# Artin's comparison theorem for projective schemes over `ℂ`

Let `Y` be a projective scheme over `ℂ`. For every torsion abelian sheaf `F` on the small étale
site of `Y` and every `n`, the comparison map `c^n(Y, F) : H^n_et(Y, F) → H^n(Y(ℂ), F_an)` is
bijective. In particular, for every finite abelian group `M`, the étale cohomology `H^n_et(Y, M)`
is isomorphic to the sheaf cohomology `H^n(Y(ℂ), M)` of the constant sheaf on `Y(ℂ)` with the
analytic topology, naturally in `M` (Artin's comparison theorem, SGA 4 XVI 4.1).

The proof reduces to a product of projective lines. A closed immersion `i : Y ⟶ ℙᴺ_ℂ` over `ℂ`
is finite, and the symmetric product `σ : (ℙ¹_ℂ)ᴺ ⟶ ℙᴺ_ℂ` is finite and surjective. In the
fibre product `Z = Y ×_{ℙᴺ} (ℙ¹)ᴺ` the projection `h : Z ⟶ Y` is finite surjective and the
projection `g : Z ⟶ (ℙ¹)ᴺ` is finite. On a direct image along a finite morphism the comparison
map is that of the source, so the comparison theorem for `(ℙ¹)ᴺ` gives it on `Z` for sheaves
killed by some positive integer. Every sheaf `F` on `Y` killed by `n > 0` embeds into
`h_* h^* F` (the unit of the adjunction is injective since `h` is surjective), again killed by
`n`, on which the comparison map is that of `Z`. As sheaves killed by `n` are stable under
quotients, the effaceability criterion gives the comparison theorem on `Y` for sheaves killed by
a positive integer, and the commutation of both cohomologies with filtered colimits extends it
to all torsion sheaves.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.pc_of_isProjective`: the comparison theorem for torsion
  sheaves on a projective scheme over `ℂ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.artinComparisonAt_of_isProjective`,
  `AlgebraicGeometry.Scheme.artinComparison`: Artin's comparison theorem with finite constant
  coefficients, for projective (in particular smooth projective) schemes over `ℂ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.pc_of_isFinite_projectiveSpaceOver`: the comparison
  theorem for `Y` projective over `ℂ` with a finite morphism to `ℙᵈ_ℂ` over `ℂ`, given it for
  `(ℙ¹_ℂ)ᵈ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonBijectiveOn_boundedTorsion_of_isFinite`:
  the comparison map is bijective on sheaves killed by a positive integer on a scheme finite
  over a separated scheme satisfying the comparison theorem.

## Implementation notes

Only finiteness of the morphism `Y ⟶ ℙᴺ_ℂ` enters, so the closed immersion of the definition of
projectivity serves; projective Noether normalization (a finite surjection onto `ℙ^{dim Y}_ℂ`) is
not needed. Smoothness of `Y` is not used.

## References

* [SGA4] M. Artin, A. Grothendieck, J.-L. Verdier, *Théorie des topos et cohomologie étale des
  schémas*, Tome 3, Exposé XVI, Théorème 4.1.
* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, 11.6.
* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
-/

@[expose] public section

open CategoryTheory Limits Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### Sheaves killed by a positive integer -/

section BoundedTorsion

/-- An object killed by `n` is sent by an additive functor to an object killed by `n`. -/
theorem _root_.CategoryTheory.Functor.zsmul_id_obj_eq_zero {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive] {F : C} {n : ℤ}
    (hF : n • 𝟙 F = 0) : n • 𝟙 (G.obj F) = 0 := by
  rw [← G.map_id, ← Functor.map_zsmul, hF, Functor.map_zero]

/-- In a short exact sequence, the quotient is killed by `n` when the middle term is. -/
theorem _root_.CategoryTheory.ShortComplex.ShortExact.zsmul_id_X₃_eq_zero {C : Type*}
    [Category C] [Abelian C] {S : ShortComplex C} (hS : S.ShortExact) {n : ℤ}
    (h : n • 𝟙 S.X₂ = 0) : n • 𝟙 S.X₃ = 0 := by
  have := hS.epi_g
  rw [← cancel_epi S.g, Preadditive.comp_zsmul, Category.comp_id, comp_zero,
    ← Category.id_comp S.g, ← Preadditive.zsmul_comp, h, zero_comp]

/-- An abelian étale sheaf killed by a positive integer is torsion. -/
theorem torsionSheafProperty_of_zsmul_id_eq_zero {X : Scheme.{0}} (F : EtSheaf X) {n : ℕ}
    (hn : 0 < n) (hF : (n : ℤ) • 𝟙 F = 0) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F := by
  intro U s
  refine ⟨⊤, X.smallEtaleTopology.top_mem U, fun V f _ => ⟨n, hn, ?_⟩⟩
  have h := congrArg ((sheafSections X.smallEtaleTopology AddCommGrpCat.{1}).obj
    (Opposite.op V)).map hF
  rw [Functor.map_zsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  simpa [AddCommGrpCat.hom_zsmul] using ConcreteCategory.congr_hom h (F.obj.map f.op s)

variable {X S : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (s : S ⟶ Spec (.of ℂ))
  [LocallyOfFiniteType x] [LocallyOfFiniteType s]

/-- **The comparison theorem descends along finite morphisms, for bounded torsion.** Let
`g : X ⟶ S` be a finite morphism over `ℂ` with `S` separated over `ℂ` satisfying the comparison
theorem for torsion sheaves. Then the comparison map of `X` is bijective in every degree on every
sheaf killed by a positive integer: it is the comparison map of `S` on the direct image, again
killed by that integer. -/
theorem comparisonBijectiveOn_boundedTorsion_of_isFinite [IsSeparated s] (g : X ⟶ S)
    [IsFinite g] (hg : g ≫ s = x) (hS : PC s) :
    ComparisonBijectiveOn x (fun F => ∃ n : ℕ, 0 < n ∧ (n : ℤ) • 𝟙 F = 0) := by
  rintro F ⟨n, hn, hF⟩ m
  rw [← comparisonMap_pushforward_bijective_iff s x g hg F m]
  exact hS _ (torsionSheafProperty_of_zsmul_id_eq_zero _ hn
    ((smallEtalePushforwardAb g).zsmul_id_obj_eq_zero hF)) m

end BoundedTorsion

/-! ### Projective schemes -/

section Projective

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

/-- **The comparison theorem for a projective scheme finite over projective space.** Let `Y` be
projective over `ℂ` with a finite morphism `π : Y ⟶ ℙᵈ_ℂ` over `ℂ`, and assume the comparison
theorem for `(ℙ¹_ℂ)ᵈ`. Then the comparison map of `Y` is bijective on torsion sheaves in every
degree. The fibre product `Z = Y ×_{ℙᵈ} (ℙ¹)ᵈ` along the symmetric product is finite over
`(ℙ¹)ᵈ` and finite surjective over `Y`, and every sheaf on `Y` killed by `n > 0` embeds into its
pull-push along `Z ⟶ Y`. -/
theorem pc_of_isFinite_projectiveSpaceOver (hy : IsProjective y) {d : ℕ}
    (π : Y ⟶ projectiveSpaceOver d (Spec (.of ℂ))) [IsFinite π]
    (hπ : π ≫ (projectiveSpaceOver d (Spec (.of ℂ)) ↘ Spec (.of ℂ)) = y)
    (hd : PC (SymmetricProduct.linePower ℂ d).hom) : PC y := by
  have := isProper_of_isProjective y hy
  let σ := SymmetricProduct.symmetricProduct ℂ d
  let h := pullback.fst π σ
  let g := pullback.snd π σ
  have hg : g ≫ (SymmetricProduct.linePower ℂ d).hom = h ≫ y := by
    rw [← SymmetricProduct.symmetricProduct_comp_fst, ← pullback.condition_assoc]
    exact congrArg (pullback.fst π σ ≫ ·) hπ
  have hZ := comparisonBijectiveOn_boundedTorsion_of_isFinite (h ≫ y) _ g hg hd
  refine pc_of_boundedTorsion_of_isProjective y hy fun F hF m => ?_
  exact (analyticInverseImage y).mapExtOfIso_bijective_of_effaceable'
      ((constantSheafIso y).app (AddCommGrpCat.of (ULift ℤ)))
      (fun F => ∃ n : ℕ, 0 < n ∧ (n : ℤ) • 𝟙 F = 0)
      (fun _ hS _ ⟨n, hn, h₂⟩ => ⟨n, hn, hS.zsmul_id_X₃_eq_zero h₂⟩)
      (fun F ⟨n, hn, hF⟩ => ⟨(etaleAbelianDirectImage.{0, 0} h).obj
          ((etaleAbelianInverseImage.{0, 0} h).obj F),
        (etaleAbelianInverseImageDirectImageAdj.{0, 0} h).unit.app F,
        mono_etaleAbelianUnit_of_surjective h F,
        ⟨n, hn, Functor.zsmul_id_obj_eq_zero _ (Functor.zsmul_id_obj_eq_zero _ hF)⟩,
        fun m => (comparisonMap_pushforward_bijective_iff y (h ≫ y) h rfl _ m).2
          (hZ _ ⟨n, hn, Functor.zsmul_id_obj_eq_zero _ hF⟩ m)⟩) m F hF

/-- The comparison theorem for projective `Y` over `ℂ`, given it for every `(ℙ¹_ℂ)ᵈ`. -/
theorem pc_of_isProjective_of_pc_linePower (hy : IsProjective y)
    (hlp : ∀ d, PC (SymmetricProduct.linePower ℂ d).hom) : PC y := by
  obtain ⟨N, i, hi, hiy⟩ := (isProjective_iff_isProjectiveMorphism_of_isAffine y).mp hy
  exact pc_of_isFinite_projectiveSpaceOver y hy i hiy (hlp N)

omit [LocallyOfFiniteType y] in
/-- Artin's comparison with finite constant coefficients for projective `Y` over `ℂ`, given the
comparison theorem for every `(ℙ¹_ℂ)ᵈ`. A finite constant sheaf is killed by the order of its
group, hence torsion. -/
theorem artinComparisonAt_of_isProjective_of_pc_linePower (hy : IsProjective y)
    (hlp : ∀ d, PC (SymmetricProduct.linePower ℂ d).hom) : ArtinComparisonAt y := by
  have := isProper_of_isProjective y hy
  refine artinComparisonAt_of_bijective y fun M _ ν => ?_
  refine pc_of_isProjective_of_pc_linePower y hy hlp _
    (torsionSheafProperty_of_zsmul_id_eq_zero _ (n := Nat.card M) Nat.card_pos
      (Functor.zsmul_id_obj_eq_zero _ ?_)) ν
  ext a
  simp only [AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply, natCast_zsmul]
  have := card_nsmul_eq_zero' (G := ULift.{1} M) (x := a)
  rwa [Nat.card_ulift] at this

/-- **The comparison theorem for projective schemes over `ℂ`.** For `Y` projective over `ℂ`, the
comparison map `H^n_et(Y, F) → H^n(Y(ℂ), F_an)` is bijective for every torsion abelian sheaf `F`
and every `n`. -/
theorem pc_of_isProjective (hy : IsProjective y) : PC y :=
  pc_of_isProjective_of_pc_linePower y hy pc_linePower

omit [LocallyOfFiniteType y] in
/-- **Artin's comparison theorem for projective schemes over `ℂ`** (SGA 4, XVI 4.1): for `Y`
projective over `ℂ`, `H^ν_et(Y, M) ≃+ H^ν(Y(ℂ), M)` for every finite abelian group `M` and every
`ν`, naturally in `M`. -/
theorem artinComparisonAt_of_isProjective (hy : IsProjective y) : ArtinComparisonAt y :=
  artinComparisonAt_of_isProjective_of_pc_linePower y hy pc_linePower

omit [LocallyOfFiniteType y] in
/-- Artin's comparison theorem for smooth projective schemes over `ℂ`. -/
theorem artinComparisonAt_of_smooth_of_isProjective (_ : Smooth y) (hy : IsProjective y) :
    ArtinComparisonAt y :=
  artinComparisonAt_of_isProjective y hy

end Projective

end AlgebraicGeometry.Scheme.ComplexPoints

/-- **Artin's comparison theorem** for smooth projective schemes over `ℂ`. -/
theorem AlgebraicGeometry.Scheme.artinComparison : AlgebraicGeometry.Scheme.ArtinComparison :=
  fun _ y _ hy => AlgebraicGeometry.Scheme.ComplexPoints.artinComparisonAt_of_isProjective y hy
