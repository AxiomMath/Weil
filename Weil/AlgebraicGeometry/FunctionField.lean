module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.RingTheory.Serre.Defs
public import Mathlib.FieldTheory.SeparableClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.SheafStalk
public import Weil.AlgebraicGeometry.Sites.StalkUnchangedAlgebraicClosure

/-!
# Sections of a normal noetherian domain over an open containing all height-one primes

Let `R` be a noetherian normal domain and `W ⊆ Spec R` an open subset containing every prime of
height at most `1`. Then the map `R → Γ(Spec R, W)` is bijective: every regular function on `W`
extends uniquely to `Spec R` (algebraic Hartogs lemma).

The proof embeds `Γ(Spec R, W)` into the function field `K` of `Spec R` by the germ at the
generic point, which lies in `W` because `(0)` has height `0`. For a prime `𝔭` of height `1`,
`𝔭 ∈ W` and the germ at the generic point factors through the stalk at `𝔭`, which is `R_𝔭`; so
the image of a section lies in `⋂_{ht 𝔭 = 1} R_𝔭 = R`.

## Main results

* `AlgebraicGeometry.bijective_algebraMap_sections_of_height_le_one_mem`: the map
  `R → Γ(Spec R, W)` is bijective.
* `AlgebraicGeometry.isIso_map_sections_of_height_le_one_mem`: the restriction map
  `Γ(Spec R, ⊤) ⟶ Γ(Spec R, W)` is an isomorphism.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], Ch. I, §7.
* [Stacks Project, Tag 031T][stacks]
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- **Algebraic Hartogs lemma.** Let `R` be a noetherian normal domain and `W ⊆ Spec R` an open
subset containing every prime ideal of height at most `1`. Then the map `R → Γ(Spec R, W)` is
bijective. -/
@[weil "lem_fk107_normal_domain_sections_codim_two"]
theorem bijective_algebraMap_sections_of_height_le_one_mem {R : CommRingCat} [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (W : (Spec R).Opens)
    (hW : ∀ p : Spec R, p.asIdeal.height ≤ 1 → p ∈ W) :
    Function.Bijective (algebraMap R Γ(Spec R, W)) := by
  have hη : genericPoint (Spec R) ∈ W := hW (genericPoint (Spec R)) (by
    rw [genericPoint_eq_bot_of_affine R]
    simp)
  have : Nonempty W := ⟨⟨_, hη⟩⟩
  have key : ∀ d : R, (Spec R).germToFunctionField W (algebraMap R Γ(Spec R, W) d) =
      algebraMap R (Spec R).functionField d := fun d =>
    StructureSheaf.algebraMap_germ_apply _ _ _ _
  refine ⟨fun a b h => IsFractionRing.injective R (Spec R).functionField ?_, fun s => ?_⟩
  · rw [← key, ← key, h]
  have hz : (Spec R).germToFunctionField W s ∈ (⊥ : Subalgebra R (Spec R).functionField) := by
    rw [← (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
      (R := R) (Spec R).functionField).2.1]
    refine Algebra.mem_iInf.mpr fun p => Algebra.mem_iInf.mpr fun hp => ?_
    have hpW : p ∈ W := hW p hp.le
    let _ : Algebra R ((Spec R).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk p) p.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk R p
    let _ : Algebra ((Spec R).presheaf.stalk p) (Spec R).functionField :=
      stalkFunctionFieldAlgebra (Spec R) p
    obtain ⟨⟨a, ⟨b, hb⟩⟩, e⟩ :=
      IsLocalization.mk'_surjective p.asIdeal.primeCompl ((Spec R).presheaf.germ W p hpW s)
    have h1 : algebraMap ((Spec R).presheaf.stalk p) (Spec R).functionField
        ((Spec R).presheaf.germ W p hpW s) = (Spec R).germToFunctionField W s :=
      Scheme.algebraMap_germ_eq_germToFunctionField _ hpW s
    have tower : ∀ r : R, algebraMap ((Spec R).presheaf.stalk p) (Spec R).functionField
        (algebraMap R _ r) = algebraMap R (Spec R).functionField r := by
      intro r
      have : Nonempty (⊤ : (Spec R).Opens) := ⟨⟨p, trivial⟩⟩
      rw [show algebraMap R ((Spec R).presheaf.stalk p) r =
          (Spec R).presheaf.germ ⊤ p trivial (algebraMap R Γ(Spec R, ⊤) r) from
        (StructureSheaf.algebraMap_germ_apply _ _ _ _).symm]
      exact (Scheme.algebraMap_germ_eq_germToFunctionField (X := Spec R) (U := ⊤)
        (x := p) trivial _).trans (StructureSheaf.algebraMap_germ_apply _ _ _ _)
    have hb0 : algebraMap R (Spec R).functionField b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero fun h => hb (h ▸ p.asIdeal.zero_mem))
    refine ⟨a, b, hb, ?_⟩
    rw [← h1, ← e, eq_mul_inv_iff_mul_eq₀ hb0, ← tower, ← tower, ← map_mul,
      IsLocalization.mk'_spec]
  obtain ⟨d, hd⟩ := Algebra.mem_bot.mp hz
  exact ⟨d, (Spec R).germToFunctionField_injective W (by rw [key, hd])⟩

/-- Under the hypotheses of `bijective_algebraMap_sections_of_height_le_one_mem`, the restriction
map `Γ(Spec R, ⊤) ⟶ Γ(Spec R, W)` is an isomorphism. -/
theorem isIso_map_sections_of_height_le_one_mem {R : CommRingCat} [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (W : (Spec R).Opens)
    (hW : ∀ p : Spec R, p.asIdeal.height ≤ 1 → p ∈ W) :
    IsIso ((Spec R).presheaf.map (homOfLE le_top : W ⟶ ⊤).op) := by
  have h : IsIso ((Scheme.ΓSpecIso R).inv ≫
      (Spec R).presheaf.map (homOfLE le_top : W ⟶ ⊤).op) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_algebraMap_sections_of_height_le_one_mem W hW)
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso R).inv _

end AlgebraicGeometry

end

/-! ### The generic geometric point of an integral scheme -/

/-!
# The generic geometric point of an integral scheme

Let `X` be an integral scheme with function field `K = 𝒪_{X,ξ}`, `ξ` the generic point. The
canonical morphism `η : Spec K ⟶ X` onto the generic point is
`Stacks.EtaleCohomology.genericPointInclusion X`. For a separable closure `K^sep` of `K`, the
morphism `θ : Spec K^sep ⟶ Spec K` given by `K ⊆ K^sep` and the composite
`η̄ = θ ≫ η : Spec K^sep ⟶ X` give the generic geometric point in the sense of Freitag–Kiehl,
whose geometric points are over separably closed fields.

Geometric points of this library, `AlgebraicGeometry.GeometricPoint`, are over algebraically
closed fields. The corresponding generic geometric point is `Spec K̄ ⟶ Spec K ⟶ X` for an
algebraic closure `K̄` of `K`. The two have the same image, the generic point, and the second
factors through the first, so that they define isomorphic points of the small étale site; in
particular the stalks of an étale sheaf at them agree.

## Main definitions

* `AlgebraicGeometry.Scheme.separableClosureι`: the morphism `θ : Spec K^sep ⟶ Spec K`.
* `AlgebraicGeometry.Scheme.genericSepClosedPoint`: `η̄ = θ ≫ η : Spec K^sep ⟶ X`.
* `AlgebraicGeometry.Scheme.genericGeometricPoint`: the generic geometric point
  `Spec K̄ ⟶ Spec K ⟶ X` as an `AlgebraicGeometry.GeometricPoint`.
* `AlgebraicGeometry.Scheme.pointSmallEtaleGenericIso`: the isomorphism of points of the small
  étale site defined by the two generic geometric points.

## Main results

* `AlgebraicGeometry.Scheme.genericSepClosedPoint_apply`,
  `AlgebraicGeometry.Scheme.genericGeometricPoint_liesOver`: both lie over the generic point.
* `AlgebraicGeometry.Scheme.exists_comp_genericSepClosedPoint_eq`: the algebraically closed
  generic geometric point factors through the separably closed one.

## Implementation notes

The separable closure is Mathlib's `SeparableClosure K` (the separable closure inside an
algebraic closure), and the algebraic closure is `AlgebraicClosure K`, as in
`AlgebraicGeometry.GeometricPoint.ofAlgebraicClosure`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.5
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.Scheme

/-- The morphism `θ : Spec K^sep ⟶ Spec K` given by the inclusion of a field into its
separable closure. -/
abbrev separableClosureι (K : Type u) [Field K] :
    Spec (.of (SeparableClosure K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))

variable (X : Scheme.{u}) [IsIntegral X]

/-- **The generic geometric point** `η̄ = θ ≫ η : Spec K^sep ⟶ X` of an integral scheme `X`
with function field `K`, where `η : Spec K ⟶ X` is the canonical morphism onto the generic
point and `θ` is given by `K ⊆ K^sep`. -/
@[weil "not_fk105_generic_geometric_point"]
def genericSepClosedPoint : Spec (.of (SeparableClosure X.functionField)) ⟶ X :=
  separableClosureι X.functionField ≫ genericPointInclusion X

lemma genericSepClosedPoint_eq :
    genericSepClosedPoint X = separableClosureι X.functionField ≫ genericPointInclusion X :=
  rfl

/-- **The generic geometric point** of an integral scheme `X` with function field `K`, as an
algebraically closed geometric point: `Spec K̄ ⟶ Spec K ⟶ X` for an algebraic closure `K̄`
of `K`. -/
@[weil "not_fk105_generic_geometric_point"]
def genericGeometricPoint : GeometricPoint X :=
  (GeometricPoint.ofAlgebraicClosure X.functionField).map (genericPointInclusion X)

@[simp]
lemma genericGeometricPoint_residueField :
    (genericGeometricPoint X).residueField = AlgebraicClosure X.functionField :=
  rfl

lemma genericGeometricPoint_hom :
    (genericGeometricPoint X).hom =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField
        (AlgebraicClosure X.functionField))) ≫ genericPointInclusion X :=
  rfl

/-- The canonical morphism `η : Spec K ⟶ X` maps every point to the generic point. -/
@[simp]
lemma genericPointInclusion_apply (p : Spec X.functionField) :
    genericPointInclusion X p = genericPoint X := by
  have : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  rw [Subsingleton.elim p (IsLocalRing.closedPoint _)]
  exact X.fromSpecStalk_closedPoint

/-- `η̄` lies over the generic point. -/
@[simp]
lemma genericSepClosedPoint_apply (p : Spec (.of (SeparableClosure X.functionField))) :
    genericSepClosedPoint X p = genericPoint X :=
  genericPointInclusion_apply X _

/-- The generic geometric point lies over the generic point. -/
@[simp]
lemma genericGeometricPoint_liesOver :
    (genericGeometricPoint X).LiesOver (genericPoint X) :=
  genericPointInclusion_apply X _

/-- The algebraically closed generic geometric point factors through `η̄`, by an embedding of
the separable closure into the algebraic closure over `K`. -/
lemma exists_comp_genericSepClosedPoint_eq :
    ∃ a : (genericGeometricPoint X).source ⟶ Spec (.of (SeparableClosure X.functionField)),
      a ≫ genericSepClosedPoint X = (genericGeometricPoint X).hom := by
  let K := X.functionField
  let φ : SeparableClosure K →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩
  rw [genericSepClosedPoint_eq, genericGeometricPoint_hom, ← Category.assoc, ← Spec.map_comp]
  congr 3
  ext x
  exact φ.commutes x

/-- The two generic geometric points `Spec K̄ ⟶ X` and `η̄ : Spec K^sep ⟶ X` define isomorphic
points of the small étale site of `X`. -/
def pointSmallEtaleGenericIso :
    pointSmallEtale (genericGeometricPoint X).hom ≅ pointSmallEtale (genericSepClosedPoint X) :=
  have := isIso_pointSmallEtaleHomOfFac _ _ _ (exists_comp_genericSepClosedPoint_eq X).choose_spec
  asIso (pointSmallEtaleHomOfFac _ _ _ (exists_comp_genericSepClosedPoint_eq X).choose_spec)

end AlgebraicGeometry.Scheme
