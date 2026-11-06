module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreStalk
public import WeilFrontier.AlgebraicGeometry.Sites.GeometricPointSameImageStalkIso
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Betti.Inputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.FiniteEtaleCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.AtPrime

/-!
# The cohomology of the geometric fibres of a smooth proper morphism over an irreducible base

Let `f : X ⟶ T` be smooth and proper with `T` irreducible, and let `F` be a locally constant
torsion abelian sheaf on `X_étale` whose stalks have orders prime to the residue characteristics.
For any two geometric points `s̄₁`, `s̄₂` of `T` the étale cohomology groups of the geometric
fibres are isomorphic, `Hᵛ(X_{s̄₁}, F) ≅ Hᵛ(X_{s̄₂}, F)`, naturally in `F`.

The isomorphism is the composite
`Hᵛ(X_{s̄₁}, F) ≅ Hᵛ((Rf_* F)_{s̄₁}) ≅ Hᵛ((Rf_* F)_{t̄₁}) ≅ Hᵛ((Rf_* F)_{t̄₂}) ≅ Hᵛ((Rf_* F)_{s̄₂})
≅ Hᵛ(X_{s̄₂}, F)`: the outer steps are proper base change at a geometric point; `t̄ᵢ` is a
geometric point of the strict henselization of `T` at `s̄ᵢ` lying over the generic point `η` of
`T` (it exists because the strict henselization is faithfully flat over the local ring, whose
spectrum maps onto the generizations of the image of `s̄ᵢ`), and the second and fourth steps are
the specialization maps, invertible for smooth proper `f` (Stacks 0GKD); the middle step
identifies the stalks at two geometric points over the same point `η`.

For the constant sheaf with value a finite abelian group `M` killed by an integer `n` invertible
on `T`, the inverse image of the constant sheaf to a fibre is the constant sheaf, which gives
`Hᵛ(X_{s̄₁}, M) ≃+ Hᵛ(X_{s̄₂}, M)`, natural in `M`.

## Main definitions

* `AlgebraicGeometry.IsSpecializationAdmissible`: the hypotheses of Stacks 0GKD on a sheaf
  (locally constant, torsion, stalks of orders prime to the residue characteristics).
* `AlgebraicGeometry.genericGeometricPointOfStrictHenselization`: a geometric point of the strict
  henselization at `s̄` lying over the generic point of an irreducible scheme.
* `AlgebraicGeometry.fibreCohomologyIsoOfSmoothProper`: `Hᵛ(X_{s̄₁}, F) ≅ Hᵛ(X_{s̄₂}, F)` for an
  admissible sheaf `F`, given points `t̄ᵢ` of the strict henselizations with the same image.
* `AlgebraicGeometry.fibreConstantCohomologyIso`: `Hᵛ(X_{s̄₁}, M) ≅ Hᵛ(X_{s̄₂}, M)` for the
  constant sheaf on a finite `M` killed by an integer invertible on `T`, `T` irreducible.
* `AlgebraicGeometry.fibreEtaleCohomologyConstantAddEquiv`: the same in universe `0` on
  `AlgebraicGeometry.Scheme.etaleCohomologyConstant`.
* `AlgebraicGeometry.fibreEtaleCohomologyZModAddEquiv`: the case `M = ℤ/ℓ^{m+1}` over `Spec R`,
  `R` a domain in which `ℓ` is invertible.

## Main results

* `AlgebraicGeometry.exists_geometricPoint_strictHenselization_liesOver`: every generization of
  the image of `s̄` is the image of a geometric point of the strict henselization at `s̄`.
* `AlgebraicGeometry.fibreCohomologyIsoOfSmoothProper_hom_naturality`,
  `AlgebraicGeometry.fibreConstantCohomologyIso_hom_naturality`,
  `AlgebraicGeometry.fibreEtaleCohomologyConstantAddEquiv_naturality`: naturality in the sheaf,
  resp. in the coefficient group.
* `AlgebraicGeometry.fibreEtaleCohomologyZModAddEquiv_transition`: compatibility with the
  reductions `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`.

## Implementation notes

The étale cohomology groups are those of Mathlib's small étale site with coefficients in
`AddCommGrpCat.{u + 1}`, and the derived categories are those of `HasDerivedCategory.standard`,
in which Stacks 0GKD is stated. The base is only required to be irreducible (an integral scheme,
e.g. the spectrum of a domain, is a special case), and the coefficients may be any finite abelian
group killed by an integer invertible on the base.

## References

* [Freitag–Kiehl, *Étale cohomology and the Weil conjecture*, IV.1.7 (proof) and I.8]
* [Stacks Project, Tag 0GKD](https://stacks.math.columbia.edu/tag/0GKD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard hasExt_sheaf_smallEtale_succ

universe w u

namespace AlgebraicGeometry

/-- A composite of three isomorphisms commutes with given vertical maps if each of the three
squares does. -/
theorem comp_trans_trans_hom_eq {C : Type*} [Category C] {A B D E A' B' D' E' : C}
    (e₁ : A ≅ B) (e₂ : B ≅ D) (e₃ : D ≅ E) (e₁' : A' ≅ B') (e₂' : B' ≅ D') (e₃' : D' ≅ E')
    (a : A ⟶ A') (b : B ⟶ B') (d : D ⟶ D') (e : E ⟶ E')
    (h₁ : e₁.hom ≫ b = a ≫ e₁'.hom) (h₂ : e₂.hom ≫ d = b ≫ e₂'.hom)
    (h₃ : e₃.hom ≫ e = d ≫ e₃'.hom) :
    (e₁ ≪≫ e₂ ≪≫ e₃).hom ≫ e = a ≫ (e₁' ≪≫ e₂' ≪≫ e₃').hom := by
  simp only [Iso.trans_hom, Category.assoc, h₃, reassoc_of% h₂, reassoc_of% h₁]

/-! ### Geometric points of the strict henselization over a generization -/

section StrictHenselizationPoints

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- Every generization `y` of the image of a geometric point `s̄` of `S` is the image of a point
of the strict henselization of `S` at `s̄`: the strict henselization is flat and local, hence
faithfully flat, over the local ring of `S` at the image of `s̄`, whose spectrum maps onto the
generizations of that point. -/
theorem exists_mem_strictHenselization_map_eq {y : S} (hy : y ⤳ s.hom default) :
    ∃ q : strictHenselization B S hS s, strictHenselizationToBase B S hS s q = y := by
  have hy' : y ⤳ s.hom (IsLocalRing.closedPoint s.residueField) := by
    convert hy using 2
    exact congrArg s.hom (Subsingleton.elim _ _)
  obtain ⟨p, hp⟩ : y ∈ Set.range
      (S.fromSpecStalk (s.hom (IsLocalRing.closedPoint s.residueField))) := by
    rw [Scheme.range_fromSpecStalk]
    exact hy'
  have := StacksDraft.flat_of_indEtale (indEtale_etaleLocalRing B S hS s)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := ↥(S.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField))))
    (B := ↥(etaleLocalRing B S hS s))
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := ↥(S.presheaf.stalk (s.hom (IsLocalRing.closedPoint s.residueField))))
    (B := ↥(etaleLocalRing B S hS s)) p
  refine ⟨q, ?_⟩
  rw [← hp, ← hq]
  rfl

/-- Every generization `y` of the image of a geometric point `s̄` of `S` is the image in `S` of a
geometric point of the strict henselization of `S` at `s̄`. -/
theorem exists_geometricPoint_strictHenselization_liesOver {y : S} (hy : y ⤳ s.hom default) :
    ∃ t : GeometricPoint (strictHenselization B S hS s),
      (specializedGeometricPoint B S hS s t).LiesOver y := by
  obtain ⟨q, hq⟩ := exists_mem_strictHenselization_map_eq B S hS s hy
  refine ⟨GeometricPoint.ofPoint _ q, ?_⟩
  change ((GeometricPoint.ofPoint _ q).hom ≫ strictHenselizationToBase B S hS s) default = y
  rw [Scheme.Hom.comp_apply, GeometricPoint.ofPoint_liesOver, hq]

/-- A geometric point of the strict henselization of an irreducible scheme `S` at `s̄` lying over
the generic point of `S`. -/
def genericGeometricPointOfStrictHenselization [IrreducibleSpace S] :
    GeometricPoint (strictHenselization B S hS s) :=
  (exists_geometricPoint_strictHenselization_liesOver B S hS s
    (genericPoint_specializes (s.hom default))).choose

theorem genericGeometricPointOfStrictHenselization_liesOver [IrreducibleSpace S] :
    (specializedGeometricPoint B S hS s
      (genericGeometricPointOfStrictHenselization B S hS s)).LiesOver (genericPoint S) :=
  (exists_geometricPoint_strictHenselization_liesOver B S hS s
    (genericPoint_specializes (s.hom default))).choose_spec

end StrictHenselizationPoints

/-! ### Transfer of the cohomology of the geometric fibres -/

section Transfer

variable (B : BigEtaleSite.{u}) {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (f : X ⟶ T) [Smooth f] [IsProper f]

/-- The hypotheses of Stacks 0GKD on an abelian sheaf, together with torsion of its sections:
locally constant, sections locally torsion, and stalks torsion of orders prime to the residue
characteristics. -/
structure IsSpecializationAdmissible (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) : Prop where
  isLocallyConstant : Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology F
  torsion : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F
  stalk_torsion : ∀ (x : GeometricPoint X) (a : (smallEtaleStalkAb x.hom).obj F),
    ∃ n : ℕ, 0 < n ∧
      (ringChar x.residueField = 0 ∨ Nat.Coprime n (ringChar x.residueField)) ∧ n • a = 0

/-- The specialization isomorphism `Hᵛ((Rf_* F)_{s̄}) ≅ Hᵛ((Rf_* F)_{t̄})` of Stacks 0GKD. -/
def derivedStalkHomologySpecializationIso (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : IsSpecializationAdmissible F) (s : GeometricPoint T)
    (t : GeometricPoint (strictHenselization B T hT s)) (ν : ℤ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} ν).obj
        ((smallEtaleDerivedStalkAb s.hom).obj ((smallEtaleDerivedPushforwardAb f).obj
          ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} ν).obj
        ((smallEtaleDerivedStalkAb (specializedGeometricPoint B T hT s t).hom).obj
          ((smallEtaleDerivedPushforwardAb f).obj
            ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))) :=
  (DerivedCategory.homologyFunctor Ab.{u + 1} ν).mapIso
    (@asIso _ _ _ _ ((smallEtaleDerivedSpecializationStalkAbAt B T hT s t).app _)
      (isIso_specializationMap_of_smooth_of_isProper_unconditional B hX hT f F
        hF.isLocallyConstant hF.stalk_torsion s t))

theorem derivedStalkHomologySpecializationIso_hom (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : IsSpecializationAdmissible F) (s : GeometricPoint T)
    (t : GeometricPoint (strictHenselization B T hT s)) (ν : ℤ) :
    (derivedStalkHomologySpecializationIso B hX hT f F hF s t ν).hom =
      (DerivedCategory.homologyFunctor Ab.{u + 1} ν).map
        ((smallEtaleDerivedSpecializationStalkAbAt B T hT s t).app _) :=
  rfl

/-- The isomorphism `Hᵛ((Rf_* F)_{s̄₁}) ≅ Hᵛ((Rf_* F)_{s̄₂})` of the cohomology of the derived
stalks at two geometric points `s̄₁`, `s̄₂` of `T`, through geometric points `t̄ᵢ` of the strict
henselizations at `s̄ᵢ` with the same image in `T`: specialization from `s̄₁` to `t̄₁`, the
identification of the stalks at `t̄₁` and `t̄₂`, and the inverse of specialization from `s̄₂` to
`t̄₂`. -/
def derivedStalkHomologyTransferIso (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : IsSpecializationAdmissible F) (s₁ s₂ : GeometricPoint T)
    (t₁ : GeometricPoint (strictHenselization B T hT s₁))
    (t₂ : GeometricPoint (strictHenselization B T hT s₂))
    (h : (specializedGeometricPoint B T hT s₁ t₁).hom default =
      (specializedGeometricPoint B T hT s₂ t₂).hom default) (ν : ℤ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} ν).obj
        ((smallEtaleDerivedStalkAb s₁.hom).obj ((smallEtaleDerivedPushforwardAb f).obj
          ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))) ≅
      (DerivedCategory.homologyFunctor Ab.{u + 1} ν).obj
        ((smallEtaleDerivedStalkAb s₂.hom).obj ((smallEtaleDerivedPushforwardAb f).obj
          ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))) :=
  derivedStalkHomologySpecializationIso B hX hT f F hF s₁ t₁ ν ≪≫
    (smallEtaleDerivedStalkAbHomologyIsoOfEq _ _ h ν).app _ ≪≫
    (derivedStalkHomologySpecializationIso B hX hT f F hF s₂ t₂ ν).symm

/-- The isomorphism `AlgebraicGeometry.derivedStalkHomologyTransferIso` is natural in the
admissible sheaf. -/
@[reassoc]
theorem derivedStalkHomologyTransferIso_hom_naturality
    {F G : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    (hF : IsSpecializationAdmissible F) (hG : IsSpecializationAdmissible G) (φ : F ⟶ G)
    (s₁ s₂ : GeometricPoint T)
    (t₁ : GeometricPoint (strictHenselization B T hT s₁))
    (t₂ : GeometricPoint (strictHenselization B T hT s₂))
    (h : (specializedGeometricPoint B T hT s₁ t₁).hom default =
      (specializedGeometricPoint B T hT s₂ t₂).hom default) (ν : ℤ) :
    (derivedStalkHomologyTransferIso B hX hT f F hF s₁ s₂ t₁ t₂ h ν).hom ≫
        (DerivedCategory.homologyFunctor Ab.{u + 1} ν).map
          ((smallEtaleDerivedStalkAb s₂.hom).map ((smallEtaleDerivedPushforwardAb f).map
            ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).map φ))) =
      (DerivedCategory.homologyFunctor Ab.{u + 1} ν).map
          ((smallEtaleDerivedStalkAb s₁.hom).map ((smallEtaleDerivedPushforwardAb f).map
            ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).map φ))) ≫
        (derivedStalkHomologyTransferIso B hX hT f G hG s₁ s₂ t₁ t₂ h ν).hom := by
  let K := (smallEtaleDerivedPushforwardAb f).map
    ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).map φ)
  have p₁ := congrArg (DerivedCategory.homologyFunctor Ab.{u + 1} ν).map
    ((smallEtaleDerivedSpecializationStalkAbAt B T hT s₁ t₁).naturality K)
  have p₂ := congrArg (DerivedCategory.homologyFunctor Ab.{u + 1} ν).map
    ((smallEtaleDerivedSpecializationStalkAbAt B T hT s₂ t₂).naturality K)
  have q := (smallEtaleDerivedStalkAbHomologyIsoOfEq _ _ h ν).hom.naturality K
  simp only [Functor.map_comp] at p₁ p₂
  simp only [Functor.comp_map] at q
  rw [← cancel_mono (derivedStalkHomologySpecializationIso B hX hT f G hG s₂ t₂ ν).hom]
  simp only [derivedStalkHomologyTransferIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [derivedStalkHomologySpecializationIso_hom B hX hT f G hG s₂ t₂ ν, p₂,
    ← derivedStalkHomologySpecializationIso_hom B hX hT f F hF s₂ t₂ ν, Iso.inv_hom_id_assoc]
  simp only [derivedStalkHomologySpecializationIso_hom, Iso.app_hom]
  rw [← q, reassoc_of% p₁]

/-- **Transfer of fibre cohomology** for a smooth proper morphism. For geometric points `s̄₁`,
`s̄₂` of `T` and geometric points `t̄ᵢ` of the strict henselizations at `s̄ᵢ` with the same image
in `T`, and an admissible sheaf `F`, the isomorphism `Hᵛ(X_{s̄₁}, F) ≅ Hᵛ(X_{s̄₂}, F)`. -/
def fibreCohomologyIsoOfSmoothProper (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : IsSpecializationAdmissible F) (s₁ s₂ : GeometricPoint T)
    (t₁ : GeometricPoint (strictHenselization B T hT s₁))
    (t₂ : GeometricPoint (strictHenselization B T hT s₂))
    (h : (specializedGeometricPoint B T hT s₁ t₁).hom default =
      (specializedGeometricPoint B T hT s₂ t₂).hom default) (ν : ℕ) :
    AddCommGrpCat.of
        (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s₁.hom)).obj F) ν) ≅
      AddCommGrpCat.of
        (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s₂.hom)).obj F) ν) :=
  (stalkHigherDirectImageIsoFibreCohomology f s₁.hom F hF.torsion ν).symm ≪≫
    derivedStalkHomologyTransferIso B hX hT f F hF s₁ s₂ t₁ t₂ h ν ≪≫
    stalkHigherDirectImageIsoFibreCohomology f s₂.hom F hF.torsion ν

/-- The transfer isomorphism `AlgebraicGeometry.fibreCohomologyIsoOfSmoothProper` is natural in
the admissible sheaf. -/
@[reassoc]
theorem fibreCohomologyIsoOfSmoothProper_hom_naturality
    {F G : Sheaf X.smallEtaleTopology Ab.{u + 1}}
    (hF : IsSpecializationAdmissible F) (hG : IsSpecializationAdmissible G) (φ : F ⟶ G)
    (s₁ s₂ : GeometricPoint T)
    (t₁ : GeometricPoint (strictHenselization B T hT s₁))
    (t₂ : GeometricPoint (strictHenselization B T hT s₂))
    (h : (specializedGeometricPoint B T hT s₁ t₁).hom default =
      (specializedGeometricPoint B T hT s₂ t₂).hom default) (ν : ℕ) :
    (fibreCohomologyIsoOfSmoothProper B hX hT f F hF s₁ s₂ t₁ t₂ h ν).hom ≫
        (Sheaf.functorH (pullback f s₂.hom).smallEtaleTopology ν).map
          ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s₂.hom)).map φ) =
      (Sheaf.functorH (pullback f s₁.hom).smallEtaleTopology ν).map
          ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s₁.hom)).map φ) ≫
        (fibreCohomologyIsoOfSmoothProper B hX hT f G hG s₁ s₂ t₁ t₂ h ν).hom := by
  have h₁ := stalkHigherDirectImageIsoFibreCohomology_hom_naturality f s₁.hom hF.torsion
    hG.torsion φ ν
  have h₂ := stalkHigherDirectImageIsoFibreCohomology_hom_naturality f s₂.hom hF.torsion
    hG.torsion φ ν
  have m := derivedStalkHomologyTransferIso_hom_naturality B hX hT f hF hG φ s₁ s₂ t₁ t₂ h ν
  simp only [fibreCohomologyIsoOfSmoothProper, Iso.trans_hom, Iso.symm_hom]
  have h₁' : (stalkHigherDirectImageIsoFibreCohomology f s₁.hom F hF.torsion ν).inv ≫
      (DerivedCategory.homologyFunctor Ab.{u + 1} (ν : ℤ)).map
        ((smallEtaleDerivedStalkAb s₁.hom).map ((smallEtaleDerivedPushforwardAb f).map
          ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).map φ))) =
      (Sheaf.functorH (pullback f s₁.hom).smallEtaleTopology ν).map
          ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s₁.hom)).map φ) ≫
        (stalkHigherDirectImageIsoFibreCohomology f s₁.hom G hG.torsion ν).inv := by
    apply (cancel_epi (stalkHigherDirectImageIsoFibreCohomology f s₁.hom F hF.torsion ν).hom).1
    erw [Iso.hom_inv_id_assoc, ← reassoc_of% h₁, Iso.hom_inv_id, Category.comp_id]
  erw [Category.assoc, Category.assoc, ← h₂, reassoc_of% m]
  erw [reassoc_of% h₁']
  exact Category.assoc _ _ _

end Transfer

/-! ### Constant sheaves -/

section Constant

variable {X : Scheme.{u}}

/-- The sections of `n • 𝟙` of an abelian sheaf are multiplication by `n`. -/
theorem sheaf_nsmul_id_hom_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (U : Cᵒᵖ) (y : F.obj.obj U) :
    (n • 𝟙 F).hom.app U y = n • y := by
  have h := congrArg (fun φ => (φ.app U).hom y)
    ((sheafToPresheaf J AddCommGrpCat.{w}).map_nsmul (f := 𝟙 F) (n := n))
  simp only [NatTrans.app_nsmul, AddCommGrpCat.hom_nsmul] at h
  exact h

/-- Multiplication by `n` on the constant sheaf on an abelian group killed by `n` is zero. -/
theorem constantSheaf_nsmul_id_eq_zero (M : AddCommGrpCat.{u + 1}) (n : ℕ)
    (hM : ∀ x : M, n • x = 0) :
    n • 𝟙 ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) = 0 := by
  have h0 : n • 𝟙 M = 0 := by
    ext x
    simpa using hM x
  rw [← (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_id M,
    ← Functor.map_nsmul, h0, Functor.map_zero]

/-- The constant sheaf on an abelian group killed by `n > 0` is a torsion sheaf. -/
theorem torsionSheafProperty_constantSheaf_of_nsmul_eq_zero (M : AddCommGrpCat.{u + 1}) (n : ℕ)
    (hn : 0 < n)
    (hM : ∀ x : M, n • x = 0) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) := by
  intro U x
  refine ⟨⊤, X.smallEtaleTopology.top_mem U, fun V g _ => ⟨n, hn, ?_⟩⟩
  rw [← sheaf_nsmul_id_hom_app_apply, constantSheaf_nsmul_id_eq_zero M n hM]
  rfl

theorem isLocallyConstant_constantSheaf (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) := by
  have := isFiniteLocallyConstant_constantSheaf_smallEtale X M
  infer_instance

/-- An integer invertible on `X` is invertible in the residue field of every geometric point of
`X`. -/
theorem isUnit_natCast_residueField_of_isUnit (x : GeometricPoint X) {n : ℕ}
    (hn : IsUnit (n : Γ(X, ⊤))) : IsUnit (n : x.residueField) := by
  have h₁ : IsUnit (n : Γ(x.source, ⊤)) := by
    simpa using hn.map x.hom.appTop.hom
  simpa using h₁.map (Scheme.ΓSpecIso (CommRingCat.of x.residueField)).hom.hom

/-- The stalks of the constant sheaf on an abelian group killed by an integer `n > 0` invertible
on `X` are killed by `n`, which is prime to the residue characteristics. -/
theorem constantSheaf_stalk_torsion (M : AddCommGrpCat.{u + 1}) (n : ℕ) (hn : 0 < n)
    (hM : ∀ x : M, n • x = 0) (hnX : IsUnit (n : Γ(X, ⊤))) (x : GeometricPoint X)
    (a : (smallEtaleStalkAb x.hom).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) :
    ∃ k : ℕ, 0 < k ∧
      (ringChar x.residueField = 0 ∨ Nat.Coprime k (ringChar x.residueField)) ∧ k • a = 0 := by
  refine ⟨n, hn, SmoothBaseChange.ringChar_eq_zero_or_coprime_of_isUnit
    (isUnit_natCast_residueField_of_isUnit x hnX), ?_⟩
  let ε := ((Sites.constantSheafFiberNatIso (D := AddCommGrpCat.{u + 1})
    (Scheme.pointSmallEtale x.hom)).app M).addCommGroupIsoToAddEquiv
  apply ε.injective
  rw [map_nsmul, map_zero]
  exact hM _

/-- The constant sheaf on a finite abelian group killed by an integer `n > 0` invertible on `X`
satisfies the hypotheses of Stacks 0GKD. -/
theorem isSpecializationAdmissible_constantSheaf (M : AddCommGrpCat.{u + 1}) [Finite M] (n : ℕ)
    (hn : 0 < n) (hM : ∀ x : M, n • x = 0) (hnX : IsUnit (n : Γ(X, ⊤))) :
    IsSpecializationAdmissible ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)
    where
  isLocallyConstant := isLocallyConstant_constantSheaf M
  torsion := torsionSheafProperty_constantSheaf_of_nsmul_eq_zero M n hn hM
  stalk_torsion := constantSheaf_stalk_torsion M n hn hM hnX

/-- The constant sheaf on `X` on a finite abelian group killed by an integer `n > 0` invertible
on the base `T` of a morphism `f : X ⟶ T` satisfies the hypotheses of Stacks 0GKD. -/
theorem isSpecializationAdmissible_constantSheaf_of_base {T : Scheme.{u}} (f : X ⟶ T)
    (M : AddCommGrpCat.{u + 1}) [Finite M]
    (hM : ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T, ⊤)) ∧ ∀ x : M, n • x = 0) :
    IsSpecializationAdmissible ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) :=
  let ⟨n, hn, hnT, hnM⟩ := hM
  isSpecializationAdmissible_constantSheaf M n hn hnM (by simpa using hnT.map f.appTop.hom)

end Constant

/-! ### The cohomology of the geometric fibres with constant coefficients -/

section ConstantTransfer

variable (B : BigEtaleSite.{u}) {X T : Scheme.{u}} (hX : B.Contains X) (hT : B.Contains T)
  (f : X ⟶ T) [Smooth f] [IsProper f] [IrreducibleSpace T]

/-- The cohomology of the inverse image of the constant sheaf on `M` to a geometric fibre is the
cohomology of the constant sheaf on `M` there. -/
def fibreInverseImageConstantCohomologyIso (s : GeometricPoint T) (M : AddCommGrpCat.{u + 1})
    (ν : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s.hom)).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) ν) ≅
      AddCommGrpCat.of (Sheaf.H.{u + 1}
        ((constantSheaf (pullback f s.hom).smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) ν) :=
  (Sheaf.functorH (pullback f s.hom).smallEtaleTopology ν).mapIso
    ((etaleAbelianInverseImageConstantIso.{u, 0} (pullback.fst f s.hom)).app M)

omit [Smooth f] [IsProper f] [IrreducibleSpace T] in
/-- The isomorphism `AlgebraicGeometry.fibreInverseImageConstantCohomologyIso` is natural in the
coefficient group. -/
@[reassoc]
theorem fibreInverseImageConstantCohomologyIso_hom_naturality (s : GeometricPoint T)
    {M N : AddCommGrpCat.{u + 1}} (g : M ⟶ N) (ν : ℕ) :
    (fibreInverseImageConstantCohomologyIso f s M ν).hom ≫
        (Sheaf.functorH (pullback f s.hom).smallEtaleTopology ν).map
          ((constantSheaf (pullback f s.hom).smallEtaleTopology AddCommGrpCat.{u + 1}).map g) =
      (Sheaf.functorH (pullback f s.hom).smallEtaleTopology ν).map
          ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s.hom)).map
            ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g)) ≫
        (fibreInverseImageConstantCohomologyIso f s N ν).hom := by
  have h := congrArg (Sheaf.functorH (pullback f s.hom).smallEtaleTopology ν).map
    ((etaleAbelianInverseImageConstantIso.{u, 0} (pullback.fst f s.hom)).hom.naturality g)
  simp only [Functor.map_comp, Functor.comp_map] at h
  exact h.symm

/-- **The cohomology of the geometric fibres with constant coefficients.** For `f : X ⟶ T`
smooth and proper with `T` irreducible, a finite abelian group `M` killed by some integer `n > 0`
invertible on `T`, and geometric points `s̄₁`, `s̄₂` of `T`: `Hᵛ(X_{s̄₁}, M) ≅ Hᵛ(X_{s̄₂}, M)`. -/
def fibreConstantCohomologyIso (M : AddCommGrpCat.{u + 1}) [Finite M]
    (hM : ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T, ⊤)) ∧ ∀ x : M, n • x = 0)
    (s₁ s₂ : GeometricPoint T) (ν : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u + 1}
        ((constantSheaf (pullback f s₁.hom).smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) ν) ≅
      AddCommGrpCat.of (Sheaf.H.{u + 1}
        ((constantSheaf (pullback f s₂.hom).smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) ν) :=
  (fibreInverseImageConstantCohomologyIso f s₁ M ν).symm ≪≫
    fibreCohomologyIsoOfSmoothProper B hX hT f _
      (isSpecializationAdmissible_constantSheaf_of_base f M hM) s₁ s₂
      (genericGeometricPointOfStrictHenselization B T hT s₁)
      (genericGeometricPointOfStrictHenselization B T hT s₂)
      ((genericGeometricPointOfStrictHenselization_liesOver B T hT s₁).trans
        (genericGeometricPointOfStrictHenselization_liesOver B T hT s₂).symm) ν ≪≫
    fibreInverseImageConstantCohomologyIso f s₂ M ν

/-- The isomorphism `AlgebraicGeometry.fibreConstantCohomologyIso` is natural in the coefficient
group. -/
@[reassoc]
theorem fibreConstantCohomologyIso_hom_naturality {M N : AddCommGrpCat.{u + 1}} [Finite M]
    [Finite N] (g : M ⟶ N) (hM : ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T, ⊤)) ∧ ∀ x : M, n • x = 0)
    (hN : ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T, ⊤)) ∧ ∀ x : N, n • x = 0)
    (s₁ s₂ : GeometricPoint T) (ν : ℕ) :
    (fibreConstantCohomologyIso B hX hT f M hM s₁ s₂ ν).hom ≫
        (Sheaf.functorH (pullback f s₂.hom).smallEtaleTopology ν).map
          ((constantSheaf (pullback f s₂.hom).smallEtaleTopology AddCommGrpCat.{u + 1}).map g) =
      (Sheaf.functorH (pullback f s₁.hom).smallEtaleTopology ν).map
          ((constantSheaf (pullback f s₁.hom).smallEtaleTopology AddCommGrpCat.{u + 1}).map g) ≫
        (fibreConstantCohomologyIso B hX hT f N hN s₁ s₂ ν).hom := by
  have h₁ := fibreInverseImageConstantCohomologyIso_hom_naturality f s₁ g ν
  have h₂ := fibreInverseImageConstantCohomologyIso_hom_naturality f s₂ g ν
  have m := fibreCohomologyIsoOfSmoothProper_hom_naturality B hX hT f
    (isSpecializationAdmissible_constantSheaf_of_base f M hM)
    (isSpecializationAdmissible_constantSheaf_of_base f N hN)
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g) s₁ s₂
    (genericGeometricPointOfStrictHenselization B T hT s₁)
    (genericGeometricPointOfStrictHenselization B T hT s₂)
    ((genericGeometricPointOfStrictHenselization_liesOver B T hT s₁).trans
      (genericGeometricPointOfStrictHenselization_liesOver B T hT s₂).symm) ν
  have h₁' : (fibreInverseImageConstantCohomologyIso f s₁ M ν).inv ≫
      (Sheaf.functorH (pullback f s₁.hom).smallEtaleTopology ν).map
          ((etaleAbelianInverseImage.{u, 0} (pullback.fst f s₁.hom)).map
            ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g)) =
      (Sheaf.functorH (pullback f s₁.hom).smallEtaleTopology ν).map
          ((constantSheaf (pullback f s₁.hom).smallEtaleTopology AddCommGrpCat.{u + 1}).map g) ≫
        (fibreInverseImageConstantCohomologyIso f s₁ N ν).inv := by
    apply (cancel_epi (fibreInverseImageConstantCohomologyIso f s₁ M ν).hom).1
    erw [Iso.hom_inv_id_assoc, ← Category.assoc, h₁, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact comp_trans_trans_hom_eq _ _ _ _ _ _ _ _ _ _ h₁' m h₂

end ConstantTransfer

/-! ### The universe-`0` statement on `etaleCohomologyConstant` -/

section EtaleCohomologyConstant

variable {X T : Scheme.{0}} (f : X ⟶ T) [Smooth f] [IsProper f] [IrreducibleSpace T]

/-- A big étale site containing both `X` and `T`. -/
def bigEtaleSiteOfPair (X T : Scheme.{u}) : BigEtaleSite.{u} :=
  (BigEtaleSite.exists_contains_of_small ({X, T} : Set Scheme.{u})).choose

theorem bigEtaleSiteOfPair_contains_left (X T : Scheme.{u}) : (bigEtaleSiteOfPair X T).Contains X :=
  (BigEtaleSite.exists_contains_of_small ({X, T} : Set Scheme.{u})).choose_spec X (by simp)

theorem bigEtaleSiteOfPair_contains_right (X T : Scheme.{u}) :
    (bigEtaleSiteOfPair X T).Contains T :=
  (BigEtaleSite.exists_contains_of_small ({X, T} : Set Scheme.{u})).choose_spec T (by simp)

omit [IrreducibleSpace T] in
theorem exists_nsmul_eq_zero_uliftFunctor_obj {M : AddCommGrpCat.{0}}
    (hM : ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T, ⊤)) ∧ ∀ x : M, n • x = 0) :
    ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T, ⊤)) ∧
      ∀ x : AddCommGrpCat.uliftFunctor.{1, 0}.obj M, n • x = 0 := by
  obtain ⟨n, hn, hnT, hnM⟩ := hM
  exact ⟨n, hn, hnT, fun x => ULift.ext _ _ (hnM x.down)⟩

/-- **The étale cohomology of the geometric fibres with constant coefficients**, in universe `0`.
For `f : X ⟶ T` smooth and proper with `T` irreducible, a finite abelian group `M` killed by some
integer `n > 0` invertible on `T`, and geometric points `s̄₁`, `s̄₂` of `T`:
`Hᵛ_et(X_{s̄₁}, M) ≃+ Hᵛ_et(X_{s̄₂}, M)`. -/
def fibreEtaleCohomologyConstantAddEquiv (M : AddCommGrpCat.{0}) [Finite M]
    (hM : ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T, ⊤)) ∧ ∀ x : M, n • x = 0)
    (s₁ s₂ : GeometricPoint T) (ν : ℕ) :
    Scheme.etaleCohomologyConstant (pullback f s₁.hom) M ν ≃+
      Scheme.etaleCohomologyConstant (pullback f s₂.hom) M ν :=
  haveI : Finite (AddCommGrpCat.uliftFunctor.{1, 0}.obj M) :=
    inferInstanceAs (Finite (ULift M))
  (fibreConstantCohomologyIso (bigEtaleSiteOfPair X T) (bigEtaleSiteOfPair_contains_left X T)
    (bigEtaleSiteOfPair_contains_right X T) f (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)
    (exists_nsmul_eq_zero_uliftFunctor_obj hM) s₁ s₂ ν).addCommGroupIsoToAddEquiv

/-- The isomorphism `AlgebraicGeometry.fibreEtaleCohomologyConstantAddEquiv` is natural in the
coefficient group. -/
theorem fibreEtaleCohomologyConstantAddEquiv_naturality {M N : AddCommGrpCat.{0}} [Finite M]
    [Finite N] (g : M ⟶ N) (hM : ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T, ⊤)) ∧ ∀ x : M, n • x = 0)
    (hN : ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(T, ⊤)) ∧ ∀ x : N, n • x = 0)
    (s₁ s₂ : GeometricPoint T) (ν : ℕ)
    (x : Scheme.etaleCohomologyConstant (pullback f s₁.hom) M ν) :
    fibreEtaleCohomologyConstantAddEquiv f N hN s₁ s₂ ν
        (Scheme.etaleCohomologyConstantMap (pullback f s₁.hom) g ν x) =
      Scheme.etaleCohomologyConstantMap (pullback f s₂.hom) g ν
        (fibreEtaleCohomologyConstantAddEquiv f M hM s₁ s₂ ν x) := by
  have : Finite (AddCommGrpCat.uliftFunctor.{1, 0}.obj M) :=
    inferInstanceAs (Finite (ULift M))
  have : Finite (AddCommGrpCat.uliftFunctor.{1, 0}.obj N) :=
    inferInstanceAs (Finite (ULift N))
  have h := ConcreteCategory.congr_hom
    (fibreConstantCohomologyIso_hom_naturality (bigEtaleSiteOfPair X T)
      (bigEtaleSiteOfPair_contains_left X T) (bigEtaleSiteOfPair_contains_right X T) f
      (AddCommGrpCat.uliftFunctor.{1, 0}.map g)
      (exists_nsmul_eq_zero_uliftFunctor_obj hM)
      (exists_nsmul_eq_zero_uliftFunctor_obj hN) s₁ s₂ ν) x
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h.symm

end EtaleCohomologyConstant

/-! ### Coefficients `ℤ/ℓ^{m+1}` over the spectrum of a domain -/

section ZModCoefficients

variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [Smooth f] [IsProper f] (ℓ : ℕ) (hℓ : IsUnit (ℓ : R))

include hℓ in
theorem ne_zero_of_isUnit_natCast_of_isDomain : ℓ ≠ 0 := by
  rintro rfl
  simp at hℓ

include hℓ in
/-- `ℤ/ℓ^{m+1}` is killed by `ℓ^{m+1}`, an integer invertible on `Spec R`. -/
theorem exists_nsmul_eq_zero_zmod_pow (m : ℕ) :
    ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(Spec (.of R), ⊤)) ∧
      ∀ x : AddCommGrpCat.of (ZMod (ℓ ^ (m + 1))), n • x = 0 := by
  refine ⟨ℓ ^ (m + 1),
    pow_pos (Nat.pos_of_ne_zero (ne_zero_of_isUnit_natCast_of_isDomain ℓ hℓ)) _, ?_, ?_⟩
  · have := (hℓ.pow (m + 1)).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    simpa using this
  · intro x
    rw [nsmul_eq_mul]
    simp

/-- The reduction `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`. -/
def zmodPowSuccReduction (m : ℕ) :
    AddCommGrpCat.of (ZMod (ℓ ^ (m + 1 + 1))) ⟶ AddCommGrpCat.of (ZMod (ℓ ^ (m + 1))) :=
  AddCommGrpCat.ofHom
    (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (m + 1))) (ZMod (ℓ ^ (m + 1)))).toAddMonoidHom

/-- **Smooth proper specialization identifies the cohomology of any two geometric fibres**, with
coefficients `ℤ/ℓ^{m+1}`, over the spectrum of a domain `R` in which `ℓ` is invertible:
`Hᵛ_et(X_{s̄₁}, ℤ/ℓ^{m+1}) ≃+ Hᵛ_et(X_{s̄₂}, ℤ/ℓ^{m+1})`. -/
def fibreEtaleCohomologyZModAddEquiv (s₁ s₂ : GeometricPoint (Spec (.of R))) (m ν : ℕ) :
    Scheme.etaleCohomologyConstant (pullback f s₁.hom) (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) ν ≃+
      Scheme.etaleCohomologyConstant (pullback f s₂.hom)
        (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) ν :=
  haveI : NeZero (ℓ ^ (m + 1)) := ⟨pow_ne_zero _ (ne_zero_of_isUnit_natCast_of_isDomain ℓ hℓ)⟩
  haveI : Finite (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) :=
    inferInstanceAs (Finite (ZMod (ℓ ^ (m + 1))))
  fibreEtaleCohomologyConstantAddEquiv f _ (exists_nsmul_eq_zero_zmod_pow ℓ hℓ m) s₁ s₂ ν

/-- The isomorphisms `AlgebraicGeometry.fibreEtaleCohomologyZModAddEquiv` are compatible with the
reductions `ℤ/ℓ^{m+2} → ℤ/ℓ^{m+1}`. -/
theorem fibreEtaleCohomologyZModAddEquiv_transition (s₁ s₂ : GeometricPoint (Spec (.of R)))
    (m ν : ℕ) (x : Scheme.etaleCohomologyConstant (pullback f s₁.hom)
      (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1 + 1)))) ν) :
    fibreEtaleCohomologyZModAddEquiv f ℓ hℓ s₁ s₂ m ν
        (Scheme.etaleCohomologyConstantMap (pullback f s₁.hom) (zmodPowSuccReduction ℓ m) ν x) =
      Scheme.etaleCohomologyConstantMap (pullback f s₂.hom) (zmodPowSuccReduction ℓ m) ν
        (fibreEtaleCohomologyZModAddEquiv f ℓ hℓ s₁ s₂ (m + 1) ν x) := by
  have : NeZero (ℓ ^ (m + 1)) := ⟨pow_ne_zero _ (ne_zero_of_isUnit_natCast_of_isDomain ℓ hℓ)⟩
  have : NeZero (ℓ ^ (m + 1 + 1)) := ⟨pow_ne_zero _ (ne_zero_of_isUnit_natCast_of_isDomain ℓ hℓ)⟩
  have : Finite (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1)))) :=
    inferInstanceAs (Finite (ZMod (ℓ ^ (m + 1))))
  have : Finite (AddCommGrpCat.of (ZMod (ℓ ^ (m + 1 + 1)))) :=
    inferInstanceAs (Finite (ZMod (ℓ ^ (m + 1 + 1))))
  exact fibreEtaleCohomologyConstantAddEquiv_naturality f (zmodPowSuccReduction ℓ m)
    (exists_nsmul_eq_zero_zmod_pow ℓ hℓ (m + 1)) (exists_nsmul_eq_zero_zmod_pow ℓ hℓ m) s₁ s₂ ν x

end ZModCoefficients

end AlgebraicGeometry
