module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Mathlib.RingTheory.Smooth.Fiber
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# Local-étale extensions of local rings spread out to étale neighbourhoods

Let `X` be a locally noetherian scheme, `x₀ ∈ X` and `A = 𝒪_{X,x₀}`. Every local-étale
homomorphism `A → B` is realized by an étale neighbourhood: there are an affine object
`U → X` of the étale category `Et(X)`, a point `u₀ ∈ U` over `x₀` and an isomorphism of
`A`-algebras `𝒪_{U,u₀} ≅ B`.

The proof writes `B` as the localization of an étale algebra. Choose an affine open
`V = Spec R ∋ x₀`, so that `A = R_q`. Since `B` is essentially of finite type over `R`, it is the
localization of a finite type `R`-subalgebra `C₀ ⊆ B` at the prime `Q₀` under the maximal ideal
of `B`. Flatness and unramifiedness of `R → B` make `C₀` étale over `R` at `Q₀`, so some
principal localization `C = (C₀)_g`, `g ∉ Q₀`, is étale over `R` (openness of the étale locus).
Then `U = Spec C → Spec R ⊆ X` is étale, and its local ring at the prime `Q₀ C` is `B`.

## Main results

* `Algebra.exists_etale_isLocalization_atPrime_of_isEtaleLocalHom`: a local-étale extension `B`
  of `R_q`, for `R` noetherian, is the localization of an étale `R`-algebra at a prime over `q`.
* `AlgebraicGeometry.exists_etale_stalk_ringEquiv_of_isEtaleLocalHom`: the statement for
  schemes.

## Implementation notes

The étale category is `AlgebraicGeometry.SmallNoetherianSeparatedEtale E X hX` for a big étale
site `E` containing `X`; the neighbourhood `U` lies in `E` because a scheme locally of finite
type over a scheme of `E` with a single affine chart does. The scheme `X` is only assumed
locally noetherian. The `A`-algebra structure on `𝒪_{U,u₀}` is the stalk map of `U → X` at
`u₀`, composed with the identification of stalks along the equality of points
`(U → X)(u₀) = x₀`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl], I.2
-/

@[expose] public section

universe u

open IsLocalRing

namespace Algebra

/-- **Spreading out a local-étale extension of a localization.** Let `R` be a noetherian ring,
`q` a prime of `R`, `A = R_q`, and `A → B` a local-étale homomorphism. Then `B` is the
localization `C_Q` of an étale `R`-algebra `C` at a prime `Q` lying over `q`, compatibly with
the `R`-algebra structures. -/
theorem exists_etale_isLocalization_atPrime_of_isEtaleLocalHom
    {R : Type u} [CommRing R] [IsNoetherianRing R] (q : Ideal R) [q.IsPrime]
    (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [IsLocalization.AtPrime A q]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalRing A] [IsNoetherianRing A]
    [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
    (h : (algebraMap A B).IsEtaleLocalHom) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.Etale R C)
      (_ : Algebra C B) (_ : IsScalarTower R C B) (Q : Ideal C) (_ : Q.IsPrime),
      Q.comap (algebraMap R C) = q ∧ IsLocalization.AtPrime B Q := by
  obtain ⟨hflat, hunr, hfin⟩ := h
  have : Algebra.EssFiniteType R A := .of_isLocalization A q.primeCompl
  have : Algebra.EssFiniteType A B := RingHom.essFiniteType_algebraMap.mp hfin
  have : Algebra.EssFiniteType R B := .comp R A B
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  have : Module.Flat R A := IsLocalization.flat A q.primeCompl
  have : Module.Flat R B := .trans R A B
  have : Algebra.FormallyUnramified A B := RingHom.formallyUnramified_algebraMap.mp hunr
  have : Algebra.FormallyUnramified R A := .of_isLocalization q.primeCompl
  have : Algebra.FormallyUnramified R B := .comp R A B
  set C₀ := EssFiniteType.subalgebra R B
  set Q₀ : Ideal C₀ := (maximalIdeal B).comap (algebraMap C₀ B)
  have : IsLocalization Q₀.primeCompl B := by
    refine IsLocalization.of_le (EssFiniteType.submonoid R B) _ ?_ ?_
    · intro c hc
      exact fun hmem => (IsLocalRing.mem_maximalIdeal _).mp hmem hc
    · intro c hc
      exact (IsLocalRing.notMem_maximalIdeal).mp hc
  let eB : Localization.AtPrime Q₀ ≃ₐ[R] B :=
    (IsLocalization.algEquiv Q₀.primeCompl (Localization.AtPrime Q₀) B).restrictScalars R
  have : Algebra.IsUnramifiedAt R Q₀ := FormallyUnramified.of_equiv eB.symm
  have : Module.Flat R (Localization.AtPrime Q₀) := Module.Flat.of_linearEquiv eB.toLinearEquiv
  have : Algebra.FinitePresentation R C₀ := FinitePresentation.of_finiteType.mp inferInstance
  have hQ₀ : Q₀.comap (algebraMap R C₀) = q := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R A B,
      ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap,
      ← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal A q]
  have : Q₀.LiesOver q := ⟨hQ₀.symm⟩
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime Q₀) :=
    Localization.AtPrime.algebraOfLiesOver q Q₀
  have : Localization.AtPrime.IsLiesOverAlgebra q Q₀ := inferInstance
  have : Module.Flat (Localization.AtPrime q) (Localization.AtPrime Q₀) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime q) q.primeCompl
      (Localization.AtPrime Q₀)).2 inferInstance
  have : Algebra.IsEtaleAt R Q₀ := IsEtaleAt.of_flat_of_map_eq_maximalIdeal q Q₀
    ((Algebra.isUnramifiedAt_iff_map_eq R q Q₀).mp inferInstance).2
  obtain ⟨g, hg, hge⟩ := exists_etale_of_isEtaleAt (R := R) Q₀
  have hle : Submonoid.powers g ≤ Q₀.primeCompl := Submonoid.powers_le.mpr hg
  let C := Localization.Away g
  let : Algebra C B :=
    IsLocalization.localizationAlgebraOfSubmonoidLe C B (Submonoid.powers g) Q₀.primeCompl hle
  have : IsScalarTower C₀ C B :=
    IsLocalization.localization_isScalarTower_of_submonoid_le C B _ _ hle
  have : IsScalarTower R C B := IsScalarTower.to₁₃₄ R C₀ C B
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid C Q₀.primeCompl) B :=
    IsLocalization.isLocalization_of_submonoid_le C B _ _ hle
  set Q : Ideal C := (maximalIdeal B).comap (algebraMap C B)
  refine ⟨C, inferInstance, inferInstance, hge, inferInstance, inferInstance, Q, inferInstance,
    ?_, ?_⟩
  · rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R A B,
      ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap, ← Ideal.under_def,
      IsLocalization.AtPrime.under_maximalIdeal A q]
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid C Q₀.primeCompl) _ ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    change algebraMap C B (algebraMap C₀ C c) ∉ maximalIdeal B
    rw [← IsScalarTower.algebraMap_apply]
    exact hc
  · intro c hc
    exact (IsLocalRing.notMem_maximalIdeal).mp hc

end Algebra

namespace AlgebraicGeometry

open CategoryTheory

/-- **A local-étale extension of a local ring of a scheme is a local ring of an étale
neighbourhood.** Let `X` be a locally noetherian scheme, `x₀ : X`, and `A → B` a local-étale
homomorphism (`RingHom.IsEtaleLocalHom`) out of the local ring `A = 𝒪_{X,x₀}`. Then there are an
object `U → X` of the étale category `Et(X)` (here relative to a big étale site `E` containing
`X`) whose scheme is affine, a point `u₀` of `U` over `x₀`, and an isomorphism `𝒪_{U,u₀} ≅ B` of
`A`-algebras, where `𝒪_{U,u₀}` is an `A`-algebra through the stalk map of `U → X` at `u₀`. -/
@[weil "lem_fk102_local_etale_spreads_out"]
theorem exists_etale_stalk_ringEquiv_of_isEtaleLocalHom {E : BigEtaleSite.{u}} {X : Scheme.{u}}
    (hX : E.Contains X) [IsLocallyNoetherian X] (x₀ : X) (B : Type u) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [Algebra (X.presheaf.stalk x₀) B]
    [IsLocalHom (algebraMap (X.presheaf.stalk x₀) B)]
    (h : (algebraMap (X.presheaf.stalk x₀) B).IsEtaleLocalHom) :
    ∃ (U : SmallNoetherianSeparatedEtale E X hX)
      (u₀ : (SmallNoetherianSeparatedEtale.toScheme E X hX).obj U)
      (hu : SmallNoetherianSeparatedEtale.structureMorphism U u₀ = x₀)
      (e : ((SmallNoetherianSeparatedEtale.toScheme E X hX).obj U).presheaf.stalk u₀ ≃+* B),
      IsAffine ((SmallNoetherianSeparatedEtale.toScheme E X hX).obj U) ∧
        e.toRingHom.comp ((X.presheaf.stalkCongr (.of_eq hu.symm)).hom ≫
          (SmallNoetherianSeparatedEtale.structureMorphism U).stalkMap u₀).hom =
          algebraMap (X.presheaf.stalk x₀) B := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  replace hV : IsAffineOpen V := hV
  set R := Γ(X, V)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  set x : V := ⟨x₀, hxV⟩
  set q := (hV.primeIdealOf x).asIdeal
  let : Algebra R (X.presheaf.stalk x₀) := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have : IsLocalization.AtPrime (X.presheaf.stalk x₀) q := hV.isLocalization_stalk x
  let : Algebra R B := ((algebraMap (X.presheaf.stalk x₀) B).comp (algebraMap R _)).toAlgebra
  have : IsScalarTower R (X.presheaf.stalk x₀) B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsLocalRing (X.presheaf.stalk x₀) := inferInstance
  obtain ⟨C, _, _, _, _, _, Q, _, hQ, _⟩ :=
    Algebra.exists_etale_isLocalization_atPrime_of_isEtaleLocalHom q _ B h
  obtain ⟨u₀, rfl⟩ : ∃ u₀ : Spec (.of C), u₀.asIdeal = Q := ⟨⟨Q, inferInstance⟩, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ CommRingCat.of C,
      φ = CommRingCat.ofHom (algebraMap R C) := ⟨_, rfl⟩
  have : Etale (Spec.map φ) := by
    subst hφ
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  have hU : E.Contains (Spec (.of C)) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_affineCover E.aleph0_lt_cutoff
      E.cutoff_isStrongPrelimit (Spec.map φ ≫ hV.fromSpec)
      (fun _ : PUnit => ⟨⊤, isAffineOpen_top (Spec (.of C))⟩) (by simp)
      ((Cardinal.mk_le_aleph0.trans (Scheme.aleph0_le_size _)).trans
        (Cardinal.self_le_power _ Cardinal.one_le_aleph0)) hX
  set y : Spec R := PrimeSpectrum.comap φ.hom u₀ with hy_def
  have hy : y = hV.primeIdealOf x := PrimeSpectrum.ext (by subst hφ; exact hQ)
  have hy₀ : hV.fromSpec y = x₀ := by rw [hy, hV.fromSpec_primeIdealOf x]
  have hu : (Spec.map φ ≫ hV.fromSpec) u₀ = x₀ := hy₀
  have key : X.presheaf.germ V x₀ hxV ≫ (X.presheaf.stalkCongr (.of_eq hy₀.symm)).hom ≫
      hV.fromSpec.stalkMap y ≫ (Spec.stalkIso R y).hom =
      CommRingCat.ofHom (algebraMap R (Localization.AtPrime y.asIdeal)) := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rw [Scheme.Hom.germ_stalkMap_assoc, hV.fromSpec_app_self]
    simp only [Category.assoc]
    erw [TopCat.Presheaf.germ_res_assoc, Spec.germ_stalkMapIso_hom]
    exact Iso.inv_hom_id_assoc _ _
  have e2 : (Spec.map φ).stalkMap u₀ ≫ (Spec.stalkIso (.of C) u₀).hom =
      (Spec.stalkIso R y).hom ≫
        CommRingCat.ofHom (Localization.localRingHom y.asIdeal u₀.asIdeal φ.hom rfl) := by
    rw [← Scheme.localRingHom_comp_stalkIso φ u₀]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have key2 : X.presheaf.germ V x₀ hxV ≫ (X.presheaf.stalkCongr (.of_eq hu.symm)).hom ≫
      (Spec.map φ ≫ hV.fromSpec).stalkMap u₀ ≫ (Spec.stalkIso (.of C) u₀).hom =
      φ ≫ CommRingCat.ofHom (algebraMap C (Localization.AtPrime u₀.asIdeal)) := by
    rw [Scheme.Hom.stalkMap_comp]
    erw [Category.assoc, e2]
    erw [reassoc_of% key]
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact Localization.localRingHom_to_map _ _ _ _ r
  let eB := IsLocalization.algEquiv u₀.asIdeal.primeCompl (Localization.AtPrime u₀.asIdeal) B
  let e : (Spec (.of C)).presheaf.stalk u₀ ≃+* B :=
    (Spec.stalkIso (.of C) u₀).commRingCatIsoToRingEquiv.trans eB.toRingEquiv
  refine ⟨SmallNoetherianSeparatedEtale.mk (Spec (.of C)) hU (Spec.map φ ≫ hV.fromSpec), u₀, hu,
    e, inferInstanceAs (IsAffine (Spec (.of C))), ?_⟩
  apply IsLocalization.ringHom_ext q.primeCompl
  rw [← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R C B]
  ext r
  have hr := congr(($key2).hom r)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, hφ, CommRingCat.hom_ofHom] at hr
  simp only [RingHom.comp_apply]
  change eB ((Spec.stalkIso (CommRingCat.of C) u₀).hom ((Spec.map φ ≫ hV.fromSpec).stalkMap u₀
      ((X.presheaf.stalkCongr (.of_eq hu.symm)).hom (X.presheaf.germ V x₀ hxV r)))) = _
  rw [hr]
  exact eB.commutes _

end AlgebraicGeometry
