module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Limits.RationalFunctionsSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupSmoothCurveVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleComparison

/-!
# The units of the sheaf of rational functions on a smooth curve are acyclic

Let `X` be a smooth curve over an algebraically closed field `k`: a separated scheme of finite
type over `k`, smooth of relative dimension one, not necessarily connected. Let
`j_X : η_X ⟶ X` be its scheme of generic points, the disjoint union of the spectra of the
residue fields at the generic points of the irreducible components of `X`, and let
`𝓡_X^* = j_{X*} 𝐆_{m,η_X}` be the sheaf of units of rational functions. Then

`H^p(X, 𝓡_X^*) = 0` for every `p > 0`.

## Main results

* `subsingleton_sheafH_genericPointsDirectImage_multiplicativeSheaf_smoothCurve`:
  the vanishing on the small étale site `X.Etale`.
* `subsingleton_sheafH_genericPointsDirectImage_multiplicativeSheaf_smoothCurve_smallEtale`:
  the same vanishing on the small étale site `SmallEtale B X hX` of a big étale site.
* `AlgebraicGeometry.Scheme.etaleRestrictionGenericPointsDirectImageIso`: for `ι : C ⟶ X` étale
  with `C` integral, the restriction of `j_{X*} 𝐆_m` to `C` is `j_{C*} 𝐆_m`, with
  `j_C : Spec k(C) ⟶ C` the inclusion of the generic point.

## Implementation notes

The source computes `H^p(X, j_{X*} 𝐆_m) ≅ H^p(η_X, 𝐆_m) ≅ ∏_c H^p(k(η_c), 𝐆_m)` and applies
Tsen's theorem to each factor. Here `X` is first cut into its finitely many connected
components `X_c`, which are open and closed; each is an integral smooth curve, being connected
and smooth over a field, and has dimension one, being smooth of relative dimension one. The
cohomology of `X` is the product of the cohomologies of the `X_c` of the restricted sheaves
(`Stacks.EtaleCohomology.bijective_etaleCohomologyPullback_pi`), the restriction of
`j_{X*} 𝐆_m` to `X_c` is `j_{X_c *} 𝐆_m` because
`X_c ×_X η_X` is the generic point of `X_c`, and on an integral smooth curve the vanishing is
[Stacks, Tag 03RK], which rests on the same Leray and Tsen arguments as the source.

The sheaf `𝓡_X^*` is written as the direct image `j_{X*} 𝐆_{m,η_X}` along the morphism of
small étale sites, whose sections over an étale `U ⟶ X` are `Γ(U ×_X η_X, 𝒪)ˣ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5, proof of
  Proposition 5.2.
* [Stacks Project, Tag 03RK](https://stacks.math.columbia.edu/tag/03RK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- The functor `Schemeᵒᵖ ⥤ Ab` sending `W` to `Γ(W, 𝒪_W)ˣ`, through which `𝐆_m` is defined. -/
abbrev globalUnitsAddFunctor : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    commGroupAddCommGroupEquivalence.functor ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

variable {X C : Scheme.{u}} (ι : C ⟶ X)

section
variable {E E' : Scheme.{u}} (j : E ⟶ X) (j' : E' ⟶ C) (e : E' ≅ pullback ι j)
  (he : e.hom ≫ pullback.fst ι j = j')

include he in
/-- Base change of `j'` along `f : Y ⟶ C` is base change of `j` along `f ≫ ι`, when `j'` is
the base change of `j` along `ι`. -/
def pullbackCompIsoOfIsoPullback {Y : Scheme.{u}} (f : Y ⟶ C) :
    pullback f j' ≅ pullback (f ≫ ι) j :=
  asIso (pullback.map f j' f (pullback.fst ι j) (𝟙 _) e.hom (𝟙 _) (by simp) (by simp [he])) ≪≫
    pullbackRightPullbackFstIso ι j f

@[reassoc (attr := simp)]
theorem pullbackCompIsoOfIsoPullback_hom_fst {Y : Scheme.{u}} (f : Y ⟶ C) :
    (pullbackCompIsoOfIsoPullback ι j j' e he f).hom ≫ pullback.fst (f ≫ ι) j =
      pullback.fst f j' := by
  simp [pullbackCompIsoOfIsoPullback]

@[reassoc (attr := simp)]
theorem pullbackCompIsoOfIsoPullback_hom_snd {Y : Scheme.{u}} (f : Y ⟶ C) :
    (pullbackCompIsoOfIsoPullback ι j j' e he f).hom ≫ pullback.snd (f ≫ ι) j =
      pullback.snd f j' ≫ e.hom ≫ pullback.snd ι j := by
  simp [pullbackCompIsoOfIsoPullback]

/-- The natural isomorphism of underlying schemes behind
`etaleRestrictionDirectImageIso`. -/
def smallEtaleBaseChangeComposeIso [Etale ι] :
    Stacks.EtaleCohomology.smallEtaleBaseChange j' ⋙ Scheme.Etale.forget E' ⋙ Over.forget E' ≅
      Scheme.Etale.smallEtaleCompose ι ⋙ Stacks.EtaleCohomology.smallEtaleBaseChange j ⋙
        Scheme.Etale.forget E ⋙ Over.forget E :=
  NatIso.ofComponents (fun V => pullbackCompIsoOfIsoPullback ι j j' e he V.hom) (by
    intro V W g
    have hg : g.left ≫ W.hom = V.hom := by simpa using g.w
    change pullback.lift (pullback.fst V.hom j' ≫ g.left) (pullback.snd V.hom j')
        (by rw [Category.assoc, hg, pullback.condition]) ≫
          (pullbackCompIsoOfIsoPullback ι j j' e he W.hom).hom =
      (pullbackCompIsoOfIsoPullback ι j j' e he V.hom).hom ≫
        pullback.lift (pullback.fst (V.hom ≫ ι) j ≫ g.left) (pullback.snd (V.hom ≫ ι) j)
        (by
          change (pullback.fst (V.hom ≫ ι) j ≫ g.left) ≫ W.hom ≫ ι = _
          rw [Category.assoc, reassoc_of% hg, pullback.condition])
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackCompIsoOfIsoPullback_hom_fst, pullback.lift_fst,
        pullbackCompIsoOfIsoPullback_hom_fst_assoc]
    · simp only [Category.assoc, pullbackCompIsoOfIsoPullback_hom_snd, pullback.lift_snd_assoc,
        pullback.lift_snd])
end

/-- For an étale `ι : C ⟶ X` with `C` integral, the base change `C ×_X η_X` of the scheme of
generic points of `X` is the spectrum of the function field of `C`, over `C`. -/
def specFunctionFieldIsoPullbackGenericPointsMorphism [Etale ι] [IsIntegral C] :
    Spec C.functionField ≅ pullback ι X.genericPointsMorphism :=
  have := ι.isIso_genericPointsSchemeToPullback
  C.genericPointsSchemeIsoSpecFunctionField ≪≫ asIso ι.genericPointsSchemeToPullback

@[reassoc (attr := simp)]
theorem specFunctionFieldIsoPullbackGenericPointsMorphism_hom_fst [Etale ι] [IsIntegral C] :
    (specFunctionFieldIsoPullbackGenericPointsMorphism ι).hom ≫
        pullback.fst ι X.genericPointsMorphism =
      Stacks.EtaleCohomology.genericPointInclusion C := by
  simp [specFunctionFieldIsoPullbackGenericPointsMorphism,
    genericPointsSchemeIsoSpecFunctionField_hom_genericPointsMorphism]

/-- **The restriction of `j_{X*} 𝐆_m` to an étale `C ⟶ X` with `C` integral is `j_{C*} 𝐆_m`**,
where `j_X : η_X ⟶ X` is the scheme of generic points of `X` and `j_C : Spec k(C) ⟶ C` the
inclusion of the generic point of `C`. -/
def etaleRestrictionGenericPointsDirectImageIso [Etale ι] [IsIntegral C] :
    (etaleRestriction.{u, u + 1} ι).obj ((etaleAbelianDirectImage.{u, u + 1}
      X.genericPointsMorphism).obj (Stacks.Kummer.multiplicativeSheaf.{u, u + 1}
        X.genericPointsScheme)) ≅
      (genericPointDirectImage.{u, u + 1} C).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec C.functionField)) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight (NatIso.op (smallEtaleBaseChangeComposeIso ι X.genericPointsMorphism
      (Stacks.EtaleCohomology.genericPointInclusion C)
      (specFunctionFieldIsoPullbackGenericPointsMorphism ι)
      (specFunctionFieldIsoPullbackGenericPointsMorphism_hom_fst ι))) globalUnitsAddFunctor)

/-- Étale cohomology with coefficients in `AddCommGrpCat.{u + 1}` vanishes in degree `p` for a
sheaf isomorphic to one whose degree-`p` cohomology vanishes. -/
theorem subsingleton_sheafH_smallEtale_of_iso {Y : Scheme.{u}}
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (p : ℕ)
    [Subsingleton (Sheaf.H.{u + 1, u + 1} G p)] :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F p) := by
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}]
  refine IsZero.of_iso ?_
    (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived p).mapIso e)
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
    Y.smallEtaleTopology G p).1 inferInstance

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The units of the sheaf of rational functions on a smooth curve are acyclic.** Let `X` be
a smooth curve over an algebraically closed field `k` (separated, quasi-compact and smooth of
relative dimension one over `k`, not necessarily connected), `j_X : η_X ⟶ X` its scheme of
generic points, and `𝓡_X^* = j_{X*} 𝐆_{m,η_X}`. Then `H^p(X, 𝓡_X^*) = 0` for every `p > 0`. -/
@[weil "lem_fk105_rational_functions_acyclic"]
theorem subsingleton_sheafH_genericPointsDirectImage_multiplicativeSheaf_smoothCurve
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 g] [IsSeparated g] [QuasiCompact g] (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((etaleAbelianDirectImage.{u, u + 1}
      X.genericPointsMorphism).obj (Stacks.Kummer.multiplicativeSheaf.{u, u + 1}
        X.genericPointsScheme)) p) := by
  classical
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace g }
  have : Finite (_root_.ConnectedComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_connectedComponents X
  let eC := Finite.equivFin (_root_.ConnectedComponents X)
  let U : Fin (Nat.card (_root_.ConnectedComponents X)) → X.Opens := fun a ↦
    ⟨connectedComponent (eC.symm a).out,
      (TopologicalSpace.isClopen_connectedComponent_of_finite_connectedComponents _).2⟩
  have hUclopen (a) : IsClopen (U a : Set X) :=
    TopologicalSpace.isClopen_connectedComponent_of_finite_connectedComponents _
  have hUmk (a) (x : X) (hx : x ∈ U a) : eC (_root_.ConnectedComponents.mk x) = a := by
    rw [(_root_.ConnectedComponents.coe_eq_coe'.mpr hx).trans (Quotient.out_eq _),
      Equiv.apply_symm_apply]
  have hrange (a) : Set.range (U a).ι.base = (U a : Set X) := Scheme.Opens.range_ι _
  have hdisj : Pairwise fun a b ↦
      Disjoint (Set.range (U a).ι.base) (Set.range (U b).ι.base) := by
    intro a b hab
    simp only [hrange]
    exact Set.disjoint_left.mpr fun x hx hx' ↦ hab ((hUmk a x hx).symm.trans (hUmk b x hx'))
  have hcov : ⋃ a, Set.range (U a).ι.base = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr
      ⟨eC (_root_.ConnectedComponents.mk x), ?_⟩
    rw [hrange]
    change x ∈ connectedComponent (eC.symm (eC _)).out
    rw [Equiv.symm_apply_apply]
    exact _root_.ConnectedComponents.coe_eq_coe'.mp (Quotient.out_eq _).symm
  have hinj := (bijective_etaleCohomologyPullback_pi (fun a ↦ (U a).ι) hdisj hcov
    ((etaleAbelianDirectImage.{u, u + 1} X.genericPointsMorphism).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X.genericPointsScheme)) p).1
  refine ⟨fun x y ↦ hinj (funext fun a ↦ ?_)⟩
  -- the connected component `C = U a` is an integral smooth curve
  let C := (U a).toScheme
  have : ConnectedSpace C := isConnected_iff_connectedSpace.mp (by
    change _root_.IsConnected (connectedComponent _)
    exact isConnected_connectedComponent)
  have : IsIntegral C := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth ((U a).ι ≫ g)
  have : IsClosedImmersion (U a).ι := IsClosedImmersion.of_isPreimmersion (U a).ι (by
    rw [Scheme.Opens.range_ι]; exact (hUclopen a).1)
  have : SmoothOfRelativeDimension 1 ((U a).ι ≫ g) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((U a).ι ≫ g))
  have : IsCurve k ((U a).ι ≫ g) :=
    { toIsVariety := { }
      topologicalKrullDim_eq_one :=
        topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 ((U a).ι ≫ g) }
  have : Subsingleton (Sheaf.H.{u + 1, u + 1} ((genericPointDirectImage.{u, u + 1} C).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec C.functionField))) p) :=
    subsingleton_sheafH_genericPointDirectImage_multiplicativeSheaf_smoothCurve
      ((U a).ι ≫ g) p hp
  have : Subsingleton (Sheaf.H.{u + 1, u + 1} ((smallEtalePullbackAb (U a).ι).obj
      ((etaleAbelianDirectImage.{u, u + 1} X.genericPointsMorphism).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X.genericPointsScheme))) p) :=
    subsingleton_sheafH_smallEtale_of_iso
      ((smallEtalePullbackAbRestrictionIso (U a).ι).app _ ≪≫
        etaleRestrictionGenericPointsDirectImageIso (U a).ι) p
  exact Subsingleton.elim _ _

/-- **The units of the sheaf of rational functions on a smooth curve are acyclic**, on the small
étale site `SmallEtale B X hX` of a big étale site `B` containing `X`: the restriction of
`𝓡_X^* = j_{X*} 𝐆_{m,η_X}` to it has vanishing cohomology in every positive degree. -/
@[weil "lem_fk105_rational_functions_acyclic"]
theorem subsingleton_sheafH_genericPointsDirectImage_multiplicativeSheaf_smoothCurve_smallEtale
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 g] [IsSeparated g] [QuasiCompact g]
    (B : BigEtaleSite.{u}) (hX : B.Contains X)
    [HasExt.{u + 1} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})]
    (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{u + 1} ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.obj
      ((etaleAbelianDirectImage.{u, u + 1} X.genericPointsMorphism).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X.genericPointsScheme))) p) := by
  have := subsingleton_sheafH_genericPointsDirectImage_multiplicativeSheaf_smoothCurve g p hp
  have : EnoughInjectives (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :=
    (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).enoughInjectives_iff.2 inferInstance
  exact (Stacks.Cohomology.DenseSubsite.hAddEquiv.{u + 1, u + 1} (SmallEtale.topology B X hX)
    X.smallEtaleTopology (SmallEtale.toEtaleSite B X hX)
    ((etaleAbelianDirectImage.{u, u + 1} X.genericPointsMorphism).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X.genericPointsScheme))
      p).symm.injective.subsingleton

end AlgebraicGeometry
