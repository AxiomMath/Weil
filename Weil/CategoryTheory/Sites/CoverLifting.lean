module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import Weil.Attr
public import Weil.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.SheafRestriction
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.SliceSiteIso

/-!
# Sheafification commutes with restriction to an object of `Et(S)`

Let `U = (U, u)` be an object of the étale category `Et(S)` of noetherian separated étale
`S`-schemes, and let `P` be a presheaf on `Et(S)`. The restriction `P ↦ P|_U` to `Et(U)` is
precomposition with the functor `Et(U) ⥤ Et(S)`, `(V, v) ↦ (V, u ∘ v)`. This functor is the
composite of the isomorphism of categories `Et(U) ≅ Et(S)/U` with the forgetful functor
`Et(S)/U ⥤ Et(S)`, and coverings correspond under the isomorphism; hence it is both continuous
and cocontinuous. Consequently restriction commutes with sheafification: `(P^#)|_U` is the
sheafification of `P|_U`, compatibly with the canonical maps from `P|_U`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isCocontinuous_postcompose`,
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isContinuous_postcompose` — the functor
  `Et(U) ⥤ Et(S)` is cocontinuous and continuous.
* `AlgebraicGeometry.EtalePresheaf.restrictSheafifyIso` — the isomorphism
  `(P^#)|_U ≅ (P|_U)^#`.
* `AlgebraicGeometry.EtalePresheaf.restrict_toSheafify_comp_restrictSheafifyIso_hom` — it is
  compatible with the canonical maps `P|_U ⟶ (P^#)|_U` and `P|_U ⟶ (P|_U)^#`.

## Implementation notes

The sheafification is Mathlib's `CategoryTheory.sheafify`, for any coefficient category `A`
admitting sheafification on both sites; for presheaves of sets or abelian groups it is
canonically isomorphic to the iterated plus construction
`CategoryTheory.GrothendieckTopology.sheafify`.
The isomorphism is the general compatibility of pushforward along a continuous and cocontinuous
functor with sheafification,
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v' u' u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable [IsLocallyNoetherian S] (U : SmallNoetherianSeparatedEtale B S hS)

instance isLocallyNoetherian_obj : IsLocallyNoetherian U.obj.obj.left.1 :=
  inferInstanceAs (IsLocallyNoetherian ((toScheme B S hS).obj U))


/-- The isomorphism `Et(S)/U ⥤ Et(U)` is cocontinuous for the induced topology on the slice. -/
instance isCocontinuous_fromOver :
    (fromOver U).IsCocontinuous ((topology B S hS).over U)
      (topology B U.obj.obj.left.1 U.obj.obj.left.property) where
  cover_lift {V R} hR := by
    rw [GrothendieckTopology.mem_over_iff, mem_topology_iff]
    intro x
    obtain ⟨W', f', hf', hx⟩ := (mem_topology_iff _ _ _ R).1 hR x
    let f'' : (fromOver U).obj ((toOver' U).obj W') ⟶ (fromOver U).obj V := f'
    let g : (toOver' U).obj W' ⟶ V := (fullyFaithfulFromOver U).preimage f''
    have hg : (fromOver U).map g = f'' := (fullyFaithfulFromOver U).map_preimage f''
    refine ⟨((toOver' U).obj W').left, g.left, ⟨(toOver' U).obj W', g, 𝟙 _, ?_, ?_⟩, ?_⟩
    · change R ((fromOver U).map g)
      rw [hg]
      exact hf'
    · simp
    · change x ∈ Set.range ((toScheme _ _ _).map ((fromOver U).map g))
      rw [hg]
      exact hx

/-- The isomorphism `Et(U) ⥤ Et(S)/U` is cocontinuous for the induced topology on the slice. -/
instance isCocontinuous_toOver' :
    (toOver' U).IsCocontinuous (topology B U.obj.obj.left.1 U.obj.obj.left.property)
      ((topology B S hS).over U) where
  cover_lift {V R} hR := by
    rw [mem_topology_iff]
    intro x
    rw [GrothendieckTopology.mem_over_iff, mem_topology_iff] at hR
    obtain ⟨W, f, ⟨Z, g, h, hg, rfl⟩, hx⟩ := hR x
    have hZ : (toOver' U).obj ((fromOver U).obj Z) = Z :=
      congrArg (fun F : Over U ⥤ Over U => F.obj Z) (fromOver_comp_toOver' U)
    let p : (fromOver U).obj Z ⟶ V :=
      ((overEquivalence U).fullyFaithfulInverse).preimage (eqToHom hZ ≫ g)
    have hp : (toOver' U).map p = eqToHom hZ ≫ g :=
      ((overEquivalence U).fullyFaithfulInverse).map_preimage _
    refine ⟨(fromOver U).obj Z, p, ?_, ?_⟩
    · change R ((toOver' U).map p)
      rw [hp]
      exact R.downward_closed hg _
    · obtain ⟨w, rfl⟩ := hx
      refine ⟨(toScheme B S hS).map h w, ?_⟩
      change ((toScheme B S hS).map ((toOver' U).map p).left) _ = _
      rw [hp, Over.comp_left, Over.eqToHom_left, Functor.map_comp, eqToHom_map]
      erw [eqToHom_refl, Category.id_comp]
      rfl

/-- **Coverings of `Et(U)` and of `Et(S)/U` correspond**: the isomorphism `Et(U) ⥤ Et(S)/U` is a
dense subsite, so a sieve on `V ∈ Et(U)` is covering exactly when its image is. -/
instance isDenseSubsite_toOver' :
    (toOver' U).IsDenseSubsite (topology B U.obj.obj.left.1 U.obj.obj.left.property)
      ((topology B S hS).over U) :=
  haveI : (overEquivalence U).functor.IsCocontinuous ((topology B S hS).over U)
      (topology B U.obj.obj.left.1 U.obj.obj.left.property) :=
    isCocontinuous_fromOver U
  haveI : (overEquivalence U).inverse.IsCocontinuous
      (topology B U.obj.obj.left.1 U.obj.obj.left.property) ((topology B S hS).over U) :=
    isCocontinuous_toOver' U
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ (overEquivalence U)

/-- The functor `Et(U) ⥤ Et(S)`, `(V, v) ↦ (V, u ∘ v)`, is cocontinuous. -/
instance isCocontinuous_postcompose :
    (postcompose U).IsCocontinuous (topology B U.obj.obj.left.1 U.obj.obj.left.property)
      (topology B S hS) :=
  isCocontinuous_comp (toOver' U) (Over.forget U) _ ((topology B S hS).over U)

/-- The functor `Et(U) ⥤ Et(S)`, `(V, v) ↦ (V, u ∘ v)`, is continuous. -/
instance isContinuous_postcompose :
    (postcompose U).IsContinuous (topology B U.obj.obj.left.1 U.obj.obj.left.property)
      (topology B S hS) :=
  Functor.isContinuous_comp (toOver' U) (Over.forget U) _ ((topology B S hS).over U) _

end SmallNoetherianSeparatedEtale

namespace EtalePresheaf

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsLocallyNoetherian S]
  (U : SmallNoetherianSeparatedEtale B S hS) {A : Type u'} [Category.{v'} A]
  [HasLimitsOfSize.{u, u} A] [HasWeakSheafify (topology B S hS) A]
  [HasWeakSheafify (topology B U.obj.obj.left.1 U.obj.obj.left.property) A]

omit [IsLocallyNoetherian S] [HasWeakSheafify (topology B S hS) A]
  [HasWeakSheafify (topology B U.obj.obj.left.1 U.obj.obj.left.property) A] in
/-- The comma categories `StructuredArrow X (postcompose U).op` are essentially small, so right
Kan extensions along `(postcompose U).op` exist. -/
instance hasLimitsOfShape_structuredArrow_postcompose
    (X : (SmallNoetherianSeparatedEtale B S hS)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (postcompose U).op) A :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- **Sheafification commutes with restriction.** For a presheaf `P` on `Et(S)` and `U ∈ Et(S)`,
the restriction to `Et(U)` of the sheafification of `P` is the sheafification of the
restriction `P|_U`. -/
@[weil "lem_fk102_sheafification_commutes_restriction"]
def restrictSheafifyIso (P : EtalePresheaf B S hS A) :
    restrict (sheafify (topology B S hS) P) U ≅
      sheafify (topology B U.obj.obj.left.1 U.obj.obj.left.property) (restrict P U) :=
  ((sheafToPresheaf (topology B U.obj.obj.left.1 U.obj.obj.left.property) A).mapIso
    (((postcompose U).pushforwardContinuousSheafificationCompatibility A
      (topology B U.obj.obj.left.1 U.obj.obj.left.property) (topology B S hS)).app P)).symm

/-- **The isomorphism `(P^#)|_U ≅ (P|_U)^#` is compatible with the canonical maps** from `P|_U`:
the restriction of `P ⟶ P^#` followed by it is `P|_U ⟶ (P|_U)^#`. -/
@[weil "lem_fk102_sheafification_commutes_restriction"]
theorem restrict_toSheafify_comp_restrictSheafifyIso_hom (P : EtalePresheaf B S hS A) :
    Functor.whiskerLeft (postcompose U).op (toSheafify (topology B S hS) P) ≫
        (restrictSheafifyIso U P).hom =
      toSheafify (topology B U.obj.obj.left.1 U.obj.obj.left.property) (restrict P U) := by
  rw [← Iso.eq_comp_inv]
  exact ((postcompose U).toSheafify_pullbackSheafificationCompatibility A
    (topology B U.obj.obj.left.1 U.obj.obj.left.property) (topology B S hS) P).symm

end EtalePresheaf

end AlgebraicGeometry
