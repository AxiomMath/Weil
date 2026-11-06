module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleGlobalFunctions
public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtaleFibreProductInEt
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtaleSheaf

/-!
# The presheaf of units is an étale sheaf

For every scheme `S`, the presheaf of units `𝒪^*_{S,et}`, `U ↦ Γ(U, 𝒪_U)ˣ`, on the étale
category `Et(S)` of noetherian separated étale `S`-schemes is a sheaf for the étale topology.

The proof restricts the sheaf property of the units presheaf on the small étale site of `S`
along the inclusion of `Et(S)`. That inclusion is continuous for the topology of `Et(S)`
restricted from the small étale site: it preserves covering sieves by definition of that
topology, and it preserves compatible families because `Et(S)` is closed under fibre products
in the small étale site.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isContinuous_inclusion`: the inclusion of
  `Et(S)` into the small étale site is continuous, for any scheme `S`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isSheaf_unitsPresheaf`: the presheaf of
  units on `Et(S)` is an étale sheaf.
* `AlgebraicGeometry.Scheme.isSheaf_unitsEtalePresheaf`: the same for a bare scheme `X`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isEtaleSheaf_unitsPresheaf`: for `S` locally
  noetherian, its underlying presheaf of sets satisfies the conditions a) and b) of an étale
  sheaf.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.unitsSheaf`: the étale sheaf `𝒪^*_{S,et}`.
* `AlgebraicGeometry.Scheme.unitsEtaleSheaf`: the same for a bare scheme `X`.

## Implementation notes

The source deduces the statement from the sheaf property of `𝒪_{X,et}` by checking that units
glue. Here it is deduced instead from the sheaf property of the units presheaf on the small
étale site, `AlgebraicGeometry.unitsPresheaf_isSheaf_smallEtale`, which rests on the
representability of `𝐆_m` and the subcanonicity of the fpqc topology. No noetherian hypothesis
on `S` is needed for the sheaf property for the topology of `Et(S)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03P4](https://stacks.math.columbia.edu/tag/03P4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS} in
/-- **`Et(S)` is closed under fibre products in the small étale site**: a commutative square
`f₁ ≫ g₁ = f₂ ≫ g₂` of the small étale site over a cospan `g₁, g₂` of `Et(S)` factors through
the fibre product `Y₁ ×_Z Y₂` formed in `Et(S)`. -/
theorem exists_lift_pullbackObj {Y₁ Y₂ Z : SmallNoetherianSeparatedEtale B S hS}
    (g₁ : Y₁ ⟶ Z) (g₂ : Y₂ ⟶ Z) {X : SmallEtale B S hS} (f₁ : X ⟶ (inclusion B S hS).obj Y₁)
    (f₂ : X ⟶ (inclusion B S hS).obj Y₂)
    (e : f₁ ≫ (inclusion B S hS).map g₁ = f₂ ≫ (inclusion B S hS).map g₂) :
    ∃ k : X ⟶ (inclusion B S hS).obj (pullbackObj g₁ g₂),
      k ≫ (inclusion B S hS).map (pullbackFst g₁ g₂) = f₁ ∧
        k ≫ (inclusion B S hS).map (pullbackSnd g₁ g₂) = f₂ := by
  have e' : (SmallEtale.toScheme B S hS).map f₁ ≫ (toScheme B S hS).map g₁ =
      (SmallEtale.toScheme B S hS).map f₂ ≫ (toScheme B S hS).map g₂ := by
    have := congrArg (SmallEtale.toScheme B S hS).map e
    simp only [Functor.map_comp] at this
    exact this
  let l := pullback.lift ((SmallEtale.toScheme B S hS).map f₁)
    ((SmallEtale.toScheme B S hS).map f₂) e'
  have hl : l ≫ B.inclusion.map (pullbackObj g₁ g₂).obj.obj.hom = B.inclusion.map X.obj.hom := by
    change l ≫ (pullback.fst _ _ ≫ structureMorphism Y₁) = _
    rw [pullback.lift_fst_assoc]
    simp only [structureMorphism, SmallEtale.toScheme, Functor.comp_map, ← Functor.map_comp]
    congr 1
    exact Over.w f₁.hom
  refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk l) (by ext1; exact hl)), ?_, ?_⟩
  · apply (SmallEtale.toScheme B S hS).map_injective
    rw [Functor.map_comp]
    exact pullback.lift_fst _ _ _
  · apply (SmallEtale.toScheme B S hS).map_injective
    rw [Functor.map_comp]
    exact pullback.lift_snd _ _ _

/-- The inclusion of `Et(S)` into the small étale site preserves compatible families. -/
theorem compatiblePreserving_inclusion :
    CompatiblePreserving.{u + 1} (SmallEtale.topology B S hS) (inclusion B S hS) := by
  refine Stacks.Sites.compatiblePreserving_of_lift _ _ ?_
  intro Y₁ Y₂ Z g₁ g₂ X f₁ f₂ e
  obtain ⟨k, h₁, h₂⟩ := exists_lift_pullbackObj g₁ g₂ f₁ f₂ e
  exact ⟨pullbackObj g₁ g₂, pullbackFst g₁ g₂, pullbackSnd g₁ g₂, k,
    (isPullback_pullbackFst_pullbackSnd g₁ g₂).w, h₁, h₂⟩

/-- The inclusion of `Et(S)` into the small étale site carries covering sieves of `Et(S)` to
covering sieves, for any scheme `S`. -/
theorem coverPreserving_inclusion :
    CoverPreserving (topology B S hS) (SmallEtale.topology B S hS) (inclusion B S hS) where
  cover_preserve {U R} hR := by
    change Precoverage.Saturate _ U R at hR
    induction hR with
    | of X R hR =>
      rw [← Sieve.generate_map_eq_functorPushforward]
      exact hR
    | top X => simp
    | pullback X R _ Y f ih =>
      refine (SmallEtale.topology B S hS).superset_covering ?_
        ((SmallEtale.topology B S hS).pullback_stable ((inclusion B S hS).map f) ih)
      rintro W x ⟨V, s, w, hs, hx⟩
      obtain ⟨k, h₁, h₂⟩ := exists_lift_pullbackObj f s x w hx
      refine ⟨pullbackObj f s, pullbackFst f s, k, ?_, h₁.symm⟩
      change R (pullbackFst f s ≫ f)
      rw [(isPullback_pullbackFst_pullbackSnd f s).w]
      exact R.downward_closed hs _
    | transitive X R R' _ _ ihR ihR' =>
      refine (SmallEtale.topology B S hS).transitive ihR _ ?_
      rintro Y g ⟨V, s, h, hs, rfl⟩
      rw [Sieve.pullback_comp]
      refine (SmallEtale.topology B S hS).pullback_stable h
        ((SmallEtale.topology B S hS).superset_covering ?_ (ihR' hs))
      rintro W x ⟨V', t, w, ht, rfl⟩
      exact ⟨V', t ≫ s, w, ht, by simp⟩

/-- **The inclusion of `Et(S)` into the small étale site is continuous**, for any scheme `S`:
restriction along it carries sheaves on the small étale site to étale sheaves on `Et(S)`. -/
instance isContinuous_inclusion :
    (inclusion B S hS).IsContinuous (topology B S hS) (SmallEtale.topology B S hS) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_inclusion B S hS)
    (coverPreserving_inclusion B S hS)

/-- **The presheaf of units is an étale sheaf** (FK I.2): for every scheme `S`, the presheaf
`𝒪^*_{S,et}`, `U ↦ Γ(U, 𝒪_U)ˣ`, is a sheaf on `Et(S)`. -/
@[weil "prop_fk102_units_etale_sheaf"]
theorem isSheaf_unitsPresheaf :
    Presheaf.IsSheaf (topology B S hS) (unitsPresheaf B S hS) :=
  (inclusion B S hS).op_comp_isSheaf (topology B S hS) (SmallEtale.topology B S hS)
    ⟨_, unitsPresheaf_isSheaf_smallEtale B S hS⟩

/-- The étale sheaf of units `𝒪^*_{S,et}` on `Et(S)`. -/
abbrev unitsSheaf : EtaleSheaf B S hS AddCommGrpCat.{u} :=
  ⟨unitsPresheaf B S hS, isSheaf_unitsPresheaf B S hS⟩

/-- For `S` locally noetherian, the underlying presheaf of sets of `𝒪^*_{S,et}` satisfies the
conditions a) (finite disjoint unions) and b) (descent along surjective morphisms) of an étale
sheaf on `Et(S)`. -/
theorem isEtaleSheaf_unitsPresheaf [IsLocallyNoetherian S] :
    EtalePresheaf.IsEtaleSheaf (unitsPresheaf B S hS ⋙ forget AddCommGrpCat) :=
  EtaleSheaf.isEtaleSheaf_forget (unitsSheaf B S hS)

end SmallNoetherianSeparatedEtale

/-- **The presheaf of units is an étale sheaf** (FK I.2): for every scheme `X`, the presheaf
`𝒪^*_{X,et}`, `U ↦ Γ(U, 𝒪_U)ˣ`, is a sheaf on `Et(X)`. -/
@[weil "prop_fk102_units_etale_sheaf"]
theorem Scheme.isSheaf_unitsEtalePresheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf
      (SmallNoetherianSeparatedEtale.topology (BigEtaleSite.containing X) X
        (BigEtaleSite.contains_containing X))
      X.unitsEtalePresheaf :=
  SmallNoetherianSeparatedEtale.isSheaf_unitsPresheaf _ _ _

/-- The étale sheaf of units `𝒪^*_{X,et}` on `Et(X)` of a bare scheme `X`. -/
abbrev Scheme.unitsEtaleSheaf (X : Scheme.{u}) : X.EtaleSheaf AddCommGrpCat.{u} :=
  ⟨X.unitsEtalePresheaf, X.isSheaf_unitsEtalePresheaf⟩

end AlgebraicGeometry

end

