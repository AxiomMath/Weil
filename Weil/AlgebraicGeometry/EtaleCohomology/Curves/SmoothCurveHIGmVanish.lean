module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Higher vanishing for the multiplicative group on a possibly disconnected smooth curve

Let `k` be an algebraically closed field and `X` a smooth curve over `k`: a separated `k`-scheme
of finite type, smooth of relative dimension one over `k`, not assumed connected, complete or
affine. Then `H^q_étale(X, 𝐆_m) = 0` for every `q ≥ 2`.

The local rings of `X` are regular, hence domains, so every point of `X` lies on exactly one
irreducible component. As `X` is Noetherian it has finitely many irreducible components, and
these are therefore open as well as closed: `X` is the finite disjoint union of the open
subschemes on its irreducible components. Each of them is an integral smooth curve, for which
the vanishing is [Stacks, Tag 03RM], and the étale cohomology of a finite disjoint union of open
subschemes is the product of their étale cohomologies.

## Main results

* `AlgebraicGeometry.Scheme.eq_of_mem_irreducibleComponents_of_isDomain_stalk`: on a scheme whose
  local rings are domains, two irreducible components through a point coincide.
* `isOpen_of_mem_irreducibleComponents_of_unique`: in a space with finitely many irreducible
  components, pairwise disjoint, every irreducible component is open.
* `AlgebraicGeometry.isCurve_opensι_comp_of_mem_irreducibleComponents`: the open subscheme on an
  irreducible component of a smooth curve is an integral curve.
* `AlgebraicGeometry.subsingleton_sheafH_multiplicativeSheaf_of_smoothOfRelativeDimension_one`:
  `H^q_étale(X, 𝐆_m) = 0` for `q ≥ 2` on a smooth curve over an algebraically closed field.

## Implementation notes

A smooth curve is written as a morphism `f : X ⟶ Spec k` which is separated, quasi-compact and
smooth of relative dimension one (`AlgebraicGeometry.SmoothOfRelativeDimension 1 f`); smoothness
of relative dimension one gives local finite type and pure dimension one. The sheaf `𝐆_m` is
`Stacks.Kummer.multiplicativeSheaf X` on Mathlib's small étale site `X.smallEtaleTopology`, the
site of [Stacks, Tag 03RM] as it is available, at the coefficient universe `max (u + 1) v` and
with cohomology in any `Ext` universe.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5, Lemma 5.2.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- In a space with finitely many irreducible components, any two of which meeting are equal,
every irreducible component is open. -/
theorem isOpen_of_mem_irreducibleComponents_of_unique
    (hfin : (irreducibleComponents X).Finite)
    (huniq : ∀ Z ∈ irreducibleComponents X, ∀ Z' ∈ irreducibleComponents X, ∀ x ∈ Z, x ∈ Z' →
      Z = Z')
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  have hc : Zᶜ = ⋃ Z' ∈ {Z' ∈ irreducibleComponents X | Z' ≠ Z}, Z' := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
        mem_irreducibleComponent⟩
      rintro h
      exact hx (h ▸ mem_irreducibleComponent)
    · rintro ⟨Z', ⟨hZ', hne⟩, hx⟩ hxZ
      exact hne (huniq Z' hZ' Z hZ x hx hxZ)
  rw [← isClosed_compl_iff, hc]
  exact (hfin.subset (fun _ h => h.1)).isClosed_biUnion
    fun Z' h => isClosed_of_mem_irreducibleComponents Z' h.1

end Topology

namespace AlgebraicGeometry.Scheme

/-- **On a scheme whose local rings are domains, two irreducible components through a point
coincide.** The generic point of `Spec 𝒪_{X,x}` maps to a generization of every generization of
`x`, so its closure contains every irreducible component through `x`. -/
theorem eq_of_mem_irreducibleComponents_of_isDomain_stalk (X : Scheme.{u})
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) {Z Z' : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) {x : X}
    (hx : x ∈ Z) (hx' : x ∈ Z') : Z = Z' := by
  have := hX x
  let ξ : X := X.fromSpecStalk x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have key : ∀ W ∈ irreducibleComponents X, x ∈ W → W = closure {ξ} := by
    intro W hW hxW
    have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
    have hirr : IsIrreducible W := hW.1
    obtain ⟨η, hgen⟩ := QuasiSober.sober hirr hWc
    have hsp : η ⤳ x := by
      rw [specializes_iff_mem_closure, hgen.def]
      exact hxW
    have hmem : η ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hsp
    obtain ⟨p, hp⟩ := hmem
    have hξ : ξ ⤳ η := by
      rw [← hp]
      refine Specializes.map ?_ (X.fromSpecStalk x).continuous
      exact (PrimeSpectrum.le_iff_specializes
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk x)) p).1 bot_le
    have hsub : W ⊆ closure {ξ} := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hξ))
        isClosed_closure
    exact hsub.antisymm (hW.2 isIrreducible_singleton.closure hsub)
  rw [key Z hZ hx, key Z' hZ' hx']

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

include f in
/-- The local rings of a scheme smooth over a field are domains. -/
theorem isDomain_stalk_of_smooth_over_field [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) :=
  ((isNormal_iff_stalk_normal X).1 (isNormal_of_isRegular X (isRegular_of_smooth_over_field f))
    x).1

include f in
/-- **An irreducible component of a scheme smooth over a field is open.** -/
theorem isOpen_of_mem_irreducibleComponents_of_smooth [Smooth f] [QuasiCompact f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { }
  exact isOpen_of_mem_irreducibleComponents_of_unique
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun Z hZ Z' hZ' x hx hx' => Scheme.eq_of_mem_irreducibleComponents_of_isDomain_stalk X
      (isDomain_stalk_of_smooth_over_field f) hZ hZ' hx hx') hZ

/-- **The open subscheme on an irreducible component of a smooth curve is a curve.** Let `X` be
separated, quasi-compact and smooth of relative dimension one over a field `k`, and `Z` an
irreducible component of `X`, open by `isOpen_of_mem_irreducibleComponents_of_smooth`. Then the
open subscheme on `Z` is an integral separated scheme of finite type over `k` of dimension one. -/
theorem isCurve_opensι_comp_of_mem_irreducibleComponents [IsSeparated f] [QuasiCompact f]
    [SmoothOfRelativeDimension 1 f] (U : X.Opens) (hU : (U : Set X) ∈ irreducibleComponents X) :
    IsCurve k (U.ι ≫ f) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { }
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : QuasiCompact (U.ι ≫ f) := (quasiCompact_iff_compactSpace _).mpr inferInstance
  have hirr : IsIrreducible (U : Set X) := hU.1
  have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hirr
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x =>
    have := isDomain_stalk_of_smooth_over_field f x
    isReduced_of_noZeroDivisors
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IsIntegral U := isIntegral_of_irreducibleSpace_of_isReduced _
  have : SmoothOfRelativeDimension 1 (U.ι ≫ f) := by
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + 1) (U.ι ≫ f))
  have : Nonempty U := hirr.nonempty.to_subtype
  have hv : IsVariety k (U.ι ≫ f) := { }
  exact (isCurve_iff k _).2
    ⟨hv, topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 (U.ι ≫ f)⟩

section Cohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable [IsAlgClosed k]

/-- **`H^q_étale(X, 𝐆_m) = 0` for `q ≥ 2` on a smooth curve**, at the coefficient universe `u + 1`
with `Ext` in universe `u + 1`. The curve is the finite disjoint union of the open subschemes on
its irreducible components, each an integral smooth curve, so restriction identifies
`H^q(X, 𝐆_m)` with the product of the groups `H^q` of `𝐆_m` on these curves, which vanish by
[Stacks, Tag 03RM]. -/
theorem subsingleton_sheafH_multiplicativeSheaf_of_smoothOfRelativeDimension_one_succ
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension 1 f] (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) q) := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { }
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have := hfin.to_subtype
  let e := Finite.equivFin (irreducibleComponents X)
  let U : Fin (Nat.card (irreducibleComponents X)) → X.Opens := fun a =>
    ⟨(e.symm a : Set X), isOpen_of_mem_irreducibleComponents_of_smooth f (e.symm a).2⟩
  have hdisj : Pairwise fun a b =>
      Disjoint (Set.range (U a).ι.base) (Set.range (U b).ι.base) := by
    intro a b hab
    simp only [Scheme.Opens.range_ι]
    refine Set.disjoint_left.2 fun x hxa hxb => hab (e.symm.injective (Subtype.ext ?_))
    exact Scheme.eq_of_mem_irreducibleComponents_of_isDomain_stalk X
      (isDomain_stalk_of_smooth_over_field f) (e.symm a).2 (e.symm b).2 hxa hxb
  have hcov : ⋃ a, Set.range (U a).ι.base = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2
      ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    rw [Scheme.Opens.range_ι]
    change x ∈ ((e.symm (e ⟨irreducibleComponent x, _⟩) : Set X))
    rw [Equiv.symm_apply_apply]
    exact mem_irreducibleComponent
  have hbij := Stacks.EtaleCohomology.bijective_etaleCohomologyPullback_pi (fun a => (U a).ι)
    hdisj hcov (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) q
  have hsub : ∀ a, Subsingleton (Sheaf.H.{u + 1}
      ((Stacks.EtaleCohomology.smallEtalePullbackAb (U a).ι).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X)) q) := by
    intro a
    have := isCurve_opensι_comp_of_mem_irreducibleComponents f (U a) (e.symm a).2
    have h := Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve
      ((U a).ι ≫ f) q hq
    exact (Stacks.Cohomology.CoefficientLift.subsingleton_sheafH_congr
      ((Stacks.EtaleCohomology.smallEtalePullbackAbRestrictionIso (U a).ι).app
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X)) q).2 h
  exact hbij.1.subsingleton

/-- **Higher vanishing for `𝐆_m` on a smooth curve.** Let `X` be a smooth curve over an
algebraically closed field `k`, not necessarily connected, complete or affine: `f : X ⟶ Spec k`
is separated, quasi-compact and smooth of relative dimension one. Then
`H^q_étale(X, 𝐆_m) = 0` for every `q ≥ 2`, for `𝐆_m` with coefficients in
`AddCommGrpCat.{max (u + 1) v}` and cohomology in any `Ext` universe. -/
@[weil "lem_fk105_smooth_curve_h_i_gm_vanish"]
theorem subsingleton_sheafH_multiplicativeSheaf_of_smoothOfRelativeDimension_one
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension 1 f]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) q) :=
  Stacks.EtaleCohomology.subsingleton_sheafH_of_iso_ulift _ _
    (Stacks.EtaleCohomology.multiplicativeSheafUliftIso.{u, v} X) q
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothOfRelativeDimension_one_succ f q hq)

end Cohomology

end AlgebraicGeometry
