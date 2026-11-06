module

public import Weil.Defs.AlgebraicGeometry.Sites.Etale
public import Weil.AlgebraicGeometry.Sites.Etale
public import Weil.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.BoundedSmallEtaleStandardCofinal
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.BoundedSmallEtaleDisjointUnion
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Covering sieves and epimorphisms on the size-bounded small étale site

Let `B` be a big étale site containing a scheme `S`, and let `SmallEtale B S hS` be the small
étale site of `S` in the sense of [Stacks, Tag 021B]. This file states, on that site, the
descriptions of covering sieves and of epimorphisms of sheaves of [FK, I.2] and [FK, I.4]:

* a sieve `R` on `V` covers if and only if for every morphism `h : U' ⟶ V` with `U'`
  quasi-compact there is a finite étale covering `(ψₖ : Wₖ ⟶ U')ₖ` with `ψₖ ≫ h ∈ R`;
* a morphism of sheaves of abelian groups is an epimorphism if and only if, over every
  quasi-compact `U`, every section of the target lies in the image after restriction to the
  members of a finite étale covering of `U`;
* a morphism of sheaves of sets is an epimorphism if and only if every section of the target
  lies in the image after restriction along a single surjective morphism of the site.

The same statements on Mathlib's small étale site `S.Etale` are
`AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff_forall_exists_isEtaleCovering`,
`AlgebraicGeometry.Scheme.epi_iff_forall_exists_isEtaleCovering` and
`AlgebraicGeometry.Scheme.epi_iff_forall_exists_surjective`.

## Main results

* `AlgebraicGeometry.Scheme.mk_le_two_power_size`: a scheme `X` has at most `2 ^ X.size`
  points.
* `AlgebraicGeometry.SmallEtale.exists_isAffine_mem_range`: every point of an object of the
  site lies in the image of a morphism from an object with affine underlying scheme.
* `AlgebraicGeometry.SmallEtale.exists_sigma_of_mem_topology`: a covering sieve is refined by
  the members of a disjoint union which is again an object of the site.
* `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff_forall_exists_isEtaleCovering_smallEtale`:
  covering sieves of `SmallEtale.topology B S hS`.
* `AlgebraicGeometry.Scheme.epi_iff_forall_exists_isEtaleCovering_smallEtale`: epimorphisms of
  sheaves of abelian groups on `SmallEtale.topology B S hS`.
* `AlgebraicGeometry.Scheme.epi_iff_forall_exists_surjective_smallEtale`: epimorphisms of
  sheaves of sets on `SmallEtale.topology B S hS`.

## Implementation notes

Both sites have the same covering sieves up to the comparison functor
`AlgebraicGeometry.SmallEtale.toEtaleSite`, but the conditions above quantify over the objects
of the site, and an object of `S.Etale` need not lie below the size cutoff of `B`. The proofs
therefore go through the description of covering sieves of `SmallEtale.topology B S hS` as the
sieves jointly surjective on points
(`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective`,
`AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`), which plays the role that
`AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff` plays on `S.Etale`. Affine
open subschemes of objects of the site are again objects, their size being bounded by that of
`S` [Stacks, Tag 04T7]. For sheaves of sets the single surjective morphism is the disjoint union
of affine pieces indexed by the points of `U`; it lies below the cutoff of `B` because a scheme
`X` has at most `2 ^ X.size` points and the cutoff is a strong limit cardinal.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2, I.4.
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Cardinal

namespace AlgebraicGeometry

namespace Scheme

/-- A scheme has at most `2 ^ X.size` points: every point is a prime ideal of the ring of
sections of one of its affine opens. -/
theorem mk_le_two_power_size (X : Scheme.{u}) : #X ≤ 2 ^ X.size := by
  have hA : ∀ x : X, ∃ A : X.affineOpens, x ∈ (A : X.Opens) := fun x ↦ by
    obtain ⟨A, hA, hx, -⟩ :=
      exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
    exact ⟨⟨A, hA⟩, hx⟩
  choose A hxA using hA
  let e : X → Σ V : X.affineOpens, PrimeSpectrum Γ(X, V.1) :=
    fun x ↦ ⟨A x, (A x).2.primeIdealOf ⟨x, hxA x⟩⟩
  have he : Function.Injective e := by
    refine Function.LeftInverse.injective (g := fun p ↦ p.1.2.fromSpec p.2) fun x ↦ ?_
    exact (A x).2.fromSpec_primeIdealOf ⟨x, hxA x⟩
  have hP : ∀ V : X.affineOpens, #(PrimeSpectrum Γ(X, V.1)) ≤ 2 ^ X.size := by
    intro V
    have hinj : Function.Injective
        (fun p : PrimeSpectrum Γ(X, V.1) ↦ (p.asIdeal : Set Γ(X, V.1))) :=
      fun p q h ↦ PrimeSpectrum.ext (SetLike.coe_injective h)
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    rw [Cardinal.mk_set]
    refine Cardinal.power_le_power_left two_ne_zero ?_
    exact (le_ciSup Cardinal.bddAbove_of_small V).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hι : #X.affineOpens ≤ X.size := (le_max_left _ _).trans (le_max_right _ _)
  calc #X ≤ #(Σ V : X.affineOpens, PrimeSpectrum Γ(X, V.1)) := Cardinal.mk_le_of_injective he
    _ = Cardinal.sum fun V : X.affineOpens ↦ #(PrimeSpectrum Γ(X, V.1)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum fun _ : X.affineOpens ↦ 2 ^ X.size := Cardinal.sum_le_sum _ _ hP
    _ = #X.affineOpens * 2 ^ X.size := Cardinal.sum_const' _ _
    _ ≤ X.size * 2 ^ X.size := mul_le_mul_left hι _
    _ = 2 ^ X.size := by
      rw [Cardinal.mul_eq_max X.aleph0_le_size
        (X.aleph0_le_size.trans (Cardinal.cantor _).le), max_eq_right (Cardinal.cantor _).le]

end Scheme

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every point of an object `V` of the small étale site lies in the image of a morphism
`U' ⟶ V` of the site whose source has affine underlying scheme: an affine open neighbourhood
of the point is étale over `S` and of size at most that of `S`. -/
theorem exists_isAffine_mem_range (V : SmallEtale B S hS) (x : (toScheme B S hS).obj V) :
    ∃ (U' : SmallEtale B S hS) (h : U' ⟶ V),
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj U') ∧
        x ∈ Set.range ((toScheme B S hS).map h) := by
  obtain ⟨R, j, _, hj, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x) (U := ⊤) (by simp)
  have : Etale V.obj.hom.hom := V.property
  have hjf : Etale (j ≫ V.obj.hom.hom) := inferInstance
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ V.obj.hom.hom)).trans_lt hS
  exact ⟨objOfEtale B S hS hR _ hjf, homOfEtale B S hS V hR hjf j rfl,
    inferInstanceAs (_root_.AlgebraicGeometry.IsAffine (Spec R)), hj⟩

/-- An object of the small étale site whose underlying scheme is affine has size at most that
of `S`. -/
theorem size_toScheme_le_of_isAffine (V : SmallEtale B S hS)
    (hV : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V)) :
    ((toScheme B S hS).obj V).size ≤ S.size := by
  have : Etale V.obj.hom.hom := V.property
  have := hV
  exact Scheme.size_le_of_locallyOfFiniteType V.obj.hom.hom

/-- **A covering sieve of the small étale site is refined by a family of affine objects
indexed by the points of the target.** The family is indexed by a type of cardinality at most
`2 ^ size U` and its members have size at most that of `S`, so that its disjoint union is again
an object of the site. -/
theorem exists_isAffine_family_of_mem_topology {U : SmallEtale B S hS} {R : Sieve U}
    (hR : R ∈ topology B S hS U) :
    ∃ (ι : Type u) (P : ι → SmallEtale B S hS) (g : ∀ i, P i ⟶ U),
      #ι ≤ 2 ^ ((toScheme B S hS).obj U).size ∧
      (∀ i, ((toScheme B S hS).obj (P i)).size ≤ S.size) ∧ (∀ i, R (g i)) ∧
      ∀ x, ∃ i, x ∈ Set.range ((toScheme B S hS).map (g i)) := by
  have key : ∀ x : (toScheme B S hS).obj U, ∃ (P : SmallEtale B S hS) (g : P ⟶ U),
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj P) ∧ R g ∧
        x ∈ Set.range ((toScheme B S hS).map g) := by
    intro x
    obtain ⟨W, g, hg, y, rfl⟩ := exists_mem_arrows_mem_range B S hS hR x
    obtain ⟨P, a, hP, z, rfl⟩ := exists_isAffine_mem_range W y
    exact ⟨P, a ≫ g, hP, R.downward_closed hg a, z, by rw [Functor.map_comp,
      Scheme.Hom.comp_apply]⟩
  choose P g hP hg hx using key
  exact ⟨_, P, g, Scheme.mk_le_two_power_size _, fun i ↦ size_toScheme_le_of_isAffine _ (hP i),
    hg, fun x ↦ ⟨x, hx x⟩⟩

/-- **A covering sieve of the small étale site is refined by the members of a disjoint
union.** For a covering sieve `R` of `U` there are a family `gᵢ : Pᵢ ⟶ U` of arrows of `R` and
an object `V` of the site, the disjoint union of the `Pᵢ` with inclusions `σᵢ`, such that the
induced morphism `f : V ⟶ U` is surjective; the `σᵢ` are monomorphisms generating a covering
sieve of `V`, and two distinct members meet only over objects covered by the empty sieve. -/
theorem exists_sigma_of_mem_topology {U : SmallEtale B S hS} {R : Sieve U}
    (hR : R ∈ topology B S hS U) :
    ∃ (ι : Type u) (P : ι → SmallEtale B S hS) (g : ∀ i, P i ⟶ U) (V : SmallEtale B S hS)
      (σ : ∀ i, P i ⟶ V) (f : V ⟶ U),
      (∀ i, R (g i)) ∧ (∀ i, σ i ≫ f = g i) ∧ Surjective ((toScheme B S hS).map f) ∧
      Sieve.ofArrows P σ ∈ topology B S hS V ∧ (∀ i, Mono (σ i)) ∧
      ∀ ⦃Z : SmallEtale B S hS⦄ ⦃i j : ι⦄ (gi : Z ⟶ P i) (gj : Z ⟶ P j), i ≠ j →
        gi ≫ σ i = gj ≫ σ j → (⊥ : Sieve Z) ∈ topology B S hS Z := by
  obtain ⟨ι, P, g, hι, hP, hg, hx⟩ := exists_isAffine_family_of_mem_topology hR
  let Y : ι → Scheme.{u} := fun i ↦ (toScheme B S hS).obj (P i)
  have hc : max (2 ^ ((toScheme B S hS).obj U).size) S.size < B.cutoff :=
    max_lt (B.cutoff_isStrongPrelimit U.obj.left.property) hS
  have hC : B.Contains (∐ Y) :=
    (schemeSize_coproduct_le Y _ (le_max_of_le_right S.aleph0_le_size)
      (hι.trans (le_max_left _ _)) fun i ↦ (hP i).trans (le_max_right _ _)).trans_lt hc
  let V : SmallEtale B S hS := objOfEtale B S hS hC (Sigma.desc fun i ↦ (P i).obj.hom.hom)
    (etale_sigmaDesc_hom B S hS P)
  let σ : ∀ i, P i ⟶ V := fun i ↦
    homMk B S hS (X := P i) (Y := V) (Sigma.ι Y i) (Sigma.ι_desc _ _)
  have hdesc : (Sigma.desc fun i ↦ (toScheme B S hS).map (g i)) ≫ U.obj.hom.hom =
      V.obj.hom.hom := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, Sigma.ι_desc]
    change _ = Sigma.ι _ i ≫ Sigma.desc fun i ↦ (P i).obj.hom.hom
    rw [Sigma.ι_desc]
    exact congrArg (fun k ↦ k.hom) (CategoryTheory.Over.w ((inclusion B S hS).map (g i)))
  let f : V ⟶ U :=
    homMk B S hS (X := V) (Y := U) (Sigma.desc fun i ↦ (toScheme B S hS).map (g i)) hdesc
  have hσf : ∀ i, σ i ≫ f = g i := fun i ↦ by
    apply ObjectProperty.hom_ext
    apply CategoryTheory.Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact Sigma.ι_desc _ _
  refine ⟨ι, P, g, V, σ, f, hg, hσf, ⟨fun x ↦ ?_⟩, ?_, fun i ↦ ?_, ?_⟩
  · obtain ⟨i, z, rfl⟩ := hx x
    exact ⟨(toScheme B S hS).map (σ i) z, by
      rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hσf]⟩
  · exact generate_ofArrows_mem_topology_of_jointlySurjective B S hS P σ fun x ↦
      ⟨(sigmaOpenCover Y).idx x, (sigmaOpenCover Y).covers x⟩
  · have : IsOpenImmersion ((toScheme B S hS).map (σ i)) := (sigmaOpenCover Y).map_prop i
    exact (toScheme B S hS).mono_of_mono_map inferInstance
  · intro Z i j gi gj hij hcomm
    refine bot_mem_topology_of_isEmpty_toScheme B S hS Z
      (isEmpty_of_commSq_sigmaι_of_ne (g := Y) (a := (toScheme B S hS).map gi)
        (b := (toScheme B S hS).map gj) ⟨?_⟩ hij)
    have h2 := congrArg (toScheme B S hS).map hcomm
    rw [Functor.map_comp, Functor.map_comp] at h2
    exact h2

end SmallEtale

namespace Scheme

open SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The form on `SmallEtale.topology B S hS` of
`AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff_forall_exists_isEtaleCovering`. -/
theorem mem_smallEtaleTopology_iff_forall_exists_isEtaleCovering_smallEtale
    {V : SmallEtale B S hS} (R : Sieve V) :
    R ∈ SmallEtale.topology B S hS V ↔
      ∀ ⦃U' : SmallEtale B S hS⦄ (h : U' ⟶ V), CompactSpace ((toScheme B S hS).obj U') →
        ∃ (K : Type u) (W : K → SmallEtale B S hS) (ψ : ∀ k, W k ⟶ U'),
          IsEtaleCovering (fun k ↦ (toScheme B S hS).map (ψ k)) ∧ ∀ k, R (ψ k ≫ h) := by
  refine ⟨fun hR U' h _ ↦ ?_, fun H ↦ ?_⟩
  · have hR' := (SmallEtale.topology B S hS).pullback_stable h hR
    choose W g hg hx using fun x ↦ exists_mem_arrows_mem_range B S hS hR' x
    obtain ⟨s, hs⟩ := exists_finite_isEtaleCovering (φ := fun x ↦ (toScheme B S hS).map (g x))
      (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
    exact ⟨s, fun x ↦ W x, fun x ↦ g x, hs, fun x ↦ hg x⟩
  · refine mem_topology_of_jointlySurjective fun x ↦ ?_
    obtain ⟨U', h, hU', y, rfl⟩ := exists_isAffine_mem_range V x
    have := hU'
    obtain ⟨K, W, ψ, hψ, hR⟩ := H h inferInstance
    obtain ⟨k, z, hz⟩ := hψ.exists_mem_range y
    refine ⟨W k, ψ k ≫ h, hR k, z, ?_⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hz]

section Abelian

variable [HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{w}]
  [(SmallEtale.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{w}]
  {F G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{w}} (φ : F ⟶ G)

/-- The form on `SmallEtale.topology B S hS` of
`AlgebraicGeometry.Scheme.epi_iff_forall_exists_isEtaleCovering`. -/
theorem epi_iff_forall_exists_isEtaleCovering_smallEtale :
    Epi φ ↔ ∀ (U : SmallEtale B S hS) [CompactSpace ((toScheme B S hS).obj U)]
      (s : G.obj.obj (op U)),
      ∃ (ι : Type u) (V : ι → SmallEtale B S hS) (f : ∀ i, V i ⟶ U),
        IsEtaleCovering (fun i ↦ (toScheme B S hS).map (f i)) ∧
          ∀ i, ∃ t : F.obj.obj (op (V i)), φ.hom.app (op (V i)) t = G.obj.map (f i).op s := by
  rw [← Sheaf.isLocallySurjective_iff_epi' (φ := φ)]
  constructor
  · intro h U _ s
    obtain ⟨K, W, ψ, hψ, ht⟩ :=
      (mem_smallEtaleTopology_iff_forall_exists_isEtaleCovering_smallEtale _).1
        (Presheaf.imageSieve_mem (SmallEtale.topology B S hS) φ.hom (U := op U) s)
        (𝟙 U) inferInstance
    refine ⟨K, W, ψ, hψ, fun k ↦ ?_⟩
    have hk := ht k
    rw [Category.comp_id] at hk
    exact hk
  · intro h
    refine ⟨fun {U} s ↦ mem_topology_of_jointlySurjective fun x ↦ ?_⟩
    obtain ⟨U', g, hU', y, rfl⟩ := exists_isAffine_mem_range U x
    have := hU'
    obtain ⟨ι, V, f, hf, ht⟩ := h U' (G.obj.map g.op s)
    obtain ⟨k, z, hz⟩ := hf.exists_mem_range y
    obtain ⟨t, ht⟩ := ht k
    refine ⟨V k, f k ≫ g, ⟨t, ?_⟩, z, ?_⟩
    · rw [ht, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    · rw [Functor.map_comp, Scheme.Hom.comp_apply, hz]

end Abelian

/-- The form on `SmallEtale.topology B S hS` of
`AlgebraicGeometry.Scheme.epi_iff_forall_exists_surjective`. -/
theorem epi_iff_forall_exists_surjective_smallEtale
    [HasSheafify (SmallEtale.topology B S hS) (Type w)]
    {F G : Sheaf (SmallEtale.topology B S hS) (Type w)} (φ : F ⟶ G) :
    Epi φ ↔ ∀ (U : SmallEtale B S hS) (s : G.obj.obj (op U)),
      ∃ (V : SmallEtale B S hS) (f : V ⟶ U), Surjective ((toScheme B S hS).map f) ∧
        ∃ t : F.obj.obj (op V), φ.hom.app (op V) t = G.obj.map f.op s := by
  rw [← Sheaf.isLocallySurjective_iff_epi]
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hG := (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  constructor
  · intro h U s
    obtain ⟨ι, P, g, V, σ, f, hg, hσf, hf, hcov, hmono, hdisj⟩ :=
      exists_sigma_of_mem_topology (Presheaf.imageSieve_mem (SmallEtale.topology B S hS)
        φ.hom (U := op U) s)
    choose t ht using hg
    have hFV := (Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)
    have hGV := (Presieve.isSheafFor_iff_generate _).2 (hG _ hcov)
    obtain ⟨t', ht', -⟩ := (Presieve.isSheafFor_arrows_iff _ σ).1 hFV t (by
      intro i j Z gi gj hcomm
      by_cases hij : i = j
      · subst hij
        rw [cancel_mono] at hcomm
        rw [hcomm]
      · exact ((hF _ (hdisj gi gj hij hcomm)).isSeparatedFor.ext fun _ _ hk ↦ hk.elim))
    refine ⟨V, f, hf, t', hGV.isSeparatedFor.ext ?_⟩
    rintro _ _ ⟨i⟩
    rw [← NatTrans.naturality_apply φ.hom (σ i).op t', ht', ht, ← Functor.map_comp_apply,
      ← op_comp, hσf]
  · intro h
    refine ⟨fun {U} s ↦ mem_topology_of_jointlySurjective fun x ↦ ?_⟩
    obtain ⟨V, f, hf, t, ht⟩ := h U s
    obtain ⟨y, hy⟩ := hf.surj x
    exact ⟨V, f, ⟨t, ht⟩, y, hy⟩

end Scheme

end AlgebraicGeometry
