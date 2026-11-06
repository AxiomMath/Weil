module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Algebra.Category.Grp.Basic
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtaleFibreProductInEt
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf
public import Weil.AlgebraicGeometry.Topologies.BoundedSmallEtaleDisjointUnion

/-!
# Covering sieves of the small étale site

A sieve `S` on an object `U` of the small étale site of `X` is *covering* in the sense of
[FK, I.2] if for every morphism `h : U' ⟶ U` of the site there is an étale covering
`(ψₖ : Wₖ ⟶ U')ₖ` (a finite, jointly surjective family of étale morphisms) with `h ∘ ψₖ ∈ S` for
all `k`.

We do not introduce a new notion: the covering sieves are those of Mathlib's small étale
topology `AlgebraicGeometry.Scheme.smallEtaleTopology`, and the stability properties FK lists
(the maximal sieve covers, covering sieves are stable under pull-back and under enlargement)
are the axioms of a Grothendieck topology. This file proves that membership in
`X.smallEtaleTopology U` is exactly FK's condition, where `h` ranges over morphisms whose source
is quasi-compact.

## Main results

* `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff_forall_exists_mem_range`: a sieve covers
  in the small étale topology if and only if every point of `U` is in the image of one of its
  arrows.
* `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff_forall_exists_isEtaleCovering`: a sieve
  `S` on `U` covers in the small étale topology if and only if for every morphism `h : U' ⟶ U`
  with `U'` quasi-compact there is a finite étale covering `ψ` of `U'` with `ψ k ≫ h ∈ S`.

## Implementation notes

FK's category `Et(X)` consists of étale `X`-schemes which are noetherian and separated, hence
quasi-compact; on quasi-compact schemes finite and arbitrary étale coverings define the same
covering sieves. We work on Mathlib's `X.Etale`, all of whose étale `X`-schemes are objects, and
quantify FK's condition over morphisms with quasi-compact source. On a quasi-compact `U` the
condition for `h = 𝟙 U` alone already implies that `S` covers.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A sieve on an object `U` of the small étale site covers if and only if every point of `U`
lies in the image of one of its arrows. -/
lemma mem_smallEtaleTopology_iff_forall_exists_mem_range {U : X.Etale} (S : Sieve U) :
    S ∈ X.smallEtaleTopology U ↔
      ∀ x : U.left, ∃ (W : X.Etale) (g : W ⟶ U), S g ∧ x ∈ Set.range g.left := by
  let ι := Σ W : X.Etale, {g : W ⟶ U // S g}
  have hS : Sieve.ofArrows (fun p : ι ↦ p.1) (fun p ↦ p.2.1) = S := by
    apply le_antisymm
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨p⟩
      exact p.2.2
    · intro W g hg
      exact Sieve.ofArrows_mk _ _ (⟨W, g, hg⟩ : ι)
  have key := ofArrows_mem_smallEtaleTopology_iff (fun p : ι ↦ p.2.1)
  rw [hS] at key
  rw [key, Set.eq_univ_iff_forall]
  simp only [Set.mem_iUnion]
  exact ⟨fun h x ↦ by obtain ⟨p, hp⟩ := h x; exact ⟨p.1, p.2.1, p.2.2, hp⟩,
    fun h x ↦ by obtain ⟨W, g, hg, hx⟩ := h x; exact ⟨⟨W, g, hg⟩, hx⟩⟩

/-- A covering sieve of the small étale site restricts, over a morphism with quasi-compact
source, to a sieve containing a finite étale covering. -/
lemma exists_isEtaleCovering_of_mem_smallEtaleTopology {U : X.Etale} {S : Sieve U}
    (hS : S ∈ X.smallEtaleTopology U) {U' : X.Etale} (h : U' ⟶ U) [CompactSpace U'.left] :
    ∃ (K : Type u) (W : K → X.Etale) (ψ : ∀ k, W k ⟶ U'),
      IsEtaleCovering (fun k ↦ (ψ k).left) ∧ ∀ k, S (ψ k ≫ h) := by
  have hS' := (mem_smallEtaleTopology_iff_forall_exists_mem_range _).1
    (X.smallEtaleTopology.pullback_stable h hS)
  choose W g hg hx using hS'
  obtain ⟨s, hs⟩ := exists_finite_isEtaleCovering (φ := fun x ↦ (g x).left)
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  exact ⟨s, fun x ↦ W x, fun x ↦ g x, hs, fun x ↦ hg x⟩

/-- **Covering sieves of the small étale site** [FK, I.2]. A sieve `S` on an object `U` of the
small étale site of `X` covers in `X.smallEtaleTopology` if and only if for every morphism
`h : U' ⟶ U` of the site with `U'` quasi-compact there is a family `(ψₖ : Wₖ ⟶ U')ₖ` of
morphisms of the site which is an étale covering of `U'` and satisfies `ψₖ ≫ h ∈ S` for all
`k`. -/
@[weil "def_fk102_covering_sieve"]
theorem mem_smallEtaleTopology_iff_forall_exists_isEtaleCovering {U : X.Etale} (S : Sieve U) :
    S ∈ X.smallEtaleTopology U ↔
      ∀ ⦃U' : X.Etale⦄ (h : U' ⟶ U), CompactSpace U'.left →
        ∃ (K : Type u) (W : K → X.Etale) (ψ : ∀ k, W k ⟶ U'),
          IsEtaleCovering (fun k ↦ (ψ k).left) ∧ ∀ k, S (ψ k ≫ h) := by
  refine ⟨fun hS U' h _ ↦ exists_isEtaleCovering_of_mem_smallEtaleTopology hS h, fun H ↦ ?_⟩
  rw [mem_smallEtaleTopology_iff_forall_exists_mem_range]
  intro x
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : U.left.Opens)) (x := x) trivial
  have : IsAffine V := hV
  let V' : X.Etale := MorphismProperty.Over.mk ⊤ (V.ι ≫ U.hom) (by
    have : Etale U.hom := U.prop
    infer_instance)
  let i : V' ⟶ U := MorphismProperty.Over.homMk V.ι rfl
  obtain ⟨K, W, ψ, hψ, hS⟩ := H i (by change CompactSpace V; infer_instance)
  obtain ⟨k, y, hy⟩ := hψ.exists_mem_range ⟨x, hxV⟩
  refine ⟨W k, ψ k ≫ i, hS k, y, ?_⟩
  change V.ι ((ψ k).left y) = x
  rw [hy]
  rfl

/-- On a quasi-compact object `U`, a sieve covers in the small étale topology if and only if it
contains a finite étale covering of `U`. -/
lemma mem_smallEtaleTopology_iff_exists_isEtaleCovering {U : X.Etale} [CompactSpace U.left]
    (S : Sieve U) :
    S ∈ X.smallEtaleTopology U ↔
      ∃ (K : Type u) (W : K → X.Etale) (ψ : ∀ k, W k ⟶ U),
        IsEtaleCovering (fun k ↦ (ψ k).left) ∧ ∀ k, S (ψ k) := by
  refine ⟨fun hS ↦ by simpa using exists_isEtaleCovering_of_mem_smallEtaleTopology hS (𝟙 U),
    fun ⟨K, W, ψ, hψ, hS⟩ ↦ ?_⟩
  have := hψ.finite
  refine X.smallEtaleTopology.superset_covering ?_
    ((isEtaleCovering_left_iff_ofArrows_mem_smallEtaleTopology ψ).1 hψ)
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨k⟩
  exact hS k

end AlgebraicGeometry.Scheme

end

/-! ### Epimorphisms of étale sheaves of abelian groups -/

/-!
# Epimorphisms of étale sheaves of abelian groups

Let `φ : F ⟶ G` be a morphism of sheaves of abelian groups on the small étale site of a
scheme `X`. Then `φ` is an epimorphism if and only if it is *locally surjective*: for every
object `U` and every section `s ∈ G(U)` there is an étale covering `(Uᵢ ⟶ U)` such that each
restriction `s|_{Uᵢ}` lies in the image of `F(Uᵢ)`.

## Main results

* `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff_exists_family`: a sieve on `U` covers in
  the small étale topology if and only if it contains a jointly surjective family of morphisms.
* `AlgebraicGeometry.Scheme.epi_iff_forall_exists_jointly_surjective`: `φ` is an epimorphism if
  and only if every section of `G` is, locally for jointly surjective étale families, in the
  image of `φ`.
* `AlgebraicGeometry.Scheme.epi_iff_forall_exists_isEtaleCovering`: the same with finite étale
  coverings, the condition being required for quasi-compact objects only.

## Implementation notes

The étale site is Mathlib's `X.Etale` with `X.smallEtaleTopology`, whose objects are all
schemes étale over `X` and whose coverings are jointly surjective families. The coverings of
[FK] are finite and its objects noetherian; finite coverings appear in
`epi_iff_forall_exists_isEtaleCovering`, where the condition is asked of the quasi-compact
objects only. This suffices for the converse because every object is covered by affine
open subschemes. The equivalence of epimorphisms with local surjectivity is Mathlib's
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`.

The sheaves take values in `AddCommGrpCat.{w}` for an arbitrary universe `w`, under the
hypotheses that sheafification exists and that the weak equivalences are the locally bijective
morphisms; both hold by Mathlib's instances for `w = u` (via the affine étale site) and for
`w = u + 1`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §2.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A sieve on an object `U` of the small étale site covers if and only if it contains a jointly
surjective family of morphisms, which may be indexed by a type in the universe of `X`. -/
lemma mem_smallEtaleTopology_iff_exists_family {U : X.Etale} (R : Sieve U) :
    R ∈ X.smallEtaleTopology U ↔
      ∃ (ι : Type u) (V : ι → X.Etale) (f : ∀ i, V i ⟶ U),
        ⋃ i, Set.range (f i).left = Set.univ ∧ ∀ i, R (f i) := by
  constructor
  · intro h
    obtain ⟨𝒰, _, p, hU⟩ := (mem_smallGrothendieckTopology _ _).1 h
    refine ⟨𝒰.I₀, fun i ↦ (𝒰.X i).asOverProp X (p i), fun i ↦ (𝒰.f i).asOverProp X, ?_,
      fun i ↦ hU _ _ ⟨i⟩⟩
    exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ⟨_, 𝒰.covers x⟩
  · rintro ⟨ι, V, f, hf, hR⟩
    refine X.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff f).mpr hf)
    rintro W g ⟨Y, h, k, ⟨i⟩, rfl⟩
    exact R.downward_closed (hR i) h

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
  [X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}} (φ : F ⟶ G)

/-- A morphism of étale sheaves of abelian groups is an epimorphism if and only if every section
of the target is, locally for a jointly surjective étale family, in the image of `φ`. -/
theorem epi_iff_forall_exists_jointly_surjective :
    Epi φ ↔ ∀ (U : X.Etale) (s : G.obj.obj (op U)),
      ∃ (ι : Type u) (V : ι → X.Etale) (f : ∀ i, V i ⟶ U),
        ⋃ i, Set.range (f i).left = Set.univ ∧
          ∀ i, ∃ t : F.obj.obj (op (V i)), φ.hom.app (op (V i)) t = G.obj.map (f i).op s := by
  rw [← Sheaf.isLocallySurjective_iff_epi' (φ := φ)]
  constructor
  · intro h U s
    exact (mem_smallEtaleTopology_iff_exists_family _).mp
      (Presheaf.IsLocallySurjective.imageSieve_mem (J := X.smallEtaleTopology) s)
  · intro h
    exact ⟨fun {U} s ↦ (mem_smallEtaleTopology_iff_exists_family _).mpr (h U s)⟩

/-- **Epimorphisms of étale sheaves are the locally surjective morphisms** [FK, I.2]: a morphism
`φ : F ⟶ G` of étale sheaves of abelian groups is an epimorphism if and only if for every
quasi-compact `U` and every `s ∈ G(U)` there is a (finite) étale covering `(Uᵢ ⟶ U)` such that
every `s|_{Uᵢ}` lies in `φ(F(Uᵢ))`. -/
@[weil "lem_fk102_epimorphism_iff_locally_surjective"]
theorem epi_iff_forall_exists_isEtaleCovering :
    Epi φ ↔ ∀ (U : X.Etale) [CompactSpace U.left] (s : G.obj.obj (op U)),
      ∃ (ι : Type u) (V : ι → X.Etale) (f : ∀ i, V i ⟶ U),
        IsEtaleCovering (fun i ↦ (f i).left) ∧
          ∀ i, ∃ t : F.obj.obj (op (V i)), φ.hom.app (op (V i)) t = G.obj.map (f i).op s := by
  constructor
  · intro h U _ s
    obtain ⟨ι, V, f, hf, ht⟩ := (epi_iff_forall_exists_jointly_surjective φ).mp h U s
    obtain ⟨S, hS⟩ := exists_finite_isEtaleCovering (φ := fun i ↦ (f i).left) hf
    exact ⟨S, fun i ↦ V i, fun i ↦ f i, hS, fun i ↦ ht i⟩
  · intro h
    rw [← Sheaf.isLocallySurjective_iff_epi' (φ := φ)]
    refine ⟨fun {U} s ↦ ?_⟩
    let 𝒰 := U.left.affineCover
    let W : 𝒰.I₀ → X.Etale := fun j ↦
      MorphismProperty.Over.mk (P := @Etale) ⊤ (𝒰.f j ≫ U.hom) (by
        have : Etale U.hom := U.prop
        infer_instance)
    let g : ∀ j, W j ⟶ U := fun j ↦ MorphismProperty.Over.homMk (𝒰.f j)
    have hcov : Sieve.ofArrows W g ∈ X.smallEtaleTopology U := by
      rw [ofArrows_mem_smallEtaleTopology_iff]
      exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr ⟨_, 𝒰.covers x⟩
    refine X.smallEtaleTopology.transitive hcov _ ?_
    rintro Y k ⟨Z, l, m, ⟨j⟩, rfl⟩
    rw [Sieve.pullback_comp]
    refine X.smallEtaleTopology.pullback_stable _ ?_
    have : CompactSpace (W j).left := inferInstanceAs (CompactSpace (𝒰.X j))
    obtain ⟨ι, V, f, hf, ht⟩ := h (W j) (G.obj.map (g j).op s)
    have := hf.finite
    refine X.smallEtaleTopology.superset_covering ?_
      ((isEtaleCovering_left_iff_ofArrows_mem_smallEtaleTopology f).mp hf)
    rintro T a ⟨T', b, c, ⟨i⟩, rfl⟩
    obtain ⟨t, ht⟩ := ht i
    refine ⟨F.obj.map b.op t, ?_⟩
    rw [NatTrans.naturality_apply φ.hom b.op t, ht]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

end AlgebraicGeometry.Scheme

end

/-! ### Common refinements of étale coverings -/

/-!
# Common refinements of étale coverings

Given finitely many étale coverings `𝔘ₖ = (Uₖ,ᵢ ⟶ U)_{i ∈ Iₖ}` of a scheme `U`, there is an
étale covering `𝔚` of `U` together with a refinement map `𝔚 ⟶ 𝔘ₖ` for every `k`, i.e. an
index map `σₖ` and `U`-morphisms `𝔚ⱼ ⟶ Uₖ,σₖ(j)`. The covering `𝔚` is given by the iterated
fibre products `U₁,ᵢ₁ ×_U ⋯ ×_U Uᵣ,ᵢᵣ`, and the refinement maps are the projections.

## Main results

* `AlgebraicGeometry.Scheme.IsEtaleCovering.pullback`: the fibre products
  `Vᵢ ×_U Wⱼ ⟶ U` of two étale coverings form an étale covering of `U`.
* `AlgebraicGeometry.Scheme.exists_isEtaleCovering_common_refinement`: any finite family of
  étale coverings of `U` has a common refinement which is an étale covering.

## Implementation notes

A refinement map `(σ, (φⱼ)ⱼ)` from `(ψⱼ : Wⱼ ⟶ U)ⱼ` to `(φᵢ : Vᵢ ⟶ U)ᵢ` is stated
explicitly: an index map `σ` and morphisms `gⱼ : Wⱼ ⟶ V (σ j)` with `gⱼ ≫ φ (σ j) = ψⱼ`.
This is the data of Mathlib's `CategoryTheory.PreZeroHypercover.Hom`. The family of coverings
may be indexed by any finite type, including the empty one.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The pairwise fibre products of the members of two étale coverings of `U` form an étale
covering of `U`. -/
lemma IsEtaleCovering.pullback {U : Scheme.{u}} {ι κ : Type*} {V : ι → Scheme.{u}}
    {W : κ → Scheme.{u}} {φ : ∀ i, V i ⟶ U} {ψ : ∀ j, W j ⟶ U}
    (hφ : IsEtaleCovering φ) (hψ : IsEtaleCovering ψ) :
    IsEtaleCovering (fun p : ι × κ ↦ Limits.pullback.fst (φ p.1) (ψ p.2) ≫ φ p.1) := by
  have := hφ.finite
  have := hψ.finite
  have := hφ.etale
  have := hψ.etale
  refine ⟨inferInstance, fun p ↦ inferInstance, ?_⟩
  rw [iUnion_range_eq_univ_iff]
  intro x
  obtain ⟨i, a, rfl⟩ := hφ.exists_mem_range x
  obtain ⟨j, b, hb⟩ := hψ.exists_mem_range (φ i a)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback a b hb.symm
  exact ⟨(i, j), z, by simp [hz]⟩

/-- **Common refinement of étale coverings.** For a finite family `(φ k)ₖ` of étale coverings
of `U`, there is an étale covering `ψ` of `U` together with a refinement map from `ψ` to each
`φ k`: an index map `σ` and `U`-morphisms `g j : W j ⟶ V k (σ j)`. -/
@[weil "lem_fk102_coverings_common_refinement"]
theorem exists_isEtaleCovering_common_refinement {U : Scheme.{u}} {K : Type w} [Finite K]
    {ι : K → Type v} {V : ∀ k, ι k → Scheme.{u}} {φ : ∀ k i, V k i ⟶ U}
    (hφ : ∀ k, IsEtaleCovering (φ k)) :
    ∃ (κ : Type v) (W : κ → Scheme.{u}) (ψ : ∀ j, W j ⟶ U), IsEtaleCovering ψ ∧
      ∀ k, ∃ (σ : κ → ι k) (g : ∀ j, W j ⟶ V k (σ j)), ∀ j, g j ≫ φ k (σ j) = ψ j := by
  classical
  have := Fintype.ofFinite K
  suffices H : ∀ s : Finset K, ∃ (κ : Type v) (W : κ → Scheme.{u}) (ψ : ∀ j, W j ⟶ U),
      IsEtaleCovering ψ ∧ ∀ k ∈ s, ∃ (σ : κ → ι k) (g : ∀ j, W j ⟶ V k (σ j)),
        ∀ j, g j ≫ φ k (σ j) = ψ j by
    obtain ⟨κ, W, ψ, hψ, h⟩ := H Finset.univ
    exact ⟨κ, W, ψ, hψ, fun k ↦ h k (Finset.mem_univ k)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨PUnit, fun _ ↦ U, fun _ ↦ 𝟙 U, ⟨inferInstance, fun _ ↦ inferInstance, ?_⟩, by simp⟩
    rw [iUnion_range_eq_univ_iff]
    exact fun x ↦ ⟨PUnit.unit, x, rfl⟩
  | insert a s _ ih =>
    obtain ⟨κ, W, ψ, hψ, h⟩ := ih
    refine ⟨κ × ι a, fun p ↦ Limits.pullback (ψ p.1) (φ a p.2),
      fun p ↦ Limits.pullback.fst (ψ p.1) (φ a p.2) ≫ ψ p.1, hψ.pullback (hφ a), ?_⟩
    intro k hk
    by_cases hka : k = a
    · subst hka
      exact ⟨fun p ↦ p.2, fun p ↦ Limits.pullback.snd _ _,
        fun p ↦ (Limits.pullback.condition).symm⟩
    · obtain ⟨σ, g, hg⟩ := h k ((Finset.mem_insert.mp hk).resolve_left hka)
      exact ⟨fun p ↦ σ p.1, fun p ↦ Limits.pullback.fst _ _ ≫ g p.1,
        fun p ↦ by simp [hg]⟩

end AlgebraicGeometry.Scheme

end

/-! ### The covering form of the sheaf condition on `Et(S)` -/

/-!
# The covering form of the sheaf condition on `Et(S)`

Let `F` be a presheaf of sets (or of abelian groups) on the étale category `Et(S)` of noetherian
separated étale `S`-schemes. Freitag and Kiehl call `F` a sheaf if

* a) for every finite family of open immersions `iₖ : Uₖ ⟶ W` of `Et(S)` with pairwise disjoint
  images covering `W`, the map `F(W) → ∏ₖ F(Uₖ)` is bijective, and
* b) for every surjective morphism `φ : U ⟶ V` of `Et(S)`, the map `φ^* : F(V) → F(U)` is
  injective with image the sections `s` with `a^* s = b^* s` whenever `φ ∘ a = φ ∘ b`.

This file proves that `F` is a sheaf in this sense if and only if, for every étale covering
`(φᵢ : Uᵢ ⟶ U)ᵢ` of an object `U` by morphisms of `Et(S)`, the map
`F(U) → {(sᵢ) ∈ ∏ᵢ F(Uᵢ) | pᵢⱼ^* sᵢ = qᵢⱼ^* sⱼ in F(Uᵢ ×_U Uⱼ)}` is bijective.

## Main definitions

* `CategoryTheory.Presieve.Arrows.toPullbackCompatible`: for a family `π : ∀ i, X i ⟶ B`, the
  map `s ↦ (π i ^* s)ᵢ` from `P(B)` to the families compatible on pairwise fibre products.
* `AlgebraicGeometry.EtalePresheaf.IsEtaleSheaf`: the sheaf condition a) + b) on a presheaf of
  sets on `Et(S)`.

## Main results

* `CategoryTheory.Presieve.isSheafFor_ofArrows_iff_bijective_toPullbackCompatible`: a presheaf
  is a sheaf for the presieve generated by a family exactly when the map above is bijective.
* `AlgebraicGeometry.EtalePresheaf.isEtaleSheaf_iff_bijective_toPullbackCompatible`: a presheaf
  of sets on `Et(S)` is a sheaf iff the covering condition holds for every étale covering.
* `AlgebraicGeometry.EtalePresheaf.isEtaleSheaf_forget_iff_bijective_toPullbackCompatible`: the
  same for presheaves of abelian groups, whose sheaf condition is that of the underlying
  presheaf of sets.

## Implementation notes

The fibre products `Uᵢ ×_U Uⱼ` in the covering condition are the categorical fibre products of
`Et(S)`, which exist by `AlgebraicGeometry.SmallNoetherianSeparatedEtale.hasPullbacks`. The
index type of a covering is an arbitrary finite type, of any universe.

The proof that a sheaf satisfies the covering condition replaces the covering by the single
surjective morphism `∐ᵢ Uᵢ ⟶ U`; the compatibility needed for condition b) is checked on
`(∐ᵢ Uᵢ) ×_U (∐ᵢ Uᵢ)`, which is the disjoint union of the open subschemes `Uᵢ ×_U Uⱼ`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Presieve

variable {C : Type*} [Category C] {B : C} {I : Type*} {X : I → C}

/-- For a family `π : ∀ i, X i ⟶ B`, the map `s ↦ (π i ^* s)ᵢ` from `P(B)` to the families of
elements which agree on the pairwise fibre products `X i ×_B X j`. -/
def Arrows.toPullbackCompatible (P : Cᵒᵖ ⥤ Type*) (π : ∀ i, X i ⟶ B)
    [(ofArrows X π).HasPairwisePullbacks] (s : P.obj (op B)) :
    Subtype (Arrows.PullbackCompatible P π) :=
  ⟨fun i ↦ P.map (π i).op s, fun i j ↦ by
    simp only [← Functor.map_comp_apply, ← op_comp, pullback.condition]⟩

@[simp]
lemma Arrows.toPullbackCompatible_coe (P : Cᵒᵖ ⥤ Type*) (π : ∀ i, X i ⟶ B)
    [(ofArrows X π).HasPairwisePullbacks] (s : P.obj (op B)) (i : I) :
    (Arrows.toPullbackCompatible P π s).1 i = P.map (π i).op s :=
  rfl

/-- A presheaf is a sheaf for the presieve generated by a family `π` if and only if the map from
sections to families compatible on pairwise fibre products is bijective. -/
theorem isSheafFor_ofArrows_iff_bijective_toPullbackCompatible (P : Cᵒᵖ ⥤ Type*)
    (π : ∀ i, X i ⟶ B) [(ofArrows X π).HasPairwisePullbacks] :
    IsSheafFor P (ofArrows X π) ↔ Function.Bijective (Arrows.toPullbackCompatible P π) := by
  rw [isSheafFor_ofArrows_iff_bijective_toCompabible]
  let e : Subtype (Arrows.Compatible P π) ≃ Subtype (Arrows.PullbackCompatible P π) :=
    Equiv.subtypeEquivRight fun x ↦ Arrows.pullbackCompatible_iff P π x
  have : Arrows.toPullbackCompatible P π = e ∘ Arrows.toCompatible P π := rfl
  rw [this, e.comp_bijective]

end CategoryTheory.Presieve

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Every morphism of `Et(S)` whose underlying morphism of schemes is an open immersion is a
monomorphism. -/
lemma mono_of_isOpenImmersion {U V : SmallNoetherianSeparatedEtale B S hS} (f : U ⟶ V)
    [IsOpenImmersion ((toScheme B S hS).map f)] : Mono f :=
  (toScheme B S hS).mono_of_mono_map inferInstance

variable {ι : Type u} [Finite ι] (U : ι → SmallNoetherianSeparatedEtale B S hS)

/-- The images of two distinct members of a finite disjoint union in `Et(S)` are disjoint. -/
lemma disjoint_range_toScheme_map_sigmaι {i j : ι} (h : i ≠ j) :
    Disjoint (Set.range ((toScheme B S hS).map (sigmaι U i)))
      (Set.range ((toScheme B S hS).map (sigmaι U j))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  rw [toScheme_map_sigmaι, toScheme_map_sigmaι] at *
  obtain ⟨rfl⟩ := (sigmaι_eq_iff _ _ _ _ _).mp hy
  exact h rfl

/-- The images of the members of a finite disjoint union in `Et(S)` cover it. -/
lemma iUnion_range_toScheme_map_sigmaι :
    ⋃ i, Set.range ((toScheme B S hS).map (sigmaι U i)) = Set.univ := by
  refine Set.eq_univ_of_forall fun z ↦ ?_
  obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk fun i ↦ (toScheme B S hS).obj (U i)).surjective z
  exact Set.mem_iUnion.mpr ⟨i, x, by rw [toScheme_map_sigmaι, sigmaMk_mk]; rfl⟩

end SmallNoetherianSeparatedEtale

namespace EtalePresheaf

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Sheaves on `Et(S)`** (FK I.2.4). A presheaf of sets `F` on `Et(S)` is an *étale sheaf* if
* a) for every object `W` and every finite family `(iₖ : Uₖ ⟶ W)ₖ` of morphisms which are open
  immersions with pairwise disjoint images covering `W`, the map `F(W) → ∏ₖ F(Uₖ)` is
  bijective (for the empty family, `W` is empty and `F(W)` is a point), and
* b) for every surjective morphism `φ : U ⟶ V`, the map `φ^* : F(V) → F(U)` is injective, and
  its image is the set of sections `s` with `a^* s = b^* s` for all morphisms `a b : W ⟶ U`
  with `a ≫ φ = b ≫ φ`. -/
@[weil "def_fk102_etale_sheaf"]
structure IsEtaleSheaf (F : EtalePresheaf B S hS (Type v)) : Prop where
  /-- Condition a): finite disjoint unions. -/
  bijective_of_disjoint (W : SmallNoetherianSeparatedEtale B S hS) (n : ℕ)
    (U : Fin n → SmallNoetherianSeparatedEtale B S hS) (i : ∀ k, U k ⟶ W)
    (open_immersion : ∀ k, IsOpenImmersion ((toScheme B S hS).map (i k)))
    (disjoint : Pairwise fun k l ↦ Disjoint (Set.range ((toScheme B S hS).map (i k)))
      (Set.range ((toScheme B S hS).map (i l))))
    (cover : ⋃ k, Set.range ((toScheme B S hS).map (i k)) = Set.univ) :
    Function.Bijective fun (s : F.obj (op W)) (k : Fin n) ↦ F.map (i k).op s
  /-- Condition b): descent along a surjective morphism. -/
  injective_and_range_eq {U V : SmallNoetherianSeparatedEtale B S hS} (φ : U ⟶ V)
    (surjective : Function.Surjective ((toScheme B S hS).map φ)) :
    Function.Injective (F.map φ.op) ∧
      Set.range (F.map φ.op) = {s | ∀ (W : SmallNoetherianSeparatedEtale B S hS)
        (a b : W ⟶ U), a ≫ φ = b ≫ φ → F.map a.op s = F.map b.op s}

variable {F : EtalePresheaf B S hS (Type v)}

/-- Condition a) for a finite family indexed by an arbitrary finite type. -/
lemma IsEtaleSheaf.existsUnique_of_disjoint (hF : IsEtaleSheaf F)
    {W : SmallNoetherianSeparatedEtale B S hS} {κ : Type*} [Finite κ]
    (U : κ → SmallNoetherianSeparatedEtale B S hS) (i : ∀ k, U k ⟶ W)
    (hi : ∀ k, IsOpenImmersion ((toScheme B S hS).map (i k)))
    (hd : Pairwise fun k l ↦ Disjoint (Set.range ((toScheme B S hS).map (i k)))
      (Set.range ((toScheme B S hS).map (i l))))
    (hc : ⋃ k, Set.range ((toScheme B S hS).map (i k)) = Set.univ)
    (x : ∀ k, F.obj (op (U k))) : ∃! s, ∀ k, F.map (i k).op s = x k := by
  let e := Finite.equivFin κ
  have hc' : ⋃ k, Set.range ((toScheme B S hS).map (i (e.symm k))) = Set.univ := by
    rw [← hc]
    exact e.symm.surjective.iUnion_comp (fun k ↦ Set.range ((toScheme B S hS).map (i k)))
  have hb := hF.bijective_of_disjoint W (Nat.card κ) (fun k ↦ U (e.symm k))
    (fun k ↦ i (e.symm k)) (fun k ↦ hi _) (fun k l hkl ↦ hd (e.symm.injective.ne hkl)) hc'
  obtain ⟨s, hs, hu⟩ := (Function.bijective_iff_existsUnique _).mp hb fun k ↦ x (e.symm k)
  refine ⟨s, fun l ↦ ?_, fun s' hs' ↦ hu s' (funext fun k ↦ hs' _)⟩
  obtain ⟨k, rfl⟩ := e.symm.surjective l
  exact congr_fun hs k

/-- The covering condition for an étale covering by morphisms of `Et(S)`, indexed by `ι`. -/
private abbrev CoveringCondition (F : EtalePresheaf B S hS (Type v)) (ι : Type w) : Prop :=
  ∀ ⦃U : SmallNoetherianSeparatedEtale B S hS⦄ (V : ι → SmallNoetherianSeparatedEtale B S hS)
    (φ : ∀ i, V i ⟶ U), Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (φ i)) →
      Function.Bijective (Presieve.Arrows.toPullbackCompatible F φ)

/-- The covering condition for the empty covering: `F` of an empty object is a subsingleton. -/
private lemma subsingleton_of_isEmpty (hC : CoveringCondition.{w} F PEmpty.{w + 1})
    (Z : SmallNoetherianSeparatedEtale B S hS) [IsEmpty ((toScheme B S hS).obj Z)] :
    Subsingleton (F.obj (op Z)) := by
  have hcov : Scheme.IsEtaleCovering
      (fun i : PEmpty.{w + 1} ↦ (toScheme B S hS).map ((fun i ↦ i.elim) i : (PEmpty.elim i :
        SmallNoetherianSeparatedEtale B S hS) ⟶ Z)) :=
    ⟨inferInstance, fun i ↦ i.elim, by
      rw [Set.iUnion_of_empty]; exact (Set.univ_eq_empty_iff.mpr inferInstance).symm⟩
  refine ⟨fun a b ↦ (hC _ _ hcov).1 (Subtype.ext (funext fun i ↦ i.elim))⟩

/-- The sheaf condition implies the covering condition. -/
private lemma isSheafFor_of_isEtaleSheaf (hF : IsEtaleSheaf F)
    {U : SmallNoetherianSeparatedEtale B S hS} {ι : Type w}
    (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U)
    (hcov : Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (φ i))) :
    Presieve.IsSheafFor F (Presieve.ofArrows V φ) := by
  have := hcov.finite
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let J := ULift.{u} (Fin (Nat.card ι))
  let e : J ≃ ι := Equiv.ulift.trans (Finite.equivFin ι).symm
  let V' : J → SmallNoetherianSeparatedEtale B S hS := fun j ↦ V (e j)
  -- The disjoint union `U' = ∐ⱼ Vⱼ` and the morphism `ψ : U' ⟶ U`.
  let U' := sigmaObj V'
  let ψs : (∐ fun j ↦ (toScheme B S hS).obj (V' j)) ⟶ (toScheme B S hS).obj U :=
    Sigma.desc fun j ↦ (toScheme B S hS).map (φ (e j))
  have hψs : ψs ≫ structureMorphism U = structureMorphism U' := by
    change _ = Sigma.desc fun j ↦ structureMorphism (V' j)
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp only [ψs, Sigma.ι_desc_assoc, Sigma.ι_desc, toScheme_map_comp_structureMorphism]
  let ψ : U' ⟶ U := (homEquiv _ _).symm ⟨ψs, hψs⟩
  have hψ' : (toScheme B S hS).map ψ = ψs := rfl
  have hψ (j : J) : sigmaι V' j ≫ ψ = φ (e j) := by
    apply hom_ext
    rw [Functor.map_comp, hψ']
    exact Sigma.ι_desc _ _
  have hψsurj : Function.Surjective ((toScheme B S hS).map ψ) := by
    intro y
    obtain ⟨i, z, hz⟩ := hcov.exists_mem_range y
    obtain ⟨j, rfl⟩ := e.surjective i
    refine ⟨(toScheme B S hS).map (sigmaι V' j) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hψ]
    exact hz
  have hdσ : Pairwise fun j k ↦ Disjoint (Set.range ((toScheme B S hS).map (sigmaι V' j)))
      (Set.range ((toScheme B S hS).map (sigmaι V' k))) :=
    fun j k h ↦ disjoint_range_toScheme_map_sigmaι V' h
  have hcσ := iUnion_range_toScheme_map_sigmaι V'
  have haU' := hF.existsUnique_of_disjoint V' (sigmaι V') (fun _ ↦ inferInstance) hdσ hcσ
  obtain ⟨s', hs', hu'⟩ := haU' fun j ↦ x (e j)
  obtain ⟨hinj, hrange⟩ := hF.injective_and_range_eq ψ hψsurj
  -- The fibre product `U' ×_U U'` and its decomposition into the `Vⱼ ×_U Vₖ`.
  let P := pullbackObj ψ ψ
  let p := pullbackFst ψ ψ
  let q := pullbackSnd ψ ψ
  let Q : J × J → SmallNoetherianSeparatedEtale B S hS :=
    fun jk ↦ pullbackObj (φ (e jk.1)) (φ (e jk.2))
  have e₁ (j : J) : (toScheme B S hS).map (φ (e j)) ≫ 𝟙 _ =
      (toScheme B S hS).map (sigmaι V' j) ≫ (toScheme B S hS).map ψ := by
    rw [Category.comp_id, ← Functor.map_comp, hψ]
  let m : ∀ jk : J × J, Q jk ⟶ P := fun jk ↦ (homEquiv _ _).symm
    ⟨pullback.map _ _ _ _ ((toScheme B S hS).map (sigmaι V' jk.1))
      ((toScheme B S hS).map (sigmaι V' jk.2)) (𝟙 _) (e₁ jk.1) (e₁ jk.2), by
      change _ ≫ pullback.fst ((toScheme B S hS).map ψ) ((toScheme B S hS).map ψ) ≫
        structureMorphism U' = pullback.fst _ _ ≫ structureMorphism (V' jk.1)
      rw [pullback.lift_fst_assoc, Category.assoc,
        toScheme_map_sigmaι_comp_structureMorphism]⟩
  have hm (jk : J × J) : (toScheme B S hS).map (m jk) =
      pullback.map _ _ _ _ ((toScheme B S hS).map (sigmaι V' jk.1))
        ((toScheme B S hS).map (sigmaι V' jk.2)) (𝟙 _) (e₁ jk.1) (e₁ jk.2) := rfl
  have hmp (jk : J × J) : m jk ≫ p = pullbackFst _ _ ≫ sigmaι V' jk.1 := by
    apply hom_ext
    rw [Functor.map_comp, Functor.map_comp]
    exact pullback.lift_fst _ _ _
  have hmq (jk : J × J) : m jk ≫ q = pullbackSnd _ _ ≫ sigmaι V' jk.2 := by
    apply hom_ext
    rw [Functor.map_comp, Functor.map_comp]
    exact pullback.lift_snd _ _ _
  have hrm (jk : J × J) : Set.range ((toScheme B S hS).map (m jk)) =
      pullback.fst ((toScheme B S hS).map ψ) ((toScheme B S hS).map ψ) ⁻¹'
          Set.range ((toScheme B S hS).map (sigmaι V' jk.1)) ∩
        pullback.snd ((toScheme B S hS).map ψ) ((toScheme B S hS).map ψ) ⁻¹'
          Set.range ((toScheme B S hS).map (sigmaι V' jk.2)) := by
    rw [hm]
    exact Scheme.Pullback.range_map _ _ _ _ _ _ _ (e₁ jk.1) (e₁ jk.2)
  have hmo (jk : J × J) : IsOpenImmersion ((toScheme B S hS).map (m jk)) := by
    rw [hm]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      (by rw [← Functor.map_comp, hψ]) (by rw [← Functor.map_comp, hψ])
  have hmd : Pairwise fun jk jk' ↦ Disjoint (Set.range ((toScheme B S hS).map (m jk)))
      (Set.range ((toScheme B S hS).map (m jk'))) := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ h
    rw [hrm, hrm]
    by_cases hj : j = j'
    · have hk : k ≠ k' := fun hk ↦ h (by rw [hj, hk])
      exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
        ((hdσ hk).preimage _)
    · exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left ((hdσ hj).preimage _)
  have hmc : ⋃ jk, Set.range ((toScheme B S hS).map (m jk)) = Set.univ := by
    refine Set.eq_univ_of_forall fun z ↦ ?_
    have h1 : _ ∈ ⋃ j, Set.range ((toScheme B S hS).map (sigmaι V' j)) :=
      hcσ ▸ Set.mem_univ (pullback.fst ((toScheme B S hS).map ψ) ((toScheme B S hS).map ψ) z)
    have h2 : _ ∈ ⋃ j, Set.range ((toScheme B S hS).map (sigmaι V' j)) :=
      hcσ ▸ Set.mem_univ (pullback.snd ((toScheme B S hS).map ψ) ((toScheme B S hS).map ψ) z)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h1
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h2
    exact Set.mem_iUnion.mpr ⟨(j, k), by rw [hrm]; exact ⟨hj, hk⟩⟩
  -- `s'` agrees on the two projections `U' ×_U U' ⟶ U'`.
  have hpq : F.map p.op s' = F.map q.op s' := by
    obtain ⟨s₀, -, hu₀⟩ := hF.existsUnique_of_disjoint Q m hmo hmd hmc
      fun jk ↦ F.map (m jk ≫ p).op s'
    have h₁ := hu₀ (F.map p.op s') fun jk ↦ by
      rw [op_comp, Functor.map_comp_apply]
    have h₂ := hu₀ (F.map q.op s') fun jk ↦ by
      rw [← Functor.map_comp_apply, ← op_comp, hmq, hmp, op_comp, op_comp,
        Functor.map_comp_apply, Functor.map_comp_apply, hs', hs']
      exact (hx _ _ _ _ _ (isPullback_pullbackFst_pullbackSnd _ _).w).symm
    exact h₁.trans h₂.symm
  have hs'mem : s' ∈ Set.range (F.map ψ.op) := by
    rw [hrange]
    intro W a b hab
    let c := (isPullback_pullbackFst_pullbackSnd ψ ψ).lift a b hab
    have hca : c ≫ p = a := (isPullback_pullbackFst_pullbackSnd ψ ψ).lift_fst a b hab
    have hcb : c ≫ q = b := (isPullback_pullbackFst_pullbackSnd ψ ψ).lift_snd a b hab
    rw [← hca, ← hcb, op_comp, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply, hpq]
  obtain ⟨t, ht⟩ := hs'mem
  refine ⟨t, fun i ↦ ?_, fun t' ht' ↦ hinj ?_⟩
  · obtain ⟨j, rfl⟩ := e.surjective i
    rw [← hψ, op_comp, Functor.map_comp_apply, ht, hs']
  · refine (hu' _ fun j ↦ ?_).trans ht.symm
    rw [← Functor.map_comp_apply, ← op_comp, hψ, ht']

/-- **The covering form of the sheaf condition** (FK I.2, p. 20). A presheaf of sets `F` on
`Et(S)` is an étale sheaf if and only if, for every object `U` of `Et(S)` and every family
`(φᵢ : Uᵢ ⟶ U)ᵢ` of morphisms of `Et(S)` which is an étale covering of `U`, the map
`F(U) → {(sᵢ) ∈ ∏ᵢ F(Uᵢ) | pᵢⱼ^* sᵢ = qᵢⱼ^* sⱼ in F(Uᵢ ×_U Uⱼ) for all i, j}`,
`s ↦ (φᵢ^* s)ᵢ`, is bijective, where `pᵢⱼ, qᵢⱼ` are the projections of `Uᵢ ×_U Uⱼ`. -/
@[weil "lem_fk102_sheaf_iff_covering_condition"]
theorem isEtaleSheaf_iff_bijective_toPullbackCompatible (F : EtalePresheaf B S hS (Type v)) :
    IsEtaleSheaf F ↔
      ∀ ⦃U : SmallNoetherianSeparatedEtale B S hS⦄ ⦃ι : Type w⦄
        (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U),
        Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (φ i)) →
          Function.Bijective (Presieve.Arrows.toPullbackCompatible F φ) := by
  refine ⟨fun hF U ι V φ hcov ↦ ?_, fun hC ↦ ?_⟩
  · exact (Presieve.isSheafFor_ofArrows_iff_bijective_toPullbackCompatible F φ).mp
      (isSheafFor_of_isEtaleSheaf hF V φ hcov)
  have hS' {U : SmallNoetherianSeparatedEtale B S hS} {ι : Type w}
      (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U)
      (hcov : Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (φ i))) :=
    (Presieve.isSheafFor_arrows_iff F φ).mp
      ((Presieve.isSheafFor_ofArrows_iff_bijective_toPullbackCompatible F φ).mpr
        (hC V φ hcov))
  refine ⟨fun W n U i hi hd hc ↦ ?_, fun {U V} φ hφ ↦ ?_⟩
  · -- Condition a).
    have hcov : Scheme.IsEtaleCovering
        (fun k : ULift.{w} (Fin n) ↦ (toScheme B S hS).map (i k.down)) :=
      ⟨inferInstance, fun _ ↦ inferInstance, by
        rw [← hc]
        exact ULift.down_surjective.iUnion_comp
          (fun k : Fin n ↦ Set.range ((toScheme B S hS).map (i k)))⟩
    rw [Function.bijective_iff_existsUnique]
    intro x
    obtain ⟨t, ht, hu⟩ := hS' (fun k : ULift.{w} (Fin n) ↦ U k.down) (fun k ↦ i k.down) hcov
      (fun k ↦ x k.down) (by
        intro k l Z gk gl hgl
        by_cases hkl : k.down = l.down
        · obtain ⟨k⟩ := k
          obtain ⟨l⟩ := l
          obtain rfl : k = l := hkl
          have := hi k
          have := mono_of_isOpenImmersion (i k)
          rw [cancel_mono] at hgl
          rw [hgl]
        · have : IsEmpty ((toScheme B S hS).obj Z) := by
            refine ⟨fun z ↦ Set.disjoint_left.mp (hd hkl) ⟨(toScheme B S hS).map gk z, rfl⟩
              ⟨(toScheme B S hS).map gl z, ?_⟩⟩
            rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Functor.map_comp,
              ← Functor.map_comp, hgl]
          have := subsingleton_of_isEmpty (fun _ V φ hcov ↦ hC V φ hcov) Z
          exact Subsingleton.elim _ _)
    exact ⟨t, funext fun k ↦ ht ⟨k⟩, fun t' ht' ↦ hu t' fun k ↦ congr_fun ht' k.down⟩
  · -- Condition b).
    have hcov : Scheme.IsEtaleCovering
        (fun _ : PUnit.{w + 1} ↦ (toScheme B S hS).map φ) :=
      ⟨inferInstance, fun _ ↦ inferInstance, by
        rw [Set.iUnion_const]; exact Set.range_eq_univ.mpr hφ⟩
    have h := hS' (fun _ : PUnit.{w + 1} ↦ U) (fun _ ↦ φ) hcov
    refine ⟨fun t t' htt ↦ ?_, ?_⟩
    · obtain ⟨t₀, -, hu⟩ := h (fun _ ↦ F.map φ.op t)
        (Presieve.Arrows.toCompatible F (fun _ : PUnit.{w + 1} ↦ φ) t).property
      exact (hu t fun _ ↦ rfl).trans (hu t' fun _ ↦ htt.symm).symm
    · ext s
      refine ⟨?_, fun hs ↦ ?_⟩
      · rintro ⟨t, rfl⟩ W a b hab
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
          ← op_comp, hab]
      · obtain ⟨t, ht, -⟩ := h (fun _ ↦ s) fun _ _ Z a b hab ↦ hs Z a b hab
        exact ⟨t, ht PUnit.unit⟩

/-- **The covering form of the sheaf condition for presheaves of abelian groups** (FK I.2,
p. 20). A presheaf of abelian groups on `Et(S)` is an étale sheaf (its underlying presheaf of
sets is one) if and only if the covering condition holds for every étale covering. -/
@[weil "lem_fk102_sheaf_iff_covering_condition"]
theorem isEtaleSheaf_forget_iff_bijective_toPullbackCompatible
    (F : EtalePresheaf B S hS AddCommGrpCat.{v}) :
    IsEtaleSheaf (F ⋙ forget AddCommGrpCat) ↔
      ∀ ⦃U : SmallNoetherianSeparatedEtale B S hS⦄ ⦃ι : Type w⦄
        (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U),
        Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (φ i)) →
          Function.Bijective
            (Presieve.Arrows.toPullbackCompatible (F ⋙ forget AddCommGrpCat) φ) :=
  isEtaleSheaf_iff_bijective_toPullbackCompatible _

end EtalePresheaf

end AlgebraicGeometry

end
