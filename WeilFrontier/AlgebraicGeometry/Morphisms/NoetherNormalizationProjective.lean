module

public import StacksFrontier.AlgebraicGeometry.Variety.Projective.FiniteProjection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLinesOfClosedSubset
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.LinearAlgebra.SubspaceUnionCodim
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# Projective Noether normalization

Let `k` be an infinite field and `X` a projective scheme over `k` of dimension `d`. Then there is
a finite surjective morphism `X ⟶ ℙ^d_k` over `k`.

Embed `X` as a closed subscheme of `𝐏(V) = Proj (Sym_k V)` for a finite-dimensional `V`. A linear
form not vanishing at a chosen point of each of the finitely many irreducible components of a
closed subset `Z ⊆ 𝐏(V)` cuts `Z` in a nowhere dense closed subset, hence lowers its dimension;
such a form exists because `k` is infinite and a vector space over an infinite field is not a
finite union of proper subspaces. After `d + 1` steps one obtains a subspace `W ≤ V` of dimension
`d + 1` whose zero locus misses `X`. The linear projection `𝐏(V) ⇢ 𝐏(W)` away from that zero locus
is defined on `X` and finite there, being affine and proper. A finite morphism does not raise
dimension, so its image is a closed subset of dimension `d` of the irreducible `d`-dimensional
`𝐏(W)`, which is all of `𝐏(W)`. A basis of `W` identifies `𝐏(W)` with `ℙ^d_k`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_finrank_eq_disjoint_linearSubspace_of_infinite`:
  over an infinite field, a closed subset of `𝐏(V)` of dimension `< e` misses the zero locus of
  some `e`-dimensional space of linear forms.
* `AlgebraicGeometry.topologicalKrullDim_le_range_of_isFinite`: a finite morphism of schemes
  locally of finite type over a field does not raise dimension: `dim X ≤ dim f(X)`.
* `AlgebraicGeometry.surjective_of_isFinite_of_topologicalKrullDim_eq`: a finite morphism over a
  field from a scheme of dimension `d` to an irreducible scheme of dimension `d` is surjective.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isFinite_surjective_projection`: the
  Noether normalization of a closed subscheme of `𝐏(V)` by a linear projection.
* `AlgebraicGeometry.exists_isFinite_surjective_projectiveSpaceOver`: **projective Noether
  normalization.** A projective `k`-scheme of dimension `d`, `k` infinite, admits a finite
  surjective morphism to `ℙ^d_k` over `k`.

## Implementation notes

"Projective over `k`" is `AlgebraicGeometry.IsProjective` (Stacks Tag 01W8), the notion used
throughout this project; over the affine base `Spec k` it is equivalent to a closed immersion into
some `ℙᴺ_k` over `k`, and
`AlgebraicGeometry.exists_isFinite_surjective_projectiveSpaceOver_of_isProjectiveMorphism` states
the result in that form. The projective space `ℙ^d_k` is
`AlgebraicGeometry.projectiveSpaceOver d (Spec k)` (Stacks Tag 01NF) with its structure morphism.
The dimension of `X` is `topologicalKrullDim X`. No irreducibility, reducedness or smoothness of
`X` is assumed; the surjectivity is obtained from dimension theory rather than from flatness.

The infinitude of `k` is used only to choose the linear forms; over a finite field linear
projections need not suffice, and the theorem there needs forms of higher degree.

## References

* [Stacks Project, Tag 0B1P](https://stacks.math.columbia.edu/tag/0B1P)
* [Stacks Project, Section 0B1N](https://stacks.math.columbia.edu/tag/0B1N)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpaceOfModule

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-- **Over an infinite field, a closed subset of `𝐏(V)` of dimension `< e` misses a linear
subspace of codimension `e`.** Let `V` be finite-dimensional and nonzero and `Z ⊆ 𝐏(V)` closed
with `dim Z < e ≤ dim V`. Then there is a subspace `W ≤ V` of linear forms with `dim W = e` whose
common zero locus `linearSubspace k V W` is disjoint from `Z`.

By induction on `e`: a linear form `v` not vanishing at a chosen point of each of the finitely
many irreducible components of `Z` cuts `Z` in a closed subset nowhere dense in `Z`, which has
dimension `< e - 1` and so misses the zero locus of some `(e - 1)`-dimensional `W'`; then
`W' + k v`, or `W'` enlarged by any vector if `v ∈ W'`, works. -/
theorem exists_finrank_eq_disjoint_linearSubspace_of_infinite [Infinite k]
    [FiniteDimensional k V] [Nontrivial V] (e : ℕ) (he : e ≤ Module.finrank k V)
    (Z : Set (projectiveSpaceOfModule k V)) (hZ : IsClosed Z)
    (hdim : topologicalKrullDim Z < (e : WithBot ℕ∞)) :
    ∃ W : Submodule k V, Module.finrank k W = e ∧ Disjoint Z (linearSubspace k V W) := by
  induction e generalizing Z with
  | zero =>
    have hbot : topologicalKrullDim Z = ⊥ :=
      (WithBot.lt_zero_iff_eq_bot _).mp (by simpa using hdim)
    have hempty : Z = ∅ := by
      have := (topologicalKrullDim_eq_bot_iff_isEmpty Z).mp hbot
      exact Set.isEmpty_coe_sort.mp this
    exact ⟨⊥, finrank_bot k V, by simp [hempty]⟩
  | succ e ih =>
    classical
    have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
    let Wc : Set Z → Submodule k V := fun C =>
      if h : C.Nonempty then pointSubmodule k V h.some.1 else ⊥
    have hWc : ∀ C ∈ hfin.toFinset, Wc C ≠ ⊤ := by
      intro C hC
      have hne : C.Nonempty := (hfin.mem_toFinset.mp hC).1.nonempty
      simp only [Wc, hne, ↓reduceDIte]
      intro htop
      obtain ⟨x, hx⟩ := exists_ι_notMem k V hne.some.1
      exact hx ((mem_pointSubmodule_iff k V _ x).mp (htop ▸ Submodule.mem_top))
    obtain ⟨v, hv⟩ := Stacks.LinearAlgebra.exists_notMem_biUnion_of_infinite hfin.toFinset Wc hWc
    set H := linearSubspace k V (k ∙ v) with hH
    set A := Z ∩ H with hA
    have hAclosed : IsClosed A := hZ.inter (isClosed_linearSubspace k V _)
    have hnd : IsNowhereDense ((Subtype.val : Z → _) ⁻¹' A) := by
      rw [isNowhereDense_preimage_val_iff_forall_irreducibleComponents hAclosed]
      intro C hC hCA
      have hne : C.Nonempty := hC.1.nonempty
      have hmem : (hne.some : Z).1 ∈ H := (hCA ⟨hne.some, hne.some_mem, rfl⟩).2
      rw [hH, mem_linearSubspace_iff, Submodule.span_singleton_le_iff_mem] at hmem
      have := hv C (hfin.mem_toFinset.mpr hC)
      simp only [Wc, hne, ↓reduceDIte] at this
      exact this hmem
    have hAdim : topologicalKrullDim A < (e : WithBot ℕ∞) := by
      have h1 := hnd.topologicalKrullDim_add_one_le (hAclosed.preimage continuous_subtype_val)
      rw [topologicalKrullDim_preimage_val Z A Set.inter_subset_left] at h1
      have h2 : topologicalKrullDim A + 1 < (e : WithBot ℕ∞) + 1 := by
        refine lt_of_le_of_lt h1 ?_
        simpa using hdim
      exact ENat.WithBot.add_one_le_natCast_iff.mp (ENat.WithBot.lt_add_one_iff.mp h2)
    obtain ⟨W', hW'rank, hW'disj⟩ := ih (by omega) A hAclosed hAdim
    have hW'top : W' ≠ ⊤ := by
      intro h
      rw [h, finrank_top] at hW'rank
      omega
    by_cases hvW' : v ∈ W'
    · obtain ⟨u, hu⟩ : ∃ u, u ∉ W' := by
        by_contra hc
        push Not at hc
        exact hW'top (eq_top_iff.mpr fun x _ => hc x)
      refine ⟨W' ⊔ k ∙ u, by rw [Submodule.finrank_sup_span_singleton hu, hW'rank], ?_⟩
      rw [Set.disjoint_iff]
      rintro q ⟨hqZ, hqW⟩
      have hqW' : q ∈ linearSubspace k V W' := linearSubspace_antitone k V le_sup_left hqW
      have hqH : q ∈ H := linearSubspace_antitone k V
        ((Submodule.span_singleton_le_iff_mem v W').mpr hvW') hqW'
      exact Set.disjoint_iff.mp hW'disj ⟨⟨hqZ, hqH⟩, hqW'⟩
    · refine ⟨W' ⊔ k ∙ v, by rw [Submodule.finrank_sup_span_singleton hvW', hW'rank], ?_⟩
      rw [Set.disjoint_iff]
      rintro q ⟨hqZ, hqW⟩
      have hqW' : q ∈ linearSubspace k V W' := linearSubspace_antitone k V le_sup_left hqW
      have hqH : q ∈ H := linearSubspace_antitone k V le_sup_right hqW
      exact Set.disjoint_iff.mp hW'disj ⟨⟨hqZ, hqH⟩, hqW'⟩

end ProjectiveSpaceOfModule

section Dimension

variable (k : Type u) [Field k]

/-- **A finite morphism from an irreducible scheme does not raise dimension.** Let `X` and `Y` be
schemes locally of finite type over a field `k`, `X` irreducible, and `f : X ⟶ Y` a finite
morphism over `k`. Then `dim X ≤ dim f(X)`: the fibres of `f` are zero-dimensional, so this is
the case of a quasi-finite morphism of the bound `dim X ≤ dim (fibre) + dim (closure of image)`
of Stacks Tag 0B2L. -/
theorem topologicalKrullDim_le_range_of_isFinite_of_irreducibleSpace {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    [LocallyOfFiniteType pY] [IrreducibleSpace X] (f : X ⟶ Y) [IsFinite f] (hf : f ≫ pY = pX) :
    topologicalKrullDim X ≤ topologicalKrullDim (Set.range f.base) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hfib : topologicalKrullDimAt (f.fiber (f.base x₀)) (f.asFiber x₀) = 0 := by
    refine (quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x₀).mp ⟨?_, f.quasiFiniteAt x₀⟩
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x₀)) isOpen_univ
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
    exact ⟨⟨U, hU⟩, ⟨W, hW⟩, hxW, hWU, f.finiteType_appLE hU hW hWU⟩
  have h2a := topologicalKrullDim_le_fiber_add_imageClosure k pX pY f hf x₀
  rw [hfib, zero_add] at h2a
  set J : Y.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range (fun x : X => f.base x)))
    with hJ
  have hclosed : IsClosed (Set.range f.base) := f.isClosedMap.isClosed_range
  have hsets : Set.range J.subschemeι.base = Set.range f.base := by
    rw [hJ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
    exact hclosed.closure_eq
  have hsubdim : topologicalKrullDim J.subscheme = topologicalKrullDim (Set.range f.base) := by
    refine (IsHomeomorph.topologicalKrullDim_eq _
      (IsClosedImmersion.isClosedEmbedding
        J.subschemeι).isEmbedding.toHomeomorph.isHomeomorph).trans ?_
    rw [hsets]
  rw [hsubdim] at h2a
  exact h2a

/-- **A finite morphism does not raise dimension.** Let `X` and `Y` be schemes locally of finite
type over a field `k` and `f : X ⟶ Y` a finite morphism over `k`. Then `dim X ≤ dim f(X)`.

The dimension of `X` is bounded by the dimensions of the closures of its points; the closure of
a point, with its reduced structure, is irreducible and maps finitely into `f(X)`, so the
irreducible case applies. -/
theorem topologicalKrullDim_le_range_of_isFinite {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    [LocallyOfFiniteType pY] (f : X ⟶ Y) [IsFinite f] (hf : f ≫ pY = pX) :
    topologicalKrullDim X ≤ topologicalKrullDim (Set.range f.base) := by
  have huniv : topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
  rw [← huniv]
  refine topologicalKrullDim_le_of_forall_closure isClosed_univ fun x _ => ?_
  set S : Set X := closure {x} with hS
  have hSclosed : IsClosed S := isClosed_closure
  set I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨S, hSclosed⟩ with hI
  have hrange : Set.range I.subschemeι.base = S := by
    rw [hI, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hhomeo : topologicalKrullDim S = topologicalKrullDim I.subscheme := by
    rw [← hrange]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (IsClosedImmersion.isClosedEmbedding I.subschemeι).isEmbedding.toHomeomorph.isHomeomorph).symm
  have hirrI : IrreducibleSpace I.subscheme :=
    (IsClosedImmersion.isClosedEmbedding
        I.subschemeι).isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr
      (by rw [hrange]; exact Subtype.irreducibleSpace isIrreducible_singleton.closure)
  have h := topologicalKrullDim_le_range_of_isFinite_of_irreducibleSpace k
    (I.subschemeι ≫ pX) pY (I.subschemeι ≫ f) (by rw [Category.assoc, hf])
  rw [hhomeo]
  refine h.trans (topologicalKrullDim_le_of_subset ?_)
  rintro _ ⟨y, rfl⟩
  exact ⟨I.subschemeι.base y, rfl⟩

/-- **A finite morphism onto an irreducible scheme of the same dimension is surjective.** Let `X`
and `Y` be schemes locally of finite type over a field `k`, `Y` irreducible and Noetherian of
dimension `d` and `X` of dimension `d`, and let `f : X ⟶ Y` be finite over `k`. The image of `f`
is closed of dimension at least `d`; a proper closed subset of `Y` is nowhere dense, hence of
dimension `< d`. -/
theorem surjective_of_isFinite_of_topologicalKrullDim_eq {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    [LocallyOfFiniteType pY] [IrreducibleSpace Y] [NoetherianSpace Y] (f : X ⟶ Y) [IsFinite f]
    (hf : f ≫ pY = pX) {d : ℕ} (hX : topologicalKrullDim X = d)
    (hY : topologicalKrullDim Y = d) : Surjective f := by
  refine ⟨Set.range_eq_univ.mp ?_⟩
  by_contra hne
  have hclosed : IsClosed (Set.range f.base) := f.isClosedMap.isClosed_range
  have hnd : IsNowhereDense (Set.range f.base) := by
    rw [hclosed.isNowhereDense_iff]
    by_contra hint
    have hdense : Dense (interior (Set.range f.base)) :=
      isOpen_interior.dense (Set.nonempty_iff_ne_empty.mpr hint)
    exact hne (by rw [← hclosed.closure_eq]; exact (hdense.mono interior_subset).closure_eq)
  have h1 := hnd.topologicalKrullDim_add_one_le hclosed
  have h2 := topologicalKrullDim_le_range_of_isFinite k pX pY f hf
  rw [hX] at h2
  rw [hY] at h1
  have h3 : ((d : WithBot ℕ∞)) + 1 ≤ (d : WithBot ℕ∞) := by
    have : ((d : WithBot ℕ∞)) + 1 ≤ topologicalKrullDim (Set.range f.base) + 1 := by gcongr
    exact this.trans h1
  have h4 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h3
  have : d + 1 ≤ d := by exact_mod_cast h4
  omega

end Dimension

namespace ProjectiveSpaceOfModule

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-- The projective space of a vector space of dimension `n + 1` is irreducible: a basis identifies
it with `Proj k[T₀, …, Tₙ]`. -/
theorem irreducibleSpace_of_finrank_eq_succ [FiniteDimensional k V] {n : ℕ}
    (hV : Module.finrank k V = n + 1) : IrreducibleSpace (projectiveSpaceOfModule k V) :=
  (projectiveSpaceOfModuleIsoProjMvPolynomial
    (Module.finBasisOfFinrankEq k V hV)).hom.homeomorph.irreducibleSpace_iff.mpr inferInstance

/-- **Noether normalization of a closed subscheme of `𝐏(V)` by a linear projection.** Let `k` be
an infinite field, `V` a nonzero finite-dimensional `k`-vector space and `i : X ⟶ 𝐏(V)` a closed
immersion with `dim X = d`. Then there is a subspace `W ≤ V` of linear forms of dimension `d + 1`
whose zero locus misses `X`, and the linear projection `𝐏(V) ⇢ 𝐏(W)` away from that zero locus,
restricted to `X`, is finite and surjective. -/
theorem exists_isFinite_surjective_projection [Infinite k] [FiniteDimensional k V]
    [Nontrivial V] {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V) [IsClosedImmersion i]
    {d : ℕ} (hdim : topologicalKrullDim X = d) :
    ∃ (W : Submodule k V) (j : X ⟶ (projectionDomain k V W).toScheme),
      Module.finrank k W = d + 1 ∧ Disjoint (Set.range i.base) (linearSubspace k V W) ∧
      j ≫ (projectionDomain k V W).ι = i ∧ IsFinite (j ≫ projection k V W) ∧
      Surjective (j ≫ projection k V W) := by
  have hZdim : topologicalKrullDim (Set.range i.base) = (d : WithBot ℕ∞) := by
    rw [← hdim]
    exact (i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq).symm
  have hVpos : 0 < Module.finrank k V := Module.finrank_pos
  have hV : Module.finrank k V = (Module.finrank k V - 1) + 1 := by omega
  have hdN : d + 1 ≤ Module.finrank k V := by
    have h := topologicalKrullDim_subspace_le (projectiveSpaceOfModule k V) (Set.range i.base)
    rw [hZdim, topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV] at h
    have : d ≤ Module.finrank k V - 1 := by exact_mod_cast h
    omega
  obtain ⟨W, hWrank, hWdisj⟩ := exists_finrank_eq_disjoint_linearSubspace_of_infinite (d + 1) hdN
    (Set.range i.base) i.isClosedEmbedding.isClosed_range
    (by rw [hZdim]; exact_mod_cast Nat.lt_succ_self d)
  have hsub : Set.range i.base ⊆ Set.range (projectionDomain k V W).ι.base := by
    rw [Scheme.Opens.range_ι, coe_mapDomain_subtype]
    exact Set.subset_compl_iff_disjoint_right.mpr hWdisj
  set j := IsOpenImmersion.lift (projectionDomain k V W).ι i hsub with hjdef
  have hj : j ≫ (projectionDomain k V W).ι = i := IsOpenImmersion.lift_fac _ _ _
  have hfin : IsFinite (j ≫ projection k V W) :=
    isFinite_projection_of_isClosedImmersion i W j hj
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have : IrreducibleSpace (projectiveSpaceOfModule k W) :=
    irreducibleSpace_of_finrank_eq_succ hWrank
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
    have := isProper_projectiveSpaceOfModuleToSpec k V
    infer_instance
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k W) := by
    have := isProper_projectiveSpaceOfModuleToSpec k W
    infer_instance
  have hfac : (j ≫ projection k V W) ≫ projectiveSpaceOfModuleToSpec k W =
      i ≫ projectiveSpaceOfModuleToSpec k V := by
    rw [Category.assoc, projection_comp_toSpec, ← Category.assoc, hj]
  refine ⟨W, j, hWrank, hWdisj, hj, hfin, ?_⟩
  exact surjective_of_isFinite_of_topologicalKrullDim_eq k (i ≫ projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k W) (j ≫ projection k V W) hfac hdim
    (topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hWrank)

end ProjectiveSpaceOfModule

section NoetherNormalization

open ProjectiveSpaceOfModule

variable {k : Type u} [Field k]

/-- **Projective Noether normalization, H-projective form.** Let `k` be an infinite field and
`X` a scheme with a closed immersion into some `ℙᴺ_k` over `k`, of dimension `d`. Then there is a
finite surjective morphism `X ⟶ ℙ^d_k` over `k`. -/
theorem exists_isFinite_surjective_projectiveSpaceOver_of_isProjectiveMorphism [Infinite k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : IsProjectiveMorphism sX) {d : ℕ}
    (hdim : topologicalKrullDim X = d) :
    ∃ π : X ⟶ projectiveSpaceOver d (Spec (.of k)),
      IsFinite π ∧ Surjective π ∧
        π ≫ (projectiveSpaceOver d (Spec (.of k)) ↘ Spec (.of k)) = sX := by
  obtain ⟨N, i₀, hi₀, hi₀s⟩ := hX
  have := hi₀
  let i : X ⟶ projectiveSpaceOfModule k (Fin (N + 1) → k) :=
    i₀ ≫ (basisProjectiveSpaceIso (Pi.basisFun k (Fin (N + 1)))).hom
  have his : i ≫ projectiveSpaceOfModuleToSpec k (Fin (N + 1) → k) = sX := by
    rw [Category.assoc, basisProjectiveSpaceIso_hom_comp_toSpec, ← hi₀s]
    rfl
  obtain ⟨W, j, hWrank, -, hj, hfin, hsurj⟩ := exists_isFinite_surjective_projection i hdim
  let b : Module.Basis (Fin (d + 1)) k W := Module.finBasisOfFinrankEq k W hWrank
  refine ⟨(j ≫ projection k (Fin (N + 1) → k) W) ≫ (basisProjectiveSpaceIso b).inv, inferInstance,
    inferInstance, ?_⟩
  have hb : (basisProjectiveSpaceIso b).inv ≫
      (projectiveSpaceOver d (Spec (.of k)) ↘ Spec (.of k)) = projectiveSpaceOfModuleToSpec k W :=
    ((Iso.eq_inv_comp _).mpr (basisProjectiveSpaceIso_hom_comp_toSpec b)).symm
  rw [Category.assoc, hb, Category.assoc, projection_comp_toSpec, ← Category.assoc, hj, his]

/-- **Projective Noether normalization.** Let `k` be an infinite field and `X` a projective
scheme over `k` (Stacks Tag 01W8) of dimension `d`. Then there is a finite surjective morphism
`X ⟶ ℙ^d_k` over `k`. -/
theorem exists_isFinite_surjective_projectiveSpaceOver [Infinite k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsProjective sX) {d : ℕ} (hdim : topologicalKrullDim X = d) :
    ∃ π : X ⟶ projectiveSpaceOver d (Spec (.of k)),
      IsFinite π ∧ Surjective π ∧
        π ≫ (projectiveSpaceOver d (Spec (.of k)) ↘ Spec (.of k)) = sX :=
  exists_isFinite_surjective_projectiveSpaceOver_of_isProjectiveMorphism sX
    ((isProjective_iff_isProjectiveMorphism_of_isAffine sX).mp hX) hdim

end NoetherNormalization

end AlgebraicGeometry
