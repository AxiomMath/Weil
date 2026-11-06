module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SplitSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.FiniteEtaleStratification
public import Weil.Attr

/-!
# An étale scheme over an integral scheme splits generically

Let `X` be an integral scheme and `f : U ⟶ X` a quasi-compact, quasi-separated étale morphism.
Then there are a nonempty scheme `V`, an étale morphism `g : V ⟶ X` and `m : ℕ` such that
`U ×_X V` is isomorphic, as a `V`-scheme, to the disjoint union of `m` copies of `V`.

The proof goes through the finite étale stratification of a quasi-compact quasi-separated étale
morphism (Stacks 03S0). Restrict `f` to a nonempty affine open `W` of `X`. The stratum through
the generic point of `W` is the image of an immersion `i : Y ⟶ W`; since its closure is all of
`W`, the immersion is closed in an open subscheme of `W` with the same underlying set, hence (as
`W` is reduced) an isomorphism onto it, so `i` is an open immersion. Over `Y` the base change of
`f` is finite étale, so it has sheet data over an étale neighbourhood `N ⟶ Y` (Stacks 04HN).
Sheet data cut the base change over `N` into finitely many pairwise disjoint opens, each mapped
isomorphically onto `N`; and a scheme covered by pairwise disjoint opens is their coproduct.

## Main results

* `AlgebraicGeometry.exists_iso_sigma_const_of_disjoint_opens`: a morphism `b : T ⟶ N` whose
  source is covered by finitely many pairwise disjoint opens, each mapped isomorphically onto `N`,
  is isomorphic over `N` to the fold map `N ⊔ ⋯ ⊔ N ⟶ N`.
* `AlgebraicGeometry.exists_etale_pullback_iso_sigma_const`: an étale scheme over an integral
  scheme becomes a finite disjoint union of copies of the base after an étale base change with
  nonempty source.

## Implementation notes

Freitag–Kiehl work with noetherian schemes, where every morphism out of `U` is quasi-compact and
quasi-separated; the statement here assumes only these two properties of `f`. Some finiteness
assumption is needed: an infinite disjoint union of copies of `X` admits no such splitting.
The sheaf-theoretic proof in the source (spreading out a splitting field of the generic fibre)
is replaced by the stratification argument, which yields the same statement.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.4
* [Stacks Project, Tag 03S0](https://stacks.math.columbia.edu/tag/03S0)
* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism `b : T ⟶ N` such that `T` is covered by finitely many pairwise disjoint opens,
each carried isomorphically onto `N` by `b`, is isomorphic over `N` to the fold map of a finite
disjoint union of copies of `N`. -/
theorem exists_iso_sigma_const_of_disjoint_opens {T N : Scheme.{u}} (b : T ⟶ N) {ι : Type*}
    [Finite ι] (W : ι → T.Opens) (hcov : iSup W = ⊤)
    (hdisj : Pairwise fun i j => Disjoint (W i) (W j)) (hiso : ∀ i, IsIso ((W i).ι ≫ b)) :
    ∃ (m : ℕ) (e : T ≅ ∐ fun _ : Fin m => N),
      e.hom ≫ Sigma.desc (fun _ => 𝟙 N) = b := by
  obtain ⟨m, ⟨σ⟩⟩ := Finite.exists_equiv_fin ι
  let f : Fin m → (N ⟶ T) := fun k => inv ((W (σ.symm k)).ι ≫ b) ≫ (W (σ.symm k)).ι
  have hf : ∀ k, (f k).opensRange = W (σ.symm k) := by
    intro k
    simp [f, Scheme.Hom.opensRange_comp_of_isIso]
  have hcol := nonempty_isColimit_cofanMk_of f (by
      rw [eq_top_iff, ← hcov]
      refine iSup_le fun i => ?_
      rw [← σ.symm_apply_apply i, ← hf]
      exact le_iSup (fun k => (f k).opensRange) (σ i))
    (by
      intro k l hkl
      simp only [Function.onFun, hf]
      exact hdisj (σ.symm.injective.ne hkl))
  have : IsIso (Sigma.desc f) := by
    simpa only [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk T f), cofan_mk_inj,
      Cofan.mk_pt] using hcol
  refine ⟨m, (asIso (Sigma.desc f)).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  ext k
  simp [f]

/-- An immersion into an integral scheme whose image contains the generic point is an open
immersion. -/
theorem isOpenImmersion_of_isImmersion_of_genericPoint_mem {Y W : Scheme.{u}} [IsIntegral W]
    (i : Y ⟶ W) [IsImmersion i] (h : genericPoint W ∈ Set.range i) : IsOpenImmersion i := by
  have hcl : closure (Set.range i) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    have := (genericPoint_spec W).def
    rw [← this]
    exact closure_mono (Set.singleton_subset_iff.mpr h)
  have hcob : coborder (Set.range i) = Set.range i := by
    rw [coborder_eq_union_closure_compl, hcl, Set.compl_univ, Set.union_empty]
  have : Surjective i.liftCoborder := by
    refine ⟨fun z => ?_⟩
    have hz : z.1 ∈ Set.range i := by
      rw [← hcob]
      exact z.2
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, i.coborderRange.ι.isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι, hy]
    rfl
  have : IsIso i.liftCoborder := isIso_of_isClosedImmersion_of_surjective _
  rw [← i.liftCoborder_ι]
  infer_instance

/-- **FK I.4, generic splitting of étale schemes.** Let `X` be an integral scheme and
`f : U ⟶ X` a quasi-compact quasi-separated étale morphism. Then there are a nonempty scheme
`V`, an étale morphism `g : V ⟶ X` and `m : ℕ` such that `U ×_X V` is isomorphic over `V` to
the disjoint union of `m` copies of `V`. -/
@[weil "lem_fk104_etale_scheme_splits_generically"]
theorem exists_etale_pullback_iso_sigma_const {X U : Scheme.{u}} [IsIntegral X] (f : U ⟶ X)
    [Etale f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (V : Scheme.{u}) (g : V ⟶ X) (_ : Etale g) (_ : Nonempty V) (m : ℕ)
      (e : pullback f g ≅ ∐ fun _ : Fin m => V),
      e.hom ≫ Sigma.desc (fun _ => 𝟙 V) = pullback.snd f g := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : IsAffine W := hW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  let f₀ : pullback f W.ι ⟶ W := pullback.snd f W.ι
  have : QuasiSeparatedSpace (pullback f W.ι : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated f₀
  obtain ⟨P, hP, -, hstrata⟩ := exists_constructible_partition_finite_etale f₀
  obtain ⟨S, ⟨hSP, hηS⟩, -⟩ := hP.1.2 (genericPoint W)
  obtain ⟨Y, i, hi, hrange, hfin, het⟩ := hstrata S hSP
  have : IsOpenImmersion i :=
    isOpenImmersion_of_isImmersion_of_genericPoint_mem i (by rw [hrange]; exact hηS)
  obtain ⟨y, -⟩ : genericPoint W ∈ Set.range i := by rw [hrange]; exact hηS
  obtain ⟨N, g, hg, -, n, -, ⟨hsp⟩⟩ :=
    Stacks.Etale.exists_compactSpace_etale_isSplitOver (pullback.fst i f₀) y
  have hpb₀ := IsPullback.of_hasPullback (pullback.fst i f₀) g
  obtain ⟨ι, _, Wk, hcov, hdisj, hiso⟩ := hsp.exists_disjoint_opens_of_isPullback hpb₀
  obtain ⟨m, e, he⟩ := exists_iso_sigma_const_of_disjoint_opens _ Wk hcov hdisj hiso
  have hpb : IsPullback
      (pullback.fst (pullback.fst i f₀) g ≫ pullback.snd i f₀ ≫ pullback.fst f W.ι)
      (pullback.snd (pullback.fst i f₀) g) f (g ≫ i ≫ W.ι) :=
    hpb₀.paste_horiz ((IsPullback.of_hasPullback i f₀).flip.paste_horiz
      (IsPullback.of_hasPullback f W.ι))
  refine ⟨N, g ≫ i ≫ W.ι, inferInstance, ⟨n⟩, m, hpb.isoPullback.symm ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, he, IsPullback.isoPullback_inv_snd]

end AlgebraicGeometry
