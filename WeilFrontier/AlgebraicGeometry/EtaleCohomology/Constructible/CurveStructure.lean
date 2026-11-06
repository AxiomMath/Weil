module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GenericTrivialization
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleIffGenericEtaleNbhdFlc
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocalTorsionColimitOfConstructibles
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import WeilFrontier.Defs.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilFrontier.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ContainsFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves

/-!
# The structure of constructible and torsion sheaves on the small étale site

Let `X` be a scheme whose underlying space is Noetherian, for instance a curve over an
algebraically closed field `k`. This file collects, in one form on the small étale site
`AlgebraicGeometry.SmallEtale` with abelian coefficients `AddCommGrpCat.{u + 1}` and cohomology
`CategoryTheory.Sheaf.H`, the four facts on which the dévissage of étale cohomology of curves
rests.

1. A constructible abelian sheaf `F` on `X` is finite locally constant on a dense open
   subscheme `U ⊆ X`. Indeed `F` is finite locally constant on the strata of a finite cover of
   `X` by locally closed subschemes; the generic point `η` of an irreducible component lies in
   one stratum `L`, and the points of `L` outside the other irreducible components form an open
   neighbourhood of `η` inside `L`. The union `U` of these neighbourhoods contains every generic
   point, hence is dense, and finite local constancy on `U` is checked on the open cover of `U`
   by the neighbourhoods.
2. A finite locally constant abelian sheaf on an irreducible, geometrically unibranch scheme `X`
   (for instance a nonempty open subscheme of a normal integral curve) becomes constant, with
   finitely generated value, on a finite étale surjective `V ⟶ X`.
3. A torsion abelian sheaf on a Noetherian `X` is the filtered colimit of its constructible
   subsheaves (Stacks 03SA); this is
   `AlgebraicGeometry.SmallEtale.nonempty_isColimit_constructibleSubobjectCocone`.
4. On a quasi-compact quasi-separated `X`, `H^n(X, -)` commutes with filtered colimits.

## Main results

* `AlgebraicGeometry.exists_dense_isFiniteLocallyConstant_of_isConstructibleAbelianSheaf`: (1).
* `AlgebraicGeometry.SmallEtale.exists_isFinite_constantSheaf_iso_of_isFiniteLocallyConstant`:
  (2) on the small étale site;
  `AlgebraicGeometry.Scheme.exists_isFinite_constantSheaf_iso_of_isFiniteLocallyConstant` is the
  same statement on Mathlib's small étale site.
* `AlgebraicGeometry.SmallEtale.isIso_colimit_post_functorH`: (4), for `Sheaf.H`.
* `AlgebraicGeometry.SmallEtale.isColimit_mapCocone_functorH`: (4) for an arbitrary colimit
  cocone, and `AlgebraicGeometry.SmallEtale.exists_isFilteredColimit_isConstructible_functorH`:
  (3) and (4) together, the cohomology of a torsion sheaf on a Noetherian scheme as a filtered
  colimit of the cohomology of constructible sheaves.

## Implementation notes

Statement (2) is made for irreducible geometrically unibranch schemes, where the trivializing
cover is constructed from a monodromy torsor; this covers the open subschemes of normal curves.
The value of the trivialization is finitely generated; it is finite as soon as `F` is torsion,
in particular for constructible `F`.

For (4) the cohomology `Sheaf.H` is identified with the right derived functors of global
sections over the final object of the site, at the coefficient universe `u + 1`; the
identification is a choice made by universality of the two `δ`-functors.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4, I.11][FreitagKiehl]
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Abelian

universe w v u


/-! ### Generic finite local constancy of constructible sheaves -/

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}}

namespace SmallEtale

/-- **Finite local constancy descends along a jointly surjective étale family.** Let
`pₖ : Uₖ ⟶ T` be étale morphisms whose images cover `T`, and `F` a sheaf of sets on the small
étale site of `T`. If every inverse image `pₖ^* F` is finite locally constant, so is `F`. -/
theorem isFiniteLocallyConstant_of_forall_smallEtaleInverseImage {T : B.Scheme} {K : Type u}
    (U : K → B.Scheme) (p : ∀ k, U k ⟶ T) [∀ k, Etale (B.inclusion.map (p k))]
    (hp : ∀ x : T.obj, ∃ k, x ∈ Set.range (B.inclusion.map (p k)))
    (F : Sheaf (topology B T.obj T.property) (Type (u + 1)))
    (hF : ∀ k, IsFiniteLocallyConstant B (U k).obj (U k).property
      ((smallEtaleInverseImage B (p k) (Type (u + 1))).obj F)) :
    IsFiniteLocallyConstant B T.obj T.property F := by
  choose I W hW hc using fun k => (isFiniteLocallyConstant_iff_exists_cover _).mp (hF k)
  rw [isFiniteLocallyConstant_iff_exists_cover]
  let W' : (Σ k, I k) → SmallEtale B T.obj T.property := fun i =>
    ⟨Over.mk ((W i.1 i.2).obj.hom ≫ p i.1), by
      have : Etale (B.inclusion.map (W i.1 i.2).obj.hom) := (W i.1 i.2).property
      change Etale (B.inclusion.map ((W i.1 i.2).obj.hom ≫ p i.1))
      rw [Functor.map_comp]
      infer_instance⟩
  refine ⟨Σ k, I k, W', fun x => ?_, fun i => ?_⟩
  · obtain ⟨k, y, rfl⟩ := hp x
    obtain ⟨i, z, hz⟩ := hW k y
    refine ⟨⟨k, i⟩, z, ?_⟩
    change (B.inclusion.map ((W k i).obj.hom ≫ p k)) z = _
    rw [Functor.map_comp, Scheme.Hom.comp_apply, hz]
  · obtain ⟨M, hM, ⟨e⟩⟩ := hc i.1 i.2
    refine ⟨M, hM, ?_⟩
    obtain ⟨e'⟩ := (nonempty_constantSheafIso_over_iff B (U i.1).obj (U i.1).property
      (W i.1 i.2) _ _ M).mp ⟨e⟩
    exact (nonempty_constantSheafIso_over_iff B T.obj T.property (W' i) _ F M).mpr
      ⟨e' ≪≫ (smallEtaleInverseImageCompObjIso B (W i.1 i.2).obj.hom (p i.1) _ F).symm⟩

end SmallEtale

/-- In a Noetherian space, the points outside every irreducible component other than the closure
of `η` form an open neighbourhood of `η` inside the closure of `η`. -/
private theorem exists_isOpen_mem_subset_closure_of_mem_irreducibleComponents' {α : Type*}
    [TopologicalSpace α] [NoetherianSpace α] {η : α} (hη : closure {η} ∈ irreducibleComponents α) :
    ∃ V : Set α, IsOpen V ∧ η ∈ V ∧ V ⊆ closure {η} := by
  classical
  set K : Set α := ⋃₀ (irreducibleComponents α \ {closure {η}})
  have hK : IsClosed K :=
    ((NoetherianSpace.finite_irreducibleComponents).subset Set.sdiff_subset).isClosed_sUnion
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  refine ⟨Kᶜ, hK.isOpen_compl, ?_, ?_⟩
  · rintro ⟨C, ⟨hC, hCne⟩, hηC⟩
    have hle : closure {η} ⊆ C :=
      (isClosed_of_mem_irreducibleComponents C hC).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hηC)
    exact hCne (Set.Subset.antisymm (hη.2 hC.1 hle) hle)
  · intro x hx
    obtain ⟨C, hC, hxC⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
    by_cases hCη : C = closure {η}
    · exact hCη ▸ hxC rfl
    · exact (hx ⟨C, ⟨hC, hCη⟩, hxC rfl⟩).elim

/-- **A locally closed set through a generic point contains an open neighbourhood of it.** In a
Noetherian space, a locally closed set `L` containing the generic point `η` of an irreducible
component contains an open neighbourhood of `η`. -/
theorem exists_isOpen_mem_subset_of_isLocallyClosed {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] {η : α} (hη : closure {η} ∈ irreducibleComponents α) {L : Set α}
    (hL : IsLocallyClosed L) (hηL : η ∈ L) :
    ∃ W : Set α, IsOpen W ∧ η ∈ W ∧ W ⊆ L := by
  obtain ⟨V, hV, hηV, hVη⟩ := exists_isOpen_mem_subset_closure_of_mem_irreducibleComponents' hη
  refine ⟨V ∩ coborder L, hV.inter hL.isOpen_coborder, ⟨hηV, subset_coborder hηL⟩, ?_⟩
  intro x ⟨hxV, hxL⟩
  rw [← coborder_inter_closure (s := L)]
  exact ⟨hxL, closure_mono (Set.singleton_subset_iff.mpr hηL) (hVη hxV)⟩

/-- **A constructible sheaf of sets is finite locally constant on a dense open.** On a scheme `X`
whose underlying space is Noetherian, a constructible sheaf of sets `F` on the small étale site
has finite locally constant restriction to some dense open subscheme `U ⊆ X`. -/
theorem exists_dense_isFiniteLocallyConstant_of_isConstructibleSetSheaf (X : B.Scheme)
    [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    ∃ (U : B.Scheme) (j : U ⟶ X), IsOpenImmersion (B.inclusion.map j) ∧
      Dense (Set.range (B.inclusion.map j)) ∧
      SmallEtale.IsFiniteLocallyConstant B U.obj U.property
        ((smallEtaleSetPullback B j).obj F) := by
  obtain ⟨n, Y, jc, hjc, hcov, hflc⟩ :=
    (isConstructibleSetSheaf_iff_exists_immersion_cover B X F).mp hF
  let K := irreducibleComponents X.obj
  let η : K → X.obj := fun Z => IsIrreducible.genericPoint Z.2.1
  have hηcl (Z : K) : closure {η Z} = Z := by
    rw [(IsIrreducible.isGenericPoint_genericPoint_closure Z.2.1).def,
      (isClosed_of_mem_irreducibleComponents _ Z.2).closure_eq]
  have hK : ∀ Z : K, ∃ i, ∃ W : Set X.obj, IsOpen W ∧ η Z ∈ W ∧
      W ⊆ Set.range (B.inclusion.map (jc i)) := by
    intro Z
    have hη : closure {η Z} ∈ irreducibleComponents X.obj := by
      rw [hηcl]
      exact Z.2
    have hmem : η Z ∈ ⋃ i, Set.range (B.inclusion.map (jc i)).base := by
      rw [← hcov]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨W, hW, hηW, hWL⟩ := exists_isOpen_mem_subset_of_isLocallyClosed hη
      (hjc i).isLocallyClosed_range hi
    exact ⟨i, W, hW, hηW, hWL⟩
  choose i W hW hηW hWL using hK
  let Uset : Set X.obj := ⋃ Z, W Z
  let Uo : X.obj.Opens := ⟨Uset, isOpen_iUnion hW⟩
  have hUc : B.Contains Uo.toScheme := Scheme.size_lt_of_isOpenImmersion Uo.ι X.property
  let UB : B.Scheme := B.obj Uo.toScheme hUc
  let j : UB ⟶ X := ObjectProperty.homMk Uo.ι
  have hj : B.inclusion.map j = Uo.ι := rfl
  refine ⟨UB, j, ?_, ?_, ?_⟩
  · rw [hj]; infer_instance
  · rw [hj, Scheme.Opens.range_ι, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨Z, hZ, hxZ⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
    have hsub : (Z : Set X.obj) ⊆ closure Uset := by
      have h := hηcl ⟨Z, hZ⟩
      change closure {η ⟨Z, hZ⟩} = Z at h
      rw [← h]
      exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_iUnion.mpr ⟨⟨Z, hZ⟩, hηW _⟩))
    exact hsub (hxZ rfl)
  · let Wo : K → UB.obj.Opens := fun Z => Uo.ι ⁻¹ᵁ ⟨W Z, hW Z⟩
    have hWc : ∀ Z, B.Contains (Wo Z).toScheme := fun Z =>
      Scheme.size_lt_of_isOpenImmersion (Wo Z).ι UB.property
    let WB : K → B.Scheme := fun Z => B.obj (Wo Z).toScheme (hWc Z)
    let p : ∀ Z, WB Z ⟶ UB := fun Z => ObjectProperty.homMk (Wo Z).ι
    have : ∀ Z, Etale (B.inclusion.map (p Z)) := fun Z => by
      change Etale (Wo Z).ι
      infer_instance
    refine SmallEtale.isFiniteLocallyConstant_of_forall_smallEtaleInverseImage WB p ?_ _ ?_
    · intro x
      obtain ⟨Z, hZ⟩ := Set.mem_iUnion.mp x.2
      refine ⟨Z, ?_⟩
      change x ∈ Set.range (Wo Z).ι
      rw [Scheme.Opens.range_ι]
      exact hZ
    · intro Z
      have := hjc (i Z)
      have hk : Set.range (B.inclusion.map (p Z ≫ j)) ⊆
          Set.range (B.inclusion.map (jc (i Z))) := by
        rintro _ ⟨y, rfl⟩
        apply hWL Z
        exact y.2
      have h1 := SmallEtale.isFiniteLocallyConstant_of_range_subset_range B (jc (i Z)) (p Z ≫ j)
        hk F (hflc (i Z))
      exact (SmallEtale.isFiniteLocallyConstant_iff_of_iso
        (smallEtaleInverseImageCompObjIso B (p Z) j _ F)).mp h1

/-- **A constructible abelian sheaf is finite locally constant on a dense open.** On a scheme
`X` whose underlying space is Noetherian, a constructible sheaf of abelian groups `F` on the
small étale site has finite locally constant restriction `F|_U` to some dense open subscheme
`j : U ⟶ X`. -/
theorem exists_dense_isFiniteLocallyConstant_of_isConstructibleAbelianSheaf (X : B.Scheme)
    [NoetherianSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    ∃ (U : B.Scheme) (j : U ⟶ X), IsOpenImmersion (B.inclusion.map j) ∧
      Dense (Set.range (B.inclusion.map j)) ∧
      SmallEtale.IsFiniteLocallyConstant B U.obj U.property
        ((smallEtaleAbelianPullback B j).obj F) := by
  obtain ⟨U, j, hj, hd, h⟩ := exists_dense_isFiniteLocallyConstant_of_isConstructibleSetSheaf X _
    ((isConstructibleAbelianSheaf_iff_isConstructibleSetSheaf B X F).mp hF)
  refine ⟨U, j, hj, hd, ?_⟩
  obtain ⟨e⟩ := smallEtaleUnderlyingSetCommutes B X U j F
  exact (Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_forget _ _).mpr
    ((SmallEtale.isFiniteLocallyConstant_iff_of_iso e).mp h)
end AlgebraicGeometry

/-! ### Trivialization of finite locally constant sheaves by finite étale covers -/

namespace AlgebraicGeometry

attribute [local instance] Stacks.ConstantSheaf.hasSheafify_addCommGrp
  Stacks.ConstantSheaf.hasSheafCompose_intCoefficients
  Stacks.ConstantSheaf.preservesSheafification_intCoefficients
  Stacks.ConstantSheaf.hasSheafCompose_forget₂_int
  Stacks.ConstantSheaf.preservesSheafification_forget₂_int

/-- A finite étale morphism with nonempty source onto an irreducible scheme is surjective: its
image is open and closed. -/
theorem Scheme.Etale.surjective_hom_of_isFinite {X : Scheme.{u}} [IrreducibleSpace X]
    (Y : X.Etale) [IsFinite Y.hom] [Nonempty Y.left] : Surjective Y.hom := by
  refine ⟨fun x => ?_⟩
  have hcl : IsClopen (Set.range Y.hom) :=
    ⟨Y.hom.isClosedMap.isClosed_range, Y.hom.isOpenMap.isOpen_range⟩
  have hpc : PreconnectedSpace X :=
    ⟨(IrreducibleSpace.isIrreducible_univ X).2.isPreconnected⟩
  have hne : (Set.range Y.hom).Nonempty := ⟨_, Classical.arbitrary Y.left, rfl⟩
  have h := @IsClopen.eq_univ X _ hpc _ hcl hne
  obtain ⟨y, hy⟩ : x ∈ Set.range Y.hom := h ▸ Set.mem_univ x
  exact ⟨y, hy⟩

/-- **Finite locally constant sheaves are trivialized by finite étale covers**, on Mathlib's small
étale site. Let `X` be an irreducible, geometrically unibranch scheme and `G` a finite locally
constant abelian sheaf on its small étale site. Then there is a finite étale surjective
`Y ⟶ X` over which `G` is the constant sheaf on a finitely generated abelian group. -/
theorem Scheme.exists_isFinite_constantSheaf_iso_of_isFiniteLocallyConstant {X : Scheme.{u}}
    [IrreducibleSpace X] (hX : IsGeometricallyUnibranch X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : Stacks.ConstantSheaf.IsFiniteLocallyConstant X.smallEtaleTopology G) :
    ∃ Y : X.Etale, IsFinite Y.hom ∧ Surjective Y.hom ∧ ∃ A : AddCommGrpCat.{u + 1}, AddGroup.FG A ∧
      Nonempty ((constantSheaf (X.smallEtaleTopology.over Y) AddCommGrpCat.{u + 1}).obj A ≅
        (X.smallEtaleTopology.overPullback AddCommGrpCat.{u + 1} Y).obj G) := by
  have hM := Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_intSheaf.{u, u + 1, 0}
    X.smallEtaleTopology G hG
  obtain ⟨Y, hfin, hne, M, hMf, ⟨e⟩⟩ := exists_finiteEtale_trivialization (Λ := ℤ) hX hM
  refine ⟨Y, hfin, Scheme.Etale.surjective_hom_of_isFinite Y, ?_⟩
  let T := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp (by
    have h := hMf
    rwa [show M.isModule = AddCommGroup.toIntModule M from Subsingleton.elim _ _] at h)
  refine ⟨T.obj M, this, ⟨?_⟩⟩
  letI : HasSheafify (X.smallEtaleTopology.over Y) (ModuleCat.{u + 1} ℤ) :=
    Stacks.ModuleSheaf.hasSheafify_over_moduleCat.{u + 1, 0, u + 1, u} ℤ X.smallEtaleTopology Y
  refine ((constantCommuteCompose (X.smallEtaleTopology.over Y) T).app M).symm ≪≫
    (sheafCompose (X.smallEtaleTopology.over Y) T).mapIso e ≪≫ ?_
  exact ObjectProperty.isoMk _ ((Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft ((X.smallEtaleTopology.overPullback AddCommGrpCat.{u + 1} Y).obj G).obj
      T.asEquivalence.counitIso ≪≫ Functor.rightUnitor _)

/-- **Finite locally constant sheaves are trivialized by finite étale covers.** Let `X` be an
irreducible, geometrically unibranch scheme and `F` a finite locally constant abelian sheaf on its
small étale site. Then there are an object `V` of the site whose structure morphism `V ⟶ X` is
finite étale and surjective, and a finitely generated abelian group `A` with `A_V ≅ F|_V`. -/
theorem SmallEtale.exists_isFinite_constantSheaf_iso_of_isFiniteLocallyConstant
    {B : BigEtaleSite.{u}}
    (X : B.Scheme) [IrreducibleSpace X.obj] (hX : IsGeometricallyUnibranch X.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X.obj X.property) F) :
    ∃ V : SmallEtale B X.obj X.property, IsFinite (B.inclusion.map V.obj.hom) ∧
      Surjective (B.inclusion.map V.obj.hom) ∧ ∃ A : AddCommGrpCat.{u + 1}, AddGroup.FG A ∧
      Nonempty ((constantSheaf (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
          AddCommGrpCat.{u + 1}).obj A ≅
        ((smallEtaleBaseChange B V.obj.hom).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B V.obj.left.1 V.obj.left.property)).obj F) := by
  let J := SmallEtale.topology B X.obj X.property
  let K := X.obj.smallEtaleTopology
  let G := SmallEtale.toEtaleSite B X.obj X.property
  let E := SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}
  have hG : Stacks.ConstantSheaf.IsFiniteLocallyConstant K (E.functor.obj F) := by
    rw [SmallEtale.isFiniteLocallyConstant_abelian_iff_toEtaleSite B X.obj X.property]
    exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _ (E.unitIso.app F) (hF := hF)
  obtain ⟨Y, hfin, hsurj, A, hA, ⟨φ⟩⟩ :=
    Scheme.exists_isFinite_constantSheaf_iso_of_isFiniteLocallyConstant hX _ hG
  have hY : B.Contains Y.left := B.contains_of_finiteEtale Y.hom ⟨hfin, Y.prop⟩ X.property
  let V : SmallEtale B X.obj X.property :=
    ⟨Over.mk (ObjectProperty.homMk Y.hom : B.obj Y.left hY ⟶ B.obj X.obj X.property), Y.prop⟩
  have : (Over.post (X := V) G).IsDenseSubsite (J.over V) (K.over (G.obj V)) :=
    Stacks.Sites.overPost_isDenseSubsite G V
  let e := Functor.IsDenseSubsite.sheafEquiv (J.over V) (K.over (G.obj V)) (Over.post (X := V) G)
    AddCommGrpCat.{u + 1}
  have hc' := equivCommuteConstant' (J.over V) AddCommGrpCat.{u + 1} (K.over (G.obj V))
    (Over.post (X := V) G) (Over.mkIdTerminal (X := V))
    (Stacks.ConstantSheaf.overPostMkIdIsTerminal G V)
  let ψ : (constantSheaf (J.over V) AddCommGrpCat.{u + 1}).obj A ≅
      (J.overPullback AddCommGrpCat.{u + 1} V).obj F :=
    hc'.app A ≪≫ e.inverse.mapIso φ ≪≫
      (J.overPullback AddCommGrpCat.{u + 1} V).mapIso (E.unitIso.app F).symm
  exact ⟨V, hfin, hsurj, A, hA,
    (nonempty_constantSheafIso_over_iff B X.obj X.property V _ F A).mp ⟨ψ⟩⟩

end AlgebraicGeometry

/-! ### Sheaf cohomology as derived functors of sections, in any coefficient universe -/

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] {T : C} (hT : IsTerminal T)
  [HasExt.{w} (Sheaf J AddCommGrpCat.{w})]

/-- Degree-zero `Ext` out of the constant sheaf `ℤ` is the functor of sections over a terminal
object, for abelian sheaves in any universe `w`. -/
def extZeroConstantIsoSections :
    extFunctorObj.{w} ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) 0 ≅
      (sheafSections J AddCommGrpCat.{w}).obj (op T) :=
  NatIso.ofComponents (fun F ↦ (H.equiv₀ F hT).toAddCommGrpIso) (by
    intro F G f
    ext x
    exact (H.equiv₀_naturality hT f x).symm)

/-- **Sheaf cohomology is the right derived functor of sections over a terminal object**, for
abelian sheaves in any universe `w` with `Ext`-groups in `w`. This is a choice of isomorphism. -/
def functorHIsoRightDerivedSectionsOfIsTerminal [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    (n : ℕ) :
    Sheaf.functorH.{w, w} J n ≅ ((sheafSections J AddCommGrpCat.{w}).obj (op T)).rightDerived n :=
  (ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso
    ((sheafSections J AddCommGrpCat.{w}).obj (op T)) _
    (extZeroConstantIsoSections J hT) n).some

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Étale cohomology commutes with filtered colimits.** For a quasi-compact quasi-separated
scheme `S` and a filtered system `F` of abelian sheaves on its small étale site, the canonical
map `colim_i H^n(S, F_i) ⟶ H^n(S, colim_i F_i)` is an isomorphism. -/
theorem isIso_colimit_post_functorH [CompactSpace S] [QuasiSeparatedSpace S]
    [HasExt.{u + 1} (Sheaf (topology B S hS) AddCommGrpCat.{u + 1})]
    (n : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) :
    IsIso (colimit.post F (Sheaf.functorH.{u + 1, u + 1} (topology B S hS) n)) := by
  have h := isIso_colimit_post_rightDerived_globalSections.{0, u} B S hS n F
  have := enoughInjectives_sheaf_addCommGrpCat.{0, u} B S hS
  exact Stacks.Cohomology.isIso_colimit_post_of_natIso F _ _
    (Sheaf.functorHIsoRightDerivedSectionsOfIsTerminal.{u + 1} (topology B S hS)
      (finalIsTerminal B S hS) n).symm

/-- **Étale cohomology preserves filtered colimits.** For a quasi-compact quasi-separated scheme
`S`, a filtered diagram `F` of abelian sheaves on its small étale site and a colimit cocone `c`
of `F`, the cocone `H^n(S, c)` is a colimit cocone of `H^n(S, F_i)`. -/
def isColimitMapCoconeFunctorH [CompactSpace S] [QuasiSeparatedSpace S]
    [HasExt.{u + 1} (Sheaf (topology B S hS) AddCommGrpCat.{u + 1})]
    (n : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf (topology B S hS) AddCommGrpCat.{u + 1}} {c : Cocone F} (hc : IsColimit c) :
    IsColimit ((Sheaf.functorH.{u + 1, u + 1} (topology B S hS) n).mapCocone c) :=
  have := isIso_colimit_post_functorH B S hS n F
  have := preservesColimit_of_isIso_post (Sheaf.functorH.{u + 1, u + 1} (topology B S hS) n) F
  isColimitOfPreserves _ hc

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **The cohomology of a torsion sheaf is a filtered colimit of cohomology of constructible
sheaves.** Let `X` be a Noetherian scheme and `F` a torsion abelian sheaf on its small étale
site. Then `F` is the colimit of a filtered diagram `D` of constructible abelian sheaves, and for
every `n` the maps `H^n(X, D_i) ⟶ H^n(X, F)` exhibit `H^n(X, F)` as the colimit of the
`H^n(X, D_i)`. -/
theorem exists_isFilteredColimit_isConstructible_functorH [IsNoetherian X.obj]
    [HasExt.{u + 1} (Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    (F : Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsTorsionSheaf B X.obj X.property F) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf (topology B X.obj X.property) AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), (∀ i, IsConstructibleAbelianSheaf B X (D.obj i)) ∧
      Nonempty (IsColimit (Cocone.mk F ι)) ∧ ∀ n : ℕ,
        Nonempty (IsColimit ((Sheaf.functorH.{u + 1, u + 1} (topology B X.obj X.property)
          n).mapCocone (Cocone.mk F ι))) := by
  have hN := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  have : CompactSpace X.obj := hN.2
  have : IsLocallyNoetherian X.obj := hN.1
  have : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  obtain ⟨I, _, _, D, ι, ⟨hc⟩, hD⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B X F hF
  exact ⟨I, inferInstance, inferInstance, D, ι, hD, ⟨hc⟩,
    fun n => ⟨isColimitMapCoconeFunctorH B X.obj X.property n hc⟩⟩

end AlgebraicGeometry.SmallEtale

end
