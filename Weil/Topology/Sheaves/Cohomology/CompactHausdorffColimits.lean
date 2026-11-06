module

public import Weil.Attr
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SoftAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.NativeCohomologyAndColimits
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedSectionsVersusSiteCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology

/-!
# Cohomology of a compact Hausdorff space: filtered colimits and torsion-free coefficients

Let `X` be a compact Hausdorff space. This file proves that the sheaf cohomology of `X` commutes
with filtered colimits of abelian sheaves, hence with filtered colimits of constant coefficient
groups,
`H^ν(X, colimᵢ Mᵢ) = colimᵢ H^ν(X, Mᵢ)`,
and deduces the universal coefficient theorem for torsion-free (equivalently, flat) coefficients:
for every torsion-free abelian group `M` the map
`M ⊗_ℤ H^ν(X, ℤ) → H^ν(X, M)`, `m ⊗ x ↦ (1 ↦ m)_* x`,
is bijective, naturally in `M`.

Cohomology of an abelian sheaf `G` is `CategoryTheory.Sheaf.H G ν`, the `Ext`-group out of the
constant sheaf `ℤ`; the cohomology of `X` with coefficients in an abelian group `M` is that of the
constant sheaf `(constantSheaf _ _).obj M`.

The argument is the classical one (Godement II.4.12, Bredon II.9, II.16).

* A section of a filtered colimit of sheaves comes, near every point, from a member of the
  diagram, and a section dying in the colimit dies near every point at a later stage
  (`exists_local_rep`, `exists_local_eq_zero`); this is local surjectivity and local injectivity
  of sheafification. On a locally compact Hausdorff space the local statements globalize to a
  neighbourhood of any compact set (`exists_rep_near_isCompact`,
  `exists_eq_zero_near_isCompact`): the local lifts over a finite cover are patched two at a time,
  their difference dying at one stage on a neighbourhood of the intersection of two compact sets,
  and the two neighbourhoods are shrunk so that their overlap lies inside it
  (`exists_isOpen_inter_subset`).
* For `X` compact Hausdorff this gives that global sections commute with filtered colimits
  (`isIso_colimit_post_sectionsTop`) and that a filtered colimit of soft sheaves is soft
  (`isSoft_of_isColimit`). Injective sheaves are soft, and soft sheaves are acyclic
  (`isZero_rightDerived_sectionsTop_of_isSoft`), so the induction on the degree of
  [Stacks, Tag 01FF] applies.
* An abelian group is the filtered colimit of its finitely generated subgroups, which are free of
  finite rank when it is torsion-free. The universal coefficient map is bijective for `ℤ`, hence
  for every retract of a finite sum of copies of `ℤ` by naturality, and both of its sides commute
  with filtered colimits.

## Main results

* `CompactHausdorffCohomology.isIso_colimit_post_rightDerived_sectionsTop`: the right derived
  functors of global sections commute with filtered colimits of abelian sheaves.
* `CompactHausdorffCohomology.preservesColimitsOfShape_functorH`: so does `Sheaf.functorH`.
* `CompactHausdorffCohomology.isIso_colimit_post_constantSheaf_comp_functorH`:
  `colimᵢ H^ν(X, Mᵢ) ⟶ H^ν(X, colimᵢ Mᵢ)` is an isomorphism.
* `CompactHausdorffCohomology.exists_H_constantSheaf_map_eq_of_isColimit`,
  `CompactHausdorffCohomology.exists_H_constantSheaf_map_eq_zero_of_isColimit`: the same
  statement read on elements, for the `Ext`-groups in an arbitrary universe.
* `CompactHausdorffCohomology.bijective_tensorCohomologyMap_of_isTorsionFree`,
  `CompactHausdorffCohomology.tensorCohomologyAddEquiv`: universal coefficients,
  `M ⊗_ℤ H^ν(X, ℤ) ≃+ H^ν(X, M)` for torsion-free `M`; `tensorCohomologyMap_naturality` is the
  naturality in `M`.

## Main definitions

* `CompactHausdorffCohomology.tensorCohomologyMap`: the universal coefficient map
  `M ⊗_ℤ H^ν(X, ℤ) → H^ν(X, M)`, for any space and any abelian group `M`.
* `CompactHausdorffCohomology.fgSubgroupCocone`: an abelian group as the union of its finitely
  generated subgroups, a colimit by `isColimitFGSubgroupCocone`.

## Implementation notes

The `Ext`-groups defining `Sheaf.H` may be taken in any universe `w`, through a `HasExt.{w}`
binder. The colimit statements are proved in the universe of the space, where `Sheaf.H` is
identified with the right derived functors of global sections
(`Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH`), and transported along the
additive change of universe of `Ext`. Since colimits indexed by a `Type u` need not exist in
`AddCommGrpCat.{w}`, the statements in a general universe are given on elements.

Softness is `Stacks.Topology.IsSoft`, a neighbourhood form of the surjectivity of
`Γ(X, F) → Γ(K, F|_K)` for closed `K`.

## References

* [R. Godement, *Topologie algébrique et théorie des faisceaux*][godement1958], II.4.12.
* [G. Bredon, *Sheaf theory*][bredon1997], II.9, II.16.
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe w u

namespace CompactHausdorffCohomology

/-- In a Hausdorff space, two compact sets `K₁, K₂` with `K₁ ∩ K₂ ⊆ W`, `W` open, have open
neighbourhoods whose intersection lies in `W`. -/
theorem exists_isOpen_inter_subset {X : Type*} [TopologicalSpace X] [T2Space X]
    {K₁ K₂ W : Set X} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂) (hW : IsOpen W)
    (hK : K₁ ∩ K₂ ⊆ W) :
    ∃ O₁ O₂ : Set X, IsOpen O₁ ∧ IsOpen O₂ ∧ K₁ ⊆ O₁ ∧ K₂ ⊆ O₂ ∧ O₁ ∩ O₂ ⊆ W := by
  have hdisj : Disjoint (K₁ \ W) (K₂ \ W) := by
    rw [Set.disjoint_left]
    rintro x ⟨hx₁, hxW⟩ ⟨hx₂, -⟩
    exact hxW (hK ⟨hx₁, hx₂⟩)
  obtain ⟨A₁, A₂, hA₁, hA₂, hKA₁, hKA₂, hA⟩ :=
    SeparatedNhds.of_isCompact_isCompact (h₁.diff hW) (h₂.diff hW) hdisj
  refine ⟨A₁ ∪ W, A₂ ∪ W, hA₁.union hW, hA₂.union hW, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inr hxW
    · exact Or.inl (hKA₁ ⟨hx, hxW⟩)
  · intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inr hxW
    · exact Or.inl (hKA₂ ⟨hx, hxW⟩)
  · rintro x ⟨hx₁ | hx₁, hx₂ | hx₂⟩
    · exact absurd hx₂ (Set.disjoint_left.mp hA hx₁)
    · exact hx₂
    · exact hx₁
    · exact hx₁


section Colimits

variable {X : TopCat.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The value at `op V` of the presheaf colimit of a diagram of sheaves is a filtered colimit
of the values. -/
theorem exists_rep_presheafColimit [IsFiltered I] (V : Opens X)
    (p : ToType ((colimit (F ⋙ sheafToPresheaf _ _)).obj (op V))) :
    ∃ (i : I) (t : ToType ((F.obj i).obj.obj (op V))),
      (colimit.ι (F ⋙ sheafToPresheaf _ _) i).app (op V) t = p := by
  have hc := isColimitOfPreserves ((evaluation _ _).obj (op V))
    (colimit.isColimit (F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  exact Concrete.isColimit_exists_rep _ hc p

theorem exists_eq_zero_presheafColimit [IsFiltered I] (V : Opens X) (i : I)
    (t : ToType ((F.obj i).obj.obj (op V)))
    (ht : (colimit.ι (F ⋙ sheafToPresheaf _ _) i).app (op V) t = 0) :
    ∃ (j : I) (f : i ⟶ j), (F.map f).hom.app (op V) t = 0 := by
  have hc := isColimitOfPreserves ((evaluation _ _).obj (op V))
    (colimit.isColimit (F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  obtain ⟨k, f, g, h⟩ := (Concrete.isColimit_rep_eq_iff_exists _ hc (i := i) (j := i) t 0).mp
    (by rw [map_zero]; exact ht)
  exact ⟨k, f, by simpa using h⟩


variable {F} {c : Cocone F}

/-- The point of a colimit cocone of sheaves is the sheafification of the presheaf colimit. -/
noncomputable def coconePtIsoSheafify (hc : IsColimit c) :
    c.pt ≅ (Sheaf.sheafifyCocone (colimit.cocone (F ⋙ sheafToPresheaf _ _))).pt :=
  hc.coconePointUniqueUpToIso (Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _))

theorem coconePtIsoSheafify_app_ι_app (hc : IsColimit c) (i : I) (V : Opens X)
    (t : ToType ((F.obj i).obj.obj (op V))) :
    (coconePtIsoSheafify hc).hom.hom.app (op V) ((c.ι.app i).hom.app (op V) t) =
      (toSheafify (Opens.grothendieckTopology X) (colimit (F ⋙ sheafToPresheaf _ _))).app (op V)
        ((colimit.ι (F ⋙ sheafToPresheaf _ _) i).app (op V) t) := by
  have h := hc.comp_coconePointUniqueUpToIso_hom
    (Sheaf.isColimitSheafifyCocone _ (colimit.isColimit (F ⋙ sheafToPresheaf _ _))) i
  have h' := congrArg (fun φ => φ.hom.app (op V) t) h
  simp only at h'
  rw [Sheaf.sheafifyCocone_ι_app_val] at h'
  exact h'

theorem coconePtIsoSheafify_injective (hc : IsColimit c) (V : Opens X) :
    Function.Injective ((coconePtIsoSheafify hc).hom.hom.app (op V)) := by
  intro a b hab
  have := congrArg ((coconePtIsoSheafify hc).inv.hom.app (op V)) hab
  simpa [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom] using this

/-- **Local representability.** A section of the colimit sheaf comes, near every point, from a
section of some member of the diagram. -/
theorem exists_local_rep [IsFiltered I] (hc : IsColimit c) {U : Opens X}
    (s : ToType (c.pt.obj.obj (op U)))
    {x : X} (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (i : I) (t : ToType ((F.obj i).obj.obj (op V))), x ∈ V ∧
      (c.ι.app i).hom.app (op V) t = c.pt.obj.map (homOfLE hVU).op s := by
  let P := colimit (F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let e := coconePtIsoSheafify hc
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) P) (e.hom.hom.app (op U) s)
  obtain ⟨V, f, ⟨p, hp⟩, hxV⟩ := (Opens.mem_grothendieckTopology _).mp hmem x hx
  obtain ⟨i, t, rfl⟩ := exists_rep_presheafColimit F V p
  refine ⟨V, f.le, i, t, hxV, coconePtIsoSheafify_injective hc V ?_⟩
  rw [coconePtIsoSheafify_app_ι_app, hp]
  exact (NatTrans.naturality_apply e.hom.hom f.op s).symm

/-- **Local vanishing.** A section of a member of the diagram which dies in the colimit sheaf
dies, near every point, at a later stage of the diagram. -/
theorem exists_local_eq_zero [IsFiltered I] (hc : IsColimit c) {V : Opens X} (i : I)
    (t : ToType ((F.obj i).obj.obj (op V))) (ht : (c.ι.app i).hom.app (op V) t = 0)
    {x : X} (hx : x ∈ V) :
    ∃ (W : Opens X) (hWV : W ≤ V) (j : I) (f : i ⟶ j), x ∈ W ∧
      (F.map f).hom.app (op W) ((F.obj i).obj.map (homOfLE hWV).op t) = 0 := by
  let P := colimit (F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  have h0 : (toSheafify (Opens.grothendieckTopology X) P).app (op V)
      ((colimit.ι (F ⋙ sheafToPresheaf _ _) i).app (op V) t) =
      (toSheafify (Opens.grothendieckTopology X) P).app (op V) 0 := by
    rw [← coconePtIsoSheafify_app_ι_app hc, ht, map_zero]
    exact (map_zero _).symm
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) P) _ _ h0
  obtain ⟨W, g, hg, hxW⟩ := (Opens.mem_grothendieckTopology _).mp hmem x hx
  simp only [Presheaf.equalizerSieve_apply, map_zero] at hg
  rw [← NatTrans.naturality_apply] at hg
  obtain ⟨j, f, hf⟩ := exists_eq_zero_presheafColimit F W i _ hg
  exact ⟨W, g.le, j, f, hxW, hf⟩

section Restriction

variable (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

theorem map_homOfLE_map_homOfLE {U V W : Opens X} (h₁ : W ≤ V) (h₂ : V ≤ U)
    (s : ToType (G.obj.obj (op U))) :
    G.obj.map (homOfLE h₁).op (G.obj.map (homOfLE h₂).op s) =
      G.obj.map (homOfLE (h₁.trans h₂)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem map_homOfLE_self {U : Opens X} (h : U ≤ U) (s : ToType (G.obj.obj (op U))) :
    G.obj.map (homOfLE h).op s = s := by
  have : (homOfLE h).op = 𝟙 (op U) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem eq_zero_of_le_bot {U : Opens X} (hU : U ≤ ⊥) (s : ToType (G.obj.obj (op U))) :
    s = 0 := by
  obtain rfl : U = ⊥ := le_bot_iff.mp hU
  exact Stacks.Topology.eq_zero_of_bot (Z := X) G s

end Restriction

/-- **Vanishing near a compact set.** A section of a member of a filtered diagram of sheaves
which dies in the colimit dies, on a neighbourhood of any compact subset of its domain, at a
single later stage. -/
theorem exists_eq_zero_near_isCompact [IsFiltered I] (hc : IsColimit c) {K : Set X}
    (hK : IsCompact K) {V : Opens X} (hKV : K ⊆ V) (i : I)
    (t : ToType ((F.obj i).obj.obj (op V))) (ht : (c.ι.app i).hom.app (op V) t = 0) :
    ∃ (W : Opens X) (hWV : W ≤ V) (j : I) (f : i ⟶ j), K ⊆ W ∧
      (F.map f).hom.app (op W) ((F.obj i).obj.map (homOfLE hWV).op t) = 0 := by
  refine hK.induction_on (p := fun S => ∃ (W : Opens X) (hWV : W ≤ V) (j : I) (f : i ⟶ j),
      S ⊆ W ∧ (F.map f).hom.app (op W) ((F.obj i).obj.map (homOfLE hWV).op t) = 0) ?_ ?_ ?_ ?_
  · exact ⟨⊥, bot_le, i, 𝟙 i, Set.empty_subset _, eq_zero_of_le_bot _ le_rfl _⟩
  · rintro S T hST ⟨W, hWV, j, f, hTW, h⟩
    exact ⟨W, hWV, j, f, hST.trans hTW, h⟩
  · rintro S T ⟨W₁, hW₁, j₁, f₁, hS, h₁⟩ ⟨W₂, hW₂, j₂, f₂, hT, h₂⟩
    obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span f₁ f₂
    refine ⟨W₁ ⊔ W₂, sup_le hW₁ hW₂, k, f₁ ≫ g₁, Set.union_subset_union hS hT, ?_⟩
    refine TopCat.Sheaf.eq_of_locally_eq₂ (F := F.obj k) (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ W₂))
      (homOfLE (le_sup_right : W₂ ≤ W₁ ⊔ W₂)) le_rfl _ _ ?_ ?_
    · change (F.obj k).obj.map _ _ = (F.obj k).obj.map _ _
      rw [map_zero, ← NatTrans.naturality_apply, map_homOfLE_map_homOfLE, F.map_comp,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
        h₁, map_zero]
    · change (F.obj k).obj.map _ _ = (F.obj k).obj.map _ _
      rw [map_zero, ← NatTrans.naturality_apply, map_homOfLE_map_homOfLE, hg, F.map_comp,
        ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
        h₂, map_zero]
  · intro x hx
    obtain ⟨W, hWV, j, f, hxW, h⟩ := exists_local_eq_zero hc i t ht (hKV hx)
    exact ⟨W, mem_nhdsWithin_of_mem_nhds (W.isOpen.mem_nhds hxW), W, hWV, j, f, subset_rfl, h⟩

theorem ι_app_map_apply {i j : I} (f : i ⟶ j) (V : Opens X)
    (t : ToType ((F.obj i).obj.obj (op V))) :
    (c.ι.app j).hom.app (op V) ((F.map f).hom.app (op V) t) = (c.ι.app i).hom.app (op V) t := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
    c.w f]

theorem ι_app_res (i : I) {V W : Opens X} (h : W ≤ V) (t : ToType ((F.obj i).obj.obj (op V))) :
    (c.ι.app i).hom.app (op W) ((F.obj i).obj.map (homOfLE h).op t) =
      c.pt.obj.map (homOfLE h).op ((c.ι.app i).hom.app (op V) t) :=
  NatTrans.naturality_apply _ _ _

theorem map_app_res {i j : I} (f : i ⟶ j) {V W : Opens X} (h : W ≤ V)
    (t : ToType ((F.obj i).obj.obj (op V))) :
    (F.map f).hom.app (op W) ((F.obj i).obj.map (homOfLE h).op t) =
      (F.obj j).obj.map (homOfLE h).op ((F.map f).hom.app (op V) t) :=
  NatTrans.naturality_apply _ _ _

/-- **Representability near a compact set.** On a locally compact Hausdorff space, a section of
the colimit of a filtered diagram of sheaves comes, on a neighbourhood of any compact subset of
its domain, from a section of a single member of the diagram. -/
theorem exists_rep_near_isCompact [IsFiltered I] [T2Space X] [LocallyCompactSpace X]
    (hc : IsColimit c) {K : Set X} (hK : IsCompact K) {U : Opens X} (hKU : K ⊆ U)
    (s : ToType (c.pt.obj.obj (op U))) :
    ∃ (W : Opens X) (hWU : W ≤ U) (i : I) (t : ToType ((F.obj i).obj.obj (op W))), K ⊆ W ∧
      (c.ι.app i).hom.app (op W) t = c.pt.obj.map (homOfLE hWU).op s := by
  suffices h : ∃ C : Set X, IsCompact C ∧ K ⊆ C ∧ ∃ (W : Opens X) (hWU : W ≤ U) (i : I)
      (t : ToType ((F.obj i).obj.obj (op W))), C ⊆ W ∧
        (c.ι.app i).hom.app (op W) t = c.pt.obj.map (homOfLE hWU).op s by
    obtain ⟨C, -, hKC, W, hWU, i, t, hCW, h⟩ := h
    exact ⟨W, hWU, i, t, hKC.trans hCW, h⟩
  refine hK.induction_on (p := fun S => ∃ C : Set X, IsCompact C ∧ S ⊆ C ∧ ∃ (W : Opens X)
      (hWU : W ≤ U) (i : I) (t : ToType ((F.obj i).obj.obj (op W))), C ⊆ W ∧
        (c.ι.app i).hom.app (op W) t = c.pt.obj.map (homOfLE hWU).op s) ?_ ?_ ?_ ?_
  · obtain ⟨i⟩ := IsFiltered.nonempty (C := I)
    exact ⟨∅, isCompact_empty, subset_rfl, ⊥, bot_le, i, 0, Set.empty_subset _,
      eq_zero_of_le_bot _ le_rfl _ |>.trans (eq_zero_of_le_bot _ le_rfl _).symm⟩
  · rintro S T hST ⟨C, hC, hTC, rest⟩
    exact ⟨C, hC, hST.trans hTC, rest⟩
  · rintro S T ⟨C₁, hC₁, hSC₁, W₁, hW₁, i₁, t₁, hCW₁, h₁⟩ ⟨C₂, hC₂, hTC₂, W₂, hW₂, i₂, t₂, hCW₂, h₂⟩
    let k := IsFiltered.max i₁ i₂
    let a₁ := IsFiltered.leftToMax i₁ i₂
    let a₂ := IsFiltered.rightToMax i₁ i₂
    let t₁' := (F.map a₁).hom.app (op W₁) t₁
    let t₂' := (F.map a₂).hom.app (op W₂) t₂
    have h₁' : (c.ι.app k).hom.app (op W₁) t₁' = c.pt.obj.map (homOfLE hW₁).op s := by
      rw [ι_app_map_apply, h₁]
    have h₂' : (c.ι.app k).hom.app (op W₂) t₂' = c.pt.obj.map (homOfLE hW₂).op s := by
      rw [ι_app_map_apply, h₂]
    let D := W₁ ⊓ W₂
    let d := (F.obj k).obj.map (homOfLE (inf_le_left : D ≤ W₁)).op t₁' -
      (F.obj k).obj.map (homOfLE (inf_le_right : D ≤ W₂)).op t₂'
    have hd : (c.ι.app k).hom.app (op D) d = 0 := by
      simp only [d, map_sub, ι_app_res, h₁', h₂', map_homOfLE_map_homOfLE, sub_self]
    obtain ⟨W', hW'D, j, g, hCW', hg⟩ := exists_eq_zero_near_isCompact hc (hC₁.inter hC₂)
      (Set.inter_subset_inter hCW₁ hCW₂) k d hd
    obtain ⟨O₁, O₂, hO₁, hO₂, hCO₁, hCO₂, hO⟩ :=
      exists_isOpen_inter_subset hC₁ hC₂ W'.isOpen hCW'
    let W₁' := W₁ ⊓ ⟨O₁, hO₁⟩
    let W₂' := W₂ ⊓ ⟨O₂, hO₂⟩
    have hW₁'W₁ : W₁' ≤ W₁ := inf_le_left
    have hW₂'W₂ : W₂' ≤ W₂ := inf_le_left
    have hW'' : W₁' ⊓ W₂' ≤ W' := fun x hx => hO ⟨hx.1.2, hx.2.2⟩
    let u₁ := (F.obj j).obj.map (homOfLE hW₁'W₁).op ((F.map g).hom.app (op W₁) t₁')
    let u₂ := (F.obj j).obj.map (homOfLE hW₂'W₂).op ((F.map g).hom.app (op W₂) t₂')
    have hu : u₁ |_ (W₁' ⊓ W₂') = u₂ |_ (W₁' ⊓ W₂') := by
      rw [← sub_eq_zero]
      change (F.obj j).obj.map (homOfLE inf_le_left).op u₁ -
        (F.obj j).obj.map (homOfLE inf_le_right).op u₂ = 0
      have hzero := congrArg ((F.obj j).obj.map (homOfLE hW'').op) hg
      rw [map_zero, map_app_res, map_homOfLE_map_homOfLE] at hzero
      rw [← hzero]
      simp only [u₁, u₂, d, map_sub, map_homOfLE_map_homOfLE, map_app_res]
    obtain ⟨u, hu₁, hu₂⟩ := Stacks.Topology.exists_glue_pair (Z := X) (F.obj j) u₁ u₂ hu
    refine ⟨C₁ ∪ C₂, hC₁.union hC₂, Set.union_subset_union hSC₁ hTC₂, W₁' ⊔ W₂',
      sup_le (hW₁'W₁.trans hW₁) (hW₂'W₂.trans hW₂), j, u,
      Set.union_subset_union (fun x hx => ⟨hCW₁ hx, hCO₁ hx⟩)
        (fun x hx => ⟨hCW₂ hx, hCO₂ hx⟩), ?_⟩
    refine TopCat.Sheaf.eq_of_locally_eq₂ (F := c.pt) (homOfLE (le_sup_left : W₁' ≤ W₁' ⊔ W₂'))
      (homOfLE (le_sup_right : W₂' ≤ W₁' ⊔ W₂')) le_rfl _ _ ?_ ?_
    · change c.pt.obj.map _ _ = c.pt.obj.map _ _
      rw [← ι_app_res, map_homOfLE_map_homOfLE]
      change (c.ι.app j).hom.app _ (u |_ W₁') = _
      rw [hu₁]
      simp only [u₁, ι_app_res, ι_app_map_apply, h₁', map_homOfLE_map_homOfLE]
    · change c.pt.obj.map _ _ = c.pt.obj.map _ _
      rw [← ι_app_res, map_homOfLE_map_homOfLE]
      change (c.ι.app j).hom.app _ (u |_ W₂') = _
      rw [hu₂]
      simp only [u₂, ι_app_res, ι_app_map_apply, h₂', map_homOfLE_map_homOfLE]
  · intro x hx
    obtain ⟨V, hVU, i, t, hxV, h⟩ := exists_local_rep hc s (hKU hx)
    obtain ⟨C, hCx, hCV, hC⟩ := local_compact_nhds (V.isOpen.mem_nhds hxV)
    exact ⟨C, mem_nhdsWithin_of_mem_nhds hCx, C, hC, subset_rfl, V, hVU, i, t, hCV, h⟩

/-- **Global sections commute with filtered colimits on a compact Hausdorff space.** -/
theorem isIso_colimit_post_sectionsTop [IsFiltered I] [CompactSpace X] [T2Space X]
    (F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsIso (colimit.post F
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤))) := by
  let Γ := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)
  have hι : ∀ (i : I) (y : ToType ((F ⋙ Γ).obj i)),
      colimit.post F Γ (colimit.ι (F ⋙ Γ) i y) = (colimit.ι F i).hom.app (op ⊤) y := by
    intro i y
    rw [← ConcreteCategory.comp_apply, colimit.ι_post]
    rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨i, y, rfl⟩ := Concrete.colimit_exists_rep (F ⋙ Γ) x
    rw [hι] at hx
    obtain ⟨W, hW, j, f, hKW, hf⟩ := exists_eq_zero_near_isCompact (colimit.isColimit F)
      isCompact_univ (Set.subset_univ _) i y hx
    have hWtop : (⊤ : Opens X) ≤ W := fun x _ => hKW (Set.mem_univ x)
    have hf' := congrArg ((F.obj j).obj.map (homOfLE hWtop).op) hf
    rw [map_zero, ← map_app_res, map_homOfLE_map_homOfLE, map_homOfLE_self] at hf'
    rw [← colimit.w_apply (F ⋙ Γ) f y]
    change colimit.ι (F ⋙ Γ) j ((F.map f).hom.app (op ⊤) y) = 0
    rw [hf', map_zero]
  · intro s
    obtain ⟨W, hW, i, t, hKW, h⟩ := exists_rep_near_isCompact (colimit.isColimit F)
      isCompact_univ (Set.subset_univ _) s
    have hWtop : (⊤ : Opens X) ≤ W := fun x _ => hKW (Set.mem_univ x)
    refine ⟨colimit.ι (F ⋙ Γ) i ((F.obj i).obj.map (homOfLE hWtop).op t), ?_⟩
    rw [hι]
    refine (ι_app_res (c := colimit.cocone F) i hWtop t).trans ?_
    rw [h, map_homOfLE_map_homOfLE, map_homOfLE_self]

/-- **Global sections commute with filtered colimits on a compact Hausdorff space.** -/
theorem preservesColimitsOfShape_sectionsTop [IsFiltered I] [CompactSpace X] [T2Space X] :
    PreservesColimitsOfShape I
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)) :=
  ⟨fun {F} => by
    have := isIso_colimit_post_sectionsTop F
    exact preservesColimit_of_isIso_post _ _⟩

/-- **A filtered colimit of soft sheaves on a compact Hausdorff space is soft.** -/
theorem isSoft_of_isColimit [IsFiltered I] [CompactSpace X] [T2Space X] (hc : IsColimit c)
    (hF : ∀ i, Stacks.Topology.IsSoft (F.obj i)) : Stacks.Topology.IsSoft c.pt := by
  intro K hK U hKU s
  obtain ⟨W, hWU, i, t, hKW, h⟩ := exists_rep_near_isCompact hc hK.isCompact hKU s
  obtain ⟨t', V, hVW, hKV, ht'⟩ := hF i K hK W hKW t
  refine ⟨(c.ι.app i).hom.app (op ⊤) t', V, hVW.trans hWU, hKV, ?_⟩
  change c.pt.obj.map _ _ = c.pt.obj.map _ _
  rw [← ι_app_res]
  change (c.ι.app i).hom.app (op V) ((F.obj i).obj.map _ t') = _
  change (F.obj i).obj.map _ t' = (F.obj i).obj.map _ t at ht'
  rw [ht', ι_app_res, h, map_homOfLE_map_homOfLE]

/-- An injective abelian sheaf is soft: its restriction maps are surjective. -/
theorem isSoft_of_injective (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [hG : Injective G] : Stacks.Topology.IsSoft G := by
  have hG' : @Injective (TopCat.Sheaf AddCommGrpCat.{u} X) _ G := hG
  have : TopCat.Sheaf.IsFlasque (C := AddCommGrpCat.{u}) (X := X) G :=
    ⟨fun {U V} i ↦ (AddCommGrpCat.epi_iff_surjective _).2
      (Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective
        (X := X) G (leOfHom i.unop))⟩
  exact Stacks.Topology.IsSoft.of_isFlasque G

open Stacks.Cohomology.AbelianColimit in
/-- **Soft sheaves on a compact Hausdorff space are acyclic for global sections**, in the form of
the vanishing of the right derived functors of sections over `⊤`. The proof is dimension shifting
along an embedding into an injective sheaf, which is soft, with soft quotient. -/
theorem isZero_rightDerived_sectionsTop_of_isSoft [CompactSpace X] [T2Space X] (n : ℕ) :
    ∀ G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}, Stacks.Topology.IsSoft G →
      IsZero ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived (n + 1)).obj G) := by
  let D := cohomologyDeltaFunctor (X := X) (⊤ : Opens X)
  induction n with
  | zero =>
    intro G hG
    let S := ShortComplex.cokernelSequence (Injective.ι G)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _,
        mono_f := (inferInstance : Mono (Injective.ι G)),
        epi_g := (inferInstance : Epi (cokernel.π (Injective.ι G))) }
    have h₂ : Stacks.Topology.IsSoft S.X₂ := isSoft_of_injective (Injective.under G)
    have hz : IsZero ((D.functor 1).obj S.X₂) :=
      Functor.isZero_rightDerived_obj_injective_succ _ 0 (Injective.under G)
    have hepi : Epi (D.δ hS 0) := D.epi_δ_of_map_f_eq_zero hS 0 (hz.eq_of_tgt _ _)
    have hΓ : Epi ((abSections (X := X) ⊤).map S.g) :=
      (AddCommGrpCat.epi_iff_surjective _).2
        (Stacks.Topology.surjective_sections_of_isSoft_univLE (Z := X) (S := S) hS hG)
    have hR : Epi ((D.functor 0).map S.g) := by
      change Epi (((abSections (X := X) ⊤).rightDerived 0).map S.g)
      rw [← NatIso.naturality_2 (abSections (X := X) ⊤).rightDerivedZeroIsoSelf S.g]
      infer_instance
    have hδ : D.δ hS 0 = 0 :=
      (cancel_epi ((D.functor 0).map S.g)).1 (by rw [D.map_g_δ, comp_zero])
    exact @IsZero.of_epi_eq_zero _ _ _ _ _ (D.δ hS 0) hepi hδ
  | succ n ih =>
    intro G hG
    let S := ShortComplex.cokernelSequence (Injective.ι G)
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _,
        mono_f := (inferInstance : Mono (Injective.ι G)),
        epi_g := (inferInstance : Epi (cokernel.π (Injective.ι G))) }
    have h₂ : Stacks.Topology.IsSoft S.X₂ := isSoft_of_injective (Injective.under G)
    have h₃ : Stacks.Topology.IsSoft S.X₃ :=
      Stacks.Topology.IsSoft.of_shortExact_univLE (Z := X) (S := S) hS hG h₂
    have hz : IsZero ((D.functor (n + 2)).obj S.X₂) :=
      Functor.isZero_rightDerived_obj_injective_succ _ (n + 1) (Injective.under G)
    have hepi : Epi (D.δ hS (n + 1)) := D.epi_δ_of_map_f_eq_zero hS (n + 1) (hz.eq_of_tgt _ _)
    have hδ : D.δ hS (n + 1) = 0 := (ih S.X₃ h₃).eq_of_src _ _
    exact @IsZero.of_epi_eq_zero _ _ _ _ _ (D.δ hS (n + 1)) hepi hδ

/-- **Cohomology commutes with filtered colimits on a compact Hausdorff space**, as right derived
functors of global sections. -/
theorem isIso_colimit_post_rightDerived_sectionsTop [IsFiltered I] [CompactSpace X] [T2Space X]
    (F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (colimit.post F
      (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).rightDerived
        q)) :=
  haveI := preservesColimitsOfShape_sectionsTop (X := X) (I := I)
  Stacks.Cohomology.AbelianColimit.isIso_colimit_post_rightDerived_of_isZero (X := X) ⊤
    (fun E hE n => isZero_rightDerived_sectionsTop_of_isSoft n _
      (isSoft_of_isColimit (colimit.isColimit E) fun i => haveI := hE i; isSoft_of_injective _))
    F q

/-- **Sheaf cohomology commutes with filtered colimits on a compact Hausdorff space**, for the
`Ext`-groups taken in the universe of the space. -/
theorem preservesColimitsOfShape_functorH [IsFiltered I] [CompactSpace X] [T2Space X] (ν : ℕ) :
    PreservesColimitsOfShape I (Sheaf.functorH.{u} (Opens.grothendieckTopology X) ν) := by
  have e := Stacks.Cohomology.GlobalSections.rightDerivedSectionsIsoFunctorH
    (Opens.grothendieckTopology X) (⊤ : Opens X) isTerminalTop ν
  have : PreservesColimitsOfShape I
      (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).rightDerived
        ν) :=
    ⟨fun {F} => by
      have := isIso_colimit_post_rightDerived_sectionsTop F ν
      exact preservesColimit_of_isIso_post _ _⟩
  exact preservesColimitsOfShape_of_natIso e

/-- The constant sheaf functor is a left adjoint, so it preserves colimits. -/
theorem preservesColimitsOfShape_constantSheaf :
    PreservesColimitsOfShape I (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  have : PreservesColimitsOfSize.{u, u}
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens X))).leftAdjoint_preservesColimits
  inferInstance

/-- **Cohomology with constant coefficients commutes with filtered colimits of the coefficient
groups on a compact Hausdorff space**: `colimᵢ H^ν(X, Mᵢ) ⟶ H^ν(X, colimᵢ Mᵢ)` is an
isomorphism, for the `Ext`-groups taken in the universe of the space. -/
theorem isIso_colimit_post_constantSheaf_comp_functorH [IsFiltered I] [CompactSpace X]
    [T2Space X] (M : I ⥤ AddCommGrpCat.{u}) (ν : ℕ) :
    IsIso (colimit.post M (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      Sheaf.functorH.{u} (Opens.grothendieckTopology X) ν)) := by
  have := preservesColimitsOfShape_constantSheaf (X := X) (I := I)
  have := preservesColimitsOfShape_functorH (X := X) (I := I) ν
  infer_instance

end Colimits

section TensorAlgebra

open TensorProduct

theorem uliftZMultiplesAddEquiv_symm_apply_apply (A : AddCommGrpCat.{u}) (a : A)
    (n : ULift.{u} ℤ) : (AddCommGrpCat.uliftZMultiplesAddEquiv A).symm a n = n.down • a :=
  rfl

theorem uliftZMultiplesAddEquiv_symm_comp {A B : AddCommGrpCat.{u}} (g : A ⟶ B) (a : A) :
    (AddCommGrpCat.uliftZMultiplesAddEquiv A).symm a ≫ g =
      (AddCommGrpCat.uliftZMultiplesAddEquiv B).symm (g a) := by
  ext n
  rw [ConcreteCategory.comp_apply, uliftZMultiplesAddEquiv_symm_apply_apply,
    uliftZMultiplesAddEquiv_symm_apply_apply, map_zsmul]

theorem uliftZMultiplesAddEquiv_symm_ulift (k : ULift.{u} ℤ) :
    ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm k :
      AddCommGrpCat.of (ULift.{u} ℤ) ⟶ AddCommGrpCat.of (ULift.{u} ℤ)) = k.down • 𝟙 _ := by
  ext n
  rw [uliftZMultiplesAddEquiv_symm_apply_apply]
  change (n.down • k).down = (k.down • n).down
  simp [mul_comm]

theorem tensorMap_comp {A B C : AddCommGrpCat.{u}} {N : Type*} [AddCommGroup N] (f : A ⟶ B)
    (g : B ⟶ C) (z : A ⊗[ℤ] N) :
    map (f ≫ g).hom.toIntLinearMap (LinearMap.id : N →ₗ[ℤ] N) z =
      map g.hom.toIntLinearMap LinearMap.id (map f.hom.toIntLinearMap LinearMap.id z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

theorem tensorMap_congr {A B : AddCommGrpCat.{u}} {N : Type*} [AddCommGroup N] {f g : A ⟶ B}
    (h : f = g) (z : A ⊗[ℤ] N) :
    map f.hom.toIntLinearMap (LinearMap.id : N →ₗ[ℤ] N) z =
      map g.hom.toIntLinearMap LinearMap.id z := by
  rw [h]

theorem tensorMap_id {A : AddCommGrpCat.{u}} {N : Type*} [AddCommGroup N] (z : A ⊗[ℤ] N) :
    map (AddCommGrpCat.Hom.hom (𝟙 A)).toIntLinearMap (LinearMap.id : N →ₗ[ℤ] N) z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- `- ⊗ N` on morphisms, as an additive function of the morphism. -/
noncomputable def tensorMapHom (A B : AddCommGrpCat.{u}) (N : Type*) [AddCommGroup N]
    (z : A ⊗[ℤ] N) : (A ⟶ B) →+ B ⊗[ℤ] N where
  toFun f := map f.hom.toIntLinearMap LinearMap.id z
  map_zero' := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact zero_tmul _ _
    | add z z' hz hz' => simp only [map_add, hz, hz', add_zero]
  map_add' f g := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact add_tmul _ _ _
    | add z z' hz hz' => simp only [map_add, hz, hz']; abel

section FGSubgroups

variable (M : Type u) [AddCommGroup M]

/-- The finitely generated subgroups of an abelian group, ordered by inclusion. -/
abbrev FGSubgroup : Type u := {N : Submodule ℤ M // N.FG}

instance : IsFiltered (FGSubgroup M) := by
  have : IsDirected (FGSubgroup M) (· ≤ ·) :=
    ⟨fun a b => ⟨⟨a.1 ⊔ b.1, a.2.sup b.2⟩, le_sup_left, le_sup_right⟩⟩
  have : Nonempty (FGSubgroup M) := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  exact isFiltered_of_directed_le_nonempty _

/-- The diagram of finitely generated subgroups of `M`. -/
noncomputable def fgSubgroupDiagram : FGSubgroup M ⥤ AddCommGrpCat.{u} where
  obj N := AddCommGrpCat.of N.1
  map h := AddCommGrpCat.ofHom (Submodule.inclusion (leOfHom h)).toAddMonoidHom

/-- `M` as the union of its finitely generated subgroups. -/
noncomputable def fgSubgroupCocone : Cocone (fgSubgroupDiagram M) where
  pt := AddCommGrpCat.of M
  ι := { app N := AddCommGrpCat.ofHom N.1.subtype.toAddMonoidHom }

/-- **An abelian group is the filtered colimit of its finitely generated subgroups.** -/
noncomputable def isColimitFGSubgroupCocone : IsColimit (fgSubgroupCocone M) := by
  have := reflectsColimitsOfShape_of_reflectsIsomorphisms (G := forget AddCommGrpCat.{u})
    (J := FGSubgroup M)
  refine isColimitOfReflects (forget AddCommGrpCat.{u})
    (Types.FilteredColimit.isColimitOf _ _ (fun (x : M) => ?_) fun i j xi xj h => ?_)
  · exact ⟨⟨Submodule.span ℤ {x}, Submodule.fg_span_singleton x⟩,
      ⟨x, Submodule.mem_span_singleton_self x⟩, rfl⟩
  · refine ⟨⟨i.1 ⊔ j.1, i.2.sup j.2⟩, homOfLE le_sup_left, homOfLE le_sup_right, ?_⟩
    exact Subtype.ext h

end FGSubgroups

end TensorAlgebra

section ExtUniverse

variable {X : TopCat.{u}} {I : Type u} [SmallCategory I]
  {F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} {c : Cocone F}
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- **Every cohomology class of a filtered colimit of sheaves comes from a member of the
diagram**, on a compact Hausdorff space. -/
theorem exists_H_map_eq_of_isColimit [IsFiltered I] [CompactSpace X] [T2Space X]
    (hc : IsColimit c) (ν : ℕ) (y : Sheaf.H.{w} c.pt ν) :
    ∃ (i : I) (x : Sheaf.H.{w} (F.obj i) ν), Sheaf.H.map (c.ι.app i) ν x = y := by
  have := preservesColimitsOfShape_functorH (X := X) (I := I) ν
  have hc' := isColimitOfPreserves (Sheaf.functorH.{u} (Opens.grothendieckTopology X) ν) hc
  let e : ∀ G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      Sheaf.H.{w} G ν ≃+ Sheaf.H.{u} G ν :=
    fun G => Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv
  obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep _ hc' (e c.pt y)
  let x' : Sheaf.H.{u} (F.obj i) ν := x
  refine ⟨i, (e (F.obj i)).symm x', (e c.pt).injective ?_⟩
  rw [Stacks.Cohomology.BiggerSite.extChgUnivAddEquiv_sheafH_map]
  change Sheaf.H.map _ ν ((e (F.obj i)) ((e (F.obj i)).symm x')) = (e c.pt) y
  rw [AddEquiv.apply_symm_apply, ← hx]
  rfl

/-- **A cohomology class of a member of a filtered diagram of sheaves which dies in the colimit
dies at a later stage**, on a compact Hausdorff space. -/
theorem exists_H_map_eq_zero_of_isColimit [IsFiltered I] [CompactSpace X] [T2Space X]
    (hc : IsColimit c) (ν : ℕ) (i : I) (x : Sheaf.H.{w} (F.obj i) ν)
    (hx : Sheaf.H.map (c.ι.app i) ν x = 0) :
    ∃ (j : I) (f : i ⟶ j), Sheaf.H.map (F.map f) ν x = 0 := by
  have := preservesColimitsOfShape_functorH (X := X) (I := I) ν
  have hc' := isColimitOfPreserves (Sheaf.functorH.{u} (Opens.grothendieckTopology X) ν) hc
  let e : ∀ G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      Sheaf.H.{w} G ν ≃+ Sheaf.H.{u} G ν :=
    fun G => Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv
  have hx' : ((Sheaf.functorH.{u} (Opens.grothendieckTopology X) ν).mapCocone c).ι.app i
      (e (F.obj i) x) = ((Sheaf.functorH.{u} (Opens.grothendieckTopology X) ν).mapCocone c).ι.app i
      0 := by
    rw [map_zero]
    change Sheaf.H.map _ ν (e (F.obj i) x) = 0
    rw [← Stacks.Cohomology.BiggerSite.extChgUnivAddEquiv_sheafH_map]
    change e c.pt _ = 0
    rw [hx, map_zero]
  obtain ⟨j, f, g, hfg⟩ := (Concrete.isColimit_rep_eq_iff_exists _ hc' _ _).mp hx'
  refine ⟨j, f, (e (F.obj j)).injective ?_⟩
  rw [map_zero]
  rw [Stacks.Cohomology.BiggerSite.extChgUnivAddEquiv_sheafH_map]
  change (Sheaf.functorH.{u} (Opens.grothendieckTopology X) ν).map (F.map f) (e (F.obj i) x) = 0
  exact hfg.trans (map_zero _)


section ConstantSheaf

variable {M : I ⥤ AddCommGrpCat.{u}} {d : Cocone M}

/-- **Every class of `H^ν(X, colimᵢ Mᵢ)` comes from some `H^ν(X, Mᵢ)`**, for a filtered colimit
of abelian groups and `X` compact Hausdorff. -/
theorem exists_H_constantSheaf_map_eq_of_isColimit [IsFiltered I] [CompactSpace X] [T2Space X]
    (hd : IsColimit d) (ν : ℕ)
    (y : Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj d.pt)
      ν) :
    ∃ (i : I) (x : Sheaf.H.{w}
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (M.obj i)) ν),
      Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        (d.ι.app i)) ν x = y := by
  have := preservesColimitsOfShape_constantSheaf (X := X) (I := I)
  exact exists_H_map_eq_of_isColimit
    (isColimitOfPreserves (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hd) ν y

/-- **A class of `H^ν(X, Mᵢ)` dying in `H^ν(X, colimᵢ Mᵢ)` dies in some `H^ν(X, Mⱼ)`**, for a
filtered colimit of abelian groups and `X` compact Hausdorff. -/
theorem exists_H_constantSheaf_map_eq_zero_of_isColimit [IsFiltered I] [CompactSpace X]
    [T2Space X] (hd : IsColimit d) (ν : ℕ) (i : I)
    (x : Sheaf.H.{w}
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (M.obj i)) ν)
    (hx : Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        (d.ι.app i)) ν x = 0) :
    ∃ (j : I) (f : i ⟶ j), Sheaf.H.map
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (M.map f)) ν x = 0 := by
  have := preservesColimitsOfShape_constantSheaf (X := X) (I := I)
  exact exists_H_map_eq_zero_of_isColimit (F := M ⋙ constantSheaf _ _)
    (isColimitOfPreserves (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hd) ν i
    x hx

end ConstantSheaf

section Tensor

open TensorProduct

variable (ν : ℕ)

/-- `H^ν(X, -)` on morphisms of coefficient groups, as an additive function of the morphism. -/
noncomputable def mapHom (A B : AddCommGrpCat.{u})
    (y : Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) ν) :
    (A ⟶ B) →+
      Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj B) ν where
  toFun f := Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map f)
    ν y
  map_zero' := by simp [Sheaf.H.map_apply]
  map_add' f g := by simp [Functor.map_add]

/-- The pairing `A × H^ν(X, ℤ) → H^ν(X, A)`, `(a, x) ↦ (1 ↦ a)_* x`. -/
noncomputable def coefficientPairing (A : AddCommGrpCat.{u}) :
    A →+ Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ν →+
      Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) ν where
  toFun a := Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm a)) ν
  map_zero' := by ext x; simp [Sheaf.H.map_apply]
  map_add' a b := by ext x; simp [Functor.map_add]

/-- **The universal coefficient map** `A ⊗ H^ν(X, ℤ) → H^ν(X, A)`, `a ⊗ x ↦ (1 ↦ a)_* x`. -/
noncomputable def tensorCohomologyMap (A : AddCommGrpCat.{u}) :
    A ⊗[ℤ] Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ν →+
      Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) ν :=
  liftAddHom (coefficientPairing ν A) fun r a x => by
    rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul]

theorem tensorCohomologyMap_tmul (A : AddCommGrpCat.{u}) (a : A)
    (x : Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ν) :
    tensorCohomologyMap ν A (a ⊗ₜ x) =
      Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm a)) ν x :=
  liftAddHom_tmul _ _ _ _

/-- **Naturality of the universal coefficient map** in the coefficient group. -/
theorem tensorCohomologyMap_naturality {A B : AddCommGrpCat.{u}} (g : A ⟶ B)
    (z : A ⊗[ℤ] Sheaf.H.{w}
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) ν) :
    tensorCohomologyMap ν B (map g.hom.toIntLinearMap LinearMap.id z) =
      Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map g) ν
        (tensorCohomologyMap ν A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [map_tmul, tensorCohomologyMap_tmul, tensorCohomologyMap_tmul, ← Sheaf.H.map_comp_apply,
      ← Functor.map_comp, uliftZMultiplesAddEquiv_symm_comp]
    rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

theorem H_map_constantSheaf_zsmul {A B : AddCommGrpCat.{u}} (n : ℤ) (f : A ⟶ B)
    (x : Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) ν) :
    Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map (n • f)) ν
      x = n • Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map f)
        ν x :=
  map_zsmul (mapHom ν A B x) n f

/-- The universal coefficient map is bijective for `A = ℤ`: it is `k ⊗ x ↦ k • x`. -/
theorem bijective_tensorCohomologyMap_ulift :
    Function.Bijective (tensorCohomologyMap.{w} (X := X) ν (AddCommGrpCat.of (ULift.{u} ℤ))) := by
  have h1 : ∀ x, tensorCohomologyMap.{w} (X := X) ν (AddCommGrpCat.of (ULift.{u} ℤ))
      (ULift.up (1 : ℤ) ⊗ₜ x) = x := by
    intro x
    rw [tensorCohomologyMap_tmul, uliftZMultiplesAddEquiv_symm_ulift, H_map_constantSheaf_zsmul,
      CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply, one_smul]
  have h2 : ∀ z, ULift.up (1 : ℤ) ⊗ₜ
      tensorCohomologyMap.{w} (X := X) ν (AddCommGrpCat.of (ULift.{u} ℤ)) z = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k x =>
      rw [tensorCohomologyMap_tmul, uliftZMultiplesAddEquiv_symm_ulift, H_map_constantSheaf_zsmul,
        CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply, tmul_smul, smul_tmul']
      congr 1
      ext
      simp
    | add z z' hz hz' => rw [map_add, tmul_add, hz, hz']
  exact ⟨fun a b hab => by rw [← h2 a, ← h2 b, hab], fun y => ⟨_, h1 y⟩⟩

/-- **The universal coefficient map is bijective on a retract of a finite sum of copies of `ℤ`**,
by naturality and the case of `ℤ` itself. -/
theorem bijective_tensorCohomologyMap_of_sum_eq_id {A : AddCommGrpCat.{u}} {ι : Type*}
    (s : Finset ι) (π : ι → (A ⟶ AddCommGrpCat.of (ULift.{u} ℤ)))
    (j : ι → (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ A)) (h : ∑ i ∈ s, π i ≫ j i = 𝟙 A) :
    Function.Bijective (tensorCohomologyMap.{w} (X := X) ν A) := by
  let e := Equiv.ofBijective _ (bijective_tensorCohomologyMap_ulift.{w} (X := X) ν)
  let ψ : Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) ν →
      A ⊗[ℤ] Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) ν := fun y =>
    ∑ i ∈ s, map (j i).hom.toIntLinearMap LinearMap.id
      (e.symm (Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).map (π i)) ν y))
  rw [Function.bijective_iff_has_inverse]
  refine ⟨ψ, fun z => ?_, fun y => ?_⟩
  · have he : ∀ i, e.symm (Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).map (π i)) ν (tensorCohomologyMap ν A z)) =
        map (π i).hom.toIntLinearMap LinearMap.id z := fun i => by
      rw [← tensorCohomologyMap_naturality]
      exact e.symm_apply_apply _
    calc ψ (tensorCohomologyMap ν A z)
        = ∑ i ∈ s, tensorMapHom A A _ z (π i ≫ j i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [he]
          exact (tensorMap_comp _ _ _).symm
      _ = z := by rw [← map_sum, h]; exact tensorMap_id (A := A) z
  · calc tensorCohomologyMap ν A (ψ y)
        = ∑ i ∈ s, mapHom ν A A y (π i ≫ j i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [tensorCohomologyMap_naturality]
          change Sheaf.H.map _ ν (e (e.symm _)) = _
          rw [e.apply_symm_apply]
          change _ = Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X)
            AddCommGrpCat.{u}).map (π i ≫ j i)) ν y
          rw [Functor.map_comp, Sheaf.H.map_comp_apply]
      _ = y := by
          rw [← map_sum, h]
          change Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X)
            AddCommGrpCat.{u}).map (𝟙 A)) ν y = y
          rw [CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]

/-- **The universal coefficient map is bijective for a finite free abelian group.** -/
theorem bijective_tensorCohomologyMap_of_free (N : Type u) [AddCommGroup N] [Module.Free ℤ N]
    [Module.Finite ℤ N] :
    Function.Bijective (tensorCohomologyMap.{w} (X := X) ν (AddCommGrpCat.of N)) := by
  let b := Module.Free.chooseBasis ℤ N
  refine bijective_tensorCohomologyMap_of_sum_eq_id ν Finset.univ
    (fun i => AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun n => ULift.up (b.repr n i))
      fun x y => by ext; simp))
    (fun i => (AddCommGrpCat.uliftZMultiplesAddEquiv _).symm (b i)) ?_
  ext n
  change AddCommGrpCat.homAddEquiv (∑ i, _) n = n
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  change ∑ i, (b.repr n i) • b i = n
  exact b.sum_repr n

/-- **Universal coefficients for torsion-free coefficients on a compact Hausdorff space.** For a
torsion-free abelian group `M` the universal coefficient map `M ⊗ H^ν(X, ℤ) → H^ν(X, M)` is
bijective. `M` is the filtered colimit of its finitely generated subgroups, which are free of
finite rank, both sides commute with that colimit, and the map is bijective on a finite free
group. -/
theorem bijective_tensorCohomologyMap_of_isTorsionFree [CompactSpace X] [T2Space X]
    (M : Type u) [AddCommGroup M] [Module.IsTorsionFree ℤ M] :
    Function.Bijective (tensorCohomologyMap.{w} (X := X) ν (AddCommGrpCat.of M)) := by
  have hc := isColimitFGSubgroupCocone M
  have hfree : ∀ N : FGSubgroup M,
      Function.Bijective (tensorCohomologyMap.{w} (X := X) ν ((fgSubgroupDiagram M).obj N)) :=
    fun N => by
      have : Module.Finite ℤ N.1 := Module.Finite.iff_fg.mpr N.2
      have : Module.Free ℤ N.1 := Module.free_of_finite_type_torsion_free'
      exact bijective_tensorCohomologyMap_of_free ν N.1
  -- every element of `M ⊗ H(ℤ)` comes from a finitely generated subgroup
  have hrep : ∀ z : M ⊗[ℤ] Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ν,
      ∃ (N : FGSubgroup M) (zN : (fgSubgroupDiagram M).obj N ⊗[ℤ] Sheaf.H.{w}
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) ν),
        map (AddCommGrpCat.Hom.hom ((fgSubgroupCocone M).ι.app N)).toIntLinearMap
          LinearMap.id zN = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨⟨⊥, Submodule.fg_bot⟩, 0, map_zero _⟩
    | tmul m x =>
      exact ⟨⟨Submodule.span ℤ {m}, Submodule.fg_span_singleton m⟩,
        (⟨m, Submodule.mem_span_singleton_self m⟩ : Submodule.span ℤ {m}) ⊗ₜ x, rfl⟩
    | add z z' hz hz' =>
      obtain ⟨N, zN, rfl⟩ := hz
      obtain ⟨N', zN', rfl⟩ := hz'
      let N'' : FGSubgroup M := ⟨N.1 ⊔ N'.1, N.2.sup N'.2⟩
      refine ⟨N'', map (AddCommGrpCat.Hom.hom ((fgSubgroupDiagram M).map
          (homOfLE (le_sup_left : N ≤ N'')))).toIntLinearMap LinearMap.id zN +
        map (AddCommGrpCat.Hom.hom ((fgSubgroupDiagram M).map
          (homOfLE (le_sup_right : N' ≤ N'')))).toIntLinearMap LinearMap.id zN', ?_⟩
      rw [map_add, ← tensorMap_comp, ← tensorMap_comp]
      exact congrArg₂ (· + ·) (tensorMap_congr ((fgSubgroupCocone M).w _) zN)
        (tensorMap_congr ((fgSubgroupCocone M).w _) zN')
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨N, zN, rfl⟩ := hrep z
    have hz' : Sheaf.H.map ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
        ((fgSubgroupCocone M).ι.app N)) ν (tensorCohomologyMap.{w} (X := X) ν _ zN) = 0 :=
      (tensorCohomologyMap_naturality ν _ zN).symm.trans hz
    obtain ⟨N', f, hf⟩ := exists_H_constantSheaf_map_eq_zero_of_isColimit hc ν N _ hz'
    rw [← tensorCohomologyMap_naturality, ← map_zero (tensorCohomologyMap.{w} (X := X) ν _)] at hf
    have h0 := (hfree N').1 hf
    change map (AddCommGrpCat.Hom.hom ((fgSubgroupCocone M).ι.app N)).toIntLinearMap
      LinearMap.id zN = 0
    rw [← tensorMap_congr ((fgSubgroupCocone M).w f) zN, tensorMap_comp, h0, map_zero]
  · intro y
    obtain ⟨N, x, rfl⟩ := exists_H_constantSheaf_map_eq_of_isColimit hc ν y
    obtain ⟨zN, rfl⟩ := (hfree N).2 x
    exact ⟨_, tensorCohomologyMap_naturality ν _ zN⟩

/-- **Universal coefficients for torsion-free coefficients on a compact Hausdorff space**, as an
additive equivalence `M ⊗_ℤ H^ν(X, ℤ) ≃+ H^ν(X, M)`. -/
noncomputable def tensorCohomologyAddEquiv [CompactSpace X] [T2Space X] (M : Type u)
    [AddCommGroup M] [Module.IsTorsionFree ℤ M] :
    M ⊗[ℤ] Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ν ≃+
      Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of M)) ν :=
  AddEquiv.ofBijective (tensorCohomologyMap ν (AddCommGrpCat.of M))
    (bijective_tensorCohomologyMap_of_isTorsionFree ν M)

theorem tensorCohomologyAddEquiv_apply [CompactSpace X] [T2Space X] (M : Type u)
    [AddCommGroup M] [Module.IsTorsionFree ℤ M]
    (z : M ⊗[ℤ] Sheaf.H.{w} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ν) :
    tensorCohomologyAddEquiv.{w} (X := X) ν M z = tensorCohomologyMap ν (AddCommGrpCat.of M) z :=
  rfl

/-- **Universal coefficients for flat coefficients on a compact Hausdorff space.** A flat abelian
group is torsion-free. -/
theorem bijective_tensorCohomologyMap_of_flat [CompactSpace X] [T2Space X] (M : Type u)
    [AddCommGroup M] [Module.Flat ℤ M] :
    Function.Bijective (tensorCohomologyMap.{w} (X := X) ν (AddCommGrpCat.of M)) :=
  bijective_tensorCohomologyMap_of_isTorsionFree ν M

end Tensor

end ExtUniverse

end CompactHausdorffCohomology
