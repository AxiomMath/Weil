module

public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.LocalImageSheaf
public import Weil.Attr

/-!
# `l`-torsion sheaves

Let `l` be a natural number. An abelian sheaf `F` on a site is *`l`-torsion* when every section is
locally annihilated by a power of `l`: for every object `U` and every `s ∈ F(U)` there is a
covering sieve of `U` such that for each of its members `V ⟶ U` some power `l ^ v` kills the
restriction of `s` to `V`. In other words `F` is the union, as a sheaf, of the kernels of the
multiplications `l ^ v : F ⟶ F`. On the small étale site of a scheme this is the notion of
`l`-torsion sheaf of Freitag and Kiehl, I.12.

The `l`-torsion sheaves form a Serre subcategory of the abelian sheaves, so the corresponding full
subcategory is abelian and its inclusion is exact. For `0 < l` every `l`-torsion sheaf is a torsion
sheaf (`Stacks.Torsion.torsionSheafProperty`).

## Main definitions

* `CategoryTheory.lTorsionSheafProperty`: the property of an abelian sheaf on a site of being
  `l`-torsion.
* `AlgebraicGeometry.SmallEtale.IsLTorsionSheaf`: `l`-torsion abelian sheaves on the small étale
  site of a scheme `S`.
* `AlgebraicGeometry.SmallEtale.LTorsionSheaf`: the full subcategory of `l`-torsion sheaves.

## Main results

* `CategoryTheory.lTorsionSheafProperty_isSerreClass`: `l`-torsion sheaves form a Serre
  subcategory.
* `CategoryTheory.lTorsionSheafProperty_le_torsionSheafProperty`: for `0 < l`, an `l`-torsion
  sheaf is a torsion sheaf.
* `CategoryTheory.exists_pow_nsmul_eq_zero_of_isQuasiCompactObject`: a section of an `l`-torsion
  sheaf over a quasi-compact object is killed by a single power of `l`.
* `AlgebraicGeometry.SmallEtale.isLTorsionSheaf_iff_forall_exists_pow_nsmul_eq_zero`: for a
  locally noetherian `S`, an abelian sheaf is `l`-torsion if and only if every section over every
  noetherian separated étale `S`-scheme is killed by a power of `l`.

## Implementation notes

Freitag and Kiehl assume `l` invertible on the scheme; the definition does not use this, and it is
stated for every natural number `l` and every scheme.

Freitag and Kiehl quantify over the objects of their category `Et(S)` of noetherian separated
étale `S`-schemes. The definition here quantifies over all objects of the small étale site
`AlgebraicGeometry.SmallEtale`; for a locally noetherian `S` the two agree, and on a noetherian
object the local powers can be replaced by a single one
(`AlgebraicGeometry.SmallEtale.isLTorsionSheaf_iff_forall_exists_pow_nsmul_eq_zero`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
* [SGA 4, IX 1.1]
-/

@[expose] public section

open CategoryTheory Limits ZeroObject Opposite

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The property that an abelian sheaf is `l`-torsion: every section is locally annihilated by a
power of `l`. -/
def lTorsionSheafProperty (l : ℕ) : ObjectProperty (Sheaf J AddCommGrpCat.{w}) :=
  fun F ↦ ∀ (U : C) (x : F.obj.obj (op U)),
    ∃ R : Sieve U, R ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), R f → ∃ v : ℕ, l ^ v • (F.obj.map f.op x) = 0

variable {J}

/-- For `0 < l`, an `l`-torsion sheaf is a torsion sheaf. -/
theorem lTorsionSheafProperty_le_torsionSheafProperty {l : ℕ} (hl : 0 < l) :
    lTorsionSheafProperty.{w} J l ≤ Stacks.Torsion.torsionSheafProperty J := by
  intro F hF U x
  obtain ⟨R, hR, h⟩ := hF U x
  exact ⟨R, hR, fun V f hf ↦ by
    obtain ⟨v, hv⟩ := h V f hf
    exact ⟨l ^ v, pow_pos hl v, hv⟩⟩

/-- **On a quasi-compact object a section of an `l`-torsion sheaf is killed by one power of
`l`.** -/
theorem exists_pow_nsmul_eq_zero_of_isQuasiCompactObject {l : ℕ} {F : Sheaf J AddCommGrpCat.{w}}
    (hF : lTorsionSheafProperty J l F) {U : C} (hU : J.IsQuasiCompactObject U)
    (x : F.obj.obj (op U)) : ∃ v : ℕ, l ^ v • x = 0 := by
  classical
  obtain ⟨R, hR, hx⟩ := hF U x
  let 𝒰 : PreZeroHypercover.{max u v} U :=
    { I₀ := Σ V : C, {f : V ⟶ U // R f}, X := fun i ↦ i.1, f := fun i ↦ i.2.1 }
  have hle : R ≤ 𝒰.sieve₀ := fun V f hf ↦ 𝒰.sieve₀_f ⟨V, f, hf⟩
  choose n hnx using fun i : 𝒰.I₀ ↦ hx i.1 i.2.1 i.2.2
  obtain ⟨𝒱, φ, h𝒱, hfin⟩ := hU 𝒰 (J.superset_covering hle hR)
  refine ⟨∑ i ∈ hfin.toFinset, n i, ?_⟩
  refine Stacks.Torsion.sheaf_section_eq_zero_of_mem F _ h𝒱 ?_
  rintro V f ⟨Y, h, g, ⟨j⟩, rfl⟩
  have hle : n (φ.s₀ j) ≤ ∑ i ∈ hfin.toFinset, n i :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (hfin.mem_toFinset.mpr (Set.mem_range_self j))
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  rw [← φ.w₀ j, op_comp, op_comp, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, map_nsmul, he, pow_add, mul_comm, mul_smul]
  change F.obj.map h.op (F.obj.map (φ.h₀ j).op (l ^ e • l ^ n (φ.s₀ j) • F.obj.map
    (φ.s₀ j).2.1.op x)) = 0
  rw [hnx, smul_zero, map_zero, map_zero]

section Serre

variable [HasSheafify J AddCommGrpCat.{w}]

/-- Given a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of abelian sheaves, a section `x` of `F₂`
over `U` and `f : V ⟶ U` such that `n` kills the image of `x|_V` in `F₃`, the section `n • x|_V`
comes from `F₁`. -/
private theorem exists_kernel_lift_of_nsmul {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) {U V : C} (f : V ⟶ U) (x : S.X₂.obj.obj (op U))
    (n : ℕ) (hn : n • S.X₃.obj.map f.op (S.g.hom.app (op U) x) = 0) :
    ∃ y : S.X₁.obj.obj (op V), S.f.hom.app (op V) y = n • S.X₂.obj.map f.op x := by
  let E := (sheafSections J AddCommGrpCat.{w}).obj (op V)
  have : PreservesFiniteLimits E :=
    preservesFiniteLimits_of_natIso
      (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{w} (X := V)).symm
  have : E.Additive := E.additive_of_preserves_binary_products
  have hex : (S.map E).Exact :=
    (hS.exact.map_of_mono_of_preservesKernel E (hS.mono_f) inferInstance)
  have hz : (S.map E).g (n • S.X₂.obj.map f.op x) = 0 := by
    change S.g.hom.app (op V) (n • S.X₂.obj.map f.op x) = 0
    rw [_root_.map_nsmul, NatTrans.naturality_apply S.g.hom f.op x, hn]
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp hex _ hz
  exact ⟨y, hy⟩

/-- **`l`-torsion sheaves form a Serre subcategory.** -/
instance lTorsionSheafProperty_isSerreClass (l : ℕ) :
    (lTorsionSheafProperty.{w} J l).IsSerreClass where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro U x
    refine ⟨⊤, J.top_mem U, ?_⟩
    intro V f hf
    refine ⟨0, ?_⟩
    have hx : x = 0 := (AddCommGrpCat.isZero_iff_subsingleton.mp
      (((sheafSections J AddCommGrpCat.{w}).obj (op U)).map_isZero
        (isZero_zero (Sheaf J AddCommGrpCat.{w})))).elim _ _
    simp [hx]
  prop_of_mono := by
    intro F G f hf hG U x
    obtain ⟨R, hR, hkill⟩ := hG U (f.hom.app (op U) x)
    refine ⟨R, hR, ?_⟩
    intro V g hg
    obtain ⟨n, hk⟩ := hkill V g hg
    have hinj : Function.Injective (f.hom.app (op V)) := by
      have : Mono ((sheafToPresheaf J AddCommGrpCat.{w}).map f) := inferInstance
      have : Mono (((sheafToPresheaf J AddCommGrpCat.{w}).map f).app (op V)) := inferInstance
      exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    refine ⟨n, hinj ?_⟩
    rwa [_root_.map_nsmul, map_zero, NatTrans.naturality_apply f.hom g.op x]
  prop_of_epi := by
    intro F G f hf hF U y
    let R := Presheaf.imageSieve f.hom y
    have hR : R ∈ J U := (Stacks.Sites.LocalImage.epi_localSurjective J f).imageSieve_mem y
    let T : ∀ ⦃V : C⦄ ⦃g : V ⟶ U⦄, R g → Sieve V := fun {V} {g} hg => by
      change ∃ z, f.hom.app (op V) z = G.obj.map g.op y at hg
      exact (hF V hg.choose).choose
    have hT : ∀ ⦃V : C⦄ ⦃g : V ⟶ U⦄ (hg : R g), T hg ∈ J V := by
      intro V g hg
      change ∃ z, f.hom.app (op V) z = G.obj.map g.op y at hg
      exact (hF V hg.choose).choose_spec.1
    refine ⟨Sieve.bind R T, J.bind_covering hR hT, ?_⟩
    intro W h hh
    obtain ⟨V, k, g, hg, hk, rfl⟩ := hh
    change ∃ z, f.hom.app (op V) z = G.obj.map g.op y at hg
    let z := hg.choose
    have hz := hg.choose_spec
    dsimp only [T] at hk
    obtain ⟨n, hkill⟩ := (hF V z).choose_spec.2 W k hk
    refine ⟨n, ?_⟩
    have hmap : f.hom.app (op W) (F.obj.map k.op z) = G.obj.map (k ≫ g).op y := by
      rw [NatTrans.naturality_apply f.hom k.op z, hz]
      simp [Functor.map_comp]
    have hkill' := congrArg (f.hom.app (op W)) hkill
    rwa [_root_.map_nsmul, map_zero, hmap] at hkill'
  prop_X₂_of_shortExact := by
    intro S hS h₁ h₃ U x
    obtain ⟨R, hR, hq⟩ := h₃ U (S.g.hom.app (op U) x)
    let ksec : ∀ ⦃V : C⦄ ⦃u : V ⟶ U⦄, R u → S.X₁.obj.obj (op V) :=
      fun {V} {u} hu =>
        (exists_kernel_lift_of_nsmul hS u x (l ^ (hq V u hu).choose)
          (hq V u hu).choose_spec).choose
    have hksec : ∀ ⦃V : C⦄ ⦃u : V ⟶ U⦄ (hu : R u),
        S.f.hom.app (op V) (ksec hu) = l ^ (hq V u hu).choose • S.X₂.obj.map u.op x := by
      intro V u hu
      exact (exists_kernel_lift_of_nsmul hS u x (l ^ (hq V u hu).choose)
        (hq V u hu).choose_spec).choose_spec
    let T : ∀ ⦃V : C⦄ ⦃u : V ⟶ U⦄, R u → Sieve V := fun {_V} {_u} hu =>
      (h₁ _ (ksec hu)).choose
    have hT : ∀ ⦃V : C⦄ ⦃u : V ⟶ U⦄ (hu : R u), T hu ∈ J V := by
      intro V u hu
      exact (h₁ V (ksec hu)).choose_spec.1
    refine ⟨Sieve.bind R T, J.bind_covering hR hT, ?_⟩
    intro W h hh
    obtain ⟨V, k, u, hu, hk, rfl⟩ := hh
    dsimp only [T] at hk
    obtain ⟨m, hkill⟩ := (h₁ V (ksec hu)).choose_spec.2 W k hk
    have hkill' := congrArg (S.f.hom.app (op W)) hkill
    rw [_root_.map_nsmul, map_zero, NatTrans.naturality_apply S.f.hom k.op (ksec hu),
      hksec hu, _root_.map_nsmul, smul_smul, ← pow_add, ← S.X₂.obj.map_comp_apply,
      ← op_comp] at hkill'
    exact ⟨m + (hq V u hu).choose, by simpa using hkill'⟩

end Serre

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- **`l`-torsion sheaves.** An abelian sheaf on the small étale site of `S` is *`l`-torsion* if
every section is locally annihilated by a power of `l`: for every étale `U ⟶ S` and every
`s ∈ F(U)` there are an étale covering of `U` and, on each of its members, a power `l ^ v` killing
the restriction of `s`. -/
@[weil "def_fk112_l_torsion_sheaf"]
abbrev IsLTorsionSheaf (l : ℕ) : ObjectProperty (Sheaf (topology B S hS) AddCommGrpCat.{w}) :=
  lTorsionSheafProperty (topology B S hS) l

variable (B S hS) in
/-- The category of `l`-torsion abelian sheaves on the small étale site of `S`. -/
abbrev LTorsionSheaf (l : ℕ) := (IsLTorsionSheaf.{w} B S hS l).FullSubcategory

/-- For `0 < l`, an `l`-torsion sheaf is a torsion sheaf. -/
theorem IsLTorsionSheaf.isTorsionSheaf {l : ℕ} (hl : 0 < l)
    {F : Sheaf (topology B S hS) AddCommGrpCat.{w}} (hF : IsLTorsionSheaf B S hS l F) :
    IsTorsionSheaf B S hS F :=
  lTorsionSheafProperty_le_torsionSheafProperty hl F hF

/-- **A section of an `l`-torsion sheaf over a quasi-compact object is killed by a power of
`l`.** -/
theorem IsLTorsionSheaf.exists_pow_nsmul_eq_zero_of_compactSpace {l : ℕ}
    {F : Sheaf (topology B S hS) AddCommGrpCat.{w}} (hF : IsLTorsionSheaf B S hS l F)
    (U : SmallEtale B S hS) [CompactSpace ((toScheme B S hS).obj U)] (x : F.obj.obj (op U)) :
    ∃ v : ℕ, l ^ v • x = 0 :=
  exists_pow_nsmul_eq_zero_of_isQuasiCompactObject hF
    (isQuasiCompactObject_of_compactSpace B S hS U inferInstance) x

/-- **`l`-torsion sheaves in terms of `Et(S)`.** For a locally noetherian `S`, an abelian sheaf on
the small étale site of `S` is `l`-torsion if and only if every section over every noetherian
separated étale `S`-scheme is killed by a power of `l`. -/
@[weil "def_fk112_l_torsion_sheaf"]
theorem isLTorsionSheaf_iff_forall_exists_pow_nsmul_eq_zero [IsLocallyNoetherian S] (l : ℕ)
    (F : Sheaf (topology B S hS) AddCommGrpCat.{w}) :
    IsLTorsionSheaf B S hS l F ↔ ∀ (U : SmallNoetherianSeparatedEtale B S hS)
      (x : F.obj.obj (op ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U))),
      ∃ v : ℕ, l ^ v • x = 0 := by
  refine ⟨fun hF U x ↦ ?_, fun h X x ↦ ?_⟩
  · have : _root_.AlgebraicGeometry.IsNoetherian
        ((toScheme B S hS).obj ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U)) :=
      U.property.1
    exact hF.exists_pow_nsmul_eq_zero_of_compactSpace _ x
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj S hS)) := ‹IsLocallyNoetherian S›
  have : IsLocallyNoetherian ((toScheme B S hS).obj X) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map X.obj.hom)
  let E : PreZeroHypercover.{u + 1} X :=
    { I₀ := ULift.{u + 1} ((toScheme B S hS).obj X).affineOpens
      X := fun W ↦ openObject B S hS X W.down.1
      f := fun W ↦ openObjectι B S hS X W.down.1 }
  refine ⟨E.sieve₀, Precoverage.generate_mem_toGrothendieck
    (presieve₀_mem_precoverage_of_jointlySurjective B S hS E fun p ↦ ?_), ?_⟩
  · obtain ⟨W, hWa, hW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    refine ⟨ULift.up ⟨W, hWa⟩, ?_⟩
    change p ∈ Set.range ((toScheme B S hS).map (openObjectι B S hS X W)).base
    rw [openObjectι_range]
    exact hW
  · rintro V f ⟨Y, g, k, ⟨W⟩, rfl⟩
    let W' : ((toScheme B S hS).obj X).Opens := W.down.1
    have : _root_.AlgebraicGeometry.IsAffine W' := W.down.2
    have : _root_.AlgebraicGeometry.IsNoetherian W' := { toCompactSpace := inferInstance }
    let U : SmallNoetherianSeparatedEtale B S hS :=
      ⟨openObject B S hS X W', ‹IsNoetherian W'›, inferInstanceAs W'.toScheme.IsSeparated⟩
    obtain ⟨v, hv⟩ := h U (F.obj.map (openObjectι B S hS X W').op x)
    refine ⟨v, ?_⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← map_nsmul]
    change F.obj.map g.op (l ^ v • F.obj.map (openObjectι B S hS X W').op x) = 0
    rw [hv, map_zero]

end AlgebraicGeometry.SmallEtale

end
