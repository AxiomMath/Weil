module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionCohomologySingle
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian

/-!
# Torsion sheaves on the small étale site

An abelian sheaf `F` on the small étale site of a scheme `S` is a *torsion sheaf* when every
section is locally annihilated by a positive integer: for every étale `U ⟶ S` and every
`s ∈ F(U)` there is an étale covering of `U` on each member of which some positive multiple of
the restriction of `s` vanishes. This is the notion of [SGA 4, IX 1.1] and of
`Stacks.Torsion.torsionSheafProperty`.

Freitag and Kiehl call `F` a torsion sheaf when `F(U)` is a torsion group for every `U` in their
category `Et(S)` of noetherian separated étale `S`-schemes. On a quasi-compact object the local
annihilators of a section can be chosen finitely many, so their product kills the section; and
on a locally noetherian `S` the noetherian separated (indeed affine) étale `S`-schemes cover every
object. Hence the two notions agree for locally noetherian `S`, which contains every scheme
Freitag and Kiehl consider.

## Main definitions

* `AlgebraicGeometry.SmallEtale.IsTorsionSheaf`: the property of an abelian sheaf on the small
  étale site of `S` of being a torsion sheaf.

## Main results

* `Stacks.Torsion.exists_nsmul_eq_zero_of_isQuasiCompactObject`: on a site, a section of a
  torsion abelian sheaf over a quasi-compact object is killed by one positive integer.
* `AlgebraicGeometry.SmallEtale.IsTorsionSheaf.isAddTorsion_of_compactSpace`: the sections of a
  torsion sheaf over an object with quasi-compact underlying scheme form a torsion group.
* `AlgebraicGeometry.SmallEtale.isTorsionSheaf_iff_forall_isAddTorsion`: for a locally noetherian
  `S`, an abelian sheaf is a torsion sheaf if and only if its sections over every noetherian
  separated étale `S`-scheme form a torsion group.

## Implementation notes

The definition is the local one, `Stacks.Torsion.torsionSheafProperty`, on the small étale site
`AlgebraicGeometry.SmallEtale`; it is stable under quotients on every site, while the sectionwise
condition is not in general. The sectionwise characterization over the category `Et(S)` is
`AlgebraicGeometry.SmallEtale.isTorsionSheaf_iff_forall_isAddTorsion`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A section of an abelian sheaf which vanishes on the members of a covering sieve vanishes. -/
theorem sheaf_section_eq_zero_of_mem (F : Sheaf J AddCommGrpCat.{w}) {U : C}
    (x : F.obj.obj (op U)) {R : Sieve U} (hR : R ∈ J U)
    (hx : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → F.obj.map f.op x = 0) : x = 0 := by
  have hF := (isSheaf_iff_isSheaf_of_type J _).mp
    (GrothendieckTopology.HasSheafCompose.isSheaf F.obj F.2
      (F := forget AddCommGrpCat.{w}))
  refine (hF.isSeparated _ hR).ext fun V f hf ↦ ?_
  change F.obj.map f.op x = F.obj.map f.op 0
  exact (hx f hf).trans (map_zero _).symm

/-- **On a quasi-compact object a section of a torsion sheaf is killed by one positive
integer.** The covering sieve along whose members the section is locally killed is refined by a
covering family through finitely many of its members, and the product of the corresponding
integers kills the section on every member of that family. -/
theorem exists_nsmul_eq_zero_of_isQuasiCompactObject {F : Sheaf J AddCommGrpCat.{w}}
    (hF : torsionSheafProperty J F) {U : C} (hU : J.IsQuasiCompactObject U)
    (x : F.obj.obj (op U)) : ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  classical
  obtain ⟨R, hR, hx⟩ := hF U x
  let 𝒰 : PreZeroHypercover.{max u v} U :=
    { I₀ := Σ V : C, {f : V ⟶ U // R f}, X := fun i ↦ i.1, f := fun i ↦ i.2.1 }
  have hle : R ≤ 𝒰.sieve₀ := fun V f hf ↦ 𝒰.sieve₀_f ⟨V, f, hf⟩
  choose n hn hnx using fun i : 𝒰.I₀ ↦ hx i.1 i.2.1 i.2.2
  obtain ⟨𝒱, φ, h𝒱, hfin⟩ := hU 𝒰 (J.superset_covering hle hR)
  refine ⟨∏ i ∈ hfin.toFinset, n i, Finset.prod_pos fun i _ ↦ hn i, ?_⟩
  refine sheaf_section_eq_zero_of_mem F _ h𝒱 ?_
  rintro V f ⟨Y, h, g, ⟨j⟩, rfl⟩
  have hdvd : n (φ.s₀ j) ∣ ∏ i ∈ hfin.toFinset, n i :=
    Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr (Set.mem_range_self j))
  obtain ⟨e, he⟩ := hdvd
  rw [← φ.w₀ j, op_comp, op_comp, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, map_nsmul, he, mul_comm, mul_smul]
  change F.obj.map h.op (F.obj.map (φ.h₀ j).op (e • n (φ.s₀ j) • F.obj.map
    (φ.s₀ j).2.1.op x)) = 0
  rw [hnx, smul_zero, map_zero, map_zero]

end Stacks.Torsion

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- **Torsion sheaves.** An abelian sheaf on the small étale site of `S` is a *torsion sheaf* if
every section is locally annihilated by a positive integer. For a locally noetherian `S` this is
equivalent to the sections over every noetherian separated étale `S`-scheme forming a torsion
group (`AlgebraicGeometry.SmallEtale.isTorsionSheaf_iff_forall_isAddTorsion`). -/
@[weil "def_fk104_torsion_sheaf"]
abbrev IsTorsionSheaf : ObjectProperty (Sheaf (topology B S hS) AddCommGrpCat.{w}) :=
  Stacks.Torsion.torsionSheafProperty (topology B S hS)

/-- **The sections of a torsion sheaf over a quasi-compact object form a torsion group.** -/
theorem IsTorsionSheaf.isAddTorsion_of_compactSpace {F : Sheaf (topology B S hS) AddCommGrpCat.{w}}
    (hF : IsTorsionSheaf B S hS F) (U : SmallEtale B S hS)
    [CompactSpace ((toScheme B S hS).obj U)] : IsAddTorsion (F.obj.obj (op U)) := fun x ↦
  isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    (Stacks.Torsion.exists_nsmul_eq_zero_of_isQuasiCompactObject hF
      (isQuasiCompactObject_of_compactSpace B S hS U inferInstance) x)

/-- **Torsion sheaves in terms of `Et(S)`.** For a locally noetherian `S`, an abelian sheaf on the
small étale site of `S` is a torsion sheaf if and only if its group of sections over every
noetherian separated étale `S`-scheme is a torsion group. -/
@[weil "def_fk104_torsion_sheaf"]
theorem isTorsionSheaf_iff_forall_isAddTorsion [IsLocallyNoetherian S]
    (F : Sheaf (topology B S hS) AddCommGrpCat.{w}) :
    IsTorsionSheaf B S hS F ↔ ∀ U : SmallNoetherianSeparatedEtale B S hS,
      IsAddTorsion (F.obj.obj (op ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U))) := by
  refine ⟨fun hF U ↦ ?_, fun h X x ↦ ?_⟩
  · have : _root_.AlgebraicGeometry.IsNoetherian
        ((toScheme B S hS).obj ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U)) :=
      U.property.1
    exact hF.isAddTorsion_of_compactSpace _
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
    obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
      (h U (F.obj.map (openObjectι B S hS X W').op x))
    refine ⟨n, hn, ?_⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← map_nsmul]
    change F.obj.map g.op (n • F.obj.map (openObjectι B S hS X W').op x) = 0
    rw [hnx, map_zero]

end AlgebraicGeometry.SmallEtale

end

/-! ### The bounded below derived category with torsion cohomology -/

/-!
# The bounded below derived category with torsion cohomology

Let `J` be a Grothendieck topology on a category `C`. Inside the unbounded derived category
`D(C_J)` of abelian sheaves on `J`, the complexes all of whose cohomology sheaves are torsion
form the full subcategory `D_tor` (`Stacks.Torsion.torsionCohomologyProperty`). The full
subcategory `D_{+,tor}` of `D_tor` consists of the complexes `K` which are moreover
cohomologically bounded below: there is `n₀ : ℤ` with `H^n(K) = 0` for all `n < n₀`. Equivalently,
`D_{+,tor}` is the intersection of `D_tor` with the bounded below derived category
`DerivedCategory.Plus`, the objects which are `≥ n` for some `n` in the canonical t-structure.

For a scheme `X`, the category `D_{+,tor}(X)` is this construction for the small étale site of
`X`.

## Main definitions

* `Stacks.Torsion.torsionPlusCohomologyProperty J`: the property of an object of `D(C_J)` of
  having torsion cohomology sheaves and being cohomologically bounded below.
* `Stacks.Torsion.TorsionPlusDerivedCategory J`: the corresponding full subcategory.
* `AlgebraicGeometry.SmallEtale.TorsionPlusDerivedCategory B S hS`: the category
  `D_{+,tor}(S)` for the small étale site of a scheme `S`.

## Main results

* `Stacks.Torsion.torsionPlusCohomologyProperty_iff`: `K` lies in `D_{+,tor}` if and only if all
  its cohomology sheaves are torsion and they vanish in all degrees below some `n₀`.
* `Stacks.Torsion.torsionPlusCohomologyProperty_singleFunctor`: a torsion sheaf placed in degree
  zero lies in `D_{+,tor}`.
* `Stacks.Torsion.TorsionPlusDerivedCategory.ιTorsion`,
  `Stacks.Torsion.TorsionPlusDerivedCategory.ιPlus`: the inclusions of `D_{+,tor}` into `D_tor`
  and into `D_+`.

## Implementation notes

The derived category is the one given by `HasDerivedCategory.standard`, as for
`Stacks.Torsion.torsionCohomologyProperty`, so that both properties live on the same category.
Bounded below is the condition `DerivedCategory.TStructure.t.plus`, which by
`DerivedCategory.isGE_iff` is the vanishing of the cohomology sheaves in low degrees; using the
t-structure gives the closure properties of `DerivedCategory.Plus` directly.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8, p. 86][FreitagKiehl]
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe w v u

namespace Stacks.Torsion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

attribute [local instance] CategoryTheory.sheafIsAbelian HasDerivedCategory.standard

/-- The property of an object of the derived category of abelian sheaves on `J` of having
torsion cohomology sheaves and being cohomologically bounded below. -/
@[weil "def_fk108_derived_category_torsion_bounded_below"]
def torsionPlusCohomologyProperty :
    ObjectProperty (DerivedCategory (Sheaf J AddCommGrpCat.{w})) :=
  torsionCohomologyProperty J ⊓ DerivedCategory.TStructure.t.plus

/-- The full subcategory `D_{+,tor}` of the derived category of abelian sheaves on `J`: the
complexes with torsion cohomology sheaves which are cohomologically bounded below. -/
@[weil "def_fk108_derived_category_torsion_bounded_below"]
abbrev TorsionPlusDerivedCategory := (torsionPlusCohomologyProperty J).FullSubcategory

variable {J}

/-- An object lies in `D_{+,tor}` if and only if all its cohomology sheaves are torsion and they
vanish in all degrees below some `n₀`. -/
@[weil "def_fk108_derived_category_torsion_bounded_below"]
theorem torsionPlusCohomologyProperty_iff (K : DerivedCategory (Sheaf J AddCommGrpCat.{w})) :
    torsionPlusCohomologyProperty J K ↔
      (∀ i : ℤ, torsionSheafProperty J
        ((DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{w}) i).obj K)) ∧
      ∃ n₀ : ℤ, ∀ n < n₀,
        IsZero ((DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{w}) n).obj K) := by
  refine and_congr Iff.rfl (exists_congr fun n₀ ↦ ?_)
  exact DerivedCategory.isGE_iff K n₀

theorem torsionPlusCohomologyProperty.torsionCohomologyProperty
    {K : DerivedCategory (Sheaf J AddCommGrpCat.{w})} (hK : torsionPlusCohomologyProperty J K) :
    Stacks.Torsion.torsionCohomologyProperty J K :=
  hK.1

theorem torsionPlusCohomologyProperty.plus
    {K : DerivedCategory (Sheaf J AddCommGrpCat.{w})} (hK : torsionPlusCohomologyProperty J K) :
    DerivedCategory.TStructure.t.plus K :=
  hK.2

theorem torsionPlusCohomologyProperty_le_torsionCohomologyProperty :
    torsionPlusCohomologyProperty J ≤ torsionCohomologyProperty J :=
  fun _ hK ↦ hK.1

theorem torsionPlusCohomologyProperty_le_plus :
    torsionPlusCohomologyProperty J ≤ DerivedCategory.TStructure.t.plus :=
  fun _ hK ↦ hK.2

instance : (torsionPlusCohomologyProperty J).IsClosedUnderIsomorphisms where
  of_iso {K L} e hK := by
    refine ⟨fun i ↦ (torsionSheafProperty J).prop_of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e) (hK.1 i), ?_⟩
    obtain ⟨n, hn⟩ := hK.2
    exact ⟨n, DerivedCategory.TStructure.t.isGE_of_iso e n⟩

/-- A torsion sheaf placed in degree zero lies in `D_{+,tor}`. -/
theorem torsionPlusCohomologyProperty_singleFunctor (F : Sheaf J AddCommGrpCat.{w})
    (hF : torsionSheafProperty J F) :
    torsionPlusCohomologyProperty J ((DerivedCategory.singleFunctor _ 0).obj F) :=
  ⟨torsionCohomologyProperty_singleFunctor J F hF, 0, inferInstance⟩

variable (J)

/-- The inclusion of `D_{+,tor}` into `D_tor`. -/
abbrev TorsionPlusDerivedCategory.ιTorsion :
    TorsionPlusDerivedCategory J ⥤ TorsionDerivedCategory J :=
  ObjectProperty.ιOfLE torsionPlusCohomologyProperty_le_torsionCohomologyProperty

/-- The inclusion of `D_{+,tor}` into the bounded below derived category `D_+`. -/
abbrev TorsionPlusDerivedCategory.ιPlus :
    TorsionPlusDerivedCategory J ⥤ DerivedCategory.Plus (Sheaf J AddCommGrpCat.{w}) :=
  ObjectProperty.ιOfLE torsionPlusCohomologyProperty_le_plus

end Stacks.Torsion

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The category `D_{+,tor}(S)`.** For a scheme `S`, the full subcategory of the derived
category of abelian sheaves on the small étale site of `S` of the complexes all of whose
cohomology sheaves are torsion sheaves and which are cohomologically bounded below. -/
@[weil "def_fk108_derived_category_torsion_bounded_below"]
abbrev TorsionPlusDerivedCategory :=
  Stacks.Torsion.TorsionPlusDerivedCategory.{u} (topology B S hS)

end AlgebraicGeometry.SmallEtale

end
