module

public import Weil.Attr
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Cech.ToSheafCohomology
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Cech.CechCohomologyOfAnObject
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroOfASheaf
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapFunctoriality
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison

/-!
# Existence and uniqueness of the canonical Čech-to-derived map

Let `S` be a noetherian separated scheme, `F` an abelian sheaf on the small étale site of `S`
and `F → I^•` an injective resolution. For every `i ≥ 0` there is exactly one canonical
Čech-to-derived map `c : Ȟ^i(S, F) → H^i(S, F)`, i.e. one homomorphism with
`c([z]_𝔘) = [y]` whenever `z ∈ Z^i(𝔘, F)`, `y` is a cocycle of `Γ(S, I^•)` and
`β_𝔘(y) - α_𝔘(z) ∈ D(T^{i-1}_𝔘)` in the total complex `T_𝔘` of `K^{p,q} = Č^p(𝔘, I^q)`.

The proof is the source's. The columns `Č^•(𝔘, I^q)` of the double complex resolve `Γ(S, I^q)`:
in degree `0` by the sheaf condition for the covering `𝔘`, in positive degrees because injective
sheaves are Čech-acyclic. Hence `β_𝔘 : Γ(S, I^•) → T_𝔘` is a quasi-isomorphism, and since
`α_𝔘 : Č^•(𝔘, F) → T_𝔘` is a map of complexes, every Čech cocycle `z` has a matching cocycle
`y`, whose class is unique. The resulting maps `γ_𝔘 : Z^i(𝔘, F) → H^i(S, F)` are additive, kill
coboundaries and are compatible with refinements (a refinement `φ : 𝔚 → 𝔘` induces a map of
double complexes commuting with `α` and `β`), so they descend to `Ȟ^i(S, F)`. Uniqueness holds
because the classes `[z]_𝔘` generate `Ȟ^i(S, F)`.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementTotalMap`: the map
  `φ^* : T_𝔘 → T_𝔚` of total complexes induced by a refinement `φ : 𝔚 → 𝔘`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.CechMatch`: the relation
  `β_𝔘(y) - α_𝔘(z) ∈ D(T^{i-1}_𝔘)` between a Čech cocycle `z` and a cocycle `y` of `Γ(S, I^•)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCyclesToH`: the map
  `γ_𝔘 : Z^i(𝔘, F) → H^i(S, F)`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.exists_quasiIso_globalSectionsComplexInt`:
  `β_𝔘` is a quasi-isomorphism.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechToTotalComplex_comp_d`: `α_𝔘` is a map
  of complexes.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.existsUnique_isCanonicalCechToDerivedMap`:
  there is exactly one canonical Čech-to-derived map `Ȟ^i(S, F) → H^i(S, F)`.

## Implementation notes

That `β_𝔘` is a quasi-isomorphism is Stacks 0133 (`quasiIso_total_of_resolution_flip`), applied
to the double complex with the resolution degree first; the source proves it by the descending
modification of cocycles, which is the same argument. The degree-zero sheaf condition and the
Čech-acyclicity of injective sheaves are used for the restrictions to `Et(S)` of sheaves on the
small étale site, through the equivalence of the two sheaf categories; the corresponding
statements on a general site require coefficients in the universe of the objects of the site,
which the sheaves of `u`-small abelian groups here are not.

The elementwise consequences of a quasi-isomorphism of complexes of abelian groups
(`HomologicalComplex.exists_d_eq_zero_and_sub_mem_range_of_isIso_homologyMap`,
`HomologicalComplex.mem_range_of_isIso_homologyMap`) are proved first, in general.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace HomologicalComplex
variable {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex AddCommGrpCat.{u} c}

/-- An element killed by the differential is a cycle. -/
lemma exists_iCycles_eq_of_d_eq_zero {j k : ι} (hk : c.next j = k) (x : K.X j)
    (hx : K.d j k x = 0) : ∃ z : K.cycles j, K.iCycles j z = x := by
  subst hk
  exact ⟨(K.sc j).abCyclesIso.inv ⟨x, hx⟩, (K.sc j).abCyclesIso_inv_apply_iCycles ⟨x, hx⟩⟩

/-- A cycle with zero class is a boundary. -/
lemma exists_d_eq_iCycles_of_homologyπ_eq_zero {i j : ι} (hi : c.prev j = i) (z : K.cycles j)
    (hz : K.homologyπ j z = 0) : ∃ x : K.X i, K.d i j x = K.iCycles j z := by
  have hS := (ShortComplex.mk (K.toCycles i j) (K.homologyπ j)
    (K.toCycles_comp_homologyπ i j)).exact_of_g_is_cokernel (K.homologyIsCokernel i j hi)
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).1 hS z hz
  refine ⟨x, ?_⟩
  rw [← hx, ← ConcreteCategory.comp_apply, K.toCycles_i]

/-- The inclusion of the cycles is injective. -/
lemma iCycles_injective (j : ι) : Function.Injective (K.iCycles j) :=
  (AddCommGrpCat.mono_iff_injective _).1 inferInstance

/-- Every cohomology class is the class of a cycle. -/
lemma homologyπ_surjective (j : ι) : Function.Surjective (K.homologyπ j) :=
  (AddCommGrpCat.epi_iff_surjective _).1 inferInstance

/-- **Surjectivity of a quasi-isomorphism on cohomology, elementwise.** -/
lemma exists_d_eq_zero_and_sub_mem_range_of_isIso_homologyMap (f : K ⟶ L) {i j k : ι}
    (hi : c.prev j = i) (hk : c.next j = k) [IsIso (homologyMap f j)] (t : L.X j)
    (ht : L.d j k t = 0) :
    ∃ y : K.X j, K.d j k y = 0 ∧ f.f j y - t ∈ (L.d i j).hom.range := by
  obtain ⟨zt, rfl⟩ := exists_iCycles_eq_of_d_eq_zero hk t ht
  obtain ⟨h, hh⟩ := ((AddCommGrpCat.epi_iff_surjective _).1 inferInstance :
    Function.Surjective (homologyMap f j)) (L.homologyπ j zt)
  obtain ⟨zy, rfl⟩ := homologyπ_surjective j h
  have h1 : L.homologyπ j (cyclesMap f j zy - zt) = 0 := by
    rw [map_sub, ← hh, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      homologyπ_naturality, sub_self]
  obtain ⟨x, hx⟩ := exists_d_eq_iCycles_of_homologyπ_eq_zero hi _ h1
  refine ⟨K.iCycles j zy, ?_, x, ?_⟩
  · subst hk
    rw [← ConcreteCategory.comp_apply, iCycles_d, AddCommGrpCat.zero_apply]
  · rw [hx, map_sub, ← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply]

/-- **Injectivity of a quasi-isomorphism on cohomology, elementwise.** -/
lemma mem_range_of_isIso_homologyMap (f : K ⟶ L) {i j k : ι}
    (hi : c.prev j = i) (hk : c.next j = k) [IsIso (homologyMap f j)] (y : K.X j)
    (hy : K.d j k y = 0) (hfy : f.f j y ∈ (L.d i j).hom.range) :
    y ∈ (K.d i j).hom.range := by
  obtain ⟨zy, rfl⟩ := exists_iCycles_eq_of_d_eq_zero hk y hy
  obtain ⟨w, hw⟩ := hfy
  have h1 : cyclesMap f j zy = L.toCycles i j w := by
    apply iCycles_injective j
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply (L.toCycles i j), toCycles_i]
    exact hw.symm
  have h2 : homologyMap f j (K.homologyπ j zy) = 0 := by
    rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply, h1,
      ← ConcreteCategory.comp_apply, toCycles_comp_homologyπ, AddCommGrpCat.zero_apply]
  have h3 : K.homologyπ j zy = 0 :=
    ((AddCommGrpCat.mono_iff_injective _).1 inferInstance :
      Function.Injective (homologyMap f j)) (h2.trans (map_zero _).symm)
  obtain ⟨x, hx⟩ := exists_d_eq_iCycles_of_homologyπ_eq_zero hi _ h3
  exact ⟨x, hx⟩

end HomologicalComplex

namespace HomologicalComplex₂

/-- A map into `K^{p,0}` killed by the second differential composes with `D` through the first
differential only. -/
lemma comp_ιTotal_d_of_comp_d₂_eq_zero {C : Type*} [Category C] [Preadditive C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] {X : C} (p p' : ℤ) (hp : p + 1 = p')
    (a : X ⟶ (K.X p).X 0) (ha : a ≫ (K.X p).d 0 1 = 0) :
    a ≫ K.ιTotal (ComplexShape.up ℤ) p 0 p (by simp) ≫ (K.total (ComplexShape.up ℤ)).d p p' =
      a ≫ (K.d p p').f 0 ≫ K.ιTotal (ComplexShape.up ℤ) p' 0 p' (by simp) := by
  subst hp
  rw [HomologicalComplex₂.ιTotal_d_up_ℤ K p 0 p (by simp), Preadditive.comp_add]
  simp [reassoc_of% ha]

end HomologicalComplex₂

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale
variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The family underlying the augmentation of a section is the family of its restrictions. -/
lemma cochainToFamily_cechAugmentation {U : SmallNoetherianSeparatedEtale B S hS}
    (E : PreZeroHypercover.{0} U) (G : EtalePresheaf B S hS AddCommGrpCat.{u})
    (s : G.obj (op U)) :
    Stacks.CechSite.cochainToFamily E G (cechAugmentation E G s) =
      (Stacks.CechSite.cechRestriction E G s).1 := by
  funext i
  have := Stacks.CechSite.singletonProjection_isIso E i
  have key : cechAugmentation E G ≫ Pi.π (Stacks.CechSite.cochainFactor E G 0) (fun _ ↦ i) ≫
      G.map (inv (Stacks.CechSite.singletonProjection E i)).left.op = G.map (E.f i).op := by
    erw [cechAugmentation_π_assoc]
    rw [← G.map_comp, ← op_comp, Over.w]
    rfl
  exact ConcreteCategory.congr_hom key s

variable [IsNoetherian S]


/-- The sieve generated by a covering of `Et(S)` is a covering sieve. -/
lemma sieve₀_mem_topology {U : SmallNoetherianSeparatedEtale B S hS} (𝔘 : CechCovering U) :
    𝔘.toPreZeroHypercover.sieve₀ ∈ topology B S hS U := by
  rw [mem_topology_iff]
  intro x
  have hx : x ∈ ⋃ ν, Set.range ((toScheme B S hS).map (𝔘.f ν)) := by
    rw [𝔘.iUnion_range]; trivial
  obtain ⟨ν, hν⟩ := Set.mem_iUnion.1 hx
  exact ⟨_, 𝔘.f ν, Sieve.ofArrows_mk _ _ ν, hν⟩

/-- **The sheaf condition in Čech form**: for an abelian sheaf `G` on the small étale site and
a covering `𝔘` of an object `U` of `Et(S)`, the augmentation `G(U) → Č^0(𝔘, G)` is injective
with image the kernel of `d^0`. -/
lemma cechAugmentation_injective {U : SmallNoetherianSeparatedEtale B S hS} (𝔘 : CechCovering U)
    (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u}) :
    Function.Injective (cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf G)) := by
  have hG : Presheaf.IsSheaf (topology B S hS) (restrictSheaf G) :=
    ((sheafEquiv B S hS AddCommGrpCat.{u}).inverse.obj G).property
  have hbij := Stacks.CechSite.cechRestriction_bijective_of_isSheaf (topology B S hS)
    _ hG _ (sieve₀_mem_topology 𝔘)
  intro s s' h
  apply hbij.1
  apply Subtype.ext
  rw [← cochainToFamily_cechAugmentation, ← cochainToFamily_cechAugmentation]
  exact congrArg _ h

/-- A Čech `0`-cocycle of the restriction of a sheaf is the augmentation of a section. -/
lemma exists_cechAugmentation_eq {U : SmallNoetherianSeparatedEtale B S hS} (𝔘 : CechCovering U)
    (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})
    (x : (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf G)).X 0)
    (hx : (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf G)).d 0 1 x = 0) :
    ∃ s, cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf G) s = x := by
  have hG : Presheaf.IsSheaf (topology B S hS) (restrictSheaf G) :=
    ((sheafEquiv B S hS AddCommGrpCat.{u}).inverse.obj G).property
  have hbij := Stacks.CechSite.cechRestriction_bijective_of_isSheaf (topology B S hS)
    _ hG _ (sieve₀_mem_topology 𝔘)
  have hmatch := (Stacks.CechSite.differential_eq_zero_iff 𝔘.toPreZeroHypercover
    (restrictSheaf G)
      (Stacks.CechSite.cochainToFamily 𝔘.toPreZeroHypercover (restrictSheaf G) x)).1 (by
      convert hx using 2; exact Stacks.CechSite.familyToCochain_cochainToFamily _ _ x)
  obtain ⟨s, hs⟩ := hbij.2 ⟨_, hmatch⟩
  refine ⟨s, ?_⟩
  rw [← Stacks.CechSite.familyToCochain_cochainToFamily _ _ x,
    ← Stacks.CechSite.familyToCochain_cochainToFamily _ _ (cechAugmentation _ _ s),
    cochainToFamily_cechAugmentation, hs]

omit [IsNoetherian S] in
/-- The augmentation `G(U) → Č^0(𝔘, G)` is natural in the presheaf. -/
@[reassoc]
lemma cechAugmentation_naturality {U : SmallNoetherianSeparatedEtale B S hS}
    (E : PreZeroHypercover.{0} U) {G G' : EtalePresheaf B S hS AddCommGrpCat.{u}} (φ : G ⟶ G') :
    cechAugmentation E G ≫ ((Stacks.CechSite.cechComplexFunctor E).map φ).f 0 =
      φ.app (op U) ≫ cechAugmentation E G' := by
  refine Pi.hom_ext (f := Stacks.CechSite.cochainFactor E G' 0) _ _ fun ν ↦ ?_
  have h1 := Stacks.CechSite.cechComplexFunctor_map_f_π E φ 0 ν
  have h2 := cechAugmentation_π E G ν
  have h3 := cechAugmentation_π E G' ν
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  erw [h1, reassoc_of% h2, h3]
  exact φ.naturality _

/-- An equivalence carries injective objects to injective objects; here: the restriction to
`Et(S)` of an injective abelian sheaf on the small étale site is injective. -/
instance injective_sheafEquiv_inverse_obj (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})
    [Injective G] : Injective ((sheafEquiv B S hS AddCommGrpCat.{u}).inverse.obj G) :=
  Injective.injective_of_adjoint (sheafEquiv B S hS AddCommGrpCat.{u}).toAdjunction G

/-- The Čech complex, along any family of `Et(S)`, of the restriction of an injective abelian
sheaf on the small étale site is exact in positive degrees. -/
lemma isZero_cechCohomology_restrictSheaf {U : SmallNoetherianSeparatedEtale B S hS}
    (E : PreZeroHypercover.{0} U) (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})
    [Injective G] (p : ℕ) (hp : 1 ≤ p) :
    IsZero (cechCohomology (A := AddCommGrpCat.{u}) E (restrictSheaf G) p) :=
  isZero_cechCohomology_of_injective E ((sheafEquiv B S hS AddCommGrpCat.{u}).inverse.obj G) p hp

omit [IsNoetherian S] in
/-- The integer-graded Čech complex vanishes in negative degrees. -/
lemma isZero_cechCochainFunctor_obj_X {U : SmallNoetherianSeparatedEtale B S hS}
    (E : PreZeroHypercover.{0} U) (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})
    (q : ℤ) (hq : q < 0) : IsZero (((cechCochainFunctor E).obj G).X q) :=
  HomologicalComplex.isZero_extend_X _ _ q (fun i hi ↦ by
    change (i : ℤ) = q at hi
    omega)

lemma exactAt_cechCochainFunctor_obj {U : SmallNoetherianSeparatedEtale B S hS}
    (E : PreZeroHypercover.{0} U) (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})
    [Injective G] (q : ℤ) (hq : q ≠ 0) : ((cechCochainFunctor E).obj G).ExactAt q := by
  rcases lt_or_gt_of_ne hq with h | h
  · exact HomologicalComplex.ExactAt.of_isZero (isZero_cechCochainFunctor_obj_X E G q h)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = q := ⟨q.toNat, by omega⟩
    refine (HomologicalComplex.extend_exactAt_iff _ ComplexShape.embeddingUpNat (j := m)
      rfl).2 ?_
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact isZero_cechCohomology_restrictSheaf E G m (by omega)

omit [IsNoetherian S] in
/-- The augmentation is killed by the degree-zero Čech differential. -/
lemma cechAugmentation_comp_d {U : SmallNoetherianSeparatedEtale B S hS} (𝔘 : CechCovering U)
    (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u}) :
    cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf G) ≫
      (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf G)).d 0 1 = 0 := by
  ext s
  have hm := (Stacks.CechSite.cechRestriction 𝔘.toPreZeroHypercover (restrictSheaf G) s).2
  change PreZeroHypercover.IsMatching _ _ _ at hm
  rw [← Stacks.CechSite.differential_eq_zero_iff, ← cochainToFamily_cechAugmentation,
    Stacks.CechSite.familyToCochain_cochainToFamily] at hm
  exact hm

/-- **The sheaf condition in Čech form, in the integer grading.** The augmentation
`G(U) → Č^0(𝔘, G)` is a kernel of the degree-zero differential of the integer-graded Čech
complex. -/
lemma exists_isIso_kernelLift_cechAugmentation {U : SmallNoetherianSeparatedEtale B S hS}
    (𝔘 : CechCovering U) (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u}) :
    ∃ (h : (cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf G) ≫
        ((cechComplex 𝔘.toPreZeroHypercover (restrictSheaf G)).extendXIso
          ComplexShape.embeddingUpNat (i' := (0 : ℤ)) (i := 0) rfl).inv) ≫
        ((cechComplex 𝔘.toPreZeroHypercover (restrictSheaf G)).extend
          ComplexShape.embeddingUpNat).d 0 1 = 0),
      IsIso (kernel.lift _ _ h) := by
  set K := cechComplex 𝔘.toPreZeroHypercover (restrictSheaf G)
  have hd : (K.extend ComplexShape.embeddingUpNat).d 0 1 =
      (K.extendXIso ComplexShape.embeddingUpNat (i' := (0 : ℤ)) (i := 0) rfl).hom ≫ K.d 0 1 ≫
        (K.extendXIso ComplexShape.embeddingUpNat (i' := (1 : ℤ)) (i := 1) rfl).inv :=
    K.extend_d_eq ComplexShape.embeddingUpNat (i' := 0) (j' := 1) (i := 0) (j := 1) rfl rfl
  have h : (cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf G) ≫
      (K.extendXIso ComplexShape.embeddingUpNat (i' := (0 : ℤ)) (i := 0) rfl).inv) ≫
        (K.extend ComplexShape.embeddingUpNat).d 0 1 = 0 := by
    rw [hd, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% (cechAugmentation_comp_d 𝔘 G),
      zero_comp]
  refine ⟨h, Stacks.CechSite.isIso_kernelLift_of_isLimit _ _ h ?_⟩
  refine ((ShortComplex.exact_and_mono_f_iff_f_is_kernel (ShortComplex.mk _ _ h)).1
    ⟨?_, ?_⟩).some
  · rw [ShortComplex.ab_exact_iff]
    intro x hx
    obtain ⟨s, hs⟩ := exists_cechAugmentation_eq 𝔘 G
      ((K.extendXIso ComplexShape.embeddingUpNat (i' := (0 : ℤ)) (i := 0) rfl).hom x) (by
        change (K.extend ComplexShape.embeddingUpNat).d 0 1 x = 0 at hx
        rw [hd] at hx
        have hx' := congrArg
          (K.extendXIso ComplexShape.embeddingUpNat (i' := (1 : ℤ)) (i := 1) rfl).hom hx
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply,
          map_zero] at hx'
        exact hx')
    refine ⟨s, ?_⟩
    change (K.extendXIso ComplexShape.embeddingUpNat (i' := (0 : ℤ)) (i := 0) rfl).inv
      (cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf G) s) = x
    rw [hs]
    exact Iso.hom_inv_id_apply _ x
  · rw [AddCommGrpCat.mono_iff_injective]
    intro s s' hss
    apply cechAugmentation_injective 𝔘 G
    have := congrArg (K.extendXIso ComplexShape.embeddingUpNat (i' := (0 : ℤ)) (i := 0) rfl).hom hss
    simpa using this

omit [IsNoetherian S] in
/-- The augmentation into the integer-graded Čech complex is natural in the presheaf. -/
lemma cechAugmentation_comp_extendMap {U : SmallNoetherianSeparatedEtale B S hS}
    (E : PreZeroHypercover.{0} U) {P P' : EtalePresheaf B S hS AddCommGrpCat.{u}} (ψ : P ⟶ P') :
    (cechAugmentation E P ≫ ((cechComplex E P).extendXIso
        ComplexShape.embeddingUpNat (i' := (0 : ℤ)) (i := 0) rfl).inv) ≫
      (HomologicalComplex.extendMap ((Stacks.CechSite.cechComplexFunctor E).map ψ)
        ComplexShape.embeddingUpNat).f 0 =
      ψ.app (op U) ≫ cechAugmentation E P' ≫ ((cechComplex E P').extendXIso
          ComplexShape.embeddingUpNat (i' := (0 : ℤ)) (i := 0) rfl).inv := by
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, cechAugmentation_naturality, Category.assoc]

omit [IsNoetherian S] in
/-- **`φ^*` is natural in the presheaf.** -/
@[reassoc]
lemma refinementCochainMap_naturality {U : SmallNoetherianSeparatedEtale B S hS}
    {E G : PreZeroHypercover.{0} U} (φ : E.Hom G) {P P' : EtalePresheaf B S hS AddCommGrpCat.{u}}
    (ψ : P ⟶ P') :
    (Stacks.CechSite.cechComplexFunctor G).map ψ ≫ refinementCochainMap φ P' =
      refinementCochainMap φ P ≫ (Stacks.CechSite.cechComplexFunctor E).map ψ := by
  ext n : 1
  refine Pi.hom_ext (f := Stacks.CechSite.cochainFactor E P' n) _ _ fun ν ↦ ?_
  have h1 := refinementCochainMap_f_π φ P' n ν
  have h2 := refinementCochainMap_f_π φ P n ν
  have h3 := Stacks.CechSite.cechComplexFunctor_map_f_π E ψ n ν
  have h4 := Stacks.CechSite.cechComplexFunctor_map_f_π G ψ n (φ.s₀ ∘ ν)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  erw [h1, reassoc_of% h4, h3, reassoc_of% h2]
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  exact congrArg _ (ψ.naturality _).symm

omit [IsNoetherian S] in
/-- The map of iterated fibre products induced by a refinement lies over `U`. -/
@[reassoc]
lemma refinementProductMap_hom {U : SmallNoetherianSeparatedEtale B S hS}
    {E G : PreZeroHypercover.{0} U} (φ : E.Hom G) (p : ℕ) (ν : Fin (p + 1) → E.I₀) :
    refinementProductMap φ p ν ≫ (∏ᶜ fun a ↦ Over.mk (G.f (φ.s₀ (ν a)))).hom =
      (∏ᶜ fun a ↦ Over.mk (E.f (ν a))).hom := by
  rw [← Over.w (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (ν a)))) 0), refinementProductMap_π_assoc]
  erw [φ.w₀ (ν 0)]
  exact Over.w (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 0)

omit [IsNoetherian S] in
/-- **`φ^*` is compatible with the augmentations**: restricting to `𝔙` and then refining is
restricting to `𝔘`. -/
@[reassoc]
lemma cechAugmentation_comp_refinementCochainMap {U : SmallNoetherianSeparatedEtale B S hS}
    {E G : PreZeroHypercover.{0} U} (φ : E.Hom G) (P : EtalePresheaf B S hS AddCommGrpCat.{u}) :
    cechAugmentation G P ≫ (refinementCochainMap φ P).f 0 = cechAugmentation E P := by
  refine Pi.hom_ext (f := Stacks.CechSite.cochainFactor E P 0) _ _ fun ν ↦ ?_
  have h1 := refinementCochainMap_f_π φ P 0 ν
  have h2 := cechAugmentation_π G P (φ.s₀ ∘ ν)
  have h3 := cechAugmentation_π E P ν
  refine (Category.assoc _ _ _).trans ?_
  erw [h1, reassoc_of% h2, h3]
  rw [← P.map_comp, ← op_comp]
  exact congrArg (fun f ↦ P.map f.op) (refinementProductMap_hom φ 0 ν)

section Resolution

variable [S.IsSeparated] {F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u}}
  (I : InjectiveResolution F)

omit [IsNoetherian S] [S.IsSeparated] in
/-- An injective resolution, as an integer-graded complex, vanishes in negative degrees. -/
lemma isZero_cochainComplex_X (q : ℤ) (hq : q < 0) : IsZero (I.cochainComplex.X q) :=
  HomologicalComplex.isZero_extend_X _ _ q (fun i hi ↦ by
    change (i : ℤ) = q at hi
    omega)

omit [IsNoetherian S] [S.IsSeparated] in
/-- The terms of an injective resolution, as an integer-graded complex, are injective. -/
lemma injective_cochainComplex_X (q : ℤ) : Injective (I.cochainComplex.X q) := by
  rcases lt_or_ge q 0 with h | h
  · exact IsZero.injective (isZero_cochainComplex_X I q h)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = q := ⟨q.toNat, by omega⟩
    exact Injective.of_iso (I.cochainComplexXIso _ n rfl).symm (I.injective n)

/-- The complex `Γ(S, I^•)`, indexed by the integers. -/
abbrev globalSectionsComplexInt : CochainComplex AddCommGrpCat.{u} ℤ :=
  (((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B S hS))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    I.cochainComplex

/-- The augmentation `Γ(S, I^q) → Č^0(𝔘, I^q)`, as a map of complexes into the row `p = 0` of
the double complex `K^{p,q}`. -/
def cechAugmentationRowZero (𝔘 : CechCovering (final B S hS)) :
    globalSectionsComplexInt I ⟶ rowZero (cechResolutionBicomplex I 𝔘).flip where
  f q := cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf (I.cochainComplex.X q)) ≫
    (((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).obj
      (restrictSheaf (I.cochainComplex.X q))).extendXIso ComplexShape.embeddingUpNat rfl).inv
  comm' q q' _ := by
    exact cechAugmentation_comp_extendMap 𝔘.toPreZeroHypercover
      (Functor.whiskerLeft (inclusion B S hS).op
        ((sheafToPresheaf _ _).map (I.cochainComplex.d q q')))

/-- **The hypotheses of Stacks 0133** for the double complex `K^{p,q} = Č^p(𝔘, I^q)` and the
augmentation `Γ(S, I^•) → Č^0(𝔘, I^•)`: its columns `Č^•(𝔘, I^q)` resolve `Γ(S, I^q)`. -/
lemma hypotheses_cechResolutionBicomplex (𝔘 : CechCovering (final B S hS)) :
    Hypotheses (globalSectionsComplexInt I) (cechResolutionBicomplex I 𝔘).flip
      (cechAugmentationRowZero I 𝔘) := by
  refine ⟨?_, fun p q hq ↦ isZero_cechCochainFunctor_obj_X _ _ q hq, fun p q hq ↦ ?_,
    fun p ↦ exists_isIso_kernelLift_cechAugmentation 𝔘 _⟩
  · intro n
    refine (Set.finite_Icc 0 n).subset fun p hp ↦ ?_
    simp only [Set.mem_ofPred_eq] at hp
    by_contra h
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact hp (Functor.map_isZero (HomologicalComplex.eval _ _ (n - p))
        ((cechCochainFunctor 𝔘.toPreZeroHypercover).map_isZero
          (isZero_cochainComplex_X I p h)))
    · exact hp (isZero_cechCochainFunctor_obj_X _ _ (n - p) (by omega))
  · have := injective_cochainComplex_X I p
    exact exactAt_cechCochainFunctor_obj _ _ q hq

/-- **`β_𝔘` is a quasi-isomorphism** (Stacks 0133): there is a quasi-isomorphism
`Γ(S, I^•) → T_𝔘` whose components are the maps `β_𝔘`. -/
lemma exists_quasiIso_globalSectionsComplexInt (𝔘 : CechCovering (final B S hS)) :
    ∃ f : globalSectionsComplexInt I ⟶ cechResolutionTotal I 𝔘, QuasiIso f ∧
      ∀ n : ℕ, globalSectionsToTotalComplex I 𝔘 n =
        ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
          (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n n rfl).inv ≫ f.f n := by
  obtain ⟨_, f, hf, hq⟩ := quasiIso_total_of_resolution_flip _ _ _
    (hypotheses_cechResolutionBicomplex I 𝔘)
  refine ⟨f, hq, fun n ↦ ?_⟩
  rw [hf]
  rfl

omit [IsNoetherian S] [S.IsSeparated] in
/-- The differential of the integer-graded `Γ(S, I^•)` in terms of the natural-number-graded one. -/
lemma globalSectionsComplexInt_d_apply (a b : ℤ) (k₁ k₂ : ℕ) (h₁ : (k₁ : ℤ) = a)
    (h₂ : (k₂ : ℤ) = b) (x : (globalSectionsComplexInt I).X a) :
    (globalSectionsComplexInt I).d a b x =
      ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
          (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso b k₂ h₂).inv
        ((globalSectionsComplex I).d k₁ k₂
          (((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
            (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso a k₁ h₁).hom x)) := by
  change ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
    (op (SmallEtale.final B S hS))).map (I.cochainComplex.d a b) x = _
  rw [I.cochainComplex_d a b k₁ k₂ h₁ h₂, Functor.map_comp, Functor.map_comp]
  rfl

omit [IsNoetherian S] [S.IsSeparated] in
/-- Sections of the identification of the terms of the two gradings of a resolution. -/
lemma map_inv_map_hom_apply (n : ℤ) (k : ℕ) (h : (k : ℤ) = n)
    (x : (globalSectionsComplexInt I).X n) :
    ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
        (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n k h).inv
      (((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
        (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n k h).hom x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]

omit [IsNoetherian S] [S.IsSeparated] in
/-- Sections of the identification of the terms of the two gradings of a resolution. -/
lemma map_hom_map_inv_apply (n : ℤ) (k : ℕ) (h : (k : ℤ) = n)
    (x : (globalSectionsComplex I).X k) :
    ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
        (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n k h).hom
      (((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
        (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n k h).inv x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]

/-- **Surjectivity of `β_𝔘` on cohomology** (FK, step (3)): every `D`-cocycle of `T_𝔘` is
cohomologous to the image of a cocycle of `Γ(S, I^•)`. -/
lemma exists_cycles_sub_mem_range (𝔘 : CechCovering (final B S hS)) (n : ℕ)
    (t : (cechResolutionTotal I 𝔘).X n) (ht : (cechResolutionTotal I 𝔘).d n (n + 1) t = 0) :
    ∃ y : (globalSectionsComplex I).cycles n,
      (globalSectionsToTotalComplex I 𝔘 n).hom (((globalSectionsComplex I).iCycles n).hom y) -
          t ∈ ((cechResolutionTotal I 𝔘).d ((n : ℤ) - 1) n).hom.range := by
  obtain ⟨f, hf, hβ⟩ := exists_quasiIso_globalSectionsComplexInt I 𝔘
  obtain ⟨y', hy', hmem⟩ :=
    HomologicalComplex.exists_d_eq_zero_and_sub_mem_range_of_isIso_homologyMap f
      (i := (n : ℤ) - 1) (j := n) (k := n + 1) (by simp) (by simp) t ht
  have hy0 : (globalSectionsComplex I).d n (n + 1)
      (((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
        (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n n rfl).hom y') = 0 := by
    have h := globalSectionsComplexInt_d_apply I n (n + 1) n (n + 1) rfl (by push_cast; rfl) y'
    rw [hy'] at h
    have h' := congrArg (((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso (n + 1) (n + 1)
        (by push_cast; rfl)).hom) h
    rw [map_zero, map_hom_map_inv_apply] at h'
    exact h'.symm
  obtain ⟨y, hy⟩ := HomologicalComplex.exists_iCycles_eq_of_d_eq_zero (by simp) _ hy0
  refine ⟨y, ?_⟩
  rw [hy, hβ, ConcreteCategory.comp_apply, map_inv_map_hom_apply]
  exact hmem

/-- **Injectivity of `β_𝔘` on cohomology** (FK, step (3)): a cocycle of `Γ(S, I^•)` whose image
in `T_𝔘` is a `D`-coboundary has zero class. -/
lemma homologyπ_eq_zero_of_mem_range (𝔘 : CechCovering (final B S hS)) (n : ℕ)
    (y : (globalSectionsComplex I).cycles n)
    (hy : (globalSectionsToTotalComplex I 𝔘 n).hom
      (((globalSectionsComplex I).iCycles n).hom y) ∈
        ((cechResolutionTotal I 𝔘).d ((n : ℤ) - 1) n).hom.range) :
    ((globalSectionsComplex I).homologyπ n).hom y = 0 := by
  obtain ⟨f, hf, hβ⟩ := exists_quasiIso_globalSectionsComplexInt I 𝔘
  set Γ := (sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
    (op (SmallEtale.final B S hS))
  set w := ((globalSectionsComplex I).iCycles n).hom y
  have hw : (globalSectionsComplexInt I).d n (n + 1)
      (Γ.map (I.cochainComplexXIso n n rfl).inv w) = 0 := by
    rw [globalSectionsComplexInt_d_apply I n (n + 1) n (n + 1) rfl (by push_cast; rfl),
      map_hom_map_inv_apply]
    change Γ.map _ (((globalSectionsComplex I).iCycles n ≫
      (globalSectionsComplex I).d n (n + 1)) y) = 0
    rw [HomologicalComplex.iCycles_d, AddCommGrpCat.zero_apply, map_zero]
  rw [hβ, ConcreteCategory.comp_apply] at hy
  obtain ⟨x, hx⟩ := HomologicalComplex.mem_range_of_isIso_homologyMap f
    (i := (n : ℤ) - 1) (j := n) (k := n + 1) (by simp) (by simp) _ hw hy
  have key : ∃ x₀, (globalSectionsComplex I).d (n - 1) n x₀ = w := by
    rcases n with _ | m
    · refine ⟨0, ?_⟩
      have hz : IsZero ((globalSectionsComplexInt I).X ((0 : ℕ) - 1 : ℤ)) :=
        Γ.map_isZero (isZero_cochainComplex_X I _ (by simp))
      have hx0 : x = 0 := (AddCommGrpCat.isZero_iff_subsingleton.1 hz).elim x 0
      rw [hx0, map_zero] at hx
      have h' := congrArg (Γ.map (I.cochainComplexXIso _ 0 rfl).hom) hx
      rw [map_zero, map_hom_map_inv_apply] at h'
      rw [map_zero]
      exact h'
    · refine ⟨Γ.map (I.cochainComplexXIso _ m (by push_cast; ring)).hom x, ?_⟩
      rw [globalSectionsComplexInt_d_apply I _ _ m (m + 1) (by push_cast; ring) rfl] at hx
      have h' := congrArg (Γ.map (I.cochainComplexXIso _ (m + 1) rfl).hom) hx
      rw [map_hom_map_inv_apply, map_hom_map_inv_apply] at h'
      exact h'
  obtain ⟨x₀, hx₀⟩ := key
  have hyx : y = (globalSectionsComplex I).toCycles (n - 1) n x₀ := by
    apply HomologicalComplex.iCycles_injective n
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i, hx₀]
  rw [hyx, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ,
    AddCommGrpCat.zero_apply]

omit [IsNoetherian S] [S.IsSeparated] in
/-- Restriction to `Et(S)` of the zero morphism of presheaves. -/
lemma whiskerLeft_inclusion_op_zero {P Q : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u}} :
    (inclusion B S hS).op.whiskerLeft (0 : P ⟶ Q) = 0 := by
  ext
  simp

/-- The map `Č^n(𝔘, F) → K^{n,0} = Č^n(𝔘, I^0)` induced by `F → I^0`. -/
def cechToBicomplex (𝔘 : CechCovering (final B S hS)) (n : ℕ) :
    (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).X n ⟶
      ((cechResolutionBicomplex I 𝔘).X n).X 0 :=
  ((sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj (inclusion B S hS).op ⋙
      Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).map I.inclusionZero).f n ≫
    (((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).obj
      (restrictSheaf (I.cochainComplex.X 0))).extendXIso ComplexShape.embeddingUpNat rfl).inv

/-- `α_𝔘` is the map into `K^{n,0}` followed by the inclusion into `T^n_𝔘`. -/
lemma cechToTotalComplex_eq (𝔘 : CechCovering (final B S hS)) (n : ℕ) :
    cechToTotalComplex I 𝔘 n = cechToBicomplex I 𝔘 n ≫
      (cechResolutionBicomplex I 𝔘).ιTotal (.up ℤ) n 0 n (by simp) := by
  rfl

/-- The composite `F → I^0 → I^1` is zero, so `α_𝔘` is killed by the vertical differential. -/
lemma cechToBicomplex_comp_d₂ (𝔘 : CechCovering (final B S hS)) (n : ℕ) :
    cechToBicomplex I 𝔘 n ≫ ((cechResolutionBicomplex I 𝔘).X n).d 0 1 = 0 := by
  change ((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).map
      (Functor.whiskerLeft (inclusion B S hS).op ((sheafToPresheaf _ _).map I.inclusionZero))).f n ≫
    (((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).obj
      (restrictSheaf (I.cochainComplex.X 0))).extendXIso ComplexShape.embeddingUpNat
        (i' := (n : ℤ)) (i := n) rfl).inv ≫
    (HomologicalComplex.extendMap ((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).map
      (Functor.whiskerLeft (inclusion B S hS).op
        ((sheafToPresheaf _ _).map (I.cochainComplex.d 0 1)))) ComplexShape.embeddingUpNat).f n = 0
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl]
  erw [Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.comp_f_assoc, ← Functor.map_comp, ← Functor.whiskerLeft_comp,
    ← Functor.map_comp, InjectiveResolution.inclusionZero_comp_d, Functor.map_zero,
    whiskerLeft_inclusion_op_zero]
  simp

/-- The map into `K^{•,0}` commutes with the Čech differentials. -/
lemma cechToBicomplex_comp_d₁ (𝔘 : CechCovering (final B S hS)) (n : ℕ) :
    cechToBicomplex I 𝔘 n ≫ ((cechResolutionBicomplex I 𝔘).d n (n + 1 : ℕ)).f 0 =
      (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).d n (n + 1) ≫
        cechToBicomplex I 𝔘 (n + 1) := by
  set K₀ := (Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).obj
    (restrictSheaf (I.cochainComplex.X 0))
  set φ := (Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).map
    (Functor.whiskerLeft (inclusion B S hS).op ((sheafToPresheaf _ _).map I.inclusionZero))
  change φ.f n ≫ (K₀.extendXIso ComplexShape.embeddingUpNat (i' := (n : ℤ)) (i := n) rfl).inv ≫
      (K₀.extend ComplexShape.embeddingUpNat).d n (n + 1 : ℕ) =
    (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).d n (n + 1) ≫ φ.f (n + 1) ≫
      (K₀.extendXIso ComplexShape.embeddingUpNat (i' := ((n + 1 : ℕ) : ℤ)) (i := n + 1) rfl).inv
  rw [K₀.extend_d_eq ComplexShape.embeddingUpNat (i := n) (j := n + 1) (i' := (n : ℤ))
    (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
  erw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc]
  erw [φ.comm n (n + 1)]
  rw [Category.assoc]
  rfl

/-- **`α_𝔘` is a map of complexes** (FK, step (1)): `D ∘ α_𝔘 = α_𝔘 ∘ d_Č`, as
`F → I^0 → I^1` is zero. -/
lemma cechToTotalComplex_comp_d (𝔘 : CechCovering (final B S hS)) (n : ℕ) :
    cechToTotalComplex I 𝔘 n ≫ (cechResolutionTotal I 𝔘).d n (n + 1 : ℕ) =
      (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).d n (n + 1) ≫
        cechToTotalComplex I 𝔘 (n + 1) := by
  rw [cechToTotalComplex_eq, cechToTotalComplex_eq, Category.assoc,
    HomologicalComplex₂.comp_ιTotal_d_of_comp_d₂_eq_zero _ _ _ (by push_cast; rfl) _
      (cechToBicomplex_comp_d₂ I 𝔘 n), reassoc_of% (cechToBicomplex_comp_d₁ I 𝔘 n)]

/-- The map `I^n(S) → K^{0,n} = Č^0(𝔘, I^n)`, `y ↦ (y|_{U_ν})_ν`. -/
def globalSectionsToBicomplex (𝔘 : CechCovering (final B S hS)) (n : ℕ) :
    ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B S hS))).obj (I.cocomplex.X n) ⟶
      ((cechResolutionBicomplex I 𝔘).X 0).X n :=
  ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n n rfl).inv ≫
    cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf (I.cochainComplex.X n)) ≫
    (((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).obj
      (restrictSheaf (I.cochainComplex.X n))).extendXIso ComplexShape.embeddingUpNat rfl).inv

/-- `β_𝔘` is the map into `K^{0,n}` followed by the inclusion into `T^n_𝔘`. -/
lemma globalSectionsToTotalComplex_eq (𝔘 : CechCovering (final B S hS)) (n : ℕ) :
    globalSectionsToTotalComplex I 𝔘 n = globalSectionsToBicomplex I 𝔘 n ≫
      (cechResolutionBicomplex I 𝔘).ιTotal (.up ℤ) 0 n n (by simp) := by
  rfl

/-- The refinement map `φ^* : Č^•(𝔘, -) → Č^•(𝔚, -)` on integer-graded Čech complexes of
restrictions of sheaves, as a natural transformation. -/
def refinementCochainNatTrans {𝔚 𝔘 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ 𝔘.toPreZeroHypercover) :
    cechCochainFunctor (B := B) (S := S) (hS := hS) 𝔘.toPreZeroHypercover ⟶
      cechCochainFunctor 𝔚.toPreZeroHypercover where
  app G := HomologicalComplex.extendMap (refinementCochainMap φ (restrictSheaf G))
    ComplexShape.embeddingUpNat
  naturality G G' ψ := by
    change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ =
      HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _
    rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    exact congrArg (HomologicalComplex.extendMap · ComplexShape.embeddingUpNat)
      (refinementCochainMap_naturality φ _)

/-- **The refinement map of double complexes** `φ^* : K_𝔘 → K_𝔚`. -/
def refinementBicomplexMap {𝔚 𝔘 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ 𝔘.toPreZeroHypercover) :
    cechResolutionBicomplex I 𝔘 ⟶ cechResolutionBicomplex I 𝔚 :=
  (HomologicalComplex₂.flipFunctor _ _ _).map
    ((NatTrans.mapHomologicalComplex (refinementCochainNatTrans φ) (.up ℤ)).app I.cochainComplex)

/-- **The refinement map of total complexes** `φ^* : T_𝔘 → T_𝔚`. -/
def refinementTotalMap {𝔚 𝔘 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ 𝔘.toPreZeroHypercover) :
    cechResolutionTotal I 𝔘 ⟶ cechResolutionTotal I 𝔚 :=
  HomologicalComplex₂.total.map (refinementBicomplexMap I φ) (.up ℤ)

/-- `φ^*` commutes with `α` (FK, step (4)). -/
lemma cechToTotalComplex_comp_refinementTotalMap {𝔚 𝔘 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ 𝔘.toPreZeroHypercover) (n : ℕ) :
    cechToTotalComplex I 𝔘 n ≫ (refinementTotalMap I φ).f n =
      (refinementCochainMap φ (restrictSheaf F)).f n ≫ cechToTotalComplex I 𝔚 n := by
  rw [cechToTotalComplex_eq, cechToTotalComplex_eq, Category.assoc, refinementTotalMap,
    HomologicalComplex₂.ιTotal_map, ← Category.assoc, ← Category.assoc]
  congr 1
  change ((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).map
      (Functor.whiskerLeft (inclusion B S hS).op ((sheafToPresheaf _ _).map I.inclusionZero))).f n ≫
    (((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).obj
      (restrictSheaf (I.cochainComplex.X 0))).extendXIso ComplexShape.embeddingUpNat
        (i' := (n : ℤ)) (i := n) rfl).inv ≫
    (HomologicalComplex.extendMap (refinementCochainMap φ (restrictSheaf (I.cochainComplex.X 0)))
      ComplexShape.embeddingUpNat).f n =
    (refinementCochainMap φ (restrictSheaf F)).f n ≫
      ((Stacks.CechSite.cechComplexFunctor 𝔚.toPreZeroHypercover).map
        (Functor.whiskerLeft (inclusion B S hS).op
          ((sheafToPresheaf _ _).map I.inclusionZero))).f n ≫
      (((Stacks.CechSite.cechComplexFunctor 𝔚.toPreZeroHypercover).obj
        (restrictSheaf (I.cochainComplex.X 0))).extendXIso ComplexShape.embeddingUpNat
          (i' := (n : ℤ)) (i := n) rfl).inv
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl]
  erw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← HomologicalComplex.comp_f]
  erw [refinementCochainMap_naturality]
  rw [HomologicalComplex.comp_f, Category.assoc]
  rfl

/-- `φ^*` commutes with `β` (FK, step (4); functoriality of restriction). -/
lemma globalSectionsToTotalComplex_comp_refinementTotalMap {𝔚 𝔘 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ 𝔘.toPreZeroHypercover) (n : ℕ) :
    globalSectionsToTotalComplex I 𝔘 n ≫ (refinementTotalMap I φ).f n =
      globalSectionsToTotalComplex I 𝔚 n := by
  rw [globalSectionsToTotalComplex_eq, globalSectionsToTotalComplex_eq, Category.assoc,
    refinementTotalMap, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  congr 1
  change ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n n rfl).inv ≫
    cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf (I.cochainComplex.X n)) ≫
    (((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).obj
      (restrictSheaf (I.cochainComplex.X n))).extendXIso ComplexShape.embeddingUpNat
        (i' := (0 : ℤ)) (i := 0) rfl).inv ≫
    (HomologicalComplex.extendMap (refinementCochainMap φ (restrictSheaf (I.cochainComplex.X n)))
      ComplexShape.embeddingUpNat).f 0 =
    ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n n rfl).inv ≫
    cechAugmentation 𝔚.toPreZeroHypercover (restrictSheaf (I.cochainComplex.X n)) ≫
    (((Stacks.CechSite.cechComplexFunctor 𝔚.toPreZeroHypercover).obj
      (restrictSheaf (I.cochainComplex.X n))).extendXIso ComplexShape.embeddingUpNat
        (i' := (0 : ℤ)) (i := 0) rfl).inv
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl]
  erw [Iso.inv_hom_id_assoc]
  erw [cechAugmentation_comp_refinementCochainMap_assoc]
  rfl

/-- A cocycle `y` of `Γ(S, I^•)` *matches* a Čech cocycle `z` on `𝔘` if
`β_𝔘(y) - α_𝔘(z) ∈ D(T^{i-1}_𝔘)`; this is the hypothesis of the defining property of a
canonical Čech-to-derived map. -/
def CechMatch (𝔘 : CechCovering (final B S hS)) (i : ℕ)
    (z : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i)
    (y : (globalSectionsComplex I).cycles i) : Prop :=
  (globalSectionsToTotalComplex I 𝔘 i).hom (((globalSectionsComplex I).iCycles i).hom y) -
      (cechToTotalComplex I 𝔘 i).hom z ∈
    ((cechResolutionTotal I 𝔘).d ((i : ℤ) - 1) i).hom.range

variable {I}

/-- `D(α_𝔘(u)) = α_𝔘(d u)`, elementwise. -/
lemma cechToTotalComplex_d_apply (𝔘 : CechCovering (final B S hS)) (n : ℕ)
    (u : (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).X n) :
    (cechResolutionTotal I 𝔘).d n (n + 1 : ℕ) ((cechToTotalComplex I 𝔘 n) u) =
      cechToTotalComplex I 𝔘 (n + 1)
        ((cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).d n (n + 1) u) := by
  rw [← ConcreteCategory.comp_apply, cechToTotalComplex_comp_d, ConcreteCategory.comp_apply]

/-- **Existence of a matching cocycle** (FK, step (4)): `α_𝔘(z)` is a `D`-cocycle, which is
cohomologous to some `β_𝔘(y)`. -/
lemma exists_cechMatch (𝔘 : CechCovering (final B S hS)) (i : ℕ)
    (z : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i) :
    ∃ y, CechMatch I 𝔘 i z y := by
  have ht := cechToTotalComplex_d_apply (I := I) 𝔘 i z
  have hz : (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).d i (i + 1) z = 0 :=
    (mem_cechCycles_iff 𝔘.toPreZeroHypercover (restrictSheaf F) z.1).1 z.2
  rw [hz, map_zero] at ht
  have ht' : (cechResolutionTotal I 𝔘).d i (i + 1) ((cechToTotalComplex I 𝔘 i) z) = 0 := by
    rw [← Nat.cast_succ]
    exact ht
  obtain ⟨y, hy⟩ := exists_cycles_sub_mem_range I 𝔘 i _ ht'
  exact ⟨y, hy⟩

/-- **Uniqueness of the class of a matching cocycle** (FK, step (4)). -/
lemma homologyπ_eq_of_cechMatch {𝔘 : CechCovering (final B S hS)} {i : ℕ}
    {z : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i}
    {y y' : (globalSectionsComplex I).cycles i} (h : CechMatch I 𝔘 i z y)
    (h' : CechMatch I 𝔘 i z y') :
    ((globalSectionsComplex I).homologyπ i).hom y =
      ((globalSectionsComplex I).homologyπ i).hom y' := by
  rw [← sub_eq_zero, ← map_sub]
  refine homologyπ_eq_zero_of_mem_range I 𝔘 i _ ?_
  have := sub_mem h h'
  rwa [sub_sub_sub_cancel_right, ← map_sub, ← map_sub] at this

/-- `0` matches `0`. -/
lemma cechMatch_zero (𝔘 : CechCovering (final B S hS)) (i : ℕ) : CechMatch I 𝔘 i 0 0 := by
  rw [CechMatch, map_zero, map_zero, ZeroMemClass.coe_zero, map_zero, sub_zero]
  exact zero_mem _

/-- Matching is additive. -/
lemma cechMatch_add {𝔘 : CechCovering (final B S hS)} {i : ℕ}
    {z z' : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i}
    {y y' : (globalSectionsComplex I).cycles i} (h : CechMatch I 𝔘 i z y)
    (h' : CechMatch I 𝔘 i z' y') : CechMatch I 𝔘 i (z + z') (y + y') := by
  have := add_mem h h'
  rw [CechMatch, map_add, map_add, AddMemClass.coe_add, map_add]
  convert this using 1
  abel

/-- **Changing the Čech cocycle by a coboundary** keeps a matching cocycle matching
(FK, step (4): `α(du) = Dα(u)`). -/
lemma CechMatch.of_sub_mem_range {𝔘 : CechCovering (final B S hS)} {i : ℕ}
    {z z' : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i}
    {y : (globalSectionsComplex I).cycles i} (h : CechMatch I 𝔘 i z y)
    (hzz : (z : (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).X i) - z' ∈
      ((cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).d (i - 1) i).hom.range) :
    CechMatch I 𝔘 i z' y := by
  have hα : (cechToTotalComplex I 𝔘 i).hom
      ((z : (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).X i) - z') ∈
      ((cechResolutionTotal I 𝔘).d ((i : ℤ) - 1) i).hom.range := by
    obtain ⟨u, hu⟩ := hzz
    rcases i with _ | m
    · rw [← hu, (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).shape 0 0 (by simp),
        AddCommGrpCat.zero_apply, map_zero]
      exact zero_mem _
    · rw [show ((m + 1 : ℕ) : ℤ) - 1 = m by push_cast; ring]
      refine ⟨(cechToTotalComplex I 𝔘 m) u, ?_⟩
      rw [← hu]
      exact cechToTotalComplex_d_apply 𝔘 m u
  have := add_mem h hα
  rw [CechMatch]
  convert this using 1
  rw [map_sub]
  abel

/-- **Refinement keeps a matching cocycle matching** (FK, step (4)): `φ^*` commutes with `D`,
`α` and `β`. -/
lemma CechMatch.refinement {𝔚 𝔘 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ 𝔘.toPreZeroHypercover) {i : ℕ}
    {z : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i}
    {y : (globalSectionsComplex I).cycles i} (h : CechMatch I 𝔘 i z y) :
    CechMatch I 𝔚 i (cechCyclesMap (restrictSheaf F) i φ z) y := by
  obtain ⟨w, hw⟩ := h
  refine ⟨(refinementTotalMap I φ).f _ w, ?_⟩
  rw [← ConcreteCategory.comp_apply, (refinementTotalMap I φ).comm, ConcreteCategory.comp_apply,
    hw, map_sub, ← ConcreteCategory.comp_apply (globalSectionsToTotalComplex I 𝔘 i),
    globalSectionsToTotalComplex_comp_refinementTotalMap,
    ← ConcreteCategory.comp_apply (cechToTotalComplex I 𝔘 i),
    cechToTotalComplex_comp_refinementTotalMap, ConcreteCategory.comp_apply, coe_cechCyclesMap]

variable [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})]

variable (I) in
/-- **The map `γ_𝔘 : Z^i(𝔘, F) → H^i(S, F)`** (FK, step (4)): a Čech cocycle goes to the class
of a matching cocycle of `Γ(S, I^•)`. -/
def cechCyclesToH (𝔘 : CechCovering (final B S hS)) (i : ℕ) :
    cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i →+ F.H i where
  toFun z := (SmallEtale.hAddEquivHomologySections B S hS F I i).symm
    (((globalSectionsComplex I).homologyπ i).hom (exists_cechMatch (I := I) 𝔘 i z).choose)
  map_zero' := by
    rw [homologyπ_eq_of_cechMatch (exists_cechMatch (I := I) 𝔘 i 0).choose_spec
      (cechMatch_zero 𝔘 i), map_zero, map_zero]
  map_add' z z' := by
    rw [homologyπ_eq_of_cechMatch (exists_cechMatch (I := I) 𝔘 i (z + z')).choose_spec
      (cechMatch_add (exists_cechMatch (I := I) 𝔘 i z).choose_spec
        (exists_cechMatch (I := I) 𝔘 i z').choose_spec), map_add, map_add]

/-- `γ_𝔘(z)` is the class of any cocycle matching `z`. -/
lemma cechCyclesToH_eq {𝔘 : CechCovering (final B S hS)} {i : ℕ}
    {z : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i}
    {y : (globalSectionsComplex I).cycles i} (h : CechMatch I 𝔘 i z y) :
    cechCyclesToH I 𝔘 i z = (SmallEtale.hAddEquivHomologySections B S hS F I i).symm
      (((globalSectionsComplex I).homologyπ i).hom y) := by
  change (SmallEtale.hAddEquivHomologySections B S hS F I i).symm _ = _
  rw [homologyπ_eq_of_cechMatch (exists_cechMatch (I := I) 𝔘 i z).choose_spec h]

/-- `γ` agrees on equivalent cocycles. -/
lemma cechCyclesToH_eq_of_cechCycleRel {𝔘 𝔘' : CechCovering (final B S hS)} {i : ℕ}
    {z : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i}
    {z' : cechCycles 𝔘'.toPreZeroHypercover (restrictSheaf F) i}
    (h : CechCycleRel (restrictSheaf F) i z z') :
    cechCyclesToH I 𝔘 i z = cechCyclesToH I 𝔘' i z' := by
  obtain ⟨𝔚, φ, φ', hφ⟩ := h
  have hy := (exists_cechMatch (I := I) 𝔘 i z).choose_spec
  have hy' := (exists_cechMatch (I := I) 𝔘' i z').choose_spec
  rw [cechCyclesToH_eq hy, cechCyclesToH_eq hy']
  congr 1
  refine homologyπ_eq_of_cechMatch ((hy.refinement φ).of_sub_mem_range ?_) (hy'.refinement φ')
  rwa [coe_cechCyclesMap, coe_cechCyclesMap]

variable (I) in
/-- **Existence and uniqueness of the canonical Čech-to-derived map.** For an abelian sheaf `F`
on the small étale site of a noetherian separated scheme `S`, an injective resolution
`F → I^•` and `i ≥ 0`, there is exactly one canonical Čech-to-derived map
`c : Ȟ^i(S, F) → H^i(S, F)`. -/
@[weil "lem_fk102_cech_to_derived_map_exists_unique"]
theorem existsUnique_isCanonicalCechToDerivedMap (i : ℕ) :
    ∃! c : cechCohomologyOfObject (final B S hS) (restrictSheaf F) i →+ F.H i,
      IsCanonicalCechToDerivedMap I i c := by
  refine ⟨cechCohomologyOfObjectDesc (restrictSheaf F) i (fun 𝔘 ↦ cechCyclesToH I 𝔘 i)
    (fun _ _ _ _ h ↦ cechCyclesToH_eq_of_cechCycleRel h), ?_, ?_⟩
  · intro 𝔘 z y h
    rw [cechCohomologyOfObjectDesc_cechClass]
    exact cechCyclesToH_eq h
  · intro c hc
    refine cechCohomologyOfObject_hom_ext (restrictSheaf F) i fun 𝔘 z ↦ ?_
    rw [cechCohomologyOfObjectDesc_cechClass,
      hc.apply_cechClass 𝔘 z _ (exists_cechMatch (I := I) 𝔘 i z).choose_spec]
    rfl

end Resolution

end AlgebraicGeometry.SmallNoetherianSeparatedEtale
