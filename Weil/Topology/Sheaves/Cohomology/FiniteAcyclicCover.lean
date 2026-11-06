module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.AcyclicCoveringFamilyCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.VanishingAboveCardinality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOnTheSlice
public import Mathlib.Algebra.Category.Grp.EpiMono
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyOverAnObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Acyclic open covers compute sheaf cohomology

Let `X` be a topological space, `U : ι → Opens X` an open cover of `X` and `F` an abelian sheaf
on `X` whose higher cohomology vanishes over every nonempty finite intersection
`U_{i_0} ∩ ⋯ ∩ U_{i_p}`.  Then the sheaf cohomology `Hⁿ(X, F)` (Mathlib's `Sheaf.H`) is the Čech
cohomology `Ȟⁿ(U, F)` of the cover, in every degree (Leray's theorem).  Two consequences:

* if `ι` is finite and the sections of `F` over the nonempty finite intersections are finitely
  generated abelian groups, every `Hⁿ(X, F)` is finitely generated;
* if any `N + 1` distinct members of the cover have empty intersection, then `Hⁿ(X, F) = 0` for
  all `n ≥ N`: an alternating Čech cochain of degree `n` is indexed by injective tuples of length
  `n + 1`, all of whose intersections are empty.

## Main definitions

* `TopologicalSpace.Opens.CechAcyclic.sheafHIsoCechHomology`: `Hⁿ(X, F) ≅ Ȟⁿ(U, F)`, Mathlib's
  Čech complex `CategoryTheory.cechComplexFunctor U`.
* `TopologicalSpace.Opens.CechAcyclic.sheafHIsoAlternatingCechHomology`: the same with the
  alternating Čech complex.
* `TopologicalSpace.Opens.CechAcyclic.siteCechComplexIso`: the Čech complex of `U` as a covering
  family of `⊤` on the site of opens is Mathlib's Čech complex of `U`.

## Main results

* `TopologicalSpace.Opens.CechAcyclic.finite_sheafH`: finite generation.
* `TopologicalSpace.Opens.CechAcyclic.subsingleton_sheafH_of_iInf_eq_bot`: vanishing in degrees
  at least `N`.
* `TopologicalSpace.Opens.CechAcyclic.subsingleton_H'_iff_over`: the acyclicity hypothesis,
  stated with the cohomology `Sheaf.H' F q V` of `F` over the open `V`, is the vanishing of the
  cohomology of the restriction `F.over V`.

## Implementation notes

The isomorphism is the acyclic-covering theorem for a covering family on a site, applied to the
family `U i ⟶ ⊤`, composed with the identification of global cohomology with derived sections
over the terminal object `⊤`.  The fibre products of the family in `Over ⊤` are the
intersections of the members, all morphisms of `Over ⊤` being unique.

The acyclicity hypothesis is indexed by nonempty finsets of indices, so that a tuple with
repetitions is covered by its image.

## References

* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopologicalSpace.Opens.CechAcyclic

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- Any two morphisms in the slice of the opens of `X` over `⊤` agree. -/
instance subsingleton_overTopHom (A B : Over (⊤ : Opens X)) : Subsingleton (A ⟶ B) :=
  ⟨fun _ _ ↦ Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

/-- An open subset of `X`, read as an object over `⊤`. -/
def toOverTop : Opens X ⥤ Over (⊤ : Opens X) where
  obj _ := Over.mk (homOfLE le_top)
  map f := Over.homMk f (Subsingleton.elim _ _)

theorem toOverTop_comp_forget : toOverTop (X := X) ⋙ Over.forget ⊤ = 𝟭 _ := rfl

/-- The family `U`, as a family of morphisms with target `⊤`. -/
def hypercover : PreZeroHypercover.{u} (⊤ : Opens X) where
  I₀ := ι
  X := U
  f _ := homOfLE le_top

/-- A functor between categories induces one between their categories of formal coproducts. -/
@[simps]
def formalCoproductMap {D : Type*} [Category* D] {C : Type*} [Category* C] (Φ : D ⥤ C) :
    FormalCoproduct.{u} D ⥤ FormalCoproduct.{u} C where
  obj Y := ⟨Y.I, fun i ↦ Φ.obj (Y.obj i)⟩
  map f := ⟨f.f, fun i ↦ Φ.map (f.φ i)⟩
  map_id _ := FormalCoproduct.hom_ext rfl fun i ↦ by simp
  map_comp _ _ := FormalCoproduct.hom_ext rfl fun i ↦ by simp

/-- The rightOp of a natural isomorphism. -/
def natIsoRightOp {C : Type*} [Category* C] {D : Type*} [Category* D] {F G : Cᵒᵖ ⥤ D}
    (η : F ≅ G) : F.rightOp ≅ G.rightOp where
  hom := NatTrans.rightOp η.inv
  inv := NatTrans.rightOp η.hom
  hom_inv_id := by rw [← NatTrans.rightOp_comp, η.hom_inv_id, NatTrans.rightOp_id]
  inv_hom_id := by rw [← NatTrans.rightOp_comp, η.inv_hom_id, NatTrans.rightOp_id]

/-- The product over `⊤` of a finite tuple of members of the cover is the product of the
opens. -/
def piIso {α : Type} [Finite α] (i : α → ι) :
    (∏ᶜ fun a ↦ Over.mk ((hypercover U).f (i a))) ≅ toOverTop.obj (∏ᶜ (U ∘ i)) where
  hom := Over.homMk (Pi.lift fun a ↦
    (Pi.π (fun a ↦ Over.mk ((hypercover U).f (i a))) a).left) (Subsingleton.elim _ _)
  inv := Pi.lift fun a ↦ Over.homMk (Pi.π (U ∘ i) a) (Subsingleton.elim _ _)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Degreewise identification of the Čech formal coproducts. -/
def cechFormalCoproductIso (α : Type) [Finite α] :
    Stacks.CechSite.cechFormalCoproduct (hypercover U) α ≅
      (formalCoproductMap toOverTop).obj ((FormalCoproduct.mk ι U).power α) :=
  FormalCoproduct.isoOfComponents (Equiv.refl _) fun i ↦ piIso U i

theorem cechFormalCoproductIso_naturality {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m) :
    (Stacks.CechSite.cechSimplicialObject (hypercover U)).map g ≫
        (cechFormalCoproductIso U (ToType m.unop)).hom =
      (cechFormalCoproductIso U (ToType n.unop)).hom ≫
        (formalCoproductMap toOverTop).map ((FormalCoproduct.mk ι U).cech.map g) :=
  (FormalCoproduct.hom_ext_iff' _ _).2 fun _ ↦ ⟨rfl, Subsingleton.elim _ _⟩

/-- The Čech simplicial objects agree. -/
def cechSimplicialObjectIso :
    Stacks.CechSite.cechSimplicialObject (hypercover U) ≅
      (FormalCoproduct.mk ι U).cech ⋙ formalCoproductMap toOverTop :=
  NatIso.ofComponents (fun n ↦ cechFormalCoproductIso U (ToType n.unop))
    (fun g ↦ cechFormalCoproductIso_naturality U g)

/-- The Čech cosimplicial objects agree. -/
def sliceCechCosimplicialObjectIso (P : (Over (⊤ : Opens X))ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Stacks.CechSite.sliceCechCosimplicialObject (hypercover U) P ≅
      (FormalCoproduct.cosimplicialObjectFunctor ((FormalCoproduct.mk ι U).cech)).obj
        (toOverTop.op ⋙ P) :=
  Functor.isoWhiskerRight (natIsoRightOp (cechSimplicialObjectIso U))
    ((FormalCoproduct.evalOp.{u} (Over (⊤ : Opens X)) AddCommGrpCat.{u}).obj P)

/-- **The Čech complex of the family `U`, read as a covering family of `⊤` on the site of opens,
is Mathlib's Čech complex of `U`.** -/
def siteCechComplexIso (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Stacks.CechSite.cechComplex (hypercover U) F ≅ (cechComplexFunctor U).obj F :=
  Stacks.CechSite.sliceCechComplexIsoOfCosimplicialIso _
    (sliceCechCosimplicialObjectIso U ((Over.forget ⊤).op ⋙ F))

/-- If the members of `U` cover `X`, the family `U` is a covering family of `⊤`. -/
theorem generate_presieve₀_mem (hU : ⨆ i, U i = ⊤) :
    Sieve.generate (hypercover U).presieve₀ ∈ Opens.grothendieckTopology X ⊤ := by
  intro x _
  have hx : x ∈ ⨆ i, U i := hU ▸ True.intro
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  refine ⟨U i, (hypercover U).f i, ?_, hi⟩
  apply Sieve.le_generate
  exact Presieve.ofArrows.mk i

/-- The fibre product over `⊤` of a tuple of members of `U` is their intersection. -/
theorem tupleObj_eq {r : ℕ} (s : Fin (r + 1) → ι) :
    Stacks.CechSite.Acyclic.tupleObj (hypercover U) s = ⨅ k, U (s k) :=
  le_antisymm (le_iInf fun k ↦ leOfHom (Pi.π (fun j ↦ Over.mk ((hypercover U).f (s j))) k).left)
    (leOfHom (Pi.lift (fun k ↦ Over.homMk (homOfLE (iInf_le _ k)) (Subsingleton.elim _ _)) :
      toOverTop.obj (⨅ k, U (s k)) ⟶ ∏ᶜ fun j ↦ Over.mk ((hypercover U).f (s j))).left)

/-- The intersection selected by a tuple is the intersection over the image of the tuple. -/
theorem iInf_eq_iInf_image {r : ℕ} (s : Fin (r + 1) → ι) [DecidableEq ι] :
    ⨅ k, U (s k) = ⨅ i ∈ Finset.univ.image s, U i := by
  rw [Finset.iInf_finset_image]
  simp

variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Acyclicity on the nonempty finite intersections, in the form of right derived sections over
the fibre products of the covering family. -/
theorem isZero_rightDerived_tupleSections
    (hac : ∀ s : Finset ι, s.Nonempty → ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H' F q (⨅ i ∈ s, U i) : AddCommGrpCat.{u}))
    (r : ℕ) (s : Fin (r + 1) → ι) (q : ℕ) (hq : 0 < q) :
    IsZero (((Stacks.CechSite.Acyclic.tupleSections (Opens.grothendieckTopology X)
      (hypercover U) s).rightDerived q).obj F) := by
  classical
  have h := hac (Finset.univ.image s) (Finset.univ_nonempty.image s) q hq
  rw [← iInf_eq_iInf_image U s, ← tupleObj_eq U s] at h
  exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
      (Opens.grothendieckTopology X) F q _).symm

/-- The cohomology of `F` over an open `V` vanishes exactly when the cohomology of the restriction
of `F` to the slice over `V` does. -/
theorem subsingleton_H'_iff_over (V : Opens X) (n : ℕ) :
    Subsingleton (Sheaf.H' F n V : AddCommGrpCat.{u}) ↔
      Subsingleton (Sheaf.H.{u} (F.over V) n) := by
  have := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{u, u, u}
    (Opens.grothendieckTopology X) V
  have := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u, u, u}
    (Opens.grothendieckTopology X) V
  have e := Stacks.Cohomology.OverObjectCohomology.h'AddEquivHOverSheafPullback.{u}
    (Opens.grothendieckTopology X) V F n
  exact ⟨fun h ↦ @Equiv.subsingleton _ _ e.toEquiv.symm h,
    fun h ↦ @Equiv.subsingleton _ _ e.toEquiv h⟩

/-- **Leray's theorem for an open cover with acyclic intersections.**  If `U` covers `X` and the
higher cohomology of `F` vanishes over every nonempty finite intersection of members of `U`,
then the sheaf cohomology `Hⁿ(X, F)` is the Čech cohomology `Ȟⁿ(U, F)`. -/
def sheafHIsoCechHomology (hU : ⨆ i, U i = ⊤)
    (hac : ∀ s : Finset ι, s.Nonempty → ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H' F q (⨅ i ∈ s, U i) : AddCommGrpCat.{u}))
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u} F n) ≅ ((cechComplexFunctor U).obj F.obj).homology n :=
  (Stacks.Cohomology.TerminalCohomology.h'IsoH (Opens.grothendieckTopology X) F n ⊤
      Stacks.Cohomology.TerminalCohomology.topIsTerminal).symm ≪≫
    Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections _ F n ⊤ ≪≫
    (Stacks.CechSite.Acyclic.cechCohomologyIsoRightDerivedSections _ (hypercover U)
      (generate_presieve₀_mem U hU) F (isZero_rightDerived_tupleSections U F hac) n).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (siteCechComplexIso U F.obj)

/-- `sheafHIsoCechHomology` with the alternating Čech complex of `U` for a linear order on the
index type. -/
def sheafHIsoAlternatingCechHomology [LinearOrder ι] (hU : ⨆ i, U i = ⊤)
    (hac : ∀ s : Finset ι, s.Nonempty → ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H' F q (⨅ i ∈ s, U i) : AddCommGrpCat.{u}))
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u} F n) ≅
      (Stacks.Cech.alternatingCechComplex U F.obj).homology n :=
  sheafHIsoCechHomology U F hU hac n ≪≫
    ((Stacks.Cech.alternatingCechInclusionToCechComplexFunctor_homotopyEquivalence U
      F.obj).choose.toHomologyIso n).symm

/-- The homology of a cochain complex of abelian groups is finitely generated in every degree
in which the term is. -/
theorem finite_homology {K : CochainComplex AddCommGrpCat.{u} ℕ} (n : ℕ)
    (h : Module.Finite ℤ (K.X n)) : Module.Finite ℤ (K.homology n) := by
  have hi : Function.Injective (K.iCycles n) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hπ : Function.Surjective (K.homologyπ n) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  have : Module.Finite ℤ (K.cycles n) :=
    Module.Finite.of_injective (K.iCycles n).hom.toIntLinearMap hi
  exact Module.Finite.of_surjective (K.homologyπ n).hom.toIntLinearMap hπ

/-- Sections of a sheaf over the empty open subset form a trivial group. -/
theorem subsingleton_obj_bot : Subsingleton (F.obj.obj (op ⊥)) :=
  AddCommGrpCat.subsingleton_of_isZero
    (Sheaf.isTerminalOfBotCover F ⊥ (fun x hx ↦ by simp at hx)).isZero

/-- **Finite generation.**  For a finite open cover with acyclic intersections on which the
sections of `F` are finitely generated, every cohomology group of `F` is finitely generated. -/
theorem finite_sheafH [Finite ι] (hU : ⨆ i, U i = ⊤)
    (hac : ∀ s : Finset ι, s.Nonempty → ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H' F q (⨅ i ∈ s, U i) : AddCommGrpCat.{u}))
    (hfg : ∀ s : Finset ι, s.Nonempty → Module.Finite ℤ (F.obj.obj (op (⨅ i ∈ s, U i))))
    (n : ℕ) : Module.Finite ℤ (Sheaf.H.{u} F n) := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have hfac : ∀ i : Fin (n + 1) → ι,
      Module.Finite ℤ (F.obj.obj (op (_root_.CechCochains.inter U i))) := by
    intro i
    have h := hfg (Finset.univ.image i) (Finset.univ_nonempty.image i)
    rw [← iInf_eq_iInf_image U i] at h
    exact h
  have hcoch : Module.Finite ℤ (_root_.CechCochains.Cochain U F.obj n) :=
    @Module.Finite.pi ℤ _ _ _ _ _ _ hfac
  have hX : Module.Finite ℤ ((Stacks.Cech.alternatingCechComplex U F.obj).X n) := by
    rw [Stacks.Cech.alternatingCechComplex_X]
    exact Module.Finite.of_injective
      (_root_.CechCochains.alternatingSubgroup U F.obj n).subtype.toIntLinearMap
      Subtype.val_injective
  have hH := finite_homology n hX
  exact Module.Finite.equiv
    (sheafHIsoAlternatingCechHomology U F hU hac n).symm.addCommGroupIsoToAddEquiv.toIntLinearEquiv

/-- **Vanishing above the nerve dimension.**  If any `N + 1` distinct members of an open cover
with acyclic intersections have empty intersection, then `Hⁿ(X, F) = 0` for every `n ≥ N`. -/
theorem subsingleton_sheafH_of_iInf_eq_bot (hU : ⨆ i, U i = ⊤)
    (hac : ∀ s : Finset ι, s.Nonempty → ∀ q : ℕ, 0 < q →
      Subsingleton (Sheaf.H' F q (⨅ i ∈ s, U i) : AddCommGrpCat.{u}))
    (N : ℕ) (hN : ∀ s : Finset ι, N < s.card → ⨅ i ∈ s, U i = ⊥) {n : ℕ} (hn : N ≤ n) :
    Subsingleton (Sheaf.H.{u} F n) := by
  classical
  let : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have hbot : _root_.CechCochains.alternatingSubgroup U F.obj n = ⊥ := by
    refine le_antisymm (fun c hc ↦ AddSubgroup.mem_bot.2 (funext fun i ↦ ?_)) bot_le
    by_cases hinj : Function.Injective i
    · have hcard : N < (Finset.univ.image i).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        omega
      have he : _root_.CechCochains.inter U i = ⊥ := by
        change ⨅ k, U (i k) = ⊥
        rw [iInf_eq_iInf_image U i]
        exact hN _ hcard
      have : Subsingleton (F.obj.obj (op (_root_.CechCochains.inter U i))) := by
        rw [he]
        exact subsingleton_obj_bot F
      exact Subsingleton.elim _ _
    · exact hc.1 i hinj
  have hX : IsZero ((Stacks.Cech.alternatingCechComplex U F.obj).X n) := by
    rw [Stacks.Cech.alternatingCechComplex_X, hbot]
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact AddCommGrpCat.subsingleton_of_isZero
    ((HomologicalComplex.ExactAt.of_isZero hX).isZero_homology.of_iso
      (sheafHIsoAlternatingCechHomology U F hU hac n))

end TopologicalSpace.Opens.CechAcyclic
