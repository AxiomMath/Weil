module

public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.StalkSystem
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Torsion.ArSheavesKernelCokernelRepresentative
public import WeilFrontier.CategoryTheory.Abelian.SerreClass.ArCategoryAbelian
public import WeilFrontier.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Weil.Attr

/-!
# The stalk functor on the Artin–Rees category is exact

Let `S` be a scheme, `l` a natural number and `s` a geometric point of `S`. Taking the system
of stalks `F ↦ F_{•,s}` is a functor from the Artin–Rees category `AR_S` of projective systems of
`l`-torsion sheaves on the small étale site of `S` to the Artin–Rees category of projective
systems of `l`-power torsion `ℤ`-modules. We show that this functor is exact: it preserves the
kernel and the cokernel of every A–R morphism, and hence exact short complexes.

The proof follows the source. An A–R morphism is the class `[r, f]` of a morphism
`f : F[r] ⟶ G` of projective systems; the kernel and cokernel of `f` in the category `P_S` of
projective systems of `l`-torsion sheaves are computed degreewise, and the kernel and cokernel of
`[r, f]` are given by those of `f`. Taking stalks is exact on abelian sheaves, so the stalk
systems of the kernel and cokernel of `f` are a kernel and a cokernel of `f_s`, and these give
the kernel and cokernel of `[r, f_s] = [r, f]_s` in the A–R category of modules.

## Main results

* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.preservesHomology_stalkSystem`: the
  functor `[f] ↦ [f]_s` preserves kernels and cokernels.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.exact_map_stalkSystem`: it sends exact
  short complexes to exact short complexes.

## Implementation notes

The category `P_S` is not shown to be abelian here; its kernels and cokernels are constructed
directly as the degreewise kernels and cokernels in the category of `ℤ`-indexed systems of
abelian sheaves, which are again systems of `l`-torsion sheaves vanishing in low degrees since
`l`-torsion sheaves form a Serre class.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

/-- Reading abelian groups as `ℤ`-modules is the inverse of the equivalence forgetting the
module structure. -/
private def ofAbIsoForget₂Inv :
    Stacks.InjectiveAcyclic.ofAb.{u} ≅ (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (by exact Iso.refl (𝟭 _)) _ ≪≫ Functor.leftUnitor _

private instance : PreservesFiniteLimits Stacks.InjectiveAcyclic.ofAb.{u} :=
  preservesFiniteLimits_of_natIso ofAbIsoForget₂Inv.symm

private instance : PreservesFiniteColimits Stacks.InjectiveAcyclic.ofAb.{u} :=
  preservesFiniteColimits_of_natIso ofAbIsoForget₂Inv.symm

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

private instance (s : GeometricPoint S) : PreservesFiniteLimits (sheafFiberInt B S hS s) :=
  comp_preservesFiniteLimits _ _

private instance (s : GeometricPoint S) : PreservesFiniteColimits (sheafFiberInt B S hS s) :=
  comp_preservesFiniteColimits _ _

namespace LTorsionProjectiveSystem

/-- The degreewise kernel of a morphism of projective systems of `l`-torsion sheaves. -/
private def kerObj {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) :
    LTorsionProjectiveSystem.{u} B S hS l :=
  ⟨kernel f.hom, fun n ↦ (IsLTorsionSheaf.{u} B S hS l).prop_of_mono
      ((kernel.ι f.hom).app (op n)) (X.isLTorsionSheaf_obj n), by
    obtain ⟨n₀, hn₀⟩ := X.exists_isZero_obj
    exact ⟨n₀, fun n hn ↦ (hn₀ n hn).of_mono ((kernel.ι f.hom).app (op n))⟩⟩

private def kerι {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) : kerObj f ⟶ X :=
  ObjectProperty.homMk (kernel.ι f.hom)

private lemma kerι_comp {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) :
    kerι f ≫ f = 0 :=
  InducedCategory.hom_ext (kernel.condition f.hom)

/-- The degreewise kernel is a kernel in `P_S`. -/
private def isLimitKer {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kerι f) (kerι_comp f)) :=
  isLimitOfReflects (ObjectProperty.ι _)
    ((KernelFork.isLimitMapConeEquiv _ _).2 (kernelIsKernel f.hom))

/-- The degreewise cokernel of a morphism of projective systems of `l`-torsion sheaves. -/
private def cokerObj {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) :
    LTorsionProjectiveSystem.{u} B S hS l :=
  ⟨cokernel f.hom, fun n ↦ (IsLTorsionSheaf.{u} B S hS l).prop_of_epi
      ((cokernel.π f.hom).app (op n)) (Y.isLTorsionSheaf_obj n), by
    obtain ⟨n₀, hn₀⟩ := Y.exists_isZero_obj
    exact ⟨n₀, fun n hn ↦ (hn₀ n hn).of_epi ((cokernel.π f.hom).app (op n))⟩⟩

private def cokerπ {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) : Y ⟶ cokerObj f :=
  ObjectProperty.homMk (cokernel.π f.hom)

private lemma comp_cokerπ {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) :
    f ≫ cokerπ f = 0 :=
  InducedCategory.hom_ext (cokernel.condition f.hom)

/-- The degreewise cokernel is a cokernel in `P_S`. -/
private def isColimitCoker {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ (cokerπ f) (comp_cokerπ f)) :=
  isColimitOfReflects (ObjectProperty.ι _)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).2 (cokernelIsCokernel f.hom))

/-- The stalk system of the degreewise kernel of `f` is a kernel of `f_s`. -/
private def isLimitStalkSystemKer (s : GeometricPoint S)
    {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι ((stalkSystem s).map (kerι f))
      (by rw [← Functor.map_comp, kerι_comp, Functor.map_zero])) :=
  isLimitOfReflects (ObjectProperty.ι _)
    ((KernelFork.isLimitMapConeEquiv _ _).2
      ((KernelFork.isLimitMapConeEquiv (KernelFork.ofι _ (kernel.condition f.hom))
        ((Functor.whiskeringRight ℤᵒᵖ _ _).obj (sheafFiberInt B S hS s))).1
        (isLimitOfPreserves _ (kernelIsKernel f.hom))))

/-- The stalk system of the degreewise cokernel of `f` is a cokernel of `f_s`. -/
private def isColimitStalkSystemCoker (s : GeometricPoint S)
    {X Y : LTorsionProjectiveSystem.{u} B S hS l} (f : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ ((stalkSystem s).map (cokerπ f))
      (by rw [← Functor.map_comp, comp_cokerπ, Functor.map_zero])) :=
  isColimitOfReflects (ObjectProperty.ι _)
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).2
      ((CokernelCofork.isColimitMapCoconeEquiv (CokernelCofork.ofπ _ (cokernel.condition f.hom))
        ((Functor.whiskeringRight ℤᵒᵖ _ _).obj (sheafFiberInt B S hS s))).1
        (isColimitOfPreserves _ (cokernelIsCokernel f.hom))))

end LTorsionProjectiveSystem

namespace ArLTorsionProjectiveSystem

open LTorsionProjectiveSystem

/-- `[g]_s = [g_s]` for a morphism `g` of projective systems of `l`-torsion sheaves. -/
private lemma stalkSystem_map_toAr_map (s : GeometricPoint S)
    {X Y : LTorsionProjectiveSystem.{u} B S hS l} (g : X ⟶ Y) :
    (stalkSystem s).map ((toAr B S hS l).map g) =
      (CategoryTheory.ProjectiveSystem.toArCategory.{u} ℤ (l : ℤ)).map
        ((LTorsionProjectiveSystem.stalkSystem s).map g) := by
  change (stalkSystem s).map (homMk 0 ((shiftι B S hS l 0).app X ≫ g)) =
    CategoryTheory.ProjectiveSystem.ArCategory.homMk 0
      (CategoryTheory.ProjectiveSystem.natMap _ 0 ≫ (LTorsionProjectiveSystem.stalkSystem s).map g)
  exact (stalkSystem_map_homMk s 0 _).trans
    (congrArg _ ((LTorsionProjectiveSystem.stalkSystem s).map_comp _ _))

/-- `[ε_r^F]_s = [ε_r^{F_{•,s}}]`. -/
private lemma stalkSystem_map_shiftιIso_hom (s : GeometricPoint S)
    (F : LTorsionProjectiveSystem.{u} B S hS l) (r : ℕ) :
    (stalkSystem s).map (shiftιIso F r).hom =
      (CategoryTheory.ProjectiveSystem.toArCategory.{u} ℤ (l : ℤ)).map
        (CategoryTheory.ProjectiveSystem.natMap
          ((LTorsionProjectiveSystem.stalkSystem s).obj F) r) :=
  (stalkSystem_map_toAr_map s ((shiftι B S hS l r).app F)).trans
    (congrArg _ (LTorsionProjectiveSystem.stalkSystem_map_shiftι s r F))

/-- `([ε_r^F] ∘ [k])_s = [ε_r^{F_{•,s}}] ∘ [k_s]`. -/
private lemma stalkSystem_map_toAr_map_comp_shiftιIso_hom (s : GeometricPoint S)
    {K F : LTorsionProjectiveSystem.{u} B S hS l} {r : ℕ}
    (k : K ⟶ (shift B S hS l (r : ℤ)).obj F) :
    (stalkSystem s).map ((toAr B S hS l).map k ≫ (shiftιIso F r).hom) =
      (CategoryTheory.ProjectiveSystem.toArCategory.{u} ℤ (l : ℤ)).map
          (((LTorsionProjectiveSystem.stalkSystem s).map k :
            (LTorsionProjectiveSystem.stalkSystem s).obj K ⟶
              (CategoryTheory.ProjectiveSystem.shift (r : ℤ)).obj
                ((LTorsionProjectiveSystem.stalkSystem s).obj F))) ≫
        (CategoryTheory.ProjectiveSystem.toArCategory.{u} ℤ (l : ℤ)).map
          (CategoryTheory.ProjectiveSystem.natMap
            ((LTorsionProjectiveSystem.stalkSystem s).obj F) r) :=
  ((stalkSystem s).map_comp ((toAr B S hS l).map k) (shiftιIso F r).hom).trans
    (congrArg₂ (fun a b ↦ a ≫ b) (stalkSystem_map_toAr_map s k)
      (stalkSystem_map_shiftιIso_hom s F r))

private lemma homMk_comp_toAr_map_cokerπ {F G : LTorsionProjectiveSystem.{u} B S hS l} {r : ℕ}
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    homMk r f ≫ (toAr B S hS l).map (cokerπ f) = 0 := by
  change homMk r f ≫ homMk 0 ((shiftι B S hS l 0).app G ≫ cokerπ f) = 0
  rw [homMk_comp_homMk_shiftι_zero, comp_cokerπ, homMk_zero]

private def isLimitKernelForkOfEq {C : Type*} [Category C] [HasZeroMorphisms C] {X Y K : C}
    {f f' : X ⟶ Y} {i i' : K ⟶ X} (hf : f = f') (hi : i = i') {w : i ≫ f = 0}
    {w' : i' ≫ f' = 0} (h : IsLimit (KernelFork.ofι i' w')) :
    IsLimit (KernelFork.ofι i w) := by
  subst hf hi
  exact h

private def isColimitCokernelCoforkOfEq {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Q : C} {f f' : X ⟶ Y} {p p' : Y ⟶ Q} (hf : f = f') (hp : p = p') {w : f ≫ p = 0}
    {w' : f' ≫ p' = 0} (h : IsColimit (CokernelCofork.ofπ p' w')) :
    IsColimit (CokernelCofork.ofπ p w) := by
  subst hf hp
  exact h

/-- The A–R kernel of `[r, f]_s = [r, f_s]` given by the stalk system of the kernel of `f`. -/
private def isLimitStalkSystemKernelFork (s : GeometricPoint S)
    {F G : LTorsionProjectiveSystem.{u} B S hS l} {r : ℕ}
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    IsLimit (KernelFork.ofι
      ((CategoryTheory.ProjectiveSystem.toArCategory.{u} ℤ (l : ℤ)).map
          (((LTorsionProjectiveSystem.stalkSystem s).map (kerι f) :
            (LTorsionProjectiveSystem.stalkSystem s).obj (kerObj f) ⟶
              (CategoryTheory.ProjectiveSystem.shift (r : ℤ)).obj
                ((LTorsionProjectiveSystem.stalkSystem s).obj F))) ≫
        (CategoryTheory.ProjectiveSystem.toArCategory.{u} ℤ (l : ℤ)).map
          (CategoryTheory.ProjectiveSystem.natMap
            ((LTorsionProjectiveSystem.stalkSystem s).obj F) r))
      (CategoryTheory.ProjectiveSystem.ArCategory.toArCategory_map_comp_natMap_comp_homMk
        (f := stalkSystemShiftHom s f)
        (((LTorsionProjectiveSystem.stalkSystem s).map_comp (kerι f) f).symm.trans
          (by rw [kerι_comp, Functor.map_zero])))) :=
  CategoryTheory.ProjectiveSystem.ArCategory.isLimitKernelForkHomMk
    (f := stalkSystemShiftHom s f) (isLimitStalkSystemKer s f)

/-- The A–R cokernel of `[r, f]_s = [r, f_s]` given by the stalk system of the cokernel of
`f`. -/
private def isColimitStalkSystemCokernelCofork (s : GeometricPoint S)
    {F G : LTorsionProjectiveSystem.{u} B S hS l} {r : ℕ}
    (f : (shift B S hS l (r : ℤ)).obj F ⟶ G) :
    IsColimit (CokernelCofork.ofπ (f := CategoryTheory.ProjectiveSystem.ArCategory.homMk r
        (stalkSystemShiftHom s f))
      ((CategoryTheory.ProjectiveSystem.toArCategory.{u} ℤ (l : ℤ)).map
        ((LTorsionProjectiveSystem.stalkSystem s).map (cokerπ f)))
      (by
        have h : stalkSystemShiftHom s f ≫
            (LTorsionProjectiveSystem.stalkSystem s).map (cokerπ f) = 0 :=
          ((LTorsionProjectiveSystem.stalkSystem s).map_comp f (cokerπ f)).symm.trans
            (by rw [comp_cokerπ]; exact Functor.map_zero _ _ _)
        rw [CategoryTheory.ProjectiveSystem.ArCategory.homMk_comp_toArCategory_map, h]
        exact CategoryTheory.ProjectiveSystem.ArCategory.homMk_zero r)) :=
  CategoryTheory.ProjectiveSystem.ArCategory.isColimitCokernelCoforkHomMk
    (f := stalkSystemShiftHom s f) (isColimitStalkSystemCoker s f)

/-- **Taking stalk systems is exact on the A–R category** (kernel and cokernel form). For a
geometric point `s`, the functor `[f] ↦ [f]_s` from the A–R category of projective systems of
`l`-torsion sheaves to the A–R category of projective systems of `l`-power torsion `ℤ`-modules
preserves the kernel and the cokernel of every A–R morphism. -/
@[weil "lem_fk112_stalk_functor_exact_ar"]
instance preservesHomology_stalkSystem (s : GeometricPoint S) :
    (stalkSystem (B := B) (hS := hS) (l := l) s).PreservesHomology where
  preservesKernels {X Y} φ := by
    induction φ using hom_induction with
    | h r f =>
      refine preservesLimit_of_preserves_limit_cone (isLimitKernelForkHomMk (isLimitKer f))
        ((KernelFork.isLimitMapConeEquiv _ _).2 ?_)
      refine isLimitKernelForkOfEq (stalkSystem_map_homMk s r f) ?_
        (w := by rw [← Functor.map_comp, KernelFork.condition, Functor.map_zero])
        (isLimitStalkSystemKernelFork s f)
      exact stalkSystem_map_toAr_map_comp_shiftιIso_hom s (kerι f)
  preservesCokernels {X Y} φ := by
    induction φ using hom_induction with
    | h r f =>
      refine preservesColimit_of_preserves_colimit_cocone
        (isColimitCokernelCoforkHomMk (isColimitCoker f))
        ((CokernelCofork.isColimitMapCoconeEquiv _ _).2 ?_)
      exact isColimitCokernelCoforkOfEq (stalkSystem_map_homMk s r f)
        (stalkSystem_map_toAr_map s (cokerπ f))
        (w := ((stalkSystem s).map_comp (homMk r f) ((toAr B S hS l).map (cokerπ f))).symm.trans
          ((congrArg (stalkSystem s).map (homMk_comp_toAr_map_cokerπ f)).trans
            (Functor.map_zero _ _ _)))
        (isColimitStalkSystemCokernelCofork s f)

/-- **Taking stalk systems is exact on the A–R category.** For a geometric point `s`, the
functor `[f] ↦ [f]_s` sends exact short complexes of the A–R category of projective systems of
`l`-torsion sheaves to exact short complexes of the A–R category of projective systems of
`l`-power torsion `ℤ`-modules. -/
@[weil "lem_fk112_stalk_functor_exact_ar"]
theorem exact_map_stalkSystem (s : GeometricPoint S)
    {T : ShortComplex (ArLTorsionProjectiveSystem.{u} B S hS l)} (hT : T.Exact) :
    (T.map (stalkSystem s)).Exact :=
  hT.map (stalkSystem s)

end ArLTorsionProjectiveSystem

end AlgebraicGeometry.SmallEtale
