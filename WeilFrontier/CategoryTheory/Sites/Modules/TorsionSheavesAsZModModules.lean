module

public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheafCategory
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import Mathlib.Algebra.Module.ZMod
public import Weil.Attr

/-!
# The `n`-torsion of an injective torsion sheaf is an injective sheaf of `ℤ/nℤ`-modules

Let `J` be a Grothendieck topology and `n` a natural number. An abelian sheaf all of whose
sections are annihilated by `n` is the same thing as a sheaf of `ℤ/nℤ`-modules: the sectionwise
`ℤ/nℤ`-module structures are compatible with every additive map, so restriction maps and
morphisms of abelian sheaves are automatically `ℤ/nℤ`-linear. In particular the forgetful functor
from sheaves of `ℤ/nℤ`-modules to abelian sheaves is fully faithful and preserves monomorphisms.

For an abelian sheaf `I`, the kernel `I_n` of multiplication by `n` on `I` is annihilated by `n`,
hence is a sheaf of `ℤ/nℤ`-modules. If `I` is injective in a full subcategory of abelian sheaves
containing every sheaf annihilated by `n` (for instance the torsion sheaves, when `n ≥ 1`), then
`I_n` is injective as a sheaf of `ℤ/nℤ`-modules: a morphism from a sheaf of `ℤ/nℤ`-modules to `I`
factors uniquely through `I_n`, so extending along a monomorphism of sheaves of `ℤ/nℤ`-modules is
extending along a monomorphism in the subcategory.

## Main definitions

* `CategoryTheory.Sheaf.zmodModuleOfNsmulEqZero`: an abelian sheaf annihilated by `n`, as a sheaf
  of `ℤ/nℤ`-modules.
* `CategoryTheory.Sheaf.nTorsion`: the kernel `I_n` of multiplication by `n` on an abelian sheaf,
  as a sheaf of `ℤ/nℤ`-modules.

## Main results

* `CategoryTheory.Sheaf.injective_nTorsion`: if `I` is injective in a full subcategory of abelian
  sheaves containing all sheaves annihilated by `n`, then `I_n` is an injective sheaf of
  `ℤ/nℤ`-modules.
* `AlgebraicGeometry.SmallEtale.TorsionSheafCategory.injective_nTorsion`: for `n ≥ 1` and an
  injective object `I` of the category `𝒯(S)` of torsion sheaves on the small étale site of `S`,
  the kernel of `n : I → I` is an injective sheaf of `ℤ/nℤ`-modules on the small étale site.

## Implementation notes

The category of sheaves of `ℤ/nℤ`-modules is `Sheaf J (ModuleCat (ZMod n))`, in the same
universe as the abelian sheaves; its forgetful functor to abelian sheaves is `sheafCompose J`
applied to `forget₂ (ModuleCat (ZMod n)) AddCommGrpCat`. Preservation of monomorphisms by this
functor is proved directly: the kernel of the underlying map of abelian sheaves is annihilated
by `n`, hence comes from a sheaf of `ℤ/nℤ`-modules, through which the original monomorphism
detects that it vanishes.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

/-- An abelian presheaf all of whose sections are annihilated by `n`, as a presheaf of
`ℤ/nℤ`-modules. -/
def zmodModulePresheafOfNsmulEqZero (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hF : ∀ (X : Cᵒᵖ) (x : F.obj X), n • x = 0) : Cᵒᵖ ⥤ ModuleCat.{w} (ZMod n) where
  obj X :=
    letI := AddCommGroup.zmodModule (hF X)
    ModuleCat.of (ZMod n) (F.obj X)
  map {X Y} f :=
    letI := AddCommGroup.zmodModule (hF X)
    letI := AddCommGroup.zmodModule (hF Y)
    ModuleCat.ofHom ((F.map f).hom.toZModLinearMap n)
  map_id X := by
    let := AddCommGroup.zmodModule (hF X)
    exact ModuleCat.hom_ext (LinearMap.ext fun x => congrArg (fun g => g.hom x) (F.map_id X))
  map_comp {X Y Z} f g := by
    let := AddCommGroup.zmodModule (hF X)
    let := AddCommGroup.zmodModule (hF Z)
    exact ModuleCat.hom_ext (LinearMap.ext fun x =>
      congrArg (fun h => h.hom x) (F.map_comp f g))

/-- The underlying abelian presheaf of `zmodModulePresheafOfNsmulEqZero n F hF` is `F`. -/
theorem zmodModulePresheafOfNsmulEqZero_comp_forget₂ (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hF : ∀ (X : Cᵒᵖ) (x : F.obj X), n • x = 0) :
    zmodModulePresheafOfNsmulEqZero n F hF ⋙ forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat = F :=
  rfl

/-- **An abelian sheaf all of whose sections are annihilated by `n`, as a sheaf of
`ℤ/nℤ`-modules.** -/
def zmodModuleOfNsmulEqZero (F : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ (X : Cᵒᵖ) (x : F.obj.obj X), n • x = 0) : Sheaf J (ModuleCat.{w} (ZMod n)) :=
  ⟨zmodModulePresheafOfNsmulEqZero n F.obj hF,
    Presheaf.isSheaf_of_isSheaf_comp J _ (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat) F.2⟩

/-- The sections of the underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules are annihilated
by `n`. -/
theorem nsmul_obj_obj_eq_zero {J} (M : Sheaf J (ModuleCat.{w} (ZMod n))) (X : Cᵒᵖ)
    (x : M.obj.obj X) : n • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]

/-- The forgetful functor from sheaves of `ℤ/nℤ`-modules to abelian sheaves. -/
abbrev zmodForget : Sheaf J (ModuleCat.{w} (ZMod n)) ⥤ Sheaf J AddCommGrpCat.{w} :=
  sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})

/-- The underlying abelian sheaf of `zmodModuleOfNsmulEqZero J n F hF` is `F`. -/
def zmodForgetObjZmodModuleOfNsmulEqZeroIso (F : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ (X : Cᵒᵖ) (x : F.obj.obj X), n • x = 0) :
    (zmodForget J n).obj (zmodModuleOfNsmulEqZero J n F hF) ≅ F :=
  Iso.refl _

/-- Every morphism between the underlying abelian sheaves of two sheaves of `ℤ/nℤ`-modules is
`ℤ/nℤ`-linear: the forgetful functor is full. -/
instance zmodForget_full : (zmodForget J n).Full where
  map_surjective {M N} φ :=
    ⟨ObjectProperty.homMk
      { app X := ModuleCat.ofHom
          (AddMonoidHom.toZModLinearMap n (M := M.obj.obj X) (M₁ := N.obj.obj X) (φ.hom.app X).hom)
        naturality X Y f := by
          ext x
          exact congrArg (fun g => g.hom x) (φ.hom.naturality f) },
      rfl⟩

/-- The forgetful functor from sheaves of `ℤ/nℤ`-modules to abelian sheaves is faithful. -/
instance zmodForget_faithful : (zmodForget J n).Faithful where
  map_injective {M N} f g h := by
    ext X x
    exact congrArg (fun φ : (zmodForget J n).obj M ⟶ (zmodForget J n).obj N => φ.hom.app X x) h

variable [HasSheafify J AddCommGrpCat.{w}]

attribute [local instance] CategoryTheory.sheafIsAbelian

omit [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] in
/-- A subsheaf of an abelian sheaf annihilated by `n` is annihilated by `n`. -/
theorem nsmul_eq_zero_of_mono {K F : Sheaf J AddCommGrpCat.{w}} (k : K ⟶ F) [Mono k]
    (hF : ∀ (X : Cᵒᵖ) (x : F.obj.obj X), n • x = 0) (X : Cᵒᵖ) (x : K.obj.obj X) :
    n • x = 0 := by
  have hF' : (n : ℤ) • 𝟙 F = 0 :=
    (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff F n).2 fun X x => by
      rw [natCast_zsmul]; exact hF X x
  have hK : (n : ℤ) • 𝟙 K = 0 := by
    rw [← cancel_mono k, zero_comp, Preadditive.zsmul_comp, Category.id_comp,
      ← Category.comp_id k, ← Preadditive.comp_zsmul, hF', comp_zero]
  have := (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff K n).1 hK X x
  rwa [natCast_zsmul] at this

/-- The forgetful functor from sheaves of `ℤ/nℤ`-modules to abelian sheaves preserves
monomorphisms. -/
theorem mono_zmodForget_map {M N : Sheaf J (ModuleCat.{w} (ZMod n))} (g : M ⟶ N) [Mono g] :
    Mono ((zmodForget J n).map g) := by
  apply Preadditive.mono_of_kernel_zero
  set k := kernel.ι ((zmodForget J n).map g)
  have hK := nsmul_eq_zero_of_mono J n k (nsmul_obj_obj_eq_zero n M)
  let e := zmodForgetObjZmodModuleOfNsmulEqZeroIso J n _ hK
  let k' : zmodModuleOfNsmulEqZero J n _ hK ⟶ M := (zmodForget J n).preimage (e.hom ≫ k)
  have hk : (zmodForget J n).map k' = e.hom ≫ k := Functor.map_preimage _ _
  have hk' : k' = 0 := by
    rw [← cancel_mono g, zero_comp]
    apply (zmodForget J n).map_injective
    rw [Functor.map_comp, hk, Functor.map_zero, Category.assoc, kernel.condition, comp_zero]
  have : k = e.inv ≫ (zmodForget J n).map k' := by rw [hk, e.inv_hom_id_assoc]
  rw [this, hk', Functor.map_zero, comp_zero]

omit [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})] in
/-- The kernel of multiplication by `n` on an abelian sheaf is annihilated by `n`. -/
theorem nsmul_kernel_nsmul_id_eq_zero (I : Sheaf J AddCommGrpCat.{w}) (X : Cᵒᵖ)
    (x : (kernel (n • 𝟙 I)).obj.obj X) : n • x = 0 := by
  have h : (n : ℤ) • 𝟙 (kernel (n • 𝟙 I)) = 0 := by
    rw [← cancel_mono (kernel.ι (n • 𝟙 I)), zero_comp, Preadditive.zsmul_comp, Category.id_comp,
      natCast_zsmul]
    calc n • kernel.ι (n • 𝟙 I) = kernel.ι (n • 𝟙 I) ≫ (n • 𝟙 I) := by
          rw [Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 := kernel.condition _
  have := (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ (n : ℤ)).1 h X x
  rwa [natCast_zsmul] at this

omit [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})] in
/-- **The `n`-torsion `I_n = Ker(n : I → I)` of an abelian sheaf `I`**, as a sheaf of
`ℤ/nℤ`-modules. -/
def nTorsion (I : Sheaf J AddCommGrpCat.{w}) : Sheaf J (ModuleCat.{w} (ZMod n)) :=
  zmodModuleOfNsmulEqZero J n (kernel (n • 𝟙 I)) (nsmul_kernel_nsmul_id_eq_zero J n I)

/-- The underlying abelian sheaf of `nTorsion J n I` is the kernel of `n : I → I`. -/
def zmodForgetObjNTorsionIso (I : Sheaf J AddCommGrpCat.{w}) :
    (zmodForget J n).obj (nTorsion J n I) ≅ kernel (n • 𝟙 I) :=
  Iso.refl _

omit [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]
  [HasSheafify J AddCommGrpCat.{w}] in
/-- An abelian sheaf whose sections are annihilated by `n` has `n • 𝟙 = 0`. -/
theorem nsmul_id_eq_zero {F : Sheaf J AddCommGrpCat.{w}}
    (hF : ∀ (X : Cᵒᵖ) (x : F.obj.obj X), n • x = 0) : n • 𝟙 F = 0 := by
  rw [← natCast_zsmul]
  exact (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff F n).2 fun X x => by
    rw [natCast_zsmul]; exact hF X x

/-- **The `n`-torsion of an injective object is an injective sheaf of `ℤ/nℤ`-modules.** Let `P`
be a property of abelian sheaves satisfied by every abelian sheaf annihilated by `n`, and let `I`
be an injective object of the full subcategory of abelian sheaves satisfying `P`. Then the
kernel `I_n` of `n : I → I` is an injective sheaf of `ℤ/nℤ`-modules. -/
theorem injective_nTorsion (P : ObjectProperty (Sheaf J AddCommGrpCat.{w}))
    (hP : ∀ F : Sheaf J AddCommGrpCat.{w}, (∀ (X : Cᵒᵖ) (x : F.obj.obj X), n • x = 0) → P F)
    (I : P.FullSubcategory) [Injective I] : Injective (nTorsion J n I.obj) where
  factors {G' G} f g _ := by
    let U := zmodForget J n
    have hU : ∀ M, P (U.obj M) := fun M => hP _ (nsmul_obj_obj_eq_zero n M)
    let ι := kernel.ι (n • 𝟙 I.obj)
    let e := zmodForgetObjNTorsionIso J n I.obj
    have hg : Mono (U.map g) := mono_zmodForget_map J n g
    let gP : (⟨U.obj G', hU G'⟩ : P.FullSubcategory) ⟶ ⟨U.obj G, hU G⟩ :=
      P.fullyFaithfulι.preimage (U.map g)
    have : Mono gP := P.ι.mono_of_mono_map (by
      rw [show P.ι.map gP = U.map g from P.fullyFaithfulι.map_preimage _]
      exact hg)
    let fP : (⟨U.obj G', hU G'⟩ : P.FullSubcategory) ⟶ I :=
      P.fullyFaithfulι.preimage (U.map f ≫ e.hom ≫ ι)
    obtain ⟨h, hh⟩ := Injective.factors fP gP
    let h0 : U.obj G ⟶ I.obj := P.ι.map h
    have hh0 : U.map g ≫ h0 = U.map f ≫ e.hom ≫ ι := by
      have := congrArg P.ι.map hh
      rwa [P.ι.map_comp, P.fullyFaithfulι.map_preimage, P.fullyFaithfulι.map_preimage] at this
    have hz : h0 ≫ (n • 𝟙 I.obj) = 0 := by
      rw [Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp h0,
        ← Preadditive.nsmul_comp, nsmul_id_eq_zero J n (nsmul_obj_obj_eq_zero n G), zero_comp]
    refine ⟨U.preimage (kernel.lift _ h0 hz ≫ e.inv), U.map_injective ?_⟩
    rw [U.map_comp, U.map_preimage, ← cancel_mono (e.hom ≫ ι)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [show kernel.lift _ h0 hz ≫ ι = h0 from kernel.lift_ι _ _ _]
    exact hh0

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallEtale.TorsionSheafCategory

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The `n`-torsion of an injective torsion sheaf is an injective sheaf of `ℤ/nℤ`-modules.**
Let `I` be an injective object of the category `𝒯(S)` of torsion sheaves on the small étale site
of `S`, and `n ≥ 1`. Then `I_n = Ker(n : I → I)`, as a sheaf of `ℤ/nℤ`-modules
(`CategoryTheory.Sheaf.nTorsion`), is an injective sheaf of `ℤ/nℤ`-modules. -/
@[weil "lem_fk104_torsion_injective_n_torsion_injective"]
theorem injective_nTorsion {n : ℕ} (hn : 0 < n) (I : TorsionSheafCategory B S hS)
    [Injective I] : Injective (Sheaf.nTorsion (topology B S hS) n I.obj) :=
  Sheaf.injective_nTorsion _ n _
    (fun _ hF U _ => ⟨⊤, (topology B S hS).top_mem U, fun _ _ _ => ⟨n, hn, hF _ _⟩⟩) I

end AlgebraicGeometry.SmallEtale.TorsionSheafCategory
