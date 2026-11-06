module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.RestrictionBijectiveBelow
public import Weil.AlgebraicGeometry.EtaleCohomology.CohomologyRestrictionNatural
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.CohomologyRestrictionConnecting
public import Weil.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ShortExactLongExactSequence
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import Weil.Attr

/-!
# Injectivity of restriction in the induction degree

Let `h : Y ⟶ X` be a morphism of schemes of a big étale site, `n` a natural number and `p ≥ 1`.
Assume `B_p`: for every abelian sheaf on the small étale site of `X` killed by `n` and every
`q < p`, the restriction map `h^* : H^q(X, -) → H^q(Y, h^* -)` is bijective. Then for every
abelian sheaf `G` killed by `n`, the restriction map `h^* : H^p(X, G) → H^p(Y, h^* G)` is
injective.

The proof is a diagram chase. A sheaf killed by `n` is a sheaf of `ℤ/n`-modules, which embeds
into an injective sheaf of `ℤ/n`-modules `J`; the quotient `K = J / G` is again killed by `n`,
and the underlying abelian sheaf of `J` has vanishing higher cohomology. In the long exact
sequences of `0 → G → J → K → 0` on `X` and of its inverse image on `Y`, the restriction maps on
`H^{p-1}(J)` and `H^{p-1}(K)` are bijective by `B_p`, and `H^p(X, J) = 0`; this forces the
restriction map on `H^p(G)` to be injective.

## Main results

* `AlgebraicGeometry.CohomologyRestrictionBijectiveBelow.injective`: under `B_p` with `p ≥ 1`,
  restriction is injective in degree `p` on every sheaf killed by `n`.

## Implementation notes

The statement holds for an arbitrary morphism `h` of a big étale site and every `n`: the
strictly henselian setting of the source enters only through the hypothesis `B_p`. Sheaves are
abelian sheaves with values in `AddCommGrpCat.{u + 1}`, as in
`AlgebraicGeometry.CohomologyRestrictionBijectiveBelow`. The vanishing of the higher cohomology
of the underlying abelian sheaf of an injective sheaf of `ℤ/n`-modules is
`Stacks.Cohomology.ModuleSheaf.ext_eq_zero_of_isTorsionFree` applied to the constant sheaf `ℤ`,
whose sections are torsion free.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.1][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian Opposite

universe w u

namespace AlgebraicGeometry

section Instances

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (n : ℕ)

/-- The forgetful functor of `ℤ/n`-modules in `Type (u + 1)` preserves filtered colimits. -/
private theorem preservesFilteredColimits_forget_moduleCat_zmod :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{u + 1} (ZMod n))) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u + 1, u + 1} (ZMod n)
  exact comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})
    (CategoryTheory.forget AddCommGrpCat.{u + 1})

/-- `ℤ/n`-modules in `Type (u + 1)` form a Grothendieck abelian category. -/
private theorem isGrothendieckAbelian_moduleCat_zmod :
    IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} (ZMod n)) := by
  refine { ab5OfSize := ⟨fun D _ _ => ?_⟩ }
  exact HasExactColimitsOfShape.domain_of_functor D
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})

/-- Sheafification of presheaves of `ℤ/n`-modules in `Type (u + 1)` on the small étale site. -/
private theorem hasSheafify_moduleCat_zmod :
    HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ZMod n)) := by
  have := preservesFilteredColimits_forget_moduleCat_zmod.{u} n
  have : EssentiallySmall.{u + 1} (SmallEtale B X.obj X.property) :=
    essentiallySmall_lift.{u + 1, u} _
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} (ZMod n)) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1}
  exact hasSheafifyEssentiallySmallSite.{_, _, _, _, u + 1} _ _

/-- Sheaves of `ℤ/n`-modules in `Type (u + 1)` on the small étale site have enough injectives. -/
private theorem enoughInjectives_sheaf_moduleCat_zmod :
    letI := hasSheafify_moduleCat_zmod.{u} B X n
    EnoughInjectives (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{u + 1} (ZMod n))) := by
  let := hasSheafify_moduleCat_zmod.{u} B X n
  have := preservesFilteredColimits_forget_moduleCat_zmod.{u} n
  have := isGrothendieckAbelian_moduleCat_zmod.{u} n
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} (ZMod n)) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1}
  have : EssentiallySmall.{u + 1} (SmallEtale B X.obj X.property) :=
    essentiallySmall_lift.{u + 1, u} _
  have : IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{u + 1} (ZMod n))) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  exact IsGrothendieckAbelian.enoughInjectives

/-- Abelian sheaves in `Type (u + 1)` on the small étale site have enough injectives. -/
private theorem enoughInjectives_sheaf_addCommGrpCat :
    EnoughInjectives (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) := by
  have : EssentiallySmall.{u + 1} (SmallEtale B X.obj X.property) :=
    essentiallySmall_lift.{u + 1, u} _
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  exact IsGrothendieckAbelian.enoughInjectives

end Instances

section ModuleStructure

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {n : ℕ}

/-- The `ℤ/n`-module structure on the sections of an abelian sheaf killed by `n`. -/
private abbrev zmodModuleOfKilled
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : ∀ (U : SmallEtale B X.obj X.property) (x : G.obj.obj (op U)), n • x = 0)
    (U : (SmallEtale B X.obj X.property)ᵒᵖ) : Module (ZMod n) (G.obj.obj U) :=
  AddCommGroup.zmodModule (hG U.unop)

/-- The presheaf of `ℤ/n`-modules underlying an abelian sheaf all of whose sections are killed
by `n`. -/
private def zmodPresheafOfKilled
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : ∀ (U : SmallEtale B X.obj X.property) (x : G.obj.obj (op U)), n • x = 0) :
    (SmallEtale B X.obj X.property)ᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod n) where
  obj U := @ModuleCat.of (ZMod n) _ (G.obj.obj U) _ (zmodModuleOfKilled G hG U)
  map {U V} f :=
    @ModuleCat.ofHom (ZMod n) _ (G.obj.obj U) (G.obj.obj V) _ (zmodModuleOfKilled G hG U) _
      (zmodModuleOfKilled G hG V)
      (@AddMonoidHom.toZModLinearMap n _ _ _ _ (zmodModuleOfKilled G hG U)
        (zmodModuleOfKilled G hG V) (G.obj.map f).hom)
  map_id U := by
    let := zmodModuleOfKilled G hG U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun g => g.hom x) (G.obj.map_id U)
  map_comp {U V W} f g := by
    let := zmodModuleOfKilled G hG U
    let := zmodModuleOfKilled G hG W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun k => k.hom x) (G.obj.map_comp f g)

/-- Its composite with the forgetful functor is the presheaf of the sheaf. -/
private def zmodPresheafOfKilledCompForgetIso
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : ∀ (U : SmallEtale B X.obj X.property) (x : G.obj.obj (op U)), n • x = 0) :
    zmodPresheafOfKilled G hG ⋙ forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1} ≅
      G.obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by ext; rfl)

/-- The sheaf of `ℤ/n`-modules underlying an abelian sheaf killed by `n`. -/
private def zmodSheafOfKilled
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : ∀ (U : SmallEtale B X.obj X.property) (x : G.obj.obj (op U)), n • x = 0) :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ZMod n)) where
  obj := zmodPresheafOfKilled G hG
  property := by
    have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ZMod n)) :=
      ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1}
    have : ReflectsLimitsOfSize.{u, u + 1}
        (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}) :=
      reflectsLimits_of_reflectsIsomorphisms
    refine Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1}) ?_
    exact (Presheaf.isSheaf_of_iso_iff (zmodPresheafOfKilledCompForgetIso G hG)).2 G.property

/-- The underlying abelian sheaf of `zmodSheafOfKilled G hG` is `G`. -/
private def zmodSheafOfKilledForgetIso
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : ∀ (U : SmallEtale B X.obj X.property) (x : G.obj.obj (op U)), n • x = 0) :
    (sheafCompose (SmallEtale.topology B X.obj X.property)
        (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj
      (zmodSheafOfKilled G hG) ≅ G :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (zmodPresheafOfKilledCompForgetIso G hG)

end ModuleStructure

section Injective

open Stacks.Cohomology.GlobalLongExactSequence

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} {h : Y ⟶ X}
  [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})]

omit [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})] in
/-- The sections of the underlying abelian sheaf of a sheaf of `ℤ/n`-modules are killed by
`n`. -/
private theorem nsmul_eq_zero_forget_zmod {n : ℕ}
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ZMod n)))
    (U : SmallEtale B X.obj X.property)
    (x : ((sheafCompose (SmallEtale.topology B X.obj X.property)
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M).obj.obj (op U)) :
    n • x = 0 := by
  have key : ∀ y : M.obj.obj (op U), n • y = 0 := fun y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  exact key x

/-- The underlying abelian sheaf of an injective sheaf of `ℤ/n`-modules has vanishing cohomology
in positive degrees. -/
private theorem subsingleton_H_forget_of_injective {n : ℕ}
    [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ZMod n))]
    (I : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ZMod n)))
    [Injective I] (q : ℕ) :
    Subsingleton (Sheaf.H.{w} ((sheafCompose (SmallEtale.topology B X.obj X.property)
      (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj I) (q + 1)) := by
  have := enoughInjectives_sheaf_addCommGrpCat.{u} B X
  have hZ : ∀ U, Module.IsTorsionFree ℤ
      (((constantSheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))).obj.obj U) :=
    ModuleSheafCohomology.isTorsionFree_sheafify _ _ (fun _ => by
      change Module.IsTorsionFree ℤ (ULift ℤ)
      exact Module.Flat.isTorsionFree)
  exact ⟨fun a b =>
    (Stacks.Cohomology.ModuleSheaf.ext_eq_zero_of_isTorsionFree _ _ I _ hZ q a).trans
      (Stacks.Cohomology.ModuleSheaf.ext_eq_zero_of_isTorsionFree _ _ I _ hZ q b).symm⟩

/-- **Injectivity of restriction in degree `p` under `B_p`.** Let `h : Y ⟶ X` be a morphism of
a big étale site, `n` a natural number and `p ≥ 1`, and assume `B_p`: restriction is bijective
in every degree `q < p` on every abelian sheaf on the small étale site of `X` killed by `n`.
Then for every abelian sheaf `G` killed by `n`, the restriction map
`h^* : H^p(X, G) → H^p(Y, h^* G)` is injective. -/
@[weil "lem_fk106_hp_restriction_injective_good_sheaf"]
theorem CohomologyRestrictionBijectiveBelow.injective {n p : ℕ}
    (hB : CohomologyRestrictionBijectiveBelow.{w} B h n p) (hp : 1 ≤ p)
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hG : ∀ (U : SmallEtale B X.obj X.property) (x : G.obj.obj (op U)), n • x = 0) :
    Function.Injective (smallEtaleCohomologyRestrictionMap.{w} B h G p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  let := hasSheafify_moduleCat_zmod.{u} B X n
  have := enoughInjectives_sheaf_moduleCat_zmod.{u} B X n
  have := enoughInjectives_sheaf_addCommGrpCat.{u} B X
  let Φ := sheafCompose (SmallEtale.topology B X.obj X.property)
    (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})
  have : PreservesFiniteLimits Φ :=
    Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂.{u + 1, 0, u, u + 1}
      _ _
  have : PreservesFiniteColimits Φ :=
    Stacks.Cohomology.ModuleSheaf.preservesFiniteColimits_sheafCompose_forget₂.{u + 1, 0, u, u + 1}
      _ _
  let G' := zmodSheafOfKilled G hG
  let ι : G' ⟶ Injective.under G' := Injective.ι G'
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
  let T := S.map Φ
  have hT : T.ShortExact := hS.map_of_exact Φ
  let hTY := hT.map_of_exact (smallEtaleInverseImage B h AddCommGrpCat.{u + 1})
  let r := fun (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) k =>
    smallEtaleCohomologyRestrictionMap.{w} B h F k
  -- injectivity on `T.X₁`, the underlying abelian sheaf of `G'`
  have key : Function.Injective (r T.X₁ (q + 1)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hsub := subsingleton_H_forget_of_injective.{w} (Injective.under G') q
    obtain ⟨y, rfl⟩ : x ∈ Set.range (boundary hT q) :=
      (exact_boundary_map hT q x).1 (@Subsingleton.elim _ hsub _ _)
    have h1 : boundary hTY q (r T.X₃ q y) = 0 := by
      rw [← hx]
      exact (smallEtaleCohomologyRestrictionMap_comp_extClass B h hT q (q + 1) rfl y).symm
    obtain ⟨ws, hws⟩ := (exact_map_boundary hTY q _).1 h1
    obtain ⟨w', rfl⟩ := (hB T.X₂ (nsmul_eq_zero_forget_zmod _) q (Nat.lt_succ_self q)).2 ws
    have h2 : r T.X₃ q (Sheaf.H.map T.g q w') = r T.X₃ q y := by
      rw [← hws]
      exact smallEtaleCohomologyRestrictionMap_map B h T.g q w'
    have h3 := (hB T.X₃ (nsmul_eq_zero_forget_zmod _) q (Nat.lt_succ_self q)).1 h2
    rw [← h3]
    exact (exact_map_boundary hT q).apply_apply_eq_zero w'
  -- transport along `T.X₁ ≅ G`
  let e : T.X₁ ≅ G := zmodSheafOfKilledForgetIso G hG
  intro a b hab
  have hinj : Function.Injective (Sheaf.H.map.{w} e.inv (q + 1)) := fun c d hcd => by
    simpa only [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply] using
      congrArg (Sheaf.H.map.{w} e.hom (q + 1)) hcd
  refine hinj (key ?_)
  rw [smallEtaleCohomologyRestrictionMap_map, smallEtaleCohomologyRestrictionMap_map]
  exact congrArg _ hab

end Injective

end AlgebraicGeometry
