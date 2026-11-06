module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonColimits
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonFinite
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonProjectiveLine
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonProperBaseChange
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.FiberProduct
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.InjectiveTorsionAcyclic
public import WeilFrontier.CategoryTheory.Abelian.EffaceableComparisonDegreeZero
public import WeilFrontier.Topology.Sheaves.Cohomology.ProperBaseChangeAbelian

/-!
# The comparison theorem for powers of the projective line

Let `c^ν(X, F) : H^ν_et(X, F) → H^ν(X(ℂ), F_an)` be the comparison map of a scheme `X` locally
of finite type over `ℂ`, and `PC(X)` the statement that it is bijective for every torsion
abelian sheaf `F` on `X_et` and every `ν`. This file proves `PC((ℙ¹_ℂ)^k)` for every `k`.

The proof is by induction on `k`. For `k = 0` the scheme is `Spec ℂ`. For the step, let
`p : X = ℙ¹ ×_ℂ S → S = (ℙ¹)^k` be the projection, which is proper with fibres `ℙ¹_ℂ` over the
complex points, so that the fibres satisfy `PC` by the comparison theorem for `ℙ¹`. It suffices
(filtered colimits) to treat sheaves killed by some `n ≥ 1`, and (effaceability) to prove that
`c^•(X, G)` is bijective for the underlying abelian sheaf `G` of an injective sheaf of
`ℤ/n`-modules, into which every sheaf killed by `n` embeds. For such `G`:
* in degree `0`, `c^0(X, G)` is identified with `c^0(S, p_* G)` through the adjunctions
  `p^* ⊣ p_*`, `p_an^* ⊣ p_an,*` and the base change isomorphism `ε^* p_* G ≅ p_an,* ε^* G`;
* in degree `q > 0`, `H^q_et(X, G) = 0` (`G` is acyclic), and
  `H^q(X(ℂ), ε^* G) ≅ H^q(S(ℂ), p_an,* ε^* G)` (the higher direct images of `ε^* G` vanish
  because those of `G` do, by proper base change on both sides), which is
  `H^q(S(ℂ), ε^* p_* G) ≅ H^q_et(S, p_* G) = 0` by `PC(S)` and acyclicity of `p_* G`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_zero_pushforward_bijective_iff`: for
  `f : X' ⟶ X` over `ℂ` and an étale sheaf `G` on `X'` whose base change map is an isomorphism,
  `c^0(X, f_* G)` is bijective if and only if `c^0(X', G)` is.
* `AlgebraicGeometry.Scheme.ComplexPoints.pc_of_pc_of_isIso_pushforwardBaseChange`: `PC(S)`
  implies `PC(X)` for `p : X ⟶ S` over `ℂ`, `X` proper with compact complex points, when the
  base change map of `p` is an isomorphism on torsion sheaves and the vanishing of `R^q p_* G`
  implies that of `R^q p_an,* ε^* G`.
* `AlgebraicGeometry.Scheme.ComplexPoints.pc_fibre_linePower`: the fibres of
  `(ℙ¹)^{k+1} → (ℙ¹)^k` over complex points satisfy `PC`.
* `AlgebraicGeometry.Scheme.ComplexPoints.pc_linePower`: `PC((ℙ¹_ℂ)^k)` for every `k`.

## References

* [SGA4, Exposé XVI, Théorème 4.1]
* [Freitag–Kiehl, *Étale cohomology and the Weil conjecture*, Ch. I, §11]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

universe w w'

namespace CategoryTheory.Functor

variable {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ]
  (ε : 𝒜 ⥤ ℬ) [ε.Additive] [PreservesFiniteLimits ε] [PreservesFiniteColimits ε]
  [HasExt.{w} 𝒜] [HasExt.{w'} ℬ]

/-- In degree `0`, an exact functor is bijective on `Ext` exactly when it is bijective on
morphisms. -/
theorem mapExtAddHom_zero_bijective_iff (A F : 𝒜) :
    Function.Bijective (ε.mapExtAddHom.{w, w'} A F 0) ↔
      Function.Bijective (fun g : A ⟶ F => ε.map g) := by
  have key : (ε.mapExtAddHom.{w, w'} A F 0) ∘ (Ext.homEquiv₀.{w}).symm =
      (Ext.homEquiv₀.{w'}).symm ∘ (fun g : A ⟶ F => ε.map g) := by
    funext g
    simp [Ext.homEquiv₀, Ext.mapExactFunctor_mk₀]
  constructor
  · intro h
    have := h.comp (Ext.homEquiv₀.{w}).symm.bijective
    rw [key] at this
    exact (Function.Bijective.of_comp_iff' (Ext.homEquiv₀.{w'}).symm.bijective _).1 this
  · intro h
    have := (Ext.homEquiv₀.{w'}).symm.bijective.comp h
    rw [← key] at this
    exact (Function.Bijective.of_comp_iff _ (Ext.homEquiv₀.{w}).symm.bijective).1 this

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.ComplexPoints

open Stacks.EtaleCohomology

variable {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ))
  [LocallyOfFiniteType x] [LocallyOfFiniteType x'] (f : X' ⟶ X) (hf : f ≫ x = x')

/-- **The degree-zero comparison map along a direct image.** If the base change map
`ε^* f_* G ⟶ f_an,* ε'^* G` is an isomorphism, then `c^0(X, f_* G)` is bijective if and only if
`c^0(X', G)` is: both are identified through the adjunctions `f^* ⊣ f_*` and
`f_an^* ⊣ f_an,*`. No exactness of `f_*` is needed in degree `0`. -/
theorem comparisonMap_zero_pushforward_bijective_iff (G : EtSheaf X')
    [IsIso ((pushforwardBaseChange x x' f hf).app G)] :
    Function.Bijective (comparisonMap x ((smallEtalePushforwardAb f).obj G) 0) ↔
      Function.Bijective (comparisonMap x' G 0) := by
  let A : EtSheaf X := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let a := etaleInverseImageAdjunction f
  let b := analyticPullbackAdjunction x x' f hf
  let γ := inverseImageIso x x' f hf
  let β : smallEtalePushforwardAb f ⋙ analyticInverseImage x ⟶
      analyticInverseImage x' ⋙ analyticPushforward x x' f hf := pushforwardBaseChange x x' f hf
  have : IsIso (β.app G) := ‹_›
  rw [comparisonMap, Functor.mapExtOfIso_bijective_iff, comparisonMap,
    Functor.mapExtOfIso_bijective_iff,
    Functor.mapExtAddHom_bijective_iff_of_iso (analyticInverseImage x')
      (((etaleAbelianInverseImageConstantIso.{0, 0} f).app (AddCommGrpCat.of (ULift ℤ))).symm),
    Functor.mapExtAddHom_zero_bijective_iff, Functor.mapExtAddHom_zero_bijective_iff]
  change Function.Bijective (fun g : A ⟶ (smallEtalePushforwardAb f).obj G =>
      (analyticInverseImage x).map g) ↔
    Function.Bijective (fun g : (etaleAbelianInverseImage.{0, 0} f).obj A ⟶ G =>
      (analyticInverseImage x').map g)
  have key : (fun w => w ≫ β.app G) ∘ (fun g : A ⟶ (smallEtalePushforwardAb f).obj G =>
      (analyticInverseImage x).map g) ∘ (a.homEquiv A G) =
      (b.homEquiv _ _) ∘ (fun w => γ.inv.app A ≫ w) ∘
        (fun g : (etaleAbelianInverseImage.{0, 0} f).obj A ⟶ G =>
          (analyticInverseImage x').map g) := by
    funext z
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    have h1 := β.naturality z
    simp only [Functor.comp_map] at h1
    rw [h1, ← Category.assoc, map_unit_comp_pushforwardBaseChange_app, Category.assoc,
      ← Functor.map_comp]
  have hB : Function.Bijective (fun w : (analyticInverseImage x).obj A ⟶
      (analyticInverseImage x).obj ((smallEtalePushforwardAb f).obj G) => w ≫ β.app G) :=
    Function.bijective_iff_has_inverse.2 ⟨fun w => w ≫ inv (β.app G), fun w => by simp,
      fun w => by simp⟩
  have hT : Function.Bijective (fun w : (analyticInverseImage x').obj
      ((etaleAbelianInverseImage.{0, 0} f).obj A) ⟶ (analyticInverseImage x').obj G =>
        γ.inv.app A ≫ w) :=
    Function.bijective_iff_has_inverse.2 ⟨fun w => γ.hom.app A ≫ w, fun w => by simp,
      fun w => by simp⟩
  have hΦ₁ := (a.homEquiv A G).bijective
  have hΦ₂ :=
    (b.homEquiv ((analyticInverseImage x).obj A) ((analyticInverseImage x').obj G)).bijective
  constructor
  · intro h
    have h1 := Eq.mp (congrArg Function.Bijective key) (hB.comp (h.comp hΦ₁))
    exact (Function.Bijective.of_comp_iff' hT _).1 ((Function.Bijective.of_comp_iff' hΦ₂ _).1 h1)
  · intro h
    have h1 := Eq.mpr (congrArg Function.Bijective key) (hΦ₂.comp (hT.comp h))
    exact (Function.Bijective.of_comp_iff _ hΦ₁).1 ((Function.Bijective.of_comp_iff' hB _).1 h1)


section Step

variable {X S : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (s : S ⟶ Spec (.of ℂ))
  [LocallyOfFiniteType s] (p : X ⟶ S) (hp : p ≫ s = x)

/-- A sheaf killed by a positive integer is torsion. -/
private theorem torsionSheafProperty_of_zsmul_id_eq_zero' {Y : Scheme.{0}} {F : EtSheaf Y} {n : ℕ}
    (hn : 0 < n) (hF : (n : ℤ) • 𝟙 F = 0) :
    Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology F :=
  fun U x => ⟨⊤, Y.smallEtaleTopology.top_mem U, fun V g _ => ⟨n, hn, by
    rw [← natCast_zsmul]
    exact (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff F (n : ℤ)).1 hF _ _⟩⟩

/-- The underlying abelian sheaf of a sheaf of `ℤ/n`-modules is killed by `n`. -/
theorem zsmul_id_forget_eq_zero {Y : Scheme.{0}} (n : ℕ)
    (I : EtaleModules.{0, 0} (ZMod n) Y) :
    (n : ℤ) • 𝟙 ((etaleModuleForgetAb.{0, 0} (ZMod n) Y).obj I) = 0 := by
  refine (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff _ _).2 fun U y => ?_
  let y' : ((I.obj.obj U : ModuleCat.{1} (ZMod n)) : Type 1) := y
  change (n : ℤ) • y' = 0
  rw [← Int.cast_smul_eq_zsmul (ZMod n)]
  simp

variable [LocallyOfFiniteType x] in
/-- **The comparison map on injective sheaves of `ℤ/n`-modules.** Let `p : X ⟶ S` be a morphism
over `ℂ` with `PC(S)`, whose base change map is an isomorphism on torsion sheaves and such that
the vanishing of `R^q p_* G` implies that of `R^q p_an,* ε^* G` for torsion `G`. Then
`c^m(X, I)` is bijective for the underlying abelian sheaf of an injective sheaf `I` of
`ℤ/n`-modules, `n ≥ 1`. -/
theorem comparisonMap_forget_injective_bijective (hs : PC s) (n : ℕ) (hn : 0 < n)
    (hβ : ∀ G : EtSheaf X, Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
      IsIso ((pushforwardBaseChange s x p hp).app G))
    (hR : ∀ G : EtSheaf X, Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
      ∀ q : ℕ, 0 < q →
      IsZero (((smallEtalePushforwardAb p).rightDerived q).obj G) →
      IsZero (((Stacks.Topology.pushforwardSheafFunctor (analyticMap s x p hp)).rightDerived q).obj
        ((analyticInverseImage x).obj G)))
    (I : EtaleModules.{0, 0} (ZMod n) X) [Injective I] (m : ℕ) :
    Function.Bijective (comparisonMap x ((etaleModuleForgetAb.{0, 0} (ZMod n) X).obj I) m) := by
  set G := (etaleModuleForgetAb.{0, 0} (ZMod n) X).obj I
  have hGn := zsmul_id_forget_eq_zero n I
  have hG := torsionSheafProperty_of_zsmul_id_eq_zero' hn hGn
  have hpG : (n : ℤ) • 𝟙 ((smallEtalePushforwardAb p).obj G) = 0 := by
    rw [← (smallEtalePushforwardAb p).map_id G, ← Functor.map_zsmul, hGn, Functor.map_zero]
  have hpGt := torsionSheafProperty_of_zsmul_id_eq_zero' hn hpG
  have := hβ G hG
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact (comparisonMap_zero_pushforward_bijective_iff s x p hp G).1 (hs _ hpGt 0)
  · have h1 : Subsingleton (Sheaf.H.{1} G m) := subsingleton_sheafH_forget_injective _ I m hm
    have h2 : Subsingleton (Sheaf.H.{1} ((smallEtalePushforwardAb p).obj G) m) :=
      subsingleton_sheafH_pushforward_forget_injective _ p I m hm
    have h3 : Subsingleton (Sheaf.H.{1} ((analyticInverseImage s).obj
        ((smallEtalePushforwardAb p).obj G)) m) :=
      (hs _ hpGt m).surjective.subsingleton
    have h4 : Subsingleton (Sheaf.H.{1} ((Stacks.Topology.pushforwardSheafFunctor
        (analyticMap s x p hp)).obj ((analyticInverseImage x).obj G)) m) :=
      haveI : Subsingleton (Sheaf.H.{1}
        ((smallEtalePushforwardAb p ⋙ analyticInverseImage s).obj G) m) := h3
      (Sheaf.H.map_bijective_of_isIso ((pushforwardBaseChange s x p hp).app G)
        m).surjective.subsingleton
    have e := TopologicalSpace.ProperBaseChange.sheafHIsoOfIsZeroHigherDirectImage
      (analyticMap s x p hp) ((analyticInverseImage x).obj G)
      (fun q hq => hR G hG q hq (isZero_rightDerived_pushforward_forget_injective _ p I q hq)) m
    have h5 : Subsingleton (Sheaf.H.{1} ((analyticInverseImage x).obj G) m) :=
      (e.addCommGroupIsoToAddEquiv).injective.subsingleton
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **`PC` along a morphism with good base change.** Under the hypotheses of
`comparisonMap_forget_injective_bijective`, with `X` proper over `ℂ` and `X(ℂ)` compact,
`PC(S)` implies `PC(X)`: effaceability by the injective sheaves of `ℤ/n`-modules on sheaves
killed by `n`, then filtered colimits. -/
theorem pc_of_pc_of_isIso_pushforwardBaseChange [IsProper x] [CompactSpace (ComplexPoints x)]
    (hs : PC s)
    (hβ : ∀ G : EtSheaf X, Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
      IsIso ((pushforwardBaseChange s x p hp).app G))
    (hR : ∀ G : EtSheaf X, Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G →
      ∀ q : ℕ, 0 < q →
      IsZero (((smallEtalePushforwardAb p).rightDerived q).obj G) →
      IsZero (((Stacks.Topology.pushforwardSheafFunctor (analyticMap s x p hp)).rightDerived q).obj
        ((analyticInverseImage x).obj G))) :
    PC x :=
  pc_of_boundedTorsion x fun F hF m =>
    (analyticInverseImage x).mapExtOfIso_bijective_of_effaceable'
      ((constantSheafIso x).app (AddCommGrpCat.of (ULift ℤ)))
      (fun F => ∃ n : ℕ, 0 < n ∧ (n : ℤ) • 𝟙 F = 0)
      (fun S hS _ ⟨n, hn, h₂⟩ => ⟨n, hn, by
        have := hS.epi_g
        rw [← cancel_epi S.g, Preadditive.comp_zsmul, Category.comp_id, comp_zero,
          ← Category.id_comp S.g, ← Preadditive.zsmul_comp, h₂, zero_comp]⟩)
      (fun F ⟨n, hn, hF⟩ => by
        obtain ⟨I, hI, i, hi⟩ := exists_mono_forget_injective n F hF
        exact ⟨_, i, hi, ⟨n, hn, zsmul_id_forget_eq_zero n I⟩,
          comparisonMap_forget_injective_bijective x s p hp hs n hn hβ hR I⟩)
      m F hF

end Step

section LinePower

open SymmetricProduct

/-- The fibre of the projection `(ℙ¹)^{k+1} → (ℙ¹)^k` over a complex point is `ℙ¹_ℂ`. -/
noncomputable def linePowerFibreIso (k : ℕ) (t : ComplexPoints (linePower ℂ k).hom) :
    pullback (pullback.snd (lineOver ℂ).hom (linePower ℂ k).hom) t.hom ≅ (lineOver ℂ).left :=
  have : IsIso (t.hom ≫ (linePower ℂ k).hom) := by rw [t.hom_comp]; infer_instance
  pullbackLeftPullbackSndIso _ _ _ ≪≫
    asIso (pullback.fst (lineOver ℂ).hom (t.hom ≫ (linePower ℂ k).hom))

theorem linePowerFibreIso_hom_comp (k : ℕ) (t : ComplexPoints (linePower ℂ k).hom) :
    (linePowerFibreIso k t).hom ≫ (lineOver ℂ).hom =
      pullback.snd (pullback.snd (lineOver ℂ).hom (linePower ℂ k).hom) t.hom := by
  simp only [linePowerFibreIso, Iso.trans_hom, asIso_hom, Category.assoc, pullback.condition,
    pullbackLeftPullbackSndIso_hom_snd, t.hom_comp, Category.comp_id]

theorem pc_fibre_linePower (k : ℕ) (t : ComplexPoints (linePower ℂ k).hom) :
    PC (pullback.snd (pullback.snd (lineOver ℂ).hom (linePower ℂ k).hom) t.hom) :=
  (pc_iff_of_iso _ _ (linePowerFibreIso k t) (linePowerFibreIso_hom_comp k t)).1 pc_line

/-- `PC((ℙ¹)^0)`: the zeroth power of `ℙ¹_ℂ` is `Spec ℂ`. -/
theorem pc_linePower_zero : PC (linePower ℂ 0).hom :=
  fun F _ n => comparisonBijectiveOn_spec F trivial n

/-- **The comparison theorem for powers of the projective line.** For every `k`, every torsion
abelian sheaf `F` on the small étale site of `(ℙ¹_ℂ)^k` and every `n`, the comparison map
`H^n_et((ℙ¹_ℂ)^k, F) → H^n((ℙ¹_ℂ)^k(ℂ), F_an)` is bijective. -/
theorem pc_linePower : ∀ k : ℕ, PC (linePower ℂ k).hom
  | 0 => pc_linePower_zero
  | k + 1 => by
    have := isProper_fiberPower_hom (lineOver ℂ) k
    have := isProper_fiberPower_hom (lineOver ℂ) (k + 1)
    have : CompactSpace (ComplexPoints
        (pullback.snd (lineOver ℂ).hom (linePower ℂ k).hom ≫ (linePower ℂ k).hom)) :=
      compactSpace_linePower (k + 1)
    exact pc_of_pc_of_isIso_pushforwardBaseChange _ _
      (pullback.snd (lineOver ℂ).hom (linePower ℂ k).hom) rfl (pc_linePower k)
      (fun G hG => isIso_pushforwardBaseChange_of_pc_fibres _ _ _ rfl
        (pc_fibre_linePower k) G hG)
      (fun G hG q _ h => isZero_rightDerived_analytic_of_isZero _ _ _ rfl
        (pc_fibre_linePower k) G hG q h)

end LinePower

end AlgebraicGeometry.Scheme.ComplexPoints
