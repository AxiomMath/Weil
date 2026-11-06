module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import WeilFrontier.Defs.AlgebraicGeometry.Modules.Sheaf
public import Weil.Attr

/-!
# Fpqc descent of homomorphisms of quasi-coherent modules

Let `f : T ⟶ S` be a flat, surjective and quasi-compact morphism of schemes and let `M`, `M'` be
quasi-coherent `𝒪_S`-modules. Then the descent sequence
```
Hom(M, M') ⟶ Hom(f^* M, f^* M') ⇉ Hom(q^* M, q^* M')
```
is exact: `u ↦ f^* u` is injective, and its image consists of the `φ` with `p₁^* φ = p₂^* φ`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.descentSequenceExact_of_flat_of_surjective`: exactness of the
  descent sequence for a faithfully flat quasi-compact morphism.

## Implementation notes

The result is deduced from the sheaf property of the presheaf of morphisms
`(T' ⟶ S) ↦ Hom(T'^* M, T'^* M')` for fpqc covering families
(`AlgebraicGeometry.isSheafFor_presheafHom_fpqc`, the full-faithfulness half of Stacks 023T),
applied to the one-member family `{f}`. Its compatibility condition along a pair of morphisms
`g₁, g₂ : Z ⟶ T` with `g₁ ≫ f = g₂ ≫ f` is reduced to the equality `p₁^* φ = p₂^* φ` by
factoring `(g₁, g₂)` through `T ×_S T`; the pullback maps of the module pseudofunctor are
identified with the maps built from `Scheme.Modules.pullbackComp` by
`AlgebraicGeometry.modulePullbackPseudofunctor_pullHom`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

public section

open CategoryTheory Limits Opposite Pseudofunctor.LocallyDiscreteOpToCat

universe u

namespace CategoryTheory.Pseudofunctor

variable {C : Type*} [Category* C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

/-- Restricting the section of `F.presheafHom M N` over `𝟙 S` attached to `φ : M ⟶ N` to an
object `W` of `Over S` gives the pullback of `φ` along `W.hom`. -/
lemma presheafHom_map_presheafHomObjHomEquiv_eq_map {S : C} {M N : F.obj (.mk (op S))}
    (φ : M ⟶ N) {W : Over S} (g : W ⟶ Over.mk (𝟙 S)) :
    (F.presheafHom M N).map g.op (F.presheafHomObjHomEquiv φ) =
      (F.map W.hom.op.toLoc).toFunctor.map φ := by
  obtain ⟨W, w, rfl⟩ := Over.mk_surjective W
  obtain rfl : g = Over.homMk w := by ext; simpa using Over.w g
  change pullHom (F.presheafHomObjHomEquiv φ) w w w (by simp) (by simp) = _
  rw [pullHom, presheafHomObjHomEquiv_apply]
  simp [F.mapComp'_id_comp_hom_app, F.mapComp'_id_comp_inv_app, ← Functor.map_comp]

/-- The restriction maps of `F.presheafHom M N` are `pullHom`. -/
lemma presheafHom_map_eq_pullHom' {S : C} {M N : F.obj (.mk (op S))} {W W' : Over S}
    (g : W' ⟶ W) (x : (F.presheafHom M N).obj (op W)) :
    (F.presheafHom M N).map g.op x = pullHom x g.left W'.hom W'.hom (Over.w g) (Over.w g) :=
  rfl

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Scheme.Modules

/-- Restricting the morphism of `presheafHom` attached to `u : M ⟶ M'` from `S` to `T` along
`f : T ⟶ S` gives `f^* u`. -/
lemma presheafHom_map_homMk_presheafHomObjHomEquiv {S T : Scheme.{u}} {f : T ⟶ S}
    {M M' : S.Modules} (u : M ⟶ M') (g : Over.mk f ⟶ Over.mk (𝟙 S)) :
    (modulePullbackPseudofunctor.presheafHom M M').map g.op
      (modulePullbackPseudofunctor.presheafHomObjHomEquiv u) = (pullback f).map u := by
  have h := CategoryTheory.Pseudofunctor.presheafHom_map_presheafHomObjHomEquiv_eq_map
    (F := modulePullbackPseudofunctor) u g
  exact h

/-- `pullHom` along equal morphisms. -/
lemma pullHom_eq_of_eq {S T T' : Scheme.{u}} {f₁ f₂ : T ⟶ S} {M M' : S.Modules}
    (φ : (modulePullbackPseudofunctor.map f₁.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map f₂.op.toLoc).toFunctor.obj M')
    {g g' : T' ⟶ T} (e : g = g') {h₁ h₂ : T' ⟶ S} (hh₁ : g ≫ f₁ = h₁) (hh₂ : g ≫ f₂ = h₂) :
    pullHom φ g h₁ h₂ hh₁ hh₂ = pullHom φ g' h₁ h₂ (e ▸ hh₁) (e ▸ hh₂) := by
  subst e
  rfl

/-- If `p₁^* φ = p₂^* φ`, then `φ` has the same pullback along any two morphisms `a, b : Z ⟶ T`
with `a ≫ f = b ≫ f`. -/
lemma pullHom_eq_pullHom_of_comp_eq {S T : Scheme.{u}} {f : T ⟶ S} {M M' : S.Modules}
    (φ : (pullback f).obj M ⟶ (pullback f).obj M')
    (key : pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ
      (pullback.fst f f) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) rfl rfl =
      pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ
      (pullback.snd f f) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f)
      pullback.condition.symm pullback.condition.symm)
    {Z : Scheme.{u}} (a b : Z ⟶ T) (z : Z ⟶ S) (ha : a ≫ f = z) (hb : b ≫ f = z) :
    pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ a z z ha ha =
      pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ b z z hb hb := by
  have hl : a = pullback.lift a b (ha.trans hb.symm) ≫ pullback.fst f f :=
    (pullback.lift_fst _ _ _).symm
  have hr : b = pullback.lift a b (ha.trans hb.symm) ≫ pullback.snd f f :=
    (pullback.lift_snd _ _ _).symm
  rw [pullHom_eq_of_eq φ hl, pullHom_eq_of_eq φ hr,
    ← pullHom_pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ
      (pullback.fst f f) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f)
      (pullback.lift a b (ha.trans hb.symm)) z z rfl rfl
      (by rw [pullback.lift_fst_assoc, ha]) (by rw [pullback.lift_fst_assoc, ha]),
    ← pullHom_pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ
      (pullback.snd f f) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f)
      (pullback.lift a b (ha.trans hb.symm)) z z
      pullback.condition.symm pullback.condition.symm
      (by rw [pullback.lift_fst_assoc, ha]) (by rw [pullback.lift_fst_assoc, ha]), key]

/-- **Fpqc descent of homomorphisms of quasi-coherent modules.** For a flat, surjective and
quasi-compact morphism `f : T ⟶ S` and quasi-coherent `𝒪_S`-modules `M`, `M'`, the descent
sequence `Hom(M, M') ⟶ Hom(f^* M, f^* M') ⇉ Hom(q^* M, q^* M')` is exact. -/
@[weil "lem_fka3_fpqc_descent_module_homs"]
theorem descentSequenceExact_of_flat_of_surjective {S T : Scheme.{u}} (f : T ⟶ S) [Flat f]
    [Surjective f] [QuasiCompact f] (M M' : S.Modules) [M.IsQuasicoherent]
    [M'.IsQuasicoherent] :
    DescentSequenceExact f M M' := by
  have hf : Presieve.ofArrows (fun _ : PUnit.{u + 1} ↦ T) (fun _ ↦ f) ∈
      Scheme.fpqcPrecoverage.{u} S := by
    rw [Presieve.ofArrows_pUnit]
    exact f.singleton_mem_fpqcPrecoverage
  have hs := isSheafFor_presheafHom_fpqc M M' (fun _ : PUnit.{u + 1} ↦ f) hf
  rw [overPresieve, Presieve.isSheafFor_arrows_iff] at hs
  rw [descentSequenceExact_iff_existsUnique]
  intro φ hφ
  have key : pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ
      (pullback.fst f f) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) rfl rfl =
      pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ
      (pullback.snd f f) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f)
      pullback.condition.symm pullback.condition.symm := by
    have e₁ : pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ
        (pullback.fst f f) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f) rfl rfl =
        descentHomFst f φ := by
      rw [modulePullbackPseudofunctor_pullHom]
      simp [descentHomFst, pullbackCongr]
      rfl
    have e₂ : pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M') φ
        (pullback.snd f f) (pullback.fst f f ≫ f) (pullback.fst f f ≫ f)
        pullback.condition.symm pullback.condition.symm = descentHomSnd f φ := by
      rw [modulePullbackPseudofunctor_pullHom]
      simp [descentHomSnd, pullbackCongr]
      rfl
    exact e₁.trans (hφ.trans e₂.symm)
  have hc : Presieve.Arrows.Compatible (modulePullbackPseudofunctor.presheafHom M M')
      (fun _ : PUnit.{u + 1} ↦ (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 S)))
      (fun _ ↦ φ) := by
    intro i j Z gi gj _
    have hi : gi.left ≫ f = Z.hom := Over.w gi
    have hj : gj.left ≫ f = Z.hom := Over.w gj
    exact (CategoryTheory.Pseudofunctor.presheafHom_map_eq_pullHom'
      (F := modulePullbackPseudofunctor) (M := M) (N := M') gi φ).trans
      ((pullHom_eq_pullHom_of_comp_eq φ key gi.left gj.left Z.hom hi hj).trans
        (CategoryTheory.Pseudofunctor.presheafHom_map_eq_pullHom'
          (F := modulePullbackPseudofunctor) (M := M) (N := M') gj φ).symm)
  obtain ⟨t, ht, htu⟩ := hs (fun _ ↦ φ) hc
  refine ⟨(modulePullbackPseudofunctor.presheafHomObjHomEquiv).symm t, ?_, ?_⟩
  · have h := presheafHom_map_homMk_presheafHomObjHomEquiv
      (modulePullbackPseudofunctor.presheafHomObjHomEquiv.symm t)
      (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 S))
    rw [Equiv.apply_symm_apply] at h
    exact h.symm.trans (ht PUnit.unit)
  · intro v hv
    apply modulePullbackPseudofunctor.presheafHomObjHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply htu
    intro _
    exact (presheafHom_map_homMk_presheafHomObjHomEquiv v _).trans hv

end AlgebraicGeometry.Scheme.Modules
