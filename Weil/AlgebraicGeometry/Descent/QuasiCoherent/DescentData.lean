module

public import Weil.Defs.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import Weil.Defs.AlgebraicGeometry.Modules.Sheaf

/-!
# Morphisms of canonical descent data and the descent sequence

Let `f : T ⟶ S` be a morphism of schemes, `M`, `M'` quasi-coherent `𝒪_S`-modules and
`φ : f^* M ⟶ f^* M'` a morphism of `𝒪_T`-modules. Write `p₁, p₂ : T ×_S T ⟶ T` for the
projections, `c_{k, M} : p_k^* f^* M ≅ q^* M` for the composite pullback isomorphisms and
`σ_M = c_{2,M}⁻¹ ∘ c_{1,M}` for the canonical descent datum. Then `φ` is compatible with the
canonical descent data, `σ_{M'} ∘ p₁^* φ = p₂^* φ ∘ σ_M`, if and only if
`c_{1,M'} ∘ p₁^* φ ∘ c_{1,M}⁻¹ = c_{2,M'} ∘ p₂^* φ ∘ c_{2,M}⁻¹`, that is, if and only if the two
parallel maps of the descent sequence agree on `φ`.

## Main results

* `AlgebraicGeometry.modulePullbackPseudofunctor_mapComp'_hom_toNatTrans`: the composition
  isomorphisms of the pullback pseudofunctor are `Scheme.Modules.pullbackComp`, up to
  `Scheme.Modules.pullbackCongr`.
* `AlgebraicGeometry.canonicalDescentIso_hom_eq`: `σ_M` written with the composite pullback
  isomorphisms `Scheme.Modules.pullbackComp` of the descent sequence.
* `AlgebraicGeometry.map_comp_canonicalDescentIso_hom_iff`: compatibility of `φ` with the
  canonical descent data is equivalent to `descentHomFst f φ = descentHomSnd f φ`.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe u

namespace AlgebraicGeometry

variable {T S : Scheme.{u}} (f : T ⟶ S)

/-- The composition isomorphisms of `modulePullbackPseudofunctor` are those of
`Scheme.Modules.pullbackComp`, up to `Scheme.Modules.pullbackCongr`. -/
lemma modulePullbackPseudofunctor_mapComp'_hom_toNatTrans {T' : Scheme.{u}} (f : T ⟶ S)
    (g : T' ⟶ T) (h : T' ⟶ S) (hh : g ≫ f = h) :
    (modulePullbackPseudofunctor.mapComp' f.op.toLoc g.op.toLoc h.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hh])).hom.toNatTrans =
      (Scheme.Modules.pullbackCongr hh).inv ≫ (Scheme.Modules.pullbackComp g f).inv := by
  subst hh
  change (modulePullbackPseudofunctor.mapComp' f.op.toLoc g.op.toLoc
    (f.op.toLoc ≫ g.op.toLoc) rfl).hom.toNatTrans = _
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  simp [modulePullbackPseudofunctor, Scheme.Modules.pullbackCongr, Bicategory.Adj.forget₁]
  rfl

variable (M M' : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)

/-- `σ_M = c_{2,M}⁻¹ ∘ c_{1,M}`, with `c_{1,M} = (Scheme.Modules.pullbackComp p₁ f).app M` and
`c_{2,M} = (Scheme.Modules.pullbackComp p₂ f).app M` followed by the identification
`(p₂ ≫ f)^* = (p₁ ≫ f)^*`: the isomorphisms of the descent sequence. -/
lemma canonicalDescentIso_hom_eq :
    (canonicalDescentIso f M).hom =
      (Scheme.Modules.pullbackComp (pullback.fst f f) f).hom.app M.obj ≫
        (Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f)).symm).inv.app
          M.obj ≫
          (Scheme.Modules.pullbackComp (pullback.snd f f) f).inv.app M.obj := by
  have h₁ := modulePullbackPseudofunctor_mapComp'_hom_toNatTrans f (pullback.fst f f)
    (pullback.fst f f ≫ f) rfl
  have h₂ := modulePullbackPseudofunctor_mapComp'_hom_toNatTrans f (pullback.snd f f)
    (pullback.fst f f ≫ f) pullback.condition.symm
  have i₁ : Cat.Hom.toNatIso (modulePullbackPseudofunctor.mapComp' f.op.toLoc
      (pullback.fst f f).op.toLoc (pullback.fst f f ≫ f).op.toLoc rfl) =
      (Scheme.Modules.pullbackCongr (rfl : pullback.fst f f ≫ f = _)).symm ≪≫
        (Scheme.Modules.pullbackComp (pullback.fst f f) f).symm :=
    Iso.ext h₁
  have i₂ : Cat.Hom.toNatIso (modulePullbackPseudofunctor.mapComp' f.op.toLoc
      (pullback.snd f f).op.toLoc (pullback.fst f f ≫ f).op.toLoc
      (by rw [pullback.condition]; rfl)) =
      (Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f)).symm).symm ≪≫
        (Scheme.Modules.pullbackComp (pullback.snd f f) f).symm :=
    Iso.ext h₂
  rw [canonicalDescentIso, i₁, i₂]
  simp [Scheme.Modules.pullbackCongr]
  rfl

/-- Conjugation identity behind `map_comp_canonicalDescentIso_hom_iff`: for isomorphisms
`A, A', B, B'`, `a ≫ A' ≫ B' = A ≫ B ≫ b` if and only if `A⁻¹ ≫ a ≫ A' = B ≫ b ≫ B'⁻¹`. -/
private lemma comp_hom_comp_hom_eq_iff {C : Type*} [Category C] {X Y Z W P Q : C}
    (a : X ⟶ Y) (b : Z ⟶ W) (A : X ≅ P) (A' : Y ≅ Q) (B : P ≅ Z) (B' : Q ≅ W) :
    a ≫ A'.hom ≫ B'.hom = A.hom ≫ B.hom ≫ b ↔ A.inv ≫ a ≫ A'.hom = B.hom ≫ b ≫ B'.inv := by
  rw [Iso.inv_comp_eq]
  simp only [← Category.assoc]
  rw [Iso.eq_comp_inv]

/-- **Morphisms of canonical descent data.** An `𝒪_T`-linear map `φ : f^* M ⟶ f^* M'` is
compatible with the canonical descent data, `σ_{M'} ∘ p₁^* φ = p₂^* φ ∘ σ_M`, if and only if
`c_{1,M'} ∘ p₁^* φ ∘ c_{1,M}⁻¹ = c_{2,M'} ∘ p₂^* φ ∘ c_{2,M}⁻¹`, i.e. the two parallel maps
`Scheme.Modules.descentHomFst f` and `Scheme.Modules.descentHomSnd f` of the descent sequence
agree on `φ`. -/
@[weil "lem_fka3_descent_datum_morphism_iff_equalizer"]
theorem map_comp_canonicalDescentIso_hom_iff
    (φ : (Scheme.Modules.pullback f).obj M.obj ⟶ (Scheme.Modules.pullback f).obj M'.obj) :
    (Scheme.Modules.pullback (pullback.fst f f)).map φ ≫ (canonicalDescentIso f M').hom =
        (canonicalDescentIso f M).hom ≫ (Scheme.Modules.pullback (pullback.snd f f)).map φ ↔
      Scheme.Modules.descentHomFst f φ = Scheme.Modules.descentHomSnd f φ := by
  rw [canonicalDescentIso_hom_eq, canonicalDescentIso_hom_eq]
  exact comp_hom_comp_hom_eq_iff _ _
    ((Scheme.Modules.pullbackComp (pullback.fst f f) f).app M.obj)
    ((Scheme.Modules.pullbackComp (pullback.fst f f) f).app M'.obj)
    ((Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f)).symm).symm.app M.obj ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd f f) f).symm.app M.obj)
    ((Scheme.Modules.pullbackCongr (pullback.condition (f := f) (g := f)).symm).symm.app M'.obj ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd f f) f).symm.app M'.obj)

end AlgebraicGeometry
