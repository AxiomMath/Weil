module

public import Weil.Defs.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import Weil.Defs.AlgebraicGeometry.Descent.QuasiCoherent.DescentDatumSheaf
public import Weil.Attr
public import StacksFrontier.CategoryTheory.Sites.Descent.LocallyRepresentableSheaves

/-!
# Effective descent data on quasi-coherent sheaves

Let `f : T ⟶ S` be a morphism of schemes and `(𝒩, σ)` a descent datum on a quasi-coherent
`𝒪_T`-module with respect to `f`. A *descent* of `(𝒩, σ)` is a quasi-coherent `𝒪_S`-module `ℳ`
together with an `𝒪_T`-linear isomorphism `φ : f^* ℳ ≅ 𝒩` such that
`σ ∘ p₁^* φ = p₂^* φ ∘ σ_ℳ` on `T ×_S T`, where `σ_ℳ` is the canonical descent datum of `f^* ℳ`.
The descent datum is *effective* if it admits a descent.

Effectivity is `AlgebraicGeometry.QuasicoherentDescentData.IsEffective`: the descent datum lies
in the essential image of the canonical descent functor `ℳ ↦ (f^* ℳ, σ_ℳ)`. We show that this
is the existence of a descent in the above sense: an isomorphism of descent data
`(f^* ℳ, σ_ℳ) ≅ (𝒩, σ)` is the same as an isomorphism `φ : f^* ℳ ≅ 𝒩` compatible with the
transition isomorphisms over `T ×_S T` alone, the compatibility over an arbitrary `S`-scheme
with two maps to `T` following by pulling back along the induced map to `T ×_S T`.

## Main definitions

* `AlgebraicGeometry.QuasicoherentDescentDatum.Descent D`: the descents `(ℳ, φ)` of a
  descent datum `D` with respect to a single morphism.
* `AlgebraicGeometry.QuasicoherentDescentDatum.Descent.descentDataIso`: the isomorphism of
  descent data `(f^* ℳ, σ_ℳ) ≅ D` given by a descent.
* `AlgebraicGeometry.QuasicoherentDescentDatum.Descent.ofIso`: the descent given by an
  isomorphism of descent data `(f^* ℳ, σ_ℳ) ≅ D`.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentDatum.isEffective_iff_nonempty_descent`: a descent
  datum is effective if and only if it admits a descent.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Opposite
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

namespace CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type*} [Category* C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

/-- Pulling back along `g : Y' ⟶ Y` preserves the compatibility of morphisms `σ` and `τ` over `Y`
with morphisms `a₁` over `X₁` and `a₂` over `X₂`. -/
lemma map_comp_pullHom_of_comm ⦃X₁ X₂ : C⦄ ⦃M₁ N₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ N₂ : F.obj (.mk (op X₂))⦄ (a₁ : M₁ ⟶ N₁) (a₂ : M₂ ⟶ N₂) ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃f₂ : Y ⟶ X₂⦄
    (σ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (τ : (F.map f₁.op.toLoc).toFunctor.obj N₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj N₂)
    (h : (F.map f₁.op.toLoc).toFunctor.map a₁ ≫ τ = σ ≫ (F.map f₂.op.toLoc).toFunctor.map a₂)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    (F.map gf₁.op.toLoc).toFunctor.map a₁ ≫ pullHom τ g gf₁ gf₂ hgf₁ hgf₂ =
      pullHom σ g gf₁ gf₂ hgf₁ hgf₂ ≫ (F.map gf₂.op.toLoc).toFunctor.map a₂ := by
  dsimp only [pullHom]
  rw [mapComp'_hom_naturality_assoc, ← Functor.map_comp_assoc, h, Functor.map_comp_assoc,
    mapComp'_inv_naturality]
  simp only [Category.assoc]

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

-- `CategoryTheory.Pseudofunctor.DescentData.objIso` is StacksFrontier's
-- (LocallyRepresentableSheaves).

namespace AlgebraicGeometry

namespace QuasicoherentDescentDatum

variable {T S : Scheme.{u}} {f : T ⟶ S}

/-- A descent of a descent datum `D = (𝒩, σ)` with respect to `f : T ⟶ S`: a quasi-coherent
`𝒪_S`-module `ℳ` and an isomorphism `φ : f^* ℳ ≅ 𝒩` with `σ ∘ p₁^* φ = p₂^* φ ∘ σ_ℳ` on
`T ×_S T`, where `σ_ℳ` is the canonical descent datum `canonicalDescentIso f ℳ`. -/
@[weil "def_fka3_effective_descent_datum_sheaf"]
structure Descent (D : QuasicoherentDescentDatum f) where
  /-- The quasi-coherent `𝒪_S`-module `ℳ`. -/
  module : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory
  /-- The isomorphism `φ : f^* ℳ ≅ 𝒩`. -/
  iso : (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.obj module.obj ≅ D.module
  /-- The compatibility `σ ∘ p₁^* φ = p₂^* φ ∘ σ_ℳ` on `T ×_S T`. -/
  comm : (modulePullbackPseudofunctor.map (pullback.fst f f).op.toLoc).toFunctor.map iso.hom ≫
      D.obj.hom (pullback.fst f f ≫ f) (i₁ := ()) (i₂ := ()) (pullback.fst f f)
        (pullback.snd f f) rfl pullback.condition.symm =
    (canonicalDescentIso f module).hom ≫
      (modulePullbackPseudofunctor.map (pullback.snd f f).op.toLoc).toFunctor.map iso.hom

namespace Descent

variable {D : QuasicoherentDescentDatum f}

/-- The isomorphism of descent data `(f^* ℳ, σ_ℳ) ≅ D` given by a descent `(ℳ, φ)` of `D`. -/
noncomputable def descentDataIso (d : Descent D) :
    canonicalDescentDatum.{0} f d.module ≅ D :=
  ObjectProperty.isoMk _ <| Pseudofunctor.DescentData.isoMk (fun _ ↦ d.iso) <| by
    rintro Y q ⟨⟩ ⟨⟩ g₁ g₂ h₁ h₂
    let p : Y ⟶ pullback f f := pullback.lift g₁ g₂ (h₁.trans h₂.symm)
    have hp₁ : p ≫ pullback.fst f f = g₁ := pullback.lift_fst _ _ _
    have hp₂ : p ≫ pullback.snd f f = g₂ := pullback.lift_snd _ _ _
    have hq : p ≫ (pullback.fst f f ≫ f) = q := by rw [← Category.assoc, hp₁, h₁]
    have hD := D.obj.pullHom_hom p (pullback.fst f f ≫ f) q hq (i₁ := ()) (i₂ := ())
      (pullback.fst f f) (pullback.snd f f) rfl pullback.condition.symm g₁ g₂
      hp₁ hp₂
    have hA := (canonicalDescentDatum.{0} f d.module).obj.pullHom_hom p (pullback.fst f f ≫ f) q
      hq (i₁ := ()) (i₂ := ()) (pullback.fst f f) (pullback.snd f f) rfl
      pullback.condition.symm g₁ g₂ hp₁ hp₂
    rw [← hD, ← hA, canonicalDescentDatum_hom_fst_snd]
    exact map_comp_pullHom_of_comm _ _ _ _ d.comm _ _ _ _ _

@[simp]
lemma descentDataIso_hom_hom_hom (d : Descent D) (i : Unit) :
    d.descentDataIso.hom.hom.hom i = d.iso.hom := rfl

@[simp]
lemma descentDataIso_inv_hom_hom (d : Descent D) (i : Unit) :
    d.descentDataIso.inv.hom.hom i = d.iso.inv := rfl

/-- The descent `(ℳ, φ)` of `D` given by an isomorphism of descent data
`(f^* ℳ, σ_ℳ) ≅ D`, with `φ` its component. -/
noncomputable def ofIso (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (e : canonicalDescentDatum.{0} f M ≅ D) : Descent D where
  module := M
  iso := Pseudofunctor.DescentData.objIso ((ObjectProperty.ι _).mapIso e) ()
  comm := by
    have h := e.hom.hom.comm (pullback.fst f f ≫ f) (i₁ := ()) (i₂ := ()) (pullback.fst f f)
      (pullback.snd f f) rfl pullback.condition.symm
    rw [canonicalDescentDatum_hom_fst_snd] at h
    exact h

@[simp]
lemma ofIso_module (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (e : canonicalDescentDatum.{0} f M ≅ D) : (ofIso M e).module = M := rfl

@[simp]
lemma ofIso_iso_hom (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (e : canonicalDescentDatum.{0} f M ≅ D) : (ofIso M e).iso.hom = e.hom.hom.hom () := rfl

end Descent

/-- A descent datum `(𝒩, σ)` with respect to `f` is effective, that is, isomorphic to the
canonical descent datum `(f^* ℳ, σ_ℳ)` of a quasi-coherent `𝒪_S`-module, if and only if it
admits a descent `(ℳ, φ)`. -/
@[weil "def_fka3_effective_descent_datum_sheaf"]
theorem isEffective_iff_nonempty_descent (D : QuasicoherentDescentDatum f) :
    D.IsEffective ↔ Nonempty (Descent D) := by
  constructor
  · rintro ⟨M, ⟨e⟩⟩
    exact ⟨Descent.ofIso M e⟩
  · rintro ⟨d⟩
    exact ⟨d.module, ⟨d.descentDataIso⟩⟩

end QuasicoherentDescentDatum

end AlgebraicGeometry
