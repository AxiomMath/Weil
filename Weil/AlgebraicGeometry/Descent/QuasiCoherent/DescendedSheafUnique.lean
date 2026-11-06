module

public import Weil.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import Weil.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import Weil.AlgebraicGeometry.Descent.QuasiCoherent.EffectiveDescentDatumSheaf
public import Weil.Attr

/-!
# Uniqueness of descents of a quasi-coherent descent datum

Let `f : T ⟶ S` be a faithfully flat quasi-compact morphism of schemes, `(𝒩, σ)` a descent
datum on a quasi-coherent `𝒪_T`-module with respect to `f`, and `(ℳ, φ)`, `(ℳ', φ')` two
descents of it. Then there is exactly one `𝒪_S`-linear map `u : ℳ ⟶ ℳ'` with
`φ' ∘ f^* u = φ`, and this `u` is an isomorphism.

The map `ψ = φ'⁻¹ ∘ φ : f^* ℳ ⟶ f^* ℳ'` is compatible with the canonical descent data of
`f^* ℳ` and `f^* ℳ'`, so it lies in the equalizer of the descent sequence
`Hom(ℳ, ℳ') ⟶ Hom(f^* ℳ, f^* ℳ') ⇉ Hom(q^* ℳ, q^* ℳ')`, which is exact by fpqc descent of
homomorphisms; hence `ψ = f^* u` for exactly one `u`. Exchanging the two descents gives `u'`
with `f^* u' = ψ⁻¹`, and injectivity of `u ↦ f^* u` shows that `u` and `u'` are inverse.

## Main definitions

* `AlgebraicGeometry.QuasicoherentDescentDatum.Descent.isoOfDescent`: the isomorphism
  `ℳ ≅ ℳ'` between two descents of the same descent datum.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentDatum.Descent.existsUnique_map_hom_comp_iso_hom`: there
  is exactly one `u : ℳ ⟶ ℳ'` with `φ' ∘ f^* u = φ`.
* `AlgebraicGeometry.QuasicoherentDescentDatum.Descent.isIso_of_map_hom_comp_iso_hom`: every such
  `u` is an isomorphism.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace QuasicoherentDescentDatum

namespace Descent

variable {T S : Scheme.{u}} {f : T ⟶ S} {D : QuasicoherentDescentDatum f}

/-- Transport of compatibilities along isomorphisms: if `φ : X ≅ N` and `φ' : X' ≅ N` are
compatible with `σ_X`, `σ_{X'}` and `σ_N` in the sense that `F₁ φ ≫ σ_N = σ_X ≫ F₂ φ` and
likewise for `φ'`, then `φ ≫ φ'⁻¹` is compatible with `σ_X` and `σ_{X'}`. -/
private lemma map_hom_comp_inv_comp_of_comm {A B : Type*} [Category A] [Category B]
    (F₁ F₂ : A ⥤ B) {X X' N : A} (φ : X ≅ N) (φ' : X' ≅ N) (σX : F₁.obj X ⟶ F₂.obj X)
    (σX' : F₁.obj X' ⟶ F₂.obj X') (σN : F₁.obj N ⟶ F₂.obj N)
    (h : F₁.map φ.hom ≫ σN = σX ≫ F₂.map φ.hom) (h' : F₁.map φ'.hom ≫ σN = σX' ≫ F₂.map φ'.hom) :
    F₁.map (φ.hom ≫ φ'.inv) ≫ σX' = σX ≫ F₂.map (φ.hom ≫ φ'.inv) := by
  have e : σX' = F₁.map φ'.hom ≫ σN ≫ F₂.map φ'.inv := by
    rw [← Category.assoc, h', Category.assoc, ← F₂.map_comp, Iso.hom_inv_id, F₂.map_id,
      Category.comp_id]
  rw [e, F₁.map_comp, Category.assoc, ← F₁.map_comp_assoc φ'.inv φ'.hom, Iso.inv_hom_id,
    F₁.map_id, Category.id_comp, reassoc_of% h, F₂.map_comp]

/-- If `F v = φ ≫ φ'⁻¹` and `F w = φ' ≫ φ⁻¹`, then `F (v ≫ w) = F (𝟙 X)`. -/
private lemma map_comp_eq_map_id_of_eq {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} {Z : B} (v : X ⟶ Y) (w : Y ⟶ X) (φ : F.obj X ≅ Z) (φ' : F.obj Y ≅ Z)
    (hv : F.map v = φ.hom ≫ φ'.inv) (hw : F.map w = φ'.hom ≫ φ.inv) :
    F.map (v ≫ w) = F.map (𝟙 X) := by
  rw [F.map_comp, hv, hw, F.map_id]
  simp

/-- For two descents `(ℳ, φ)` and `(ℳ', φ')` of the same descent datum, the map
`φ'⁻¹ ∘ φ : f^* ℳ ⟶ f^* ℳ'` is compatible with the canonical descent data:
`σ_{ℳ'} ∘ p₁^* (φ'⁻¹ ∘ φ) = p₂^* (φ'⁻¹ ∘ φ) ∘ σ_ℳ`. -/
lemma map_iso_hom_comp_iso_inv_comp_canonicalDescentIso_hom (d d' : Descent D) :
    (modulePullbackPseudofunctor.map (pullback.fst f f).op.toLoc).toFunctor.map
        (d.iso.hom ≫ d'.iso.inv) ≫ (canonicalDescentIso f d'.module).hom =
      (canonicalDescentIso f d.module).hom ≫
        (modulePullbackPseudofunctor.map (pullback.snd f f).op.toLoc).toFunctor.map
          (d.iso.hom ≫ d'.iso.inv) :=
  map_hom_comp_inv_comp_of_comm _ _ d.iso d'.iso _ _ _ d.comm d'.comm

variable [Flat f] [Surjective f] [QuasiCompact f]

/-- For two descents `(ℳ, φ)` and `(ℳ', φ')` of the same descent datum with respect to a
faithfully flat quasi-compact morphism `f`, there is exactly one morphism `u : ℳ ⟶ ℳ'` with
`f^* u = φ'⁻¹ ∘ φ`. -/
lemma existsUnique_map_hom_eq (d d' : Descent D) :
    ∃! v : d.module ⟶ d'.module,
      (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.map v.hom =
        d.iso.hom ≫ d'.iso.inv := by
  have hex := (Scheme.Modules.descentSequenceExact_iff_existsUnique f (M := d.module.obj)
    (M' := d'.module.obj)).1
    (Scheme.Modules.descentSequenceExact_of_flat_of_surjective f d.module.obj d'.module.obj)
  obtain ⟨v, hv, hvu⟩ := hex (d.iso.hom ≫ d'.iso.inv)
    ((map_comp_canonicalDescentIso_hom_iff f d.module d'.module
      (d.iso.hom ≫ d'.iso.inv)).1 (map_iso_hom_comp_iso_inv_comp_canonicalDescentIso_hom d d'))
  exact ⟨ObjectProperty.homMk v, hv, fun w hw ↦ ObjectProperty.hom_ext _ (hvu w.hom hw)⟩

/-- `f^* u` determines a morphism `u` of quasi-coherent `𝒪_S`-modules, for `f` faithfully flat
and quasi-compact. -/
lemma hom_ext_of_map_hom_eq
    {M M' : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} {v w : M ⟶ M'}
    (h : (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.map v.hom =
      (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.map w.hom) : v = w :=
  ObjectProperty.hom_ext _
    ((Scheme.Modules.descentSequenceExact_of_flat_of_surjective f M.obj M'.obj).injective h)

/-- **Uniqueness of descents, existence and uniqueness of the comparison map.** For two
descents `(ℳ, φ)` and `(ℳ', φ')` of a descent datum `(𝒩, σ)` with respect to a faithfully flat
quasi-compact morphism `f`, there is exactly one `𝒪_S`-linear `u : ℳ ⟶ ℳ'` with
`φ' ∘ f^* u = φ`. -/
@[weil "lem_fka3_descended_sheaf_unique"]
theorem existsUnique_map_hom_comp_iso_hom (d d' : Descent D) :
    ∃! v : d.module ⟶ d'.module,
      (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.map v.hom ≫ d'.iso.hom =
        d.iso.hom := by
  obtain ⟨v, hv, hvu⟩ := existsUnique_map_hom_eq d d'
  exact ⟨v, (Iso.eq_comp_inv _).1 hv, fun w hw ↦ hvu w ((Iso.eq_comp_inv _).2 hw)⟩

/-- **Uniqueness of descents, the comparison map is an isomorphism.** For two descents
`(ℳ, φ)` and `(ℳ', φ')` of a descent datum with respect to a faithfully flat quasi-compact
morphism `f`, every `𝒪_S`-linear `u : ℳ ⟶ ℳ'` with `φ' ∘ f^* u = φ` is an isomorphism. -/
@[weil "lem_fka3_descended_sheaf_unique"]
theorem isIso_of_map_hom_comp_iso_hom {d d' : Descent D} (v : d.module ⟶ d'.module)
    (hv : (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.map v.hom ≫ d'.iso.hom =
      d.iso.hom) : IsIso v := by
  have hv' := (Iso.eq_comp_inv _).2 hv
  obtain ⟨w, hw, -⟩ := existsUnique_map_hom_eq d' d
  refine ⟨w, hom_ext_of_map_hom_eq (f := f) ?_, hom_ext_of_map_hom_eq (f := f) ?_⟩
  · exact map_comp_eq_map_id_of_eq _ v.hom w.hom d.iso d'.iso hv' hw
  · exact map_comp_eq_map_id_of_eq _ w.hom v.hom d'.iso d.iso hw hv'

/-- The isomorphism `u : ℳ ≅ ℳ'` between two descents `(ℳ, φ)` and `(ℳ', φ')` of the same
descent datum with respect to a faithfully flat quasi-compact morphism, characterized by
`φ' ∘ f^* u = φ`. -/
noncomputable def isoOfDescent (d d' : Descent D) : d.module ≅ d'.module :=
  have := isIso_of_map_hom_comp_iso_hom _ (existsUnique_map_hom_comp_iso_hom d d').choose_spec.1
  asIso (existsUnique_map_hom_comp_iso_hom d d').choose

lemma map_isoOfDescent_hom_comp_iso_hom (d d' : Descent D) :
    (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.map (isoOfDescent d d').hom.hom ≫
      d'.iso.hom = d.iso.hom :=
  (existsUnique_map_hom_comp_iso_hom d d').choose_spec.1

lemma eq_isoOfDescent_hom {d d' : Descent D} (v : d.module ⟶ d'.module)
    (hv : (modulePullbackPseudofunctor.map f.op.toLoc).toFunctor.map v.hom ≫ d'.iso.hom =
      d.iso.hom) :
    v = (isoOfDescent d d').hom :=
  (existsUnique_map_hom_comp_iso_hom d d').unique hv (map_isoOfDescent_hom_comp_iso_hom d d')

end Descent

end QuasicoherentDescentDatum

end AlgebraicGeometry
