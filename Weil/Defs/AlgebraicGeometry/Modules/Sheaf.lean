module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Weil.Attr

/-!
# The descent sequence for homomorphisms of modules

Let `f : T ⟶ S` be a morphism of schemes, let `p₁ p₂ : T ×_S T ⟶ T` be the two projections and
`q = p₁ ≫ f = p₂ ≫ f`. For sheaves of modules `M`, `M'` on `S` there is a diagram of sets
```
Hom(M, M') ⟶ Hom(f^* M, f^* M') ⇉ Hom(q^* M, q^* M')
```
whose first map is `u ↦ f^* u` and whose two parallel maps send `φ` to `p_k^* φ`, transported
along the canonical isomorphisms `p_k^* f^* ≅ (p_k ≫ f)^* = q^*`. The diagram is *exact* when the
first map is injective and its image is the set of `φ` with `p₁^* φ = p₂^* φ`, that is, when
`f^*` identifies `Hom(M, M')` with the equalizer of the two parallel maps.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.descentHomFst`: the map `φ ↦ p₁^* φ`.
* `AlgebraicGeometry.Scheme.Modules.descentHomSnd`: the map `φ ↦ p₂^* φ`.
* `AlgebraicGeometry.Scheme.Modules.DescentSequenceExact`: exactness of the diagram.

## Main results

* `AlgebraicGeometry.Scheme.Modules.descentHomFst_map` and
  `AlgebraicGeometry.Scheme.Modules.descentHomSnd_map`: both parallel maps send `f^* u` to `q^* u`.
* `AlgebraicGeometry.Scheme.Modules.descentHomFst_map_eq_descentHomSnd_map`: the diagram is a
  fork.
* `AlgebraicGeometry.Scheme.Modules.descentSequenceExact_iff_existsUnique`: exactness says that
  every `φ` equalized by the two maps is `f^* u` for exactly one `u`.

## Implementation notes

The definition makes sense for arbitrary sheaves of modules; quasi-coherence of `M` and `M'`,
which the source assumes throughout, is a hypothesis of the results that need it. The scheme
`T ×_S T` is Mathlib's chosen fibre product `Limits.pullback f f`, and `q` is taken to be
`p₁ ≫ f`; the second parallel map is transported to `q^*` along `Scheme.Modules.pullbackCongr`
applied to `Limits.pullback.condition`. The canonical isomorphisms `c_{k, M}` are the components
of `Scheme.Modules.pullbackComp`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III, p. 304][FK88]
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}} (f : T ⟶ S) {M M' : S.Modules}

/-- The map `φ ↦ p₁^* φ` of the descent sequence: pullback along the first projection
`p₁ : T ×_S T ⟶ T`, transported along the canonical isomorphisms `p₁^* f^* ≅ (p₁ ≫ f)^*`. -/
noncomputable def descentHomFst
    (φ : (pullback f).obj M ⟶ (pullback f).obj M') :
    (pullback (Limits.pullback.fst f f ≫ f)).obj M ⟶
      (pullback (Limits.pullback.fst f f ≫ f)).obj M' :=
  (pullbackComp (Limits.pullback.fst f f) f).inv.app M ≫
    (pullback (Limits.pullback.fst f f)).map φ ≫
      (pullbackComp (Limits.pullback.fst f f) f).hom.app M'

/-- The map `φ ↦ p₂^* φ` of the descent sequence: pullback along the second projection
`p₂ : T ×_S T ⟶ T`, transported along the canonical isomorphisms
`p₂^* f^* ≅ (p₂ ≫ f)^* = (p₁ ≫ f)^*`. -/
noncomputable def descentHomSnd
    (φ : (pullback f).obj M ⟶ (pullback f).obj M') :
    (pullback (Limits.pullback.fst f f ≫ f)).obj M ⟶
      (pullback (Limits.pullback.fst f f ≫ f)).obj M' :=
  (pullbackCongr (Limits.pullback.condition (f := f) (g := f)).symm).inv.app M ≫
    (pullbackComp (Limits.pullback.snd f f) f).inv.app M ≫
      (pullback (Limits.pullback.snd f f)).map φ ≫
        (pullbackComp (Limits.pullback.snd f f) f).hom.app M' ≫
          (pullbackCongr (Limits.pullback.condition (f := f) (g := f)).symm).hom.app M'

/-- The descent sequence
`Hom(M, M') ⟶ Hom(f^* M, f^* M') ⇉ Hom(q^* M, q^* M')` is *exact*: the map `u ↦ f^* u` is
injective, and its image is the set of `φ` with `p₁^* φ = p₂^* φ`. -/
@[weil "def_fka3_descent_sequence_modules"]
structure DescentSequenceExact (M M' : S.Modules) : Prop where
  /-- The map `u ↦ f^* u` is injective. -/
  injective : Function.Injective fun u : M ⟶ M' ↦ (pullback f).map u
  /-- The image of `u ↦ f^* u` is the equalizer of `p₁^*` and `p₂^*`. -/
  range_eq : Set.range (fun u : M ⟶ M' ↦ (pullback f).map u) =
    {φ | descentHomFst f φ = descentHomSnd f φ}

@[simp]
lemma descentHomFst_map (u : M ⟶ M') :
    descentHomFst f ((pullback f).map u) = (pullback (Limits.pullback.fst f f ≫ f)).map u := by
  simp only [descentHomFst]
  have h₁ := (pullbackComp (Limits.pullback.fst f f) f).inv.naturality u
  simp only [Functor.comp_map] at h₁
  rw [← reassoc_of% h₁, Iso.inv_hom_id_app, Category.comp_id]

@[simp]
lemma descentHomSnd_map (u : M ⟶ M') :
    descentHomSnd f ((pullback f).map u) = (pullback (Limits.pullback.fst f f ≫ f)).map u := by
  simp only [descentHomSnd]
  have h₁ := (pullbackComp (Limits.pullback.snd f f) f).inv.naturality u
  have h₂ := (pullbackCongr (Limits.pullback.condition (f := f) (g := f)).symm).inv.naturality u
  simp only [Functor.comp_map] at h₁
  rw [← reassoc_of% h₁, Iso.inv_hom_id_app_assoc, ← reassoc_of% h₂, Iso.inv_hom_id_app,
    Category.comp_id]

/-- The descent sequence is a fork: `p₁^* (f^* u) = p₂^* (f^* u)`. -/
lemma descentHomFst_map_eq_descentHomSnd_map (u : M ⟶ M') :
    descentHomFst f ((pullback f).map u) = descentHomSnd f ((pullback f).map u) := by
  simp

/-- The image of `u ↦ f^* u` always lies in the equalizer of `p₁^*` and `p₂^*`. -/
lemma range_pullback_map_subset :
    Set.range (fun u : M ⟶ M' ↦ (pullback f).map u) ⊆
      {φ | descentHomFst f φ = descentHomSnd f φ} := by
  rintro _ ⟨u, rfl⟩
  exact descentHomFst_map_eq_descentHomSnd_map f u

/-- Exactness of the descent sequence: every `φ` equalized by `p₁^*` and `p₂^*` is `f^* u` for
exactly one `u`. -/
lemma descentSequenceExact_iff_existsUnique :
    DescentSequenceExact f M M' ↔
      ∀ φ : (pullback f).obj M ⟶ (pullback f).obj M',
        descentHomFst f φ = descentHomSnd f φ → ∃! u : M ⟶ M', (pullback f).map u = φ := by
  constructor
  · intro h φ hφ
    obtain ⟨u, hu⟩ : φ ∈ Set.range (fun u : M ⟶ M' ↦ (pullback f).map u) := by
      rw [h.range_eq]; exact hφ
    exact ⟨u, hu, fun v hv ↦ h.injective (hv.trans hu.symm)⟩
  · intro h
    refine ⟨fun u v huv ↦ ?_, (range_pullback_map_subset f).antisymm fun φ hφ ↦ ?_⟩
    · obtain ⟨w, -, hw⟩ := h _ (descentHomFst_map_eq_descentHomSnd_map f u)
      exact (hw u rfl).trans (hw v huv.symm).symm
    · obtain ⟨u, hu, -⟩ := h φ hφ
      exact ⟨u, hu⟩

/-- Exactness of the descent sequence says that `u ↦ f^* u` is a bijection from `Hom(M, M')`
onto the equalizer of `p₁^*` and `p₂^*`. -/
lemma descentSequenceExact_iff_bijective :
    DescentSequenceExact f M M' ↔
      Function.Bijective (fun u : M ⟶ M' ↦
        (⟨(pullback f).map u, descentHomFst_map_eq_descentHomSnd_map f u⟩ :
          {φ : (pullback f).obj M ⟶ (pullback f).obj M' //
            descentHomFst f φ = descentHomSnd f φ})) := by
  rw [descentSequenceExact_iff_existsUnique]
  constructor
  · intro h
    refine ⟨fun u v huv ↦ ?_, fun ⟨φ, hφ⟩ ↦ ?_⟩
    · obtain ⟨w, -, hw⟩ := h _ (descentHomFst_map_eq_descentHomSnd_map f u)
      exact (hw u rfl).trans (hw v (congrArg Subtype.val huv).symm).symm
    · obtain ⟨u, hu, -⟩ := h φ hφ
      exact ⟨u, Subtype.ext hu⟩
  · intro h φ hφ
    obtain ⟨u, hu⟩ := h.2 ⟨φ, hφ⟩
    refine ⟨u, congrArg Subtype.val hu, fun v hv ↦ h.1 (Subtype.ext ?_)⟩
    exact hv.trans (congrArg Subtype.val hu).symm

end AlgebraicGeometry.Scheme.Modules
