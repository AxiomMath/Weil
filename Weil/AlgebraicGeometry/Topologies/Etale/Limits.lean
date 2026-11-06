module

public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Weil.Attr

/-!
# Monomorphisms of the small étale site are open immersions

Let `B` be a big étale site containing a scheme `X`, and let `j : R ⟶ Z` be a morphism in the
small étale site of `X` such that `Hom_X(T, R) → Hom_X(T, Z)`, `a ↦ j ∘ a`, is injective for
every `T` in the small étale site. Then the underlying morphism of schemes of `j` is an open
immersion. Indeed `j` is a monomorphism of the small étale site, which has fibre products
preserved by the functor to schemes, so `j` is a monomorphism of schemes; it is étale, hence
flat and locally of finite presentation, and a flat monomorphism locally of finite
presentation is an open immersion.

In particular, if `u, v : R ⇉ Y` is a pair of morphisms of the small étale site which is
jointly injective on `T`-valued points for every `T` (for instance an equivalence relation in
the small étale site), then `(u, v) : R ⟶ Y ×_X Y` is an open immersion.

## Main results

* `AlgebraicGeometry.SmallEtale.isOpenImmersion_toScheme_map_of_injective`: a morphism of the
  small étale site that is injective on `T`-valued points is an open immersion.
* `AlgebraicGeometry.SmallEtale.isOpenImmersion_toScheme_map_pullbackLift`: for a pair
  `u, v : R ⇉ Y` jointly injective on points, `(u, v) : R ⟶ Y ×_X Y` (fibre product in the
  small étale site) is an open immersion.
* `AlgebraicGeometry.SmallEtale.isOpenImmersion_pullback_lift`: the same with `Y ×_X Y` the
  fibre product of schemes.

## Implementation notes

The étale site is the small étale site `AlgebraicGeometry.SmallEtale B X hX` of all étale
`X`-schemes lying in `B`; the category `Et(X)` of noetherian separated étale `X`-schemes of
Freitag–Kiehl is a full subcategory of it, and the hypothesis is asked for all `T` in the
larger site. Freitag–Kiehl's hypothesis on an equivalence relation (injectivity of
`(u, v)` on sections of representable sheaves) is `CategoryTheory.JointlyMono₂ u v`; only this
part of the equivalence relation condition is used, so the second statement assumes only it.
The proof goes through `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono` instead of
Freitag–Kiehl's descent argument.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.4
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- A morphism of the small étale site which is a monomorphism there is a monomorphism of
schemes. -/
theorem mono_toScheme_map {R Z : SmallEtale B X hX} (j : R ⟶ Z) [Mono j] :
    Mono ((SmallEtale.toScheme B X hX).map j) :=
  (SmallEtale.toScheme B X hX).map_mono j

/-- **Injective étale morphisms are open immersions.** Let `j : R ⟶ Z` be a morphism of the
small étale site of `X` such that `a ↦ a ≫ j` is injective on `Hom(T, R)` for every `T` in the
small étale site. Then the underlying morphism of schemes of `j` is an open immersion. -/
@[weil "lem_fk104_injective_etale_into_product_open_embedding"]
theorem isOpenImmersion_toScheme_map_of_injective {R Z : SmallEtale B X hX} (j : R ⟶ Z)
    (hj : ∀ T : SmallEtale B X hX, Function.Injective fun a : T ⟶ R ↦ a ≫ j) :
    IsOpenImmersion ((SmallEtale.toScheme B X hX).map j) := by
  have : Mono j := ⟨fun a b h ↦ hj _ h⟩
  have := mono_toScheme_map j
  have := etale_toScheme_map B X hX j
  exact IsOpenImmersion.of_flat_of_mono _

/-- The morphism from an object of the small étale site of `X` to the final object `X / X`. -/
noncomputable abbrev toFinal (Y : SmallEtale B X hX) : Y ⟶ SmallEtale.final B X hX :=
  (SmallEtale.finalIsTerminal B X hX).from Y

/-- **`(u, v) : R ⟶ Y ×_X Y` is an open immersion.** For a pair `u, v : R ⇉ Y` of morphisms of
the small étale site of `X` which is jointly injective on `T`-valued points (e.g. an
equivalence relation), the induced morphism into the fibre product `Y ×_X Y`, formed in the
small étale site, is an open immersion. -/
@[weil "lem_fk104_injective_etale_into_product_open_embedding"]
theorem isOpenImmersion_toScheme_map_pullbackLift {R Y : SmallEtale B X hX} (u v : R ⟶ Y)
    [JointlyMono₂ u v] :
    IsOpenImmersion ((SmallEtale.toScheme B X hX).map
      (pullback.lift u v ((SmallEtale.finalIsTerminal B X hX).hom_ext _ _) :
        R ⟶ pullback (toFinal Y) (toFinal Y))) := by
  refine isOpenImmersion_toScheme_map_of_injective _ fun T a b h ↦ ?_
  dsimp only at h
  exact JointlyMono₂.right_cancellation (p₁ := u) (p₂ := v) a b
    (by simpa only [Category.assoc, pullback.lift_fst] using
      congrArg (· ≫ pullback.fst (toFinal Y) (toFinal Y)) h)
    (by simpa only [Category.assoc, pullback.lift_snd] using
      congrArg (· ≫ pullback.snd (toFinal Y) (toFinal Y)) h)

/-- **`(u, v) : R ⟶ Y ×_X Y` is an open immersion, fibre product of schemes.** For a pair
`u, v : R ⇉ Y` of morphisms of the small étale site of `X` which is jointly injective on
`T`-valued points, the morphism of schemes `(u, v) : R ⟶ Y ×_X Y` into the fibre product of
schemes is an open immersion. -/
@[weil "lem_fk104_injective_etale_into_product_open_embedding"]
theorem isOpenImmersion_pullback_lift {R Y : SmallEtale B X hX} (u v : R ⟶ Y)
    [JointlyMono₂ u v] :
    IsOpenImmersion (pullback.lift ((SmallEtale.toScheme B X hX).map u)
      ((SmallEtale.toScheme B X hX).map v)
      (by rw [← Functor.map_comp, ← Functor.map_comp,
        (SmallEtale.finalIsTerminal B X hX).hom_ext (u ≫ toFinal Y) (v ≫ toFinal Y)]) :
      (SmallEtale.toScheme B X hX).obj R ⟶
        pullback ((SmallEtale.toScheme B X hX).map (toFinal Y))
          ((SmallEtale.toScheme B X hX).map (toFinal Y))) := by
  have := isOpenImmersion_toScheme_map_pullbackLift u v
  let e := PreservesPullback.iso (SmallEtale.toScheme B X hX) (toFinal Y) (toFinal Y)
  convert (inferInstance : IsOpenImmersion
    ((SmallEtale.toScheme B X hX).map (pullback.lift u v
      ((SmallEtale.finalIsTerminal B X hX).hom_ext _ _)) ≫ e.hom)) using 1
  ext1 <;> simp only [Category.assoc, e, PreservesPullback.iso_hom_fst,
    PreservesPullback.iso_hom_snd, pullback.lift_fst, pullback.lift_snd, ← Functor.map_comp]

end AlgebraicGeometry.SmallEtale

end
