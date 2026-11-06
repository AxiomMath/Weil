module

public import WeilFrontier.Algebra.Homology.DerivedCategory.KInjective
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.ResolutionFunctor
public import Weil.Attr

/-!
# The injective-resolution functor is an equivalence `D⁺(C) ≌ K⁺(Inj C)`

Let `C` be an abelian category, `c` a choice of injective resolutions `(I(X), i_X)` on the
bounded below derived category `D⁺(C)` and `ρ` an injective-resolution functor for `c`. Each
`ρ(X) = I(X)` is a bounded below complex of injective objects, so `ρ` factors through the full
subcategory `K⁺(Inj C)` of the homotopy category, and the resulting functor
`D⁺(C) ⥤ K⁺(Inj C)` is an equivalence of categories.

It is fully faithful because, `Q(i_X)` and `Q(i_Y)` being isomorphisms, `φ ↦ Q(ρ φ)` is the
bijection `φ ↦ Q(i_X)⁻¹ ≫ φ ≫ Q(i_Y)`, and `Q` is bijective on morphisms into the K-injective
complex `I(Y)`. It is essentially surjective because a bounded below complex of injectives `J`
is K-injective, so the quasi-isomorphism `i_J : J ⟶ I(J)` is a homotopy equivalence.

## Main definitions

* `CochainComplex.InjectiveResolutionFunctor.toPlusInjective`: the functor
  `ρ : D⁺(C) ⥤ K⁺(Inj C)`.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.toPlusInjective_comp_ι`: `ρ` followed by the
  inclusion `K⁺(Inj C) ⥤ K(C)` is the injective-resolution functor.
* `CochainComplex.InjectiveResolutionFunctor.isEquivalence_toPlusInjective`: `ρ` is an
  equivalence of categories.

## Implementation notes

The source assumes that `C` has enough injectives; this is only used to guarantee that a choice
of injective resolutions exists, so the statement is made for any given choice and needs no
`EnoughInjectives` instance. The equivalence in the other direction, the localization functor
`QhPlus : K⁺(Inj C) ⥤ D⁺(C)`, is [Stacks 013V].

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits DerivedCategory

namespace CochainComplex

namespace InjectiveResolutionFunctor

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)

/-- Each `ρ(X) = I(X)` is a bounded below complex of injective objects. -/
lemma homotopyInjPlus_functor_obj (X : PlusComplexes C) :
    _root_.homotopyInjPlus C (ρ.functor.obj X) := by
  rw [functor_obj, _root_.homotopyInjPlus_quotient_obj_iff]
  exact ⟨(c _ _).exists_isStrictlyGE, fun i => inferInstance⟩

/-- The injective-resolution functor `ρ : D⁺(C) ⥤ K⁺(Inj C)`, with values in the bounded below
homotopy category of injective objects. -/
noncomputable def toPlusInjective : PlusComplexes C ⥤ HomotopyCategory.PlusInjective C :=
  (_root_.homotopyInjPlus C).lift ρ.functor ρ.homotopyInjPlus_functor_obj

/-- `ρ` takes values in `K⁺(Inj C)`: composed with the inclusion into `K(C)` it is the
injective-resolution functor. -/
@[weil "prop_fka2_injectives_equivalence_dplus"]
lemma toPlusInjective_comp_ι : ρ.toPlusInjective ⋙ HomotopyCategory.PlusInjective.ι = ρ.functor :=
  rfl

/-- `φ ↦ Q(ρ φ)` is injective. -/
lemma Qh_map_injective {X Y : PlusComplexes C} {φ ψ : X ⟶ Y}
    (h : Qh.map (ρ.map φ) = Qh.map (ρ.map ψ)) : φ = ψ := by
  rw [Qh_map_map, Qh_map_map] at h
  have h' := (cancel_epi (inv (resolutionMap c X))).1 h
  exact InducedCategory.hom_ext ((cancel_mono (resolutionMap c Y)).1 h')

instance : ρ.functor.Faithful where
  map_injective {X Y} φ ψ h := ρ.Qh_map_injective (by rw [← functor_map, ← functor_map, h])

/-- Every morphism `I(X) ⟶ I(Y)` of `K(C)` is `ρ φ` for some `φ : X ⟶ Y` of `D⁺(C)`. -/
lemma exists_map_eq {X Y : PlusComplexes C}
    (f : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex) :
    ∃ φ : X ⟶ Y, ρ.map φ = f := by
  refine ⟨InducedCategory.homMk (resolutionMap c X ≫ Qh.map f ≫ inv (resolutionMap c Y)), ?_⟩
  apply (homEquiv c X Y).injective
  rw [homEquiv_apply, homEquiv_apply, Qh_map_map]
  simp

instance : ρ.functor.Full where
  map_surjective f := ρ.exists_map_eq f

instance : ρ.toPlusInjective.Faithful :=
  inferInstanceAs ((_root_.homotopyInjPlus C).lift ρ.functor _).Faithful

instance : ρ.toPlusInjective.Full :=
  inferInstanceAs ((_root_.homotopyInjPlus C).lift ρ.functor _).Full

instance : ρ.toPlusInjective.EssSurj where
  mem_essImage J := by
    obtain ⟨_, ⟨K, ⟨⟨d, hd⟩, hinj⟩⟩⟩ := J
    have hK : ∃ n : ℤ, K.IsGE n := ⟨d, inferInstance⟩
    let R := c K hK
    have hι : Function.Bijective
        (fun g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex ⟶
            (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K =>
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι ≫ g) :=
      bijective_precomp_quotient_map_of_quasiIso_of_injective R.ι K d
    obtain ⟨d', _⟩ := R.exists_isStrictlyGE
    have hι' : Function.Bijective
        (fun g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex ⟶
            (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex =>
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι ≫ g) :=
      bijective_precomp_quotient_map_of_quasiIso_of_injective R.ι R.cocomplex d'
    obtain ⟨g, hg⟩ := hι.2 (𝟙 _)
    simp only at hg
    have e : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex ≅
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K :=
      { hom := g
        inv := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι
        hom_inv_id := hι'.1 (by
          change _ ≫ g ≫ _ = _ ≫ 𝟙 _
          simp [reassoc_of% hg])
        inv_hom_id := hg }
    exact ⟨⟨K, hK⟩, ⟨(_root_.homotopyInjPlus C).fullyFaithfulι.preimageIso e⟩⟩

/-- An injective-resolution functor `ρ : D⁺(C) ⥤ K⁺(Inj C)` is an equivalence of categories. -/
@[weil "prop_fka2_injectives_equivalence_dplus"]
instance isEquivalence_toPlusInjective : ρ.toPlusInjective.IsEquivalence where

end InjectiveResolutionFunctor

end CochainComplex

end
