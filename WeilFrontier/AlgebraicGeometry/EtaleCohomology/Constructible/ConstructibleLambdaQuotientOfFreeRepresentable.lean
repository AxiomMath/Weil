module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleIffQuotientOfRepresentable
public import WeilFrontier.CategoryTheory.Sites.FreeLambdaModuleSheafConstant
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# A constructible sheaf of `Λ`-modules is a quotient of a free sheaf on a representable

Let `X` be a Noetherian scheme and `Λ` a ring (in [FK], `Λ = ℤ/nℤ`). A sheaf of `Λ`-modules
`F` on the small étale site of `X` is constructible if its underlying sheaf of abelian groups
is. Then there are a Noetherian scheme `U` étale over `X` and an epimorphism of sheaves of
`Λ`-modules `(h_U)^Λ ⟶ F`, where `h_U` is the sheaf of sets represented by `U` and
`M ↦ M^Λ` is the free sheaf of `Λ`-modules on a sheaf of sets `M` (the sheafification of
`V ↦ Λ^(M(V))`).

The proof is that of [FK]: the underlying sheaf of sets of `F` is constructible, so it receives
an epimorphism `ψ : h_U ⟶ F` of sheaves of sets; `ψ` factors as `ι ≫ φ` through the unit
`ι : h_U ⟶ (h_U)^Λ` of the free–forgetful adjunction, with `φ` a morphism of sheaves of
`Λ`-modules; since `ψ` is locally surjective, so is `φ`, which is therefore an epimorphism.

## Main results

* `exists_epi_composeAndSheafify_freeMax_sheafifiedYoneda_of_isConstructibleAbelianSheaf`:
  a constructible sheaf of `Λ`-modules on a Noetherian scheme is a quotient of `(h_U)^Λ` for a
  Noetherian étale `X`-scheme `U`.
* `exists_epi_composeAndSheafify_freeMax_sheafifiedYoneda_of_isConstructibleSetSheaf`:
  the same with the hypothesis that the underlying sheaf of sets is constructible.
* `epi_of_epi_unit_comp_sheafCompose_forget_map`: a morphism of sheaves of
  `Λ`-modules out of a free sheaf is an epimorphism when its adjoint morphism of sheaves of sets
  is.

## Implementation notes

The free sheaf of `Λ`-modules is `CategoryTheory.Sheaf.composeAndSheafify` of the free module
functor `ModuleCat.freeMax`, which allows a ring `Λ : Type` (such as `ZMod n`) with modules and
sets in the universe `u + 1` of the sheaves on the small étale site. The objects of [FK]'s
`Et(X)` are étale `X`-schemes which are Noetherian, which is why the Noetherian condition on `U`
is part of the conclusion. The statement holds for every ring `Λ`, not only for `ℤ/nℤ`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.10][FreitagKiehl1988]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type) [Ring Λ]

/-- A morphism `φ : M^Λ ⟶ F` of sheaves of `Λ`-modules on the small étale site, out of the free
sheaf of `Λ`-modules on a sheaf of sets `M`, is an epimorphism when the morphism of sheaves of
sets `M ⟶ F` adjoint to it (the composite of `φ` with the unit `ι : M ⟶ M^Λ`) is one. -/
theorem epi_of_epi_unit_comp_sheafCompose_forget_map
    {M : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)}
    (φ : (Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
      (ModuleCat.freeMax.{u + 1} Λ)).obj M ⟶ F)
    (h : Epi ((Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
      (ModuleCat.adjMax.{u + 1} Λ)).unit.app M ≫
        (sheafCompose (SmallEtale.topology B X.obj X.property)
          (forget (ModuleCat.{u + 1} Λ))).map φ)) :
    Epi φ := by
  rw [← Sheaf.isLocallySurjective_iff_epi] at h
  have : Presheaf.IsLocallySurjective (SmallEtale.topology B X.obj X.property)
      (((Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
        (ModuleCat.adjMax.{u + 1} Λ)).unit.app M).hom ≫
          Functor.whiskerRight φ.hom (forget (ModuleCat.{u + 1} Λ))) := h
  have : Presheaf.IsLocallySurjective (SmallEtale.topology B X.obj X.property)
      (Functor.whiskerRight φ.hom (forget (ModuleCat.{u + 1} Λ))) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective _
      ((Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
        (ModuleCat.adjMax.{u + 1} Λ)).unit.app M).hom _
  have : Sheaf.IsLocallySurjective φ :=
    (Presheaf.isLocallySurjective_iff_whisker_forget _ φ.hom).2 this
  infer_instance

/-- **A constructible sheaf of `Λ`-modules is a quotient of a free sheaf on a representable,**
in the form where the underlying sheaf of sets is constructible. On a Noetherian scheme `X`,
if the underlying sheaf of sets of a sheaf of `Λ`-modules `F` on the small étale site is
constructible, there are a Noetherian étale `X`-scheme `Y` and an epimorphism `(h_Y)^Λ ⟶ F`
from the free sheaf of `Λ`-modules on the sheaf represented by `Y`. -/
theorem exists_epi_composeAndSheafify_freeMax_sheafifiedYoneda_of_isConstructibleSetSheaf
    [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSetSheaf B X
      ((sheafCompose (SmallEtale.topology B X.obj X.property)
        (forget (ModuleCat.{u + 1} Λ))).obj F)) :
    ∃ (Y : SmallEtale B X.obj X.property)
      (_ : IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj Y))
      (p : (Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
          (ModuleCat.freeMax.{u + 1} Λ)).obj
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj Y) ⟶ F),
      Epi p := by
  obtain ⟨Y, hY, ψ, hψ⟩ :=
    (isConstructibleSetSheaf_iff_exists_epi_sheafifiedYoneda B X _).1 hF
  have hfac := fun (ψ : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj Y ⟶
      (sheafCompose (SmallEtale.topology B X.obj X.property)
        (forget (ModuleCat.{u + 1} Λ))).obj F) =>
    ((Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
      (ModuleCat.adjMax.{u + 1} Λ)).homEquiv_unit _ _ _).symm.trans
        (Equiv.apply_symm_apply _ ψ)
  refine ⟨Y, hY, ((Sheaf.adjunction (SmallEtale.topology B X.obj X.property)
    (ModuleCat.adjMax.{u + 1} Λ)).homEquiv _ _).symm ψ, ?_⟩
  apply epi_of_epi_unit_comp_sheafCompose_forget_map
  rw [hfac ψ]
  exact hψ

/-- **A constructible sheaf of `Λ`-modules is a quotient of a free sheaf on a representable.**
Let `X` be a Noetherian scheme and `F` a sheaf of `Λ`-modules on the small étale site of `X`
whose underlying sheaf of abelian groups is constructible. Then there are a Noetherian scheme
`Y` étale over `X` and an epimorphism of sheaves of `Λ`-modules `(h_Y)^Λ ⟶ F`, where `h_Y` is
the sheaf represented by `Y` and `(h_Y)^Λ` the free sheaf of `Λ`-modules on it. -/
@[weil "prop_fk104_constructible_lambda_quotient_of_free_representable"]
theorem exists_epi_composeAndSheafify_freeMax_sheafifiedYoneda_of_isConstructibleAbelianSheaf
    [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleAbelianSheaf B X
      ((sheafCompose (SmallEtale.topology B X.obj X.property)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) :
    ∃ (Y : SmallEtale B X.obj X.property)
      (_ : IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj Y))
      (p : (Sheaf.composeAndSheafify (SmallEtale.topology B X.obj X.property)
          (ModuleCat.freeMax.{u + 1} Λ)).obj
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj Y) ⟶ F),
      Epi p :=
  exists_epi_composeAndSheafify_freeMax_sheafifiedYoneda_of_isConstructibleSetSheaf B X Λ F
    ((isConstructibleAbelianSheaf_iff_isConstructibleSetSheaf B X _).1 hF)

end AlgebraicGeometry
