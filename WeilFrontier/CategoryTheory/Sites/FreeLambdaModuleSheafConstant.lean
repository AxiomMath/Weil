module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Weil.Attr

/-!
# The free sheaf of modules on a constant sheaf of sets

Let `(C, J)` be a site, `Λ` a ring and `M₀` a set. The free sheaf of `Λ`-modules
`M ↦ M^Λ` (the sheafification of the sectionwise free module `U ↦ Λ^(M(U))`, Mathlib's
`CategoryTheory.Sheaf.composeAndSheafify J (ModuleCat.freeMax.{w} Λ)`) applied to the constant
sheaf of sets `(M₀)_C` is the constant sheaf of `Λ`-modules `N_C` on the free module
`N = Λ^(M₀) = M₀ →₀ Λ`. The isomorphism composed with the unit
`ι : (M₀)_C ⟶ ((M₀)_C)^Λ` of the free–forget adjunction is the map `(M₀)_C ⟶ N_C` induced by
the inclusion `m ↦ single m 1` of `M₀` as the basis of `N`: precomposed with the
sheafification unit of the constant presheaf `U ↦ M₀`, it sends `m ∈ M₀` over `U` to the image
of the basis vector `single m 1` in the sections of `N_C` over `U`. That property characterises
the isomorphism, since maps of sheaves of sets out of `(M₀)_C` are determined by their
composite with the sheafification unit, and maps of sheaves of modules out of `((M₀)_C)^Λ` by
their composite with `ι`.

## Main definitions

* `ModuleCat.freeMax`, `ModuleCat.adjMax`: the free module functor
  `Type (max w w') ⥤ ModuleCat.{max w w'} R` for a ring `R : Type w'`, and the free–forget
  adjunction.
* `CategoryTheory.Sheaf.composeAndSheafifyFreeConstantSheafIso`: the isomorphism
  `((M₀)_C)^Λ ≅ (Λ^(M₀))_C` of sheaves of `Λ`-modules.

## Main results

* `CategoryTheory.Sheaf.toSheafify_comp_unit_comp_composeAndSheafifyFreeConstantSheafIso_hom`:
  its composite with `ι_{(M₀)_C}` is induced by the inclusion of the basis `M₀ → Λ^(M₀)`.
* `AlgebraicGeometry.Scheme.toSheafify_comp_unit_comp_etaleFreeConstantSheafIso_hom`: the same
  on the small étale site of a scheme.

## Implementation notes

The constant sheaf is Mathlib's `CategoryTheory.constantSheaf`, the sheafification of the
constant presheaf; its identification with the sheaf of locally constant functions
`U ↦ N^{π₀(U)}` of the source is a separate statement. The isomorphism is the comparison
`CategoryTheory.presheafToSheafCompComposeAndSheafifyIso` between sheafifying and then taking
free modules, and taking free modules and then sheafifying, which applies because the free
module functor is a left adjoint; the free module on the constant presheaf at `M₀` is the
constant presheaf at `Λ^(M₀)`. This needs no terminal object on the site, unlike the argument
by uniqueness of left adjoints to the sections over a terminal object.

The ring `Λ : Type w'` and the universe `max w w'` of the sets and modules are independent, so
that `Λ = ZMod n : Type` with modules in `ModuleCat.{u + 1}` is an instance; Mathlib's
`ModuleCat.free` asks for both in one universe, and is `ModuleCat.freeMax.{w'}`
(`ModuleCat.freeMax_eq_free`). The forgetful functor of `ModuleCat.{max w w'} R` is
corepresented by the free module on one generator, which gives the sheaf property of the
underlying sheaf of sets.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory

universe w w' v u

namespace ModuleCat

variable (R : Type w') [Ring R]

/-- The free functor `Type (max w w') ⥤ ModuleCat.{max w w'} R` for a ring `R : Type w'`,
sending a type `X` to the free `R`-module `X →₀ R`. At `w = w'` it is `ModuleCat.free R`. -/
def freeMax : Type (max w w') ⥤ ModuleCat.{max w w'} R where
  obj X := ModuleCat.of R (X →₀ R)
  map {_ _} f := ofHom <| Finsupp.lmapDomain _ _ (f : _ → _)

theorem freeMax_eq_free : freeMax.{w'} R = free R := rfl

variable {R}

/-- The bijection `((freeMax R).obj X ⟶ M) ≃ (X → M)`. -/
def freeMaxHomEquiv {X : Type (max w w')} {M : ModuleCat.{max w w'} R} :
    ((freeMax.{w} R).obj X ⟶ M) ≃ (X ⟶ M) where
  toFun φ := TypeCat.ofHom fun x ↦ φ.hom (Finsupp.single x 1)
  invFun ψ := ofHom <| Finsupp.lift M R X ψ
  left_inv φ := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    simp [freeMax]
    rfl
  right_inv ψ := by
    ext x
    change Finsupp.lift M R X ψ (Finsupp.single x 1) = ψ x
    rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

theorem freeMaxHomEquiv_symm_apply_single {X : Type (max w w')} {M : ModuleCat.{max w w'} R}
    (ψ : X ⟶ M) (x : X) :
    (freeMaxHomEquiv.{w} (R := R) |>.symm ψ).hom (Finsupp.single x 1) = ψ x :=
  congrArg (fun f : X ⟶ M ↦ f x) (freeMaxHomEquiv.{w}.apply_symm_apply ψ)

variable (R)

/-- The free–forgetful adjunction for `R`-modules in the universe `max w w'`. -/
def adjMax : freeMax.{w} R ⊣ forget (ModuleCat.{max w w'} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => freeMaxHomEquiv
      homEquiv_naturality_left_symm := fun {X Y M} f g ↦ by
        apply ModuleCat.hom_ext
        apply Finsupp.lhom_ext'
        intro x
        apply LinearMap.ext_ring
        change (freeMaxHomEquiv.symm (f ≫ g)).hom (Finsupp.single x 1) =
          (freeMaxHomEquiv.symm g).hom (Finsupp.mapDomain f (Finsupp.single x 1))
        rw [Finsupp.mapDomain_single, freeMaxHomEquiv_symm_apply_single,
          freeMaxHomEquiv_symm_apply_single]
        rfl }

/-- The forgetful functor of `ModuleCat.{max w w'} R` is corepresented by the free module on
one generator. -/
def forgetCorepresentableByFreeMaxPUnit :
    (forget (ModuleCat.{max w w'} R)).CorepresentableBy ((freeMax.{w} R).obj PUnit) where
  homEquiv := freeMaxHomEquiv.trans
    { toFun f := f PUnit.unit
      invFun m := TypeCat.ofHom fun _ ↦ m
      left_inv _ := rfl
      right_inv _ := rfl }
  homEquiv_comp _ _ := rfl

instance forget_isCorepresentable_max :
    (forget (ModuleCat.{max w w'} R)).IsCorepresentable :=
  (forgetCorepresentableByFreeMaxPUnit R).isCorepresentable

end ModuleCat

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (Λ : Type w') [Ring Λ]
  [HasWeakSheafify J (ModuleCat.{max w w'} Λ)] [HasWeakSheafify J (Type (max w w'))]
  (M₀ : Type (max w w'))

/-- The free module functor preserves sheafification, being a left adjoint. -/
instance preservesSheafification_moduleCatFree :
    J.PreservesSheafification (ModuleCat.freeMax.{w} Λ) :=
  preservesSheafification_of_adjunction J (ModuleCat.adjMax.{w} Λ)

/-- **The free sheaf of `Λ`-modules on a constant sheaf of sets is constant.** For a set `M₀`,
the free sheaf of `Λ`-modules `((M₀)_C)^Λ` on the constant sheaf of sets `(M₀)_C` is the
constant sheaf of `Λ`-modules on the free module `Λ^(M₀) = M₀ →₀ Λ`. -/
@[weil "lem_fk104_free_lambda_module_sheaf_constant"]
def composeAndSheafifyFreeConstantSheafIso :
    (composeAndSheafify J (ModuleCat.freeMax.{w} Λ)).obj
        ((constantSheaf J (Type (max w w'))).obj M₀) ≅
      (constantSheaf J (ModuleCat.{max w w'} Λ)).obj (ModuleCat.of Λ (M₀ →₀ Λ)) :=
  (presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.freeMax.{w} Λ)).app _ ≪≫
    (presheafToSheaf J (ModuleCat.{max w w'} Λ)).mapIso
      (Functor.constComp Cᵒᵖ M₀ (ModuleCat.freeMax.{w} Λ))

/-- **The composite of `composeAndSheafifyFreeConstantSheafIso` with `ι_{(M₀)_C}` is induced
by the inclusion of the basis.** Precomposed with the sheafification unit of the constant
presheaf at `M₀`, the composite of the unit `ι : (M₀)_C ⟶ ((M₀)_C)^Λ` of the free–forget
adjunction with the isomorphism `((M₀)_C)^Λ ≅ (Λ^(M₀))_C` sends `m ∈ M₀` to the image of the
basis vector `single m 1` under the sheafification unit of the constant presheaf at
`Λ^(M₀)`. -/
@[weil "lem_fk104_free_lambda_module_sheaf_constant"]
theorem toSheafify_comp_unit_comp_composeAndSheafifyFreeConstantSheafIso_hom :
    toSheafify J ((Functor.const Cᵒᵖ).obj M₀) ≫
        ((adjunction J (ModuleCat.adjMax.{w} Λ)).unit.app
            ((constantSheaf J (Type (max w w'))).obj M₀) ≫
          (sheafCompose J (forget (ModuleCat.{max w w'} Λ))).map
            (composeAndSheafifyFreeConstantSheafIso.{w} J Λ M₀).hom).hom =
      (Functor.const Cᵒᵖ).map
          (TypeCat.ofHom fun m : M₀ ↦ (Finsupp.single m (1 : Λ) : M₀ →₀ Λ)) ≫
        Functor.whiskerRight
          (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of Λ (M₀ →₀ Λ))))
          (forget (ModuleCat.{max w w'} Λ)) := by
  set P := (Functor.const Cᵒᵖ).obj M₀
  set e := presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.freeMax.{w} Λ)
  set η := (Adjunction.whiskerRight Cᵒᵖ (ModuleCat.adjMax.{w} Λ)).unit
  have h0 : sheafifyMap J (Functor.whiskerRight (toSheafify J P) (ModuleCat.freeMax.{w} Λ)) ≫
      (e.hom.app P).hom = 𝟙 _ := by
    simpa [e] using Sheaf.hom_ext_iff.1 (e.inv_hom_id_app P)
  have h1 : Functor.whiskerRight (toSheafify J P) (ModuleCat.freeMax.{w} Λ) ≫
      toSheafify J (sheafify J P ⋙ ModuleCat.freeMax.{w} Λ) ≫ (e.hom.app P).hom =
        toSheafify J (P ⋙ ModuleCat.freeMax.{w} Λ) := by
    rw [toSheafify_naturality_assoc, h0, Category.comp_id]
  have h2 : toSheafify J P ≫ η.app (sheafify J P) = η.app P ≫
      Functor.whiskerRight (Functor.whiskerRight (toSheafify J P) (ModuleCat.freeMax.{w} Λ))
        (forget (ModuleCat.{max w w'} Λ)) :=
    η.naturality (toSheafify J P)
  have h3 : η.app P ≫ Functor.whiskerRight (Functor.constComp Cᵒᵖ M₀ (ModuleCat.freeMax.{w} Λ)).hom
      (forget (ModuleCat.{max w w'} Λ)) =
      (Functor.const Cᵒᵖ).map
        (TypeCat.ofHom fun m : M₀ ↦ (Finsupp.single m (1 : Λ) : M₀ →₀ Λ)) := by
    ext U m
    rfl
  simp only [adjunction_unit_app_hom, ObjectProperty.FullSubcategory.comp_hom, sheafCompose_map_hom]
  change toSheafify J P ≫ (η.app (sheafify J P) ≫
      Functor.whiskerRight (toSheafify J (sheafify J P ⋙ ModuleCat.freeMax.{w} Λ))
        (forget (ModuleCat.{max w w'} Λ))) ≫
      Functor.whiskerRight ((e.hom.app P).hom ≫
        sheafifyMap J (Functor.constComp Cᵒᵖ M₀ (ModuleCat.freeMax.{w} Λ)).hom)
        (forget (ModuleCat.{max w w'} Λ)) = _
  rw [Category.assoc, reassoc_of% h2]
  simp only [← Functor.whiskerRight_comp]
  rw [reassoc_of% h1, ← toSheafify_naturality, Functor.whiskerRight_comp, ← Category.assoc]
  erw [h3]
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) (Λ : Type w') [Ring Λ]
  [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{max w w'} Λ)]
  [HasWeakSheafify Y.smallEtaleTopology (Type (max w w'))] (M₀ : Type (max w w'))

/-- **The free sheaf of `Λ`-modules on a constant étale sheaf of sets** (FK I.4): on the small
étale site of a scheme `Y`, the composite of the unit `ι : (M₀)_Y ⟶ ((M₀)_Y)^Λ` with the
isomorphism `((M₀)_Y)^Λ ≅ (Λ^(M₀))_Y` is induced by the inclusion of `M₀` as the basis of
`Λ^(M₀)`. -/
theorem toSheafify_comp_unit_comp_etaleFreeConstantSheafIso_hom :
    toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M₀) ≫
        ((Sheaf.adjunction Y.smallEtaleTopology (ModuleCat.adjMax.{w} Λ)).unit.app
            ((constantSheaf Y.smallEtaleTopology (Type (max w w'))).obj M₀) ≫
          (sheafCompose Y.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{max w w'} Λ))).map
            (Sheaf.composeAndSheafifyFreeConstantSheafIso.{w} Y.smallEtaleTopology Λ M₀).hom).hom =
      (Functor.const Y.Etaleᵒᵖ).map
          (TypeCat.ofHom fun m : M₀ ↦ (Finsupp.single m (1 : Λ) : M₀ →₀ Λ)) ≫
        Functor.whiskerRight
          (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj
            (ModuleCat.of Λ (M₀ →₀ Λ))))
          (CategoryTheory.forget (ModuleCat.{max w w'} Λ)) :=
  Sheaf.toSheafify_comp_unit_comp_composeAndSheafifyFreeConstantSheafIso_hom.{w}
    Y.smallEtaleTopology Λ M₀

end AlgebraicGeometry.Scheme

end
