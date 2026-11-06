module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Sites.EtaleCategoryEssentiallySmall
public import Weil.AlgebraicGeometry.Sites.SheafExactIffLocallyExact
public import Weil.Defs.CategoryTheory.Generator.Sheaf

/-!
# Free abelian sheaves on representables generate the abelian sheaves on `Et(A)`

Let `A` be a commutative ring and let `R` be a set of objects of the étale category `Et(A)`
containing a representative of every isomorphism class. Every sheaf of abelian groups `G` on
`Et(A)` is a quotient of a direct sum, taken in the category of sheaves, of free abelian sheaves
`B̲^ab` on representable presheaves `B̲ = Hom_A(B, -)` with `B ∈ R`.

## Main results

- `AlgebraicGeometry.EtaleCategory.exists_epi_sigma_freeAbelianSheaf`: the epimorphism
  `⨁ⱼ B̲ⱼ^ab ⟶ G` with all `Bⱼ ∈ R`.

## Implementation notes

The representable presheaf `B̲` of an object `B` of `Et(A) = (Scheme.AffineEtale (Spec A))ᵒᵖ`
is `yoneda.obj B.unop` on the affine étale site. The index set is the set of pairs `(B, s)` with
`s ∈ G(B)` and `B` running over a set of representatives in `R` of the isomorphism classes of a
small model of `Et(A)`; so no smallness hypothesis on `R` is needed. That the morphism is an
epimorphism follows from the exactness criterion
`AlgebraicGeometry.EtaleCategory.exact_iff_forall_exists_faithfullyFlat`, with the identity
as faithfully flat morphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

/-- Sheaves of abelian groups on `Et(A)` have all `u`-small coproducts, computed by sheafifying
the coproduct of presheaves. This shortcut avoids a slow instance search. -/
instance hasColimitsOfShape_discrete_sheaf (J : Type u) :
    HasColimitsOfShape (Discrete J)
      (Sheaf (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u}) :=
  @Sheaf.instHasColimitsOfShape _ _ _ _ _ _ _ inferInstance inferInstance

/-- **Free abelian sheaves on representables generate** [FK, I.1]. Let `R` be a set of
objects of `Et(A)` containing a representative of every isomorphism class. Every sheaf of
abelian groups `G` on `Et(A)` receives an epimorphism from a coproduct, in the category of
sheaves, of free abelian sheaves `B̲ⱼ^ab` on representable presheaves with `Bⱼ ∈ R`. -/
@[weil "lem_fk101_representable_free_sheaves_generate"]
theorem exists_epi_sigma_freeAbelianSheaf (R : Set (EtaleCategory A))
    (hR : ∀ C : EtaleCategory A, ∃ B ∈ R, Nonempty (B ≅ C))
    (G : Sheaf (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u}) :
    ∃ (J : Type u) (B : J → EtaleCategory A) (_ : ∀ j, B j ∈ R)
      (π : ∐ (fun j ↦ Presheaf.freeAbelianSheafObj (Scheme.AffineEtale.topology (Spec A))
        (yoneda.obj (B j).unop)) ⟶ G), Epi π := by
  let e := equivSmallModel.{u} (EtaleCategory A)
  choose b hbR hb using fun C : SmallModel.{u} (EtaleCategory A) ↦ hR (e.inverse.obj C)
  let J := Σ C : SmallModel.{u} (EtaleCategory A), G.obj.obj (b C)
  let ψ : ∀ j : J, Presheaf.freeAbelianSheafObj (Scheme.AffineEtale.topology (Spec A))
      (yoneda.obj (b j.1).unop) ⟶ G :=
    fun j ↦ (Presheaf.freeAbelianSheafYonedaHomEquiv _).symm j.2
  refine ⟨J, fun j ↦ b j.1, fun j ↦ hbR j.1, Sigma.desc ψ, ?_⟩
  have hψ : ∀ (j : J) (C : EtaleCategory A) (f : C.unop ⟶ (b j.1).unop),
      (ψ j).hom.app (op C.unop)
        ((Presheaf.toFreeAbelianSheaf _ (yoneda.obj (b j.1).unop)).app (op C.unop) f) =
        G.obj.map f.op j.2 := by
    intro j C f
    have h0 : Presheaf.freeAbelianSheafHomEquiv _ (ψ j) = yonedaEquiv.symm j.2 := by
      simp only [ψ, Presheaf.freeAbelianSheafYonedaHomEquiv, Equiv.symm_trans_apply,
        Equiv.apply_symm_apply]
    have h := congrArg (fun α ↦ α.app (op C.unop) f)
      ((Presheaf.freeAbelianSheafHomEquiv_apply _ (ψ j)).symm.trans h0)
    exact h
  rw [← ShortComplex.exact_iff_epi (ShortComplex.mk (Sigma.desc ψ) (0 : G ⟶ G) (by simp)) rfl,
    exact_iff_forall_exists_faithfullyFlat]
  intro C t _
  refine ⟨C, 𝟙 C, RingHom.FaithfullyFlat.of_bijective (by
    rw [ringHom_id]; exact Function.bijective_id), ?_⟩
  let c := e.functor.obj C
  let u : b c ≅ C := (hb c).some ≪≫ e.unitIso.symm.app C
  let j : J := ⟨c, G.obj.map u.inv t⟩
  refine ⟨(Sigma.ι (fun j : J ↦ Presheaf.freeAbelianSheafObj (Scheme.AffineEtale.topology (Spec A))
      (yoneda.obj (b j.1).unop)) j).hom.app C
    ((Presheaf.toFreeAbelianSheaf _ (yoneda.obj (b j.1).unop)).app (op C.unop) u.hom.unop), ?_⟩
  have hι := Sigma.ι_desc ψ j
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← InducedCategory.comp_hom, hι,
    hψ j C u.hom.unop]
  simp [j, ← ConcreteCategory.comp_apply, ← Functor.map_comp]

end EtaleCategory

end AlgebraicGeometry
