module

public import Weil.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Weil.Attr

/-!
# Étale sheaves are coequalizers of coproducts of representable sheaves

Let `B` be a big étale site containing a scheme `X`. Every étale sheaf of sets `H` on the small
étale site of `X` is the coequalizer, in the category of sheaves, of a pair of morphisms
`a, b : ∐_{α ∈ A} h_{Z_α} ⇉ ∐_{β ∈ B} h_{W_β}` between coproducts of representable sheaves.

One takes `B` to be the set of pairs `(W, s)` with `s ∈ H(W)`, and `p : ∐ h_W → H` the morphism
which is the Yoneda map of `s` on the summand `(W, s)`; it is an epimorphism of sheaves. Doing
the same for the kernel pair `R = C ×_H C` of `p` gives an epimorphism `q : ∐ h_Z → R`, and
`a, b` are `q` followed by the two projections. Since the category of sheaves of sets is a
regular category, the epimorphism `p` is effective, hence a coequalizer of its kernel pair, and
so of `(a, b)` because `q` is an epimorphism.

## Main results

* `CategoryTheory.GrothendieckTopology.epi_sigmaDesc_yonedaEquiv_symm`: for a subcanonical
  topology and a family of objects meeting every isomorphism class, the canonical map
  `∐_{(i, s)} yoneda (V i) ⟶ F` is an epimorphism of sheaves.
* `AlgebraicGeometry.SmallEtale.exists_epi_sigma_representableSheaf`: every étale sheaf of sets
  is a quotient of a coproduct of representable sheaves.
* `CategoryTheory.isColimitCoforkOfEffectiveEpiOfEpi`: an effective epimorphism `p` is a
  coequalizer of any pair `q ≫ fst, q ≫ snd` with `q` an epimorphism onto its kernel pair.
* `AlgebraicGeometry.SmallEtale.exists_isColimit_cofork_sigma_representableSheaf`: every étale
  sheaf of sets is a coequalizer of a pair of morphisms between coproducts of representable
  sheaves.

## Implementation notes

The étale site is the small étale site `AlgebraicGeometry.SmallEtale B X hX` (Stacks, Tag 021B);
the category `Et(X)` of noetherian separated étale `X`-schemes of Freitag–Kiehl is a full
subcategory of it. The small étale site is essentially small; the representatives of its
isomorphism classes indexing the coproducts are the objects of a small model of the site
(`CategoryTheory.equivSmallModel`). Instead of sheafifying a presheaf
coequalizer, the proof uses that epimorphisms of sheaves of sets are effective.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.2
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory

/-- If `p` is an effective epimorphism and `q` is an epimorphism onto the kernel pair of `p`,
then `p` is a coequalizer of `q ≫ fst` and `q ≫ snd`. -/
noncomputable def isColimitCoforkOfEffectiveEpiOfEpi {D : Type*} [Category D] {Y H W : D}
    (p : Y ⟶ H) [EffectiveEpi p] [HasPullback p p] (q : W ⟶ pullback p p) [Epi q] :
    IsColimit (Cofork.ofπ (f := q ≫ pullback.fst p p) (g := q ≫ pullback.snd p p) p
      (by simp [pullback.condition])) :=
  Cofork.IsColimit.mk' _ fun s ↦ by
    have hs : pullback.fst p p ≫ s.π = pullback.snd p p ≫ s.π :=
      (cancel_epi q).1 (by simpa using s.condition)
    refine ⟨EffectiveEpi.desc p s.π fun g₁ g₂ h ↦ ?_, EffectiveEpi.fac p _ _, fun hm ↦
      EffectiveEpi.uniq p _ _ _ hm⟩
    calc g₁ ≫ s.π = pullback.lift g₁ g₂ h ≫ pullback.fst p p ≫ s.π := by
          rw [pullback.lift_fst_assoc]
      _ = pullback.lift g₁ g₂ h ≫ pullback.snd p p ≫ s.π := by rw [hs]
      _ = g₂ ≫ s.π := by rw [pullback.lift_snd_assoc]

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]

/-- For a subcanonical topology `J` and a family of objects `V i` meeting every isomorphism
class, the map `∐_{(i, s)} yoneda (V i) ⟶ F`, indexed by the pairs of an index `i` and a section
`s ∈ F(V i)` and given on the summand `(i, s)` by the Yoneda map of `s`, is an epimorphism of
sheaves. -/
theorem epi_sigmaDesc_yonedaEquiv_symm {ι : Type w} (V : ι → C)
    (hV : ∀ U : C, ∃ i, Nonempty (U ≅ V i)) (F : Sheaf J (Type v))
    [HasCoproduct fun x : Σ i, F.obj.obj (op (V i)) ↦ J.yoneda.obj (V x.1)] :
    Epi (Sigma.desc fun x : Σ i, F.obj.obj (op (V i)) ↦ J.yonedaEquiv.symm x.2) := by
  refine ⟨fun {T} f g h ↦ ?_⟩
  ext U s
  obtain ⟨i, ⟨e⟩⟩ := hV U.unop
  have := congrArg J.yonedaEquiv
    (Sigma.ι (fun x : Σ i, F.obj.obj (op (V i)) ↦ J.yoneda.obj (V x.1)) ⟨i, F.obj.map e.inv.op s⟩
      ≫= h)
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app,
    yonedaEquiv_comp, Equiv.apply_symm_apply, NatTrans.naturality_apply] at this
  have h₂ := congrArg (T.obj.map e.hom.op) this
  simpa [← Functor.map_comp_apply, ← op_comp] using h₂

end GrothendieckTopology

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- Étale sheaves of sets on the small étale site of `X` have `u`-small coproducts. (This is
an instance of Mathlib, which instance search does not find within its default budget.) -/
instance (priority := high) hasColimitsOfShape_discrete_sheaf_type (A : Type u) :
    HasColimitsOfShape (Discrete A) (Sheaf (topology B X hX) (Type u)) :=
  Sheaf.instHasColimitsOfShape

/-- Every étale sheaf of sets `F` on the small étale site of `X` receives an epimorphism of
sheaves from a coproduct of representable sheaves `h_{V i}`, indexed by a `u`-small set. -/
theorem exists_epi_sigma_representableSheaf (F : Sheaf (topology B X hX) (Type u)) :
    ∃ (ι : Type u) (V : ι → SmallEtale B X hX)
      (π : (∐ fun i ↦ (representableSheaf B X hX).obj (V i)) ⟶ F), Epi π := by
  let E := equivSmallModel.{u} (SmallEtale B X hX)
  have hV : ∀ U, ∃ i, Nonempty (U ≅ E.inverse.obj i) :=
    fun U ↦ ⟨E.functor.obj U, ⟨E.unitIso.app U⟩⟩
  have := (topology B X hX).epi_sigmaDesc_yonedaEquiv_symm E.inverse.obj hV F
  let e : (∐ fun x : Σ i, F.obj.obj (op (E.inverse.obj i)) ↦
        (representableSheaf B X hX).obj (E.inverse.obj x.1)) ≅
      ∐ fun x : Σ i, F.obj.obj (op (E.inverse.obj i)) ↦
        (topology B X hX).yoneda.obj (E.inverse.obj x.1) :=
    Sigma.mapIso fun x ↦ (representableSheafIsoYoneda B X hX).app (E.inverse.obj x.1)
  refine ⟨Σ i, F.obj.obj (op (E.inverse.obj i)), fun x ↦ E.inverse.obj x.1,
    e.hom ≫ Sigma.desc fun x ↦ (topology B X hX).yonedaEquiv.symm x.2, ?_⟩
  exact epi_comp e.hom _

/-- **Étale sheaves are coequalizers of coproducts of representables.** For every étale sheaf
of sets `H` on the small étale site of `X`, there are sets `A, B'`, objects `Z α` (`α ∈ A`) and
`W β` (`β ∈ B'`) of the small étale site, morphisms of sheaves
`a, b : ∐_α h_{Z α} ⇉ ∐_β h_{W β}` and `p : ∐_β h_{W β} ⟶ H`, such that `p` is a coequalizer of
`(a, b)` in the category of étale sheaves (coproducts taken in sheaves). -/
@[weil "lem_fk102_sheaf_is_coequalizer_of_representables"]
theorem exists_isColimit_cofork_sigma_representableSheaf (H : Sheaf (topology B X hX) (Type u)) :
    ∃ (A B' : Type u) (Z : A → SmallEtale B X hX) (W : B' → SmallEtale B X hX)
      (a b : (∐ fun α ↦ (representableSheaf B X hX).obj (Z α)) ⟶
        ∐ fun β ↦ (representableSheaf B X hX).obj (W β))
      (p : (∐ fun β ↦ (representableSheaf B X hX).obj (W β)) ⟶ H) (w : a ≫ p = b ≫ p),
      Nonempty (IsColimit (Cofork.ofπ p w)) := by
  obtain ⟨ι, W, p, hp⟩ := exists_epi_sigma_representableSheaf B X hX H
  have : IsRegularEpi p := IsRegularEpiCategory.regularEpiOfEpi p
  obtain ⟨κ, Z, q, hq⟩ := exists_epi_sigma_representableSheaf B X hX (pullback p p)
  exact ⟨κ, ι, Z, W, q ≫ pullback.fst p p, q ≫ pullback.snd p p, p, _,
    ⟨isColimitCoforkOfEffectiveEpiOfEpi p q⟩⟩

end AlgebraicGeometry.SmallEtale

end
