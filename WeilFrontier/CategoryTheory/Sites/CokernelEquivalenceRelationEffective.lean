module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Weil.Attr

/-!
# Equivalence relations in a category of sheaves of sets are effective

Let `u v : R ⟶ G` be morphisms of sheaves of types on a site `(C, J)` which represent an
equivalence relation: for every object `U`, the map `(u_U, v_U) : R(U) → G(U) × G(U)` is
injective and its image is an equivalence relation on `G(U)`. Let `c : G ⟶ H` be the cokernel
(coequalizer) of `u` and `v` in the category of sheaves. Then for sections `s t : G(U)` we have
`c_U s = c_U t` if and only if `(s, t) = (u_U r, v_U r)` for some `r : R(U)`.

The proof compares the coequalizer with the sheafification of the sectionwise quotient presheaf
`U ↦ G(U) / R(U)`: if `c_U s = c_U t`, then the classes of `s` and `t` have equal images in the
sheafification of that presheaf, hence agree locally, i.e. there is a covering sieve on `U`
over every arrow `f : V ⟶ U` of which `(s|_V, t|_V)` is the image of some `r_f : R(V)`. By
injectivity of `(u, v)` these sections are compatible, and they glue to `r : R(U)`; then
`(u_U r, v_U r) = (s, t)` because `G` is separated.

## Main definitions

* `CategoryTheory.Sheaf.pairQuotientPresheaf`: the presheaf `U ↦ G(U) / ~`, where `~` is the
  relation `s ~ t ↔ ∃ r, u_U r = s ∧ v_U r = t`.

## Main results

* `CategoryTheory.Sheaf.cofork_π_app_eq_iff_of_isColimit`: the statement for any colimit cofork
  of `u` and `v`.
* `CategoryTheory.Sheaf.coequalizer_π_app_eq_iff`: the statement for the chosen coequalizer.

## Implementation notes

The statement is proved for an arbitrary site whose sheafification of type-valued presheaves
is locally bijective (`GrothendieckTopology.WEqualsLocallyBijective`), which holds for
`Type (max u v)` on any site `C : Type u` with `Category.{v} C`; Freitag–Kiehl state it for the
étale site of a scheme. The coequalizer of the category of sheaves plays the role of the
cokernel of a pair of sheaf morphisms (the sheafification of the sectionwise coequalizer).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §4.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

variable {R G : Sheaf J (Type w)} (u v : R ⟶ G)

/-- The relation on `G(U)` given by the image of `(u_U, v_U) : R(U) → G(U) × G(U)`. -/
def PairRel (U : Cᵒᵖ) (s t : G.obj.obj U) : Prop :=
  ∃ r, u.hom.app U r = s ∧ v.hom.app U r = t

lemma pairRel_map {U V : Cᵒᵖ} (f : U ⟶ V) {s t : G.obj.obj U} (h : PairRel u v U s t) :
    PairRel u v V (G.obj.map f s) (G.obj.map f t) := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact ⟨R.obj.map f r, NatTrans.naturality_apply u.hom f r,
    NatTrans.naturality_apply v.hom f r⟩

/-- The presheaf `U ↦ G(U) / ~` of sectionwise quotients by the relation `PairRel u v U`. -/
def pairQuotientPresheaf : Cᵒᵖ ⥤ Type w where
  obj U := Quot (PairRel u v U)
  map f := TypeCat.ofHom (Quot.map (G.obj.map f) (fun _ _ h => pairRel_map u v f h))
  map_id U := by
    ext x
    induction x using Quot.ind
    exact congrArg (Quot.mk _) (Functor.map_id_apply G.obj _ _)
  map_comp f g := by
    ext x
    induction x using Quot.ind
    exact congrArg (Quot.mk _) (Functor.map_comp_apply G.obj f g _)

/-- The projection `G ⟶ pairQuotientPresheaf u v`. -/
def toPairQuotientPresheaf : G.obj ⟶ pairQuotientPresheaf u v where
  app U := TypeCat.ofHom (Quot.mk _)
  naturality U V f := by
    ext x
    rfl

lemma toPairQuotientPresheaf_app_apply (U : Cᵒᵖ) (s : G.obj.obj U) :
    (toPairQuotientPresheaf u v).app U s = Quot.mk _ s :=
  rfl

lemma condition_toPairQuotientPresheaf :
    u.hom ≫ toPairQuotientPresheaf u v = v.hom ≫ toPairQuotientPresheaf u v := by
  ext U r
  exact Quot.sound ⟨r, rfl, rfl⟩

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

/-- Equivalence relations in sheaves of types are effective, for an arbitrary colimit cofork:
if `(u, v) : R ⟶ G × G` is sectionwise injective with image a sectionwise equivalence
relation, and `c` is a coequalizer of `u` and `v`, then `c_U s = c_U t` if and only if
`(s, t) = (u_U r, v_U r)` for some section `r` of `R` over `U`. -/
theorem cofork_π_app_eq_iff_of_isColimit
    (hinj : ∀ U, Function.Injective (fun r : R.obj.obj U => (u.hom.app U r, v.hom.app U r)))
    (heqv : ∀ U, _root_.Equivalence (PairRel u v U))
    {c : Cofork u v} (hc : IsColimit c) {U : Cᵒᵖ} (s t : G.obj.obj U) :
    c.π.hom.app U s = c.π.hom.app U t ↔ ∃ r, u.hom.app U r = s ∧ v.hom.app U r = t := by
  constructor
  · intro h
    induction U using Opposite.rec with | op U => ?_
    let P := pairQuotientPresheaf u v
    let φ : G ⟶ (presheafToSheaf J (Type w)).obj P :=
      ObjectProperty.homMk (toPairQuotientPresheaf u v ≫ toSheafify J P)
    have hφ : u ≫ φ = v ≫ φ := by
      apply Sheaf.hom_ext
      change u.hom ≫ toPairQuotientPresheaf u v ≫ toSheafify J P =
        v.hom ≫ toPairQuotientPresheaf u v ≫ toSheafify J P
      rw [← Category.assoc, condition_toPairQuotientPresheaf, Category.assoc]
    let d := hc.desc (Cofork.ofπ φ hφ)
    have hd : c.π ≫ d = φ := hc.fac (Cofork.ofπ φ hφ) WalkingParallelPair.one
    have key : ∀ x, (toSheafify J P).app (op U) ((toPairQuotientPresheaf u v).app (op U) x) =
        d.hom.app (op U) (c.π.hom.app (op U) x) := fun x =>
      (congrArg (fun g : G ⟶ (presheafToSheaf J (Type w)).obj P => g.hom.app (op U) x) hd).symm
    have h1 := (key s).trans ((congrArg (d.hom.app (op U)) h).trans (key t).symm)
    let S := Presheaf.equalizerSieve (F := P) (X := op U)
      ((toPairQuotientPresheaf u v).app (op U) s) ((toPairQuotientPresheaf u v).app (op U) t)
    have hS : S ∈ J U := Presheaf.equalizerSieve_mem J (toSheafify J P) _ _ h1
    have hrel : ∀ ⦃V : C⦄ (f : V ⟶ U), S.arrows f →
        PairRel u v (op V) (G.obj.map f.op s) (G.obj.map f.op t) := by
      intro V f hf
      exact (heqv (op V)).eqvGen_iff.mp (Quot.eqvGen_exact hf)
    choose x hxu hxv using hrel
    have hx : Presieve.FamilyOfElements.Compatible (P := R.obj) (R := S.arrows) x := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
      apply hinj (op Z)
      simp only [Prod.mk.injEq]
      rw [NatTrans.naturality_apply u.hom g₁.op, NatTrans.naturality_apply u.hom g₂.op,
        NatTrans.naturality_apply v.hom g₁.op, NatTrans.naturality_apply v.hom g₂.op,
        hxu, hxu, hxv, hxv, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
      exact ⟨rfl, rfl⟩
    have hR := (isSheaf_iff_isSheaf_of_type J R.obj).1 R.property S hS
    have hG := ((isSheaf_iff_isSheaf_of_type J G.obj).1 G.property S hS).isSeparatedFor
    refine ⟨hR.amalgamate x hx, ?_, ?_⟩
    · refine hG.ext fun V f hf => ?_
      rw [← NatTrans.naturality_apply u.hom f.op, hR.valid_glue hx f hf, hxu]
    · refine hG.ext fun V f hf => ?_
      rw [← NatTrans.naturality_apply v.hom f.op, hR.valid_glue hx f hf, hxv]
  · rintro ⟨r, rfl, rfl⟩
    have := congrArg (fun φ => φ.hom.app U r) c.condition
    simpa using this

/-- **Equivalence relations in sheaves of types are effective** (Freitag–Kiehl I.4): if
`(u, v) : R ⟶ G × G` is sectionwise injective with image a sectionwise equivalence relation,
then two sections `s t` of `G` over `U` have the same image in the coequalizer of `u` and `v`
if and only if `(s, t) = (u_U r, v_U r)` for some section `r` of `R` over `U`. -/
@[weil "lem_fk104_cokernel_equivalence_relation_effective"]
theorem coequalizer_π_app_eq_iff [HasCoequalizer u v]
    (hinj : ∀ U, Function.Injective (fun r : R.obj.obj U => (u.hom.app U r, v.hom.app U r)))
    (heqv : ∀ U, _root_.Equivalence (PairRel u v U)) {U : Cᵒᵖ} (s t : G.obj.obj U) :
    (coequalizer.π u v).hom.app U s = (coequalizer.π u v).hom.app U t ↔
      ∃ r, u.hom.app U r = s ∧ v.hom.app U r = t :=
  cofork_π_app_eq_iff_of_isColimit u v hinj heqv (coequalizerIsCoequalizer u v) s t

end Sheaf

end CategoryTheory
