module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import Weil.Attr

/-!
# Descent data on quasi-coherent sheaves along a single morphism

Let `f : T ⟶ S` be a morphism of schemes and `𝒩` a quasi-coherent `𝒪_T`-module. A descent
datum on `𝒩` with respect to `f` is an isomorphism `σ : p₁^* 𝒩 ≅ p₂^* 𝒩` of modules on
`T ×_S T` satisfying the cocycle condition `p₁₃^* σ = p₂₃^* σ ∘ p₁₂^* σ` on `T ×_S T ×_S T`.

We take for the category of such data the full subcategory
`AlgebraicGeometry.QuasicoherentDescentData` of Mathlib's `Pseudofunctor.DescentData`, for
the family consisting of `f` alone. Its objects carry transition isomorphisms over every
`S`-scheme mapping twice to `T`, rather than over a chosen fibre product. We show that the
presentation by a single isomorphism over a chosen fibre product, subject to the cocycle
condition over a chosen triple fibre product, yields such a datum, and conversely.

The identity `δ^* σ = 𝟙` along the diagonal is not part of the definition: it follows from
the cocycle condition because `σ` is an isomorphism. This is
`CategoryTheory.Pseudofunctor.DescentData'.pullHom'_self_eq_id_of_iso`, stated for an
arbitrary pseudofunctor and an arbitrary family.

## Main definitions

* `CategoryTheory.Pseudofunctor.DescentData'.ofIso`: a descent datum relative to chosen
  fibre products, from isomorphisms satisfying the cocycle condition alone.
* `CategoryTheory.Pseudofunctor.DescentData'.IsCocycle`: the cocycle condition
  `p₁₃^* σ = p₂₃^* σ ∘ p₁₂^* σ` for `σ : p₁^* N ⟶ p₂^* N` over a chosen fibre product.
* `CategoryTheory.Pseudofunctor.DescentData'.descentDataOfIsCocycle`: the descent datum
  relative to a single morphism given by such an isomorphism `σ`.
* `AlgebraicGeometry.QuasicoherentDescentDatum f`: descent data on quasi-coherent sheaves with
  respect to the single morphism `f : T ⟶ S`.
* `AlgebraicGeometry.QuasicoherentDescentDatum.mk'`: the descent datum `(𝒩, σ)` given by a
  quasi-coherent module `𝒩` and an isomorphism `σ : p₁^* 𝒩 ≅ p₂^* 𝒩` on a chosen fibre product
  satisfying the cocycle condition on a chosen triple fibre product.
* `AlgebraicGeometry.QuasicoherentDescentDatum.sigma`: the isomorphism `p₁^* 𝒩 ≅ p₂^* 𝒩` of
  a descent datum on a chosen fibre product.

## Main results

* `CategoryTheory.Pseudofunctor.DescentData'.pullHom'_self_eq_id_of_iso`: the cocycle
  condition for isomorphisms forces the diagonal condition.
* `AlgebraicGeometry.QuasicoherentDescentDatum.sigma_mk'`: the isomorphism of `mk' 𝒩 σ` is `σ`.
* `AlgebraicGeometry.QuasicoherentDescentDatum.isCocycle_sigma`: the isomorphism of every
  descent datum satisfies the cocycle condition `p₁₃^* σ = p₂₃^* σ ∘ p₁₂^* σ`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Opposite
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe t v' u' v u

namespace CategoryTheory.Pseudofunctor.DescentData'

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  {sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)}

/-- For transition morphisms that are isomorphisms, the cocycle condition over the chosen
triple fibre products implies that the transition morphisms restrict to the identity along the
diagonal. -/
lemma pullHom'_self_eq_id_of_iso {obj : ∀ i, F.obj (.mk (op (X i)))}
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (hom_comp : ∀ i₁ i₂ i₃ : ι,
      pullHom' (fun i j ↦ (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₂ ≫
        pullHom' (fun i j ↦ (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂
          (sq₃ i₁ i₂ i₃).p₃ =
      pullHom' (fun i j ↦ (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₃)
    (i : ι) :
    pullHom' (fun i j ↦ (hom i j).hom) (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _ := by
  set e := pullHom' (fun i j ↦ (hom i j).hom) (f i) (𝟙 (X i)) (𝟙 (X i))
  have hcomp : e ≫ e = e :=
    comp_pullHom'' (sq₃ := sq₃) _ hom_comp (f i) (𝟙 (X i)) (𝟙 (X i)) (𝟙 (X i))
      (by simp) (by simp) (by simp)
  have : IsIso e := by
    simp only [e, pullHom', pullHom]
    infer_instance
  rw [← cancel_mono e, hcomp, Category.id_comp]

/-- A descent datum relative to chosen binary and triple fibre products, given by transition
isomorphisms satisfying the cocycle condition; the diagonal condition is a consequence,
`pullHom'_self_eq_id_of_iso`. -/
@[simps]
noncomputable def ofIso (obj : ∀ i, F.obj (.mk (op (X i))))
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (hom_comp : ∀ i₁ i₂ i₃ : ι,
      pullHom' (fun i j ↦ (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₂ ≫
        pullHom' (fun i j ↦ (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂
          (sq₃ i₁ i₂ i₃).p₃ =
      pullHom' (fun i j ↦ (hom i j).hom) (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₃) :
    F.DescentData' sq sq₃ where
  obj := obj
  hom i j := (hom i j).hom
  pullHom'_hom_self := pullHom'_self_eq_id_of_iso hom hom_comp
  pullHom'_hom_comp := hom_comp

/-- For a single morphism, the cocycle condition on the chosen triple fibre product, in the
form of `pullHom'`, is the condition `p₁₃^* σ = p₂₃^* σ ∘ p₁₂^* σ` on the three projections. -/
lemma pullHom'_unit_cocycle_iff {X S : C} {f : X ⟶ S} (sq : ChosenPullback f f)
    (sq₃ : ChosenPullback₃ sq sq sq) {N : F.obj (.mk (op X))}
    (σ : (F.map sq.p₁.op.toLoc).toFunctor.obj N ⟶ (F.map sq.p₂.op.toLoc).toFunctor.obj N) :
    pullHom' (F := F) (f := fun _ : Unit ↦ f) (sq := fun _ _ ↦ sq) (obj := fun _ ↦ N)
          (obj' := fun _ ↦ N) (fun _ _ ↦ σ) sq₃.p (i₁ := ()) (i₂ := ()) sq₃.p₁ sq₃.p₂ ≫
        pullHom' (F := F) (f := fun _ : Unit ↦ f) (sq := fun _ _ ↦ sq) (obj := fun _ ↦ N)
          (obj' := fun _ ↦ N) (fun _ _ ↦ σ) sq₃.p (i₁ := ()) (i₂ := ()) sq₃.p₂ sq₃.p₃ =
      pullHom' (F := F) (f := fun _ : Unit ↦ f) (sq := fun _ _ ↦ sq) (obj := fun _ ↦ N)
          (obj' := fun _ ↦ N) (fun _ _ ↦ σ) sq₃.p (i₁ := ()) (i₂ := ()) sq₃.p₁ sq₃.p₃ ↔
    pullHom σ sq₃.p₁₂ sq₃.p₁ sq₃.p₂ ≫ pullHom σ sq₃.p₂₃ sq₃.p₂ sq₃.p₃ =
      pullHom σ sq₃.p₁₃ sq₃.p₁ sq₃.p₃ := by
  rw [pullHom'_eq_pullHom _ _ _ _ sq₃.p₁₂, pullHom'_eq_pullHom _ _ _ _ sq₃.p₂₃,
    pullHom'_eq_pullHom _ _ _ _ sq₃.p₁₃]

section Single

variable {X S : C} {f : X ⟶ S}

/-- The cocycle condition `p₁₃^* σ = p₂₃^* σ ∘ p₁₂^* σ` for a morphism `σ : p₁^* N ⟶ p₂^* N`
over a chosen fibre product `X ×_S X`, as an equality of morphisms `q₁^* N ⟶ q₃^* N` over a
chosen triple fibre product. -/
def IsCocycle (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)
    {N : F.obj (.mk (op X))}
    (σ : (F.map sq.p₁.op.toLoc).toFunctor.obj N ⟶ (F.map sq.p₂.op.toLoc).toFunctor.obj N) :
    Prop :=
  pullHom σ sq₃.p₁₂ sq₃.p₁ sq₃.p₂ ≫ pullHom σ sq₃.p₂₃ sq₃.p₂ sq₃.p₃ =
    pullHom σ sq₃.p₁₃ sq₃.p₁ sq₃.p₃

/-- For a single morphism, the cocycle condition in the form of `pullHom'` is `IsCocycle`. -/
lemma isCocycle_iff_pullHom' (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)
    {N : F.obj (.mk (op X))}
    (σ : (F.map sq.p₁.op.toLoc).toFunctor.obj N ⟶ (F.map sq.p₂.op.toLoc).toFunctor.obj N) :
    IsCocycle sq sq₃ σ ↔
      pullHom' (F := F) (f := fun _ : Unit ↦ f) (sq := fun _ _ ↦ sq) (obj := fun _ ↦ N)
          (obj' := fun _ ↦ N) (fun _ _ ↦ σ) sq₃.p (i₁ := ()) (i₂ := ()) sq₃.p₁ sq₃.p₂ ≫
        pullHom' (F := F) (f := fun _ : Unit ↦ f) (sq := fun _ _ ↦ sq) (obj := fun _ ↦ N)
          (obj' := fun _ ↦ N) (fun _ _ ↦ σ) sq₃.p (i₁ := ()) (i₂ := ()) sq₃.p₂ sq₃.p₃ =
      pullHom' (F := F) (f := fun _ : Unit ↦ f) (sq := fun _ _ ↦ sq) (obj := fun _ ↦ N)
          (obj' := fun _ ↦ N) (fun _ _ ↦ σ) sq₃.p (i₁ := ()) (i₂ := ()) sq₃.p₁ sq₃.p₃ := by
  rw [IsCocycle, pullHom'_eq_pullHom _ _ _ _ sq₃.p₁₂, pullHom'_eq_pullHom _ _ _ _ sq₃.p₂₃,
    pullHom'_eq_pullHom _ _ _ _ sq₃.p₁₃]

/-- The descent datum relative to the single morphism `f` given by an object `N` over `X` and
an isomorphism `σ : p₁^* N ≅ p₂^* N` over a chosen fibre product satisfying the cocycle
condition over a chosen triple fibre product. -/
noncomputable def descentDataOfIsCocycle (sq : ChosenPullback f f)
    (sq₃ : ChosenPullback₃ sq sq sq) (N : F.obj (.mk (op X)))
    (σ : (F.map sq.p₁.op.toLoc).toFunctor.obj N ≅ (F.map sq.p₂.op.toLoc).toFunctor.obj N)
    (hσ : IsCocycle sq sq₃ σ.hom) : F.DescentData (fun _ : Unit ↦ f) :=
  (ofIso (sq := fun _ _ ↦ sq) (sq₃ := fun _ _ _ ↦ sq₃) (fun _ ↦ N) (fun _ _ ↦ σ) (by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact (isCocycle_iff_pullHom' sq sq₃ σ.hom).1 hσ)).descentData

@[simp]
lemma descentDataOfIsCocycle_obj (sq : ChosenPullback f f)
    (sq₃ : ChosenPullback₃ sq sq sq) (N : F.obj (.mk (op X)))
    (σ : (F.map sq.p₁.op.toLoc).toFunctor.obj N ≅ (F.map sq.p₂.op.toLoc).toFunctor.obj N)
    (hσ : IsCocycle sq sq₃ σ.hom) (i : Unit) :
    (descentDataOfIsCocycle sq sq₃ N σ hσ).obj i = N := rfl

/-- The transition isomorphism of `descentDataOfIsCocycle sq sq₃ N σ hσ` over the chosen fibre
product is `σ`. -/
@[simp]
lemma descentDataOfIsCocycle_hom (sq : ChosenPullback f f)
    (sq₃ : ChosenPullback₃ sq sq sq) (N : F.obj (.mk (op X)))
    (σ : (F.map sq.p₁.op.toLoc).toFunctor.obj N ≅ (F.map sq.p₂.op.toLoc).toFunctor.obj N)
    (hσ : IsCocycle sq sq₃ σ.hom) :
    (descentDataOfIsCocycle sq sq₃ N σ hσ).hom sq.p (i₁ := ()) (i₂ := ()) sq.p₁ sq.p₂ =
      σ.hom :=
  pullHom'_p₁_p₂ (sq := fun _ _ ↦ sq) (fun _ _ ↦ σ.hom) () ()

/-- The transition isomorphism over a chosen fibre product of a descent datum relative to a
single morphism satisfies the cocycle condition. -/
lemma isCocycle_hom (D : F.DescentData (fun _ : Unit ↦ f)) (sq : ChosenPullback f f)
    (sq₃ : ChosenPullback₃ sq sq sq) :
    IsCocycle sq sq₃ (D.hom sq.p (i₁ := ()) (i₂ := ()) sq.p₁ sq.p₂) :=
  (isCocycle_iff_pullHom' sq sq₃ _).2
    ((ofDescentData (fun _ _ ↦ sq) (fun _ _ _ ↦ sq₃) D).pullHom'_hom_comp () () ())

end Single

end CategoryTheory.Pseudofunctor.DescentData'

namespace AlgebraicGeometry

/-- Descent data on quasi-coherent sheaves with respect to a morphism of schemes `f : T ⟶ S`:
a quasi-coherent `𝒪_T`-module `𝒩` together with an isomorphism `σ : p₁^* 𝒩 ≅ p₂^* 𝒩` on
`T ×_S T` satisfying the cocycle condition on `T ×_S T ×_S T`. The transition isomorphisms are
recorded over every `S`-scheme with two maps to `T`; `QuasicoherentDescentDatum.mk'` and
`QuasicoherentDescentDatum.sigma` pass to and from the presentation on chosen fibre
products. -/
@[weil "def_fka3_descent_datum_sheaf"]
abbrev QuasicoherentDescentDatum {T S : Scheme.{u}} (f : T ⟶ S) :=
  QuasicoherentDescentData (fun _ : Unit ↦ f)

namespace QuasicoherentDescentDatum

open Pseudofunctor.DescentData'

variable {T S : Scheme.{u}} {f : T ⟶ S}

/-- The quasi-coherent `𝒪_T`-module underlying a descent datum. -/
abbrev module (D : QuasicoherentDescentDatum f) : T.Modules := D.component ()

/-- The descent datum `(𝒩, σ)` given by a quasi-coherent module `𝒩` on `T` and an
isomorphism `σ : p₁^* 𝒩 ≅ p₂^* 𝒩` on a chosen fibre product `T ×_S T` satisfying the cocycle
condition on a chosen triple fibre product. -/
noncomputable def mk' (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)
    (N : T.Modules) [N.IsQuasicoherent]
    (σ : (modulePullbackPseudofunctor.map sq.p₁.op.toLoc).toFunctor.obj N ≅
      (modulePullbackPseudofunctor.map sq.p₂.op.toLoc).toFunctor.obj N)
    (hσ : IsCocycle sq sq₃ σ.hom) : QuasicoherentDescentDatum f where
  obj := descentDataOfIsCocycle sq sq₃ N σ hσ
  property _ := ‹N.IsQuasicoherent›

@[simp]
lemma module_mk' (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)
    (N : T.Modules) [N.IsQuasicoherent]
    (σ : (modulePullbackPseudofunctor.map sq.p₁.op.toLoc).toFunctor.obj N ≅
      (modulePullbackPseudofunctor.map sq.p₂.op.toLoc).toFunctor.obj N)
    (hσ : IsCocycle sq sq₃ σ.hom) : (mk' sq sq₃ N σ hσ).module = N := rfl

/-- The isomorphism `σ : p₁^* 𝒩 ≅ p₂^* 𝒩` of a descent datum, on a chosen fibre product
`T ×_S T`. -/
noncomputable def sigma (D : QuasicoherentDescentDatum f) (sq : ChosenPullback f f) :
    (modulePullbackPseudofunctor.map sq.p₁.op.toLoc).toFunctor.obj D.module ≅
      (modulePullbackPseudofunctor.map sq.p₂.op.toLoc).toFunctor.obj D.module :=
  D.obj.iso sq.p (i₁ := ()) (i₂ := ()) sq.p₁ sq.p₂

@[simp]
lemma sigma_hom (D : QuasicoherentDescentDatum f) (sq : ChosenPullback f f) :
    (D.sigma sq).hom = D.obj.hom sq.p (i₁ := ()) (i₂ := ()) sq.p₁ sq.p₂ := rfl

/-- The isomorphism of the descent datum `mk' 𝒩 σ` is `σ`. -/
@[simp]
lemma sigma_mk' (sq : ChosenPullback f f) (sq₃ : ChosenPullback₃ sq sq sq)
    (N : T.Modules) [N.IsQuasicoherent]
    (σ : (modulePullbackPseudofunctor.map sq.p₁.op.toLoc).toFunctor.obj N ≅
      (modulePullbackPseudofunctor.map sq.p₂.op.toLoc).toFunctor.obj N)
    (hσ : IsCocycle sq sq₃ σ.hom) : (mk' sq sq₃ N σ hσ).sigma sq = σ :=
  Iso.ext (descentDataOfIsCocycle_hom (F := modulePullbackPseudofunctor) sq sq₃ N σ hσ)

/-- The isomorphism of a descent datum satisfies the cocycle condition
`p₁₃^* σ = p₂₃^* σ ∘ p₁₂^* σ`. -/
lemma isCocycle_sigma (D : QuasicoherentDescentDatum f) (sq : ChosenPullback f f)
    (sq₃ : ChosenPullback₃ sq sq sq) : IsCocycle sq sq₃ (D.sigma sq).hom :=
  Pseudofunctor.DescentData'.isCocycle_hom D.obj sq sq₃

end QuasicoherentDescentDatum

end AlgebraicGeometry
