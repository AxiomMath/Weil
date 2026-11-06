module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Cech.CechCohomologyCovering
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CechProductMapExt
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Two refinements induce homotopic maps of Čech complexes

Let `𝔘 = (U_ν → U)_ν` and `𝔙 = (V_μ → U)_μ` be families of morphisms with target `U`, and let
`φ = (σ, (φ_ν))` and `ψ = (τ, (ψ_ν))` be two refinements `𝔘 ⟶ 𝔙`. For a presheaf `F`, the
induced cochain maps `φ^*, ψ^* : Č^•(𝔙, F) ⟶ Č^•(𝔘, F)` are homotopic. The homotopy is
`h^n : Č^n(𝔙, F) ⟶ Č^{n-1}(𝔘, F)`,
`h^n(s)_{ν₀ … ν_{n-1}} = ∑_k (-1)^k χ_k^* (s_{σν₀, …, σν_k, τν_k, …, τν_{n-1}})`,
where `χ_k = φ_{ν₀} × ⋯ × φ_{ν_k} × ψ_{ν_k} × ⋯ × ψ_{ν_{n-1}}`. Consequently, for a presheaf of
abelian groups and a cocycle `z ∈ Z^i(𝔙, F)`, `φ^* z - ψ^* z ∈ im d^{i-1}`, and `φ^* z = ψ^* z`
for `i = 0`.

## Main definitions

* `CategoryTheory.PreZeroHypercover.refinementSimplicialHomotopy`: the simplicial homotopy,
  in the opposite category, between the cosimplicial maps induced by two refinements.
* `CategoryTheory.PreZeroHypercover.cechComplexMapHomotopy`: the homotopy between the maps of
  Čech complexes induced by two refinements, for families in any category.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMapHomotopy`: the same
  homotopy for families of morphisms of `Et(S)`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMap_sub_mem_range`: for a
  cocycle `z ∈ Z^i(𝔙, F)`, `φ^* z - ψ^* z` lies in the image of `d^{i-1}`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMap_f_zero_eq`: for a
  `0`-cocycle `z`, `φ^* z = ψ^* z`.

## Implementation notes

The Čech complex `Č^•(𝔘, F)` is the alternating coface complex of the cosimplicial object
`F(𝔘_•)`, `𝔘_•` being the Čech nerve of `𝔘` in the category of formal coproducts. All the maps
involved (the cosimplicial structure maps, the maps `φ^*`, `ψ^*` and the homotopy operators) are
of one shape: the component at a tuple `ν` of a cochain of `𝔙` at a tuple whose `b`-th entry is
`ν_{c(b)}` taken through `φ` or `ψ`, restricted along the corresponding map of iterated fibre
products (`CategoryTheory.PreZeroHypercover.mixMap`). Composites of such maps are again of this
shape, so the simplicial identities defining a simplicial homotopy reduce to identities between
the functions `c` on finite ordinals. The individual terms `χ_k^*` of FK's formula are the
operators `h_k` of a simplicial homotopy in `Aᵒᵖ`, and the cancellation of terms in the
expansion of `d h + h d` is Mathlib's `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`.
The two refinements may be any morphisms of families over the identity of `U`, the index sets
need not be finite, the families need not be coverings, and the coefficients may lie in any
preadditive category with products.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe a w w' v' u' v u

namespace CategoryTheory.PreZeroHypercover

variable {C : Type u} [Category.{v} C] {U : C} {E : PreZeroHypercover.{w} U}
  {G : PreZeroHypercover.{w'} U} {κ : Type*} (φ : κ → E.Hom G)

/-- The tuple of indices of `G` obtained from a tuple `ν` of indices of `E` by a "mixing"
function `c`: its `b`-th entry is the image of `ν (c b).1` under the refinement `φ (c b).2`. -/
abbrev mixIndex {m n : ℕ} (c : Fin (m + 1) → Fin (n + 1) × κ) (ν : Fin (n + 1) → E.I₀) :
    Fin (m + 1) → G.I₀ :=
  fun b ↦ (φ (c b).2).s₀ (ν (c b).1)

/-- The component `U_i ⟶ V_{σ i}` of a refinement, as a morphism over `U`. -/
abbrev overHom (ψ : E.Hom G) (i : E.I₀) : Over.mk (E.f i) ⟶ Over.mk (G.f (ψ.s₀ i)) :=
  Over.homMk (ψ.h₀ i) (ψ.w₀ i)

variable [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]

/-- The morphism of iterated fibre products `U_ν ⟶ V_{mixIndex φ c ν}` whose `b`-th
component is the projection to `U_{ν (c b).1}` followed by `φ (c b).2`. -/
noncomputable def mixProd {m n : ℕ} (c : Fin (m + 1) → Fin (n + 1) × κ)
    (ν : Fin (n + 1) → E.I₀) :
    (∏ᶜ fun a ↦ Over.mk (E.f (ν a))) ⟶ ∏ᶜ fun b ↦ Over.mk (G.f (mixIndex φ c ν b)) :=
  Pi.lift fun b ↦ Pi.π (fun a ↦ Over.mk (E.f (ν a))) (c b).1 ≫
    overHom (φ (c b).2) (ν (c b).1)

@[reassoc (attr := simp)]
lemma mixProd_π {m n : ℕ} (c : Fin (m + 1) → Fin (n + 1) × κ) (ν : Fin (n + 1) → E.I₀)
    (b : Fin (m + 1)) :
    mixProd φ c ν ≫ Pi.π _ b = Pi.π (fun a ↦ Over.mk (E.f (ν a))) (c b).1 ≫
      overHom (φ (c b).2) (ν (c b).1) :=
  Pi.lift_π _ _

lemma mixProd_comp_reindex {m m' n : ℕ} (c : Fin (m + 1) → Fin (n + 1) × κ)
    (g : Fin (m' + 1) → Fin (m + 1)) (ν : Fin (n + 1) → E.I₀) :
    mixProd φ c ν ≫ Pi.lift (fun a ↦ Pi.π (fun b ↦ Over.mk (G.f (mixIndex φ c ν b))) (g a)) =
      mixProd φ (c ∘ g) ν := by
  refine Pi.hom_ext _ _ fun a ↦ ?_
  rw [Category.assoc, Pi.lift_π]
  exact (mixProd_π φ c ν (g a)).trans (mixProd_π φ (c ∘ g) ν a).symm

lemma reindex_comp_mixProd {m n n' : ℕ} (c : Fin (m + 1) → Fin (n' + 1) × κ)
    (g : Fin (n' + 1) → Fin (n + 1)) (ν : Fin (n + 1) → E.I₀) :
    Pi.lift (fun a ↦ Pi.π (fun b ↦ Over.mk (E.f (ν b))) (g a)) ≫ mixProd φ c (ν ∘ g) =
      mixProd φ (fun a ↦ (g (c a).1, (c a).2)) ν := by
  refine Pi.hom_ext _ _ fun a ↦ ?_
  rw [Category.assoc, mixProd_π]
  erw [Pi.lift_π_assoc]
  exact (mixProd_π φ (fun a ↦ (g (c a).1, (c a).2)) ν a).symm

variable {A : Type u'} [Category.{v'} A] (F : Cᵒᵖ ⥤ A)

section

variable (E)

/-- The factor `F(U_{ν₀} ×_U ⋯ ×_U U_{ν_n})` of the degree-`n` Čech cochains. -/
noncomputable abbrev cechFactor (n : ℕ) (ν : Fin (n + 1) → E.I₀) : A :=
  F.obj (op (∏ᶜ fun a ↦ Over.mk (E.f (ν a))).left)

variable [HasProducts.{w} A]

/-- The cosimplicial object of `A` whose alternating coface complex is the Čech complex
`Č^•(E, F)`. -/
noncomputable abbrev cechCosimplicial : CosimplicialObject A :=
  (FormalCoproduct.cosimplicialObjectFunctor.{w} (Stacks.CechSite.cechSimplicialObject E)).obj
    ((Over.forget U).op ⋙ F)

/-- The `n`-th term of `cechCosimplicial E F` is the product of the sections of `F` over the
iterated fibre products. -/
lemma cechCosimplicial_obj (n : ℕ) :
    (cechCosimplicial E F).obj ⦋n⦌ =
      ∏ᶜ cechFactor E F n :=
  rfl

/-- Reindexing of Čech cochains along a morphism `θ : ⦋m⦌ ⟶ ⦋n⦌` of the simplex category:
the coface and codegeneracy maps of `cechCosimplicial E F`. -/
noncomputable def reindexMap {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    ∏ᶜ cechFactor E F m ⟶ ∏ᶜ cechFactor E F n :=
  Pi.lift fun ν ↦ Pi.π (cechFactor E F m) (ν ∘ θ.toOrderHom) ≫
    F.map (Pi.lift fun a ↦ Pi.π (fun b ↦ Over.mk (E.f (ν b))) (θ.toOrderHom a)).left.op

@[reassoc (attr := simp)]
lemma reindexMap_π {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (ν : Fin (n + 1) → E.I₀) :
    reindexMap E F θ ≫ Pi.π (cechFactor E F n) ν =
      Pi.π (cechFactor E F m) (ν ∘ θ.toOrderHom) ≫
        F.map (Pi.lift fun a ↦ Pi.π (fun b ↦ Over.mk (E.f (ν b))) (θ.toOrderHom a)).left.op :=
  Pi.lift_π _ _

lemma cechCosimplicial_map {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (cechCosimplicial E F).map θ = reindexMap E F θ :=
  rfl

end

variable [HasProducts.{w} A] [HasProducts.{w'} A]

/-- The morphism `Č^m(G, F) ⟶ Č^n(E, F)` whose `ν`-component is the component of a cochain at
`mixIndex φ c ν`, restricted along `mixProd φ c ν`. -/
noncomputable def mixMap {m n : ℕ} (c : Fin (m + 1) → Fin (n + 1) × κ) :
    ∏ᶜ cechFactor G F m ⟶ ∏ᶜ cechFactor E F n :=
  Pi.lift fun ν : Fin (n + 1) → E.I₀ ↦
    Pi.π (cechFactor G F m) (mixIndex φ c ν) ≫ F.map (mixProd φ c ν).left.op

@[reassoc (attr := simp)]
lemma mixMap_π {m n : ℕ} (c : Fin (m + 1) → Fin (n + 1) × κ) (ν : Fin (n + 1) → E.I₀) :
    mixMap φ F c ≫ Pi.π (cechFactor E F n) ν =
      Pi.π (cechFactor G F m) (mixIndex φ c ν) ≫ F.map (mixProd φ c ν).left.op :=
  Pi.lift_π _ _

lemma reindexMap_comp_mixMap {m m' n : ℕ} (θ : ⦋m'⦌ ⟶ ⦋m⦌)
    (c : Fin (m + 1) → Fin (n + 1) × κ) :
    reindexMap G F θ ≫ mixMap φ F c = mixMap φ F (c ∘ θ.toOrderHom) := by
  refine Pi.hom_ext _ _ fun ν ↦ ?_
  rw [Category.assoc, mixMap_π]
  erw [reindexMap_π_assoc]
  rw [mixMap_π, ← F.map_comp, ← op_comp, ← Over.comp_left, mixProd_comp_reindex]
  rfl

lemma mixMap_comp_reindexMap {m n n' : ℕ} (c : Fin (m + 1) → Fin (n + 1) × κ)
    (θ : ⦋n⦌ ⟶ ⦋n'⦌) :
    mixMap φ F c ≫ reindexMap E F θ =
      mixMap φ F (fun a ↦ (θ.toOrderHom (c a).1, (c a).2)) := by
  refine Pi.hom_ext _ _ fun ν ↦ ?_
  rw [Category.assoc, reindexMap_π, mixMap_π_assoc, mixMap_π, ← F.map_comp,
    ← op_comp, ← Over.comp_left]
  erw [reindex_comp_mixProd]
  rfl

variable (κ) in
/-- The cosimplicial morphism `cechCosimplicial G F ⟶ cechCosimplicial E F` induced by the
refinement `φ k`. -/
@[simps]
noncomputable def refinementCosimplicialHom (k : κ) :
    cechCosimplicial G F ⟶ cechCosimplicial E F where
  app X := mixMap φ F (m := X.len) (n := X.len) (fun a ↦ (a, k))
  naturality X Y θ := by
    change reindexMap G F θ ≫ mixMap φ F _ = mixMap φ F _ ≫ reindexMap E F θ
    rw [reindexMap_comp_mixMap, mixMap_comp_reindexMap]
    rfl


end CategoryTheory.PreZeroHypercover

namespace Fin

/-- The value of `i.succAbove a` as a natural number. -/
lemma val_succAbove_eq_ite {n : ℕ} (i : Fin (n + 1)) (a : Fin n) :
    (i.succAbove a : ℕ) = if (a : ℕ) < i then (a : ℕ) else (a : ℕ) + 1 := by
  unfold Fin.succAbove; split_ifs <;> simp_all [Fin.lt_def]

/-- The value of `j.predAbove k` as a natural number. -/
lemma val_predAbove_eq_ite {n : ℕ} (j : Fin n) (k : Fin (n + 1)) :
    (j.predAbove k : ℕ) = if (j : ℕ) < k then (k : ℕ) - 1 else (k : ℕ) := by
  unfold Fin.predAbove
  rcases lt_or_ge (j : ℕ) k with h | h
  · have h' : j.castSucc < k := by simpa [Fin.lt_def] using h
    simp [h, h']
  · have h' : ¬ j.castSucc < k := by simpa [Fin.lt_def] using h
    simp [h', show ¬ (j : ℕ) < k by omega]

end Fin

namespace SimplexCategory

private lemma δ_toOrderHom_apply {n : ℕ} (i : Fin (n + 2)) (a : Fin (n + 1)) :
    (δ i).toOrderHom a = i.succAbove a :=
  rfl

private lemma σ_toOrderHom_apply {n : ℕ} (i : Fin (n + 1)) (a : Fin (n + 2)) :
    (σ i).toOrderHom a = i.predAbove a :=
  rfl

end SimplexCategory

namespace CategoryTheory.PreZeroHypercover

/-- The mixing function of the `j`-th homotopy operator: the `k`-th entry of
`(σ ν₀, …, σ ν_j, τ ν_j, …, τ ν_n)` is `ν (j.predAbove k)` taken through `σ` (`true`) when
`k ≤ j` and through `τ` (`false`) otherwise. -/
def homotopyMix {n : ℕ} (j : Fin (n + 1)) (k : Fin (n + 2)) : Fin (n + 1) × Bool :=
  (j.predAbove k, decide (k ≤ j.castSucc))

/-- Closes identities between functions on `Fin` built from `succAbove` and `predAbove`. -/
local macro "fin_tac" : tactic => `(tactic| (
  simp only [homotopyMix, Function.comp_apply, SimplexCategory.δ_toOrderHom_apply,
    SimplexCategory.σ_toOrderHom_apply, Prod.mk.injEq, Fin.ext_iff, Fin.val_succAbove_eq_ite,
    Fin.val_predAbove_eq_ite, Fin.lt_def, Fin.le_def, decide_eq_decide, Fin.val_castSucc,
    Fin.val_succ, Fin.val_last, Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.decide_eq_false, Bool.decide_eq_true, Bool.not_eq_true'] at *
  split_ifs <;> omega))

variable {C : Type u} [Category.{v} C] {U : C} {E : PreZeroHypercover.{w} U}
  {G : PreZeroHypercover.{w'} U}
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [HasProducts.{w'} A] (F : Cᵒᵖ ⥤ A)
  (φ ψ : E.Hom G)

/-- The two refinements `φ, ψ` as a family indexed by `Bool`. -/
abbrev pairFamily : Bool → E.Hom G := fun b ↦ cond b φ ψ

/-- **The simplicial homotopy between two refinements.** In the opposite category, the
cosimplicial maps induced by `φ` and `ψ` are simplicially homotopic; the `j`-th homotopy
operator in degree `n` restricts the component at `(σ ν₀, …, σ ν_j, τ ν_j, …, τ ν_n)`. -/
noncomputable def refinementSimplicialHomotopy :
    SimplicialObject.Homotopy
      ((cosimplicialSimplicialEquiv A).functor.map
        (refinementCosimplicialHom Bool (pairFamily φ ψ) F true).op)
      ((cosimplicialSimplicialEquiv A).functor.map
        (refinementCosimplicialHom Bool (pairFamily φ ψ) F false).op) where
  h j := (mixMap (pairFamily φ ψ) F (homotopyMix j)).op
  h_zero_comp_δ_zero n := by
    apply Quiver.Hom.unop_inj
    change reindexMap G F (SimplexCategory.δ 0) ≫ mixMap (pairFamily φ ψ) F (homotopyMix 0) =
      mixMap (pairFamily φ ψ) F (fun a : Fin (n + 1) ↦ (a, false))
    rw [reindexMap_comp_mixMap]
    congr 1
  h_last_comp_δ_last n := by
    apply Quiver.Hom.unop_inj
    change reindexMap G F (SimplexCategory.δ (Fin.last (n + 1))) ≫
        mixMap (pairFamily φ ψ) F (homotopyMix (Fin.last n)) =
      mixMap (pairFamily φ ψ) F (fun a : Fin (n + 1) ↦ (a, true))
    rw [reindexMap_comp_mixMap]
    congr 1
    funext a
    fin_tac
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply Quiver.Hom.unop_inj
    change reindexMap G F (SimplexCategory.δ i.castSucc) ≫
        mixMap (pairFamily φ ψ) F (homotopyMix j.succ) =
      mixMap (pairFamily φ ψ) F (homotopyMix j) ≫ reindexMap E F (SimplexCategory.δ i)
    rw [reindexMap_comp_mixMap, mixMap_comp_reindexMap]
    congr 1
    funext a
    fin_tac
  h_succ_comp_δ_castSucc_succ j := by
    apply Quiver.Hom.unop_inj
    change reindexMap G F (SimplexCategory.δ j.castSucc.succ) ≫
        mixMap (pairFamily φ ψ) F (homotopyMix j.succ) =
      reindexMap G F (SimplexCategory.δ j.castSucc.succ) ≫
        mixMap (pairFamily φ ψ) F (homotopyMix j.castSucc)
    rw [reindexMap_comp_mixMap, reindexMap_comp_mixMap]
    congr 1
    funext a
    fin_tac
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply Quiver.Hom.unop_inj
    change reindexMap G F (SimplexCategory.δ i.succ) ≫
        mixMap (pairFamily φ ψ) F (homotopyMix j.castSucc) =
      mixMap (pairFamily φ ψ) F (homotopyMix j) ≫ reindexMap E F (SimplexCategory.δ i)
    rw [reindexMap_comp_mixMap, mixMap_comp_reindexMap]
    congr 1
    funext a
    fin_tac
  h_comp_σ_castSucc_of_le i j hij := by
    apply Quiver.Hom.unop_inj
    change reindexMap G F (SimplexCategory.σ i.castSucc) ≫
        mixMap (pairFamily φ ψ) F (homotopyMix j) =
      mixMap (pairFamily φ ψ) F (homotopyMix j.succ) ≫ reindexMap E F (SimplexCategory.σ i)
    rw [reindexMap_comp_mixMap, mixMap_comp_reindexMap]
    congr 1
    funext a
    fin_tac
  h_comp_σ_succ_of_lt i j hji := by
    apply Quiver.Hom.unop_inj
    change reindexMap G F (SimplexCategory.σ i.succ) ≫ mixMap (pairFamily φ ψ) F (homotopyMix j) =
      mixMap (pairFamily φ ψ) F (homotopyMix j.castSucc) ≫ reindexMap E F (SimplexCategory.σ i)
    rw [reindexMap_comp_mixMap, mixMap_comp_reindexMap]
    congr 1
    funext a
    fin_tac

section Preadditive

variable [Preadditive A]

omit [HasProducts.{w'} A] in
variable (E) in
/-- The Čech differential is the opposite of the differential of the alternating face complex
of the simplicial object of `Aᵒᵖ` opposite to `cechCosimplicial E F`. -/
lemma cechComplex_d_eq_unop (i j : ℕ) :
    (Stacks.CechSite.cechComplex E F).d i j =
      (((AlgebraicTopology.alternatingFaceMapComplex Aᵒᵖ).obj
        ((cosimplicialSimplicialEquiv A).functor.obj (op (cechCosimplicial E F)))).d j i).unop := by
  by_cases h : i + 1 = j
  · subst h
    change (AlgebraicTopology.AlternatingCofaceMapComplex.obj (cechCosimplicial E F)).d i
      (i + 1) = _
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.alternatingFaceMapComplex_obj_d]
    exact AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d _ i
  · rw [HomologicalComplex.shape _ i j (by simpa using h),
      HomologicalComplex.shape _ j i (by simpa using h)]
    rfl

/-- The cochain map of the refinement `φ k` is `mixMap φ F (fun a ↦ (a, k))` in each degree. -/
lemma cechComplexMap_f_eq_mixMap {κ : Type*} (φ : κ → E.Hom G) (k : κ) (n : ℕ) :
    (Stacks.CechSite.cechComplexMap E G ((homOverIdEquivHom E G).symm (φ k)) F).f n =
      mixMap φ F (fun a : Fin (n + 1) ↦ (a, k)) := by
  refine Pi.hom_ext (f := cechFactor E F n) _ _ fun ν ↦ ?_
  refine (Stacks.CechSite.cechComplexMap_f_Pi_π E G ((homOverIdEquivHom E G).symm (φ k)) F n
    ν).trans (Eq.trans ?_ (mixMap_π φ F (fun a : Fin (n + 1) ↦ (a, k)) ν).symm)
  congr 1
  refine congrArg (fun t ↦ F.map t.op)
    (Stacks.CechSite.eq_cechProductMap E G _ n ν _ fun b ↦ ?_).symm
  exact (Over.comp_left _ _ _ _ _).symm.trans
    (congrArg Over.Hom.left (mixProd_π φ (fun a ↦ (a, k)) ν b))

/-- The homotopy operators `h^j : Č^j(𝔙, F) ⟶ Č^i(𝔘, F)` between the cochain maps of two
refinements, deduced from `refinementSimplicialHomotopy`. -/
noncomputable def cechComplexMapHomotopyHom (i j : ℕ) :
    (Stacks.CechSite.cechComplex G F).X i ⟶ (Stacks.CechSite.cechComplex E F).X j :=
  ((refinementSimplicialHomotopy F φ ψ).toChainHomotopy.hom j i).unop

/-- **Two refinements induce homotopic maps of Čech complexes.** For two refinements
`φ, ψ : 𝔘 ⟶ 𝔙` of families with target `U`, the cochain maps `φ^*, ψ^* : Č^•(𝔙, F) ⟶ Č^•(𝔘, F)`
are homotopic. -/
noncomputable def cechComplexMapHomotopy :
    Homotopy (Stacks.CechSite.cechComplexMap E G ((homOverIdEquivHom E G).symm φ) F)
      (Stacks.CechSite.cechComplexMap E G ((homOverIdEquivHom E G).symm ψ) F) where
  hom := cechComplexMapHomotopyHom F φ ψ
  zero i j hij := by
    rw [cechComplexMapHomotopyHom,
      (refinementSimplicialHomotopy F φ ψ).toChainHomotopy.zero j i (by simpa using hij)]
    rfl
  comm n := by
    have h := congrArg Quiver.Hom.unop
      ((refinementSimplicialHomotopy F φ ψ).toChainHomotopy.comm n)
    have e₁ : (Stacks.CechSite.cechComplexMap E G ((homOverIdEquivHom E G).symm φ) F).f n =
        mixMap (pairFamily φ ψ) F (fun a : Fin (n + 1) ↦ (a, true)) :=
      cechComplexMap_f_eq_mixMap F (pairFamily φ ψ) true n
    have e₂ : (Stacks.CechSite.cechComplexMap E G ((homOverIdEquivHom E G).symm ψ) F).f n =
        mixMap (pairFamily φ ψ) F (fun a : Fin (n + 1) ↦ (a, false)) :=
      cechComplexMap_f_eq_mixMap F (pairFamily φ ψ) false n
    rcases n with _ | m
    · rw [dNext_eq_zero _ 0 (by simp), prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl),
        zero_add, unop_add, unop_comp] at h
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel 0 1 from rfl), prevD_eq_zero _ 0 (by simp),
        add_zero, cechComplex_d_eq_unop G F 0 1]
      exact e₁.trans (h.trans (congrArg₂ (· + ·) rfl e₂.symm))
    · rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (m + 2) (m + 1) from rfl),
        unop_add, unop_add, unop_comp, unop_comp] at h
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel (m + 1) (m + 2) from rfl),
        prevD_eq _ (show (ComplexShape.up ℕ).Rel m (m + 1) from rfl),
        cechComplex_d_eq_unop G F (m + 1) (m + 2), cechComplex_d_eq_unop E F m (m + 1)]
      exact e₁.trans (h.trans (congrArg₂ (· + ·) (add_comm _ _) e₂.symm))

end Preadditive

end CategoryTheory.PreZeroHypercover

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : SmallNoetherianSeparatedEtale B S hS}
  {E : PreZeroHypercover.{w} U} {G : PreZeroHypercover.{w'} U}

/-- **The cochain maps of two refinements are homotopic.** For two refinements
`φ, ψ : 𝔘 ⟶ 𝔙` of families of morphisms of `Et(S)` with target `U` and a presheaf `F` on
`Et(S)`, the cochain maps `φ^*, ψ^* : Č^•(𝔙, F) ⟶ Č^•(𝔘, F)` are homotopic:
`φ^* - ψ^* = d ∘ h + h ∘ d`. -/
noncomputable def refinementCochainMapHomotopy {A : Type u'} [Category.{v'} A] [Preadditive A]
    [HasProducts.{w} A] [HasProducts.{w'} A] (φ ψ : E.Hom G) (F : EtalePresheaf B S hS A) :
    Homotopy (refinementCochainMap φ F) (refinementCochainMap ψ F) :=
  PreZeroHypercover.cechComplexMapHomotopy F φ ψ

section AddCommGrp

variable [HasProducts.{w} AddCommGrpCat.{a}] [HasProducts.{w'} AddCommGrpCat.{a}]
  (φ ψ : E.Hom G) (F : EtalePresheaf B S hS AddCommGrpCat.{a})

/-- **Two refinements agree on cocycles up to coboundaries.** For two refinements
`φ, ψ : 𝔘 ⟶ 𝔙` of families of morphisms of `Et(S)` with target `U`, a presheaf of abelian groups
`F` and a cocycle `z ∈ Z^i(𝔙, F)`, the difference `φ^* z - ψ^* z` lies in the image of the
differential `d^{i-1}` of `Č^•(𝔘, F)`. -/
@[weil "lem_fk102_cech_refinement_maps_homotopic"]
theorem refinementCochainMap_sub_mem_range {i : ℕ} {z : (cechComplex G F).X i}
    (hz : z ∈ cechCycles G F i) :
    (refinementCochainMap φ F).f i z - (refinementCochainMap ψ F).f i z ∈
      ((cechComplex E F).d (i - 1) i).hom.range := by
  have hc := ConcreteCategory.congr_hom ((refinementCochainMapHomotopy φ ψ F).comm i) z
  rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel i (i + 1) from rfl), AddCommGrpCat.hom_add_apply,
    AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply,
    show (cechComplex G F).d i (i + 1) z = 0 from hz, map_zero, zero_add] at hc
  rw [hc, add_sub_cancel_right]
  rcases i with _ | m
  · rw [prevD_eq_zero _ 0 (by simp)]
    exact zero_mem _
  · rw [prevD_eq _ (show (ComplexShape.up ℕ).Rel m (m + 1) from rfl), ConcreteCategory.comp_apply]
    exact ⟨_, rfl⟩

/-- **Two refinements agree on `0`-cocycles.** For two refinements `φ, ψ : 𝔘 ⟶ 𝔙` and a
`0`-cocycle `z ∈ Z^0(𝔙, F)`, `φ^* z = ψ^* z`. -/
@[weil "lem_fk102_cech_refinement_maps_homotopic"]
theorem refinementCochainMap_f_zero_eq {z : (cechComplex G F).X 0} (hz : z ∈ cechCycles G F 0) :
    (refinementCochainMap φ F).f 0 z = (refinementCochainMap ψ F).f 0 z := by
  have h := refinementCochainMap_sub_mem_range φ ψ F hz
  rw [← cechBoundaries_eq_range, cechBoundaries_zero, AddSubgroup.mem_bot] at h
  exact sub_eq_zero.mp h

end AddCommGrp

end AlgebraicGeometry.SmallNoetherianSeparatedEtale
