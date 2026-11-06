module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.GaloisActionOnStalk
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.GroupTheory.Index

/-!
# The Galois stalk is a discrete Galois module

Let `K` be a field, `Ω` an extension field of `K` (in the source, a separable closure `K̄`) and
`G = Aut_K(Ω)` with its Krull topology. For a presheaf `F` of abelian groups on `Et(K)`, the group
`G` acts on the Galois stalk `F(Ω)` by group automorphisms, `σ · [s] = [F(σ|_L)(s)]`. This action
is discrete: for `x = [s]` with `s ∈ F(L)`, every `σ` fixing `L` pointwise fixes `x`, so the
stabilizer of `x` contains the open subgroup `Aut_L(Ω)` of `G`; hence it is open. It also has
finite index, since the cosets of `Aut_L(Ω)` inject into the finite set of `K`-embeddings
`L → Ω`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.instDistribMulActionGaloisStalk`: the action of
  `Aut_K(Ω)` on `F(Ω)` by additive automorphisms.

## Main results

- `AlgebraicGeometry.EtaleCategory.fixingSubgroup_le_stabilizer_galoisStalkι`: `Aut_L(Ω)` fixes
  every `[s]` with `s ∈ F(L)`.
- `AlgebraicGeometry.EtaleCategory.isOpen_stabilizer_galoisStalk`: stabilizers are open.
- `AlgebraicGeometry.EtaleCategory.finiteIndex_stabilizer_galoisStalk`: stabilizers have finite
  index.

## Implementation notes

The extension `Ω` is arbitrary; the source's case is `Ω = K̄`. Finiteness of the index is
proved without compactness of `Aut_K(Ω)` (which needs `Ω / K` algebraic), from the finiteness of
the set of `K`-algebra maps from a finite extension `L` to `Ω`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace EtaleCategory

open GaloisStalkIndex

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- An automorphism fixing `L` pointwise acts trivially on the image of `F(L)` in `F(Ω)`. -/
lemma galoisStalkι_galoisStalkAction_of_mem_fixingSubgroup {C : Type*} [Category C]
    [HasColimitsOfShape (GaloisStalkIndex K Ω) C] (F : Presheaf (CommRingCat.of K) C)
    (L : GaloisStalkIndex K Ω) {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ L.field.fixingSubgroup) :
    galoisStalkι Ω F L ≫ galoisStalkAction σ F = galoisStalkι Ω F L := by
  have hfix : ∀ x : L.field, σ x = x := fun x ↦ hσ x
  have hle : map σ L ≤ L := by
    rw [le_iff, field_map]
    rintro _ ⟨y, hy, rfl⟩
    have := hfix ⟨y, hy⟩
    change σ y ∈ L.field
    rw [this]
    exact hy
  rw [galoisStalkι_galoisStalkAction, ← map_galoisStalkι Ω F (homOfLE hle),
    ← Functor.map_comp_assoc, restrictHom, toEtaleCategory_map_eq_etaleHom, etaleHom_comp]
  convert (Category.id_comp (galoisStalkι Ω F L))
  convert F.map_id _
  rw [← etaleHom_id]
  congr 1
  ext x
  exact hfix x

section AddCommGrp

variable (F : Presheaf (CommRingCat.of K) AddCommGrpCat.{u})

/-- **The Galois action on the Galois stalk**, as an action of `Aut_K(Ω)` on `F(Ω)` by additive
automorphisms: `σ • x = galoisStalkAction σ F x`. -/
@[weil "lem_fk101_galois_action_continuous"]
instance instDistribMulActionGaloisStalk :
    DistribMulAction (Ω ≃ₐ[K] Ω) (galoisStalk Ω F : AddCommGrpCat.{u}) where
  smul σ x := galoisStalkAction σ F x
  one_smul x := by
    change galoisStalkAction 1 F x = x
    rw [galoisStalkAction_one]
    rfl
  mul_smul σ τ x := by
    change galoisStalkAction (σ * τ) F x = galoisStalkAction σ F (galoisStalkAction τ F x)
    rw [galoisStalkAction_mul]
    rfl
  smul_zero σ := map_zero (galoisStalkAction σ F).hom
  smul_add σ x y := map_add (galoisStalkAction σ F).hom x y

lemma galoisStalk_smul_def (σ : Ω ≃ₐ[K] Ω) (x : (galoisStalk Ω F : AddCommGrpCat.{u})) :
    σ • x = galoisStalkAction σ F x := rfl

/-- `Aut_L(Ω)` fixes every element `[s]` with `s ∈ F(L)`. -/
lemma fixingSubgroup_le_stabilizer_galoisStalkι (L : GaloisStalkIndex K Ω)
    (s : F.obj ((toEtaleCategory K Ω).obj L)) :
    L.field.fixingSubgroup ≤ MulAction.stabilizer (Ω ≃ₐ[K] Ω) (galoisStalkι Ω F L s) := by
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff, galoisStalk_smul_def]
  exact ConcreteCategory.congr_hom
    (galoisStalkι_galoisStalkAction_of_mem_fixingSubgroup F L hσ) s

/-- The fixing subgroup of a finite-dimensional intermediate field has finite index in
`Aut_K(Ω)`: its left cosets inject into the finite set of `K`-algebra maps `L → Ω`. -/
lemma _root_.IntermediateField.finiteIndex_fixingSubgroup (E : IntermediateField K Ω)
    [FiniteDimensional K E] : E.fixingSubgroup.FiniteIndex := by
  let f : (Ω ≃ₐ[K] Ω) ⧸ E.fixingSubgroup → (E →ₐ[K] Ω) :=
    Quotient.lift (fun σ ↦ (σ : Ω →ₐ[K] Ω).comp E.val) (fun σ τ h ↦ by
      have h' : σ⁻¹ * τ ∈ E.fixingSubgroup := QuotientGroup.leftRel_apply.mp h
      ext x
      have hx : (σ⁻¹ * τ) x = x := h' x
      change σ x = τ x
      rw [AlgEquiv.mul_apply] at hx
      rw [← congrArg σ hx]
      exact AlgEquiv.apply_symm_apply σ _)
  have hf : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rename_i σ τ
    rw [QuotientGroup.eq]
    intro x
    have h := DFunLike.congr_fun hab x
    change σ x = τ x at h
    change (σ⁻¹ * τ) x = x
    rw [AlgEquiv.mul_apply, ← h]
    exact σ.symm_apply_apply x
  have : Finite ((Ω ≃ₐ[K] Ω) ⧸ E.fixingSubgroup) := Finite.of_injective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **The Galois stalk is a discrete module**: the stabilizer of every element of `F(Ω)` is open
in the Krull topology of `Aut_K(Ω)`. -/
@[weil "lem_fk101_galois_action_continuous"]
theorem isOpen_stabilizer_galoisStalk (x : (galoisStalk Ω F : AddCommGrpCat.{u})) :
    IsOpen (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x : Set (Ω ≃ₐ[K] Ω)) := by
  obtain ⟨L, s, rfl⟩ := galoisStalk_exists_rep Ω F x
  exact Subgroup.isOpen_mono (fixingSubgroup_le_stabilizer_galoisStalkι F L s)
    L.field.fixingSubgroup_isOpen

/-- The stabilizer of every element of `F(Ω)` has finite index in `Aut_K(Ω)`. -/
@[weil "lem_fk101_galois_action_continuous"]
theorem finiteIndex_stabilizer_galoisStalk (x : (galoisStalk Ω F : AddCommGrpCat.{u})) :
    (MulAction.stabilizer (Ω ≃ₐ[K] Ω) x).FiniteIndex := by
  obtain ⟨L, s, rfl⟩ := galoisStalk_exists_rep Ω F x
  have := L.field.finiteIndex_fixingSubgroup
  exact Subgroup.finiteIndex_of_le (fixingSubgroup_le_stabilizer_galoisStalkι F L s)

end AddCommGrp

end EtaleCategory

end AlgebraicGeometry
