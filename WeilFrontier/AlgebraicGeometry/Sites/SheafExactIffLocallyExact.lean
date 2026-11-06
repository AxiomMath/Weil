module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleSheaf
public import StacksFrontier.CategoryTheory.Sites.AbelianSheavesAbelian

/-!
# Exactness of sequences of abelian sheaves on the étale category

Let `A` be a commutative ring and let `F ⟶ G ⟶ H` be morphisms of sheaves of abelian groups on
the étale category `Et(A)` with zero composite. The sequence is exact in the abelian category of
sheaves if and only if every section `s` of `G` over an object `B` killed by `G ⟶ H` becomes,
after pulling back along a single faithfully flat morphism `B ⟶ C` of `Et(A)`, the image of a
section of `F` over `C`.

## Main results

- `AlgebraicGeometry.EtaleCategory.exact_iff_forall_exists_faithfullyFlat`: the exactness
  criterion above.

## Implementation notes

The proof starts from the general criterion that a complex of abelian sheaves on a site is
exact if and only if every section of the middle term killed by the second map lifts along the
arrows of some covering sieve. A covering sieve of `Et(A)` contains a finite covering family
`(gᵢ : B ⟶ Cᵢ)ᵢ`, and the induced morphism `B ⟶ ∏ᵢ Cᵢ` is faithfully flat; since sheaves take
finite products in `Et(A)` to products, the local lifts glue to a lift over `∏ᵢ Cᵢ`.
Conversely, a faithfully flat morphism is a one-member covering.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

/-- **Exactness of sheaves on `Et(A)` is local for faithfully flat morphisms** [FK, I.1].
A sequence `F ⟶ G ⟶ H` of sheaves of abelian groups on `Et(A)` with zero composite is exact if
and only if for every object `B` and every section `s` of `G` over `B` killed by `β`, there is a
faithfully flat morphism `g : B ⟶ C` of `Et(A)` such that `G(g)(s)` lies in the image of `α`
over `C`. -/
@[weil "lem_fk101_sheaf_exact_iff_locally_exact"]
theorem exact_iff_forall_exists_faithfullyFlat
    {F G H : Sheaf (Scheme.AffineEtale.topology (Spec A)) AddCommGrpCat.{u}}
    (α : F ⟶ G) (β : G ⟶ H) (w : α ≫ β = 0) :
    (ShortComplex.mk α β w).Exact ↔
      ∀ (B : EtaleCategory A) (s : G.obj.obj B), β.hom.app B s = 0 →
        ∃ (C : EtaleCategory A) (g : B ⟶ C), (ringHom g).hom.FaithfullyFlat ∧
          G.obj.map g s ∈ Set.range (α.hom.app C) := by
  refine (Stacks.AbelianSheaves.exact_iff_locallyLiftable (ShortComplex.mk α β w)).trans ?_
  constructor
  · intro h B s hs
    obtain ⟨T, hT, hlift⟩ := h (V := B.unop) s hs
    obtain ⟨ι, _, Y, g, hgT, hg⟩ := exists_finite_of_mem_topology hT
    have hcov : IsCovering (B := B) (C := fun i ↦ op (Y i)) (fun i ↦ (g i).op) :=
      (isCovering_iff_mem_topology _).2 ⟨inferInstance, hg⟩
    choose x hx using fun i ↦ hlift (g i) (hgT i)
    have hF := (isSheaf_iff_isSheafAxioms_forget F.obj).1 F.property
    have hG := (isSheaf_iff_isSheafAxioms_forget G.obj).1 G.property
    obtain ⟨y, hy⟩ := (hF.bijective_pi _ _ _ (bijective_pi_piπ (fun i ↦ op (Y i)))).2 x
    refine ⟨finiteProductObj (fun i ↦ op (Y i)), piLift (fun i ↦ (g i).op),
      faithfullyFlat_piLift hcov, y, ?_⟩
    apply (hG.bijective_pi _ _ _ (bijective_pi_piπ (fun i ↦ op (Y i)))).1
    funext i
    have h1 := ConcreteCategory.congr_hom (α.hom.naturality (piπ (fun i ↦ op (Y i)) i)) y
    have h2 : F.obj.map (piπ (fun i ↦ op (Y i)) i) y = x i := congrFun hy i
    change G.obj.map (piπ (fun i ↦ op (Y i)) i) (α.hom.app _ y) =
      G.obj.map (piπ (fun i ↦ op (Y i)) i) (G.obj.map (piLift (fun i ↦ (g i).op)) s)
    simp only [ConcreteCategory.comp_apply] at h1
    rw [← h1, h2]
    refine (hx i).trans ?_
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, piLift_π]
  · intro h V z hz
    obtain ⟨C, g, hg, x, hx⟩ := h (op V) z hz
    refine ⟨Sieve.ofArrows (fun _ : PUnit.{1} ↦ C.unop) (fun _ ↦ g.unop),
      (isCovering_of_faithfullyFlat g hg).mem_topology, ?_⟩
    rintro W p ⟨Z, q, r, ⟨⟩, rfl⟩
    refine ⟨F.obj.map q.op x, ?_⟩
    have h1 := ConcreteCategory.congr_hom (α.hom.naturality q.op) x
    simp only [ConcreteCategory.comp_apply] at h1
    rw [h1, hx, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl

end EtaleCategory

end AlgebraicGeometry
