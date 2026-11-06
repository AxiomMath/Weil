module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable

/-!
# Disjoint copies of an object of the small étale site

Let `S` be a scheme in a big étale site `B` and `Y` an object of the small étale site of `S`.
For `m : ℕ`, the object `Y^{⊔ m} = Y ⊔ ⋯ ⊔ Y` (`m` copies) is the disjoint union of `m` copies
of `Y` in the small étale site, with the inclusions `ι_i : Y ⟶ Y^{⊔ m}` of the copies. For
`m = 0` it is the empty scheme.

The disjoint union of a finite family of objects of the small étale site is the coproduct of
the family in that category, with the tautological inclusions as coproduct injections; in
particular `Y^{⊔ m}` is the `m`-fold coproduct of `Y`.

## Main definitions

* `Stacks.EtaleCohomology.disjointCopies` — the disjoint union `Y^{⊔ m}` of `m` copies of `Y`.
* `Stacks.EtaleCohomology.disjointCopiesι` — the inclusion `ι_i : Y ⟶ Y^{⊔ m}` of the `i`-th
  copy.

## Main results

* `Stacks.EtaleCohomology.isColimitCofanDisjointUnion` — the disjoint union of a finite family
  is its coproduct in the small étale site.
* `Stacks.EtaleCohomology.isColimitCofanDisjointCopies` — `Y^{⊔ m}` with the inclusions
  `ι_i` is the `m`-fold coproduct of `Y` in the small étale site.
* `Stacks.EtaleCohomology.isEmpty_toScheme_disjointCopies_zero` — `Y^{⊔ 0}` is empty.

## Implementation notes

The copies are indexed by `Fin m`, that is by `0, …, m - 1`, rather than by `1, …, m`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], §I.3
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) {S : AlgebraicGeometry.Scheme.{u}}
  (hS : B.Contains S)

/-- The structure morphism of the disjoint union is induced by the structure morphisms of the
members. -/
theorem inclusion_map_hom_disjointUnionObj {n : ℕ} (U : Fin n → SmallEtale B S hS) :
    B.inclusion.map (disjointUnionObj B hS U).obj.hom =
      (Sigma.desc fun k => B.inclusion.map (U k).obj.hom :
        (∐ fun k => (SmallEtale.toScheme B S hS).obj (U k)) ⟶ S) :=
  rfl

/-- The structure morphism of the disjoint union restricts to that of each member. -/
theorem ι_comp_inclusion_map_hom_disjointUnionObj {n : ℕ} (U : Fin n → SmallEtale B S hS)
    (k : Fin n) :
    Sigma.ι (fun j => (SmallEtale.toScheme B S hS).obj (U j)) k ≫
      B.inclusion.map (disjointUnionObj B hS U).obj.hom = B.inclusion.map (U k).obj.hom := by
  rw [inclusion_map_hom_disjointUnionObj, Sigma.ι_desc]

/-- **The disjoint union of a finite family of objects of the small étale site is their
coproduct** in the small étale site, with the tautological inclusions as the coproduct
injections. -/
def isColimitCofanDisjointUnion {n : ℕ} (U : Fin n → SmallEtale B S hS) :
    IsColimit (Cofan.mk (disjointUnionObj B hS U) (disjointUnionHom B hS U)) :=
  Cofan.IsColimit.mk _
    (fun t => mkHom B hS (V := disjointUnionObj B hS U) (W := t.pt)
      (Sigma.desc fun k => (SmallEtale.toScheme B S hS).map (t.inj k))
      (Sigma.hom_ext _ _ fun k => by
        rw [ι_comp_inclusion_map_hom_disjointUnionObj, ← toScheme_map_comp_hom B hS (t.inj k)]
        exact Sigma.ι_desc_assoc (fun k => (SmallEtale.toScheme B S hS).map (t.inj k)) k
          (B.inclusion.map t.pt.obj.hom)))
    (fun t k => by
      apply hom_ext B hS
      exact (Functor.map_comp _ _ _).trans (Sigma.ι_desc _ k))
    (fun t m hm => by
      apply hom_ext B hS
      refine Sigma.hom_ext _ _ fun k => ?_
      exact ((Functor.map_comp (SmallEtale.toScheme B S hS) _ _).symm.trans
        (congrArg (SmallEtale.toScheme B S hS).map (hm k))).trans
        (Sigma.ι_desc (fun k => (SmallEtale.toScheme B S hS).map (t.inj k)) k).symm)

/-- **The disjoint union `Y^{⊔ m} = Y ⊔ ⋯ ⊔ Y` of `m` copies** of an object `Y` of the small
étale site. For `m = 0` it is the empty scheme. -/
@[weil "not_fk103_disjoint_copies"]
abbrev disjointCopies (Y : SmallEtale B S hS) (m : ℕ) : SmallEtale B S hS :=
  disjointUnionObj B hS (fun _ : Fin m => Y)

/-- **The inclusion `ι_i : Y ⟶ Y^{⊔ m}` of the `i`-th copy** of `Y` into the disjoint union of
`m` copies. -/
@[weil "not_fk103_disjoint_copies"]
abbrev disjointCopiesι (Y : SmallEtale B S hS) (m : ℕ) (i : Fin m) :
    Y ⟶ disjointCopies B hS Y m :=
  disjointUnionHom B hS (fun _ : Fin m => Y) i

/-- **`Y^{⊔ m}` is the `m`-fold coproduct of `Y` in the small étale site**, with the inclusions
`ι_i` of the copies as the coproduct injections. -/
@[weil "not_fk103_disjoint_copies"]
def isColimitCofanDisjointCopies (Y : SmallEtale B S hS) (m : ℕ) :
    IsColimit (Cofan.mk (f := fun _ : Fin m => Y) (disjointCopies B hS Y m)
      (disjointCopiesι B hS Y m)) :=
  isColimitCofanDisjointUnion B hS (fun _ : Fin m => Y)

/-- The underlying scheme of `Y^{⊔ m}` is the coproduct of `m` copies of the underlying scheme
of `Y`. -/
theorem toScheme_obj_disjointCopies (Y : SmallEtale B S hS) (m : ℕ) :
    (SmallEtale.toScheme B S hS).obj (disjointCopies B hS Y m) =
      ∐ fun _ : Fin m => (SmallEtale.toScheme B S hS).obj Y :=
  rfl

/-- The underlying morphism of schemes of `ι_i` is the `i`-th coproduct injection. -/
theorem toScheme_map_disjointCopiesι (Y : SmallEtale B S hS) (m : ℕ) (i : Fin m) :
    (SmallEtale.toScheme B S hS).map (disjointCopiesι B hS Y m i) =
      Sigma.ι (fun _ : Fin m => (SmallEtale.toScheme B S hS).obj Y) i :=
  rfl

/-- `Y^{⊔ 0}` is the empty scheme. -/
theorem isEmpty_toScheme_disjointCopies_zero (Y : SmallEtale B S hS) :
    IsEmpty ((SmallEtale.toScheme B S hS).obj (disjointCopies B hS Y 0)) := by
  rw [toScheme_obj_disjointCopies]
  refine ⟨fun x => ?_⟩
  obtain ⟨k, -⟩ :=
    (sigmaOpenCover fun _ : Fin 0 => (SmallEtale.toScheme B S hS).obj Y).exists_eq x
  exact k.elim0

end Stacks.EtaleCohomology
