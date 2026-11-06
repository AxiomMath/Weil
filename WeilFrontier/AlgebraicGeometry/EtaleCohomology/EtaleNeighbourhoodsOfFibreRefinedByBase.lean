module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import Weil.Attr
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Bijectivity

/-!
# Étale neighbourhoods of the geometric fibre of a finite morphism

Let `f : X ⟶ Y` be a finite morphism of schemes and `y : Spec k ⟶ Y` a geometric point. The
lifts `x₁, …, xₙ` of `y` to `X` are finitely many geometric points of `X`. Given an étale
neighbourhood `(Uᵥ, uᵥ)` of each lift `xᵥ`, there is a single étale neighbourhood `(V, v)` of
`y` whose base change `V ×_Y X` maps over `X` to the disjoint union `U₁ ⊔ ⋯ ⊔ Uₙ`, carrying
the point `(v, xᵥ)` of `V ×_Y X` to the point `uᵥ` of the `v`-th summand. Thus the étale
neighbourhoods of `y`, pulled back to `X`, are cofinal among families of étale neighbourhoods
of the lifts.

## Main results

* `AlgebraicGeometry.IsFinite.exists_etaleNeighborhood_pullback_hom_sigma`: the statement
  above.

## Implementation notes

Geometric points take values in algebraically closed fields (`AlgebraicGeometry.GeometricPoint`).
The source asks moreover that every point of the geometric fibre `Spec k ×_Y X` have residue
field `k`; for an algebraically closed `k` this holds automatically, the fibre being finite over
`k`, so the hypothesis is omitted. The lifts are indexed by the morphisms
`g : Spec k ⟶ X` with `g ≫ f = y`, each regarded as a geometric point of `X` by
`AlgebraicGeometry.geometricPointLift`.

The proof does not go through strict local rings. A single étale neighbourhood `V` of `y` is
found whose base change `V ×_Y X` is partitioned into open and closed pieces, the piece
containing `(v, xᵥ)` mapping into `Uᵥ` over `X` (Tag 04DM, property (A) of finite morphisms,
combined with the separation of the lifts after an étale base change). The morphism to the
disjoint union is glued from these pieces along the open cover they form; it is well defined
because the pieces are pairwise disjoint. The partition is constructed inside a big étale site
containing `X`, `Y` and the `Uᵥ`, which exists by Tag 000J.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 04DM](https://stacks.math.columbia.edu/tag/04DM)
-/

/- FK's residue-field hypothesis is
dropped (automatic for geometric points over algebraically closed fields, the Stacks project
convention); FK's proof via
the tensor decomposition of the strict local ring is replaced by StacksFrontier's partition
`exists_etaleNeighborhoodPartition`, private in its module and reached by `import all`. -/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- **Étale neighbourhoods of the lifts are refined by one of the base.** Let `f : X ⟶ Y` be
finite, `y` a geometric point of `Y`, and `U x` an étale neighbourhood of each lift `x` of `y`
to `X`. Then there are an étale neighbourhood `V` of `y` and a morphism
`h : V ×_Y X ⟶ ∐ₓ U x` over `X` carrying the point `(v, x)` of `V ×_Y X` to the point of
`U x` in the summand indexed by `x`, for every lift `x`. -/
@[weil "lem_fk103_etale_neighbourhoods_of_fibre_refined_by_base"]
theorem IsFinite.exists_etaleNeighborhood_pullback_hom_sigma {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] (y : GeometricPoint Y)
    (U : ∀ x : {g : y.source ⟶ X // g ≫ f = y.hom},
      GeometricPoint.EtaleNeighborhood (geometricPointLift f y x)) :
    ∃ (V : GeometricPoint.EtaleNeighborhood y)
      (h : pullback V.toBase f ⟶ ∐ fun x => (U x).scheme),
      h ≫ Sigma.desc (fun x => (U x).toBase) = pullback.snd V.toBase f ∧
      ∀ x, pullback.lift V.point x.1 (V.point_comp.trans x.2.symm) ≫ h =
        (U x).point ≫ Sigma.ι (fun x => (U x).scheme) x := by
  classical
  let L := {g : y.source ⟶ X // g ≫ f = y.hom}
  let S₀ : Set Scheme.{u} := {X, Y} ∪ Set.range (fun x : L => (U x).scheme)
  have : Small.{u} S₀ := small_union _ _
  let B := BigEtaleSite.ofSet S₀
  have hX : B.Contains X := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  have hY : B.Contains Y := BigEtaleSite.contains_ofSet S₀ (by simp [S₀])
  have hU (x : L) : B.Contains (U x).scheme :=
    BigEtaleSite.contains_ofSet S₀ (Or.inr ⟨x, rfl⟩)
  let Xb : B.Scheme := B.obj X hX
  let Yb : B.Scheme := B.obj Y hY
  let fb : Xb ⟶ Yb := ObjectProperty.homMk f
  have : IsFinite (B.inclusion.map fb) := ‹IsFinite f›
  let Ub : ∀ x : {g : y.source ⟶ X // g ≫ B.inclusion.map fb = y.hom},
      (geometricPointFiber B X hX (geometricPointLift (B.inclusion.map fb) y x)).Elements :=
    fun x => ⟨⟨Over.mk (ObjectProperty.homMk (U x).toBase : B.obj (U x).scheme (hU x) ⟶ Xb),
      (U x).etale_toBase⟩, ⟨(U x).point, (U x).point_comp⟩⟩
  obtain ⟨Q⟩ := exists_etaleNeighborhoodPartition B fb y Ub
  let T := SmallEtale.toScheme B X hX
  let V : GeometricPoint.EtaleNeighborhood y :=
    { scheme := B.inclusion.obj Q.base.1.obj.left
      toBase := B.inclusion.map Q.base.1.obj.hom
      etale_toBase := Q.base.1.property
      point := Q.base.2.1
      point_comp := Q.base.2.2 }
  let P : IsPullback (B.inclusion.map (pullback.fst Q.base.1.obj.hom fb))
      (B.inclusion.map (pullback.snd Q.base.1.obj.hom fb)) V.toBase f :=
    (IsPullback.of_hasPullback Q.base.1.obj.hom fb).map B.inclusion
  let Z : Scheme.{u} := T.obj ((smallEtaleBaseChange B fb).obj Q.base.1)
  let e : Z ≅ pullback V.toBase f := P.isoPullback
  have he₁ : e.hom ≫ pullback.fst V.toBase f = B.inclusion.map (pullback.fst Q.base.1.obj.hom fb) :=
    P.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd V.toBase f = B.inclusion.map (pullback.snd Q.base.1.obj.hom fb) :=
    P.isoPullback_hom_snd
  let j (x : L) : T.obj (Q.neighborhood x).1 ⟶ Z := T.map (Q.toBase x)
  have hjmono (x : L) : Mono (j x) := by
    have h := (mono_iff_isPullback (Q.toBase x)).1 (Q.mono_toBase x)
    have h' := h.map T
    rw [(mono_iff_isPullback (j x))]
    convert h' using 1 <;> exact (T.map_id _).symm
  have hjopen (x : L) : IsOpenImmersion (j x) := by
    have : Etale (j x) := etale_smallEtale_map B X hX _
    have := hjmono x
    exact IsOpenImmersion.of_flat_of_mono _
  let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers L (fun x => T.obj (Q.neighborhood x).1) j
    (fun p => by
      obtain ⟨x, q, hq⟩ := Q.covers p
      exact ⟨x, q, hq⟩) hjopen
  let g (x : L) : T.obj (Q.neighborhood x).1 ⟶ ∐ fun x => (U x).scheme :=
    T.map (Q.toNeighborhood x).1 ≫ Sigma.ι (fun x => (U x).scheme) x
  have hg : ∀ x x', pullback.fst (𝒰.f x) (𝒰.f x') ≫ g x = pullback.snd (𝒰.f x) (𝒰.f x') ≫ g x' := by
    intro x x'
    by_cases hxx : x = x'
    · subst hxx
      have := hjmono x
      have : pullback.fst (j x) (j x) = pullback.snd (j x) (j x) :=
        (cancel_mono (j x)).1 pullback.condition
      change pullback.fst (j x) (j x) ≫ g x = pullback.snd (j x) (j x) ≫ g x
      rw [this]
    · have : IsEmpty (↑(pullback (j x) (j x') : Scheme.{u})) := ⟨fun w => by
        have he := congrArg (fun k => k w) (pullback.condition (f := j x) (g := j x'))
        simp only [Scheme.Hom.comp_apply] at he
        exact Set.disjoint_left.mp (Q.disjoint hxx) (Set.mem_range_self _)
          ⟨_, he.symm⟩⟩
      exact (@isInitialOfIsEmpty (pullback (j x) (j x')) this).hom_ext _ _
  let hZ : Z ⟶ ∐ fun x => (U x).scheme := 𝒰.glueMorphisms g hg
  refine ⟨V, e.inv ≫ hZ, ?_, ?_⟩
  · rw [← cancel_epi e.hom, Category.assoc, Iso.hom_inv_id_assoc, he₂]
    refine 𝒰.hom_ext _ _ (fun x => ?_)
    change j x ≫ hZ ≫ _ = j x ≫ _
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ Sigma.desc fun x => (U x).toBase)
      (𝒰.ι_glueMorphisms g hg x : j x ≫ hZ = g x)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => T.map (Q.toNeighborhood x).1 ≫ k)
      (Sigma.ι_desc (fun x => (U x).toBase) x)).trans ?_
    exact (SmallEtale.toScheme_map_comp B X hX (Q.toNeighborhood x).1).trans
      (SmallEtale.toScheme_map_comp B X hX (Q.toBase x)).symm
  · intro x
    have hc : j x ≫ B.inclusion.map (pullback.snd Q.base.1.obj.hom fb) =
        B.inclusion.map (Q.neighborhood x).1.obj.hom :=
      SmallEtale.toScheme_map_comp B X hX (Q.toBase x)
    have hl : pullback.lift V.point x.1 (V.point_comp.trans x.2.symm) =
        (Q.neighborhood x).2.1 ≫ j x ≫ e.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, Category.assoc, he₁]
        exact (Q.point_toBase x).symm
      · rw [pullback.lift_snd, Category.assoc, Category.assoc, he₂]
        exact ((Q.neighborhood x).2.2.symm).trans
          (congrArg (fun k => (Q.neighborhood x).2.1 ≫ k) hc.symm)
    rw [hl, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    have hp : (Q.neighborhood x).2.1 ≫ T.map (Q.toNeighborhood x).1 = (U x).point :=
      congrArg Subtype.val (Q.toNeighborhood x).2
    have hq : (Q.neighborhood x).2.1 ≫ g x =
        (U x).point ≫ Sigma.ι (fun x => (U x).scheme) x := by
      rw [← hp]
      exact (Category.assoc _ _ _).symm
    exact (congrArg (fun k => (Q.neighborhood x).2.1 ≫ k)
      (𝒰.ι_glueMorphisms g hg x : j x ≫ hZ = g x)).trans hq

end AlgebraicGeometry

end
