module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import Weil.CategoryTheory.Sites.LocallySurjective
public import Weil.Attr

/-!
# Local surjectivity on the small étale site and stalks at geometric points

Let `φ : F ⟶ G` be a map of sheaves of sets on the small étale site of a scheme `S`. We show
that the following are equivalent:

1. for every `U` étale over `S` and every section `s ∈ G(U)` there is a *single* surjective
   étale morphism `h : V ⟶ U` such that the restriction of `s` to `V` lies in the image of
   `φ_V : F(V) → G(V)`;
2. the map `φ_x : F_x → G_x` on stalks is surjective at every geometric point `x` of `S`.

The first condition is local surjectivity of `φ` in the sense of Grothendieck topologies, with
the covering sieve replaced by one surjective étale map: given a covering family `Vᵢ ⟶ U` on
which `s` is locally in the image, the disjoint union `∐ Vᵢ ⟶ U` is surjective étale, and the
local preimages glue on `∐ Vᵢ` because the components are pairwise disjoint.

## Main results

* `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff`: a sieve on `U` is a covering sieve of
  the small étale site exactly when every point of `U` is in the image of one of its arrows.
* `AlgebraicGeometry.Scheme.Sheaf.isLocallySurjective_iff_exists_surjective`: local
  surjectivity of a map of étale sheaves of sets, tested by one surjective étale map.
* `AlgebraicGeometry.GeometricPoint.exists_surjective_etale_iff_forall_surjective_stalkFunctor`:
  the equivalence of the two conditions above.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`, and the stalk
at a geometric point is `AlgebraicGeometry.GeometricPoint.stalkFunctor`, the fibre of the
corresponding point of the site. Geometric points take values in algebraically closed fields;
the source allows separably closed ones. The source assumes `S` noetherian and uses a finite
subcover; the disjoint union of an arbitrary covering family is still étale and surjective, so
no finiteness hypothesis is needed.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

/- Stated on Mathlib's `smallEtaleTopology`
(where StacksFrontier's stalk functor and conservativity live), not on StacksFrontier's
`SmallEtale`. No noetherian hypothesis (stronger than FK). -/

@[expose] public section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- A sieve on `U` in the small étale site covers exactly when every point of `U` is in the
image of one of its arrows. -/
lemma mem_smallEtaleTopology_iff {U : S.Etale} (R : Sieve U) :
    R ∈ S.smallEtaleTopology U ↔
      ∀ x : U.left, ∃ (Y : S.Etale) (f : Y ⟶ U) (y : Y.left), R f ∧ f.left y = x := by
  refine (Iff.of_eq (congrArg (fun J : GrothendieckTopology S.Etale => R ∈ J U)
    (smallGrothendieckTopology_eq_toGrothendieck_smallPretopology S
      (P := @AlgebraicGeometry.Etale) (Q := @AlgebraicGeometry.Etale) le_rfl))).trans
    ((mem_toGrothendieck_smallPretopology U R).trans (forall_congr' fun x => ⟨?_, ?_⟩))
  · rintro ⟨Y, f, y, hf, -, hy⟩
    exact ⟨Y, f, y, hf, hy⟩
  · rintro ⟨Y, f, y, hf, hy⟩
    exact ⟨Y, f, y, hf, inferInstance, hy⟩

/-- A sieve of the small étale site containing a surjective arrow is a covering sieve. -/
lemma mem_smallEtaleTopology_of_surjective {U V : S.Etale} {R : Sieve U} (h : V ⟶ U)
    (hR : R h) (hh : Function.Surjective h.left) : R ∈ S.smallEtaleTopology U := by
  rw [mem_smallEtaleTopology_iff]
  intro x
  obtain ⟨y, rfl⟩ := hh x
  exact ⟨V, h, y, hR, rfl⟩

/-- On an object of the small étale site with empty underlying scheme, a sheaf of sets has at
most one section. -/
lemma subsingleton_sheaf_obj_of_isEmpty (F : Sheaf S.smallEtaleTopology (Type u))
    (Z : S.Etale) [IsEmpty Z.left] : Subsingleton (F.obj.obj (op Z)) := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hbot : (⊥ : Sieve Z) ∈ S.smallEtaleTopology Z := by
    rw [mem_smallEtaleTopology_iff]
    exact fun x => isEmptyElim x
  exact ⟨fun a b => (hF _ hbot).isSeparatedFor.ext fun _ _ hf => hf.elim⟩

namespace Etale

variable {ι : Type u}

lemma sigmaι_jointly_surjective (Y : ι → S.Etale) (x : (sigmaObj Y).left) :
    ∃ (i : ι) (y : (Y i).left), (sigmaι Y i).left y = x := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk fun i => (Y i).left).surjective x
  refine ⟨i, y, ?_⟩
  change Sigma.ι (fun i => (Y i).left) i y = _
  exact (sigmaMk_mk (fun i => (Y i).left) i y).symm

instance (Y : ι → S.Etale) (i : ι) : Mono (sigmaι Y i) :=
  (Etale.forget S ⋙ Over.forget S).mono_of_mono_map
    (inferInstanceAs (Mono (Sigma.ι (fun i => (Y i).left) i)))

end Etale

namespace Sheaf

variable {F G : Sheaf S.smallEtaleTopology (Type u)}

/-- **Local surjectivity by one surjective étale map.** A map of sheaves of sets on the small
étale site is locally surjective exactly when every section of the target becomes, after
restriction along a single surjective étale map, a section in the image. -/
theorem isLocallySurjective_iff_exists_surjective (φ : F ⟶ G) :
    CategoryTheory.Sheaf.IsLocallySurjective φ ↔
      ∀ (U : S.Etale) (s : G.obj.obj (op U)), ∃ (V : S.Etale) (h : V ⟶ U),
        Function.Surjective h.left ∧
          ∃ t : F.obj.obj (op V), φ.hom.app (op V) t = G.obj.map h.op s := by
  constructor
  · intro hφ U s
    have hR := Presheaf.imageSieve_mem S.smallEtaleTopology φ.hom (U := op U) s
    rw [mem_smallEtaleTopology_iff] at hR
    choose Y f y hf hy using hR
    choose t ht using hf
    obtain ⟨t', ht'⟩ := Etale.exists_map_sigmaι_eq F Y t
    refine ⟨Etale.sigmaObj Y, Etale.sigmaDesc f, fun x => ⟨(Etale.sigmaι Y x).left (y x), ?_⟩,
      t', Etale.ext_of_map_sigmaι_eq G fun x => ?_⟩
    · exact (congrArg (fun g => g.left (y x)) (Etale.sigmaι_sigmaDesc f x)).trans (hy x)
    · rw [← types_comp_apply (φ.hom.app _) (G.obj.map _), ← φ.hom.naturality, types_comp_apply,
        ht', ht, ← types_comp_apply (G.obj.map _) (G.obj.map _), ← Functor.map_comp, ← op_comp,
        Etale.sigmaι_sigmaDesc]
  · intro h
    refine ⟨fun {U} s => ?_⟩
    obtain ⟨V, g, hg, t, ht⟩ := h U s
    exact mem_smallEtaleTopology_of_surjective g ⟨t, ht⟩ hg

end Sheaf

end Scheme

namespace GeometricPoint

variable {S : Scheme.{u}} {F G : Sheaf S.smallEtaleTopology (Type u)}

/-- **Surjectivity on stalks at geometric points.** For a map `φ : F ⟶ G` of sheaves of sets on
the small étale site of `S`, the following are equivalent: every section `s ∈ G(U)` becomes, after
restriction along some surjective étale map `V ⟶ U`, a section in the image of `φ_V`; and `φ`
is surjective on the stalk at every geometric point of `S`. -/
@[weil "lem_fk104_locally_surjective_iff_stalks_surjective"]
theorem exists_surjective_etale_iff_forall_surjective_stalkFunctor (φ : F ⟶ G) :
    (∀ (U : S.Etale) (s : G.obj.obj (op U)), ∃ (V : S.Etale) (h : V ⟶ U),
        Function.Surjective h.left ∧
          ∃ t : F.obj.obj (op V), φ.hom.app (op V) t = G.obj.map h.op s) ↔
      ∀ x : GeometricPoint S, Function.Surjective (x.stalkFunctor.map φ) := by
  rw [← Scheme.Sheaf.isLocallySurjective_iff_exists_surjective,
    CategoryTheory.Sheaf.isLocallySurjective_iff_epi, epi_iff_forall_surjective_stalkFunctor]

end GeometricPoint

end AlgebraicGeometry

end
