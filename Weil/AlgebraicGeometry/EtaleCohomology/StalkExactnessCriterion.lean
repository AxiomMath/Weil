module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# A sequence of abelian étale sheaves is exact iff it is exact on geometric stalks

Let `B` be a big étale site containing a scheme `S`, and let `F ⟶ G ⟶ H` be two composable
morphisms of abelian sheaves on the small étale site of `S`. The sequence is exact (the
composite vanishes and the image of the first map is the kernel of the second) exactly when, at
every geometric point `s` of `S`, the sequence of stalks `F_s ⟶ G_s ⟶ H_s` is exact as a sequence
of abelian groups, that is, the kernel of `G_s ⟶ H_s` is the image of `F_s ⟶ G_s`.

## Main results

* `AlgebraicGeometry.exists_exact_iff_etaleStalk_exact` — `φ ≫ ψ = 0` and the short complex
  `F ⟶ G ⟶ H` is exact if and only if for every geometric point the stalk sequence is exact.

## Implementation notes

The sequence is not assumed to be a complex: the vanishing of `φ ≫ ψ` is part of exactness, and
on the stalk side it is part of "kernel equals image". The implication from stalkwise exactness to
`φ ≫ ψ = 0` uses that the stalk functors at the geometric points are jointly faithful
(`AlgebraicGeometry.jointlyFaithful_etaleStalkSheafFiber`); the rest is
`AlgebraicGeometry.exact_iff_etaleStalk_exact` (Stacks 03PU). Geometric points are over
algebraically closed fields, as in the Stacks project.

## References

* [FK] Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A sequence `F ⟶ G ⟶ H` of abelian sheaves on the small étale site of `S` is exact (its
composite vanishes and the resulting short complex is exact) if and only if, at every geometric
point `s` of `S`, the kernel of `G_s ⟶ H_s` is the image of `F_s ⟶ G_s`. -/
@[weil "lem_fk102_exact_iff_stalkwise_exact"]
theorem exists_exact_iff_etaleStalk_exact
    {F G H : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    (∃ h : φ ≫ ψ = 0, (ShortComplex.mk φ ψ h).Exact) ↔ ∀ s : GeometricPoint S,
      let Φ := sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v} ⋙
        etaleStalkPresheafFunctor B S hS s AddCommGrpCat.{max (u + 1) v}
      ∀ b : Φ.obj G,
        ((Φ.map ψ).hom b = 0 ↔ ∃ a : Φ.obj F, (Φ.map φ).hom a = b) := by
  constructor
  · rintro ⟨h, hT⟩
    exact (exact_iff_etaleStalk_exact.{u, v} B S hS (ShortComplex.mk φ ψ h)).1 hT
  · intro hst
    have h : φ ≫ ψ = 0 := by
      apply (jointlyFaithful_etaleStalkSheafFiber.{u, v} B S hS).map_injective
      intro s
      rw [Functor.map_comp, Functor.map_zero]
      apply AddCommGrpCat.hom_ext
      ext a
      exact ((hst s _).2 ⟨a, rfl⟩)
    exact ⟨h, (exact_iff_etaleStalk_exact.{u, v} B S hS (ShortComplex.mk φ ψ h)).2 hst⟩

end AlgebraicGeometry

end

/-! ### Exactness of étale sheaves is tested on the stalks over a detecting set -/

/-!
# Exactness of étale sheaves is tested on the stalks over a detecting set

Let `B` be a big étale site containing a scheme `S` and let `P ⊆ S` be a detecting set of
points (`AlgebraicGeometry.SmallEtale.IsDetecting`). A sequence `F ⟶ G ⟶ H` of abelian sheaves
on the small étale site of `S` is exact as soon as the sequence of stalks is exact at every
geometric point of `S` lying over a point of `P`.

The key input is that the stalks at the geometric points over `P` are jointly faithful. Given an
object `X` of the site and a sieve `R` on `X` through which every geometric point over `P`
lifts, the union `W` of the images of the arrows of `R` is open in `X`, since étale morphisms
are open. If its closed complement were nonempty, it would contain a point mapping into `P`,
and the geometric point at that point would lift through `R`, a contradiction. So the arrows of
`R` are jointly surjective, and `R` is covering. Exactness then follows by applying joint
faithfulness to the identity of the homology.

## Main results

* `AlgebraicGeometry.SmallEtale.IsDetecting.mem_topology_of_forall_geometricPointFiber_lift` —
  a sieve through which every geometric point over a detecting set lifts is covering.
* `AlgebraicGeometry.SmallEtale.IsDetecting.jointlyFaithful_etaleStalkSheafFiber` — the stalk
  functors at the geometric points over a detecting set are jointly faithful.
* `AlgebraicGeometry.SmallEtale.IsDetecting.exact_iff_etaleStalk_exact` — a short complex of
  abelian sheaves is exact iff its stalk complexes over the detecting set are exact.
* `AlgebraicGeometry.SmallEtale.IsDetecting.exact_of_etaleStalk_exact` — for morphisms
  `φ : F ⟶ G` and `ψ : G ⟶ H` with exact stalk sequences over the detecting set, `φ ≫ ψ = 0`
  and the resulting short complex is exact.

## Implementation notes

The site is the small étale site of [Stacks, Tag 021B] rather than the category of noetherian
separated étale schemes, and geometric points have algebraically closed residue fields. A
geometric point `s` lies over a point of `P` when `s.hom default ∈ P`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

namespace SmallEtale

namespace IsDetecting

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {P : Set S}

/-- The geometric point attached to a point `x` of an object `V` of the small étale site lies
over the image of `x` in `S`. -/
theorem geometricPointOfEtalePoint_hom_default (V : SmallEtale B S hS)
    (x : (toScheme B S hS).obj V) :
    (geometricPointOfEtalePoint B S hS V x).hom default =
      (B.inclusion.map V.obj.hom).base x := by
  change (B.inclusion.map V.obj.hom).base
      ((GeometricPoint.ofPoint ((toScheme B S hS).obj V) x).hom default) = _
  rw [GeometricPoint.ofPoint_liesOver]

/-- **A sieve through which every geometric point over a detecting set lifts is covering.**
The images of its arrows form an open subset of the object; the complement, if nonempty, would
contain a point mapping into the detecting set, whose geometric point lifts through the sieve. -/
theorem mem_topology_of_forall_geometricPointFiber_lift (hP : IsDetecting B S hS P)
    {X : SmallEtale B S hS} (R : Sieve X)
    (hR : ∀ (s : GeometricPoint S), s.hom default ∈ P →
      ∀ q : (geometricPointFiber B S hS s).obj X,
      ∃ (Y : SmallEtale B S hS) (g : Y ⟶ X), R g ∧
        ∃ q' : (geometricPointFiber B S hS s).obj Y,
          (geometricPointFiber B S hS s).map g q' = q) :
    R ∈ SmallEtale.topology B S hS X := by
  refine SmallEtale.mem_topology_of_jointlySurjective fun x => ?_
  let W : Set ((toScheme B S hS).obj X) :=
    ⋃ (Y : SmallEtale B S hS) (g : Y ⟶ X) (_ : R g), Set.range ((toScheme B S hS).map g)
  have hW : IsOpen W := by
    refine isOpen_iUnion fun Y => isOpen_iUnion fun g => isOpen_iUnion fun _ => ?_
    have : Etale ((toScheme B S hS).map g) := inferInstance
    exact ((toScheme B S hS).map g).isOpenMap.isOpen_range
  have key : ∀ t ∈ Wᶜ, (B.inclusion.map X.obj.hom).base t ∈ P → False := by
    intro t ht htP
    have hPt : (geometricPointOfEtalePoint B S hS X t).hom default ∈ P := by
      rw [geometricPointOfEtalePoint_hom_default]; exact htP
    obtain ⟨Y, g, hg, q', hq'⟩ := hR _ hPt (geometricPointOfEtalePointLift B S hS X t)
    apply ht
    refine Set.mem_iUnion.2 ⟨Y, Set.mem_iUnion.2 ⟨g, Set.mem_iUnion.2 ⟨hg, ?_⟩⟩⟩
    refine ⟨q'.1.base default, ?_⟩
    have h1 : q'.1 ≫ (SmallEtale.toScheme B S hS).map g =
        (geometricPointOfEtalePointLift B S hS X t).1 := congrArg Subtype.val hq'
    have h2 : ((SmallEtale.toScheme B S hS).map g).base (q'.1.base default) =
        (geometricPointOfEtalePointLift B S hS X t).1.base default :=
      congrArg (fun m : (geometricPointOfEtalePoint B S hS X t).source ⟶ _ =>
        m.base (default : ↥(geometricPointOfEtalePoint B S hS X t).source)) h1
    exact h2.trans (geometricPointOfEtalePointLift_base B S hS X t)
  have hxW : x ∈ W := by
    by_contra hx
    obtain ⟨t, ht, htP⟩ := hP X Wᶜ hW.isClosed_compl ⟨x, hx⟩
    exact key t ht htP
  obtain ⟨Y, hY⟩ := Set.mem_iUnion.1 hxW
  obtain ⟨g, hg⟩ := Set.mem_iUnion.1 hY
  obtain ⟨hR, hx'⟩ := Set.mem_iUnion.1 hg
  exact ⟨Y, g, hR, hx'⟩

/-- **The stalks over a detecting set are jointly faithful.** Two morphisms of abelian sheaves
on the small étale site of `S` inducing the same map on the stalk at every geometric point lying
over a point of a detecting set `P` are equal. -/
theorem jointlyFaithful_etaleStalkSheafFiber (hP : IsDetecting B S hS P) :
    JointlyFaithful (fun s : {s : GeometricPoint S // s.hom default ∈ P} =>
      (geometricPointSitePoint B S hS s.1).sheafFiber (A := AddCommGrpCat.{max (u + 1) v})) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u} _
  refine ⟨fun {F G} {φ ψ} h => ?_⟩
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext a
  have hcov : Presheaf.equalizerSieve (φ.1.app U a) (ψ.1.app U a) ∈
      SmallEtale.topology B S hS U.unop := by
    refine hP.mem_topology_of_forall_geometricPointFiber_lift _ fun s hs q => ?_
    have heq : (geometricPointSitePoint B S hS s).toPresheafFiber U.unop q G.obj
          (φ.1.app U a) =
        (geometricPointSitePoint B S hS s).toPresheafFiber U.unop q G.obj (ψ.1.app U a) := by
      have hh := ConcreteCategory.congr_hom (h ⟨s, hs⟩)
        ((geometricPointSitePoint B S hS s).toPresheafFiber U.unop q F.obj a)
      change (geometricPointSitePoint B S hS s).presheafFiber.map φ.1
          ((geometricPointSitePoint B S hS s).toPresheafFiber U.unop q F.obj a) =
        (geometricPointSitePoint B S hS s).presheafFiber.map ψ.1
          ((geometricPointSitePoint B S hS s).toPresheafFiber U.unop q F.obj a) at hh
      exact (((geometricPointSitePoint B S hS s).toPresheafFiber_naturality_apply
          φ.1 U.unop q a).symm.trans hh).trans
        ((geometricPointSitePoint B S hS s).toPresheafFiber_naturality_apply ψ.1 U.unop q a)
    obtain ⟨V, g, y, hfiber, hsection⟩ :=
      ((geometricPointSitePoint B S hS s).toPresheafFiber_eq_iff' U.unop q _ _).mp heq
    exact ⟨V, g, hsection, y, hfiber⟩
  exact G.property.isSeparated _ _ hcov _ _ fun _ _ hf => hf

/-- **Exactness is tested on the stalks over a detecting set.** A short complex of abelian
sheaves on the small étale site of `S` is exact exactly when its complex of stalks is exact at
every geometric point lying over a point of a detecting set `P`. -/
theorem exact_iff_etaleStalk_exact (hP : IsDetecting B S hS P)
    (T : ShortComplex (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v})) :
    T.Exact ↔ ∀ s : GeometricPoint S, s.hom default ∈ P →
      let Φ := sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v} ⋙
        etaleStalkPresheafFunctor B S hS s AddCommGrpCat.{max (u + 1) v}
      ∀ b : Φ.obj T.X₂,
        ((Φ.map T.g).hom b = 0 ↔ ∃ a : Φ.obj T.X₁, (Φ.map T.f).hom a = b) := by
  constructor
  · intro h s _
    exact (AlgebraicGeometry.exact_iff_etaleStalk_exact B S hS T).1 h s
  · intro h
    have : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) v} :=
      AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
    let Ψ := fun s : GeometricPoint S =>
      (geometricPointSitePoint B S hS s).sheafFiber (A := AddCommGrpCat.{max (u + 1) v})
    have hs : ∀ s : GeometricPoint S, s.hom default ∈ P → (T.map (Ψ s)).Exact := by
      intro s hsP
      rw [ShortComplex.ab_exact_iff]
      intro b hb
      exact (h s hsP b).1 hb
    rw [T.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    apply (hP.jointlyFaithful_etaleStalkSheafFiber.{u, v}).map_injective
    intro s
    have hz : IsZero ((Ψ s.1).obj T.homology) :=
      (Iso.isZero_iff (T.mapHomologyIso (Ψ s.1))).1
        ((T.map (Ψ s.1)).exact_iff_isZero_homology.1 (hs s.1 s.2))
    simpa using hz.eq_of_src (𝟙 _) 0

/-- **A sequence of abelian étale sheaves is exact if it is exact on the stalks over a
detecting set.** Let `φ : F ⟶ G` and `ψ : G ⟶ H` be morphisms of abelian sheaves on the small
étale site of `S` and `P ⊆ S` a detecting set. If `F_s ⟶ G_s ⟶ H_s` is exact at every geometric
point `s` lying over a point of `P`, then `φ ≫ ψ = 0` and `F ⟶ G ⟶ H` is exact. -/
@[weil "lem_fk102_exact_of_stalks_exact_on_detecting"]
theorem exact_of_etaleStalk_exact (hP : IsDetecting B S hS P)
    {F G H : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) (ψ : G ⟶ H)
    (h : ∀ s : GeometricPoint S, s.hom default ∈ P →
      let Φ := sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v} ⋙
        etaleStalkPresheafFunctor B S hS s AddCommGrpCat.{max (u + 1) v}
      ∀ b : Φ.obj G,
        ((Φ.map ψ).hom b = 0 ↔ ∃ a : Φ.obj F, (Φ.map φ).hom a = b)) :
    ∃ hφψ : φ ≫ ψ = 0, (ShortComplex.mk φ ψ hφψ).Exact := by
  have hzero : φ ≫ ψ = 0 := by
    apply (hP.jointlyFaithful_etaleStalkSheafFiber.{u, v}).map_injective
    intro s
    rw [Functor.map_comp, Functor.map_zero]
    apply AddCommGrpCat.hom_ext
    ext a
    exact (h s.1 s.2 _).2 ⟨a, rfl⟩
  exact ⟨hzero, (hP.exact_iff_etaleStalk_exact _).2 h⟩

end IsDetecting

end SmallEtale

end AlgebraicGeometry

end
