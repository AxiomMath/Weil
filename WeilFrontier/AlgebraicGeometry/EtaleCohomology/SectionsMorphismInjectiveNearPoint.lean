module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable
public import WeilFrontier.AlgebraicGeometry.Etale.SheafMinusSectionsSubsheaf
public import WeilFrontier.AlgebraicGeometry.Sites.OpenDifferenceLociClopen
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.MorphismFromCopiesDefinedBySections
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci

/-!
# Injectivity of the morphism from copies near a geometric point

Let `G` be a sheaf of sets with open difference loci on the small étale site of a scheme `X`,
`x̄` a geometric point of `X`, and `s = (s_0, …, s_{m-1})` global sections of `G` whose germs
at `x̄` are pairwise distinct. Let `Φ_s : X̃^{⊔ m} ⟶ G` be the morphism from the sheaf
represented by `m` disjoint copies of `X` defined by `s`. Then for every object `U` of the site
whose image in `X` lies in the connected component of the point under `x̄`, the map
`Φ_{s,U} : Hom_X(U, X^{⊔ m}) → G(U)` is injective; if `X` is connected this holds for every `U`.

Two `X`-morphisms `a, b : U ⟶ X^{⊔ m}` are compared locally on the covering of `U` obtained by
pulling back the covering of `X^{⊔ m}` by its copies along `a` and along `b`. On a member
`f : V ⟶ U` of it, `f ≫ a = π ≫ ι_i` and `f ≫ b = π ≫ ι_j`, with `π : V ⟶ X` the structure
morphism. If `V` is empty the two agree. Otherwise `Φ_{s,U}(a) = Φ_{s,U}(b)` gives
`π^* s_i = π^* s_j`, so the image of `V` in `X` lies in the coincidence set `C(s_i, s_j)`.
That set is open and closed, and meets the connected component of the point under `x̄`, so it
contains this point; hence the germs of `s_i` and `s_j` at `x̄` agree, and `i = j`. As the
represented sheaf is separated, `a = b`.

## Main results

* `Stacks.EtaleCohomology.injective_morphismFromCopies_app_of_range_subset_connectedComponent`:
  `Φ_{s,U}` is injective when the image of `U` lies in the connected component of `x̄`.
* `Stacks.EtaleCohomology.injective_morphismFromCopies_app_of_connectedSpace`: for connected
  `X`, `Φ_{s,U}` is injective for every `U`.

## Implementation notes

The source asks that the structure morphism of `U` factor through the connected component
`X_0` of `x̄`; here the hypothesis is that its image lies in `X_0` as a set, which does not
require `X_0` to be open. The source reduces to connected `U` through the connected components
of the noetherian `U`; here the comparison is local on an étale covering, so no finiteness or
noetherian hypothesis on `U` is needed. The copies are indexed by `Fin m`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3.15
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {B : _root_.AlgebraicGeometry.BigEtaleSite.{u}} {S : _root_.AlgebraicGeometry.Scheme.{u}}
  {hS : B.Contains S}

/-- **Injectivity of `Φ_{s,U}` near a geometric point.** Let `G` be a sheaf of sets with open
difference loci on the small étale site of `S`, `x` a geometric point of `S`, and
`s_0, …, s_{m-1}` global sections of `G` with pairwise distinct germs at `x`. For every object
`U` of the site whose image in `S` lies in the connected component of the point under `x`, the
map `Φ_{s,U} : Hom_S(U, S^{⊔ m}) → G(U)` is injective. -/
@[weil "lem_fk103_sections_morphism_injective_near_point"]
theorem injective_morphismFromCopies_app_of_range_subset_connectedComponent
    (G : smallEtaleTopos.{u, u} B S hS) (hG : HasOpenDifferenceLoci G.obj) {m : ℕ}
    (s : Fin m → G.obj.obj (op (SmallEtale.final B S hS))) (x : GeometricPoint S)
    (hs : Pairwise fun i j => germ G.obj (s i) x ≠ germ G.obj (s j) x)
    (U : SmallEtale B S hS)
    (hU : Set.range ((SmallEtale.toScheme B S hS).map ((SmallEtale.finalIsTerminal B S hS).from U))
      ⊆ connectedComponent (x.hom default)) :
    Function.Injective ((morphismFromCopies G (SmallEtale.final B S hS) s).hom.app (op U)) := by
  intro (a : U ⟶ disjointCopies B hS _ m) (b : U ⟶ disjointCopies B hS _ m) hab
  replace hab := (morphismFromCopies_app G _ s U a).symm.trans
    (hab.trans (morphismFromCopies_app G _ s U b))
  let Y := SmallEtale.final B S hS
  let T := Sieve.ofArrows (fun _ : Fin m => Y) (disjointCopiesι B hS Y m)
  have hT : T ∈ SmallEtale.topology B S hS (disjointCopies B hS Y m) :=
    ofArrows_disjointUnionHom_mem_topology B hS _
  have hcov : T.pullback a ⊓ T.pullback b ∈ SmallEtale.topology B S hS U :=
    GrothendieckTopology.intersection_covering _
      (GrothendieckTopology.pullback_stable _ a hT) (GrothendieckTopology.pullback_stable _ b hT)
  refine (SmallEtale.representedSheaf (disjointCopies B hS Y m)).property.isSeparated _ _ hcov
    a b fun V f hf => ?_
  refine (SmallEtale.representedSheaf_map _ f a).trans (Eq.trans ?_
    (SmallEtale.representedSheaf_map _ f b).symm)
  obtain ⟨i, g, hg⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf.1
  obtain ⟨j, g', hg'⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf.2
  have hgg : g = g' := (SmallEtale.finalIsTerminal B S hS).hom_ext _ _
  subst hgg
  change f ≫ a = f ≫ b
  rw [hg, hg']
  rcases isEmpty_or_nonempty ((SmallEtale.toScheme B S hS).obj V) with hV | ⟨⟨v⟩⟩
  · exact hom_ext B hS (isInitialOfIsEmpty.hom_ext _ _)
  suffices hij : i = j by rw [hij]
  have h1 : G.obj.map g.op (s i) = G.obj.map g.op (s j) := by
    have := congrArg (G.obj.map f.op) hab
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      hg, hg', op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
      map_disjointCopiesι_disjointCopiesSection, map_disjointCopiesι_disjointCopiesSection] at this
    exact this
  have hC := range_subset_germCoincidenceSet_of_map_eq G.obj g h1 ⟨v, rfl⟩
  have hw : (SmallEtale.toScheme B S hS).map g v ∈ connectedComponent (x.hom default) := by
    have : g = f ≫ (SmallEtale.finalIsTerminal B S hS).from U :=
      (SmallEtale.finalIsTerminal B S hS).hom_ext _ _
    rw [this, Functor.map_comp]
    exact hU ⟨_, rfl⟩
  have hx : x.hom default ∈ germCoincidenceSet G.obj (s i) (s j) :=
    (hG.isClopen_germCoincidenceSet (s i) (s j)).connectedComponent_subset hC
      ((connectedComponent_eq hw).subset mem_connectedComponent)
  by_contra hne
  exact hs hne (hx x rfl)

/-- **Injectivity of `Φ_{s,U}` over a connected scheme.** If `S` is connected, `G` is a sheaf
of sets with open difference loci on the small étale site of `S`, and `s_0, …, s_{m-1}` are
global sections of `G` with pairwise distinct germs at some geometric point `x` of `S`, then
`Φ_{s,U} : Hom_S(U, S^{⊔ m}) → G(U)` is injective for every object `U` of the site. -/
@[weil "lem_fk103_sections_morphism_injective_near_point"]
theorem injective_morphismFromCopies_app_of_connectedSpace [ConnectedSpace S]
    (G : smallEtaleTopos.{u, u} B S hS) (hG : HasOpenDifferenceLoci G.obj) {m : ℕ}
    (s : Fin m → G.obj.obj (op (SmallEtale.final B S hS))) (x : GeometricPoint S)
    (hs : Pairwise fun i j => germ G.obj (s i) x ≠ germ G.obj (s j) x)
    (U : SmallEtale B S hS) :
    Function.Injective ((morphismFromCopies G (SmallEtale.final B S hS) s).hom.app (op U)) :=
  have : PreconnectedSpace ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) :=
    inferInstanceAs (PreconnectedSpace S)
  injective_morphismFromCopies_app_of_range_subset_connectedComponent G hG s x hs U
    fun y _ => isPreconnected_univ.subset_connectedComponent (Set.mem_univ _) (Set.mem_univ y)

end Stacks.EtaleCohomology
