module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Sections of an étale sheaf are determined by their germs over a detecting set

Let `B` be a big étale site containing a scheme `S`, let `F` be a sheaf of sets on the small
étale site of `S`, and let `P ⊆ S` be a detecting set of points. Two sections `s t` of `F` over
an object `U` of the site which have the same germ at every geometric point of `U` lying over a
point of `P` are equal.

The proof follows Freitag–Kiehl. The union `E ⊆ U` of the images of the étale morphisms
`V ⟶ U` along which `s` and `t` agree is open, since étale morphisms are open. A point of `U`
over `P` lies in `E`: at the geometric point it carries, the germs of `s` and `t` agree, so `s`
and `t` agree on an étale neighbourhood of it. As `P` is detecting, the closed complement of `E`
is empty, so the sieve of arrows along which `s` and `t` agree is jointly surjective, hence
covering, and `s = t` because `F` is separated.

## Main results

* `AlgebraicGeometry.SmallEtale.IsDetecting.eq_of_toPresheafFiber_eq` — sections of an étale
  sheaf of sets with the same germs at all geometric points over a detecting set are equal.

## Implementation notes

The site is the small étale site of [Stacks, Tag 021B] and the geometric points are those of
[Stacks, Tag 03PO], with algebraically closed residue field. A geometric point of `U` is recorded
as a geometric point `x` of `S` together with a lift `q` of `x` to `U`; its germs are those of
the point `AlgebraicGeometry.geometricPointSitePoint` of the site. The objects `U` are arbitrary
objects of the small étale site, not only noetherian separated ones, and no quasi-compactness is
needed: a jointly surjective sieve is covering.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale.IsDetecting

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Sections are determined by their germs over a detecting set.** Let `F` be a sheaf of sets
on the small étale site of `S` and `P ⊆ S` detecting. If two sections `s t` over `U` have the same
germ at every geometric point of `U` (a geometric point `x` of `S` with a lift `q` to `U`) whose
image in `S` lies in `P`, then `s = t`. -/
@[weil "lem_fk102_sections_determined_by_germs"]
theorem eq_of_toPresheafFiber_eq [UnivLE.{u, w}] {P : Set S} (hP : IsDetecting B S hS P)
    (F : Sheaf (SmallEtale.topology B S hS) (Type w)) (U : SmallEtale B S hS)
    (s t : F.obj.obj (op U))
    (h : ∀ (x : GeometricPoint S) (q : (geometricPointFiber B S hS x).obj U),
      x.hom default ∈ P →
        (geometricPointSitePoint B S hS x).toPresheafFiber U q F.obj s =
          (geometricPointSitePoint B S hS x).toPresheafFiber U q F.obj t) :
    s = t := by
  let R : Sieve U := Presheaf.equalizerSieve (F := F.obj) s t
  let E : Set ((toScheme B S hS).obj U) :=
    ⋃ (Y : SmallEtale B S hS) (g : Y ⟶ U) (_ : R g), Set.range ((toScheme B S hS).map g)
  have hE : IsOpen E :=
    isOpen_iUnion fun Y ↦ isOpen_iUnion fun g ↦ isOpen_iUnion fun _ ↦
      ((toScheme B S hS).map g).isOpenMap.isOpen_range
  have hEuniv : E = Set.univ := by
    by_contra hne
    obtain ⟨x, hxE, hxP⟩ := hP.exists_mem U hE.isClosed_compl
      ((Set.nonempty_compl).2 hne)
    apply hxE
    let xs := geometricPointOfEtalePoint B S hS U x
    let q := geometricPointOfEtalePointLift B S hS U x
    have hxs : xs.hom default ∈ P := by
      have := geometricPointOfEtalePointLift_base B S hS U x
      change ((GeometricPoint.ofPoint _ x).hom ≫ B.inclusion.map U.obj.hom) default ∈ P
      rw [Scheme.Hom.comp_apply]
      change (B.inclusion.map U.obj.hom)
        ((geometricPointOfEtalePointLift B S hS U x).1 default) ∈ P
      rw [this]
      exact hxP
    obtain ⟨Y, g, y, hy, hgst⟩ :=
      ((geometricPointSitePoint B S hS xs).toPresheafFiber_eq_iff' U q _ _).mp (h xs q hxs)
    refine Set.mem_iUnion.2 ⟨Y, Set.mem_iUnion.2 ⟨g, Set.mem_iUnion.2 ⟨hgst, ?_⟩⟩⟩
    refine ⟨y.1 default, ?_⟩
    have h1 : y.1 ≫ (toScheme B S hS).map g = q.1 := congrArg Subtype.val hy
    rw [← geometricPointOfEtalePointLift_base B S hS U x]
    change ((y.1 ≫ (toScheme B S hS).map g)) default = q.1 default
    rw [h1]
  have hR : R ∈ SmallEtale.topology B S hS U := by
    refine SmallEtale.mem_topology_of_jointlySurjective fun x ↦ ?_
    have hx : x ∈ E := hEuniv ▸ Set.mem_univ x
    simp only [E, Set.mem_iUnion] at hx
    obtain ⟨Y, g, hg, hx⟩ := hx
    exact ⟨Y, g, hg, hx⟩
  exact F.property.isSeparated _ _ hR _ _ fun _ _ hf ↦ hf

end AlgebraicGeometry.SmallEtale.IsDetecting

end
