module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleQuasiCompact
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion

/-!
# A stalkwise surjective family onto a constructible sheaf has a finite subfamily

Let `X` be a quasi-compact and quasi-separated scheme and `F` a constructible sheaf of sets on
the small étale site of `X`. If a family `(φᵢ : Fᵢ ⟶ F)_{i ∈ I}` of morphisms of sheaves of sets
is surjective, in the sense that every element of every stalk `F_x` at a geometric point `x` of
`X` lies in the image of some `(φᵢ)ₓ`, then a finite subfamily is already surjective in the same
sense.

The proof goes through quasi-compactness in the topos of sheaves of sets. A constructible sheaf
receives an epimorphism from a finite coproduct of sheaves represented by quasi-compact étale
objects (Stacks, Tag 09Y9); the sheaf represented by a quasi-compact object of the small étale
site is a quasi-compact object of the topos (Stacks, Tag 0D06), finite coproducts of quasi-compact
sheaves are quasi-compact, and quasi-compactness passes along surjections (Stacks, Tag 0GMP). So
`F` is quasi-compact, and it remains to compare surjectivity of a family on stalks with local
surjectivity of the induced map out of the coproduct, which is done through germs at the
geometric points with algebraically closed residue field attached to the points of étale
objects.

## Main results

* `AlgebraicGeometry.isQuasiCompact_of_isConstructibleSetSheaf`: a constructible sheaf of sets is
  a quasi-compact object of the topos of sheaves of sets.
* `AlgebraicGeometry.SmallEtale.exists_sieve_of_forall_exists_sheafFiber_map_eq`: a family which
  is surjective on all stalks at geometric points is locally surjective on sections.
* `AlgebraicGeometry.SmallEtale.exists_sheafFiber_map_eq_of_exists_sieve`: the converse.
* `AlgebraicGeometry.exists_finset_forall_exists_sheafFiber_map_eq_of_isConstructibleSetSheaf`:
  the finite subfamily.

## Implementation notes

The scheme is assumed quasi-compact and quasi-separated rather than Noetherian; a scheme whose
underlying space is Noetherian is both. Stalks are taken at geometric points with algebraically
closed residue field, the fibres of `AlgebraicGeometry.geometricPointSitePoint`; the index type of
the family is arbitrary.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 0D06](https://stacks.math.columbia.edu/tag/0D06)
* [Stacks Project, Tag 0GMP](https://stacks.math.columbia.edu/tag/0GMP)
-/

/- FK's proof (Noetherian induction over
generic étale neighbourhoods) is replaced by the quasi-compactness argument of Stacks 09Y9. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A family of morphisms of sheaves of sets on the small étale site which is surjective on the
stalk at every geometric point is locally surjective on sections: every section of the target is,
on a covering sieve, the image of a section of a single member of the family. -/
theorem exists_sieve_of_forall_exists_sheafFiber_map_eq {ι : Type*}
    {G : ι → Sheaf (topology B S hS) (Type (u + 1))} {F : Sheaf (topology B S hS) (Type (u + 1))}
    (φ : ∀ i, G i ⟶ F)
    (h : ∀ (x : GeometricPoint S) (a : (geometricPointSitePoint B S hS x).sheafFiber.obj F),
      ∃ (i : ι) (b : (geometricPointSitePoint B S hS x).sheafFiber.obj (G i)),
        (geometricPointSitePoint B S hS x).sheafFiber.map (φ i) b = a)
    {U : SmallEtale B S hS} (s : F.obj.obj (op U)) :
    ∃ T : Sieve U, T ∈ topology B S hS U ∧
      ∀ ⦃V : SmallEtale B S hS⦄ (g : V ⟶ U), T g →
        ∃ (i : ι) (t : (G i).obj.obj (op V)), (φ i).hom.app (op V) t = F.obj.map g.op s := by
  let T : Sieve U :=
    { arrows := fun V g => ∃ (i : ι) (t : (G i).obj.obj (op V)),
        (φ i).hom.app (op V) t = F.obj.map g.op s
      downward_closed := by
        rintro V W g ⟨i, t, ht⟩ f
        refine ⟨i, (G i).obj.map f.op t, ?_⟩
        rw [NatTrans.naturality_apply, ht, op_comp, Functor.map_comp, types_comp_apply] }
  refine ⟨T, ?_, fun V g hg => hg⟩
  apply mem_topology_of_jointlySurjective
  intro x
  let s₀ := geometricPointOfEtalePoint B S hS U x
  let Φ := geometricPointSitePoint B S hS s₀
  let p : Φ.fiber.obj U := geometricPointOfEtalePointLift B S hS U x
  obtain ⟨i, z, hz⟩ := h s₀ (Φ.toPresheafFiber U p F.obj s)
  obtain ⟨W, y, c, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := (G i).obj) z
  replace hz : (Φ.presheafFiber.map (φ i).hom) (Φ.toPresheafFiber W y (G i).obj c) =
      Φ.toPresheafFiber U p F.obj s := hz
  rw [Φ.toPresheafFiber_naturality_apply (φ i).hom] at hz
  let ZW : Φ.fiber.Elements := ⟨W, y⟩
  let ZV : Φ.fiber.Elements := ⟨U, p⟩
  let Z : Φ.fiber.Elements := IsCofiltered.min ZW ZV
  let l : Z ⟶ ZW := IsCofiltered.minToLeft ZW ZV
  let r : Z ⟶ ZV := IsCofiltered.minToRight ZW ZV
  have hl : Φ.toPresheafFiber Z.1 Z.2 F.obj (F.obj.map l.1.op ((φ i).hom.app (op W) c)) =
      Φ.toPresheafFiber W y F.obj ((φ i).hom.app (op W) c) := by
    rw [Φ.toPresheafFiber_w_apply, l.2]
  have hr : Φ.toPresheafFiber Z.1 Z.2 F.obj (F.obj.map r.1.op s) =
      Φ.toPresheafFiber U p F.obj s := by
    rw [Φ.toPresheafFiber_w_apply, r.2]
  obtain ⟨Y, f, y', hy', heq⟩ :=
    (Φ.toPresheafFiber_eq_iff' (P := F.obj) Z.1 Z.2 (F.obj.map l.1.op ((φ i).hom.app (op W) c))
      (F.obj.map r.1.op s)).1 (hl.trans (hz.trans hr.symm))
  refine ⟨Y, f ≫ r.1, ⟨i, (G i).obj.map (f ≫ l.1).op c, ?_⟩, ?_⟩
  · rw [NatTrans.naturality_apply, op_comp, op_comp, F.obj.map_comp, F.obj.map_comp,
      types_comp_apply, types_comp_apply]
    exact heq
  · have h1 : y'.1 ≫ (toScheme B S hS).map f = Z.2.1 := congrArg Subtype.val hy'
    have h2 : Z.2.1 ≫ (toScheme B S hS).map r.1 = p.1 := congrArg Subtype.val r.2
    refine ⟨y'.1 default, ?_⟩
    rw [← geometricPointOfEtalePointLift_base B S hS U x]
    change (y'.1 ≫ (toScheme B S hS).map (f ≫ r.1)) default = p.1 default
    rw [Functor.map_comp, ← Category.assoc, h1, h2]

/-- Conversely, a family of morphisms of sheaves of sets on the small étale site which is
locally surjective on sections, through members satisfying a predicate `P`, is surjective on
every stalk at a geometric point through members satisfying `P`. -/
theorem exists_sheafFiber_map_eq_of_exists_sieve {ι : Type*}
    {G : ι → Sheaf (topology B S hS) (Type (u + 1))} {F : Sheaf (topology B S hS) (Type (u + 1))}
    (φ : ∀ i, G i ⟶ F) (P : ι → Prop)
    (h : ∀ ⦃U : SmallEtale B S hS⦄ (s : F.obj.obj (op U)),
      ∃ T : Sieve U, T ∈ topology B S hS U ∧
        ∀ ⦃V : SmallEtale B S hS⦄ (g : V ⟶ U), T g →
          ∃ (i : ι), P i ∧ ∃ (t : (G i).obj.obj (op V)),
            (φ i).hom.app (op V) t = F.obj.map g.op s)
    (x : GeometricPoint S) (a : (geometricPointSitePoint B S hS x).sheafFiber.obj F) :
    ∃ (i : ι), P i ∧ ∃ (b : (geometricPointSitePoint B S hS x).sheafFiber.obj (G i)),
      (geometricPointSitePoint B S hS x).sheafFiber.map (φ i) b = a := by
  let Φ := geometricPointSitePoint B S hS x
  obtain ⟨U, u, s, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) a
  obtain ⟨T, hT, hTs⟩ := h s
  obtain ⟨Y, f, hf, y, rfl⟩ := Φ.jointly_surjective T hT u
  obtain ⟨i, hi, t, ht⟩ := hTs f hf
  refine ⟨i, hi, Φ.toPresheafFiber Y y (G i).obj t, ?_⟩
  change (Φ.presheafFiber.map (φ i).hom) (Φ.toPresheafFiber Y y (G i).obj t) = _
  rw [Φ.toPresheafFiber_naturality_apply (φ i).hom, ht, Φ.toPresheafFiber_w_apply]

end SmallEtale

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance 2000] Sheaf.instHasFiniteColimits

/-- A constructible sheaf of sets on the small étale site of a quasi-compact and quasi-separated
scheme is a quasi-compact object of the topos of sheaves of sets: it receives an epimorphism from
a finite coproduct of sheaves represented by quasi-compact étale objects, each of which is
quasi-compact. -/
theorem isQuasiCompact_of_isConstructibleSetSheaf (B : BigEtaleSite.{u}) (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (hF : IsConstructibleSetSheaf B X F) : Sheaf.IsQuasiCompact F := by
  obtain ⟨n, U, hU, p, hp⟩ := exists_finite_representable_epi_of_isConstructibleSetSheaf B X F hF
  let A : ULift.{u + 1} (Fin n) → Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)) :=
    fun k => (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U k.down)
  have hA : ∀ k, Sheaf.IsQuasiCompact (A k) := fun k => by
    exact (GrothendieckTopology.isQuasiCompactObject_iff_isQuasiCompact_sheafifiedYoneda _
      (U k.down)).1 (SmallEtale.isQuasiCompactObject_of_compactSpace B X.obj X.property
        (U k.down) (hU k.down).1)
  let m : ∐ A ⟶ ∐ fun k : Fin n =>
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U k) :=
    Sigma.desc fun k => Sigma.ι (fun k : Fin n =>
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U k)) k.down
  let m' : (∐ fun k : Fin n =>
      (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj (U k)) ⟶ ∐ A :=
    Sigma.desc fun k => Sigma.ι A (ULift.up k)
  have hmm : m' ≫ m = 𝟙 _ := by
    apply Sigma.hom_ext
    intro k
    rw [Category.comp_id, Sigma.ι_desc_assoc, Sigma.ι_desc]
  have : IsSplitEpi m := ⟨⟨⟨m', hmm⟩⟩⟩
  exact Sheaf.isQuasiCompact_of_isLocallySurjective (m ≫ p)
    ((Sheaf.isLocallySurjective_iff_epi _).2 inferInstance)
    (Sheaf.isQuasiCompact_sigmaObj_of_finite A hA)

/-- **A stalkwise surjective family onto a constructible sheaf has a finite subfamily.** Let `F`
be a constructible sheaf of sets on the small étale site of a quasi-compact and quasi-separated
scheme `X`, and `(φᵢ : Gᵢ ⟶ F)_{i ∈ I}` a family of morphisms of sheaves of sets such that, for
every geometric point `x` of `X`, the stalk `F_x` is the union of the images of the `(φᵢ)ₓ`. Then
there is a finite subset `J ⊆ I` such that, for every geometric point `x`, the stalk `F_x` is the
union of the images of the `(φᵢ)ₓ` with `i ∈ J`. -/
@[weil "lem_fk104_constructible_surjective_family_finite_subfamily"]
theorem exists_finset_forall_exists_sheafFiber_map_eq_of_isConstructibleSetSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))}
    (hF : IsConstructibleSetSheaf B X F) {I : Type*}
    {G : I → Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (φ : ∀ i, G i ⟶ F)
    (hφ : ∀ (x : GeometricPoint X.obj)
      (a : (geometricPointSitePoint B X.obj X.property x).sheafFiber.obj F),
      ∃ (i : I) (b : (geometricPointSitePoint B X.obj X.property x).sheafFiber.obj (G i)),
        (geometricPointSitePoint B X.obj X.property x).sheafFiber.map (φ i) b = a) :
    ∃ J : Finset I, ∀ (x : GeometricPoint X.obj)
      (a : (geometricPointSitePoint B X.obj X.property x).sheafFiber.obj F),
      ∃ i ∈ J, ∃ (b : (geometricPointSitePoint B X.obj X.property x).sheafFiber.obj (G i)),
        (geometricPointSitePoint B X.obj X.property x).sheafFiber.map (φ i) b = a := by
  classical
  -- Replace the index type by the set of images of the `φᵢ`, which lives in the universe of
  -- the sheaves.
  let R : I → ((V : (SmallEtale B X.obj X.property)ᵒᵖ) → Set (F.obj.obj V)) :=
    fun i V => Set.range ((φ i).hom.app V)
  let I' := Set.range R
  let c : I' → I := fun S => S.2.choose
  have hc : ∀ S : I', R (c S) = S.1 := fun S => S.2.choose_spec
  let φ' : ∀ S : I', G (c S) ⟶ F := fun S => φ (c S)
  have hloc : Sheaf.IsLocallySurjective (Sigma.desc φ') := by
    refine (Sheaf.isLocallySurjective_sigmaDesc_iff φ').2 fun U s => ?_
    obtain ⟨T, hT, hTs⟩ := SmallEtale.exists_sieve_of_forall_exists_sheafFiber_map_eq φ hφ s
    refine ⟨T, hT, fun V g hg => ?_⟩
    obtain ⟨i, t, ht⟩ := hTs g hg
    let S : I' := ⟨R i, i, rfl⟩
    have hmem : F.obj.map g.op s ∈ R (c S) (op V) := by
      rw [hc S]
      exact ⟨t, ht⟩
    obtain ⟨t', ht'⟩ := hmem
    exact ⟨S, t', ht'⟩
  obtain ⟨T, hT, hTloc⟩ := isQuasiCompact_of_isConstructibleSetSheaf B X hF I' (fun S => G (c S))
    φ' hloc
  refine ⟨hT.toFinset.image c, fun x a => ?_⟩
  refine SmallEtale.exists_sheafFiber_map_eq_of_exists_sieve φ (· ∈ hT.toFinset.image c)
    (fun U s => ?_) x a
  obtain ⟨T', hT', hT's⟩ := (Sheaf.isLocallySurjective_sigmaDesc_iff _).1 hTloc s
  refine ⟨T', hT', fun V g hg => ?_⟩
  obtain ⟨j, t, ht⟩ := hT's g hg
  exact ⟨c j.1, Finset.mem_image_of_mem c (hT.mem_toFinset.2 j.2), t, ht⟩

end AlgebraicGeometry
