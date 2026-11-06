module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical

/-!
# The morphism from disjoint copies defined by a tuple of sections

Let `G` be a sheaf of sets on the small étale site of a scheme `S`, `Y` an object of the site
and `s = (s_0, …, s_{m-1})` an `m`-tuple of sections of `G` over `Y`. Since the inclusions
`ι_i : Y ⟶ Y^{⊔ m}` of the copies cover the disjoint union `Y^{⊔ m}`, and two different copies
meet in the empty scheme, there is a unique section `s^⊔` of `G` over `Y^{⊔ m}` whose
restriction along `ι_i` is `s_i` for every `i`. The section `s^⊔` corresponds by the Yoneda
lemma to the morphism of sheaves `Φ_s : Ỹ^{⊔ m} ⟶ G` from the sheaf represented by `Y^{⊔ m}`,
given by `Φ_{s,U}(a) = a^* s^⊔` for `a : U ⟶ Y^{⊔ m}`.

More generally, for a finite family `U_0, …, U_{n-1}` of objects of the site, sections
`s_k ∈ G(U_k)` glue uniquely to a section of `G` over the disjoint union `⊔ U_k`.

## Main definitions

* `Stacks.EtaleCohomology.disjointUnionSection`: the section of `G` over `⊔ U_k` glued from
  sections `s_k ∈ G(U_k)`.
* `Stacks.EtaleCohomology.disjointCopiesSection`: the section `s^⊔` of `G` over `Y^{⊔ m}`.
* `Stacks.EtaleCohomology.morphismFromCopies`: the morphism `Φ_s : Ỹ^{⊔ m} ⟶ G`.

## Main results

* `Stacks.EtaleCohomology.existsUnique_map_disjointUnionHom_eq`: sections over the members of
  a finite family glue uniquely over the disjoint union.
* `Stacks.EtaleCohomology.map_disjointCopiesι_disjointCopiesSection`,
  `Stacks.EtaleCohomology.eq_disjointCopiesSection`: `s^⊔` restricts to `s_i` on the `i`-th
  copy, and is the only such section.
* `Stacks.EtaleCohomology.morphismFromCopies_app`: `Φ_{s,U}(a) = a^* s^⊔`.
* `Stacks.EtaleCohomology.map_disjointCopiesι_comp_morphismFromCopies`: the restriction of
  `Φ_s` to the `i`-th copy is the morphism `Ỹ ⟶ G` defined by `s_i`.

## Implementation notes

The copies are indexed by `Fin m`. For `m = 0` no assumption on `G` is needed: `Y^{⊔ 0}` is
empty, and a sheaf has exactly one section over the empty scheme, since the empty family covers
it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], §I.3
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace Stacks.EtaleCohomology

variable {B : AlgebraicGeometry.BigEtaleSite.{u}} {S : AlgebraicGeometry.Scheme.{u}}
  {hS : B.Contains S}

/-- A sheaf of sets on the small étale site has at most one section over an object whose
underlying scheme is empty. -/
theorem subsingleton_sheaf_obj_of_isEmpty_toScheme
    (G : Sheaf (SmallEtale.topology B S hS) (Type v)) (Z : SmallEtale B S hS)
    (hZ : IsEmpty ((SmallEtale.toScheme B S hS).obj Z)) :
    Subsingleton (G.obj.obj (op Z)) := by
  have hcov : Sieve.ofArrows (fun _ : PEmpty.{1} => Z) (fun i => PEmpty.elim i) ∈
      SmallEtale.topology B S hS Z :=
    ofArrows_mem_topology B hS (fun _ : PEmpty.{1} => Z) (fun i => PEmpty.elim i) fun x =>
      hZ.elim x
  have hsf : Presieve.IsSheafFor G.obj
      (Presieve.ofArrows (fun _ : PEmpty.{1} => Z) (fun i => PEmpty.elim i)) :=
    (Presieve.isSheafFor_iff_generate _).2
      ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS) G.obj).1 G.property _ hcov)
  have h := (Presieve.isSheafFor_arrows_iff G.obj (fun i : PEmpty.{1} => PEmpty.elim i)).1 hsf
    (fun i => PEmpty.elim i) (fun i => PEmpty.elim i)
  exact ⟨fun _ _ => h.unique (fun i => PEmpty.elim i) (fun i => PEmpty.elim i)⟩

/-- **Sections over the members of a finite family glue uniquely over the disjoint union.**
For a sheaf of sets `G` on the small étale site and sections `s_k ∈ G(U_k)`, there is a unique
section of `G` over `⊔ U_k` whose restriction to `U_k` is `s_k` for every `k`. -/
theorem existsUnique_map_disjointUnionHom_eq
    (G : Sheaf (SmallEtale.topology B S hS) (Type v)) {n : ℕ} (U : Fin n → SmallEtale B S hS)
    (s : ∀ k, G.obj.obj (op (U k))) :
    ∃! t : G.obj.obj (op (disjointUnionObj B hS U)),
      ∀ k, G.obj.map (disjointUnionHom B hS U k).op t = s k := by
  classical
  have hcomp : Presieve.Arrows.Compatible G.obj (disjointUnionHom B hS U) s := by
    intro i j Z a b hab
    by_cases hij : i = j
    · subst hij
      have hu : (SmallEtale.toScheme B S hS).map a = (SmallEtale.toScheme B S hS).map b :=
        (cancel_mono (Sigma.ι (fun k => (SmallEtale.toScheme B S hS).obj (U k)) i)).mp
          (congrArg (SmallEtale.toScheme B S hS).map hab)
      rw [hom_ext B hS hu]
    · have hempty : IsEmpty ((SmallEtale.toScheme B S hS).obj Z) :=
        AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne
          (g := fun k => (SmallEtale.toScheme B S hS).obj (U k))
          ⟨congrArg (SmallEtale.toScheme B S hS).map hab⟩ hij
      have := subsingleton_sheaf_obj_of_isEmpty_toScheme G Z hempty
      exact Subsingleton.elim _ _
  have hsf : Presieve.IsSheafFor G.obj (Presieve.ofArrows U (disjointUnionHom B hS U)) :=
    (Presieve.isSheafFor_iff_generate _).2
      ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS) G.obj).1 G.property _
        (ofArrows_disjointUnionHom_mem_topology B hS U))
  exact (Presieve.isSheafFor_arrows_iff G.obj (disjointUnionHom B hS U)).1 hsf s hcomp

/-- The section of a sheaf `G` over the disjoint union `⊔ U_k` glued from sections
`s_k ∈ G(U_k)`. -/
def disjointUnionSection (G : Sheaf (SmallEtale.topology B S hS) (Type v)) {n : ℕ}
    (U : Fin n → SmallEtale B S hS) (s : ∀ k, G.obj.obj (op (U k))) :
    G.obj.obj (op (disjointUnionObj B hS U)) :=
  (existsUnique_map_disjointUnionHom_eq G U s).exists.choose

/-- The glued section restricts to `s_k` on `U_k`. -/
@[simp]
theorem map_disjointUnionHom_disjointUnionSection
    (G : Sheaf (SmallEtale.topology B S hS) (Type v)) {n : ℕ} (U : Fin n → SmallEtale B S hS)
    (s : ∀ k, G.obj.obj (op (U k))) (k : Fin n) :
    G.obj.map (disjointUnionHom B hS U k).op (disjointUnionSection G U s) = s k :=
  (existsUnique_map_disjointUnionHom_eq G U s).exists.choose_spec k

/-- The glued section is the only section restricting to `s_k` on every `U_k`. -/
theorem eq_disjointUnionSection (G : Sheaf (SmallEtale.topology B S hS) (Type v)) {n : ℕ}
    (U : Fin n → SmallEtale B S hS) (s : ∀ k, G.obj.obj (op (U k)))
    (t : G.obj.obj (op (disjointUnionObj B hS U)))
    (ht : ∀ k, G.obj.map (disjointUnionHom B hS U k).op t = s k) :
    t = disjointUnionSection G U s :=
  (existsUnique_map_disjointUnionHom_eq G U s).unique ht
    (map_disjointUnionHom_disjointUnionSection G U s)

/-- Two sections of a sheaf over the disjoint union that agree on every member are equal. -/
theorem sheaf_section_disjointUnion_ext (G : Sheaf (SmallEtale.topology B S hS) (Type v))
    {n : ℕ} (U : Fin n → SmallEtale B S hS) {t t' : G.obj.obj (op (disjointUnionObj B hS U))}
    (h : ∀ k, G.obj.map (disjointUnionHom B hS U k).op t =
      G.obj.map (disjointUnionHom B hS U k).op t') :
    t = t' :=
  (eq_disjointUnionSection G U _ t h).trans (eq_disjointUnionSection G U _ t' fun _ => rfl).symm

/-- **The section `s^⊔` of `G` over `Y^{⊔ m}`** defined by an `m`-tuple `s` of sections of `G`
over `Y`: the unique section whose restriction along the inclusion `ι_i` of the `i`-th copy is
`s_i`. -/
@[weil "def_fk103_morphism_from_copies_defined_by_sections"]
abbrev disjointCopiesSection (G : Sheaf (SmallEtale.topology B S hS) (Type v))
    (Y : SmallEtale B S hS) {m : ℕ} (s : Fin m → G.obj.obj (op Y)) :
    G.obj.obj (op (disjointCopies B hS Y m)) :=
  disjointUnionSection G (fun _ : Fin m => Y) s

/-- `s^⊔` restricts to `s_i` along the inclusion `ι_i` of the `i`-th copy. -/
@[weil "def_fk103_morphism_from_copies_defined_by_sections", simp]
theorem map_disjointCopiesι_disjointCopiesSection
    (G : Sheaf (SmallEtale.topology B S hS) (Type v)) (Y : SmallEtale B S hS) {m : ℕ}
    (s : Fin m → G.obj.obj (op Y)) (i : Fin m) :
    G.obj.map (disjointCopiesι B hS Y m i).op (disjointCopiesSection G Y s) = s i :=
  map_disjointUnionHom_disjointUnionSection G (fun _ : Fin m => Y) s i

/-- `s^⊔` is the only section of `G` over `Y^{⊔ m}` restricting to `s_i` on every copy. -/
@[weil "def_fk103_morphism_from_copies_defined_by_sections"]
theorem eq_disjointCopiesSection (G : Sheaf (SmallEtale.topology B S hS) (Type v))
    (Y : SmallEtale B S hS) {m : ℕ} (s : Fin m → G.obj.obj (op Y))
    (t : G.obj.obj (op (disjointCopies B hS Y m)))
    (ht : ∀ i, G.obj.map (disjointCopiesι B hS Y m i).op t = s i) :
    t = disjointCopiesSection G Y s :=
  eq_disjointUnionSection G (fun _ : Fin m => Y) s t ht

/-- **The morphism `Φ_s : Ỹ^{⊔ m} ⟶ G`** defined by an `m`-tuple `s` of sections of a sheaf of
sets `G` over `Y`: it sends `a : U ⟶ Y^{⊔ m}` to `a^* s^⊔`. -/
@[weil "def_fk103_morphism_from_copies_defined_by_sections"]
def morphismFromCopies (G : smallEtaleTopos.{u, u} B S hS) (Y : SmallEtale B S hS) {m : ℕ}
    (s : Fin m → G.obj.obj (op Y)) :
    SmallEtale.representedSheaf (disjointCopies B hS Y m) ⟶ G :=
  (SmallEtale.topology B S hS).yonedaEquiv.symm (disjointCopiesSection G Y s)

/-- `Φ_{s,U}(a) = a^* s^⊔` for `a : U ⟶ Y^{⊔ m}`. -/
@[weil "def_fk103_morphism_from_copies_defined_by_sections", simp]
theorem morphismFromCopies_app (G : smallEtaleTopos.{u, u} B S hS) (Y : SmallEtale B S hS)
    {m : ℕ} (s : Fin m → G.obj.obj (op Y)) (U : SmallEtale B S hS)
    (a : U ⟶ disjointCopies B hS Y m) :
    (morphismFromCopies G Y s).hom.app (op U) a = G.obj.map a.op (disjointCopiesSection G Y s) :=
  GrothendieckTopology.yonedaEquiv_symm_app_apply _ _ (op U) a

/-- `Φ_s` corresponds to `s^⊔` under the Yoneda bijection. -/
theorem yonedaEquiv_morphismFromCopies (G : smallEtaleTopos.{u, u} B S hS)
    (Y : SmallEtale B S hS) {m : ℕ} (s : Fin m → G.obj.obj (op Y)) :
    (SmallEtale.topology B S hS).yonedaEquiv (morphismFromCopies G Y s) =
      disjointCopiesSection G Y s :=
  Equiv.apply_symm_apply _ _

/-- The restriction of `Φ_s` to the `i`-th copy is the morphism `Ỹ ⟶ G` defined by `s_i`. -/
theorem map_disjointCopiesι_comp_morphismFromCopies (G : smallEtaleTopos.{u, u} B S hS)
    (Y : SmallEtale B S hS) {m : ℕ} (s : Fin m → G.obj.obj (op Y)) (i : Fin m) :
    (smallEtaleYoneda B S hS).map (disjointCopiesι B hS Y m i) ≫ morphismFromCopies G Y s =
      (SmallEtale.topology B S hS).yonedaEquiv.symm (s i) := by
  apply (SmallEtale.topology B S hS).yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, ← map_disjointCopiesι_disjointCopiesSection G Y s i,
    ← morphismFromCopies_app]
  rfl

end Stacks.EtaleCohomology

end
