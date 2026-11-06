module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable
public import Weil.AlgebraicGeometry.Sites.Bridges.ConstantSheaf
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical

/-!
# The sheaf represented by disjoint copies of the base is constant

Let `S` be a scheme in a big étale site and `m : ℕ`. Let `S^{⊔ m}` be the disjoint union of `m`
copies of the final object `S / S` of the small étale site, with inclusions `ι_i`. The sheaf
`S^{⊔ m}~` represented by `S^{⊔ m}` is the constant sheaf `(Fin m)_S` of locally constant
`Fin m`-valued maps.

For an object `W` of the small étale site, an `S`-morphism `a : W ⟶ S^{⊔ m}` is sent to the
locally constant map `k_a : |W| → Fin m` with `k_a(w) = i` if and only if `a(w)` lies in the
`i`-th copy. These maps are compatible with restriction. The resulting morphism of sheaves is
locally injective and locally surjective: on the open subscheme `k⁻¹{i}` of `W` where a locally
constant map `k` takes the value `i`, every `S`-morphism `a` with `k_a = k` is `ι_i ∘ π`, with
`π` the structure morphism. Hence it is an isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.copyIndex` — the locally constant map `|S^{⊔ m}| → Fin m` sending a
  point to the index of the copy it lies in.
* `Stacks.EtaleCohomology.representedSheafDisjointCopiesToLocallyConstantSheaf` — the morphism
  `a ↦ k_a` from `S^{⊔ m}~` to the constant sheaf.
* `Stacks.EtaleCohomology.representedSheafDisjointCopiesIso` — the isomorphism
  `S^{⊔ m}~ ≅ (Fin m)_S`.
* `Stacks.EtaleCohomology.representedSheafDisjointCopiesIsoOfFinite` — the isomorphism
  `S^{⊔ |E|}~ ≅ E_S` for a finite set `E`.
* `Stacks.EtaleCohomology.sheafEquivInverseObjRepresentedSheafDisjointCopiesIso` — the same
  isomorphism on the category `Et(S)` of noetherian separated étale `S`-schemes, for a locally
  noetherian `S`.

## Main results

* `Stacks.EtaleCohomology.eq_comp_disjointCopiesι_of_range_subset` — an `S`-morphism into
  `S^{⊔ m}` whose image lies in the `i`-th copy is `ι_i ∘ π`.

## Implementation notes

The statement is made on the small étale site `SmallEtale B S hS` of an arbitrary scheme `S`;
no noetherian or separatedness hypothesis is needed. The copies are indexed by `Fin m`. The
constant sheaf is the sheaf of locally constant maps,
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantSheafSmallEtale`; its
restriction to the category of noetherian separated étale `S`-schemes is the constant presheaf
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheaf`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], Appendix A I
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) {S : AlgebraicGeometry.Scheme.{u}}
  (hS : B.Contains S)

theorem exists_mem_range_sigmaι_fin {m : ℕ} (g : Fin m → Scheme.{u}) (y : (∐ g :)) :
    ∃ i, y ∈ Set.range (Sigma.ι g i).base := by
  obtain ⟨k, hk⟩ := (sigmaOpenCover g).exists_eq y
  exact ⟨k, hk⟩

theorem eq_of_mem_range_sigmaι {m : ℕ} (g : Fin m → Scheme.{u}) {y : (∐ g :)} {i j : Fin m}
    (hi : y ∈ Set.range (Sigma.ι g i).base) (hj : y ∈ Set.range (Sigma.ι g j).base) :
    i = j := by
  by_contra hne
  have hd := disjoint_opensRange_sigmaι g i j hne
  exact (eq_bot_iff.mp (disjoint_iff.mp hd) (show y ∈ _ ⊓ _ from ⟨hi, hj⟩) :)

/-- The index of the copy containing a point of a coproduct of schemes indexed by `Fin m`, as a
locally constant map. -/
def copyIndex {m : ℕ} (g : Fin m → Scheme.{u}) : LocallyConstant (∐ g :) (Fin m) where
  toFun y := Classical.choose (exists_mem_range_sigmaι_fin g y)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro i
    have : (fun y => Classical.choose (exists_mem_range_sigmaι_fin g y)) ⁻¹' {i} =
        Set.range (Sigma.ι g i).base := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => h ▸ Classical.choose_spec (exists_mem_range_sigmaι_fin g y), fun h =>
        eq_of_mem_range_sigmaι g (Classical.choose_spec (exists_mem_range_sigmaι_fin g y)) h⟩
    rw [this]
    exact (Sigma.ι g i).opensRange.2

theorem copyIndex_eq_iff {m : ℕ} (g : Fin m → Scheme.{u}) (y : (∐ g :)) (i : Fin m) :
    copyIndex g y = i ↔ y ∈ Set.range (Sigma.ι g i).base :=
  ⟨fun h => h ▸ Classical.choose_spec (exists_mem_range_sigmaι_fin g y), fun h =>
    eq_of_mem_range_sigmaι g (Classical.choose_spec (exists_mem_range_sigmaι_fin g y)) h⟩

@[simp]
theorem copyIndex_ι {m : ℕ} (g : Fin m → Scheme.{u}) (i : Fin m) (x : g i) :
    copyIndex g ((Sigma.ι g i).base x) = i :=
  (copyIndex_eq_iff g _ i).2 ⟨x, rfl⟩

/-- An `S`-morphism into `S^{⊔ m}` whose image lies in the `i`-th copy is `ι_i ∘ π`, with
`π` the morphism to the final object. -/
theorem eq_comp_disjointCopiesι_of_range_subset {m : ℕ} (Z : SmallEtale B S hS)
    (a : Z ⟶ disjointCopies B hS (SmallEtale.final B S hS) m) (i : Fin m)
    (h : Set.range ((SmallEtale.toScheme B S hS).map a).base ⊆
      Set.range (Sigma.ι (fun _ : Fin m => (SmallEtale.toScheme B S hS).obj
        (SmallEtale.final B S hS)) i).base) :
    a = (SmallEtale.finalIsTerminal B S hS).from Z ≫
      disjointCopiesι B hS (SmallEtale.final B S hS) m i := by
  set π := (SmallEtale.finalIsTerminal B S hS).from Z
  let F := SmallEtale.toScheme B S hS
  let g : Fin m → Scheme.{u} := fun _ => F.obj (SmallEtale.final B S hS)
  let φ : F.obj Z ⟶ ∐ g := F.map a
  let b := IsOpenImmersion.lift (Sigma.ι g i) φ h
  have hb : b ≫ Sigma.ι g i = φ := IsOpenImmersion.lift_fac _ _ _
  apply hom_ext B hS
  change φ = F.map (π ≫ disjointCopiesι B hS (SmallEtale.final B S hS) m i)
  rw [Functor.map_comp, toScheme_map_disjointCopiesι, ← hb]
  congr 1
  have hπ := toScheme_map_comp_hom B hS π
  have hb' : b ≫ B.inclusion.map (SmallEtale.final B S hS).obj.hom =
      B.inclusion.map Z.obj.hom := by
    have h2 := ι_comp_inclusion_map_hom_disjointUnionObj B hS
      (fun _ : Fin m => SmallEtale.final B S hS) i
    have h3 := toScheme_map_comp_hom B hS a
    rw [← h2]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans h3)
  have hid : B.inclusion.map (SmallEtale.final B S hS).obj.hom = 𝟙 _ := by
    simp [SmallEtale.final]
  have h' := hπ.trans hb'.symm
  rw [hid] at h'
  exact ((Category.comp_id _).symm.trans (h'.trans (Category.comp_id _))).symm

/-- **The morphism `a ↦ k_a` from `S^{⊔ m}~` to the constant sheaf.** An `S`-morphism
`a : W ⟶ S^{⊔ m}` is sent to the locally constant map `k_a : |W| → Fin m`, `k_a(w)` being the
index of the copy containing `a(w)`. -/
def representedSheafDisjointCopiesToLocallyConstantSheaf (m : ℕ) :
    SmallEtale.representedSheaf (disjointCopies B hS (SmallEtale.final B S hS) m) ⟶
      SmallNoetherianSeparatedEtale.locallyConstantSheafSmallEtale B S hS (Fin m) :=
  ⟨{ app := fun W => TypeCat.ofHom fun a =>
        (copyIndex fun _ : Fin m => (SmallEtale.toScheme B S hS).obj
          (SmallEtale.final B S hS)).comap
          ((SmallEtale.toScheme B S hS).map (show W.unop ⟶ _ from a)).base.hom
     naturality := fun _ _ _ => rfl }⟩

theorem representedSheafDisjointCopiesToLocallyConstantSheaf_app_apply (m : ℕ)
    (W : SmallEtale B S hS) (a : W ⟶ disjointCopies B hS (SmallEtale.final B S hS) m)
    (x : (SmallEtale.toScheme B S hS).obj W) :
    (show LocallyConstant ((SmallEtale.toScheme B S hS).obj W) (Fin m) from
      (representedSheafDisjointCopiesToLocallyConstantSheaf B hS m).hom.app (op W) a) x =
      copyIndex (fun _ : Fin m => (SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS))
        (((SmallEtale.toScheme B S hS).map a).base x) :=
  rfl

/-- The open subscheme of `W` on which a locally constant map `k : |W| → Fin m` takes the value
`i`. -/
abbrev locallyConstantFiberOpen {W : Scheme.{u}} {m : ℕ} (k : LocallyConstant W (Fin m))
    (i : Fin m) :
    W.Opens :=
  ⟨k ⁻¹' {i}, k.isLocallyConstant.isOpen_fiber i⟩

/-- The open subschemes `k⁻¹{i}` of an object `W` of the small étale site, as a covering of `W`.
-/
theorem ofArrows_locallyConstantFiberOpen_mem_topology {W : SmallEtale B S hS} {m : ℕ}
    (k : LocallyConstant ((SmallEtale.toScheme B S hS).obj W) (Fin m)) :
    Sieve.ofArrows (fun i => openObj B hS W (locallyConstantFiberOpen k i).ι inferInstance)
        (fun i => openHom B hS W (locallyConstantFiberOpen k i).ι inferInstance) ∈
      SmallEtale.topology B S hS W :=
  ofArrows_mem_topology B hS _ _ fun x => ⟨k x, ⟨⟨x, rfl⟩, rfl⟩⟩

/-- On the open subscheme `k_a⁻¹{i}`, an `S`-morphism `a : W ⟶ S^{⊔ m}` is `ι_i ∘ π`. -/
theorem openHom_locallyConstantFiberOpen_comp_eq {m : ℕ} {W : SmallEtale B S hS}
    (a : W ⟶ disjointCopies B hS (SmallEtale.final B S hS) m)
    (k : LocallyConstant ((SmallEtale.toScheme B S hS).obj W) (Fin m))
    (hk : ∀ x, copyIndex (fun _ : Fin m => (SmallEtale.toScheme B S hS).obj
      (SmallEtale.final B S hS)) (((SmallEtale.toScheme B S hS).map a).base x) = k x)
    (i : Fin m) :
    openHom B hS W (locallyConstantFiberOpen k i).ι inferInstance ≫ a =
      (SmallEtale.finalIsTerminal B S hS).from _ ≫
        disjointCopiesι B hS (SmallEtale.final B S hS) m i := by
  apply eq_comp_disjointCopiesι_of_range_subset
  rintro _ ⟨z, rfl⟩
  refine (copyIndex_eq_iff _ _ i).1 ?_
  change copyIndex _ (((SmallEtale.toScheme B S hS).map a).base
    ((locallyConstantFiberOpen k i).ι.base z)) = i
  rw [hk]
  exact z.2

instance isLocallyInjective_representedSheafDisjointCopiesToLocallyConstantSheaf (m : ℕ) :
    Sheaf.IsLocallyInjective (representedSheafDisjointCopiesToLocallyConstantSheaf B hS m) where
  equalizerSieve_mem {W} a b hab := by
    let k : LocallyConstant ((SmallEtale.toScheme B S hS).obj W.unop) (Fin m) :=
      (representedSheafDisjointCopiesToLocallyConstantSheaf B hS m).hom.app W a
    refine (SmallEtale.topology B S hS).superset_covering ?_
      (ofArrows_locallyConstantFiberOpen_mem_topology B hS k)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro T f ⟨i⟩
    have ha := openHom_locallyConstantFiberOpen_comp_eq B hS (W := W.unop) a k (fun _ => rfl) i
    have hb := openHom_locallyConstantFiberOpen_comp_eq B hS (W := W.unop) b k (fun x => (congrArg
        (fun l : LocallyConstant ((SmallEtale.toScheme B S hS).obj W.unop) (Fin m) => l x)
        hab).symm) i
    exact ha.trans hb.symm

instance isLocallySurjective_representedSheafDisjointCopiesToLocallyConstantSheaf (m : ℕ) :
    Sheaf.IsLocallySurjective (representedSheafDisjointCopiesToLocallyConstantSheaf B hS m) where
  imageSieve_mem {W} k := by
    refine (SmallEtale.topology B S hS).superset_covering ?_
      (ofArrows_locallyConstantFiberOpen_mem_topology B hS k)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro T f ⟨i⟩
    refine ⟨(SmallEtale.finalIsTerminal B S hS).from _ ≫
      disjointCopiesι B hS (SmallEtale.final B S hS) m i, ?_⟩
    refine LocallyConstant.ext fun z => ?_
    change copyIndex (fun _ : Fin m => (SmallEtale.toScheme B S hS).obj
      (SmallEtale.final B S hS)) ((Sigma.ι (fun _ : Fin m => (SmallEtale.toScheme B S hS).obj
      (SmallEtale.final B S hS)) i).base
        (((SmallEtale.toScheme B S hS).map ((SmallEtale.finalIsTerminal B S hS).from _)).base z))
      = (show LocallyConstant ((SmallEtale.toScheme B S hS).obj W) (Fin m) from k)
        ((locallyConstantFiberOpen k i).ι.base z)
    rw [copyIndex_ι]
    exact z.2.symm

instance isIso_representedSheafDisjointCopiesToLocallyConstantSheaf (m : ℕ) :
    IsIso (representedSheafDisjointCopiesToLocallyConstantSheaf B hS m) :=
  (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨inferInstance, inferInstance⟩

/-- **The sheaf represented by `m` disjoint copies of the base is the constant sheaf on
`Fin m`.** On the small étale site of `S`, the sheaf `S^{⊔ m}~` represented by the disjoint
union of `m` copies of the final object is isomorphic, by `a ↦ k_a`, to the sheaf of locally
constant `Fin m`-valued maps. -/
@[weil "lem_fka1_disjoint_copies_sheaf_constant"]
def representedSheafDisjointCopiesIso (m : ℕ) :
    SmallEtale.representedSheaf (disjointCopies B hS (SmallEtale.final B S hS) m) ≅
      SmallNoetherianSeparatedEtale.locallyConstantSheafSmallEtale B S hS (Fin m) :=
  asIso (representedSheafDisjointCopiesToLocallyConstantSheaf B hS m)

/-- A bijection `Fin m ≃ E` induces an isomorphism of the sheaves of locally constant `Fin m`-
and `E`-valued maps on the small étale site, by composition with the bijection. -/
def locallyConstantSheafSmallEtaleFinIso {m : ℕ} {E : Type u} (e : Fin m ≃ E) :
    SmallNoetherianSeparatedEtale.locallyConstantSheafSmallEtale B S hS (Fin m) ≅
      SmallNoetherianSeparatedEtale.locallyConstantSheafSmallEtale B S hS E :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun W => (LocallyConstant.congrRight (X :=
      (SmallEtale.toScheme B S hS).obj W.unop) e).toIso) fun _ => rfl)

/-- **The sheaf represented by disjoint copies of the base indexed by a finite set `E` is the
constant sheaf `E_S`.** For a finite set `E`, the sheaf represented by the disjoint union of
`|E|` copies of the final object of the small étale site of `S` is isomorphic to the sheaf of
locally constant `E`-valued maps. -/
@[weil "lem_fka1_disjoint_copies_sheaf_constant"]
def representedSheafDisjointCopiesIsoOfFinite (E : Type u) [Finite E] :
    SmallEtale.representedSheaf
        (disjointCopies B hS (SmallEtale.final B S hS) (Nat.card E)) ≅
      SmallNoetherianSeparatedEtale.locallyConstantSheafSmallEtale B S hS E :=
  representedSheafDisjointCopiesIso B hS _ ≪≫
    locallyConstantSheafSmallEtaleFinIso B hS (Finite.equivFin E).symm

/-- **The form on `Et(S)`.** For a locally noetherian scheme `S` and a finite set `E`, the
restriction to the category `Et(S)` of noetherian separated étale `S`-schemes of the sheaf
represented by `|E|` disjoint copies of the base is isomorphic to the constant sheaf `E_S`. -/
@[weil "lem_fka1_disjoint_copies_sheaf_constant"]
def sheafEquivInverseObjRepresentedSheafDisjointCopiesIso [IsLocallyNoetherian S] (E : Type u)
    [Finite E] :
    (SmallNoetherianSeparatedEtale.sheafEquiv B S hS (Type u)).inverse.obj
        (SmallEtale.representedSheaf
          (disjointCopies B hS (SmallEtale.final B S hS) (Nat.card E))) ≅
      SmallNoetherianSeparatedEtale.locallyConstantEtSheaf B S hS E :=
  (SmallNoetherianSeparatedEtale.sheafEquiv B S hS (Type u)).inverse.mapIso
      (representedSheafDisjointCopiesIsoOfFinite B hS E) ≪≫
    SmallNoetherianSeparatedEtale.sheafEquivInverseObjLocallyConstantSheafSmallEtaleIso B S hS E

end Stacks.EtaleCohomology
