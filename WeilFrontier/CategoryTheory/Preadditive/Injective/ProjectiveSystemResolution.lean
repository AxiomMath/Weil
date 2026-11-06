module

public import Weil.Attr
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChangeIdComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Injectivity
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import WeilFrontier.CategoryTheory.Sites.Pullback
public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.AbelianSheaves
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Compatible injective resolutions along a projective system of schemes

Let `(X_α)` be a projective system of schemes, `α₀` an index and `F_{α₀}` an abelian sheaf on the
small étale site of `X_{α₀}`, and put `F_α = p_{αα₀}^* F_{α₀}`. With the units
`u_{βα} : F_α ⟶ (p_{βα})_* F_β` of the adjunctions `p^* ⊣ p_*`, there are injective resolutions
`F_α ⟶ I_α^•` and chain maps `ψ_{βα} : I_α^• ⟶ (p_{βα})_* I_β^•` over `u_{βα}` with
`ψ_{αα} = id` and `(p_{βα})_*(ψ_{γβ}) ∘ ψ_{βα} = ψ_{γα}`.

The proof is carried out for an arbitrary *pseudo-diagram* of categories `D`: categories `C j`
indexed by a category `J`, functors `D.map f : C i ⥤ C j` along the arrows, and coherent
comparison isomorphisms for identities and composites. A *system* is a family `G j` with maps
`ψ f : G j ⟶ (D.map f) (G i)` satisfying the two identities above. Cokernels of morphisms of
systems are systems, and every system `G` embeds into the system
`E(G)_j = ∏_{b : k ⟶ j} (D.map b) I(G k)`, `I(G k)` an injective object containing `G k`, whose
structure maps are the projections. Iterating `G ↦ Coker(G ⟶ E(G))` gives the resolution.

## Main definitions

* `CategoryTheory.PseudoDiagram`: a pseudofunctor from a category to categories, by components.
* `CategoryTheory.PseudoDiagram.System`, `CategoryTheory.PseudoDiagram.System.Hom`: systems for a
  pseudo-diagram and their morphisms.
* `CategoryTheory.PseudoDiagram.System.envelope`: the injective envelope `E(G)` of a system.
* `AlgebraicGeometry.smallEtaleDirectImagePseudoDiagram`: the direct images of sheaves on the small
  étale sites along a diagram of schemes.
* `AlgebraicGeometry.smallEtaleInverseImageSystem`: the system `(p_j^* F₀, u)` along a cocone.

## Main results

* `CategoryTheory.PseudoDiagram.System.exists_injective_resolution`: compatible injective
  resolutions of a system.
* `AlgebraicGeometry.exists_injective_resolution_smallEtaleInverseImage_cocone`: the statement for
  the inverse images of an abelian sheaf along a cocone of schemes of a big étale site.
* `AlgebraicGeometry.exists_injective_resolution_smallEtaleInverseImage_over`: the same over the
  indices above a fixed index `α₀`, the form of the source.

## Implementation notes

The index is an arbitrary category: for a directed set the arrows `β ⟶ α` are the relations
`β ≥ α`, and the indices `α ≥ α₀` are the objects of `Over α₀`. The general statement takes any
cocone `p_j : X_j ⟶ S` of a small diagram of schemes, of which `X_α ⟶ X_{α₀}` for `α ≥ α₀` is the
case `J = Over α₀`; the existence of the limit of the system and the noetherian, separatedness
and affineness hypotheses are not needed. The identifications `(p_{αα})_* = id` and
`(p_{γα})_* = (p_{βα})_* (p_{γβ})_*` are the canonical ones,
`AlgebraicGeometry.smallEtaleDirectImageIdIsoOfEq` and
`AlgebraicGeometry.smallEtaleDirectImageComp`.
The products in `E(G)` are indexed by all arrows into an index; since the index category need
not be thin, the factor indexed by `(k, b)` is `D.map b` applied to the envelope of `G k`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory

/-- A product of injective objects is injective, for an index type of any size. -/
lemma injective_piObj {C : Type u₂} [Category.{v₂} C] {T : Type*} (X : T → C) [HasProduct X]
    [∀ t, Injective (X t)] : Injective (∏ᶜ X) :=
  ⟨fun g f _ => ⟨Pi.lift fun t => Injective.factorThru (g ≫ Pi.π X t) f, by
    refine Pi.hom_ext _ _ fun t => ?_
    rw [Category.assoc, Pi.lift_π, Injective.comp_factorThru]⟩⟩

/-- Exactness of `ShortComplex.mk f g w` only depends on `f` and `g`. -/
lemma exact_mk_of_eq {C : Type u₂} [Category.{v₂} C] [Preadditive C] {X₁ X₂ X₃ : C}
    {f f' : X₁ ⟶ X₂} {g g' : X₂ ⟶ X₃} (hf : f = f') (hg : g = g') {w : f ≫ g = 0}
    (w' : f' ≫ g' = 0) (h : (ShortComplex.mk f' g' w').Exact) :
    (ShortComplex.mk f g w).Exact := by
  subst hf hg; exact h

/-- In an abelian category, `I₀ --p--> K --η--> I₁ --π--> Coker η --η'--> I₂` with `p` epi and `η'`
mono is exact at `I₁`. -/
lemma exact_comp_cokernel_π_comp {C : Type u₂} [Category.{v₂} C] [Abelian C] {I₀ K I₁ I₂ : C}
    (p : I₀ ⟶ K) [Epi p] (η : K ⟶ I₁) (η' : cokernel η ⟶ I₂) (hη' : Mono η') (f : I₀ ⟶ I₁)
    (hf : p ≫ η = f) (w : f ≫ cokernel.π η ≫ η' = 0) :
    (ShortComplex.mk f (cokernel.π η ≫ η') w).Exact := by
  subst hf
  have h₁ : (ShortComplex.mk (p ≫ η) (cokernel.π η) (by simp)).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (p ≫ η) (cokernel.π η) (by simp))
      (S₂ := ShortComplex.mk η (cokernel.π η) (by simp))
      { τ₁ := p, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }).2 (ShortComplex.exact_cokernel η)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk (p ≫ η) (cokernel.π η) (by simp))
    (S₂ := ShortComplex.mk (p ≫ η) (cokernel.π η ≫ η') w)
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := η' }).1 h₁

/-- A pseudofunctor from a category `J` to categories, given by its components: categories
`C j`, functors `map f : C i ⥤ C j` along the arrows `f : i ⟶ j`, and comparison isomorphisms
`map (𝟙 j) ≅ 𝟭` and `map f ⋙ map g ≅ map fg` for `f ≫ g = fg`, subject to the associativity and
unit laws. -/
structure PseudoDiagram (J : Type u₁) [Category.{v₁} J] (C : J → Type u₂)
    [∀ j, Category.{v₂} (C j)] where
  /-- The functor along an arrow. -/
  map {i j : J} (f : i ⟶ j) : C i ⥤ C j
  /-- The comparison along an identity. -/
  mapId (j : J) : map (𝟙 j) ≅ 𝟭 (C j)
  /-- The comparison along a composite. -/
  mapComp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k) (h : f ≫ g = fg) :
    map f ⋙ map g ≅ map fg
  mapComp_assoc {a b c d : J} (h : a ⟶ b) (f : b ⟶ c) (g : c ⟶ d) (fg : b ⟶ d)
    (hfg : f ≫ g = fg) (hf : a ⟶ c) (hhf : h ≫ f = hf) (hfg' : a ⟶ d)
    (h₁ : h ≫ fg = hfg') (h₂ : hf ≫ g = hfg') (X : C a) :
    (mapComp f g fg hfg).hom.app ((map h).obj X) ≫ (mapComp h fg hfg' h₁).hom.app X =
      (map g).map ((mapComp h f hf hhf).hom.app X) ≫ (mapComp hf g hfg' h₂).hom.app X
  mapComp_id_left {i j : J} (g : i ⟶ j) (X : C i) :
    (mapComp (𝟙 i) g g (Category.id_comp g)).hom.app X = (map g).map ((mapId i).hom.app X)
  mapComp_id_right {i j : J} (f : i ⟶ j) (X : C i) :
    (mapComp f (𝟙 j) f (Category.comp_id f)).hom.app X = (mapId j).hom.app ((map f).obj X)

namespace PseudoDiagram

variable {J : Type u₁} [Category.{v₁} J] {C : J → Type u₂} [∀ j, Category.{v₂} (C j)]
  (D : PseudoDiagram J C)

/-- A system for a pseudo-diagram `D`: objects `G j` of `C j` with maps
`ψ f : G j ⟶ (D.map f).obj (G i)` along the arrows `f : i ⟶ j`, compatible with identities and
composites. -/
structure System where
  /-- The object at an index. -/
  obj (j : J) : C j
  /-- The structure map along an arrow. -/
  ψ {i j : J} (f : i ⟶ j) : obj j ⟶ (D.map f).obj (obj i)
  ψ_id (j : J) : ψ (𝟙 j) ≫ (D.mapId j).hom.app (obj j) = 𝟙 (obj j)
  ψ_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    ψ g ≫ (D.map g).map (ψ f) ≫ (D.mapComp f g (f ≫ g) rfl).hom.app (obj i) = ψ (f ≫ g)

variable {D}

/-- A morphism of systems: maps at every index commuting with the structure maps. -/
@[ext]
structure System.Hom (G H : D.System) where
  /-- The map at an index. -/
  app (j : J) : G.obj j ⟶ H.obj j
  comm {i j : J} (f : i ⟶ j) : app j ≫ H.ψ f = G.ψ f ≫ (D.map f).map (app i)

/-- The composite of morphisms of systems. -/
def System.Hom.comp {G H K : D.System} (a : G.Hom H) (b : H.Hom K) : G.Hom K where
  app j := a.app j ≫ b.app j
  comm f := by
    rw [Category.assoc, b.comm, reassoc_of% a.comm, Functor.map_comp]

@[simp]
lemma System.Hom.comp_app {G H K : D.System} (a : G.Hom H) (b : H.Hom K) (j : J) :
    (a.comp b).app j = a.app j ≫ b.app j := rfl

/-- The associativity law of the comparison isomorphisms, in the form used for products. -/
lemma mapComp_inv_app_assoc_eq {a b c d : J} (h : a ⟶ b) (f : b ⟶ c) (g : c ⟶ d) (X : C a) :
    (D.mapComp (h ≫ f) g (h ≫ f ≫ g) (Category.assoc _ _ _)).inv.app X ≫
        (D.map g).map ((D.mapComp h f _ rfl).inv.app X) ≫
          (D.mapComp f g _ rfl).hom.app ((D.map h).obj X) =
      (D.mapComp h (f ≫ g) _ rfl).inv.app X := by
  rw [← cancel_mono ((D.mapComp h (f ≫ g) _ rfl).hom.app X), Category.assoc, Category.assoc,
    Iso.inv_hom_id_app, D.mapComp_assoc h f g (f ≫ g) rfl (h ≫ f) rfl _ rfl
      (Category.assoc _ _ _), ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app]

/-! ### Cokernels -/

section Cokernel

variable [∀ j, Abelian (C j)] [∀ {i j : J} (f : i ⟶ j), (D.map f).PreservesZeroMorphisms]

/-- The cokernel of a morphism of systems, computed indexwise. -/
def System.cokernel {G H : D.System} (w : G.Hom H) : D.System where
  obj j := Limits.cokernel (w.app j)
  ψ {i j} f := cokernel.desc (w.app j) (H.ψ f ≫ (D.map f).map (cokernel.π (w.app i))) (by
    rw [reassoc_of% w.comm, ← Functor.map_comp, cokernel.condition, Functor.map_zero,
      comp_zero])
  ψ_id j := by
    refine (cancel_epi (cokernel.π (w.app j))).1 ?_
    have hn := (D.mapId j).hom.naturality (cokernel.π (w.app j))
    simp only [Functor.id_map] at hn
    rw [cokernel.π_desc_assoc, Category.assoc, hn, reassoc_of% H.ψ_id, Category.comp_id]
  ψ_comp {i j k} f g := by
    refine (cancel_epi (cokernel.π (w.app k))).1 ?_
    have hn := (D.mapComp f g (f ≫ g) rfl).hom.naturality (cokernel.π (w.app i))
    simp only [Functor.comp_map] at hn
    rw [cokernel.π_desc_assoc, Category.assoc, ← Functor.map_comp_assoc, cokernel.π_desc,
      Functor.map_comp, Category.assoc, hn, cokernel.π_desc, ← H.ψ_comp]
    simp only [Category.assoc]

/-- The projection onto the cokernel, as a morphism of systems. -/
def System.cokernelπ {G H : D.System} (w : G.Hom H) : H.Hom (System.cokernel w) where
  app j := cokernel.π (w.app j)
  comm _ := cokernel.π_desc _ _ _

end Cokernel

/-! ### Embedding into injectives -/

section Envelope

variable [∀ j, Abelian (C j)] [∀ j, EnoughInjectives (C j)]
  [∀ i j : J, HasProductsOfShape (Σ k : J, k ⟶ i) (C j)]
  [∀ {i j : J} (f : i ⟶ j), PreservesLimitsOfShape (Discrete (Σ k : J, k ⟶ i)) (D.map f)]

/-- The factor `(D.map b).obj I(G k)` of the envelope at `j`, for an arrow `b : k ⟶ j`. -/
abbrev System.envelopeFactor (G : D.System) (j : J) (x : Σ k : J, k ⟶ j) : C j :=
  (D.map x.2).obj (Injective.under (G.obj x.1))

/-- The envelope `E(G)_j = ∏_{b : k ⟶ j} (D.map b).obj I(G k)`. -/
abbrev System.envelopeObj (G : D.System) (j : J) : C j :=
  ∏ᶜ G.envelopeFactor j

/-- The structure maps of the envelope, given on the factors by the comparison isomorphisms. -/
def System.envelopeψ (G : D.System) {i j : J} (f : i ⟶ j) :
    G.envelopeObj j ⟶ (D.map f).obj (G.envelopeObj i) :=
  Pi.lift (fun x : Σ k : J, k ⟶ i => Pi.π (G.envelopeFactor j) ⟨x.1, x.2 ≫ f⟩ ≫
    (D.mapComp x.2 f _ rfl).inv.app _) ≫ (PreservesProduct.iso (D.map f) _).inv

omit [∀ j, Abelian (C j)] in
lemma System.envelopeψ_map_π (G : D.System) {i j : J} (f : i ⟶ j) (x : Σ k : J, k ⟶ i) :
    G.envelopeψ f ≫ (D.map f).map (Pi.π (G.envelopeFactor i) x) =
      Pi.π (G.envelopeFactor j) ⟨x.1, x.2 ≫ f⟩ ≫ (D.mapComp x.2 f _ rfl).inv.app _ := by
  rw [envelopeψ, Category.assoc, ← piComparison_comp_π, ← PreservesProduct.iso_hom,
    Iso.inv_hom_id_assoc]
  exact Pi.lift_π _ _

omit [∀ j, Abelian (C j)] [∀ j, EnoughInjectives (C j)]
  [∀ i j : J, HasProductsOfShape (Σ k : J, k ⟶ i) (C j)]
  [∀ {i j : J} (f : i ⟶ j), PreservesLimitsOfShape (Discrete (Σ k : J, k ⟶ i)) (D.map f)] in
/-- Two maps into `(D.map f).obj (∏ X)` agree when they agree after every `(D.map f).map π`. -/
lemma map_pi_hom_ext {i j : J} (f : i ⟶ j) {T : Type*} [HasProductsOfShape T (C i)]
    [HasProductsOfShape T (C j)] [PreservesLimitsOfShape (Discrete T) (D.map f)]
    {X : T → C i} {Y : C j} {a b : Y ⟶ (D.map f).obj (∏ᶜ X)}
    (h : ∀ t, a ≫ (D.map f).map (Pi.π X t) = b ≫ (D.map f).map (Pi.π X t)) : a = b := by
  refine (cancel_mono (PreservesProduct.iso (D.map f) X).hom).1 (Pi.hom_ext _ _ fun t => ?_)
  simp only [PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π, h]

omit [∀ j, Abelian (C j)]
  [∀ {i j : J} (f : i ⟶ j), PreservesLimitsOfShape (Discrete (Σ k : J, k ⟶ i)) (D.map f)] in
@[reassoc]
lemma System.π_mapComp_inv (G : D.System) {i j k : J} (c : k ⟶ i) (f : i ⟶ j) (e : k ⟶ j)
    (h : c ≫ f = e) :
    Pi.π (G.envelopeFactor j) ⟨k, c ≫ f⟩ ≫
        (D.mapComp c f _ rfl).inv.app (Injective.under (G.obj k)) =
      Pi.π (G.envelopeFactor j) ⟨k, e⟩ ≫
        (D.mapComp c f e h).inv.app (Injective.under (G.obj k)) := by
  subst h; rfl

/-- The envelope `E(G)` of a system: a system whose objects are products of the images of
injective objects. -/
def System.envelope (G : D.System) : D.System where
  obj := G.envelopeObj
  ψ := G.envelopeψ
  ψ_id j := by
    refine Pi.hom_ext _ _ fun ⟨k, c⟩ => ?_
    have hn := (D.mapId j).hom.naturality (Pi.π (G.envelopeFactor j) ⟨k, c⟩)
    simp only [Functor.id_map] at hn
    rw [Category.assoc, ← hn, reassoc_of% G.envelopeψ_map_π, Category.id_comp,
      G.π_mapComp_inv_assoc c (𝟙 j) c (Category.comp_id _),
      ← D.mapComp_id_right, Iso.inv_hom_id_app, Category.comp_id]
  ψ_comp {i j k} f g := by
    refine D.map_pi_hom_ext (f ≫ g) fun ⟨l, c⟩ => ?_
    have hn := (D.mapComp f g (f ≫ g) rfl).hom.naturality (Pi.π (G.envelopeFactor i) ⟨l, c⟩)
    simp only [Functor.comp_map] at hn
    rw [Category.assoc, Category.assoc, ← hn, ← Functor.map_comp_assoc, G.envelopeψ_map_π,
      Functor.map_comp_assoc, reassoc_of% G.envelopeψ_map_π, G.envelopeψ_map_π]
    dsimp only
    rw [G.π_mapComp_inv_assoc (c ≫ f) g (c ≫ f ≫ g) (Category.assoc _ _ _)]
    congr 1
    exact D.mapComp_inv_app_assoc_eq c f g _

/-- The component at `j` of the embedding `η : G ⟶ E(G)`; its factor at `b : k ⟶ j` is
`(D.map b).map (ι (G k)) ∘ ψ b`. -/
def System.toEnvelopeApp (G : D.System) (j : J) : G.obj j ⟶ G.envelopeObj j :=
  Pi.lift fun x : Σ k : J, k ⟶ j => G.ψ x.2 ≫ (D.map x.2).map (Injective.ι (G.obj x.1))

omit [∀ j, Abelian (C j)]
  [∀ {i j : J} (f : i ⟶ j), PreservesLimitsOfShape (Discrete (Σ k : J, k ⟶ i)) (D.map f)] in
@[reassoc]
lemma System.toEnvelopeApp_π (G : D.System) (j : J) (x : Σ k : J, k ⟶ j) :
    G.toEnvelopeApp j ≫ Pi.π (G.envelopeFactor j) x =
      G.ψ x.2 ≫ (D.map x.2).map (Injective.ι (G.obj x.1)) :=
  Pi.lift_π _ _

omit [∀ j, Abelian (C j)] in
lemma System.toEnvelopeApp_comm (G : D.System) {i j : J} (f : i ⟶ j) :
    G.toEnvelopeApp j ≫ G.envelopeψ f = G.ψ f ≫ (D.map f).map (G.toEnvelopeApp i) := by
  refine D.map_pi_hom_ext f fun ⟨l, c⟩ => ?_
  have hn := (D.mapComp c f _ rfl).inv.naturality (Injective.ι (G.obj l))
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, G.envelopeψ_map_π,
    G.toEnvelopeApp_π_assoc, G.toEnvelopeApp_π]
  dsimp only
  rw [hn, ← G.ψ_comp, Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc,
    Functor.map_comp]

/-- The embedding `η : G ⟶ E(G)` of a system into its envelope. -/
def System.toEnvelope (G : D.System) : G.Hom G.envelope where
  app := G.toEnvelopeApp
  comm f := G.toEnvelopeApp_comm f

omit [∀ j, Abelian (C j)]
  [∀ {i j : J} (f : i ⟶ j), PreservesLimitsOfShape (Discrete (Σ k : J, k ⟶ i)) (D.map f)] in
lemma System.mono_toEnvelopeApp (G : D.System) (j : J) : Mono (G.toEnvelopeApp j) := by
  have hn := (D.mapId j).hom.naturality (Injective.ι (G.obj j))
  simp only [Functor.id_map] at hn
  have h : G.toEnvelopeApp j ≫ Pi.π (G.envelopeFactor j) ⟨j, 𝟙 j⟩ ≫
      (D.mapId j).hom.app _ = Injective.ι (G.obj j) := by
    rw [G.toEnvelopeApp_π_assoc]
    dsimp only
    rw [hn, reassoc_of% G.ψ_id]
  have : Mono (G.toEnvelopeApp j ≫ Pi.π (G.envelopeFactor j) ⟨j, 𝟙 j⟩ ≫
      (D.mapId j).hom.app _) := by
    rw [h]; infer_instance
  exact mono_of_mono _ (Pi.π (G.envelopeFactor j) ⟨j, 𝟙 j⟩ ≫ (D.mapId j).hom.app _)

instance System.mono_toEnvelope_app (G : D.System) (j : J) : Mono (G.toEnvelope.app j) :=
  G.mono_toEnvelopeApp j

omit [∀ j, Abelian (C j)] in
lemma System.injective_envelope_obj [∀ {i j : J} (f : i ⟶ j), (D.map f).PreservesInjectiveObjects]
    (G : D.System) (j : J) : Injective (G.envelope.obj j) :=
  injective_piObj _

end Envelope

/-! ### The resolution -/

section Resolution

variable [∀ j, Abelian (C j)] [∀ j, EnoughInjectives (C j)]
  [∀ i j : J, HasProductsOfShape (Σ k : J, k ⟶ i) (C j)]
  [∀ {i j : J} (f : i ⟶ j), PreservesLimitsOfShape (Discrete (Σ k : J, k ⟶ i)) (D.map f)]
  [∀ {i j : J} (f : i ⟶ j), (D.map f).PreservesZeroMorphisms]

/-- The successive cokernels `K⁰ = G`, `Kⁿ⁺¹ = Coker(Kⁿ ⟶ E(Kⁿ))`. -/
def System.resolutionCokernel (G : D.System) : ℕ → D.System
  | 0 => G
  | n + 1 => System.cokernel (G.resolutionCokernel n).toEnvelope

/-- The terms `Iⁿ = E(Kⁿ)` of the resolution. -/
abbrev System.resolutionObj (G : D.System) (n : ℕ) : D.System :=
  (G.resolutionCokernel n).envelope

/-- The differential `Iⁿ ⟶ Kⁿ⁺¹ ⟶ Iⁿ⁺¹`. -/
def System.resolutionDiff (G : D.System) (n : ℕ) :
    (G.resolutionObj n).Hom (G.resolutionObj (n + 1)) :=
  (System.cokernelπ (G.resolutionCokernel n).toEnvelope).comp
    (G.resolutionCokernel (n + 1)).toEnvelope

lemma System.resolutionDiff_app (G : D.System) (n : ℕ) (j : J) :
    (G.resolutionDiff n).app j = cokernel.π ((G.resolutionCokernel n).toEnvelope.app j) ≫
      (G.resolutionCokernel (n + 1)).toEnvelope.app j := rfl

lemma System.toEnvelope_comp_resolutionDiff (G : D.System) (j : J) :
    G.toEnvelope.app j ≫ (G.resolutionDiff 0).app j = 0 := by
  exact (cokernel.condition_assoc _ _).trans zero_comp

lemma System.resolutionDiff_comp (G : D.System) (n : ℕ) (j : J) :
    (G.resolutionDiff n).app j ≫ (G.resolutionDiff (n + 1)).app j = 0 :=
  (Category.assoc _ _ _).trans <| (_ ≫= (cokernel.condition_assoc _ _).trans zero_comp).trans
    comp_zero

lemma System.injective_resolutionObj [∀ {i j : J} (f : i ⟶ j), (D.map f).PreservesInjectiveObjects]
    (G : D.System) (n : ℕ) (j : J) : Injective ((G.resolutionObj n).obj j) :=
  (G.resolutionCokernel n).injective_envelope_obj j

lemma System.exact_toEnvelope (G : D.System) (j : J) :
    (ShortComplex.mk (G.toEnvelope.app j) ((G.resolutionDiff 0).app j)
      (G.toEnvelope_comp_resolutionDiff j)).Exact :=
  exact_comp_cokernel_π_comp (𝟙 _) ((G.resolutionCokernel 0).toEnvelope.app j)
    ((G.resolutionCokernel 1).toEnvelope.app j) ((G.resolutionCokernel 1).mono_toEnvelopeApp j) _
    (Category.id_comp _) _

lemma System.exact_resolutionDiff (G : D.System) (n : ℕ) (j : J) :
    (ShortComplex.mk ((G.resolutionDiff n).app j) ((G.resolutionDiff (n + 1)).app j)
      (G.resolutionDiff_comp n j)).Exact :=
  have : Epi (cokernel.π ((G.resolutionCokernel n).toEnvelope.app j)) := inferInstance
  exact_comp_cokernel_π_comp (cokernel.π ((G.resolutionCokernel n).toEnvelope.app j))
    ((G.resolutionCokernel (n + 1)).toEnvelope.app j)
    ((G.resolutionCokernel (n + 2)).toEnvelope.app j)
    ((G.resolutionCokernel (n + 2)).mono_toEnvelopeApp j) _ rfl _

/-- **Compatible injective resolutions of a system.** Every system `G` admits, at every index
`j`, an injective resolution `G j ⟶ I j` such that the structure maps of `G` extend to chain maps
`ψ f : I j ⟶ (D.map f) (I i)`, compatible with identities and composites. -/
theorem System.exists_injective_resolution
    [∀ {i j : J} (f : i ⟶ j), (D.map f).PreservesInjectiveObjects] (G : D.System) :
    ∃ (I : ∀ j, CochainComplex (C j) ℕ) (e : ∀ j, G.obj j ⟶ (I j).X 0)
      (he : ∀ j, e j ≫ (I j).d 0 1 = 0)
      (ψ : ∀ {i j : J} (_ : i ⟶ j) (n : ℕ), (I j).X n ⟶ (D.map ‹i ⟶ j›).obj ((I i).X n)),
      (∀ j, (∀ n, Injective ((I j).X n)) ∧ Mono (e j) ∧
        (ShortComplex.mk (e j) ((I j).d 0 1) (he j)).Exact ∧
        ∀ n, (ShortComplex.mk ((I j).d n (n + 1)) ((I j).d (n + 1) (n + 2))
          ((I j).d_comp_d _ _ _)).Exact) ∧
      (∀ {i j : J} (f : i ⟶ j) (n : ℕ),
        (I j).d n (n + 1) ≫ ψ f (n + 1) = ψ f n ≫ (D.map f).map ((I i).d n (n + 1))) ∧
      (∀ {i j : J} (f : i ⟶ j), e j ≫ ψ f 0 = G.ψ f ≫ (D.map f).map (e i)) ∧
      (∀ (j : J) (n : ℕ), ψ (𝟙 j) n ≫ (D.mapId j).hom.app ((I j).X n) = 𝟙 _) ∧
      (∀ {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (n : ℕ),
        ψ g n ≫ (D.map g).map (ψ f n) ≫ (D.mapComp f g (f ≫ g) rfl).hom.app ((I i).X n) =
          ψ (f ≫ g) n) := by
  let I : ∀ j, CochainComplex (C j) ℕ := fun j => CochainComplex.of
    (fun n => (G.resolutionObj n).obj j) (fun n => (G.resolutionDiff n).app j)
    (fun n => G.resolutionDiff_comp n j)
  have hd (j : J) (n : ℕ) : (I j).d n (n + 1) = (G.resolutionDiff n).app j :=
    CochainComplex.of_d (fun n => (G.resolutionObj n).obj j) (fun n => (G.resolutionDiff n).app j) n
  refine ⟨I, fun j => G.toEnvelope.app j, fun j => (hd j 0).symm ▸
      G.toEnvelope_comp_resolutionDiff j, fun f n => (G.resolutionObj n).ψ f,
    fun j => ⟨fun n => G.injective_resolutionObj n j, G.mono_toEnvelopeApp j, ?_, fun n => ?_⟩,
    fun f n => ?_, fun f => G.toEnvelope.comm f, fun j n => (G.resolutionObj n).ψ_id j,
    fun f g n => (G.resolutionObj n).ψ_comp f g⟩
  · exact exact_mk_of_eq rfl (hd j 0) _ (G.exact_toEnvelope j)
  · exact exact_mk_of_eq (hd j n) (hd j (n + 1)) _ (G.exact_resolutionDiff n j)
  · rw [hd, hd]
    exact (G.resolutionDiff n).comm f

end Resolution


end PseudoDiagram

end CategoryTheory

namespace AlgebraicGeometry

open CategoryTheory.PseudoDiagram

variable (B : BigEtaleSite.{u}) (A : Type w) [Category.{v} A]

/-- **The right unit law for small étale base change.** Base changing along `𝟙 Y` and then along
`f`, compared with base change along `f ≫ 𝟙 Y = f`, is base change along `f` of the comparison
of base change along `𝟙 Y` with the identity functor. -/
lemma smallEtaleBaseChange_factoredCompIso_id_right_hom_app {X Y : B.Scheme} (f : X ⟶ Y)
    (V : SmallEtale B Y.obj Y.property) :
    (smallEtaleBaseChange_factoredCompIso B X Y Y f (𝟙 Y) f (Category.comp_id f)).hom.app V =
      (smallEtaleBaseChange B f).map ((smallEtaleBaseChange_idIso B Y).hom.app V) := by
  apply smallEtaleBaseChange_hom_ext_fst
  rw [smallEtaleBaseChange_factoredCompIso_hom_app_left_pullbackFst]
  refine Eq.trans ?_ (smallEtaleBaseChange_map_hom_left_fst B f _).symm
  congr 1
  exact (smallEtaleBaseChange_idIso_hom_app_left B _).symm

/-- The direct image along an endomorphism equal to the identity is the identity functor. -/
def smallEtaleDirectImageIdIsoOfEq {X : B.Scheme} (f : X ⟶ X) (hf : f = 𝟙 X) :
    smallEtaleDirectImage B A f ≅ 𝟭 _ :=
  eqToIso (by rw [hf]) ≪≫
    Functor.sheafPushforwardContinuousId' (smallEtaleBaseChange_idIso B X) A _

lemma smallEtaleDirectImageIdIsoOfEq_hom_app_hom_app {X : B.Scheme}
    (F : Sheaf (SmallEtale.topology B X.obj X.property) A)
    (V : (SmallEtale B X.obj X.property)ᵒᵖ) :
    ((smallEtaleDirectImageIdIsoOfEq B A (𝟙 X) rfl).hom.app F).hom.app V =
      F.obj.map ((smallEtaleBaseChange_idIso B X).inv.app V.unop).op := by
  simp [smallEtaleDirectImageIdIsoOfEq]
  rfl

/-- **The left unit law for the direct images.** -/
lemma smallEtaleDirectImageComp_id_left_hom_app {X Y : B.Scheme} (f : X ⟶ X) (hf : f = 𝟙 X)
    (g : X ⟶ Y) (h : f ≫ g = g) (F : Sheaf (SmallEtale.topology B X.obj X.property) A) :
    (smallEtaleDirectImageComp B A f g g h).hom.app F =
      (smallEtaleDirectImage B A g).map ((smallEtaleDirectImageIdIsoOfEq B A f hf).hom.app F) := by
  subst hf
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  have key := smallEtaleBaseChange_factoredCompIso_id_left_inv_app B g V.unop
  simp only [smallEtaleDirectImageComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    Functor.sheafPushforwardContinuous_map_hom_app, smallEtaleDirectImageIdIsoOfEq_hom_app_hom_app]
  rw [key]

/-- **The right unit law for the direct images.** -/
lemma smallEtaleDirectImageComp_id_right_hom_app {X Y : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Y)
    (hg : g = 𝟙 Y) (h : f ≫ g = f) (F : Sheaf (SmallEtale.topology B X.obj X.property) A) :
    (smallEtaleDirectImageComp B A f g f h).hom.app F =
      (smallEtaleDirectImageIdIsoOfEq B A g hg).hom.app ((smallEtaleDirectImage B A f).obj F) := by
  subst hg
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => ?_))
  have key := congrArg (fun e => NatTrans.app (Iso.inv e) V.unop)
    (Iso.ext (NatTrans.ext (funext
      (smallEtaleBaseChange_factoredCompIso_id_right_hom_app B f))) :
      smallEtaleBaseChange_factoredCompIso B X Y Y f (𝟙 Y) f (Category.comp_id f) =
        Functor.isoWhiskerRight (smallEtaleBaseChange_idIso B Y) (smallEtaleBaseChange B f) ≪≫
          (smallEtaleBaseChange B f).leftUnitor)
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Category.id_comp] at key
  simp only [smallEtaleDirectImageComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    smallEtaleDirectImageIdIsoOfEq_hom_app_hom_app]
  rw [key]
  rfl

/-- The direct images along a diagram of schemes of a big étale site, as a pseudo-diagram of the
categories of sheaves on the small étale sites. -/
def smallEtaleDirectImagePseudoDiagram {J : Type u₁} [Category.{v₁} J] (D : J ⥤ B.Scheme) :
    PseudoDiagram J fun j => Sheaf (SmallEtale.topology B (D.obj j).obj (D.obj j).property) A where
  map f := smallEtaleDirectImage B A (D.map f)
  mapId j := smallEtaleDirectImageIdIsoOfEq B A (D.map (𝟙 j)) (D.map_id j)
  mapComp f g fg h := smallEtaleDirectImageComp B A (D.map f) (D.map g) (D.map fg)
    (by rw [← D.map_comp, h])
  mapComp_assoc h f g fg hfg hf hhf hfg' h₁ h₂ X := by
    have := congrArg (fun e => NatTrans.app (Iso.hom e) X)
      (smallEtaleDirectImageComp_assoc B A (D.map h) (D.map f) (D.map g) (D.map fg)
        (by rw [← D.map_comp, hfg]) (D.map hf) (by rw [← D.map_comp, hhf]) (D.map hfg')
        (by rw [← D.map_comp, h₁]) (by rw [← D.map_comp, h₂]))
    simpa using this
  mapComp_id_left g X := smallEtaleDirectImageComp_id_left_hom_app B A _ (D.map_id _) _ _ X
  mapComp_id_right f X := smallEtaleDirectImageComp_id_right_hom_app B A _ _ (D.map_id _) _ X

section InverseImage

variable [HasColimitsOfSize.{u, u + 1} A]

/-- The unit along an endomorphism equal to the identity, followed by the identification of the
direct image with the identity, is the identity. -/
lemma smallEtaleInverseImageAdjunction_homEquiv_comp_directImageIdIsoOfEq {X S : B.Scheme}
    (g : X ⟶ S) (e : X ⟶ X) (he : e = 𝟙 X) (hw : e ≫ g = g)
    [HasWeakSheafify (SmallEtale.topology B X.obj X.property) A]
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    (smallEtaleInverseImageAdjunction B e A).homEquiv _ _
        ((smallEtaleInverseImageComp B A e g g hw).hom.app G) ≫
      (smallEtaleDirectImageIdIsoOfEq B A e he).hom.app _ = 𝟙 _ := by
  subst he
  have h : smallEtaleDirectImageComp B A (𝟙 X) g g hw =
      Functor.isoWhiskerRight (smallEtaleDirectImageIdIsoOfEq B A (𝟙 X) rfl)
        (smallEtaleDirectImage B A g) ≪≫ Functor.leftUnitor _ := by
    refine Iso.ext (NatTrans.ext (funext fun F => ?_))
    simp [smallEtaleDirectImageComp_id_left_hom_app B A (𝟙 X) rfl g hw F]
  have hθ := Adjunction.leftAdjointCompIso_comp_id (smallEtaleInverseImageAdjunction B g A)
    (smallEtaleInverseImageAdjunction B (𝟙 X) A) _ _ h
  change (smallEtaleInverseImageAdjunction B (𝟙 X) A).homEquiv _ _
      ((Adjunction.leftAdjointCompIso _ _ _ _).hom.app G) ≫ _ = _
  rw [hθ]
  simp [Adjunction.leftAdjointIdIso_hom_app, Adjunction.homEquiv_unit]

variable {J : Type u₁} [Category.{v₁} J] (D : J ⥤ B.Scheme) (c : Cocone D)
  [∀ j, HasWeakSheafify (SmallEtale.topology B (D.obj j).obj (D.obj j).property) A]
  (F₀ : Sheaf (SmallEtale.topology B c.pt.obj c.pt.property) A)

/-- The unit `u_t : p_j^* F₀ ⟶ (D t)_* p_i^* F₀` along an arrow `t : i ⟶ j`, for a cocone
`p_j : D j ⟶ S` and a sheaf `F₀` on the small étale site of `S`: the unit of the adjunction
`(D t)^* ⊣ (D t)_*` followed by the identification `(D t)^* p_j^* F₀ ≅ p_i^* F₀`. -/
def smallEtaleInverseImageSystemUnit {i j : J} (t : i ⟶ j) :
    (smallEtaleInverseImage B (c.ι.app j) A).obj F₀ ⟶
      (smallEtaleDirectImage B A (D.map t)).obj ((smallEtaleInverseImage B (c.ι.app i) A).obj F₀) :=
  (smallEtaleInverseImageUnit B (D.map t) A).app _ ≫ (smallEtaleDirectImage B A (D.map t)).map
    ((smallEtaleInverseImageComp B A (D.map t) (c.ι.app j) (c.ι.app i) (c.w t)).hom.app F₀)

lemma smallEtaleInverseImageSystemUnit_eq {i j : J} (t : i ⟶ j) :
    smallEtaleInverseImageSystemUnit B A D c F₀ t =
      (smallEtaleInverseImageAdjunction B (D.map t) A).homEquiv _ _
        ((smallEtaleInverseImageComp B A (D.map t) (c.ι.app j) (c.ι.app i) (c.w t)).hom.app F₀) :=
  ((smallEtaleInverseImageAdjunction B (D.map t) A).homEquiv_unit _ _ _).symm

/-- **Transitivity of the units.** -/
lemma smallEtaleInverseImageSystemUnit_comp {i j k : J} (s : k ⟶ i) (t : i ⟶ j) :
    smallEtaleInverseImageSystemUnit B A D c F₀ t ≫
        (smallEtaleDirectImage B A (D.map t)).map (smallEtaleInverseImageSystemUnit B A D c F₀ s) ≫
        (smallEtaleDirectImageComp B A (D.map s) (D.map t) (D.map (s ≫ t))
          (D.map_comp s t).symm).hom.app _ =
      smallEtaleInverseImageSystemUnit B A D c F₀ (s ≫ t) := by
  apply ((smallEtaleInverseImageAdjunction B (D.map (s ≫ t)) A).homEquiv _ _).symm.injective
  rw [← Stacks.EtaleCohomology.leftAdjointCompIso_inv_homEquiv_symm
    (smallEtaleInverseImageAdjunction B (D.map t) A)
    (smallEtaleInverseImageAdjunction B (D.map s) A),
    smallEtaleInverseImageSystemUnit_eq B A D c F₀ (s ≫ t),
    smallEtaleInverseImageSystemUnit_eq B A D c F₀ s,
    smallEtaleInverseImageSystemUnit_eq B A D c F₀ t]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change (smallEtaleInverseImageComp B A (D.map s) (D.map t) (D.map (s ≫ t))
    (D.map_comp s t).symm).inv.app _ ≫ _ = _
  rw [← smallEtaleInverseImageComp_hom_app_cocycle B A (D.map s) (D.map t) (c.ι.app j)
      (c.ι.app i) (c.w t) (D.map (s ≫ t)) (D.map_comp s t).symm (c.ι.app k) (c.w s)
      (c.w (s ≫ t)) F₀, Iso.inv_hom_id_app_assoc]

/-- **The system of inverse images** `(p_j^* F₀, u)` along a cocone `p_j : D j ⟶ S`. -/
def smallEtaleInverseImageSystem : (smallEtaleDirectImagePseudoDiagram B A D).System where
  obj j := (smallEtaleInverseImage B (c.ι.app j) A).obj F₀
  ψ t := smallEtaleInverseImageSystemUnit B A D c F₀ t
  ψ_id j := by
    rw [smallEtaleInverseImageSystemUnit_eq]
    exact smallEtaleInverseImageAdjunction_homEquiv_comp_directImageIdIsoOfEq B A _ _
      (D.map_id j) _ F₀
  ψ_comp s t := smallEtaleInverseImageSystemUnit_comp B A D c F₀ s t

end InverseImage

section AbelianSheaves

/-- **Compatible injective resolutions along a cocone of schemes.** Let `D : J ⥤ B.Scheme` be a
small diagram of schemes of a big étale site, `p_j : D j ⟶ S` a cocone over it and `F₀` an
abelian sheaf on the small étale site of `S`; put `F_j = p_j^* F₀`, and let
`u_t : F_j ⟶ (D t)_* F_i` be the units (`smallEtaleInverseImageSystemUnit`). Then there are,
for every `j`, an injective resolution `e_j : F_j ⟶ I_j` and, for every `t : i ⟶ j`, chain maps
`ψ_t : I_j ⟶ (D t)_* I_i` over `u_t`, with `ψ_{𝟙} = id` and
`(D t)_*(ψ_s) ∘ ψ_t = ψ_{s ≫ t}` under `(D (s ≫ t))_* ≅ (D t)_* (D s)_*`. -/
@[weil "lem_fk104_projective_system_injective_resolution"]
theorem exists_injective_resolution_smallEtaleInverseImage_cocone {J : Type u} [SmallCategory J]
    (D : J ⥤ B.Scheme) (c : Cocone D)
    (F₀ : Sheaf (SmallEtale.topology B c.pt.obj c.pt.property) AddCommGrpCat.{u + 1}) :
    ∃ (I : ∀ j, CochainComplex
        (Sheaf (SmallEtale.topology B (D.obj j).obj (D.obj j).property) AddCommGrpCat.{u + 1}) ℕ)
      (e : ∀ j, (smallEtaleInverseImage B (c.ι.app j) _).obj F₀ ⟶ (I j).X 0)
      (he : ∀ j, e j ≫ (I j).d 0 1 = 0)
      (ψ : ∀ {i j : J} (t : i ⟶ j) (n : ℕ),
        (I j).X n ⟶ (smallEtaleDirectImage B _ (D.map t)).obj ((I i).X n)),
      (∀ j, (∀ n, Injective ((I j).X n)) ∧ Mono (e j) ∧
        (ShortComplex.mk (e j) ((I j).d 0 1) (he j)).Exact ∧
        ∀ n, (ShortComplex.mk ((I j).d n (n + 1)) ((I j).d (n + 1) (n + 2))
          ((I j).d_comp_d _ _ _)).Exact) ∧
      (∀ {i j : J} (t : i ⟶ j) (n : ℕ), (I j).d n (n + 1) ≫ ψ t (n + 1) =
        ψ t n ≫ (smallEtaleDirectImage B _ (D.map t)).map ((I i).d n (n + 1))) ∧
      (∀ {i j : J} (t : i ⟶ j), e j ≫ ψ t 0 =
        smallEtaleInverseImageSystemUnit B _ D c F₀ t ≫
          (smallEtaleDirectImage B _ (D.map t)).map (e i)) ∧
      (∀ (j : J) (n : ℕ), ψ (𝟙 j) n ≫
        (smallEtaleDirectImageIdIsoOfEq B _ (D.map (𝟙 j)) (D.map_id j)).hom.app ((I j).X n) =
          𝟙 _) ∧
      (∀ {i j k : J} (s : k ⟶ i) (t : i ⟶ j) (n : ℕ),
        ψ t n ≫ (smallEtaleDirectImage B _ (D.map t)).map (ψ s n) ≫
          (smallEtaleDirectImageComp B _ (D.map s) (D.map t) (D.map (s ≫ t))
            (D.map_comp s t).symm).hom.app ((I k).X n) = ψ (s ≫ t) n) := by
  have (j : J) : EnoughInjectives (Sheaf (SmallEtale.topology B (D.obj j).obj (D.obj j).property)
      AddCommGrpCat.{u + 1}) := ⟨fun F => by
    obtain ⟨I, f, hI, hf⟩ := SmallEtale.exists_mono_injective_sheaf B _ _ F
    exact ⟨{ J := I, f := f }⟩⟩
  have {i j : J} (t : i ⟶ j) : PreservesLimitsOfShape (Discrete (Σ k : J, k ⟶ i))
      ((smallEtaleDirectImagePseudoDiagram B AddCommGrpCat.{u + 1} D).map t) :=
    (smallEtaleInverseImageAdjunction B (D.map t) _).rightAdjoint_preservesLimits
      |>.preservesLimitsOfShape
  have {i j : J} (t : i ⟶ j) : Functor.PreservesZeroMorphisms
      ((smallEtaleDirectImagePseudoDiagram B AddCommGrpCat.{u + 1} D).map t) :=
    inferInstanceAs (smallEtaleDirectImage B AddCommGrpCat.{u + 1} (D.map t)).PreservesZeroMorphisms
  have {i j : J} (t : i ⟶ j) : Functor.PreservesInjectiveObjects
      ((smallEtaleDirectImagePseudoDiagram B AddCommGrpCat.{u + 1} D).map t) :=
    ⟨fun h => by have := h; exact BigEtaleSite.injective_smallPushforward_obj B (D.map t) _⟩
  obtain ⟨I, e, he, ψ, h₁, h₂, h₃, h₄, h₅⟩ :=
    (smallEtaleInverseImageSystem B _ D c F₀).exists_injective_resolution
  exact ⟨I, e, he, fun t n => ψ t n, h₁, fun t n => h₂ t n, fun t => h₃ t, h₄,
    fun s t n => h₅ s t n⟩

/-- **Compatible injective resolutions along a projective system of schemes** (Freitag–Kiehl).
Let `(X_α)` be a system of schemes of a big étale site indexed by a category `I` (for a directed
set, the arrows `β ⟶ α` are the relations `β ≥ α`), `α₀` an index and `F_{α₀}` an abelian sheaf on
the small étale site of `X_{α₀}`. For `b : β ⟶ α₀` put `F_b = p_b^* F_{α₀}`, and let
`u_t : F_a ⟶ (p_t)_* F_b` be the units along the arrows `t : b ⟶ a` over `α₀`
(`smallEtaleInverseImageSystemUnit`). There are injective resolutions `F_a ⟶ I_a` and chain maps
`ψ_t : I_a ⟶ (p_t)_* I_b` over `u_t` with `ψ_{𝟙} = id` and `(p_t)_*(ψ_s) ∘ ψ_t = ψ_{s ≫ t}`. -/
theorem exists_injective_resolution_smallEtaleInverseImage_over {Λ : Type u} [Category.{u} Λ]
    (D : Λ ⥤ B.Scheme) (α₀ : Λ)
    (F₀ : Sheaf (SmallEtale.topology B (D.obj α₀).obj (D.obj α₀).property)
      AddCommGrpCat.{u + 1}) :
    ∃ (I : ∀ j : Over α₀, CochainComplex (Sheaf (SmallEtale.topology B (D.obj j.left).obj
        (D.obj j.left).property) AddCommGrpCat.{u + 1}) ℕ)
      (e : ∀ j, (smallEtaleInverseImage B (D.map j.hom) _).obj F₀ ⟶ (I j).X 0)
      (he : ∀ j, e j ≫ (I j).d 0 1 = 0)
      (ψ : ∀ {i j : Over α₀} (t : i ⟶ j) (n : ℕ),
        (I j).X n ⟶ (smallEtaleDirectImage B _ (D.map t.left)).obj ((I i).X n)),
      (∀ j, (∀ n, Injective ((I j).X n)) ∧ Mono (e j) ∧
        (ShortComplex.mk (e j) ((I j).d 0 1) (he j)).Exact ∧
        ∀ n, (ShortComplex.mk ((I j).d n (n + 1)) ((I j).d (n + 1) (n + 2))
          ((I j).d_comp_d _ _ _)).Exact) ∧
      (∀ {i j : Over α₀} (t : i ⟶ j) (n : ℕ), (I j).d n (n + 1) ≫ ψ t (n + 1) =
        ψ t n ≫ (smallEtaleDirectImage B _ (D.map t.left)).map ((I i).d n (n + 1))) ∧
      (∀ {i j : Over α₀} (t : i ⟶ j), e j ≫ ψ t 0 =
        smallEtaleInverseImageSystemUnit B _ (Over.forget α₀ ⋙ D)
          (D.mapCocone (Over.forgetCocone α₀)) F₀ t ≫
          (smallEtaleDirectImage B _ (D.map t.left)).map (e i)) ∧
      (∀ (j : Over α₀) (n : ℕ), ψ (𝟙 j) n ≫ (smallEtaleDirectImageIdIsoOfEq B _
        (D.map (𝟙 j : j ⟶ j).left) ((Over.forget α₀ ⋙ D).map_id j)).hom.app ((I j).X n) = 𝟙 _) ∧
      (∀ {i j k : Over α₀} (s : k ⟶ i) (t : i ⟶ j) (n : ℕ),
        ψ t n ≫ (smallEtaleDirectImage B _ (D.map t.left)).map (ψ s n) ≫
          (smallEtaleDirectImageComp B _ (D.map s.left) (D.map t.left) (D.map (s ≫ t).left)
            ((Over.forget α₀ ⋙ D).map_comp s t).symm).hom.app ((I k).X n) = ψ (s ≫ t) n) :=
  exists_injective_resolution_smallEtaleInverseImage_cocone B (Over.forget α₀ ⋙ D)
    (D.mapCocone (Over.forgetCocone α₀)) F₀

end AbelianSheaves

end AlgebraicGeometry
