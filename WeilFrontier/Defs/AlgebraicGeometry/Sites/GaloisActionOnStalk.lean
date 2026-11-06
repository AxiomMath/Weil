module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.EtalePresheafFk101
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.GaloisStalk

/-!
# The Galois action on the Galois stalk of a presheaf on `Et(K)`

Let `K` be a field, `Ω` an extension field of `K` (in the source, a separable closure `K̄`) and
`G = Aut_K(Ω)`. For `σ ∈ G` and `L ∈ Λ_K` (a finite étale intermediate field of `Ω / K`), the
image `σ L` is again in `Λ_K`, and `σ` restricts to an isomorphism of `K`-algebras
`σ|_L : L → σ L`, a morphism of the étale category `Et(K)`. These restrictions are compatible with
the inclusions: `(σ L ⊆ σ L') ∘ σ|_L = σ|_{L'} ∘ (L ⊆ L')`. Hence, for a presheaf `F` on `Et(K)`,
the maps `F(L) → F(Ω)`, `s ↦ [F(σ|_L)(s)]` induce a map `σ : F(Ω) → F(Ω)` on the Galois stalk,
characterised by
`σ · [s] = [F(σ|_L)(s)]` for `s ∈ F(L)`.
This is a left action of `G` on `F(Ω)` by automorphisms, natural in `F`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.GaloisStalkIndex.map σ L`: the element `σ L` of `Λ_K`.
- `AlgebraicGeometry.EtaleCategory.GaloisStalkIndex.restrictHom σ L`: the morphism
  `σ|_L : L ⟶ σ L` of `Et(K)`.
- `AlgebraicGeometry.EtaleCategory.galoisStalkAction σ F`: the map `σ : F(Ω) ⟶ F(Ω)`.
- `AlgebraicGeometry.EtaleCategory.galoisStalkActionHom F`: the action
  `Aut_K(Ω) →* Aut (F(Ω))`.

## Main results

- `AlgebraicGeometry.EtaleCategory.galoisStalkι_galoisStalkAction`: `σ · [s] = [F(σ|_L)(s)]`.
- `AlgebraicGeometry.EtaleCategory.galoisStalkAction_one`,
  `AlgebraicGeometry.EtaleCategory.galoisStalkAction_mul`: it is a left action.
- `AlgebraicGeometry.EtaleCategory.galoisStalkAction_naturality`: `α_Ω` is equivariant for every
  morphism of presheaves `α`.

## Implementation notes

The action is defined for presheaves with values in any category having colimits of shape `Λ_K`,
and for an arbitrary extension field `Ω` of `K`; the source's case is presheaves of abelian groups
and `Ω = K̄`. It is the composite of the map of colimits induced by the natural transformation
`L ↦ σ|_L` and the comparison map `colimit.pre` along the reindexing `L ↦ σ L` of `Λ_K`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace EtaleCategory

namespace GaloisStalkIndex

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω]

/-- The image `σ L ∈ Λ_K` of `L ∈ Λ_K` under a `K`-automorphism `σ` of `Ω`. -/
@[weil "def_fk101_galois_action_on_stalk"]
def map (σ : Ω ≃ₐ[K] Ω) (L : GaloisStalkIndex K Ω) : GaloisStalkIndex K Ω :=
  ⟨L.field.map (σ : Ω →ₐ[K] Ω),
    LinearEquiv.finiteDimensional (L.field.equivMap (σ : Ω →ₐ[K] Ω)).toLinearEquiv,
    Algebra.Etale.of_equiv (L.field.equivMap (σ : Ω →ₐ[K] Ω))⟩

lemma field_map (σ : Ω ≃ₐ[K] Ω) (L : GaloisStalkIndex K Ω) :
    (map σ L).field = L.field.map (σ : Ω →ₐ[K] Ω) := rfl

lemma mem_map_field {σ : Ω ≃ₐ[K] Ω} {L : GaloisStalkIndex K Ω} {x : Ω} :
    x ∈ (map σ L).field ↔ ∃ y ∈ L.field, σ y = x :=
  IntermediateField.mem_map _

lemma map_mono (σ : Ω ≃ₐ[K] Ω) : Monotone (map σ) := fun _ _ h ↦
  le_iff.mpr (IntermediateField.map_mono _ (le_iff.mp h))

@[simp]
lemma map_one (L : GaloisStalkIndex K Ω) : map 1 L = L := by
  apply Subtype.ext
  ext x
  simp [field_map, IntermediateField.mem_map]

lemma map_mul (σ τ : Ω ≃ₐ[K] Ω) (L : GaloisStalkIndex K Ω) :
    map (σ * τ) L = map σ (map τ L) := by
  apply Subtype.ext
  ext x
  simp [field_map, IntermediateField.mem_map]

variable (K Ω) in
/-- The reindexing `L ↦ σ L` of `Λ_K`, as a functor. -/
def mapFunctor (σ : Ω ≃ₐ[K] Ω) : GaloisStalkIndex K Ω ⥤ GaloisStalkIndex K Ω :=
  (map_mono σ).functor

/-- The morphism of étale `K`-algebras given by a `K`-algebra map `L → L'` between elements
of `Λ_K`. -/
def algebraHom {L L' : GaloisStalkIndex K Ω} (f : L.field →ₐ[K] L'.field) :
    toAlgebra K L ⟶ toAlgebra K L' :=
  ObjectProperty.homMk (CommAlgCat.ofHom f)

set_option backward.isDefEq.respectTransparency.types false in
lemma algebraHom_comp {L L' L'' : GaloisStalkIndex K Ω} (f : L.field →ₐ[K] L'.field)
    (g : L'.field →ₐ[K] L''.field) : algebraHom f ≫ algebraHom g = algebraHom (g.comp f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
lemma algebraHom_id (L : GaloisStalkIndex K Ω) :
    algebraHom (AlgHom.id K L.field) = 𝟙 (toAlgebra K L) :=
  rfl

/-- The morphism of `Et(K)` given by a `K`-algebra map `L → L'` between elements of `Λ_K`. -/
def etaleHom {L L' : GaloisStalkIndex K Ω} (f : L.field →ₐ[K] L'.field) :
    (toEtaleCategory K Ω).obj L ⟶ (toEtaleCategory K Ω).obj L' :=
  (fromAlgebras (CommRingCat.of K)).map (algebraHom f)

lemma etaleHom_comp {L L' L'' : GaloisStalkIndex K Ω} (f : L.field →ₐ[K] L'.field)
    (g : L'.field →ₐ[K] L''.field) : etaleHom f ≫ etaleHom g = etaleHom (g.comp f) := by
  rw [etaleHom, etaleHom, etaleHom, ← algebraHom_comp]
  exact ((fromAlgebras (CommRingCat.of K)).map_comp _ _).symm

lemma etaleHom_id (L : GaloisStalkIndex K Ω) : etaleHom (AlgHom.id K L.field) = 𝟙 _ := by
  rw [etaleHom, algebraHom_id]
  exact (fromAlgebras (CommRingCat.of K)).map_id _

lemma toEtaleCategory_map_eq_etaleHom {L L' : GaloisStalkIndex K Ω} (h : L ⟶ L') :
    (toEtaleCategory K Ω).map h = etaleHom (IntermediateField.inclusion (le_iff.mp h.le)) :=
  rfl

/-- The restriction `σ|_L : L → σ L` of `σ`, an isomorphism of `K`-algebras. -/
def restrict (σ : Ω ≃ₐ[K] Ω) (L : GaloisStalkIndex K Ω) : L.field ≃ₐ[K] (map σ L).field :=
  L.field.equivMap (σ : Ω →ₐ[K] Ω)

@[simp]
lemma coe_restrict_apply (σ : Ω ≃ₐ[K] Ω) (L : GaloisStalkIndex K Ω) (x : L.field) :
    (restrict σ L x : Ω) = σ x := rfl

/-- The morphism `σ|_L : L ⟶ σ L` of `Et(K)` given by restricting `σ` to `L`. -/
@[weil "def_fk101_galois_action_on_stalk"]
def restrictHom (σ : Ω ≃ₐ[K] Ω) (L : GaloisStalkIndex K Ω) :
    (toEtaleCategory K Ω).obj L ⟶ (toEtaleCategory K Ω).obj (map σ L) :=
  etaleHom (restrict σ L).toAlgHom

/-- `(σ L ⊆ σ L') ∘ σ|_L = σ|_{L'} ∘ (L ⊆ L')`. -/
@[reassoc]
lemma restrictHom_naturality (σ : Ω ≃ₐ[K] Ω) {L L' : GaloisStalkIndex K Ω} (h : L ⟶ L') :
    restrictHom σ L ≫ (toEtaleCategory K Ω).map ((mapFunctor K Ω σ).map h) =
      (toEtaleCategory K Ω).map h ≫ restrictHom σ L' := by
  change etaleHom (restrict σ L).toAlgHom ≫
      etaleHom (IntermediateField.inclusion (le_iff.mp (map_mono σ h.le))) =
    etaleHom (IntermediateField.inclusion (le_iff.mp h.le)) ≫ etaleHom (restrict σ L').toAlgHom
  rw [etaleHom_comp, etaleHom_comp]
  rfl

variable (K Ω) in
/-- The natural transformation `L ↦ σ|_L` from `Λ_K ⥤ Et(K)` to its reindexing by `σ`. -/
def restrictNatTrans (σ : Ω ≃ₐ[K] Ω) :
    toEtaleCategory K Ω ⟶ mapFunctor K Ω σ ⋙ toEtaleCategory K Ω where
  app L := restrictHom σ L
  naturality _ _ h := (restrictHom_naturality σ h).symm

end GaloisStalkIndex

open GaloisStalkIndex

variable {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω]
variable {C : Type v} [Category.{w} C] [HasColimitsOfShape (GaloisStalkIndex K Ω) C]

/-- **The Galois action on the Galois stalk.** For `σ ∈ Aut_K(Ω)` and a presheaf `F` on `Et(K)`,
the map `σ : F(Ω) ⟶ F(Ω)` induced by the maps `F(L) → F(Ω)`, `s ↦ [F(σ|_L)(s)]`. -/
@[weil "def_fk101_galois_action_on_stalk"]
def galoisStalkAction (σ : Ω ≃ₐ[K] Ω) (F : Presheaf (CommRingCat.of K) C) :
    galoisStalk Ω F ⟶ galoisStalk Ω F :=
  colimMap (Functor.whiskerRight (restrictNatTrans K Ω σ) F) ≫
    colimit.pre (toEtaleCategory K Ω ⋙ F) (mapFunctor K Ω σ)

/-- `σ · [s] = [F(σ|_L)(s)]`. -/
@[weil "def_fk101_galois_action_on_stalk", reassoc (attr := simp)]
lemma galoisStalkι_galoisStalkAction (σ : Ω ≃ₐ[K] Ω) (F : Presheaf (CommRingCat.of K) C)
    (L : GaloisStalkIndex K Ω) :
    galoisStalkι Ω F L ≫ galoisStalkAction σ F =
      F.map (restrictHom σ L) ≫ galoisStalkι Ω F (map σ L) := by
  exact (ι_colimMap_assoc _ _ _).trans
    (congrArg _ (colimit.ι_pre (toEtaleCategory K Ω ⋙ F) (mapFunctor K Ω σ) L))

/-- The identity of `Ω` acts trivially. -/
@[simp]
lemma galoisStalkAction_one (F : Presheaf (CommRingCat.of K) C) :
    galoisStalkAction 1 F = 𝟙 (galoisStalk Ω F) := by
  refine galoisStalk_hom_ext Ω fun L ↦ ?_
  have hle : map 1 L ≤ L := (map_one L).le
  rw [galoisStalkι_galoisStalkAction, Category.comp_id,
    ← map_galoisStalkι Ω F (homOfLE hle), ← Functor.map_comp_assoc, restrictHom,
    toEtaleCategory_map_eq_etaleHom, etaleHom_comp]
  convert (Category.id_comp (galoisStalkι Ω F L))
  convert F.map_id _
  rw [← etaleHom_id]
  congr 1

/-- `(σ τ) · x = σ · (τ · x)`. -/
lemma galoisStalkAction_mul (σ τ : Ω ≃ₐ[K] Ω) (F : Presheaf (CommRingCat.of K) C) :
    galoisStalkAction (σ * τ) F = galoisStalkAction τ F ≫ galoisStalkAction σ F := by
  refine galoisStalk_hom_ext Ω fun L ↦ ?_
  have hle : map σ (map τ L) ≤ map (σ * τ) L := (map_mul σ τ L).symm.le
  rw [galoisStalkι_galoisStalkAction, galoisStalkι_galoisStalkAction_assoc,
    galoisStalkι_galoisStalkAction, ← map_galoisStalkι Ω F (homOfLE hle),
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, restrictHom, restrictHom, restrictHom,
    toEtaleCategory_map_eq_etaleHom, etaleHom_comp, etaleHom_comp]
  congr 3

/-- A morphism of presheaves `α : F ⟶ F'` induces a `Aut_K(Ω)`-equivariant map
`α_Ω : F(Ω) ⟶ F'(Ω)`. -/
@[reassoc]
lemma galoisStalkAction_naturality (σ : Ω ≃ₐ[K] Ω) {F F' : Presheaf (CommRingCat.of K) C}
    (α : F ⟶ F') :
    galoisStalkAction σ F ≫ (galoisStalkFunctor K Ω C).map α =
      (galoisStalkFunctor K Ω C).map α ≫ galoisStalkAction σ F' := by
  refine galoisStalk_hom_ext Ω fun L ↦ ?_
  have h₁ := galoisStalkι_galoisStalkAction_assoc σ F L ((galoisStalkFunctor K Ω C).map α)
  have h₂ := galoisStalkι_galoisStalkFunctor_map_assoc Ω α L (galoisStalkAction σ F')
  have h₃ := galoisStalkι_galoisStalkFunctor_map Ω α (map σ L)
  have h₄ := galoisStalkι_galoisStalkAction σ F' L
  refine h₁.trans (Eq.trans ?_
    ((Category.assoc _ _ _).symm.trans (h₂.trans (Category.assoc _ _ _))).symm)
  refine (congrArg (F.map (restrictHom σ L) ≫ ·) h₃).trans ?_
  refine Eq.trans ?_ (congrArg (α.app _ ≫ ·) h₄.symm)
  exact α.naturality_assoc _ _

/-- The Galois action on `F(Ω)` as a monoid homomorphism `Aut_K(Ω) →* End (F(Ω))`. -/
def galoisStalkActionEndHom (F : Presheaf (CommRingCat.of K) C) :
    (Ω ≃ₐ[K] Ω) →* End (galoisStalk Ω F) where
  toFun σ := galoisStalkAction σ F
  map_one' := galoisStalkAction_one F
  map_mul' σ τ := galoisStalkAction_mul σ τ F

/-- The Galois action on `F(Ω)` as a group homomorphism `Aut_K(Ω) →* Aut (F(Ω))`: every `σ`
acts by an automorphism. -/
def galoisStalkActionHom (F : Presheaf (CommRingCat.of K) C) :
    (Ω ≃ₐ[K] Ω) →* Aut (galoisStalk Ω F) :=
  (Aut.unitsEndEquivAut (galoisStalk Ω F)).toMonoidHom.comp
    (galoisStalkActionEndHom F).toHomUnits

@[simp]
lemma galoisStalkActionHom_apply_hom (σ : Ω ≃ₐ[K] Ω) (F : Presheaf (CommRingCat.of K) C) :
    (galoisStalkActionHom F σ).hom = galoisStalkAction σ F := rfl

section AddCommGrp

/-! ### Presheaves of abelian groups -/

/-- `σ · [s] = [F(σ|_L)(s)]`, elementwise, for presheaves of abelian groups. -/
lemma galoisStalkAction_galoisStalkι_apply (σ : Ω ≃ₐ[K] Ω)
    (F : Presheaf (CommRingCat.of K) AddCommGrpCat.{u}) (L : GaloisStalkIndex K Ω)
    (s : F.obj ((toEtaleCategory K Ω).obj L)) :
    galoisStalkAction σ F (galoisStalkι Ω F L s) =
      galoisStalkι Ω F (map σ L) (F.map (restrictHom σ L) s) :=
  ConcreteCategory.congr_hom (galoisStalkι_galoisStalkAction σ F L) s

end AddCommGrp

end EtaleCategory

end AlgebraicGeometry
