module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.EtalePresheafFk101
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The Galois stalk of a presheaf on the étale category of a field

Let `K` be a field and `Ω` an extension field of `K` (in the source, a separable closure `K̄`).
Let `Λ_K` be the set of intermediate fields `K ⊆ L ⊆ Ω` with `[L : K] < ∞` and `K → L` étale,
ordered by inclusion. For `L ⊆ L'` in `Λ_K`, the inclusion `L → L'` is a morphism of the étale
category `Et(K)`. For a presheaf `F` on `Et(K)` the Galois stalk is
`F(Ω) = colim_{L ∈ Λ_K} F(L)`, the colimit along the restriction maps `F(L ⊆ L')`. For `s ∈ F(L)`
we write `[s]` for its image in `F(Ω)`, and a morphism `α : F ⟶ F'` induces
`α_Ω : F(Ω) ⟶ F'(Ω)`, `[s] ↦ [α_L(s)]`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.GaloisStalkIndex K Ω`: the poset `Λ_K` of finite étale
  intermediate fields of `Ω / K`.
- `AlgebraicGeometry.EtaleCategory.GaloisStalkIndex.toEtaleCategory K Ω`: the functor
  `Λ_K ⥤ Et(K)`, `L ↦ L`, sending an inclusion to the inclusion map.
- `AlgebraicGeometry.EtaleCategory.galoisStalk Ω F`: the Galois stalk `F(Ω)`.
- `AlgebraicGeometry.EtaleCategory.galoisStalkι Ω F L`: the map `F(L) ⟶ F(Ω)`, `s ↦ [s]`.
- `AlgebraicGeometry.EtaleCategory.galoisStalkFunctor K Ω C`: the functor `F ↦ F(Ω)`, whose action
  on a morphism `α` is `α_Ω`.

## Main results

- `AlgebraicGeometry.EtaleCategory.GaloisStalkIndex.mem_iff`: `L ∈ Λ_K` iff `L / K` is finite and
  separable.
- `AlgebraicGeometry.EtaleCategory.GaloisStalkIndex.isFiltered`: `Λ_K` is directed and nonempty.
- `AlgebraicGeometry.EtaleCategory.galoisStalkι_galoisStalkFunctor_map`: `α_Ω [s] = [α_L s]`.
- `AlgebraicGeometry.EtaleCategory.galoisStalk_exists_rep`,
  `AlgebraicGeometry.EtaleCategory.galoisStalkι_eq_iff`: for presheaves of abelian groups, every
  element of `F(Ω)` is some `[s]`, and `[s] = [t]` iff `s` and `t` agree on a common
  `L'' ∈ Λ_K`.

## Implementation notes

The extension `Ω` is arbitrary: the definition makes sense for every extension field of `K`, and
the source's case is `Ω = K̄`, a separable closure. The stalk is defined for presheaves with values
in any category having colimits of shape `Λ_K`; the source's case is abelian groups.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace EtaleCategory

variable (K : Type u) [Field K] (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- The poset `Λ_K` of intermediate fields `K ⊆ L ⊆ Ω` with `[L : K] < ∞` and `K → L` étale,
ordered by inclusion. -/
@[weil "def_fk101_galois_stalk"]
def GaloisStalkIndex : Type u :=
  {L : IntermediateField K Ω // FiniteDimensional K L ∧ Algebra.Etale K L}

namespace GaloisStalkIndex

instance : PartialOrder (GaloisStalkIndex K Ω) :=
  inferInstanceAs (PartialOrder {L : IntermediateField K Ω // FiniteDimensional K L ∧
    Algebra.Etale K L})

variable {K Ω}

/-- The intermediate field underlying an element of `Λ_K`. -/
abbrev field (L : GaloisStalkIndex K Ω) : IntermediateField K Ω := L.1

instance (L : GaloisStalkIndex K Ω) : FiniteDimensional K L.field := L.2.1

instance (L : GaloisStalkIndex K Ω) : Algebra.Etale K L.field := L.2.2

lemma le_iff {L L' : GaloisStalkIndex K Ω} : L ≤ L' ↔ L.field ≤ L'.field := Iff.rfl

/-- For an intermediate field of finite degree, being étale is being separable. -/
lemma etale_iff_isSeparable (L : IntermediateField K Ω) [FiniteDimensional K L] :
    Algebra.Etale K L ↔ Algebra.IsSeparable K L := by
  refine ⟨fun _ ↦ Algebra.FormallyUnramified.isSeparable K L, fun _ ↦ ?_⟩
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.FinitePresentation K L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- An intermediate field belongs to `Λ_K` iff it is finite and separable over `K`. -/
lemma mem_iff (L : IntermediateField K Ω) :
    (FiniteDimensional K L ∧ Algebra.Etale K L) ↔
      (FiniteDimensional K L ∧ Algebra.IsSeparable K L) := by
  constructor
  · rintro ⟨h, he⟩
    exact ⟨h, (etale_iff_isSeparable L).mp he⟩
  · rintro ⟨h, hs⟩
    exact ⟨h, (etale_iff_isSeparable L).mpr hs⟩

/-- The element of `Λ_K` given by a finite separable intermediate field. -/
def ofIsSeparable (L : IntermediateField K Ω) [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : GaloisStalkIndex K Ω :=
  ⟨L, (mem_iff L).mpr ⟨inferInstance, inferInstance⟩⟩

@[simp]
lemma field_ofIsSeparable (L : IntermediateField K Ω) [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : (ofIsSeparable L).field = L := rfl

instance (L : GaloisStalkIndex K Ω) : Algebra.IsSeparable K L.field :=
  (etale_iff_isSeparable L.field).mp inferInstance

/-- The base field `K` itself, as an element of `Λ_K`. -/
instance : Inhabited (GaloisStalkIndex K Ω) := ⟨ofIsSeparable ⊥⟩

/-- The compositum of two elements of `Λ_K`. -/
def sup (L L' : GaloisStalkIndex K Ω) : GaloisStalkIndex K Ω :=
  have := IntermediateField.isSeparable_sup K Ω L.field L'.field
  ofIsSeparable (L.field ⊔ L'.field)

lemma le_sup_left (L L' : GaloisStalkIndex K Ω) : L ≤ sup L L' :=
  le_iff.mpr (_root_.le_sup_left : L.field ≤ L.field ⊔ L'.field)

lemma le_sup_right (L L' : GaloisStalkIndex K Ω) : L' ≤ sup L L' :=
  le_iff.mpr (_root_.le_sup_right : L'.field ≤ L.field ⊔ L'.field)

instance : IsDirectedOrder (GaloisStalkIndex K Ω) :=
  ⟨fun L L' ↦ ⟨sup L L', le_sup_left L L', le_sup_right L L'⟩⟩

/-- `Λ_K` is a filtered category. -/
instance isFiltered : IsFiltered (GaloisStalkIndex K Ω) :=
  isFiltered_of_directed_le_nonempty _

variable (K) in
/-- The étale `K`-algebra underlying an element of `Λ_K`. -/
def toAlgebra (L : GaloisStalkIndex K Ω) :
    (IsEtaleAlgebra (CommRingCat.of K)).FullSubcategory :=
  ⟨CommAlgCat.of K L.field, (inferInstance : Algebra.Etale K L.field)⟩

variable (K Ω) in
/-- The functor `Λ_K ⥤` étale `K`-algebras, sending an inclusion `L ⊆ L'` to the inclusion
map `L → L'`. -/
def toAlgebras : GaloisStalkIndex K Ω ⥤ (IsEtaleAlgebra (CommRingCat.of K)).FullSubcategory where
  obj L := toAlgebra K L
  map h := ObjectProperty.homMk
    (CommAlgCat.ofHom (IntermediateField.inclusion (le_iff.mp h.le)))
  map_id _ := rfl
  map_comp _ _ := rfl

variable (K Ω) in
/-- The functor `Λ_K ⥤ Et(K)`, `L ↦ L`, sending an inclusion `L ⊆ L'` to the morphism of
`Et(K)` given by the inclusion map `L → L'`. -/
@[weil "def_fk101_galois_stalk"]
def toEtaleCategory : GaloisStalkIndex K Ω ⥤ EtaleCategory (CommRingCat.of K) :=
  toAlgebras K Ω ⋙ fromAlgebras (CommRingCat.of K)

lemma toEtaleCategory_obj (L : GaloisStalkIndex K Ω) :
    (toEtaleCategory K Ω).obj L = ofAlgebra (CommRingCat.of K) (toAlgebra K L) := rfl

/-- The morphism `L ⟶ L'` of `Et(K)` attached to `L ⊆ L'` is the inclusion of fields. -/
lemma algHomOfHom_toEtaleCategory_map {L L' : GaloisStalkIndex K Ω} (h : L ⟶ L') :
    algHomOfHom ((toEtaleCategory K Ω).map h) = IntermediateField.inclusion (le_iff.mp h.le) :=
  rfl

end GaloisStalkIndex

open GaloisStalkIndex

variable {C : Type v} [Category.{w} C] [HasColimitsOfShape (GaloisStalkIndex K Ω) C]

variable {K} in
/-- **The Galois stalk.** For a presheaf `F` on `Et(K)` and an extension field `Ω` of `K`,
`F(Ω) = colim_{L ∈ Λ_K} F(L)`, the colimit along the restriction maps `F(L ⊆ L')`. -/
@[weil "def_fk101_galois_stalk"]
def galoisStalk (F : Presheaf (CommRingCat.of K) C) : C :=
  colimit (toEtaleCategory K Ω ⋙ F)

variable {K} in
/-- The map `F(L) ⟶ F(Ω)`, `s ↦ [s]`, for `L ∈ Λ_K`. -/
@[weil "def_fk101_galois_stalk"]
def galoisStalkι (F : Presheaf (CommRingCat.of K) C) (L : GaloisStalkIndex K Ω) :
    F.obj ((toEtaleCategory K Ω).obj L) ⟶ galoisStalk Ω F :=
  colimit.ι (toEtaleCategory K Ω ⋙ F) L

variable (C) in
/-- The Galois stalk as a functor on presheaves: a morphism `α : F ⟶ F'` goes to
`α_Ω : F(Ω) ⟶ F'(Ω)`, `[s] ↦ [α_L(s)]`. -/
@[weil "def_fk101_galois_stalk"]
def galoisStalkFunctor : Presheaf (CommRingCat.of K) C ⥤ C :=
  (Functor.whiskeringLeft _ _ C).obj (toEtaleCategory K Ω) ⋙ colim

variable {K}

@[simp]
lemma galoisStalkFunctor_obj (F : Presheaf (CommRingCat.of K) C) :
    (galoisStalkFunctor K Ω C).obj F = galoisStalk Ω F := rfl

/-- Compatibility of `[·]` with restriction: `[s|_{L'}] = [s]` for `L ⊆ L'`. -/
@[reassoc (attr := simp)]
lemma map_galoisStalkι (F : Presheaf (CommRingCat.of K) C) {L L' : GaloisStalkIndex K Ω}
    (h : L ⟶ L') :
    F.map ((toEtaleCategory K Ω).map h) ≫ galoisStalkι Ω F L' = galoisStalkι Ω F L :=
  colimit.w (toEtaleCategory K Ω ⋙ F) h

/-- `α_Ω [s] = [α_L s]`. -/
@[reassoc (attr := simp)]
lemma galoisStalkι_galoisStalkFunctor_map {F F' : Presheaf (CommRingCat.of K) C} (α : F ⟶ F')
    (L : GaloisStalkIndex K Ω) :
    galoisStalkι Ω F L ≫ (galoisStalkFunctor K Ω C).map α =
      α.app ((toEtaleCategory K Ω).obj L) ≫ galoisStalkι Ω F' L :=
  colimit.ι_map _ L

/-- Two maps out of `F(Ω)` agree when they agree on every `[s]`. -/
lemma galoisStalk_hom_ext {F : Presheaf (CommRingCat.of K) C} {X : C}
    {f g : galoisStalk Ω F ⟶ X} (h : ∀ L, galoisStalkι Ω F L ≫ f = galoisStalkι Ω F L ≫ g) :
    f = g :=
  colimit.hom_ext h

section AddCommGrp

/-! ### Presheaves of abelian groups -/

/-- `α_Ω [s] = [α_L s]`, elementwise, for presheaves of abelian groups. -/
lemma galoisStalkFunctor_map_galoisStalkι_apply {F F' : Presheaf (CommRingCat.of K)
    AddCommGrpCat.{u}} (α : F ⟶ F') (L : GaloisStalkIndex K Ω)
    (s : F.obj ((toEtaleCategory K Ω).obj L)) :
    (galoisStalkFunctor K Ω AddCommGrpCat.{u}).map α (galoisStalkι Ω F L s) =
      galoisStalkι Ω F' L (α.app _ s) :=
  ConcreteCategory.congr_hom (galoisStalkι_galoisStalkFunctor_map Ω α L) s

/-- Every element of `F(Ω)` is of the form `[s]` for some `L ∈ Λ_K` and `s ∈ F(L)`. -/
lemma galoisStalk_exists_rep (F : Presheaf (CommRingCat.of K) AddCommGrpCat.{u})
    (x : (galoisStalk Ω F : AddCommGrpCat.{u})) :
    ∃ (L : GaloisStalkIndex K Ω) (s : F.obj ((toEtaleCategory K Ω).obj L)),
      galoisStalkι Ω F L s = x :=
  Concrete.colimit_exists_rep (toEtaleCategory K Ω ⋙ F) x

/-- `[s] = [t]` iff `s` and `t` have the same restriction to some `L'' ∈ Λ_K` containing both
fields. -/
lemma galoisStalkι_eq_iff (F : Presheaf (CommRingCat.of K) AddCommGrpCat.{u})
    {L L' : GaloisStalkIndex K Ω} (s : F.obj ((toEtaleCategory K Ω).obj L))
    (t : F.obj ((toEtaleCategory K Ω).obj L')) :
    galoisStalkι Ω F L s = galoisStalkι Ω F L' t ↔
      ∃ (L'' : GaloisStalkIndex K Ω) (h : L ⟶ L'') (h' : L' ⟶ L''),
        F.map ((toEtaleCategory K Ω).map h) s = F.map ((toEtaleCategory K Ω).map h') t :=
  Concrete.colimit_rep_eq_iff_exists (toEtaleCategory K Ω ⋙ F) s t

/-- `[s] = 0` iff `s` restricts to `0` on some `L' ∈ Λ_K` containing `L`. -/
lemma galoisStalkι_eq_zero_iff (F : Presheaf (CommRingCat.of K) AddCommGrpCat.{u})
    {L : GaloisStalkIndex K Ω} (s : F.obj ((toEtaleCategory K Ω).obj L)) :
    galoisStalkι Ω F L s = 0 ↔
      ∃ (L' : GaloisStalkIndex K Ω) (h : L ⟶ L'), F.map ((toEtaleCategory K Ω).map h) s = 0 := by
  have h0 : galoisStalkι Ω F L (0 : F.obj ((toEtaleCategory K Ω).obj L)) = 0 := map_zero _
  rw [← h0, galoisStalkι_eq_iff]
  constructor
  · rintro ⟨L'', h, h', e⟩
    exact ⟨L'', h, e.trans (map_zero _)⟩
  · rintro ⟨L', h, e⟩
    exact ⟨L', h, h, e.trans (map_zero _).symm⟩

end AddCommGrp

end EtaleCategory

end AlgebraicGeometry
