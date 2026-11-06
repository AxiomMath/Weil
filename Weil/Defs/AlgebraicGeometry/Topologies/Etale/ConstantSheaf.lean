module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.LocallyConstant.Algebra
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantSheafSections
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import Weil.Attr
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# The constant presheaf of locally constant maps on `Et(S)`

Let `F` be a set (resp. an abelian group, a group). The presheaf `F_S` on the étale category
`Et(S)` sends an object `U` to the set of locally constant maps `|U| → F` on the underlying
topological space of `U` (`F` discrete), with restriction along `h : V ⟶ U` given by
`k ↦ k ∘ |h|`; for an abelian group (resp. a group) `F` the sections form a group under
pointwise addition (resp. multiplication).

Since every object `U` of `Et(S)` is a noetherian scheme, its underlying space has finitely many
connected components, each of them open, and a locally constant map on `U` is the same as a map
on the set of connected components. Hence `F_S(U) ≅ F ^ n_U` with `n_U` the number of connected
components of `U`.

## Main definitions

* `AlgebraicGeometry.locallyConstantMapsType` — the presheaf of sets on schemes sending a scheme
  to the set of locally constant `F`-valued maps on it.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheaf` — the presheaf of
  sets `F_S` on `Et(S)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheafAb` — the presheaf of
  abelian groups `F_S` on `Et(S)`, for an abelian group `F`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheafGrp` — the presheaf of
  groups `F_S` on `Et(S)`, for a group `F`.
* `LocallyConstant.equivConnectedComponents` — on a space whose connected components are open,
  locally constant maps are the maps on the set of connected components.

## Main results

* `TopologicalSpace.NoetherianSpace.instFiniteConnectedComponents` and
  `TopologicalSpace.NoetherianSpace.isOpen_connectedComponent` — a noetherian space has finitely
  many connected components, and each of them is open.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheafEquivFin` — the
  identification `F_S(U) ≃ (Fin n_U → F)`, with `n_U` the number of connected components of `U`,
  and `locallyConstantPresheafAbEquivFin` its additive version.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheafAbForgetIso` — the
  underlying presheaf of sets of the abelian presheaf is the presheaf of sets.

## Implementation notes

The presheaves are restrictions, along the functor `Et(S) ⥤ Schemes`, of presheaves on all
schemes; for abelian groups and groups these are `AlgebraicGeometry.locallyConstantMapsAb` and
`AlgebraicGeometry.locallyConstantMaps`, whose restrictions to the small étale site are known to
be the sheafifications of the constant presheaves. The sections live in the universe
`max u w`, where `u` is the universe of schemes and `w` that of `F`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public section

open CategoryTheory Opposite

universe w u

/-! ### Connected components of a noetherian space -/

namespace TopologicalSpace.NoetherianSpace

variable {X : Type*} [TopologicalSpace X] [NoetherianSpace X]

/-- A noetherian space has finitely many connected components
(`TopologicalSpace.NoetherianSpace.finite_connectedComponents`), as an instance. -/
instance instFiniteConnectedComponents : Finite (ConnectedComponents X) :=
  finite_connectedComponents X

/-- In a noetherian space every connected component is open: its complement is the union of the
finitely many other connected components, each of them closed. -/
theorem isOpen_connectedComponent (x : X) : IsOpen (connectedComponent x) := by
  have h : (connectedComponent x)ᶜ =
      ⋃ c ∈ {c : ConnectedComponents X | c ≠ ConnectedComponents.mk x},
        ConnectedComponents.mk ⁻¹' {c} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, exists_prop, exists_eq_right']
    exact (ConnectedComponents.coe_eq_coe' (x := y) (y := x)).not.symm
  rw [← isClosed_compl_iff, h]
  refine (Set.toFinite _).isClosed_biUnion fun c _ => ?_
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

instance discreteTopology_connectedComponents : DiscreteTopology (ConnectedComponents X) :=
  ConnectedComponents.discreteTopology_iff.2 isOpen_connectedComponent

end TopologicalSpace.NoetherianSpace

/-! ### Locally constant maps and connected components -/

namespace LocallyConstant

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology (ConnectedComponents X)]
  {Y : Type*}

/-- On a space whose connected components are open (equivalently, whose space of connected
components is discrete), a locally constant map is the same as a map on the set of connected
components. -/
def equivConnectedComponents : LocallyConstant X Y ≃ (ConnectedComponents X → Y) where
  toFun k := Quotient.lift k fun a b (hab : connectedComponent a = connectedComponent b) =>
    k.apply_eq_of_isPreconnected isPreconnected_connectedComponent mem_connectedComponent
      (hab ▸ mem_connectedComponent : b ∈ connectedComponent a)
  invFun g := ⟨g ∘ ConnectedComponents.mk,
    (IsLocallyConstant.of_discrete g).comp_continuous ConnectedComponents.continuous_coe⟩
  left_inv k := by ext; rfl
  right_inv g := by
    funext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl

@[simp]
lemma equivConnectedComponents_apply_mk (k : LocallyConstant X Y) (x : X) :
    equivConnectedComponents k (ConnectedComponents.mk x) = k x :=
  rfl

@[simp]
lemma equivConnectedComponents_symm_apply (g : ConnectedComponents X → Y) (x : X) :
    equivConnectedComponents.symm g x = g (ConnectedComponents.mk x) :=
  rfl

/-- The additive version of `LocallyConstant.equivConnectedComponents`. -/
def addEquivConnectedComponents [AddCommGroup Y] :
    LocallyConstant X Y ≃+ (ConnectedComponents X → Y) where
  __ := equivConnectedComponents
  map_add' _ _ := by
    funext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl

@[simp]
lemma addEquivConnectedComponents_apply_mk [AddCommGroup Y] (k : LocallyConstant X Y) (x : X) :
    addEquivConnectedComponents k (ConnectedComponents.mk x) = k x :=
  rfl

end LocallyConstant

namespace AlgebraicGeometry

/-! ### Locally constant maps as a presheaf of sets on schemes -/

/-- The presheaf of sets on schemes sending a scheme to the set of locally constant `F`-valued
maps on it, with pullback of functions on morphisms. -/
def locallyConstantMapsType (F : Type w) : Scheme.{u}ᵒᵖ ⥤ Type (max u w) where
  obj T := LocallyConstant T.unop F
  map f := TypeCat.ofHom fun k => k.comap f.unop.base.hom

@[simp]
lemma locallyConstantMapsType_map_apply (F : Type w) {T T' : Scheme.{u}ᵒᵖ} (f : T ⟶ T')
    (k : LocallyConstant T.unop F) :
    ((locallyConstantMapsType F).map f k : LocallyConstant T'.unop F) =
      k.comap f.unop.base.hom :=
  rfl

/-- The underlying presheaf of sets of `AlgebraicGeometry.locallyConstantMapsAb` is
`AlgebraicGeometry.locallyConstantMapsType`. -/
def locallyConstantMapsAbForgetIso (A : Type w) [AddCommGroup A] :
    locallyConstantMapsAb.{u, w} A ⋙ forget AddCommGrpCat ≅ locallyConstantMapsType.{w, u} A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The presheaf `F_S` on `Et(S)` -/

/-- **The constant presheaf `F_S` on `Et(S)`** for a set `F`: the presheaf of sets sending an
object `U` to the set of locally constant maps `|U| → F`, with restriction along `h : V ⟶ U`
given by `k ↦ k ∘ |h|`. -/
@[weil "def_fk102_constant_sheaf"]
abbrev locallyConstantPresheaf (F : Type w) : EtalePresheaf B S hS (Type (max u w)) :=
  (toScheme B S hS).op ⋙ locallyConstantMapsType.{w, u} F

/-- **The constant presheaf `F_S` on `Et(S)`** for an abelian group `F`: the locally constant
maps `|U| → F`, a group under pointwise addition. -/
@[weil "def_fk102_constant_sheaf"]
abbrev locallyConstantPresheafAb (F : Type w) [AddCommGroup F] :
    EtalePresheaf B S hS AddCommGrpCat.{max u w} :=
  (toScheme B S hS).op ⋙ locallyConstantMapsAb.{u, w} F

/-- The constant presheaf `F_S` on `Et(S)` for a group `F`: the locally constant maps
`|U| → F`, a group under pointwise multiplication. -/
abbrev locallyConstantPresheafGrp (F : Type w) [Group F] :
    EtalePresheaf B S hS GrpCat.{max u w} :=
  (toScheme B S hS).op ⋙ locallyConstantMaps.{u, w} F

variable {B S hS}

lemma locallyConstantPresheaf_obj (F : Type w) (U : SmallNoetherianSeparatedEtale B S hS) :
    (locallyConstantPresheaf B S hS F).obj (op U) = LocallyConstant ((toScheme B S hS).obj U) F :=
  rfl

/-- Restriction along `h : V ⟶ U` is `k ↦ k ∘ |h|`. -/
@[simp]
lemma locallyConstantPresheaf_map_apply (F : Type w) {U V : SmallNoetherianSeparatedEtale B S hS}
    (h : V ⟶ U) (k : LocallyConstant ((toScheme B S hS).obj U) F)
    (x : (toScheme B S hS).obj V) :
    (show LocallyConstant ((toScheme B S hS).obj V) F from
      (locallyConstantPresheaf B S hS F).map h.op k) x =
      k (((toScheme B S hS).map h).base x) :=
  rfl

lemma locallyConstantPresheafAb_obj (F : Type w) [AddCommGroup F]
    (U : SmallNoetherianSeparatedEtale B S hS) :
    (locallyConstantPresheafAb B S hS F).obj (op U) =
      AddCommGrpCat.of (LocallyConstant ((toScheme B S hS).obj U) F) :=
  rfl

/-- Restriction along `h : V ⟶ U` is `k ↦ k ∘ |h|`. -/
@[simp]
lemma locallyConstantPresheafAb_map_apply (F : Type w) [AddCommGroup F]
    {U V : SmallNoetherianSeparatedEtale B S hS} (h : V ⟶ U)
    (k : LocallyConstant ((toScheme B S hS).obj U) F) (x : (toScheme B S hS).obj V) :
    (show LocallyConstant ((toScheme B S hS).obj V) F from
      ((locallyConstantPresheafAb B S hS F).map h.op).hom k) x =
      k (((toScheme B S hS).map h).base x) :=
  rfl

/-- The group structure of `F_S(U)` is pointwise addition. -/
lemma locallyConstantPresheafAb_add_apply (F : Type w) [AddCommGroup F]
    (U : SmallNoetherianSeparatedEtale B S hS)
    (k l : (locallyConstantPresheafAb B S hS F).obj (op U)) (x : (toScheme B S hS).obj U) :
    (show LocallyConstant ((toScheme B S hS).obj U) F from k + l) x =
      (show LocallyConstant ((toScheme B S hS).obj U) F from k) x +
        (show LocallyConstant ((toScheme B S hS).obj U) F from l) x :=
  rfl

variable (B S hS) in
/-- The presheaf of abelian groups `F_S` has the presheaf of sets `F_S` as underlying presheaf
of sets. -/
def locallyConstantPresheafAbForgetIso (F : Type w) [AddCommGroup F] :
    locallyConstantPresheafAb B S hS F ⋙ forget AddCommGrpCat ≅ locallyConstantPresheaf B S hS F :=
  Functor.isoWhiskerLeft (toScheme B S hS).op (locallyConstantMapsAbForgetIso.{w, u} F)

/-! ### `F_S(U) = F ^ n_U` -/

/-- The underlying space of an object of `Et(S)` is noetherian. -/
instance noetherianSpace_toScheme_obj (U : SmallNoetherianSeparatedEtale B S hS) :
    TopologicalSpace.NoetherianSpace ((toScheme B S hS).obj U) :=
  inferInstance

/-- An object of `Et(S)` has finitely many connected components. -/
instance finite_connectedComponents_toScheme_obj (U : SmallNoetherianSeparatedEtale B S hS) :
    Finite (ConnectedComponents ((toScheme B S hS).obj U)) :=
  inferInstance

/-- **`F_S(U) = F ^ n_U`.** For an object `U` of `Et(S)` with `n_U` connected components, the
sections of `F_S` over `U` are the maps from the `n_U` connected components of `U` to `F`. -/
@[weil "def_fk102_constant_sheaf"]
noncomputable def locallyConstantPresheafEquivFin (F : Type w)
    (U : SmallNoetherianSeparatedEtale B S hS) :
    (locallyConstantPresheaf B S hS F).obj (op U) ≃
      (Fin (Nat.card (ConnectedComponents ((toScheme B S hS).obj U))) → F) :=
  (LocallyConstant.equivConnectedComponents (X := (toScheme B S hS).obj U) (Y := F)).trans
    (Equiv.arrowCongr (Finite.equivFin _) (Equiv.refl F))

/-- **`F_S(U) = F ^ n_U`**, as abelian groups, for an abelian group `F`. -/
@[weil "def_fk102_constant_sheaf"]
noncomputable def locallyConstantPresheafAbEquivFin (F : Type w) [AddCommGroup F]
    (U : SmallNoetherianSeparatedEtale B S hS) :
    LocallyConstant ((toScheme B S hS).obj U) F ≃+
      (Fin (Nat.card (ConnectedComponents ((toScheme B S hS).obj U))) → F) :=
  (LocallyConstant.addEquivConnectedComponents (X := (toScheme B S hS).obj U) (Y := F)).trans
    (AddEquiv.arrowCongr (Finite.equivFin _) (AddEquiv.refl F))

end SmallNoetherianSeparatedEtale

/-- The constant presheaf `F_X` of a set `F` on the étale category `Et(X)` of a bare scheme
`X`. -/
noncomputable abbrev Scheme.locallyConstantPresheaf (X : Scheme.{u}) (F : Type w) :
    X.EtalePresheaf (Type (max u w)) :=
  SmallNoetherianSeparatedEtale.locallyConstantPresheaf _ X _ F

/-- The constant presheaf `F_X` of an abelian group `F` on the étale category `Et(X)` of a bare
scheme `X`. -/
noncomputable abbrev Scheme.locallyConstantPresheafAb (X : Scheme.{u}) (F : Type w)
    [AddCommGroup F] : X.EtalePresheaf AddCommGrpCat.{max u w} :=
  SmallNoetherianSeparatedEtale.locallyConstantPresheafAb _ X _ F

end AlgebraicGeometry

end
