module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImage
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.LAdicSheaves
public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.ArCategorySheaves

/-!
# Homomorphisms of ℓ-adic sheaves over an endomorphism

Let `φ : X ⟶ X` be an endomorphism of a Noetherian scheme `X` and `G = (Gₙ)` an ℓ-adic sheaf on
the small étale site of `X`. A homomorphism `f : φ^* G ⟶ G` of ℓ-adic sheaves over `φ` is a
family of homomorphisms `fₙ : φ^* Gₙ ⟶ Gₙ` of sheaves of `ℤ/ℓⁿ⁺¹ℤ`-modules, where `φ^*` is the
inverse image of sheaves on the small étale site, compatible with the transition maps:
`f_{n+1} ≫ uₙ = φ^*(uₙ) ≫ fₙ`, where `φ^*(uₙ)` is the transition map of the inverse image
system `φ^* G`. This is exactly a morphism of ℓ-adic sheaves from the inverse image
`LAdicSheaf.inverseImage φ G` to `G`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.HomOver`: homomorphisms `φ^* G ⟶ G` of ℓ-adic
  sheaves over an endomorphism `φ`.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.HomOver.mk`: such a homomorphism from a compatible
  family of homomorphisms of sheaves of modules `φ^* Gₙ ⟶ Gₙ`.

## Main results

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.HomOver.app_comp_transition`: the components are
  compatible with the transition maps.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.HomOver.ext`: a homomorphism over `φ` is determined by
  its components.

## Implementation notes

The source works with a `k`-morphism `φ` of a scheme over a field `k`; the definition does not
use the structure over `k`, so it is stated for an arbitrary endomorphism of a Noetherian scheme
of the big étale site. The levels are indexed from `0`, level `n` carrying coefficients
`ℤ/ℓⁿ⁺¹ℤ`, and each transition map is a map to the restriction of scalars of the previous level,
as in `AlgebraicGeometry.SmallEtale.LAdicSheaf`. The inverse image at each level is
`AlgebraicGeometry.smallEtaleInverseImage` with values in sheaves of modules.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, II.4][FreitagKiehl]
* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale.LAdicSheaf

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj]

/-- **Homomorphisms of ℓ-adic sheaves over an endomorphism.** For an endomorphism `φ` of `X` and
an ℓ-adic sheaf `G` on `X`, a homomorphism `φ^* G ⟶ G` of ℓ-adic sheaves: a family of
homomorphisms of sheaves of modules `φ^* Gₙ ⟶ Gₙ` compatible with the transition maps, i.e. a
morphism of ℓ-adic sheaves out of the inverse image `inverseImage φ G`. -/
@[weil "def_fk204_ladic_sheaf_homomorphism_over_endomorphism"]
abbrev HomOver (φ : X ⟶ X) (G : LAdicSheaf.{u, u + 1} B X ℓ) : Type _ :=
  inverseImage φ G ⟶ G

namespace HomOver

variable {φ : X ⟶ X} {G : LAdicSheaf.{u, u + 1} B X ℓ}

/-- The level `n` of the inverse image `φ^* G` is the inverse image of the level `n` of `G`. -/
theorem inverseImage_level_eq (n : ℕ) :
    (inverseImage φ G).level n =
      (smallEtaleInverseImage B φ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj (G.level n) :=
  rfl

/-- The component `fₙ : φ^* Gₙ ⟶ Gₙ` of a homomorphism over `φ`, a homomorphism of sheaves of
`ℤ/ℓⁿ⁺¹ℤ`-modules. -/
abbrev level (f : HomOver φ G) (n : ℕ) :
    (smallEtaleInverseImage B φ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj (G.level n) ⟶
      G.level n :=
  f.app n

/-- The components of a homomorphism over `φ` are compatible with the transition maps:
`f_{n+1} ≫ uₙ = φ^*(uₙ) ≫ fₙ`, where `φ^*(uₙ)` is the transition map of `φ^* G`. -/
@[reassoc]
theorem app_comp_transition (f : HomOver φ G) (n : ℕ) :
    f.app (n + 1) ≫ G.transition n =
      (inverseImage φ G).transition n ≫
        (sheafCompose (SmallEtale.topology B X.obj X.property)
          (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))).map (f.app n) :=
  f.naturality n

/-- A homomorphism over `φ` from a family of homomorphisms of sheaves of modules
`fₙ : φ^* Gₙ ⟶ Gₙ` compatible with the transition maps. -/
def mk
    (f : ∀ n : ℕ,
      (smallEtaleInverseImage B φ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj (G.level n) ⟶
        G.level n)
    (hf : ∀ n : ℕ, f (n + 1) ≫ G.transition n =
      (inverseImage φ G).transition n ≫
        (sheafCompose (SmallEtale.topology B X.obj X.property)
          (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))).map (f n)) :
    HomOver φ G :=
  ⟨f, hf⟩

@[simp]
theorem mk_app
    (f : ∀ n : ℕ,
      (smallEtaleInverseImage B φ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj (G.level n) ⟶
        G.level n)
    (hf : ∀ n : ℕ, f (n + 1) ≫ G.transition n =
      (inverseImage φ G).transition n ≫
        (sheafCompose (SmallEtale.topology B X.obj X.property)
          (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))).map (f n))
    (n : ℕ) : (mk f hf).app n = f n :=
  rfl

/-- A homomorphism over `φ` is determined by its components. -/
@[ext]
theorem ext {f g : HomOver φ G} (h : ∀ n, f.app n = g.app n) : f = g :=
  LAdicSheaf.Hom.ext B X ℓ h

end HomOver

end AlgebraicGeometry.SmallEtale.LAdicSheaf

end

/-! ### The inverse image of projective systems of `l`-torsion sheaves -/

/-!
# The inverse image of projective systems of `l`-torsion sheaves

Let `f : T ⟶ S` be a morphism of schemes of a big étale site. For a projective system
`F = (F_n, u_n)_{n ∈ ℤ}` of `l`-torsion sheaves on the small étale site of `S` (an object of
`P_S`), its inverse image is `f^* F = (f^* F_n, f^* u_n)_{n ∈ ℤ}`; for a morphism `g = (g_n)_n`
of `P_S`, `f^* g = (f^* g_n)_n`; and for an A–R morphism `[g]` represented by `g : F[r] ⟶ G`,
`f^* [g] = [f^* g]`. For an étale `S`-scheme `U` and a closed subscheme `A` of `S`, the
restrictions `F|U` and `F|A` are the inverse images along `U ⟶ S` and `A ⟶ S`.

That `f^* F` is again a projective system of `l`-torsion sheaves rests on the fact that the
pullback of an `l`-torsion sheaf along a continuous functor of sites is `l`-torsion: the pullback
is the sheafification of the left Kan extension of presheaves, whose sections are colimits of
sections of the original sheaf, hence locally killed by powers of `l`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.inverseImage f`: the functor
  `f^* : P_S ⥤ P_T`.
* `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.inverseImage f`: the functor
  `f^* : AR_S ⥤ AR_T`, with `f^* [r, g] = [r, f^* g]`.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.restrict`,
  `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.restrictClosed` and their A–R
  counterparts: the restrictions `F|U` to an étale `S`-scheme and `F|A` to a closed subscheme.

## Main results

* `CategoryTheory.lTorsionSheafProperty_sheafPullback_obj`: the pullback of an `l`-torsion
  abelian sheaf along a continuous functor of sites is `l`-torsion.
* `AlgebraicGeometry.SmallEtale.isLTorsionSheaf_smallEtaleInverseImage_obj`: the inverse image
  of an `l`-torsion sheaf on the small étale site is `l`-torsion.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.transition_inverseImage_obj`,
  `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.inverseImage_map_hom_app`,
  `AlgebraicGeometry.SmallEtale.ArLTorsionProjectiveSystem.inverseImage_map_homMk`: the
  defining formulas `f^* F = (f^* F_n, f^* u_n)_n`, `f^* g = (f^* g_n)_n`, `f^* [g] = [f^* g]`.
* Both functors are additive.

## Implementation notes

The inverse image commutes with the shifts `F ↦ F[r]` on the nose
(`LTorsionProjectiveSystem.shiftCompInverseImageIso` is the identity), since both act
levelwise; this makes `f^* [g] = [f^* g]` well defined on A–R morphisms. The sheaves take values
in `AddCommGrpCat.{u + 1}`, the universe in which the inverse image of sheaves on the small étale
sites of a big étale site `B : BigEtaleSite.{u}` exists.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v₁ u₁ v₂ u₂ u

namespace CategoryTheory

section LocalTorsion

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (l : ℕ)

/-- A section `x` of an abelian presheaf `P` over `U` is *locally `l`-torsion* if there is a
covering sieve of `U` on whose members the restriction of `x` is killed by a power of `l`. -/
def IsLocallyLTorsionSection {P : Dᵒᵖ ⥤ AddCommGrpCat.{w}} {U : D} (x : P.obj (op U)) : Prop :=
  ∃ R : Sieve U, R ∈ K U ∧ ∀ (V : D) (f : V ⟶ U), R f → ∃ v : ℕ, l ^ v • (P.map f.op x) = 0

variable {K l}

namespace IsLocallyLTorsionSection

variable {P : Dᵒᵖ ⥤ AddCommGrpCat.{w}}

lemma zero (U : D) : IsLocallyLTorsionSection K l (0 : P.obj (op U)) :=
  ⟨⊤, K.top_mem U, fun _ _ _ ↦ ⟨0, by simp⟩⟩

lemma add {U : D} {x y : P.obj (op U)} (hx : IsLocallyLTorsionSection K l x)
    (hy : IsLocallyLTorsionSection K l y) : IsLocallyLTorsionSection K l (x + y) := by
  obtain ⟨R, hR, hRx⟩ := hx
  obtain ⟨R', hR', hRy⟩ := hy
  refine ⟨R ⊓ R', K.intersection_covering hR hR', fun V f hf ↦ ?_⟩
  obtain ⟨a, ha⟩ := hRx V f hf.1
  obtain ⟨b, hb⟩ := hRy V f hf.2
  refine ⟨a + b, ?_⟩
  rw [map_add, smul_add, pow_add, mul_comm, mul_smul, ha, smul_zero, zero_add, mul_comm,
    mul_smul, hb, smul_zero]

lemma neg {U : D} {x : P.obj (op U)} (hx : IsLocallyLTorsionSection K l x) :
    IsLocallyLTorsionSection K l (-x) := by
  obtain ⟨R, hR, hRx⟩ := hx
  exact ⟨R, hR, fun V f hf ↦ by
    obtain ⟨a, ha⟩ := hRx V f hf
    exact ⟨a, by rw [map_neg, smul_neg, ha, neg_zero]⟩⟩

/-- Restrictions of locally `l`-torsion sections are locally `l`-torsion. -/
lemma map {U V : D} {x : P.obj (op U)} (hx : IsLocallyLTorsionSection K l x) (g : V ⟶ U) :
    IsLocallyLTorsionSection K l (P.map g.op x) := by
  obtain ⟨R, hR, hRx⟩ := hx
  refine ⟨R.pullback g, K.pullback_stable g hR, fun W f hf ↦ ?_⟩
  obtain ⟨a, ha⟩ := hRx W (f ≫ g) hf
  exact ⟨a, by rwa [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]⟩

/-- A section which is locally locally `l`-torsion is locally `l`-torsion. -/
lemma of_local {U : D} {x : P.obj (op U)} (R : Sieve U) (hR : R ∈ K U)
    (h : ∀ ⦃V : D⦄ (f : V ⟶ U), R f → IsLocallyLTorsionSection K l (P.map f.op x)) :
    IsLocallyLTorsionSection K l x := by
  choose T hT hkill using h
  refine ⟨Sieve.bind R T, K.bind_covering hR hT, ?_⟩
  rintro W _ ⟨V, k, f, hf, hk, rfl⟩
  obtain ⟨a, ha⟩ := hkill f hf W k hk
  exact ⟨a, by rwa [op_comp, P.map_comp, ConcreteCategory.comp_apply]⟩

/-- Images of locally `l`-torsion sections under a morphism of presheaves are locally
`l`-torsion. -/
lemma app {Q : Dᵒᵖ ⥤ AddCommGrpCat.{w}} (φ : P ⟶ Q) {U : D} {x : P.obj (op U)}
    (hx : IsLocallyLTorsionSection K l x) : IsLocallyLTorsionSection K l (φ.app (op U) x) := by
  obtain ⟨R, hR, hRx⟩ := hx
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨a, ha⟩ := hRx V f hf
  exact ⟨a, by rw [← NatTrans.naturality_apply, ← map_nsmul, ha, map_zero]⟩

end IsLocallyLTorsionSection

variable (K l) in
/-- The subgroup of locally `l`-torsion sections. -/
def locallyLTorsionAddSubgroup (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) (U : D) :
    AddSubgroup (P.obj (op U)) where
  carrier := {x | IsLocallyLTorsionSection K l x}
  zero_mem' := IsLocallyLTorsionSection.zero U
  add_mem' := IsLocallyLTorsionSection.add
  neg_mem' := IsLocallyLTorsionSection.neg

/-- An abelian sheaf is `l`-torsion iff all its sections are locally `l`-torsion. -/
lemma lTorsionSheafProperty_iff_forall_isLocallyLTorsionSection (F : Sheaf K AddCommGrpCat.{w}) :
    lTorsionSheafProperty K l F ↔
      ∀ (U : D) (x : F.obj.obj (op U)), IsLocallyLTorsionSection K l x :=
  Iff.rfl

/-- Being an `l`-torsion sheaf is invariant under isomorphism. -/
lemma lTorsionSheafProperty_of_iso {F G : Sheaf K AddCommGrpCat.{w}} (e : F ≅ G)
    (hF : lTorsionSheafProperty K l F) : lTorsionSheafProperty K l G := by
  intro U x
  have hx := IsLocallyLTorsionSection.app e.hom.hom (hF U (e.inv.hom.app (op U) x))
  have h : e.inv.hom ≫ e.hom.hom = 𝟙 G.obj := congrArg (·.hom) e.inv_hom_id
  rwa [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, h, NatTrans.id_app,
    ConcreteCategory.id_apply] at hx

/-- The sheafification of a presheaf whose sections are locally `l`-torsion is an `l`-torsion
sheaf. -/
lemma lTorsionSheafProperty_presheafToSheaf [HasWeakSheafify K AddCommGrpCat.{w}]
    {P : Dᵒᵖ ⥤ AddCommGrpCat.{w}} [Presheaf.IsLocallySurjective K (toSheafify K P)]
    (hP : ∀ (U : D) (x : P.obj (op U)), IsLocallyLTorsionSection K l x) :
    lTorsionSheafProperty K l ((presheafToSheaf K AddCommGrpCat.{w}).obj P) := by
  intro U y
  refine IsLocallyLTorsionSection.of_local _ (Presheaf.imageSieve_mem K (toSheafify K P) y)
    fun V f ⟨z, hz⟩ ↦ ?_
  rw [← hz]
  exact IsLocallyLTorsionSection.app (toSheafify K P) (hP V z)

end LocalTorsion

section Pullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (G : C ⥤ D) [G.IsContinuous J K]
  {l : ℕ}

/-- The sections of the left Kan extension `G.op.lan F` of an `l`-torsion sheaf `F` along a
continuous functor are locally `l`-torsion. -/
lemma isLocallyLTorsionSection_lan_obj
    [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, G.op.HasPointwiseLeftKanExtension F]
    {F : Sheaf J AddCommGrpCat.{w}} (hF : lTorsionSheafProperty J l F) (V : D)
    (y : (G.op.leftKanExtension F.obj).obj (op V)) : IsLocallyLTorsionSection K l y := by
  let P := G.op.leftKanExtension F.obj
  -- the image of a section of `F` under the unit is locally `l`-torsion
  have hη : ∀ (U : C) (x : F.obj.obj (op U)),
      IsLocallyLTorsionSection K l ((G.op.leftKanExtensionUnit F.obj).app (op U) x) := by
    intro U x
    obtain ⟨R, hR, hRx⟩ := hF U x
    refine ⟨R.functorPushforward G, (CoverPreserving.of_isContinuous G J K).cover_preserve hR,
      ?_⟩
    rintro W _ ⟨U', e, g, he, rfl⟩
    obtain ⟨a, ha⟩ := hRx U' e he
    refine ⟨a, ?_⟩
    have hnat := NatTrans.naturality_apply (G.op.leftKanExtensionUnit F.obj) e.op x
    dsimp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at hnat
    rw [op_comp, P.map_comp, ConcreteCategory.comp_apply]
    change l ^ a • P.map g.op (P.map (G.map e).op _) = 0
    rw [← hnat, ← map_nsmul, ← map_nsmul, ha, map_zero, map_zero]
  let H := locallyLTorsionAddSubgroup K l P V
  let q : P.obj (op V) ⟶ AddCommGrpCat.of (P.obj (op V) ⧸ H) :=
    AddCommGrpCat.ofHom (QuotientAddGroup.mk' H)
  have hq : (G.op.leftKanExtensionObjIsoColimit F.obj (op V)).inv ≫ q = 0 := by
    refine colimit.hom_ext fun j ↦ ?_
    rw [comp_zero, Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc]
    ext x
    exact (QuotientAddGroup.eq_zero_iff _).mpr ((hη j.left.unop x).map j.hom.unop)
  have := congrArg (fun φ ↦ φ ((G.op.leftKanExtensionObjIsoColimit F.obj (op V)).hom y))
    (congrArg ConcreteCategory.hom hq)
  simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at this
  exact (QuotientAddGroup.eq_zero_iff _).mp this

/-- **The pullback of an `l`-torsion sheaf along a continuous functor is `l`-torsion.** The
pullback is the sheafification of the left Kan extension, whose sections are locally
`l`-torsion (`isLocallyLTorsionSection_lan_obj`). -/
theorem lTorsionSheafProperty_sheafPullback_obj [HasWeakSheafify K AddCommGrpCat.{w}]
    [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, G.op.HasPointwiseLeftKanExtension F]
    [∀ P : Dᵒᵖ ⥤ AddCommGrpCat.{w}, Presheaf.IsLocallySurjective K (toSheafify K P)]
    {F : Sheaf J AddCommGrpCat.{w}} (hF : lTorsionSheafProperty J l F) :
    lTorsionSheafProperty K l ((G.sheafPullback AddCommGrpCat.{w} J K).obj F) :=
  lTorsionSheafProperty_of_iso
    ((Functor.sheafPullbackConstruction.sheafPullbackIso G AddCommGrpCat.{w} J K).app F).symm
    (lTorsionSheafProperty_presheafToSheaf fun V y ↦ isLocallyLTorsionSection_lan_obj G hF V y)

end Pullback

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S T : B.Scheme} (f : T ⟶ S) {l : ℕ}

/-- **The inverse image of an `l`-torsion sheaf is `l`-torsion.** -/
theorem isLTorsionSheaf_smallEtaleInverseImage_obj
    {G : Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (hG : IsLTorsionSheaf.{u + 1} B S.obj S.property l G) :
    IsLTorsionSheaf.{u + 1} B T.obj T.property l
      ((smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).obj G) :=
  lTorsionSheafProperty_sheafPullback_obj _ hG

namespace LTorsionProjectiveSystem

/-- **The inverse image `f^*` on projective systems of `l`-torsion sheaves.** For a morphism
`f : T ⟶ S`, the functor `P_S ⥤ P_T` sending `F = (F_n, u_n)_n` to
`f^* F = (f^* F_n, f^* u_n)_n` and a morphism `g = (g_n)_n` to `f^* g = (f^* g_n)_n`, where
`f^*` is the inverse image of abelian sheaves on the small étale sites
(`AlgebraicGeometry.smallEtaleInverseImage`). -/
@[weil "def_fk112_inverse_image_system_sheaves"]
def inverseImage :
    LTorsionProjectiveSystem.{u + 1} B S.obj S.property l ⥤
      LTorsionProjectiveSystem.{u + 1} B T.obj T.property l :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙
      (Functor.whiskeringRight _ _ _).obj (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}))
    fun F ↦ ⟨fun n ↦ isLTorsionSheaf_smallEtaleInverseImage_obj f (F.property.1 n), by
      obtain ⟨n₀, h₀⟩ := F.property.2
      have := (smallEtaleInverseImageAdjunction B f AddCommGrpCat.{u + 1}).isLeftAdjoint
      exact ⟨n₀, fun n hn ↦ (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).map_isZero
        (h₀ n hn)⟩⟩

@[simp]
theorem inverseImage_obj_obj_obj (F : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l)
    (n : ℤ) : ((inverseImage f).obj F).obj.obj (op n) =
      (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).obj (F.obj.obj (op n)) :=
  rfl

/-- The transition maps of `f^* F` are the inverse images `f^* u_n` of those of `F`. -/
@[weil "def_fk112_inverse_image_system_sheaves"]
theorem transition_inverseImage_obj (F : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l)
    (n : ℤ) : ((inverseImage f).obj F).transition n =
      (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).map (F.transition n) :=
  rfl

/-- The components of `f^* g` are the inverse images `f^* g_n` of those of `g`. -/
@[simp, weil "def_fk112_inverse_image_system_sheaves"]
theorem inverseImage_map_hom_app {F G : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l}
    (g : F ⟶ G) (n : ℤ) : ((inverseImage f).map g).hom.app (op n) =
      (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).map (g.hom.app (op n)) :=
  rfl

/-- The inverse image commutes with the shifts: `(f^* F)[r] = f^* (F[r])`. -/
def shiftCompInverseImageIso (r : ℤ) :
    shift.{u + 1} B S.obj S.property l r ⋙ inverseImage f ≅
      inverseImage f ⋙ shift.{u + 1} B T.obj T.property l r :=
  Iso.refl _

theorem inverseImage_obj_shift_obj (r : ℤ)
    (F : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l) :
    (inverseImage f).obj ((shift B S.obj S.property l r).obj F) =
      (shift B T.obj T.property l r).obj ((inverseImage f).obj F) :=
  rfl

theorem inverseImage_map_shift_map (r : ℤ)
    {F G : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l} (g : F ⟶ G) :
    (inverseImage f).map ((shift B S.obj S.property l r).map g) =
      (shift B T.obj T.property l r).map ((inverseImage f).map g) :=
  rfl

theorem inverseImage_map_shiftMap (F : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l)
    {r t : ℕ} (h : r ≤ t) :
    (inverseImage f).map (shiftMap F h) = shiftMap ((inverseImage f).obj F) h :=
  rfl

theorem inverseImage_map_shiftShift (F : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l)
    (r s : ℕ) :
    (inverseImage f).map (shiftShift F r s) = shiftShift ((inverseImage f).obj F) r s :=
  rfl

theorem inverseImage_map_shiftι_app (F : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l)
    (r : ℕ) :
    (inverseImage f).map ((shiftι B S.obj S.property l r).app F) =
      (shiftι B T.obj T.property l r).app ((inverseImage f).obj F) :=
  rfl

instance : ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (topology B S.obj S.property) (topology B T.obj T.property)).Additive :=
  have := (smallEtaleInverseImageAdjunction B f AddCommGrpCat.{u + 1}).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

instance : (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).Additive :=
  (smallEtaleInverseImageAdjunction B f AddCommGrpCat.{u + 1}).left_adjoint_additive

instance : (inverseImage (l := l) f).Additive where
  map_add := hom_ext fun _ ↦ (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).map_add

/-- **The restriction `F|U`** of a projective system of `l`-torsion sheaves on `S` to an étale
`S`-scheme `U`: the inverse image along the structure morphism `U ⟶ S`. -/
@[weil "def_fk112_inverse_image_system_sheaves"]
abbrev restrict (U : SmallEtale B S.obj S.property) :
    LTorsionProjectiveSystem.{u + 1} B S.obj S.property l ⥤
      LTorsionProjectiveSystem.{u + 1} B U.obj.left.obj U.obj.left.property l :=
  inverseImage (S := S) U.obj.hom

/-- **The restriction `F|A`** of a projective system of `l`-torsion sheaves on `S` to a closed
subscheme `A`, given by a closed immersion `i : A ⟶ S`: the inverse image along `i`. -/
@[weil "def_fk112_inverse_image_system_sheaves"]
abbrev restrictClosed {A : B.Scheme} (i : A ⟶ S) [IsClosedImmersion (B.inclusion.map i)] :
    LTorsionProjectiveSystem.{u + 1} B S.obj S.property l ⥤
      LTorsionProjectiveSystem.{u + 1} B A.obj A.property l :=
  inverseImage i

end LTorsionProjectiveSystem

namespace ArLTorsionProjectiveSystem

open LTorsionProjectiveSystem

/-- The inverse image of the A–R morphism `[r, g]`: the class `[r, f^* g]`. -/
def inverseImageMap {X Y : ArLTorsionProjectiveSystem.{u + 1} B S.obj S.property l}
    (φ : X ⟶ Y) :
    of ((LTorsionProjectiveSystem.inverseImage f).obj X.obj) ⟶
      of ((LTorsionProjectiveSystem.inverseImage f).obj Y.obj) :=
  ArHom.lift (F := X.obj) (G := Y.obj)
    (fun p ↦ homMk (F := (LTorsionProjectiveSystem.inverseImage f).obj X.obj) p.1
      ((LTorsionProjectiveSystem.inverseImage f).map p.2))
    (fun r t h g ↦ by
      dsimp only
      rw [Functor.map_comp, inverseImage_map_shiftMap]
      exact homMk_shiftMap_comp h _) φ

theorem inverseImageMap_homMk {F G : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l}
    (r : ℕ) (g : (shift B S.obj S.property l (r : ℤ)).obj F ⟶ G) :
    inverseImageMap f (homMk r g) =
      homMk (F := (LTorsionProjectiveSystem.inverseImage f).obj F) r
        ((LTorsionProjectiveSystem.inverseImage f).map g) :=
  rfl

/-- **The inverse image `f^*` on the A–R category.** For a morphism `f : T ⟶ S`, the functor
`AR_S ⥤ AR_T` sending a projective system `F` to `f^* F` and the A–R morphism `[g]`
represented by `g : F[r] ⟶ G` to `[f^* g]`, represented by `f^* g : (f^* F)[r] ⟶ f^* G`
(`ArLTorsionProjectiveSystem.inverseImage_map_homMk`). -/
@[weil "def_fk112_inverse_image_system_sheaves"]
def inverseImage :
    ArLTorsionProjectiveSystem.{u + 1} B S.obj S.property l ⥤
      ArLTorsionProjectiveSystem.{u + 1} B T.obj T.property l where
  obj X := of ((LTorsionProjectiveSystem.inverseImage f).obj X.obj)
  map φ := inverseImageMap f φ
  map_id X := by
    rw [id_eq, id_eq]
    rfl
  map_comp {X Y Z} φ ψ := by
    induction φ using hom_induction with
    | h r g =>
    induction ψ using hom_induction with
    | h s k =>
      rw [homMk_comp_homMk]
      change inverseImageMap f (homMk _ _) = inverseImageMap f (homMk _ _) ≫
        inverseImageMap f (homMk _ _)
      rw [inverseImageMap_homMk, inverseImageMap_homMk, inverseImageMap_homMk]
      erw [homMk_comp_homMk]
      congr 1
      rw [Functor.map_comp, Functor.map_comp]
      rfl

@[simp]
theorem inverseImage_obj (X : ArLTorsionProjectiveSystem.{u + 1} B S.obj S.property l) :
    (inverseImage f).obj X = of ((LTorsionProjectiveSystem.inverseImage f).obj X.obj) :=
  rfl

/-- `f^* [g] = [f^* g]` for an A–R morphism `[g]` represented by `g : F[r] ⟶ G`. -/
@[simp, weil "def_fk112_inverse_image_system_sheaves"]
theorem inverseImage_map_homMk {F G : LTorsionProjectiveSystem.{u + 1} B S.obj S.property l}
    (r : ℕ) (g : (shift B S.obj S.property l (r : ℤ)).obj F ⟶ G) :
    (inverseImage f).map (homMk r g) =
      homMk (F := (LTorsionProjectiveSystem.inverseImage f).obj F) r
        ((LTorsionProjectiveSystem.inverseImage f).map g) :=
  rfl

instance : (inverseImage (l := l) f).Additive where
  map_add {X Y φ ψ} := by
    induction φ using hom_induction with
    | h r g =>
    induction ψ using hom_induction with
    | h s k =>
      rw [homMk_add_homMk (max r s) (le_max_left r s) (le_max_right r s)]
      change inverseImageMap f (homMk _ _) = inverseImageMap f (homMk _ _) +
        inverseImageMap f (homMk _ _)
      rw [inverseImageMap_homMk, inverseImageMap_homMk, inverseImageMap_homMk]
      erw [homMk_add_homMk (max r s) (le_max_left r s) (le_max_right r s)]
      congr 1
      rw [Functor.map_add, Functor.map_comp, Functor.map_comp]
      rfl

/-- **The restriction `F|U`** in the A–R category, for an étale `S`-scheme `U`. -/
@[weil "def_fk112_inverse_image_system_sheaves"]
abbrev restrict (U : SmallEtale B S.obj S.property) :
    ArLTorsionProjectiveSystem.{u + 1} B S.obj S.property l ⥤
      ArLTorsionProjectiveSystem.{u + 1} B U.obj.left.obj U.obj.left.property l :=
  inverseImage (S := S) U.obj.hom

/-- **The restriction `F|A`** in the A–R category, for a closed immersion `i : A ⟶ S`. -/
@[weil "def_fk112_inverse_image_system_sheaves"]
abbrev restrictClosed {A : B.Scheme} (i : A ⟶ S) [IsClosedImmersion (B.inclusion.map i)] :
    ArLTorsionProjectiveSystem.{u + 1} B S.obj S.property l ⥤
      ArLTorsionProjectiveSystem.{u + 1} B A.obj A.property l :=
  inverseImage i

end ArLTorsionProjectiveSystem

end AlgebraicGeometry.SmallEtale

end
