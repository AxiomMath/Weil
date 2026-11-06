module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.EtaleFibreProductInEt
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Weil.CategoryTheory.Sites.ConstantSheaf

/-!
# The constant presheaf `F_S` is an étale sheaf

Let `F` be a set (resp. an abelian group). The presheaf `F_S` on the étale category `Et(S)` of
noetherian separated étale `S`-schemes, sending `U` to the locally constant maps `|U| → F`,
satisfies the sheaf condition for every family of morphisms of `Et(S)` which is jointly
surjective, i.e. for every étale covering.

The argument is elementary. If `φ₁ : V₁ ⟶ U` and `φ₂ : V₂ ⟶ U` are members of the covering and
`a ∈ V₁`, `b ∈ V₂` have the same image in `U`, there is a point of `V₁ ×_U V₂` over `(a, b)`.
Hence the values of a compatible family at points over a given `u ∈ U` all agree, and define a
map `k : |U| → F`; it is locally constant because étale morphisms are open. Uniqueness is joint
surjectivity of the covering.

## Main results

* `AlgebraicGeometry.isSheafFor_locallyConstantMapsType_comp` — for a functor `Φ : C ⥤ Scheme`,
  the presheaf `V ↦ LocallyConstant (Φ V) F` satisfies the sheaf condition for a presieve whose
  members are jointly surjective open maps, provided points of two members with the same image
  in the base come from a common point of some object mapping to both.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheaf_isSheafFor` — `F_S`
  satisfies the sheaf condition for every jointly surjective presieve of `Et(S)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheafAb_isSheafFor` — the
  same for the presheaf of abelian groups `F_S`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheaf_isSheafFor_ofArrows`
  and `locallyConstantPresheafAb_isSheafFor_ofArrows` — the same for an étale covering given as
  an indexed family `(φ_i : U_i ⟶ U)_i`.

## Implementation notes

The sheaf condition is `CategoryTheory.Presieve.IsSheafFor`, whose compatibility condition is
tested on all pairs of morphisms `W ⟶ V₁`, `W ⟶ V₂` agreeing on `U`; since `Et(S)` has fibre
products (`AlgebraicGeometry.SmallNoetherianSeparatedEtale.isPullback_pullbackFst_pullbackSnd`)
this is the compatibility on `V₁ ×_U V₂` of the covering condition. For abelian groups the
sheaf condition is the one of the underlying presheaf of sets.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v₁ u₁

namespace AlgebraicGeometry

variable {C : Type u₁} [Category.{v₁} C] (Φ : C ⥤ Scheme.{u}) (F : Type w)

/-- Let `Φ : C ⥤ Scheme` and let `R` be a presieve on `U` whose members are open maps after `Φ`,
jointly surjective onto `Φ U`, and such that points of two members with the same image in `Φ U`
come from one point of an object mapping compatibly to both. Then the presheaf of locally
constant `F`-valued maps `V ↦ LocallyConstant (Φ V) F` satisfies the sheaf condition for `R`. -/
theorem isSheafFor_locallyConstantMapsType_comp {U : C} (R : Presieve U)
    (hsurj : ∀ x : Φ.obj U, ∃ (V : C) (f : V ⟶ U), R f ∧ x ∈ Set.range (Φ.map f).base)
    (hopen : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → IsOpenMap (Φ.map f).base)
    (hpt : ∀ ⦃V₁ V₂ : C⦄ (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U), R f₁ → R f₂ →
      ∀ (a : Φ.obj V₁) (b : Φ.obj V₂), (Φ.map f₁).base a = (Φ.map f₂).base b →
        ∃ (W : C) (g₁ : W ⟶ V₁) (g₂ : W ⟶ V₂), g₁ ≫ f₁ = g₂ ≫ f₂ ∧
          ∃ z : Φ.obj W, (Φ.map g₁).base z = a ∧ (Φ.map g₂).base z = b) :
    Presieve.IsSheafFor (Φ.op ⋙ locallyConstantMapsType.{w, u} F) R := by
  intro x hx
  -- the value of the family at a point of a member
  let val : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Φ.obj V → F := fun V f hf a =>
    (show LocallyConstant (Φ.obj V) F from x f hf) a
  have hval : ∀ ⦃V₁ V₂ : C⦄ (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (hf₁ : R f₁) (hf₂ : R f₂)
      (a : Φ.obj V₁) (b : Φ.obj V₂), (Φ.map f₁).base a = (Φ.map f₂).base b →
        val f₁ hf₁ a = val f₂ hf₂ b := by
    intro V₁ V₂ f₁ f₂ hf₁ hf₂ a b hab
    obtain ⟨W, g₁, g₂, hg, z, rfl, rfl⟩ := hpt f₁ f₂ hf₁ hf₂ a b hab
    have := hx g₁ g₂ hf₁ hf₂ hg
    exact congrArg (fun s : LocallyConstant (Φ.obj W) F => s z) this
  choose V f hf a ha using hsurj
  let k : Φ.obj U → F := fun u => val (f u) (hf u) (a u)
  have hk : ∀ ⦃V' : C⦄ (f' : V' ⟶ U) (hf' : R f') (b : Φ.obj V'),
      k ((Φ.map f').base b) = val f' hf' b := fun V' f' hf' b =>
    hval _ _ _ _ _ _ (ha _)
  have hlc : IsLocallyConstant k := by
    rw [IsLocallyConstant.iff_exists_open]
    intro u
    let s : Set (Φ.obj (V u)) := {y | val (f u) (hf u) y = val (f u) (hf u) (a u)}
    have hs : IsOpen s :=
      (show LocallyConstant (Φ.obj (V u)) F from x (f u) (hf u)).isLocallyConstant.isOpen_fiber _
    refine ⟨(Φ.map (f u)).base '' s, hopen _ (hf u) _ hs, ⟨a u, rfl, ha u⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hk _ (hf u) y, hy]
  let t : LocallyConstant (Φ.obj U) F := ⟨k, hlc⟩
  refine ⟨t, ?_, ?_⟩
  · intro V' f' hf'
    apply LocallyConstant.ext
    intro b
    exact hk f' hf' b
  · intro t' ht'
    apply LocallyConstant.ext
    intro u
    have h := congrArg (fun s : LocallyConstant (Φ.obj (V u)) F => s (a u)) (ht' (f u) (hf u))
    simp only at h
    change (show LocallyConstant (Φ.obj U) F from t') ((Φ.map (f u)).base (a u)) = _ at h
    rw [ha u] at h
    exact h

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Points of `V₁` and `V₂` with the same image in `U` under morphisms of `Et(S)` come from one
point of the fibre product `V₁ ×_U V₂` in `Et(S)`. -/
lemma exists_pullbackObj_point {U V₁ V₂ : SmallNoetherianSeparatedEtale B S hS}
    (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (a : (toScheme B S hS).obj V₁)
    (b : (toScheme B S hS).obj V₂)
    (hab : ((toScheme B S hS).map f₁).base a = ((toScheme B S hS).map f₂).base b) :
    ∃ z : (toScheme B S hS).obj (pullbackObj f₁ f₂),
      ((toScheme B S hS).map (pullbackFst f₁ f₂)).base z = a ∧
        ((toScheme B S hS).map (pullbackSnd f₁ f₂)).base z = b :=
  Scheme.Pullback.exists_preimage_pullback a b hab

/-- **The constant presheaf `F_S` is an étale sheaf** (sets). For every presieve `R` on an
object `U` of `Et(S)` whose members are jointly surjective, i.e. an étale covering of `U`, the
presheaf `F_S` of locally constant `F`-valued maps satisfies the sheaf condition for `R`. -/
@[weil "lem_fk102_constant_sheaf_is_sheaf"]
theorem locallyConstantPresheaf_isSheafFor (F : Type w)
    {U : SmallNoetherianSeparatedEtale B S hS} (R : Presieve U)
    (hR : ∀ x : (toScheme B S hS).obj U, ∃ (V : SmallNoetherianSeparatedEtale B S hS)
      (f : V ⟶ U), R f ∧ x ∈ Set.range ((toScheme B S hS).map f).base) :
    Presieve.IsSheafFor (locallyConstantPresheaf B S hS F) R :=
  isSheafFor_locallyConstantMapsType_comp (toScheme B S hS) F R hR
    (fun _ f _ => ((toScheme B S hS).map f).isOpenMap)
    (fun _ _ f₁ f₂ _ _ a b hab =>
      ⟨pullbackObj f₁ f₂, pullbackFst f₁ f₂, pullbackSnd f₁ f₂,
        (isPullback_pullbackFst_pullbackSnd f₁ f₂).w, exists_pullbackObj_point f₁ f₂ a b hab⟩)

/-- **The constant presheaf `F_S` is an étale sheaf** (abelian groups). For an abelian group
`F` and every presieve `R` on an object `U` of `Et(S)` whose members are jointly surjective, the
presheaf of abelian groups `F_S` satisfies the sheaf condition for `R` (on underlying sets). -/
@[weil "lem_fk102_constant_sheaf_is_sheaf"]
theorem locallyConstantPresheafAb_isSheafFor (F : Type w) [AddCommGroup F]
    {U : SmallNoetherianSeparatedEtale B S hS} (R : Presieve U)
    (hR : ∀ x : (toScheme B S hS).obj U, ∃ (V : SmallNoetherianSeparatedEtale B S hS)
      (f : V ⟶ U), R f ∧ x ∈ Set.range ((toScheme B S hS).map f).base) :
    Presieve.IsSheafFor (locallyConstantPresheafAb B S hS F ⋙ forget AddCommGrpCat) R :=
  Presieve.isSheafFor_iso (locallyConstantPresheafAbForgetIso B S hS F).symm
    (locallyConstantPresheaf_isSheafFor F R hR)

/-- `F_S` satisfies the sheaf condition for an étale covering `(φ_i : U_i ⟶ U)_i` of `Et(S)`,
i.e. a jointly surjective family of morphisms. -/
theorem locallyConstantPresheaf_isSheafFor_ofArrows (F : Type w)
    {U : SmallNoetherianSeparatedEtale B S hS} {ι : Type*}
    (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U)
    (hφ : ∀ x : (toScheme B S hS).obj U, ∃ i, x ∈ Set.range ((toScheme B S hS).map (φ i)).base) :
    Presieve.IsSheafFor (locallyConstantPresheaf B S hS F) (Presieve.ofArrows V φ) :=
  locallyConstantPresheaf_isSheafFor F _ fun x =>
    let ⟨i, hi⟩ := hφ x
    ⟨V i, φ i, Presieve.ofArrows.mk i, hi⟩

/-- The presheaf of abelian groups `F_S` satisfies the sheaf condition for an étale covering
`(φ_i : U_i ⟶ U)_i` of `Et(S)`. -/
theorem locallyConstantPresheafAb_isSheafFor_ofArrows (F : Type w) [AddCommGroup F]
    {U : SmallNoetherianSeparatedEtale B S hS} {ι : Type*}
    (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U)
    (hφ : ∀ x : (toScheme B S hS).obj U, ∃ i, x ∈ Set.range ((toScheme B S hS).map (φ i)).base) :
    Presieve.IsSheafFor (locallyConstantPresheafAb B S hS F ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows V φ) :=
  locallyConstantPresheafAb_isSheafFor F _ fun x =>
    let ⟨i, hi⟩ := hφ x
    ⟨V i, φ i, Presieve.ofArrows.mk i, hi⟩

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end

/-! ### The universal property of the constant sheaf -/

/-!
# The universal property of the constant sheaf

Let `S` be a scheme, `M` a set and `M_S` the sheaf on the small étale site of `S` sending an
étale `S`-scheme `U` to the set of locally constant maps `|U| → M`. Let `c : M → M_S(S)` send
`m` to the constant map with value `m`. For every sheaf of sets `G` the map
`Hom(M_S, G) → Map(M, G(S))`, `φ ↦ φ_S ∘ c`, is bijective, and it is natural in `G`.
If `Λ` is a ring, `M` a `Λ`-module and `G` a sheaf of `Λ`-modules, the same formula gives a
bijection `Hom_Λ(M_S, G) → Hom_Λ(M, G(S))`, where `M_S(U)` carries the pointwise `Λ`-module
structure.

The proof is formal once two facts are known: `M_S` is a sheaf, and the map from the constant
presheaf `U ↦ M` to `M_S` is a local isomorphism (locally injective and locally surjective).
Then morphisms of sheaves out of `M_S` are morphisms of presheaves out of the constant
presheaf, and those are determined by their component at the final object `S`, which may be
chosen freely. In the linear case a morphism of sheaves of sets `ψ : M_S ⟶ G` whose component
`ψ_S ∘ c` is linear is linear on every `M_S(U)`: two sections of `M_S(U)` are locally constant,
so linearity can be checked on a covering of `U` on which they are constants, where it is the
linearity of `ψ_S ∘ c`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.W.sheafHomEquiv`: on a site with a terminal object `T`,
  if a morphism `c` from the constant presheaf on `M` to a sheaf `L` is a local isomorphism,
  then `Hom(L, G) ≃ Hom(M, G(T))`, `φ ↦ c_T ≫ φ_T`.
* `AlgebraicGeometry.SmallEtale.locallyConstantPresheaf`: the presheaf `M_S` of locally
  constant maps on the small étale site.
* `AlgebraicGeometry.SmallEtale.locallyConstantSheaf`: `M_S` as a sheaf of sets.
* `AlgebraicGeometry.SmallEtale.locallyConstantModuleSheaf`: `M_S` as a sheaf of `Λ`-modules,
  for a `Λ`-module `M`.
* `AlgebraicGeometry.SmallEtale.locallyConstantSheafHomEquiv`: the bijection
  `Hom(M_S, G) ≃ Map(M, G(S))`.
* `AlgebraicGeometry.SmallEtale.locallyConstantModuleSheafHomEquiv`: the bijection
  `Hom_Λ(M_S, G) ≃ Hom_Λ(M, G(S))`.

## Main results

* `AlgebraicGeometry.SmallEtale.isSheaf_locallyConstantPresheaf`: `M_S` is a sheaf.
* `AlgebraicGeometry.SmallEtale.W_constToLocallyConstant`: the map from the constant presheaf
  to `M_S` is a local isomorphism.
* `AlgebraicGeometry.SmallEtale.locallyConstantSheafHomEquiv_apply` and
  `AlgebraicGeometry.SmallEtale.locallyConstantModuleSheafHomEquiv_apply`: the bijections are
  `φ ↦ φ_S ∘ c`.
* `AlgebraicGeometry.SmallEtale.locallyConstantSheafHomEquiv_comp` and
  `AlgebraicGeometry.SmallEtale.locallyConstantModuleSheafHomEquiv_comp`: naturality in `G`.

## Implementation notes

The site is the small étale site `AlgebraicGeometry.SmallEtale B S hS` of a big étale site `B`
containing `S`, whose final object is `AlgebraicGeometry.SmallEtale.final`. The sections of
`M_S` are the locally constant maps, as in the definition of the constant sheaf on `Et(S)`
(`AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheaf`); on a noetherian
`U` these are the maps on the finitely many connected components, i.e. `M ^ π₀(U)`. The set
`M` and the sheaves live in `Type (max (u + 1) v)`, the universes in which sheafification
exists on this site. The ring `Λ` need not be commutative.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

/- Stated on StacksFrontier's `SmallEtale B S hS` (the étale site used throughout) rather than on
FK's `Et(X)`; `M_X` is modelled by locally constant maps (= `M ^ π₀` on noetherian objects). -/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u r

/-! ### Homomorphisms out of a sheaf receiving a local isomorphism from a constant presheaf -/

namespace CategoryTheory.GrothendieckTopology.W

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  {T : C} (hT : IsTerminal T) {M : A} {L : Sheaf J A} {c : (Functor.const Cᵒᵖ).obj M ⟶ L.obj}

/-- Let `T` be a terminal object of the site and `c` a morphism from the constant presheaf with
value `M` to a sheaf `L` which is a local isomorphism. Then morphisms of sheaves `L ⟶ G`
correspond to morphisms `M ⟶ G(T)`, through `φ ↦ c_T ≫ φ_T`. -/
noncomputable def sheafHomEquiv (hc : J.W c) (G : Sheaf J A) :
    (L ⟶ G) ≃ (M ⟶ G.obj.obj (op T)) :=
  Sheaf.homEquiv.trans ((Equiv.ofBijective _ (hc G.obj G.property)).trans
    ((constantPresheafAdj A hT).homEquiv M G.obj))

lemma sheafHomEquiv_apply (hc : J.W c) (G : Sheaf J A) (φ : L ⟶ G) :
    hc.sheafHomEquiv hT G φ = c.app (op T) ≫ φ.hom.app (op T) := by
  simp [sheafHomEquiv, Adjunction.homEquiv_unit]
  rfl

/-- The bijection `GrothendieckTopology.W.sheafHomEquiv` is natural in the sheaf `G`. -/
lemma sheafHomEquiv_comp (hc : J.W c) {G G' : Sheaf J A} (φ : L ⟶ G) (ψ : G ⟶ G') :
    hc.sheafHomEquiv hT G' (φ ≫ ψ) = hc.sheafHomEquiv hT G φ ≫ ψ.hom.app (op T) := by
  simp [sheafHomEquiv_apply]

end CategoryTheory.GrothendieckTopology.W

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The sheaf of locally constant maps -/

/-- The presheaf `M_S` of sets on the small étale site of `S` sending an étale `S`-scheme `U` to
the set of locally constant maps `|U| → M`, with restriction `k ↦ k ∘ |h|` along `h`. -/
abbrev locallyConstantPresheaf (M : Type (max (u + 1) v)) :
    (SmallEtale B S hS)ᵒᵖ ⥤ Type (max (u + 1) v) :=
  (toScheme B S hS).op ⋙ locallyConstantMapsType.{max (u + 1) v, u} M

/-- For a discrete space `M`, the locally constant maps `|U| → M` are the continuous maps. -/
def locallyConstantPresheafIsoContinuousMapPresheaf (M : Type (max (u + 1) v))
    [TopologicalSpace M] [DiscreteTopology M] :
    locallyConstantPresheaf B S hS M ≅
      (toScheme B S hS).op ⋙ continuousMapPresheaf.{max (u + 1) v, u} M :=
  NatIso.ofComponents (fun U => Equiv.toIso
    { toFun := fun (f : LocallyConstant ((toScheme B S hS).obj U.unop) M) => f.toContinuousMap
      invFun := fun (f : C((toScheme B S hS).obj U.unop, M)) =>
        ⟨f, (IsLocallyConstant.iff_continuous f).2 f.continuous⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- The presheaf `M_S` of locally constant maps is a sheaf on the small étale site. -/
theorem isSheaf_locallyConstantPresheaf (M : Type (max (u + 1) v)) :
    Presheaf.IsSheaf (topology B S hS) (locallyConstantPresheaf B S hS M) := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  exact (Presheaf.isSheaf_of_iso_iff (locallyConstantPresheafIsoContinuousMapPresheaf B S hS M)).2
    (isSheaf_continuousMapPresheaf B S hS M)

/-- The sheaf `M_S` of sets on the small étale site of `S`: the locally constant maps
`|U| → M`. -/
def locallyConstantSheaf (M : Type (max (u + 1) v)) :
    Sheaf (topology B S hS) (Type (max (u + 1) v)) :=
  ⟨locallyConstantPresheaf B S hS M, isSheaf_locallyConstantPresheaf B S hS M⟩

/-- The map from the constant presheaf with value `M` to `M_S`, sending `m` to the constant map
with value `m`. -/
def constToLocallyConstant (M : Type (max (u + 1) v)) :
    (Functor.const (SmallEtale B S hS)ᵒᵖ).obj M ⟶ locallyConstantPresheaf B S hS M where
  app _ := TypeCat.ofHom fun m => LocallyConstant.const _ m
  naturality _ _ _ := rfl

@[simp]
lemma constToLocallyConstant_app_apply (M : Type (max (u + 1) v)) (U : (SmallEtale B S hS)ᵒᵖ)
    (m : M) : (constToLocallyConstant B S hS M).app U m = LocallyConstant.const _ m :=
  rfl

/-- The map from the constant presheaf to `M_S` is a local isomorphism: it is locally injective
and locally surjective. -/
theorem W_constToLocallyConstant (M : Type (max (u + 1) v)) :
    (topology B S hS).W (constToLocallyConstant B S hS M) := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  have := GrothendieckTopology.wEqualsLocallyBijective_type.{max (u + 1) v} (topology B S hS)
  have hα : (topology B S hS).W (constToContinuousMap B S hS M) :=
    (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨constToContinuousMap_isLocallyInjective B S hS M,
        constToContinuousMap_isLocallySurjective B S hS M⟩
  have he : constToContinuousMap B S hS M ≫
      (locallyConstantPresheafIsoContinuousMapPresheaf B S hS M).inv =
        constToLocallyConstant B S hS M := rfl
  rw [← he]
  exact (topology B S hS).W.comp_mem _ _ hα (MorphismProperty.of_isIso _ _)

/-! ### The universal property, for sheaves of sets -/

/-- **The universal property of the constant sheaf.** For a sheaf of sets `G` on the small
étale site of `S`, morphisms `M_S ⟶ G` correspond to maps `M → G(S)`, through
`φ ↦ φ_S ∘ c` with `c : M → M_S(S)` the constant maps
(`AlgebraicGeometry.SmallEtale.locallyConstantSheafHomEquiv_apply`); the correspondence is
natural in `G` (`AlgebraicGeometry.SmallEtale.locallyConstantSheafHomEquiv_comp`). -/
@[weil "lem_fk104_constant_sheaf_universal"]
noncomputable def locallyConstantSheafHomEquiv (M : Type (max (u + 1) v))
    (G : Sheaf (topology B S hS) (Type (max (u + 1) v))) :
    (locallyConstantSheaf B S hS M ⟶ G) ≃ (M → G.obj.obj (op (final B S hS))) :=
  ((W_constToLocallyConstant B S hS M).sheafHomEquiv (L := locallyConstantSheaf B S hS M)
    (finalIsTerminal B S hS) G).trans TypeCat.homEquiv

@[weil "lem_fk104_constant_sheaf_universal"]
lemma locallyConstantSheafHomEquiv_apply (M : Type (max (u + 1) v))
    (G : Sheaf (topology B S hS) (Type (max (u + 1) v))) (φ : locallyConstantSheaf B S hS M ⟶ G)
    (m : M) :
    locallyConstantSheafHomEquiv B S hS M G φ m =
      φ.hom.app (op (final B S hS)) (LocallyConstant.const _ m) := by
  rfl

@[weil "lem_fk104_constant_sheaf_universal"]
lemma locallyConstantSheafHomEquiv_comp (M : Type (max (u + 1) v))
    {G G' : Sheaf (topology B S hS) (Type (max (u + 1) v))}
    (φ : locallyConstantSheaf B S hS M ⟶ G) (ψ : G ⟶ G') (m : M) :
    locallyConstantSheafHomEquiv B S hS M G' (φ ≫ ψ) m =
      ψ.hom.app (op (final B S hS)) (locallyConstantSheafHomEquiv B S hS M G φ m) := by
  simp only [locallyConstantSheafHomEquiv_apply]
  rfl

/-! ### The universal property, for sheaves of `Λ`-modules -/

section Module

variable (Λ : Type r) [Ring Λ] (M : Type (max (u + 1) v)) [AddCommGroup M] [Module Λ M]

/-- The presheaf `M_S` of `Λ`-modules on the small étale site of `S`, for a `Λ`-module `M`: the
locally constant maps `|U| → M`, a `Λ`-module under pointwise operations. -/
def locallyConstantModulePresheaf : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{max (u + 1) v} Λ where
  obj U := ModuleCat.of Λ (LocallyConstant ((toScheme B S hS).obj U.unop) M)
  map f := ModuleCat.ofHom (LocallyConstant.comapₗ Λ ((toScheme B S hS).map f.unop).base.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying presheaf of sets of the presheaf of `Λ`-modules `M_S` is `M_S`. -/
def locallyConstantModulePresheafCompForgetIso :
    locallyConstantModulePresheaf B S hS Λ M ⋙ forget (ModuleCat.{max (u + 1) v} Λ) ≅
      locallyConstantPresheaf B S hS M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The presheaf of `Λ`-modules `M_S` is a sheaf. -/
theorem isSheaf_locallyConstantModulePresheaf :
    Presheaf.IsSheaf (topology B S hS) (locallyConstantModulePresheaf B S hS Λ M) := by
  have : ReflectsLimitsOfSize.{u, u + 1} (forget (ModuleCat.{max (u + 1) v} Λ)) :=
    reflectsLimitsOfSize_shrink.{u + 1, max (u + 1) v, u, max (u + 1) v} _
  exact Presheaf.isSheaf_of_isSheaf_comp _ _ (forget _)
    ((Presheaf.isSheaf_of_iso_iff (locallyConstantModulePresheafCompForgetIso B S hS Λ M)).2
      (isSheaf_locallyConstantPresheaf B S hS M))

/-- The sheaf `M_S` of `Λ`-modules on the small étale site of `S`, for a `Λ`-module `M`. -/
def locallyConstantModuleSheaf : Sheaf (topology B S hS) (ModuleCat.{max (u + 1) v} Λ) :=
  ⟨locallyConstantModulePresheaf B S hS Λ M, isSheaf_locallyConstantModulePresheaf B S hS Λ M⟩

variable {Λ M} {G : Sheaf (topology B S hS) (ModuleCat.{max (u + 1) v} Λ)}

/-- The morphism of sheaves of sets underlying a morphism of sheaves of `Λ`-modules out of
`M_S`. -/
def locallyConstantModuleSheafForgetHom (φ : locallyConstantModuleSheaf B S hS Λ M ⟶ G) :
    locallyConstantSheaf B S hS M ⟶
      (sheafCompose (topology B S hS) (forget (ModuleCat.{max (u + 1) v} Λ))).obj G :=
  Sheaf.homEquiv.symm ((locallyConstantModulePresheafCompForgetIso B S hS Λ M).inv ≫
    Functor.whiskerRight φ.hom (forget _))

/-- A morphism of sheaves of `Λ`-modules out of `M_S` is determined by its values on the
constant maps over `S`. -/
theorem locallyConstantModuleSheaf_hom_ext {φ₁ φ₂ : locallyConstantModuleSheaf B S hS Λ M ⟶ G}
    (h : ∀ m : M, φ₁.hom.app (op (final B S hS)) (LocallyConstant.const _ m) =
      φ₂.hom.app (op (final B S hS)) (LocallyConstant.const _ m)) :
    φ₁ = φ₂ := by
  have h' := (locallyConstantSheafHomEquiv B S hS M
    ((sheafCompose (topology B S hS) (forget (ModuleCat.{max (u + 1) v} Λ))).obj G)).injective
      (a₁ := locallyConstantModuleSheafForgetHom B S hS φ₁)
      (a₂ := locallyConstantModuleSheafForgetHom B S hS φ₂) (funext h)
  apply Sheaf.homEquiv.injective
  ext U x
  exact congrArg (fun ψ => ψ.hom.app U x) h'

/-- The morphism of sheaves of `Λ`-modules `M_S ⟶ G` whose value on the constant maps over `S`
is a given `Λ`-linear map `f : M → G(S)`. It is the morphism of sheaves of sets attached to `f`,
which is `Λ`-linear on every `M_S(U)`: two sections of `M_S(U)` are constant on the members of
a covering of `U`, where linearity is that of `f`. -/
noncomputable def locallyConstantModuleSheafHomOfLinearMap
    (f : M →ₗ[Λ] G.obj.obj (op (final B S hS))) : locallyConstantModuleSheaf B S hS Λ M ⟶ G := by
  let J := topology B S hS
  let G' := (sheafCompose J (forget (ModuleCat.{max (u + 1) v} Λ))).obj G
  let L := locallyConstantPresheaf B S hS M
  let c := constToLocallyConstant B S hS M
  let ψ := (locallyConstantSheafHomEquiv B S hS M G').symm (f : M → G.obj.obj (op (final B S hS)))
  have := GrothendieckTopology.wEqualsLocallyBijective_type.{max (u + 1) v} J
  have : Presheaf.IsLocallySurjective J c := (W_constToLocallyConstant B S hS M).isLocallySurjective
  have hsep : Presheaf.IsSeparated J G.obj := G.property.isSeparated
  have hψX : ∀ m : M, ψ.hom.app (op (final B S hS)) (LocallyConstant.const _ m) = f m :=
    fun m => congr_fun ((locallyConstantSheafHomEquiv B S hS M G').apply_symm_apply _) m
  have hnat : ∀ {U V : (SmallEtale B S hS)ᵒᵖ} (g : U ⟶ V) (s : L.obj U),
      (ψ.hom.app V (L.map g s) : G.obj.obj V) = G.obj.map g (ψ.hom.app U s) :=
    fun g s => ConcreteCategory.congr_hom (ψ.hom.naturality g) s
  have hconst : ∀ (V : (SmallEtale B S hS)ᵒᵖ) (m : M),
      (ψ.hom.app V (LocallyConstant.const _ m) : G.obj.obj V) =
        G.obj.map ((finalIsTerminal B S hS).from V.unop).op (f m) := fun V m => by
    rw [← hψX m]
    exact hnat ((finalIsTerminal B S hS).from V.unop).op (LocallyConstant.const _ m)
  -- on a member `g : V ⟶ U` of a covering on which `s` is the constant `m`
  have hloc : ∀ {U : (SmallEtale B S hS)ᵒᵖ} {V : SmallEtale B S hS} (g : V ⟶ U.unop)
      (s : LocallyConstant ((toScheme B S hS).obj U.unop) M) (m : M),
      c.app (op V) m = L.map g.op s →
        G.obj.map g.op (ψ.hom.app U s) =
          G.obj.map ((finalIsTerminal B S hS).from V).op (f m) := fun g s m hm =>
    (hnat g.op s).symm.trans ((congrArg (fun x => (ψ.hom.app (op _) x : G.obj.obj (op _)))
      hm.symm).trans (hconst (op _) m))
  refine Sheaf.homEquiv.symm
    { app := fun U => ModuleCat.ofHom
        { toFun := fun s => (ψ.hom.app U s : G.obj.obj U)
          map_add' := fun s t => ?_
          map_smul' := fun a s => ?_ }
      naturality := fun U V g => ?_ }
  · refine hsep U.unop _ (J.intersection_covering (Presheaf.imageSieve_mem J c s)
      (Presheaf.imageSieve_mem J c t)) _ _ ?_
    rintro V g ⟨⟨(m : M), hm⟩, ⟨(n : M), hn⟩⟩
    have hmn : c.app (op V) (m + n : M) =
        L.map g.op (s + t : LocallyConstant ((toScheme B S hS).obj U.unop) M) := by
      change LocallyConstant.const ((toScheme B S hS).obj V) m + LocallyConstant.const _ n =
        (show LocallyConstant ((toScheme B S hS).obj V) M from L.map g.op s) +
          (show LocallyConstant ((toScheme B S hS).obj V) M from L.map g.op t)
      exact congrArg₂ (fun x y : LocallyConstant ((toScheme B S hS).obj V) M => x + y) hm hn
    refine (hloc g _ _ hmn).trans ?_
    refine Eq.trans ?_ (LinearMap.map_add (G.obj.map g.op).hom _ _).symm
    refine Eq.trans ?_ (congrArg₂ (· + ·) (hloc g s m hm) (hloc g t n hn)).symm
    rw [map_add]
    exact LinearMap.map_add (G.obj.map ((finalIsTerminal B S hS).from V).op).hom _ _
  · refine hsep U.unop _ (Presheaf.imageSieve_mem J c s) _ _ ?_
    rintro V g ⟨(m : M), hm⟩
    have ham : c.app (op V) (a • m : M) =
        L.map g.op (a • s : LocallyConstant ((toScheme B S hS).obj U.unop) M) := by
      change a • LocallyConstant.const ((toScheme B S hS).obj V) m =
        a • (show LocallyConstant ((toScheme B S hS).obj V) M from L.map g.op s)
      exact congrArg (fun x : LocallyConstant ((toScheme B S hS).obj V) M => a • x) hm
    refine (hloc g _ _ ham).trans ?_
    refine Eq.trans ?_ (LinearMap.map_smul (G.obj.map g.op).hom a _).symm
    refine Eq.trans ?_ (congrArg (a • ·) (hloc g s m hm)).symm
    rw [map_smul]
    exact LinearMap.map_smul (G.obj.map ((finalIsTerminal B S hS).from V).op).hom a _
  · ext s
    exact hnat g s

lemma locallyConstantModuleSheafHomOfLinearMap_app_const
    (f : M →ₗ[Λ] G.obj.obj (op (final B S hS))) (m : M) :
    (locallyConstantModuleSheafHomOfLinearMap B S hS f).hom.app (op (final B S hS))
      (LocallyConstant.const _ m) = f m :=
  congr_fun ((locallyConstantSheafHomEquiv B S hS M
    ((sheafCompose (topology B S hS) (forget (ModuleCat.{max (u + 1) v} Λ))).obj
      G)).apply_symm_apply _) m

variable (Λ M G) in
/-- **The universal property of the constant sheaf of `Λ`-modules.** For a sheaf of
`Λ`-modules `G` on the small étale site of `S` and a `Λ`-module `M`, morphisms of sheaves of
`Λ`-modules `M_S ⟶ G` correspond to `Λ`-linear maps `M → G(S)`, through `φ ↦ φ_S ∘ c`
(`AlgebraicGeometry.SmallEtale.locallyConstantModuleSheafHomEquiv_apply`), the formula of
`AlgebraicGeometry.SmallEtale.locallyConstantSheafHomEquiv`; the correspondence is natural in
`G` (`AlgebraicGeometry.SmallEtale.locallyConstantModuleSheafHomEquiv_comp`). -/
@[weil "lem_fk104_constant_sheaf_universal"]
noncomputable def locallyConstantModuleSheafHomEquiv :
    (locallyConstantModuleSheaf B S hS Λ M ⟶ G) ≃ (M →ₗ[Λ] G.obj.obj (op (final B S hS))) :=
  Equiv.ofBijective
    (fun φ => (φ.hom.app (op (final B S hS))).hom ∘ₗ
      LocallyConstant.constₗ (X := (toScheme B S hS).obj (final B S hS)) Λ)
    ⟨fun _ _ h => locallyConstantModuleSheaf_hom_ext B S hS fun m => LinearMap.congr_fun h m,
      fun f => ⟨locallyConstantModuleSheafHomOfLinearMap B S hS f,
        LinearMap.ext (locallyConstantModuleSheafHomOfLinearMap_app_const B S hS f)⟩⟩

@[weil "lem_fk104_constant_sheaf_universal"]
lemma locallyConstantModuleSheafHomEquiv_apply (φ : locallyConstantModuleSheaf B S hS Λ M ⟶ G)
    (m : M) :
    locallyConstantModuleSheafHomEquiv B S hS Λ M G φ m =
      φ.hom.app (op (final B S hS)) (LocallyConstant.const _ m) :=
  rfl

@[weil "lem_fk104_constant_sheaf_universal"]
lemma locallyConstantModuleSheafHomEquiv_comp
    {G' : Sheaf (topology B S hS) (ModuleCat.{max (u + 1) v} Λ)}
    (φ : locallyConstantModuleSheaf B S hS Λ M ⟶ G) (ψ : G ⟶ G') :
    locallyConstantModuleSheafHomEquiv B S hS Λ M G' (φ ≫ ψ) =
      (ψ.hom.app (op (final B S hS))).hom ∘ₗ locallyConstantModuleSheafHomEquiv B S hS Λ M G φ :=
  rfl

end Module

end AlgebraicGeometry.SmallEtale

end
