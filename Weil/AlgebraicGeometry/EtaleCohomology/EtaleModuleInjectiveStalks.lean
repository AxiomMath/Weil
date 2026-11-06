module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SectionwiseFunctorEtaleQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsAcyclic

/-!
# Étale sheaves of `ℤ/ℓⁿ⁺¹`-modules with injective stalks

Let `Y` be a scheme, `ℓ` a prime and `Λ = ℤ/ℓᵏ⁺¹`. A sheaf `M` of `Λ`-modules on the small étale
site of `Y` *has injective stalks* when its stalk at the separable closure of every residue field
is an injective `Λ`-module. This class of sheaves is the one along which the cup product on the
`Ext`-algebra of the unit can be moved by dimension shifting:

* the unit `Λ_Y` has injective stalks, because `Λ` is self-injective;
* tensoring with a sheaf with injective stalks is exact, because injective `Λ`-modules are flat;
* a sheaf with injective stalks embeds into an injective sheaf with a cokernel with injective
  stalks, since stalks of injective sheaves are injective and the stalk sequence splits;
* tensoring a monomorphism out of a sheaf with injective stalks with any sheaf is a monomorphism,
  since its stalks are split monomorphisms.

The module theory holds over any finite principal ideal ring `R`: it satisfies the double
annihilator condition `ann (ann a) = (a)`, from which Baer's criterion for `R` and the flatness of
injective modules follow.

## Main definitions

* `Weil.HasInjectiveStalks`: every stalk at `AlgebraicGeometry.Scheme.residueEtalePoint` is an
  injective `Λ`-module.

## Main results

* `Weil.injective_self_of_isPrincipalIdealRing`, `Weil.flat_of_injective_of_isPrincipalIdealRing`:
  a finite principal ideal ring is self-injective, and injective modules over it are flat.
* `Weil.hasInjectiveStalks_unit`
* `Weil.tensorRight_exact_of_hasInjectiveStalks`
* `Weil.exists_shortExact_injective_of_hasInjectiveStalks`
* `Weil.preservesFiniteColimits_tensorLeft`
* `Weil.mono_whiskerLeft_of_hasInjectiveStalks`, `Weil.mono_whiskerLeft_f_of_shortExact`

## Implementation notes

The tensor product is `CategoryTheory.Sheaf.monoidalCategory`, a local instance, together with the
monoidality of the class of morphisms inverted by sheafification
(`Stacks.EtaleCohomology.isMonoidal_W_etaleModules`), as in the rest of the étale duality theory.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TensorProduct

universe u

namespace Weil

section Algebra

variable {R : Type*} [CommRing R]

/-- In a finite commutative ring, `|(b)| · |ann b| = |R|`: the kernel of `r ↦ r b` is the
annihilator of `b` and its image is `(b)`. -/
theorem card_span_mul_card_ker_toSpanSingleton [Finite R] (b : R) :
    Nat.card (Ideal.span {b}) * Nat.card (LinearMap.ker (LinearMap.toSpanSingleton R R b)) =
      Nat.card R := by
  have e := (LinearMap.toSpanSingleton R R b).quotKerEquivRange
  rw [LinearMap.range_toSpanSingleton] at e
  rw [← Nat.card_congr e.toEquiv, mul_comm, ← Submodule.card_eq_card_quotient_mul_card]

/-- **Double annihilators of principal ideals** in a finite commutative ring: if the annihilator
of `a` is `(b)`, then the annihilator of `b` is `(a)`. It contains `(a)`, and both have
`|R| / |(b)|` elements by `card_span_mul_card_ker_toSpanSingleton`. -/
theorem ker_toSpanSingleton_eq_span_of_eq_span [Finite R] {a b : R}
    (hab : LinearMap.ker (LinearMap.toSpanSingleton R R a) = Ideal.span {b}) :
    LinearMap.ker (LinearMap.toSpanSingleton R R b) = Ideal.span {a} := by
  have hb : b * a = 0 := by
    have : b ∈ LinearMap.ker (LinearMap.toSpanSingleton R R a) :=
      hab ▸ Ideal.mem_span_singleton_self b
    simpa using this
  have hle : Ideal.span {a} ≤ LinearMap.ker (LinearMap.toSpanSingleton R R b) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simp [mul_comm a b, hb]
  have h1 := card_span_mul_card_ker_toSpanSingleton a
  have h2 := card_span_mul_card_ker_toSpanSingleton b
  rw [hab] at h1
  have hpos : 0 < Nat.card (Ideal.span {b}) := Nat.card_pos
  have hcard : Nat.card (Ideal.span {a}) =
      Nat.card (LinearMap.ker (LinearMap.toSpanSingleton R R b)) := by
    have := h1.trans h2.symm
    rw [mul_comm] at this
    exact (Nat.eq_of_mul_eq_mul_left hpos this)
  symm
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact hcard.symm.le

variable (R)

/-- **A finite principal ideal ring satisfies Baer's criterion over itself.** A map
`g : (a) → R` sends `a` to an element killed by the annihilator `(b)` of `a`, hence in the
annihilator `(a)` of `b`; so `g a = z a` and `g` extends to multiplication by `z`. -/
theorem baer_self_of_isPrincipalIdealRing [Finite R] [IsPrincipalIdealRing R] :
    Module.Baer R R := by
  intro I g
  set a := Submodule.IsPrincipal.generator I
  have hI : I = Ideal.span {a} := (Submodule.IsPrincipal.span_singleton_generator I).symm
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal
    (LinearMap.ker (LinearMap.toSpanSingleton R R a))).principal
  have hb' : LinearMap.ker (LinearMap.toSpanSingleton R R a) = Ideal.span {b} := hb
  have ha : a ∈ I := hI ▸ Ideal.mem_span_singleton_self a
  set c := g ⟨a, ha⟩
  have hc : c ∈ Ideal.span {a} := by
    rw [← ker_toSpanSingleton_eq_span_of_eq_span hb']
    have hba : b * a = 0 := by
      have : b ∈ LinearMap.ker (LinearMap.toSpanSingleton R R a) :=
        hb' ▸ Ideal.mem_span_singleton_self b
      simpa using this
    have : b • (⟨a, ha⟩ : I) = 0 := Subtype.ext (by simpa using hba)
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [mul_comm, show b * c = g (b • ⟨a, ha⟩) by rw [map_smul]; rfl, this, map_zero]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hc
  refine ⟨LinearMap.toSpanSingleton R R z, fun x hx => ?_⟩
  rw [hI] at hx
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  have : (⟨t * a, hI ▸ hx⟩ : I) = t • ⟨a, ha⟩ := rfl
  rw [this, map_smul, smul_eq_mul, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  change t * a * z = t * c
  rw [← hz]
  ring

/-- **A finite principal ideal ring is self-injective.** -/
theorem injective_self_of_isPrincipalIdealRing [Finite R] [IsPrincipalIdealRing R] :
    Module.Injective R R :=
  (baer_self_of_isPrincipalIdealRing R).injective

/-- **Over a finite principal ideal ring, injective modules are flat.** For an ideal `I = (a)`,
every element of `I ⊗ M` is `a ⊗ m`; if `a m = 0`, then `m` is a multiple `b z` with `(b)` the
annihilator of `a`: the map `R/ann(b) → M`, `1 ↦ m`, is well defined since `ann(b) = (a)`, and it
extends along the injection `R/ann(b) → R`, `1 ↦ b`. So `a ⊗ m = b a ⊗ z = 0`. -/
theorem flat_of_injective_of_isPrincipalIdealRing [Finite R] [IsPrincipalIdealRing R] (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Injective R M] : Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  set a := Submodule.IsPrincipal.generator I
  have hI : I = Ideal.span {a} := (Submodule.IsPrincipal.span_singleton_generator I).symm
  have ha : a ∈ I := hI ▸ Ideal.mem_span_singleton_self a
  have hgen : ∀ t : I ⊗[R] M, ∃ m : M, t = (⟨a, ha⟩ : I) ⊗ₜ m := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x m =>
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (by rw [← hI]; exact x.2)
      refine ⟨r • m, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1
      exact Subtype.ext (by simp [← hr])
    | add x y hx hy =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨n, rfl⟩ := hy
      exact ⟨m + n, by rw [TensorProduct.tmul_add]⟩
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨m, rfl⟩ := hgen t
  simp only [TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, LinearMap.lsmul_apply] at ht
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal
    (LinearMap.ker (LinearMap.toSpanSingleton R R a))).principal
  have hb' : LinearMap.ker (LinearMap.toSpanSingleton R R a) = Ideal.span {b} := hb
  have hL := ker_toSpanSingleton_eq_span_of_eq_span hb'
  set L := LinearMap.ker (LinearMap.toSpanSingleton R R b)
  have hf : Function.Injective (L.liftQ (LinearMap.toSpanSingleton R R b) le_rfl) := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hle : L ≤ LinearMap.ker (LinearMap.toSpanSingleton R M m) := by
    rw [hL, Ideal.span_le, Set.singleton_subset_iff]
    simpa using ht
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R M _ _ _ hf
    (L.liftQ (LinearMap.toSpanSingleton R M m) hle)
  have hm : b • h 1 = m := by
    have := congr($hh (Submodule.Quotient.mk 1))
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply, one_smul] at this
    rw [← map_smul, smul_eq_mul, mul_one, ← this]
  have hba : b * a = 0 := by
    have : b ∈ LinearMap.ker (LinearMap.toSpanSingleton R R a) :=
      hb' ▸ Ideal.mem_span_singleton_self b
    simpa using this
  rw [← hm, ← TensorProduct.smul_tmul]
  have : b • (⟨a, ha⟩ : I) = 0 := Subtype.ext (by simpa using hba)
  rw [this, TensorProduct.zero_tmul]

end Algebra

/-- `ℤ/n` is a principal ideal ring, as a quotient of `ℤ`. -/
instance isPrincipalIdealRing_zmod (n : ℕ) : IsPrincipalIdealRing (ZMod n) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod n)) ZMod.intCast_surjective

attribute [local instance] Sheaf.monoidalCategory

local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules (Λ := Λ) S

variable {Y : Scheme.{u}} {ℓ k : ℕ} [Fact ℓ.Prime]

/-- The coefficient ring `ℤ/ℓᵏ⁺¹`. -/
local notation "Λ" => ZMod (ℓ ^ (k + 1))

/-- Sheaves of `ℤ/ℓᵏ⁺¹`-modules on the small étale site of `Y`. -/
local notation "𝒞" => Stacks.EtaleCohomology.EtaleModules Λ Y

local instance : NeZero (ℓ ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

/-- A sheaf of `ℤ/ℓᵏ⁺¹`-modules on the small étale site of `Y` **has injective stalks** when its
stalk at the separable closure of every residue field is an injective `ℤ/ℓᵏ⁺¹`-module. -/
def HasInjectiveStalks (M : 𝒞) :
    Prop :=
  ∀ x : Y, Module.Injective Λ
    (((Scheme.residueEtalePoint.{u, 0} Y x).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj M)

local instance (R : Type) [Ring R] :
    HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} R) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} R

local instance (R : Type) [Ring R] :
    HasLimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} R) :=
  ModuleCat.instHasLimitsOfSize.{u + 1, u + 1, 0}

attribute [local instance] Stacks.EtaleCohomology.etaleModules_AB5OfSize
  Stacks.EtaleCohomology.etaleModules_preservesFilteredColimits_forget

local instance (R : Type) [CommRing R] (X : ModuleCat.{u + 1} R) :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (tensorLeft X) :=
  have := ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft R X
  inferInstance

local instance (R : Type) [CommRing R] (X : ModuleCat.{u + 1} R) :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (tensorRight X) :=
  have := ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight R X
  inferInstance

/-- An object of `ModuleCat R` is an injective module iff it is an injective object. -/
theorem moduleInjective_iff_injective {R : Type*} [Ring R] (A : ModuleCat.{u + 1} R) :
    Module.Injective R A ↔ Injective A :=
  Module.injective_iff_injective_object R A

/-- **The unit has injective stalks**: the stalk functors are monoidal, so the stalk of the unit is
the unit `Λ` of `Λ`-modules, which is self-injective. -/
theorem hasInjectiveStalks_unit :
    HasInjectiveStalks (𝟙_ (𝒞)) := by
  intro x
  rw [moduleInjective_iff_injective]
  have : Module.Injective Λ Λ :=
    injective_self_of_isPrincipalIdealRing _
  have : Injective (ModuleCat.of Λ (ULift.{u + 1} Λ)) :=
    Module.injective_object_of_injective_module (inj := Module.ulift_injective_of_injective _ this)
  exact Injective.of_iso (Functor.Monoidal.εIso _) this

/-- **Tensoring with a sheaf with injective stalks is exact**: its stalks are flat, injective
`ℤ/ℓᵏ⁺¹`-modules being flat. -/
theorem tensorRight_exact_of_hasInjectiveStalks
    (M : 𝒞)
    (hM : HasInjectiveStalks M) :
    (tensorRight M).Additive ∧ PreservesFiniteLimits (tensorRight M) ∧
      PreservesFiniteColimits (tensorRight M) := by
  refine (Scheme.isConservativeFamilyOfPoints_residueEtalePoint.{u, 0}
    Y).preservesFiniteLimits_tensorRight_of_flat _ M fun Φ => ?_
  obtain ⟨_, ⟨x⟩⟩ := Φ
  have := hM x
  exact flat_of_injective_of_isPrincipalIdealRing _ _

/-- **Embedding into an injective sheaf, with injective stalks throughout.** A sheaf `M` with
injective stalks is the kernel of `I ⟶ I/M` for an injective sheaf `I`; the stalks of `I` are
injective, and since the stalk sequence of `0 ⟶ M ⟶ I ⟶ I/M ⟶ 0` is exact and splits, the stalks
of `I/M` are direct summands of injective modules. -/
theorem exists_shortExact_injective_of_hasInjectiveStalks
    (M : 𝒞)
    (hM : HasInjectiveStalks M) :
    ∃ (S : ShortComplex (𝒞))
      (_ : S.ShortExact) (_ : S.X₁ ≅ M), Injective S.X₂ ∧ HasInjectiveStalks S.X₂ ∧
        HasInjectiveStalks S.X₃ := by
  let S := ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι M) }
  have h₂ : HasInjectiveStalks S.X₂ := fun x =>
    Scheme.moduleInjective_residueEtalePoint_sheafFiber (R := ZMod (ℓ ^ (k + 1)))
      (Injective.under M) x
  refine ⟨S, hS, Iso.refl _, inferInstanceAs (Injective (Injective.under M)), h₂, fun x => ?_⟩
  let Ψ := (Scheme.residueEtalePoint.{u, 0} Y x).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hS' := hS.map_of_exact Ψ
  have : Injective (S.map Ψ).X₁ := (moduleInjective_iff_injective _).1 (hM x)
  have : Injective (S.map Ψ).X₂ := (moduleInjective_iff_injective _).1 (h₂ x)
  let σ := hS'.splittingOfInjective
  have : Injective (S.map Ψ).X₃ := Retract.injective ⟨σ.s, (S.map Ψ).g, σ.s_g⟩
  exact (moduleInjective_iff_injective _).2 this

omit [Fact ℓ.Prime] in
/-- **Tensoring on the left is right exact**: `Z ⊗ -` is a left adjoint, the tensor product of
sheaves of modules being closed (`CategoryTheory.Sheaf.monoidalClosedLifted`). -/
theorem preservesFiniteColimits_tensorLeft
    (Z : 𝒞) :
    PreservesFiniteColimits (tensorLeft Z) := by
  let := Sheaf.monoidalClosedLifted Y.smallEtaleTopology Λ
  have : PreservesColimitsOfSize.{u, u + 1} (tensorLeft Z) :=
    (ihom.adjunction Z).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

omit [Fact ℓ.Prime] in
/-- **Tensoring a monomorphism out of a sheaf with injective stalks is a monomorphism.** At every
point the stalk of `f` is a split monomorphism, its source being injective; so is the stalk of
`Z ◁ f`, through the monoidal structure of the stalk functor, and the stalk functors jointly
reflect monomorphisms. -/
theorem mono_whiskerLeft_of_hasInjectiveStalks
    {A B : 𝒞} (f : A ⟶ B) [Mono f]
    (hA : HasInjectiveStalks A) (Z : 𝒞) :
    Mono (Z ◁ f) := by
  have : ∀ Φ : (ObjectProperty.ofObj (Scheme.residueEtalePoint.{u, 0} Y)).FullSubcategory,
      Mono ((Φ.obj.sheafFiber (A := ModuleCat.{u + 1} Λ)).map (Z ◁ f)) := by
    rintro ⟨_, ⟨x⟩⟩
    let Ψ := (Scheme.residueEtalePoint.{u, 0} Y x).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have : Injective (Ψ.obj A) := (moduleInjective_iff_injective _).1 (hA x)
    have : IsSplitMono (Ψ.map f) :=
      IsSplitMono.mk' ⟨Injective.factorThru (𝟙 _) (Ψ.map f), Injective.comp_factorThru _ _⟩
    have : IsSplitMono (Ψ.obj Z ◁ Ψ.map f) :=
      inferInstanceAs (IsSplitMono ((tensorLeft (Ψ.obj Z)).map (Ψ.map f)))
    change Mono (Ψ.map (Z ◁ f))
    rw [Functor.Monoidal.map_whiskerLeft]
    infer_instance
  exact @JointlyReflectMonomorphisms.mono _ _ _ _ _ _
    ((Scheme.isConservativeFamilyOfPoints_residueEtalePoint.{u, 0} Y).jointlyReflectMonomorphisms
      (ModuleCat.{u + 1} Λ)) _ _ _ this

omit [Fact ℓ.Prime] in
/-- **Tensoring a short exact sequence of sheaves with injective stalks keeps its first map a
monomorphism**: the case of `Weil.mono_whiskerLeft_of_hasInjectiveStalks` for `S.f`. -/
theorem mono_whiskerLeft_f_of_shortExact
    {S : ShortComplex (𝒞)}
    (hS : S.ShortExact) (h₁ : HasInjectiveStalks S.X₁) (_h₂ : HasInjectiveStalks S.X₂)
    (_h₃ : HasInjectiveStalks S.X₃)
    (Z : 𝒞) :
    Mono (Z ◁ S.f) :=
  have := hS.mono_f
  mono_whiskerLeft_of_hasInjectiveStalks S.f h₁ Z

end Weil
