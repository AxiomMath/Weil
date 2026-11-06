module

public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The holomorphic structure sheaf, the exponential sequence and the Kummer sequence

Let `M` be a complex manifold, modelled on `I : ModelWithCorners ℂ E H`. Its structure sheaf
`𝒪_M` is the sheaf of holomorphic functions `U → ℂ`, and `𝒪_M^×` is the sheaf of nowhere vanishing
holomorphic functions, i.e. holomorphic maps `U → ℂˣ`, an abelian group under multiplication.

The *exponential sequence* is
`0 ⟶ ℤ_M ⟶ 𝒪_M ⟶ 𝒪_M^× ⟶ 0`, where `ℤ_M` is the constant sheaf, the first map sends an integer
to the corresponding constant function and the second is `f ↦ exp (2πi f)`.
It is a short exact sequence of sheaves of abelian groups:
* the kernel of `f ↦ exp (2πi f)` consists of the continuous functions with values in `ℤ`, which
  are locally constant;
* the map is an epimorphism since a nowhere vanishing holomorphic function `u` has a holomorphic
  logarithm near every point `x`: on the open neighbourhood where `u / u(x)` lies in the slit
  plane, `log (u / u(x)) + log u(x)` is holomorphic and exponentiates to `u`.

For `n ≥ 1` the *Kummer sequence* is `0 ⟶ ℤ/n ⟶ 𝒪_M^× ⟶ 𝒪_M^× ⟶ 0`, the second map being
`u ↦ uⁿ` and the first one sending `k` to the constant function `exp (2πik/n)`. It is short exact:
a nowhere vanishing function with `uⁿ = 1` is continuous with values in the finite discrete set
of `n`-th roots of unity, hence locally constant; and locally `u = exp (2πi f)`, so
`u = (exp (2πi f / n))ⁿ`. Consequently the sheaf `μ_n` of `n`-th roots of unity in `𝒪_M^×`
(the kernel of `u ↦ uⁿ`) is isomorphic to the constant sheaf `ℤ/n`.

## Main definitions

* `ComplexManifold.holomorphicSheaf`: the sheaf `𝒪_M` of holomorphic functions, as a sheaf of
  commutative rings; `ComplexManifold.holomorphicSheafAb` is its underlying sheaf of abelian
  groups.
* `ComplexManifold.holomorphicUnitsSheaf`: the sheaf `𝒪_M^×`, as a sheaf of abelian groups
  (written additively, through `Additive`).
* `ComplexManifold.exponentialMap`: `𝒪_M ⟶ 𝒪_M^×`, `f ↦ exp (2πi f)`;
  more generally `ComplexManifold.expMap c`, `f ↦ exp (c f)`.
* `ComplexManifold.intToHolomorphic`: `ℤ_M ⟶ 𝒪_M`.
* `ComplexManifold.exponentialSequence`: `0 ⟶ ℤ_M ⟶ 𝒪_M ⟶ 𝒪_M^× ⟶ 0`.
* `ComplexManifold.powMap`: `𝒪_M^× ⟶ 𝒪_M^×`, `u ↦ uⁿ`.
* `ComplexManifold.zmodToHolomorphicUnits`: `ℤ/n ⟶ 𝒪_M^×`, `k ↦ exp (2πik/n)`.
* `ComplexManifold.kummerSequence`: `0 ⟶ ℤ/n ⟶ 𝒪_M^× ⟶ 𝒪_M^× ⟶ 0`.
* `ComplexManifold.rootsOfUnitySheaf`: the sheaf `μ_n`, the kernel of `u ↦ uⁿ`, and
  `ComplexManifold.kummerSequenceRootsOfUnity`: `0 ⟶ μ_n ⟶ 𝒪_M^× ⟶ 𝒪_M^× ⟶ 0`.

## Main results

* `ComplexManifold.exponentialSequence_shortExact`: the exponential sequence is short exact.
* `ComplexManifold.kummerSequence_shortExact`,
  `ComplexManifold.kummerSequenceRootsOfUnity_shortExact`: the Kummer sequence is short exact.
* `ComplexManifold.constantSheafZModIsoRootsOfUnitySheaf`: `ℤ/n ≅ μ_n`.
* `ComplexManifold.isLocallySurjective_expMap`: local logarithms.
* `TopCat.Sheaf.shortExact_of_constantSheafLift`: a criterion for a sequence
  `0 ⟶ A_X ⟶ F ⟶ G ⟶ 0` of abelian sheaves on a topological space, starting with a constant
  sheaf, to be short exact, in terms of sections.

## Implementation notes

Holomorphic functions are taken to be the `C^∞` functions for the complex model `I`, that is,
`smoothSheafCommRing I 𝓘(ℂ) M ℂ` (Mathlib's sheaf of smooth functions, which uses the
smoothness exponent `∞`, not `ω`). A complex-differentiable function on an open subset of a
complex Banach space is infinitely complex-differentiable (indeed analytic), so for a boundaryless
complex manifold modelled on `𝓘(ℂ, E)` these are exactly the holomorphic functions. Nothing below
uses the manifold axioms of `M`, only its charted structure.

The units sheaf is Mathlib's sheaf `smoothSheafCommGroup I 𝓘(ℂ) M ℂˣ` of smooth maps into the
Lie group `ℂˣ`, composed with `CommGrpCat.toAddCommGrp`, so that all sheaves live in the abelian
category of sheaves of abelian groups on `M`. The constant sheaf `A_M` is Mathlib's
`constantSheaf`, the sheafification of the constant presheaf; maps out of it are induced from the
constant presheaf (`TopCat.Sheaf.constantSheafLift`). The primitive `n`-th root of unity used to
identify `ℤ/n` with `μ_n` is `exp (2πi / n)`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], Ch. I, §11
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite


namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- A short complex of abelian sheaves on a topological space is exact if every section of the
middle term killed by the second map lifts, locally around each point, along the first map. -/
theorem exact_of_exists_local_preimage
    (S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (h : ∀ (U : Opens X) (s : S.X₂.obj.obj (op U)), S.g.hom.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ t : S.X₁.obj.obj (op V), S.f.hom.app (op V) t = S.X₂.obj.map (homOfLE hVU).op s) :
    S.Exact := by
  refine (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (C := AddCommGrpCat.{u}) (X := X) S).mpr
    fun x => ?_
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.obj y
  have h0 : TopCat.Presheaf.germ S.X₃.obj U x hxU (S.g.hom.app (op U) s) =
      TopCat.Presheaf.germ S.X₃.obj U x hxU 0 := by
    rw [map_zero]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU S.g.hom s).symm.trans hy
  obtain ⟨W, hxW, iU, iU', hW⟩ := TopCat.Presheaf.germ_eq S.X₃.obj x hxU hxU _ _ h0
  have hgW : S.g.hom.app (op W) (S.X₂.obj.map iU.op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.g.hom.naturality, ConcreteCategory.comp_apply, hW,
      map_zero]
  obtain ⟨V, hVW, hxV, t, ht⟩ := h W _ hgW x hxW
  refine ⟨TopCat.Presheaf.germ S.X₁.obj V x hxV t, ?_⟩
  change (TopCat.Presheaf.stalkFunctor _ x).map S.f.hom _ = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply]

/-- The morphism of sheaves out of the constant sheaf with value `A` induced by a morphism from
the constant presheaf. -/
noncomputable def constantSheafLift {A : AddCommGrpCat.{u}}
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ F.obj) :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A ⟶ F :=
  ObjectProperty.homMk (sheafifyLift _ φ F.property)

/-- `constantSheafLift φ` restricts to `φ` on the constant presheaf. -/
theorem toSheafify_comp_constantSheafLift {A : AddCommGrpCat.{u}}
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ F.obj) :
    toSheafify _ _ ≫ (constantSheafLift φ).hom = φ :=
  toSheafify_sheafifyLift _ _ _

/-- `constantSheafLift φ ≫ g` vanishes as soon as `φ ≫ g` does on presheaves. -/
theorem constantSheafLift_comp_eq_zero {A : AddCommGrpCat.{u}}
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ F.obj)
    (g : F ⟶ G) (hzero : φ ≫ g.hom = 0) : constantSheafLift φ ≫ g = 0 := by
  ext1
  apply sheafify_hom_ext _ _ _ G.property
  rw [ObjectProperty.FullSubcategory.comp_hom]
  erw [← Category.assoc, toSheafify_comp_constantSheafLift, hzero]
  exact (comp_zero).symm

/-- A criterion for `0 ⟶ A_X ⟶ F ⟶ G ⟶ 0` to be short exact, the first map being induced by a
morphism `φ` from the constant presheaf `A`: `φ` is injective on nonempty opens, `φ ≫ g = 0`,
every section killed by `g` is locally a constant section `φ a`, and `g` is locally surjective. -/
theorem shortExact_of_constantSheafLift {A : AddCommGrpCat.{u}}
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : (Functor.const (Opens X)ᵒᵖ).obj A ⟶ F.obj)
    (g : F ⟶ G)
    (hinj : ∀ U : Opens X, (U : Set X).Nonempty → Function.Injective (φ.app (op U)))
    (hzero : φ ≫ g.hom = 0)
    (hker : ∀ (U : Opens X) (s : F.obj.obj (op U)), g.hom.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        ∃ a : A, φ.app (op V) a = F.obj.map (homOfLE hVU).op s)
    (hsurj : TopCat.Presheaf.IsLocallySurjective g.hom) :
    (ShortComplex.mk _ _ (constantSheafLift_comp_eq_zero φ g hzero)).ShortExact := by
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ := by
    refine ⟨fun {U} x y hxy => ?_⟩
    rw [Opens.mem_grothendieckTopology]
    intro p hp
    refine ⟨U.unop, 𝟙 _, ?_, hp⟩
    simp only [Presheaf.equalizerSieve_apply, op_id]
    exact hinj U.unop ⟨p, hp⟩ hxy
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) (constantSheafLift φ).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac _
      (f₁ := toSheafify _ _) φ (toSheafify_comp_constantSheafLift φ)
  have : Mono (constantSheafLift φ) := Sheaf.mono_of_isLocallyInjective _
  have : Epi g := (TopCat.Sheaf.isLocallySurjective_iff_epi (X := X) g).mp hsurj
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  apply exact_of_exists_local_preimage
  intro U s hs x hx
  obtain ⟨V, hVU, hxV, a, ha⟩ := hker U s hs x hx
  refine ⟨V, hVU, hxV,
    (toSheafify (Opens.grothendieckTopology X) ((Functor.const _).obj A)).app (op V) a, ?_⟩
  rw [← ha]
  exact congrArg (fun f => (f.app (op V)) a) (toSheafify_comp_constantSheafLift φ)

end TopCat.Sheaf

namespace ComplexManifold

open scoped Manifold ContDiff
open Complex

/-- The exponential `ℂ → ℂˣ`. -/
noncomputable def expUnits (z : ℂ) : ℂˣ := Units.mk0 (cexp z) (Complex.exp_ne_zero z)

@[simp] lemma coe_expUnits (z : ℂ) : (expUnits z : ℂ) = cexp z := rfl

/-- The exponential `ℂ → ℂˣ` is a homomorphism. -/
lemma expUnits_add (z w : ℂ) : expUnits (z + w) = expUnits z * expUnits w :=
  Units.ext (Complex.exp_add z w)

lemma expUnits_zero : expUnits 0 = 1 := Units.ext Complex.exp_zero

/-- The exponential `ℂ → ℂˣ` is holomorphic. -/
lemma contMDiff_expUnits {n : ℕ∞ω} : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n expUnits :=
  ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    (contMDiff_iff_contDiff.mpr Complex.contDiff_exp)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type} [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The sheaf of holomorphic functions on a complex manifold, as a sheaf of commutative rings. -/
noncomputable abbrev holomorphicSheaf : TopCat.Sheaf CommRingCat (TopCat.of M) :=
  smoothSheafCommRing I 𝓘(ℂ) M ℂ

/-- The sheaf of holomorphic functions, as a sheaf of abelian groups. -/
noncomputable abbrev holomorphicSheafAb :
    Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0} :=
  smoothSheafAddCommGroup I 𝓘(ℂ) M ℂ

/-- The presheaf of nowhere vanishing holomorphic functions, written additively. -/
noncomputable def holomorphicUnitsPresheaf : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of M) :=
  smoothPresheafCommGroup I 𝓘(ℂ) M ℂˣ ⋙ CommGrpCat.toAddCommGrp

/-- The sheaf of nowhere vanishing holomorphic functions, written additively. -/
noncomputable def holomorphicUnitsSheaf :
    Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0} where
  obj := holomorphicUnitsPresheaf I M
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat)]
    exact (smoothSheaf I 𝓘(ℂ) M ℂˣ).property

variable {I M}

/-- On sections over `U`: `f ↦ exp (c * f)`. -/
noncomputable def expSections (c : ℂ) (U : Opens M) :
    C^∞⟮I, U; 𝓘(ℂ), ℂ⟯ →+ Additive C^∞⟮I, U; 𝓘(ℂ), ℂˣ⟯ where
  toFun f := Additive.ofMul
    ⟨fun x => expUnits (c * f x), contMDiff_expUnits.comp (contMDiff_const.mul f.contMDiff)⟩
  map_zero' := by
    apply Additive.toMul.injective
    refine ContMDiffMap.ext fun x => Units.ext ?_
    change cexp (c * 0) = 1
    simp
  map_add' f g := by
    apply Additive.toMul.injective
    refine ContMDiffMap.ext fun x => Units.ext ?_
    change cexp (c * (f x + g x)) = cexp (c * f x) * cexp (c * g x)
    rw [mul_add, Complex.exp_add]

@[simp] lemma expSections_apply (c : ℂ) (U : Opens M) (f : C^∞⟮I, U; 𝓘(ℂ), ℂ⟯) (x : U) :
    ((Additive.toMul (expSections c U f) x : ℂˣ) : ℂ) = cexp (c * f x) := rfl

/-- The morphism `𝒪_M ⟶ 𝒪_M^×`, `f ↦ exp (c * f)`. -/
noncomputable def expMap (c : ℂ) : holomorphicSheafAb I M ⟶ holomorphicUnitsSheaf I M :=
  ObjectProperty.homMk
  { app := fun U => AddCommGrpCat.ofHom (expSections c (unop U))
    naturality := fun _ _ _ => rfl }

/-- The `n`-th power map `𝒪_M^× ⟶ 𝒪_M^×`. -/
noncomputable def powMap (n : ℕ) : holomorphicUnitsSheaf I M ⟶ holomorphicUnitsSheaf I M :=
  ObjectProperty.homMk
  { app := fun U => AddCommGrpCat.ofHom (nsmulAddMonoidHom n)
    naturality := fun _ _ f => by
      ext s
      exact (map_nsmul _ n s).symm }

@[simp] lemma powMap_app_apply (n : ℕ) (U : (Opens (TopCat.of M))ᵒᵖ)
    (s : (holomorphicUnitsSheaf I M).obj.obj U) :
    (powMap (I := I) (M := M) n).hom.app U s = n • s := rfl

/-- The constant integer-valued functions, as a morphism from the constant presheaf `ℤ`. -/
noncomputable def intConstSections (U : Opens M) : ℤ →+ C^∞⟮I, U; 𝓘(ℂ), ℂ⟯ where
  toFun k := ContMDiffMap.const (k : ℂ)
  map_zero' := ContMDiffMap.ext fun _ => by
    change ((0 : ℤ) : ℂ) = 0
    simp
  map_add' a b := ContMDiffMap.ext fun _ => by
    change ((a + b : ℤ) : ℂ) = a + b
    simp

/-- The inclusion of the constant presheaf `ℤ` into `𝒪_M`. -/
noncomputable def intConstToHolomorphic :
    (Functor.const (Opens (TopCat.of M))ᵒᵖ).obj (AddCommGrpCat.of ℤ) ⟶
      (holomorphicSheafAb I M).obj where
  app U := AddCommGrpCat.ofHom (intConstSections (unop U))
  naturality _ _ _ := rfl

/-- The morphism `ℤ_M ⟶ 𝒪_M` from the constant sheaf `ℤ`. -/
noncomputable def intToHolomorphic :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of ℤ) ⟶ holomorphicSheafAb I M :=
  TopCat.Sheaf.constantSheafLift intConstToHolomorphic

/-- The constant sections with value in `ℂˣ`. -/
noncomputable def unitsConstSections (U : Opens M) :
    Additive ℂˣ →+ Additive C^∞⟮I, U; 𝓘(ℂ), ℂˣ⟯ where
  toFun a := Additive.ofMul (ContMDiffMap.const a.toMul)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The open subset of `M` underlying an open subset of an open subset `U` of `M`. -/
def opensOfSubtype (U : Opens M) (S : Set U) (hS : IsOpen S) : Opens M :=
  ⟨Subtype.val '' S, U.isOpen.isOpenMap_subtype_val S hS⟩

lemma opensOfSubtype_le (U : Opens M) (S : Set U) (hS : IsOpen S) : opensOfSubtype U S hS ≤ U := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

lemma mem_opensOfSubtype {U : Opens M} {S : Set U} {hS : IsOpen S} {y : U} (hy : y ∈ S) :
    (y : M) ∈ opensOfSubtype U S hS :=
  ⟨y, hy, rfl⟩

lemma of_mem_opensOfSubtype {U : Opens M} {S : Set U} {hS : IsOpen S} {y : M}
    (hy : y ∈ opensOfSubtype U S hS) : (⟨y, opensOfSubtype_le U S hS hy⟩ : U) ∈ S := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact hy'

/-- The local logarithm `z ↦ log (z / c₀) + log c₀`, divided by `c`, is holomorphic where
`z / c₀` lies in the slit plane. -/
lemma contDiffAt_logDiv {n : ℕ∞ω} {c₀ c z : ℂ} (h : z / c₀ ∈ slitPlane) :
    ContDiffAt ℂ n (fun z => (log (z / c₀) + log c₀) / c) z :=
  (((contDiffAt_log h).comp z (contDiffAt_id.div_const c₀)).add contDiffAt_const).div_const c

variable (I) in
/-- Local logarithms: `f ↦ exp (c * f)` is locally surjective for `c ≠ 0`. -/
theorem isLocallySurjective_expMap {c : ℂ} (hc : c ≠ 0) :
    TopCat.Presheaf.IsLocallySurjective (expMap (I := I) (M := M) c).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  let u : C^∞⟮I, U; 𝓘(ℂ), ℂˣ⟯ := Additive.toMul t
  let x₀ : U := ⟨x, hx⟩
  let c₀ : ℂ := u x₀
  have hc₀ : c₀ ≠ 0 := (u x₀).ne_zero
  have hcont : Continuous fun y : U => (u y : ℂ) / c₀ :=
    (Units.continuous_val.comp u.2.continuous).div_const c₀
  let S : Set U := (fun y : U => (u y : ℂ) / c₀) ⁻¹' slitPlane
  have hS : IsOpen S := isOpen_slitPlane.preimage hcont
  let V := opensOfSubtype U S hS
  have hVU : V ≤ U := opensOfSubtype_le U S hS
  have hxV : x ∈ V := mem_opensOfSubtype (y := x₀) (by
    change (u x₀ : ℂ) / c₀ ∈ slitPlane
    rw [div_self hc₀]
    exact one_mem_slitPlane)
  let u' : C^∞⟮I, V; 𝓘(ℂ), ℂˣ⟯ :=
    Additive.toMul ((holomorphicUnitsSheaf I M).obj.map (homOfLE hVU).op t)
  have hu' : ∀ y : V, u' y = u ⟨y, hVU y.2⟩ := fun _ => rfl
  have hmem : ∀ y : V, (u' y : ℂ) / c₀ ∈ slitPlane := fun y => by
    rw [hu']
    exact of_mem_opensOfSubtype y.2
  let g : ℂ → ℂ := fun z => (log (z / c₀) + log c₀) / c
  have hg : ∀ y : V, ContDiffAt ℂ ∞ g (u' y) := fun y => contDiffAt_logDiv (hmem y)
  let f : C^∞⟮I, V; 𝓘(ℂ), ℂ⟯ :=
    ⟨fun y => g (u' y), fun y =>
      (hg y).comp_contMDiffAt (f := fun y : V => (u' y : ℂ))
        ((Units.contMDiff_val.comp u'.2) y)⟩
  refine ⟨V, hVU, ⟨f, ?_⟩, hxV⟩
  apply Additive.toMul.injective
  refine ContMDiffMap.ext fun y => Units.ext ?_
  change cexp (c * ((log ((u' y : ℂ) / c₀) + log c₀) / c)) = (u' y : ℂ)
  rw [mul_div_cancel₀ _ hc, Complex.exp_add, Complex.exp_log (div_ne_zero (u' y).ne_zero hc₀),
    Complex.exp_log hc₀, div_mul_cancel₀ _ hc₀]

/-- The exponential map `𝒪_M ⟶ 𝒪_M^×`, `f ↦ exp (2πi f)`. -/
noncomputable abbrev exponentialMap : holomorphicSheafAb I M ⟶ holomorphicUnitsSheaf I M :=
  expMap (2 * Real.pi * Complex.I)

/-- `exp (2πi k) = 1` for integers `k`. -/
lemma intConstToHolomorphic_comp_exponentialMap :
    intConstToHolomorphic ≫ (exponentialMap (I := I) (M := M)).hom = 0 := by
  ext U k : 4
  apply Additive.toMul.injective
  refine ContMDiffMap.ext fun x => Units.ext ?_
  change cexp (2 * Real.pi * Complex.I * ((show ℤ from k) : ℂ)) = 1
  rw [mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma intToHolomorphic_comp_exponentialMap :
    intToHolomorphic ≫ exponentialMap (I := I) (M := M) = 0 :=
  TopCat.Sheaf.constantSheafLift_comp_eq_zero _ _ intConstToHolomorphic_comp_exponentialMap

variable (I M) in
/-- The exponential sequence `0 ⟶ ℤ_M ⟶ 𝒪_M ⟶ 𝒪_M^× ⟶ 0`. -/
noncomputable def exponentialSequence :
    ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}) :=
  ShortComplex.mk _ _ (intToHolomorphic_comp_exponentialMap (I := I) (M := M))

variable (I M) in
/-- The exponential sequence `0 ⟶ ℤ_M ⟶ 𝒪_M ⟶ 𝒪_M^× ⟶ 0` is short exact. -/
theorem exponentialSequence_shortExact : (exponentialSequence I M).ShortExact := by
  refine TopCat.Sheaf.shortExact_of_constantSheafLift _ _ ?_
    intConstToHolomorphic_comp_exponentialMap ?_ (isLocallySurjective_expMap I two_pi_I_ne_zero)
  · rintro U ⟨y, hy⟩ a b hab
    have h : ((show ℤ from a : ℤ) : ℂ) = ((show ℤ from b : ℤ) : ℂ) :=
      congrArg (fun f : C^∞⟮I, U; 𝓘(ℂ), ℂ⟯ => f ⟨y, hy⟩) hab
    exact Int.cast_injective h
  · intro U s₀ hs x hx
    let s : C^∞⟮I, U; 𝓘(ℂ), ℂ⟯ := s₀
    have hint : ∀ y : U, ∃ k : ℤ, s y = k := fun y => by
      have h1 : cexp (2 * Real.pi * Complex.I * s y) = 1 :=
        congrArg (fun t : Additive C^∞⟮I, U; 𝓘(ℂ), ℂˣ⟯ => ((Additive.toMul t y : ℂˣ) : ℂ)) hs
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
      refine ⟨k, ?_⟩
      have := two_pi_I_ne_zero
      rw [mul_comm] at hk
      exact mul_right_cancel₀ this hk
    let x₀ : U := ⟨x, hx⟩
    obtain ⟨k₀, hk₀⟩ := hint x₀
    let S : Set U := (fun y : U => s y) ⁻¹' Metric.ball (s x₀) 1
    have hS : IsOpen S := Metric.isOpen_ball.preimage s.contMDiff.continuous
    let V := opensOfSubtype U S hS
    have hVU : V ≤ U := opensOfSubtype_le U S hS
    refine ⟨V, hVU, mem_opensOfSubtype (y := x₀) (Metric.mem_ball_self one_pos), k₀, ?_⟩
    refine ContMDiffMap.ext fun y => ?_
    change (k₀ : ℂ) = s ⟨y, hVU y.2⟩
    have hy : dist (s ⟨y, hVU y.2⟩) (s x₀) < 1 := of_mem_opensOfSubtype (hS := hS) y.2
    obtain ⟨k, hk⟩ := hint ⟨y, hVU y.2⟩
    rw [hk, hk₀, dist_eq_norm, ← Int.cast_sub, Complex.norm_intCast] at hy
    have : k - k₀ = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hy)
    rw [hk, sub_eq_zero.mp this]

section Kummer

variable (n : ℕ) [NeZero n]

/-- The primitive `n`-th root of unity `exp (2πi / n)`, as a unit. -/
noncomputable def primitiveRootUnit : ℂˣ := expUnits (2 * Real.pi * Complex.I / n)

lemma isPrimitiveRoot_primitiveRootUnit : IsPrimitiveRoot (primitiveRootUnit n) n :=
  IsPrimitiveRoot.coe_units_iff.mp (Complex.isPrimitiveRoot_exp n (NeZero.ne n))

/-- `ZMod n ≅ μ_n(ℂ)`, `k ↦ exp (2πik/n)`, as an additive map into `ℂˣ`. -/
noncomputable def zmodToUnits : ZMod n →+ Additive ℂˣ :=
  (Subgroup.zpowers (primitiveRootUnit n)).subtype.toAdditive.comp
    (isPrimitiveRoot_primitiveRootUnit n).zmodEquivZPowers.toAddMonoidHom

lemma zmodToUnits_injective : Function.Injective (zmodToUnits n) :=
  Subtype.val_injective.comp (isPrimitiveRoot_primitiveRootUnit n).zmodEquivZPowers.injective

/-- The image of `zmodToUnits n` consists of `n`-th roots of unity. -/
lemma zmodToUnits_pow (a : ZMod n) : (zmodToUnits n a).toMul ^ n = 1 := by
  have h := ((isPrimitiveRoot_primitiveRootUnit n).zpowers_eq).le
    ((isPrimitiveRoot_primitiveRootUnit n).zmodEquivZPowers a).toMul.2
  exact (_root_.mem_rootsOfUnity _ _).mp h

/-- Every `n`-th root of unity is in the image of `zmodToUnits n`. -/
lemma exists_zmodToUnits_eq {z : ℂˣ} (hz : z ^ n = 1) :
    ∃ a : ZMod n, (zmodToUnits n a).toMul = z := by
  have hmem : z ∈ Subgroup.zpowers (primitiveRootUnit n) := by
    rw [(isPrimitiveRoot_primitiveRootUnit n).zpowers_eq]
    exact (_root_.mem_rootsOfUnity _ _).mpr hz
  refine ⟨(isPrimitiveRoot_primitiveRootUnit n).zmodEquivZPowers.symm
    (Additive.ofMul ⟨z, hmem⟩), ?_⟩
  simp [zmodToUnits]

variable {n}

/-- The inclusion of the constant presheaf `ZMod n` into `𝒪_M^×` as the `n`-th roots of unity. -/
noncomputable def zmodConstToUnits :
    (Functor.const (Opens (TopCat.of M))ᵒᵖ).obj (AddCommGrpCat.of (ZMod n)) ⟶
      (holomorphicUnitsSheaf I M).obj where
  app U := AddCommGrpCat.ofHom ((unitsConstSections (unop U)).comp (zmodToUnits n))
  naturality _ _ _ := rfl

variable (n) in
/-- The morphism `ℤ/n ⟶ 𝒪_M^×` from the constant sheaf, with image the `n`-th roots of unity. -/
noncomputable def zmodToHolomorphicUnits :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod n)) ⟶ holomorphicUnitsSheaf I M :=
  TopCat.Sheaf.constantSheafLift zmodConstToUnits

lemma zmodConstToUnits_comp_powMap :
    zmodConstToUnits (n := n) ≫ (powMap (I := I) (M := M) n).hom = 0 := by
  ext U a : 4
  apply Additive.toMul.injective
  refine ContMDiffMap.ext fun x => ?_
  exact zmodToUnits_pow n (show ZMod n from a)

lemma zmodToHolomorphicUnits_comp_powMap :
    zmodToHolomorphicUnits n ≫ powMap (I := I) (M := M) n = 0 :=
  TopCat.Sheaf.constantSheafLift_comp_eq_zero _ _ zmodConstToUnits_comp_powMap

/-- `exp (c f / n)ⁿ = exp (c f)`. -/
lemma expMap_div_comp_powMap (c : ℂ) :
    (expMap (I := I) (M := M) (c / n)).hom ≫ (powMap n).hom = (expMap c).hom := by
  ext U f : 4
  apply Additive.toMul.injective
  refine ContMDiffMap.ext fun x => Units.ext ?_
  change cexp (c / n * (show C^∞⟮I, (unop U : Opens M); 𝓘(ℂ), ℂ⟯ from f) x) ^ n =
    cexp (c * (show C^∞⟮I, (unop U : Opens M); 𝓘(ℂ), ℂ⟯ from f) x)
  rw [← Complex.exp_nat_mul, ← mul_assoc, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne n))]

variable (I) in
/-- Local `n`-th roots: `u ↦ uⁿ` is locally surjective on `𝒪_M^×`. -/
theorem isLocallySurjective_powMap :
    TopCat.Presheaf.IsLocallySurjective (powMap (I := I) (M := M) n).hom := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of M))
      (expMap (I := I) (M := M) (2 * Real.pi * Complex.I)).hom :=
    isLocallySurjective_expMap (M := M) I Complex.two_pi_I_ne_zero
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (expMap_div_comp_powMap (2 * Real.pi * Complex.I))

variable (I M n) in
/-- The Kummer sequence `0 ⟶ ℤ/n ⟶ 𝒪_M^× ⟶ 𝒪_M^× ⟶ 0`, the second map being `u ↦ uⁿ`. -/
noncomputable def kummerSequence :
    ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}) :=
  ShortComplex.mk _ _ (zmodToHolomorphicUnits_comp_powMap (I := I) (M := M) (n := n))

variable (I M n) in
/-- The Kummer sequence `0 ⟶ ℤ/n ⟶ 𝒪_M^× ⟶ 𝒪_M^× ⟶ 0` is short exact. -/
theorem kummerSequence_shortExact : (kummerSequence I M n).ShortExact := by
  refine TopCat.Sheaf.shortExact_of_constantSheafLift _ _ ?_
    zmodConstToUnits_comp_powMap ?_ (isLocallySurjective_powMap I)
  · rintro U ⟨y, hy⟩ a b hab
    have h : (zmodToUnits n (show ZMod n from a)).toMul =
        (zmodToUnits n (show ZMod n from b)).toMul :=
      congrArg (fun f : Additive C^∞⟮I, U; 𝓘(ℂ), ℂˣ⟯ => (Additive.toMul f) ⟨y, hy⟩) hab
    exact zmodToUnits_injective n (Additive.toMul.injective h)
  · intro U t hs x hx
    let u : C^∞⟮I, U; 𝓘(ℂ), ℂˣ⟯ := Additive.toMul t
    have hpow : ∀ y : U, u y ^ n = 1 := fun y =>
      congrArg (fun t : Additive C^∞⟮I, U; 𝓘(ℂ), ℂˣ⟯ => (Additive.toMul t y : ℂˣ)) hs
    let v : U → rootsOfUnity n ℂ := fun y => ⟨u y, (_root_.mem_rootsOfUnity _ _).mpr (hpow y)⟩
    have hv : Continuous v := (Continuous.subtype_mk u.2.continuous _)
    have hlc : IsLocallyConstant v := (IsLocallyConstant.iff_continuous v).mpr hv
    let x₀ : U := ⟨x, hx⟩
    let S : Set U := {y | v y = v x₀}
    have hS : IsOpen S := hlc.isOpen_fiber _
    let V := opensOfSubtype U S hS
    have hVU : V ≤ U := opensOfSubtype_le U S hS
    obtain ⟨a, ha⟩ := exists_zmodToUnits_eq n (hpow x₀)
    refine ⟨V, hVU, mem_opensOfSubtype (y := x₀) rfl, a, ?_⟩
    apply Additive.toMul.injective
    refine ContMDiffMap.ext fun y => ?_
    change (zmodToUnits n a).toMul = u ⟨y, hVU y.2⟩
    have hy : v ⟨y, hVU y.2⟩ = v x₀ := of_mem_opensOfSubtype (hS := hS) y.2
    rw [ha]
    exact (congrArg Subtype.val hy).symm

variable (I M n)

/-- The sheaf `μ_n` of `n`-th roots of unity in `𝒪_M^×`: the kernel of `u ↦ uⁿ`. -/
noncomputable abbrev rootsOfUnitySheaf :
    Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0} :=
  kernel (powMap (I := I) (M := M) n)

/-- The Kummer sequence `0 ⟶ μ_n ⟶ 𝒪_M^× ⟶ 𝒪_M^× ⟶ 0` with `μ_n` the kernel of `u ↦ uⁿ`. -/
noncomputable def kummerSequenceRootsOfUnity :
    ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}) :=
  ShortComplex.mk (kernel.ι (powMap (I := I) (M := M) n)) _ (kernel.condition _)

/-- The Kummer sequence `0 ⟶ μ_n ⟶ 𝒪_M^× ⟶ 𝒪_M^× ⟶ 0` is short exact. -/
theorem kummerSequenceRootsOfUnity_shortExact :
    (kummerSequenceRootsOfUnity I M n).ShortExact := by
  have : Epi (powMap (I := I) (M := M) n) := (kummerSequence_shortExact I M n).epi_g
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    (Fork.IsLimit.mono (limit.isLimit _)) this

/-- The sheaf of `n`-th roots of unity is the constant sheaf `ℤ/n`
(a primitive root of unity being `exp (2πi / n)`). -/
noncomputable def constantSheafZModIsoRootsOfUnitySheaf :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod n)) ≅ rootsOfUnitySheaf I M n :=
  have := (kummerSequence_shortExact I M n).mono_f
  IsLimit.conePointUniqueUpToIso (kummerSequence_shortExact I M n).exact.fIsKernel
    (limit.isLimit _)

/-- The isomorphism `ℤ/n ≅ μ_n` is compatible with the maps into `𝒪_M^×`. -/
@[reassoc (attr := simp)]
lemma constantSheafZModIsoRootsOfUnitySheaf_hom_ι :
    (constantSheafZModIsoRootsOfUnitySheaf I M n).hom ≫ kernel.ι (powMap n) =
      zmodToHolomorphicUnits n :=
  have := (kummerSequence_shortExact I M n).mono_f
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

end Kummer

end ComplexManifold
