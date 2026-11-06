module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Cech.CechCohomologyOfAnObject
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TorsorClasses

/-!
# Torsors under a constant sheaf and the first Čech cohomology

Let `S` be a noetherian separated scheme, `Et(S)` its étale category of noetherian separated
étale `S`-schemes, `A` an abelian group and `F_S` the constant sheaf of locally constant
`A`-valued maps. An `F_S`-torsor is a sheaf of sets `𝒢` on `Et(S)` with a simply transitive
action of `F_S` which has sections over the members of some étale covering of `S`. This file
proves that the isomorphism classes of `F_S`-torsors are in bijection with the Čech cohomology
group `Ȟ¹(S, F_S)`, by the class `κ[𝒢] = [σ]_𝔙` of the transition cocycle `σ` of sections
`t_l ∈ 𝒢(V_l)` over a covering `𝔙 = (V_l → S)_l`, defined by `t_l ^ σ_{lm} = t_m` on
`V_l ×_S V_m`.

The class does not depend on the covering or the sections, since two choices become comparable
on a common refinement, where the transition cocycles differ by a coboundary. Torsors with the
same class have the same transition cocycle on one covering, after changing the sections, and
are then isomorphic by gluing. Conversely a cocycle `σ` on `𝔙` is the transition cocycle of the
torsor whose sections over `W` are the families `k_l ∈ F_S(W ×_S V_l)` with `k_l = k_m + σ_{lm}`
on `W ×_S V_l ×_S V_m`.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.constantGroupSheaf`: the constant sheaf of
  groups `F_S`, written multiplicatively.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.transitionCochain`: the transition cochain
  of sections of a torsor over the members of a covering.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.torsorCechClass`: the Čech class `κ[𝒢]`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.glueHom`: the morphism of torsors with the
  same transition data.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cocycleTorsor`: the torsor of a cocycle.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechClass_transitionCycle_eq`: the class of
  the transition cocycle is independent of the choices.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.nonempty_hom_of_torsorCechClass_eq`:
  injectivity of `κ`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.exists_torsorCechClass_eq`: surjectivity.
* `SmallNoetherianSeparatedEtale.exists_torsorClasses_equiv_cechCohomologyOfObject`:
  the bijection `κ` between torsor classes and `Ȟ¹(S, F_S)` with `κ[𝒢] = [σ]_𝔙`.

## Implementation notes

Torsors are the pseudo torsors of Stacks, Tag 03AH, with their left action; the right action of
the statement is `t ^ σ = σ⁻¹ • t` (`PseudoTorsor.toRightAction`), and since `F_S` is abelian
both describe the same torsors. Isomorphism classes are `SheafOfGroups.TorsorClasses`, for
torsors whose sets of sections lie in the universe of `F_S`. A torsor is required to be locally
nonempty on every object (Stacks); over the final object `S` this is the same as having sections
over the members of one covering of `S`. The fibre product `V_l ×_S V_m` of the statement is the
twofold product of the Čech complex, over the final object `(S, id)`, which requires `S` to be
separated, as for `Ȟ¹(S, F_S)` itself.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a w u

namespace PseudoTorsor

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {G : SheafOfGroups J}
  (T : PseudoTorsor G)

/-- The difference `δ(s, t)` of two sections of a pseudo torsor: the unique section `g` of `G`
with `g • s = t`. -/
noncomputable def diff {U : Cᵒᵖ} (s t : T.presheaf.obj U) : G.presheaf.obj U :=
  (T.simplyTransitive U ⟨s⟩ s t).exists.choose

lemma diff_act {U : Cᵒᵖ} (s t : T.presheaf.obj U) : T.act U (T.diff s t) s = t :=
  (T.simplyTransitive U ⟨s⟩ s t).exists.choose_spec

lemma eq_diff {U : Cᵒᵖ} {s t : T.presheaf.obj U} {g : G.presheaf.obj U}
    (h : T.act U g s = t) : g = T.diff s t :=
  (T.simplyTransitive U ⟨s⟩ s t).unique h (T.diff_act s t)

lemma diff_self {U : Cᵒᵖ} (s : T.presheaf.obj U) : T.diff s s = 1 :=
  (T.eq_diff (T.one_act U s)).symm

lemma diff_mul_diff {U : Cᵒᵖ} (r s t : T.presheaf.obj U) :
    T.diff s t * T.diff r s = T.diff r t :=
  T.eq_diff (by rw [T.mul_act, T.diff_act, T.diff_act])

lemma diff_act_right {U : Cᵒᵖ} (s t : T.presheaf.obj U) (g : G.presheaf.obj U) :
    T.diff s (T.act U g t) = g * T.diff s t :=
  (T.eq_diff (by rw [T.mul_act, T.diff_act])).symm

lemma diff_comm {U : Cᵒᵖ} (s t : T.presheaf.obj U) : T.diff t s = (T.diff s t)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [T.diff_mul_diff, T.diff_self])

lemma map_diff {U V : Cᵒᵖ} (f : U ⟶ V) (s t : T.presheaf.obj U) :
    G.presheaf.map f (T.diff s t) = T.diff (T.presheaf.map f s) (T.presheaf.map f t) :=
  T.eq_diff (by rw [← T.naturality, T.diff_act])

lemma diff_hom {T' : PseudoTorsor G} (e : T.Hom T') {U : Cᵒᵖ} (s t : T.presheaf.obj U) :
    T'.diff (e.hom.app U s) (e.hom.app U t) = T.diff s t :=
  (T'.eq_diff (by rw [← e.map_act, T.diff_act])).symm

end PseudoTorsor

namespace CategoryTheory.Presheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type*}

/-- Sections of a sheaf of sets agreeing on a covering sieve are equal. -/
lemma IsSheaf.ext_of_mem (hP : Presheaf.IsSheaf J P) {W : C} {R : Sieve W} (hR : R ∈ J W)
    {a b : P.obj (op W)}
    (h : ∀ ⦃V : C⦄ (g : V ⟶ W), R g → P.map g.op a = P.map g.op b) : a = b := by
  have hsh := ((isSheaf_iff_isSheaf_of_type J P).mp hP) R hR
  exact hsh.isSeparatedFor.ext h

/-- A compatible family of sections of a sheaf of sets on a covering sieve glues. -/
lemma IsSheaf.exists_of_mem (hP : Presheaf.IsSheaf J P) {W : C} {R : Sieve W} (hR : R ∈ J W)
    (y : ∀ ⦃V : C⦄ (g : V ⟶ W), R g → P.obj (op V))
    (hy : ∀ ⦃V V' : C⦄ (g : V ⟶ W) (e : V' ⟶ V) (hg : R g),
      y (e ≫ g) (R.downward_closed hg e) = P.map e.op (y g hg)) :
    ∃ z : P.obj (op W), ∀ ⦃V : C⦄ (g : V ⟶ W) (hg : R g), P.map g.op z = y g hg := by
  have hsh := ((isSheaf_iff_isSheaf_of_type J P).mp hP) R hR
  let x : Presieve.FamilyOfElements P R.arrows := fun V g hg ↦ y g hg
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V V' g e hg
    exact hy g e hg
  obtain ⟨z, hz, -⟩ := hsh x hx
  exact ⟨z, fun V g hg ↦ hz g hg⟩

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Restriction of a locally constant map along a morphism of `Et(S)`. -/
def lcRes {V W : SmallNoetherianSeparatedEtale B S hS} (g : V ⟶ W) {A : Type w}
    (k : LocallyConstant ((toScheme B S hS).obj W) A) :
    LocallyConstant ((toScheme B S hS).obj V) A :=
  k.comap ((toScheme B S hS).map g).base.hom

@[simp]
lemma lcRes_apply {V W : SmallNoetherianSeparatedEtale B S hS} (g : V ⟶ W) {A : Type w}
    (k : LocallyConstant ((toScheme B S hS).obj W) A) (x : (toScheme B S hS).obj V) :
    lcRes g k x = k (((toScheme B S hS).map g).base x) :=
  rfl

lemma lcRes_comp {V W Y : SmallNoetherianSeparatedEtale B S hS} (e : V ⟶ W) (g : W ⟶ Y)
    {A : Type w} (k : LocallyConstant ((toScheme B S hS).obj Y) A) :
    lcRes (e ≫ g) k = lcRes e (lcRes g k) := by
  ext x
  rw [lcRes_apply, lcRes_apply, lcRes_apply, Functor.map_comp]
  rfl

lemma lcRes_id {V : SmallNoetherianSeparatedEtale B S hS} {A : Type w}
    (k : LocallyConstant ((toScheme B S hS).obj V) A) : lcRes (𝟙 V) k = k := by
  ext x
  rw [lcRes_apply, CategoryTheory.Functor.map_id]
  rfl

lemma lcRes_sub {V W : SmallNoetherianSeparatedEtale B S hS} (g : V ⟶ W) {A : Type w}
    [AddCommGroup A] (k l : LocallyConstant ((toScheme B S hS).obj W) A) :
    lcRes g (k - l) = lcRes g k - lcRes g l :=
  rfl

lemma lcRes_zero {V W : SmallNoetherianSeparatedEtale B S hS} (g : V ⟶ W) {A : Type w}
    [AddCommGroup A] : lcRes g (0 : LocallyConstant ((toScheme B S hS).obj W) A) = 0 :=
  rfl

lemma lcRes_add {V W : SmallNoetherianSeparatedEtale B S hS} (g : V ⟶ W) {A : Type w}
    [AddCommGroup A] (k l : LocallyConstant ((toScheme B S hS).obj W) A) :
    lcRes g (k + l) = lcRes g k + lcRes g l :=
  rfl


section Sheaf

variable [IsLocallyNoetherian S]

/-- Locally constant maps are determined on a covering sieve. -/
lemma lcRes_injective_of_mem {A : Type w} {W : SmallNoetherianSeparatedEtale B S hS}
    {R : Sieve W} (hR : R ∈ topology B S hS W)
    {a b : LocallyConstant ((toScheme B S hS).obj W) A}
    (h : ∀ ⦃V : SmallNoetherianSeparatedEtale B S hS⦄ (g : V ⟶ W), R g → lcRes g a = lcRes g b) :
    a = b := by
  ext x
  obtain ⟨V, f, hf, y, rfl⟩ := (mem_topology_iff B S hS R).mp hR x
  exact congrArg (fun k ↦ k y) (h f hf)

/-- Locally constant maps glue along a covering sieve. -/
lemma exists_lcRes_eq_of_mem {A : Type w} {W : SmallNoetherianSeparatedEtale B S hS}
    {R : Sieve W} (hR : R ∈ topology B S hS W)
    (y : ∀ ⦃V : SmallNoetherianSeparatedEtale B S hS⦄ (g : V ⟶ W), R g →
      LocallyConstant ((toScheme B S hS).obj V) A)
    (hy : ∀ ⦃V V' : SmallNoetherianSeparatedEtale B S hS⦄ (g : V ⟶ W) (e : V' ⟶ V) (hg : R g),
      y (e ≫ g) (R.downward_closed hg e) = lcRes e (y g hg)) :
    ∃ z : LocallyConstant ((toScheme B S hS).obj W) A,
      ∀ ⦃V : SmallNoetherianSeparatedEtale B S hS⦄ (g : V ⟶ W) (hg : R g), lcRes g z = y g hg := by
  have hsh := locallyConstantPresheaf_isSheafFor A R.arrows (fun x ↦ by
    obtain ⟨V, f, hf, hx⟩ := (mem_topology_iff B S hS R).mp hR x
    exact ⟨V, f, hf, hx⟩)
  let x : Presieve.FamilyOfElements (locallyConstantPresheaf B S hS A) R.arrows :=
    fun V g hg ↦ y g hg
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V V' g e hg
    exact hy g e hg
  obtain ⟨z, hz, -⟩ := hsh x hx
  exact ⟨z, fun V g hg ↦ hz g hg⟩

end Sheaf


section Final

variable [IsNoetherian S] [S.IsSeparated]

/-- The morphism from an object of `Et(S)` to the final object `(S, id)`. -/
noncomputable def toFinal (V : SmallNoetherianSeparatedEtale B S hS) : V ⟶ final B S hS :=
  (finalIsTerminal B S hS).from V

lemma hom_ext_final {V : SmallNoetherianSeparatedEtale B S hS} (f g : V ⟶ final B S hS) :
    f = g :=
  (finalIsTerminal B S hS).hom_ext f g

/-- The morphism into a product `∏ Y_j` of objects over the final object given by morphisms
into the factors. -/
noncomputable def ovLift {ι : Type*} (Y : ι → Over (final B S hS)) [HasProduct Y]
    {T : SmallNoetherianSeparatedEtale B S hS} (h : ∀ j, T ⟶ (Y j).left) : T ⟶ (∏ᶜ Y).left :=
  (Pi.lift (fun j ↦ (Over.homMk (h j) (hom_ext_final _ _) : Over.mk (toFinal T) ⟶ Y j))).left

@[reassoc (attr := simp)]
lemma ovLift_π {ι : Type*} (Y : ι → Over (final B S hS)) [HasProduct Y]
    {T : SmallNoetherianSeparatedEtale B S hS} (h : ∀ j, T ⟶ (Y j).left) (j : ι) :
    ovLift Y h ≫ (Pi.π Y j).left = h j := by
  rw [ovLift, ← Over.comp_left, Pi.lift_π]
  rfl

lemma ovLift_ext {ι : Type*} {Y : ι → Over (final B S hS)} [HasProduct Y]
    {T : SmallNoetherianSeparatedEtale B S hS} {g g' : T ⟶ (∏ᶜ Y).left}
    (h : ∀ j, g ≫ (Pi.π Y j).left = g' ≫ (Pi.π Y j).left) : g = g' := by
  have := Pi.hom_ext (Over.homMk g (hom_ext_final _ _) : Over.mk (toFinal T) ⟶ ∏ᶜ Y)
    (Over.homMk g' (hom_ext_final _ _)) (fun j ↦ Over.OverMorphism.ext (by simpa using h j))
  exact congrArg CommaMorphism.left this

lemma eq_ovLift {ι : Type*} {Y : ι → Over (final B S hS)} [HasProduct Y]
    {T : SmallNoetherianSeparatedEtale B S hS} (g : T ⟶ (∏ᶜ Y).left) :
    g = ovLift Y (fun j ↦ g ≫ (Pi.π Y j).left) :=
  ovLift_ext fun j ↦ by simp

lemma comp_ovLift {ι : Type*} {Y : ι → Over (final B S hS)} [HasProduct Y]
    {T T' : SmallNoetherianSeparatedEtale B S hS} (e : T' ⟶ T) (h : ∀ j, T ⟶ (Y j).left) :
    e ≫ ovLift Y h = ovLift Y (fun j ↦ e ≫ h j) :=
  ovLift_ext fun j ↦ by simp

/-- Points of `W` and `V` with the same image in `S` come from a point of `W ×_S V`. -/
lemma exists_pullback_toFinal_point {W V : SmallNoetherianSeparatedEtale B S hS}
    (w : (toScheme B S hS).obj W) (v : (toScheme B S hS).obj V)
    (h : ((toScheme B S hS).map (toFinal W)).base w = ((toScheme B S hS).map (toFinal V)).base v) :
    ∃ p : (toScheme B S hS).obj (pullback (toFinal W) (toFinal V)),
      ((toScheme B S hS).map (pullback.fst _ _)).base p = w ∧
        ((toScheme B S hS).map (pullback.snd _ _)).base p = v := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback w v h
  refine ⟨(PreservesPullback.iso (toScheme B S hS) (toFinal W) (toFinal V)).inv.base z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_fst]
    exact hz1
  · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_snd]
    exact hz2

end Final

section Constant

variable [IsLocallyNoetherian S] (A : Type w) [AddCommGroup A]

variable (B S hS) in
/-- The constant sheaf of groups `F_S` of an additive group `A`, written multiplicatively. -/
abbrev constantGroupSheaf :
    SheafOfGroups.{max u w} (C := SmallNoetherianSeparatedEtale B S hS) (topology B S hS) :=
  locallyConstantSheafOfGroups B S hS (Multiplicative A)

variable {A}

/-- Sections of `constantGroupSheaf` are locally constant `A`-valued maps. -/
def toAddSection {V : SmallNoetherianSeparatedEtale B S hS} :
    (constantGroupSheaf B S hS A).presheaf.obj (op V) ≃
      LocallyConstant ((toScheme B S hS).obj V) A :=
  Equiv.refl _

@[simp]
lemma toAddSection_mul {V : SmallNoetherianSeparatedEtale B S hS}
    (a b : (constantGroupSheaf B S hS A).presheaf.obj (op V)) :
    toAddSection (a * b) = toAddSection a + toAddSection b :=
  rfl

@[simp]
lemma toAddSection_one {V : SmallNoetherianSeparatedEtale B S hS} :
    toAddSection (1 : (constantGroupSheaf B S hS A).presheaf.obj (op V)) = 0 :=
  rfl

@[simp]
lemma toAddSection_inv {V : SmallNoetherianSeparatedEtale B S hS}
    (a : (constantGroupSheaf B S hS A).presheaf.obj (op V)) :
    toAddSection a⁻¹ = - toAddSection a :=
  rfl

@[simp]
lemma toAddSection_map {V W : SmallNoetherianSeparatedEtale B S hS} (g : V ⟶ W)
    (a : (constantGroupSheaf B S hS A).presheaf.obj (op W)) :
    toAddSection ((constantGroupSheaf B S hS A).presheaf.map g.op a) = lcRes g (toAddSection a) :=
  rfl

omit [IsLocallyNoetherian S] in
lemma locallyConstantPresheafAb_map_eq {V W : SmallNoetherianSeparatedEtale B S hS} (g : V ⟶ W)
    (k : (locallyConstantPresheafAb B S hS A).obj (op W)) :
    (locallyConstantPresheafAb B S hS A).map g.op k =
      lcRes g (show LocallyConstant ((toScheme B S hS).obj W) A from k) :=
  rfl

lemma constantGroupSheaf_mul_comm {V : SmallNoetherianSeparatedEtale B S hS}
    (a b : (constantGroupSheaf B S hS A).presheaf.obj (op V)) : a * b = b * a :=
  toAddSection.injective (by rw [toAddSection_mul, toAddSection_mul, add_comm])

end Constant

section Cochain

variable [IsNoetherian S] [S.IsSeparated] {A : Type w} [AddCommGroup A]

variable (T : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A))
  (E : PreZeroHypercover.{0} (final B S hS))

/-- The section `t_{ν_j}` restricted to `V_{ν_0} ×_S ⋯ ×_S V_{ν_p}`. -/
noncomputable abbrev restrictToProduct {p : ℕ} (t : ∀ l, T.presheaf.obj (op (E.X l)))
    (ν : Fin (p + 1) → E.I₀) (j : Fin (p + 1)) :
    T.presheaf.obj (op (∏ᶜ (fun a ↦ Over.mk (E.f (ν a)))).left) :=
  T.presheaf.map (Pi.π (fun a ↦ Over.mk (E.f (ν a))) j).left.op (t (ν j))

/-- **The transition cochain** of sections `t_l ∈ 𝒢(V_l)`: over `V_l ×_S V_m` the section
`σ_{lm}` of `F_S` with `t_l = σ_{lm} • t_m` (so that `t_l ^ σ_{lm} = t_m` for the right
action). -/
noncomputable def transitionCochain (t : ∀ l, T.presheaf.obj (op (E.X l))) :
    Stacks.CechSite.cechCochain E (locallyConstantPresheafAb B S hS A) 1 :=
  fun ν ↦ toAddSection (T.diff (restrictToProduct T E t ν 1) (restrictToProduct T E t ν 0))

lemma lcRes_transitionCochain (t : ∀ l, T.presheaf.obj (op (E.X l))) (ν : Fin 2 → E.I₀)
    {P : SmallNoetherianSeparatedEtale B S hS}
    (g : P ⟶ (∏ᶜ (fun a ↦ Over.mk (E.f (ν a)))).left) :
    lcRes g (transitionCochain T E t ν) = toAddSection (T.diff
      (T.presheaf.map (g ≫ (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 1).left).op (t (ν 1)))
      (T.presheaf.map (g ≫ (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 0).left).op (t (ν 0)))) := by
  rw [transitionCochain, ← toAddSection_map, T.map_diff, op_comp, op_comp,
    Functor.map_comp_apply, Functor.map_comp_apply]

lemma faceProjection_left_π {n : ℕ} (k : Fin (n + 2) → E.I₀) (j : Fin (n + 2)) (b : Fin (n + 1)) :
    (Stacks.CechSite.faceProjection E k j).left ≫
        (Pi.π (fun c ↦ Over.mk (E.f (k (j.succAbove c)))) b).left =
      (Pi.π (fun c ↦ Over.mk (E.f (k c))) (j.succAbove b)).left := by
  rw [← Over.comp_left, Stacks.CechSite.faceProjection, Pi.lift_π]

/-- The transition cochain is a cocycle. -/
lemma transitionCochain_mem_cocycles1 (t : ∀ l, T.presheaf.obj (op (E.X l))) :
    transitionCochain T E t ∈ Stacks.CechSite.cocycles1 E (locallyConstantPresheafAb B S hS A) := by
  rw [Stacks.CechSite.mem_cocycles1_iff']
  intro k
  let r : Fin 3 → T.presheaf.obj (op (∏ᶜ (fun a ↦ Over.mk (E.f (k a)))).left) :=
    fun i ↦ restrictToProduct T E t k i
  have key : ∀ j : Fin 3, (locallyConstantPresheafAb B S hS A).map
      (Stacks.CechSite.faceProjection E k j).left.op
        (transitionCochain T E t fun b ↦ k (j.succAbove b)) =
      toAddSection (T.diff (r (j.succAbove 1)) (r (j.succAbove 0))) := by
    intro j
    rw [locallyConstantPresheafAb_map_eq]
    erw [lcRes_transitionCochain]
    rw [faceProjection_left_π, faceProjection_left_π]
  rw [key, key, key]
  change toAddSection (T.diff (r 2) (r 1)) + toAddSection (T.diff (r 1) (r 0)) =
    toAddSection (T.diff (r 2) (r 0))
  rw [← toAddSection_mul, constantGroupSheaf_mul_comm, T.diff_mul_diff]


omit [IsNoetherian S] [S.IsSeparated] in
lemma productAddEquiv_apply {ι : Type} (G : ι → AddCommGrpCat.{a}) [HasProduct G]
    (x : (∏ᶜ G : AddCommGrpCat.{a})) (i : ι) :
    Stacks.CechSite.productAddEquiv G x i = Pi.π G i x :=
  rfl

/-- The degree-zero cochain `(λ_l|)_l` of a family of sections `λ_l ∈ F_S(V_l)`. -/
noncomputable def zeroCochain (lam : ∀ l, (constantGroupSheaf B S hS A).presheaf.obj (op (E.X l))) :
    Stacks.CechSite.cechCochain E (locallyConstantPresheafAb B S hS A) 0 :=
  fun μ ↦ lcRes (Pi.π (fun a ↦ Over.mk (E.f (μ a))) 0).left (toAddSection (lam (μ 0)))

/-- The morphism `V_l ⟶ ∏_{Fin 1} V_l`. -/
noncomputable abbrev unaryLift (l : E.I₀) :
    E.X l ⟶ (∏ᶜ (fun _ : Fin 1 ↦ Over.mk (E.f l))).left :=
  ovLift (fun _ : Fin 1 ↦ Over.mk (E.f l)) (fun _ ↦ 𝟙 (E.X l))

/-- Every degree-zero cochain is the cochain of a family of sections. -/
lemma exists_zeroCochain_eq
    (c : Stacks.CechSite.cechCochain E (locallyConstantPresheafAb B S hS A) 0) :
    ∃ lam, zeroCochain E lam = c := by
  refine ⟨fun l ↦ toAddSection.symm (lcRes (unaryLift E l) (c fun _ ↦ l)), ?_⟩
  funext μ
  obtain ⟨l, rfl⟩ : ∃ l, μ = fun _ ↦ l := ⟨μ 0, funext fun i ↦ congrArg μ (Fin.eq_zero i)⟩
  rw [zeroCochain, Equiv.apply_symm_apply]
  have : (Pi.π (fun _ : Fin 1 ↦ Over.mk (E.f l)) 0).left ≫ unaryLift E l = 𝟙 _ :=
    ovLift_ext fun j ↦ by rw [Fin.eq_zero j]; simp
  exact ((lcRes_comp _ _ _).symm.trans (congrArg (fun g ↦ lcRes g _) this)).trans (lcRes_id _)

lemma cechDifferential_zeroCochain
    (lam : ∀ l, (constantGroupSheaf B S hS A).presheaf.obj (op (E.X l))) (ν : Fin 2 → E.I₀) :
    Stacks.CechSite.cechDifferential E (locallyConstantPresheafAb B S hS A) 0
        (zeroCochain E lam) ν =
      lcRes (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 1).left (toAddSection (lam (ν 1))) -
        lcRes (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 0).left (toAddSection (lam (ν 0))) := by
  rw [Stacks.CechSite.cechDifferential_zero_apply, locallyConstantPresheafAb_map_eq,
    locallyConstantPresheafAb_map_eq]
  change lcRes _ (lcRes _ _) - lcRes _ (lcRes _ _) = _
  rw [← lcRes_comp, ← lcRes_comp, faceProjection_left_π, faceProjection_left_π]
  rfl

/-- **Changing the sections by `λ`** changes the transition cochain by the coboundary of `λ`. -/
lemma transitionCochain_act (t : ∀ l, T.presheaf.obj (op (E.X l)))
    (lam : ∀ l, (constantGroupSheaf B S hS A).presheaf.obj (op (E.X l))) :
    transitionCochain T E (fun l ↦ T.act _ (lam l) (t l)) =
      transitionCochain T E t -
        Stacks.CechSite.cechDifferential E (locallyConstantPresheafAb B S hS A) 0
          (zeroCochain E lam) := by
  funext ν
  rw [Pi.sub_apply, cechDifferential_zeroCochain, transitionCochain, transitionCochain]
  simp only [restrictToProduct]
  erw [T.naturality, T.naturality]
  set a := (constantGroupSheaf B S hS A).presheaf.map
    (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 1).left.op (lam (ν 1))
  set b := (constantGroupSheaf B S hS A).presheaf.map
    (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 0).left.op (lam (ν 0))
  set x := T.presheaf.map (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 1).left.op (t (ν 1))
  set y := T.presheaf.map (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 0).left.op (t (ν 0))
  have h : T.diff (T.act _ a x) (T.act _ b y) = b * T.diff x y * a⁻¹ := by
    rw [T.diff_act_right, ← T.diff_mul_diff (T.act _ a x) x y,
      ← T.eq_diff (show T.act _ a⁻¹ (T.act _ a x) = x by
        rw [← T.mul_act, inv_mul_cancel, T.one_act]), mul_assoc]
  rw [h, toAddSection_mul, toAddSection_mul, toAddSection_inv, ← toAddSection_map,
    ← toAddSection_map]
  abel

variable (A) in
/-- The degree-`n` terms of the Čech complex of `F_S` are the cochain families. -/
noncomputable def cochainEquiv (n : ℕ) :
    (cechComplex E (locallyConstantPresheafAb B S hS A)).X n ≃+
      Stacks.CechSite.cechCochain E (locallyConstantPresheafAb B S hS A) n :=
  Stacks.CechSite.productAddEquiv _

lemma cochainEquiv_apply (n : ℕ) (x : (cechComplex E (locallyConstantPresheafAb B S hS A)).X n)
    (ν : Fin (n + 1) → E.I₀) :
    cochainEquiv A E n x ν =
      Pi.π (Stacks.CechSite.cochainFactor E (locallyConstantPresheafAb B S hS A) n) ν x :=
  rfl

lemma cochainEquiv_d (x : (cechComplex E (locallyConstantPresheafAb B S hS A)).X 0) :
    cochainEquiv A E 1 ((cechComplex E (locallyConstantPresheafAb B S hS A)).d 0 1 x) =
      Stacks.CechSite.cechDifferential E (locallyConstantPresheafAb B S hS A) 0
        (cochainEquiv A E 0 x) :=
  (Stacks.CechSite.cechDifferential_productAddEquiv E _ 0 x).symm

lemma mem_cechCycles_iff_cochainEquiv
    (x : (cechComplex E (locallyConstantPresheafAb B S hS A)).X 1) :
    x ∈ cechCycles E (locallyConstantPresheafAb B S hS A) 1 ↔
      cochainEquiv A E 1 x ∈ Stacks.CechSite.cocycles1 E (locallyConstantPresheafAb B S hS A) :=
  (Stacks.CechSite.productAddEquiv_mem_cocycles1_iff E _ x).symm

lemma cochainEquiv_refinementCochainMap {E' : PreZeroHypercover.{0} (final B S hS)}
    (φ : E'.Hom E) (x : (cechComplex E (locallyConstantPresheafAb B S hS A)).X 1)
    (ν : Fin 2 → E'.I₀) :
    cochainEquiv A E' 1 ((refinementCochainMap φ (locallyConstantPresheafAb B S hS A)).f 1 x) ν =
      lcRes (refinementProductMap φ 1 ν) (cochainEquiv A E 1 x (φ.s₀ ∘ ν)) :=
  refinementCochainMap_f_apply φ _ 1 x ν

/-- **Refinement.** Pulling the sections back along a refinement `φ` pulls the transition
cochain back along `φ`. -/
lemma transitionCochain_refinement {E' : PreZeroHypercover.{0} (final B S hS)} (φ : E'.Hom E)
    (t : ∀ l, T.presheaf.obj (op (E.X l)))
    (x : (cechComplex E (locallyConstantPresheafAb B S hS A)).X 1)
    (hx : cochainEquiv A E 1 x = transitionCochain T E t) :
    cochainEquiv A E' 1 ((refinementCochainMap φ (locallyConstantPresheafAb B S hS A)).f 1 x) =
      transitionCochain T E' (fun k ↦ T.presheaf.map (φ.h₀ k).op (t (φ.s₀ k))) := by
  funext ν
  rw [cochainEquiv_refinementCochainMap, hx]
  erw [lcRes_transitionCochain]
  rw [refinementProductMap_π, refinementProductMap_π, transitionCochain]
  simp only [restrictToProduct, op_comp, Functor.map_comp_apply]
  rfl

/-- An equivariant morphism of torsors does not change the transition cochain. -/
lemma transitionCochain_hom {T' : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A)}
    (e : T.Hom T') (t : ∀ l, T.presheaf.obj (op (E.X l))) :
    transitionCochain T' E (fun l ↦ e.hom.app _ (t l)) = transitionCochain T E t := by
  funext ν
  simp only [transitionCochain, restrictToProduct]
  erw [← NatTrans.naturality_apply e.hom, ← NatTrans.naturality_apply e.hom]
  rw [T.diff_hom]

end Cochain

section Class

variable [IsNoetherian S] [S.IsSeparated] {A : Type w} [AddCommGroup A]
  (T : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A))

/-- The transition cocycle of sections `t_l ∈ 𝒢(V_l)` over a covering, in `Z^1(𝔙, F_S)`. -/
noncomputable def transitionCycle (𝔙 : CechCovering (final B S hS))
    (t : ∀ l, T.presheaf.obj (op (𝔙.toPreZeroHypercover.X l))) :
    cechCycles 𝔙.toPreZeroHypercover (locallyConstantPresheafAb B S hS A) 1 :=
  ⟨(cochainEquiv A _ 1).symm (transitionCochain T _ t), by
    rw [mem_cechCycles_iff_cochainEquiv, AddEquiv.apply_symm_apply]
    exact transitionCochain_mem_cocycles1 T _ t⟩

lemma cochainEquiv_transitionCycle (𝔙 : CechCovering (final B S hS))
    (t : ∀ l, T.presheaf.obj (op (𝔙.toPreZeroHypercover.X l))) :
    cochainEquiv A _ 1 (transitionCycle T 𝔙 t).1 = transitionCochain T _ t :=
  AddEquiv.apply_symm_apply _ _

/-- Two cochains of one covering whose transition cochains differ by the coboundary of
`zeroCochain λ` differ by a coboundary. -/
lemma sub_mem_range_of_transitionCochain {E : PreZeroHypercover.{0} (final B S hS)}
    (x y : (cechComplex E (locallyConstantPresheafAb B S hS A)).X 1)
    (lam : ∀ l, (constantGroupSheaf B S hS A).presheaf.obj (op (E.X l)))
    (h : cochainEquiv A E 1 y = cochainEquiv A E 1 x -
        Stacks.CechSite.cechDifferential E (locallyConstantPresheafAb B S hS A) 0
          (zeroCochain E lam)) :
    x - y ∈ ((cechComplex E (locallyConstantPresheafAb B S hS A)).d (1 - 1) 1).hom.range := by
  refine ⟨(cochainEquiv A E 0).symm (zeroCochain E lam), ?_⟩
  apply (cochainEquiv A E 1).injective
  change cochainEquiv A E 1 ((cechComplex E (locallyConstantPresheafAb B S hS A)).d 0 1 _) = _
  rw [cochainEquiv_d, AddEquiv.apply_symm_apply, map_sub, h]
  abel

/-- **Independence of the choices.** The Čech class of the transition cocycle does not depend
on the covering or on the sections. -/
theorem cechClass_transitionCycle_eq (𝔙 𝔙' : CechCovering (final B S hS))
    (t : ∀ l, T.presheaf.obj (op (𝔙.toPreZeroHypercover.X l)))
    (t' : ∀ l, T.presheaf.obj (op (𝔙'.toPreZeroHypercover.X l))) :
    cechClass (locallyConstantPresheafAb B S hS A) 1 𝔙 (transitionCycle T 𝔙 t) =
      cechClass (locallyConstantPresheafAb B S hS A) 1 𝔙' (transitionCycle T 𝔙' t') := by
  refine cechClass_eq_cechClass _ 1 ⟨𝔙.inf 𝔙', CechCovering.infFst 𝔙 𝔙',
    CechCovering.infSnd 𝔙 𝔙', ?_⟩
  set φ := CechCovering.infFst 𝔙 𝔙'
  set φ' := CechCovering.infSnd 𝔙 𝔙'
  let s := fun k ↦ T.presheaf.map (φ.h₀ k).op (t (φ.s₀ k))
  let s' := fun k ↦ T.presheaf.map (φ'.h₀ k).op (t' (φ'.s₀ k))
  have hs' : s' = fun k ↦ T.act _ (T.diff (s k) (s' k)) (s k) :=
    funext fun k ↦ (T.diff_act _ _).symm
  refine sub_mem_range_of_transitionCochain _ _ (fun k ↦ T.diff (s k) (s' k)) ?_
  rw [transitionCochain_refinement T _ φ t _ (cochainEquiv_transitionCycle T 𝔙 t),
    transitionCochain_refinement T _ φ' t' _ (cochainEquiv_transitionCycle T 𝔙' t'),
    ← transitionCochain_act]
  exact congrArg _ hs'

end Class

section Injectivity

variable [IsNoetherian S] [S.IsSeparated] {A : Type w} [AddCommGroup A]
  {T T' : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A)} (𝔚 : CechCovering (final B S hS))
  (s : ∀ k, T.presheaf.obj (op (𝔚.X k))) (s' : ∀ k, T'.presheaf.obj (op (𝔚.X k)))

/-- The sieve of the morphisms `V ⟶ W` such that `V` maps to a member of `𝔚`. -/
def memberSieve (W : SmallNoetherianSeparatedEtale B S hS) : Sieve W where
  arrows V _ := ∃ k, Nonempty (V ⟶ 𝔚.X k)
  downward_closed := by
    rintro V V' g ⟨k, ⟨h⟩⟩ e
    exact ⟨k, ⟨e ≫ h⟩⟩

lemma memberSieve_mem (W : SmallNoetherianSeparatedEtale B S hS) :
    memberSieve 𝔚 W ∈ topology B S hS W := by
  rw [mem_topology_iff]
  intro w
  obtain ⟨k, v, hv⟩ := Set.mem_iUnion.mp (𝔚.iUnion_range ▸ Set.mem_univ
    (((toScheme B S hS).map (toFinal W)).base w))
  obtain ⟨p, hp, -⟩ := exists_pullback_toFinal_point (W := W) (V := 𝔚.X k) w v
    (by rw [← hv, hom_ext_final (𝔚.f k) (toFinal _)])
  exact ⟨_, pullback.fst _ _, ⟨k, ⟨pullback.snd _ _⟩⟩, p, hp⟩

/-- The candidate value `δ(s_k|_V, x) • s'_k|_V` of the comparison map at `x ∈ 𝒢(V)`, for
`h : V ⟶ W_k`. -/
noncomputable def glueValue {V : SmallNoetherianSeparatedEtale B S hS} (k : Fin 𝔚.n)
    (h : V ⟶ 𝔚.X k) (x : T.presheaf.obj (op V)) : T'.presheaf.obj (op V) :=
  T'.act _ (T.diff (T.presheaf.map h.op (s k)) x) (T'.presheaf.map h.op (s' k))

variable {𝔚 s s'}

lemma glueValue_indep
    (H : ∀ (V : SmallNoetherianSeparatedEtale B S hS) (k k' : Fin 𝔚.n) (h : V ⟶ 𝔚.X k)
      (h' : V ⟶ 𝔚.X k'), T.diff (T.presheaf.map h.op (s k)) (T.presheaf.map h'.op (s k')) =
        T'.diff (T'.presheaf.map h.op (s' k)) (T'.presheaf.map h'.op (s' k')))
    {V : SmallNoetherianSeparatedEtale B S hS} (k k' : Fin 𝔚.n) (h : V ⟶ 𝔚.X k)
    (h' : V ⟶ 𝔚.X k') (x : T.presheaf.obj (op V)) :
    glueValue 𝔚 s s' k h x = glueValue 𝔚 s s' k' h' x := by
  rw [glueValue, glueValue, ← T'.diff_act (T'.presheaf.map h.op (s' k))
    (T'.presheaf.map h'.op (s' k')), ← T'.mul_act, ← H, T.diff_mul_diff]

lemma map_glueValue {V V' : SmallNoetherianSeparatedEtale B S hS} (k : Fin 𝔚.n)
    (h : V ⟶ 𝔚.X k) (e : V' ⟶ V) (x : T.presheaf.obj (op V)) :
    T'.presheaf.map e.op (glueValue 𝔚 s s' k h x) =
      glueValue 𝔚 s s' k (e ≫ h) (T.presheaf.map e.op x) := by
  rw [glueValue, glueValue, T'.naturality, T.map_diff, op_comp, Functor.map_comp_apply,
    Functor.map_comp_apply]

lemma glueValue_act {V : SmallNoetherianSeparatedEtale B S hS} (k : Fin 𝔚.n) (h : V ⟶ 𝔚.X k)
    (g : (constantGroupSheaf B S hS A).presheaf.obj (op V)) (x : T.presheaf.obj (op V)) :
    glueValue 𝔚 s s' k h (T.act _ g x) = T'.act _ g (glueValue 𝔚 s s' k h x) := by
  rw [glueValue, glueValue, T.diff_act_right, T'.mul_act]

variable (H : ∀ (V : SmallNoetherianSeparatedEtale B S hS) (k k' : Fin 𝔚.n) (h : V ⟶ 𝔚.X k)
      (h' : V ⟶ 𝔚.X k'), T.diff (T.presheaf.map h.op (s k)) (T.presheaf.map h'.op (s k')) =
        T'.diff (T'.presheaf.map h.op (s' k)) (T'.presheaf.map h'.op (s' k')))

include H in
lemma exists_glue {W : SmallNoetherianSeparatedEtale B S hS} (x : T.presheaf.obj (op W)) :
    ∃ y : T'.presheaf.obj (op W), ∀ (V : SmallNoetherianSeparatedEtale B S hS) (g : V ⟶ W)
      (k : Fin 𝔚.n) (h : V ⟶ 𝔚.X k),
        T'.presheaf.map g.op y = glueValue 𝔚 s s' k h (T.presheaf.map g.op x) := by
  obtain ⟨y, hy⟩ := T'.isSheaf.exists_of_mem (memberSieve_mem 𝔚 W)
    (fun V g hg ↦ glueValue 𝔚 s s' hg.choose hg.choose_spec.some (T.presheaf.map g.op x))
    (fun V V' g e hg ↦ by
      rw [map_glueValue, op_comp, Functor.map_comp_apply]
      exact glueValue_indep H _ _ _ _ _)
  exact ⟨y, fun V g k h ↦ (hy g ⟨k, ⟨h⟩⟩).trans (glueValue_indep H _ _ _ _ _)⟩

/-- The comparison map `𝒢(W) → 𝒢'(W)`. -/
noncomputable def glueApp {W : SmallNoetherianSeparatedEtale B S hS}
    (x : T.presheaf.obj (op W)) : T'.presheaf.obj (op W) :=
  (exists_glue H x).choose

lemma glueApp_spec {W : SmallNoetherianSeparatedEtale B S hS} (x : T.presheaf.obj (op W))
    (V : SmallNoetherianSeparatedEtale B S hS) (g : V ⟶ W) (k : Fin 𝔚.n) (h : V ⟶ 𝔚.X k) :
    T'.presheaf.map g.op (glueApp H x) = glueValue 𝔚 s s' k h (T.presheaf.map g.op x) :=
  (exists_glue H x).choose_spec V g k h

lemma glueApp_eq_of {W : SmallNoetherianSeparatedEtale B S hS} (x : T.presheaf.obj (op W))
    (y : T'.presheaf.obj (op W))
    (hy : ∀ (V : SmallNoetherianSeparatedEtale B S hS) (g : V ⟶ W) (k : Fin 𝔚.n)
      (h : V ⟶ 𝔚.X k), T'.presheaf.map g.op y = glueValue 𝔚 s s' k h (T.presheaf.map g.op x)) :
    glueApp H x = y :=
  T'.isSheaf.ext_of_mem (memberSieve_mem 𝔚 W) fun V g ⟨k, ⟨h⟩⟩ ↦
    (glueApp_spec H x V g k h).trans (hy V g k h).symm

/-- **The comparison morphism of torsors** with the same transition data on one covering. -/
noncomputable def glueHom : T.Hom T' where
  hom :=
    { app W := TypeCat.ofHom (glueApp H (W := W.unop))
      naturality W W' f := by
        ext x
        change glueApp H (W := W'.unop) (T.presheaf.map f x) =
          T'.presheaf.map f (glueApp H (W := W.unop) x)
        refine glueApp_eq_of H _ _ fun V g k h ↦ ?_
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        exact glueApp_spec H x V (g ≫ f.unop) k h }
  map_act W g x := by
    change glueApp H (W := W.unop) (T.act W g x) = T'.act W g (glueApp H (W := W.unop) x)
    refine glueApp_eq_of H _ _ fun V e k h ↦ ?_
    rw [T'.naturality, glueApp_spec H x V e k h, T.naturality, glueValue_act]

end Injectivity

section Pairs

variable [IsNoetherian S] [S.IsSeparated] {A : Type w} [AddCommGroup A]
  (E : PreZeroHypercover.{0} (final B S hS))

/-- The morphism `V ⟶ V_k ×_S V_{k'}` given by `h : V ⟶ V_k` and `h' : V ⟶ V_{k'}`. -/
noncomputable def pairLift {V : SmallNoetherianSeparatedEtale B S hS} {k k' : E.I₀}
    (h : V ⟶ E.X k) (h' : V ⟶ E.X k') :
    V ⟶ (∏ᶜ (fun j : Fin 2 ↦ Over.mk (E.f (![k, k'] j)))).left :=
  ovLift _ (fun j ↦ Fin.cases h (fun i ↦ Fin.cases h' (fun i ↦ i.elim0) i) j)

lemma pairLift_fst {V : SmallNoetherianSeparatedEtale B S hS} {k k' : E.I₀}
    (h : V ⟶ E.X k) (h' : V ⟶ E.X k') :
    pairLift E h h' ≫ (Pi.π (fun j : Fin 2 ↦ Over.mk (E.f (![k, k'] j))) 0).left = h :=
  ovLift_π _ _ _

lemma pairLift_snd {V : SmallNoetherianSeparatedEtale B S hS} {k k' : E.I₀}
    (h : V ⟶ E.X k) (h' : V ⟶ E.X k') :
    pairLift E h h' ≫ (Pi.π (fun j : Fin 2 ↦ Over.mk (E.f (![k, k'] j))) 1).left = h' :=
  ovLift_π _ _ _

variable {E} {T T' : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A)}

/-- The difference of two sections over `V` mapping to `V_k` and `V_{k'}` is read off from the
transition cochain. -/
lemma toAddSection_diff_eq_lcRes (t : ∀ l, T.presheaf.obj (op (E.X l)))
    {V : SmallNoetherianSeparatedEtale B S hS} {k k' : E.I₀} (h : V ⟶ E.X k)
    (h' : V ⟶ E.X k') :
    toAddSection (T.diff (T.presheaf.map h.op (t k)) (T.presheaf.map h'.op (t k'))) =
      lcRes (pairLift E h' h) (transitionCochain T E t ![k', k]) := by
  erw [lcRes_transitionCochain]
  rw [pairLift_fst, pairLift_snd]
  rfl

lemma diff_eq_of_transitionCochain_eq (t : ∀ l, T.presheaf.obj (op (E.X l)))
    (t' : ∀ l, T'.presheaf.obj (op (E.X l)))
    (ht : transitionCochain T E t = transitionCochain T' E t')
    (V : SmallNoetherianSeparatedEtale B S hS) (k k' : E.I₀) (h : V ⟶ E.X k)
    (h' : V ⟶ E.X k') :
    T.diff (T.presheaf.map h.op (t k)) (T.presheaf.map h'.op (t k')) =
      T'.diff (T'.presheaf.map h.op (t' k)) (T'.presheaf.map h'.op (t' k')) :=
  toAddSection.injective (by rw [toAddSection_diff_eq_lcRes, toAddSection_diff_eq_lcRes, ht])

end Pairs

section Covering

variable [IsNoetherian S] [S.IsSeparated] {A : Type w} [AddCommGroup A]

/-- **A torsor is trivial on the members of a covering of `S`.** -/
lemma exists_cechCovering_nonempty (T : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A))
    (hT : T.IsTorsor) :
    ∃ 𝔙 : CechCovering (final B S hS), ∀ l : 𝔙.toPreZeroHypercover.I₀,
      Nonempty (T.presheaf.obj (op (𝔙.toPreZeroHypercover.X l))) := by
  obtain ⟨R, hR, hne⟩ := hT (final B S hS)
  have hcov := (mem_topology_iff B S hS R).mp hR
  choose V f hf hx using hcov
  have hopen : ∀ x, IsOpen (Set.range ((toScheme B S hS).map (f x))) :=
    fun x ↦ ((toScheme B S hS).map (f x)).isOpenMap.isOpen_range
  have : CompactSpace ((toScheme B S hS).obj (final B S hS)) :=
    inferInstanceAs (CompactSpace S)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  by_cases hpos : 0 < t.card
  · let e := t.equivFin.symm
    refine ⟨⟨t.card, hpos, fun i ↦ V (e i), fun i ↦ f (e i), ?_⟩, fun i ↦ hne (hf (e i))⟩
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact Set.mem_iUnion.mpr ⟨e.symm ⟨x, hxt⟩, by rw [e.apply_symm_apply]; exact hy⟩
  · have hempty : IsEmpty ((toScheme B S hS).obj (final B S hS)) := by
      rw [Finset.card_pos, Finset.not_nonempty_iff_eq_empty] at hpos
      refine ⟨fun y ↦ ?_⟩
      simpa [hpos] using ht (Set.mem_univ y)
    refine ⟨CechCovering.self _, fun _ ↦ ?_⟩
    have hbot : (⊥ : Sieve (final B S hS)) ∈ topology B S hS (final B S hS) :=
      (mem_topology_iff B S hS ⊥).mpr fun y ↦ hempty.elim y
    obtain ⟨z, -⟩ := T.isSheaf.exists_of_mem hbot (fun V g hg ↦ hg.elim) (fun _ _ _ _ hg ↦ hg.elim)
    exact ⟨z⟩

end Covering

section Kappa

variable [IsNoetherian S] [S.IsSeparated] {A : Type w} [AddCommGroup A]

/-- The Čech class `κ[𝒢] = [σ]_𝔙 ∈ Ȟ¹(S, F_S)` of a torsor, for a covering `𝔙` over whose
members it has sections. -/
noncomputable def torsorCechClass (T : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A))
    (hT : T.IsTorsor) :
    cechCohomologyOfObject (final B S hS) (locallyConstantPresheafAb B S hS A) 1 :=
  cechClass _ 1 (exists_cechCovering_nonempty T hT).choose
    (transitionCycle T _ fun l ↦ ((exists_cechCovering_nonempty T hT).choose_spec l).some)

lemma torsorCechClass_eq (T : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A))
    (hT : T.IsTorsor) (𝔙 : CechCovering (final B S hS))
    (t : ∀ l, T.presheaf.obj (op (𝔙.toPreZeroHypercover.X l))) :
    torsorCechClass T hT = cechClass _ 1 𝔙 (transitionCycle T 𝔙 t) :=
  cechClass_transitionCycle_eq T _ _ _ _

lemma torsorCechClass_eq_of_hom {T T' : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A)}
    (hT : T.IsTorsor) (hT' : T'.IsTorsor) (e : T.Hom T') :
    torsorCechClass T hT = torsorCechClass T' hT' := by
  obtain ⟨𝔙, ht⟩ := exists_cechCovering_nonempty T hT
  let t := fun l ↦ (ht l).some
  rw [torsorCechClass_eq T hT 𝔙 t, torsorCechClass_eq T' hT' 𝔙 (fun l ↦ e.hom.app _ (t l))]
  congr 1
  apply Subtype.ext
  apply (cochainEquiv A _ 1).injective
  rw [cochainEquiv_transitionCycle, cochainEquiv_transitionCycle, transitionCochain_hom]

/-- **Injectivity of `κ`.** Torsors with the same Čech class are isomorphic. -/
theorem nonempty_hom_of_torsorCechClass_eq
    {T T' : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A)}
    (hT : T.IsTorsor) (hT' : T'.IsTorsor) (h : torsorCechClass T hT = torsorCechClass T' hT') :
    Nonempty (T.Hom T') := by
  obtain ⟨𝔙, ht⟩ := exists_cechCovering_nonempty T hT
  obtain ⟨𝔙', ht'⟩ := exists_cechCovering_nonempty T' hT'
  let t := fun l ↦ (ht l).some
  let t' := fun l ↦ (ht' l).some
  rw [torsorCechClass_eq T hT 𝔙 t, torsorCechClass_eq T' hT' 𝔙' t',
    cechClass_eq_cechClass_iff] at h
  obtain ⟨𝔚, φ, φ', ⟨x, hx⟩⟩ := h
  let s : ∀ k, T.presheaf.obj (op (𝔚.toPreZeroHypercover.X k)) :=
    fun k ↦ T.presheaf.map (φ.h₀ k).op (t (φ.s₀ k))
  let s' : ∀ k, T'.presheaf.obj (op (𝔚.toPreZeroHypercover.X k)) :=
    fun k ↦ T'.presheaf.map (φ'.h₀ k).op (t' (φ'.s₀ k))
  obtain ⟨lam, hlam⟩ := exists_zeroCochain_eq _ (-cochainEquiv A _ 0 x)
  have hx' := congrArg (cochainEquiv A _ 1) hx
  change cochainEquiv A _ 1 ((cechComplex _ (locallyConstantPresheafAb B S hS A)).d 0 1 x) = _
    at hx'
  rw [cochainEquiv_d, map_sub,
    transitionCochain_refinement T _ φ t _ (cochainEquiv_transitionCycle T 𝔙 t),
    transitionCochain_refinement T' _ φ' t' _ (cochainEquiv_transitionCycle T' 𝔙' t')] at hx'
  have heq : transitionCochain T _ s =
      transitionCochain T' _ (fun k ↦ T'.act _ (lam k) (s' k)) := by
    rw [transitionCochain_act, hlam, map_neg, hx']
    abel
  exact ⟨glueHom (𝔚 := 𝔚) (s := s) (s' := fun k ↦ T'.act _ (lam k) (s' k))
    (diff_eq_of_transitionCochain_eq _ _ heq)⟩

end Kappa

section CocycleTorsor

variable [IsNoetherian S] [S.IsSeparated] {A : Type w} [AddCommGroup A]
  {E : PreZeroHypercover.{0} (final B S hS)}

lemma pairLift_comp {V V' : SmallNoetherianSeparatedEtale B S hS} {k k' : E.I₀}
    (e : V' ⟶ V) (h : V ⟶ E.X k) (h' : V ⟶ E.X k') :
    e ≫ pairLift E h h' = pairLift E (e ≫ h) (e ≫ h') :=
  ovLift_ext fun j ↦ by
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Category.assoc, pairLift_fst]
      rfl
    · simp only [Fin.mk_one, Fin.isValue, Category.assoc, pairLift_snd]
      rfl

/-- Cochain values agree along maps with the same components, also for propositionally equal
index tuples. -/
lemma lcRes_cochain_congr (c : Stacks.CechSite.cechCochain E (locallyConstantPresheafAb B S hS A) 1)
    {μ μ' : Fin 2 → E.I₀} (hμ : μ = μ') {V : SmallNoetherianSeparatedEtale B S hS}
    (g : V ⟶ (∏ᶜ (fun a ↦ Over.mk (E.f (μ a)))).left)
    (g' : V ⟶ (∏ᶜ (fun a ↦ Over.mk (E.f (μ' a)))).left)
    (hg : ∀ j, g ≫ (Pi.π (fun a ↦ Over.mk (E.f (μ a))) j).left ≍
      g' ≫ (Pi.π (fun a ↦ Over.mk (E.f (μ' a))) j).left) :
    lcRes g (c μ) = lcRes g' (c μ') := by
  subst hμ
  obtain rfl : g = g' := ovLift_ext fun j ↦ eq_of_heq (hg j)
  rfl

/-- The cocycle condition `σ_{ln} = σ_{mn} + σ_{lm}` read along maps into `V_l`, `V_m`, `V_n`. -/
lemma cocycle_lcRes {c : Stacks.CechSite.cechCochain E (locallyConstantPresheafAb B S hS A) 1}
    (hc : c ∈ Stacks.CechSite.cocycles1 E (locallyConstantPresheafAb B S hS A))
    {V : SmallNoetherianSeparatedEtale B S hS} {l m n : E.I₀} (x : V ⟶ E.X l) (y : V ⟶ E.X m)
    (z : V ⟶ E.X n) :
    lcRes (pairLift E x z) (c ![l, n]) =
      lcRes (pairLift E y z) (c ![m, n]) + lcRes (pairLift E x y) (c ![l, m]) := by
  let k : Fin 3 → E.I₀ := ![l, m, n]
  let G : V ⟶ (∏ᶜ (fun a : Fin 3 ↦ Over.mk (E.f (k a)))).left :=
    ovLift (fun a : Fin 3 ↦ Over.mk (E.f (k a)))
      (fun j ↦ Fin.cases x (fun i ↦ Fin.cases y (fun i ↦ Fin.cases z (fun i ↦ i.elim0) i) i) j)
  have h0 := (Stacks.CechSite.mem_cocycles1_iff' E _ c).mp hc k
  have hj : ∀ j : Fin 3, lcRes G ((locallyConstantPresheafAb B S hS A).map
      (Stacks.CechSite.faceProjection E k j).left.op (c fun b ↦ k (j.succAbove b))) =
      lcRes (G ≫ (Stacks.CechSite.faceProjection E k j).left) (c fun b ↦ k (j.succAbove b)) :=
    fun j ↦ (lcRes_comp _ _ _).symm
  have h1 : lcRes G ((locallyConstantPresheafAb B S hS A).map
        (Stacks.CechSite.faceProjection E k 0).left.op (c fun b ↦ k ((0 : Fin 3).succAbove b))) +
      lcRes G ((locallyConstantPresheafAb B S hS A).map
        (Stacks.CechSite.faceProjection E k 2).left.op (c fun b ↦ k ((2 : Fin 3).succAbove b))) =
      lcRes G ((locallyConstantPresheafAb B S hS A).map
        (Stacks.CechSite.faceProjection E k 1).left.op (c fun b ↦ k ((1 : Fin 3).succAbove b))) :=
    congrArg (lcRes G) h0
  rw [hj, hj, hj] at h1
  have e0 : lcRes (G ≫ (Stacks.CechSite.faceProjection E k 0).left)
      (c fun b ↦ k ((0 : Fin 3).succAbove b)) = lcRes (pairLift E y z) (c ![m, n]) := by
    refine lcRes_cochain_congr c (by funext j; fin_cases j <;> rfl) _ _ fun j ↦ ?_
    rw [Category.assoc, faceProjection_left_π, ovLift_π]
    fin_cases j
    · exact heq_of_eq (pairLift_fst E y z).symm
    · exact heq_of_eq (pairLift_snd E y z).symm
  have e1 : lcRes (G ≫ (Stacks.CechSite.faceProjection E k 1).left)
      (c fun b ↦ k ((1 : Fin 3).succAbove b)) = lcRes (pairLift E x z) (c ![l, n]) := by
    refine lcRes_cochain_congr c (by funext j; fin_cases j <;> rfl) _ _ fun j ↦ ?_
    rw [Category.assoc, faceProjection_left_π, ovLift_π]
    fin_cases j
    · exact heq_of_eq (pairLift_fst E x z).symm
    · exact heq_of_eq (pairLift_snd E x z).symm
  have e2 : lcRes (G ≫ (Stacks.CechSite.faceProjection E k 2).left)
      (c fun b ↦ k ((2 : Fin 3).succAbove b)) = lcRes (pairLift E x y) (c ![l, m]) := by
    refine lcRes_cochain_congr c (by funext j; fin_cases j <;> rfl) _ _ fun j ↦ ?_
    rw [Category.assoc, faceProjection_left_π, ovLift_π]
    fin_cases j
    · exact heq_of_eq (pairLift_fst E x y).symm
    · exact heq_of_eq (pairLift_snd E x y).symm
  rw [e0, e1, e2] at h1
  exact h1.symm

lemma lcRes_comp_cochain (c : Stacks.CechSite.cechCochain E (locallyConstantPresheafAb B S hS A) 1)
    (ν : Fin 2 → E.I₀) {V V' : SmallNoetherianSeparatedEtale B S hS} (e : V' ⟶ V)
    (g : V ⟶ (∏ᶜ (fun a ↦ Over.mk (E.f (ν a)))).left) :
    lcRes (e ≫ g) (c ν) = lcRes e (lcRes g (c ν)) :=
  lcRes_comp e g _

variable (E) in
/-- The fibre product `W ×_S V_l`. -/
noncomputable abbrev memberProd (W : SmallNoetherianSeparatedEtale B S hS) (l : E.I₀) :
    SmallNoetherianSeparatedEtale B S hS :=
  pullback (toFinal W) (toFinal (E.X l))

/-- The morphism `W' ×_S V_l ⟶ W ×_S V_l` induced by `f : W' ⟶ W`. -/
noncomputable def memberProdMap {W W' : SmallNoetherianSeparatedEtale B S hS} (f : W' ⟶ W)
    (l : E.I₀) : memberProd E W' l ⟶ memberProd E W l :=
  pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _) (hom_ext_final _ _)

@[reassoc (attr := simp)]
lemma memberProdMap_fst {W W' : SmallNoetherianSeparatedEtale B S hS} (f : W' ⟶ W) (l : E.I₀) :
    memberProdMap f l ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma memberProdMap_snd {W W' : SmallNoetherianSeparatedEtale B S hS} (f : W' ⟶ W) (l : E.I₀) :
    memberProdMap f l ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

lemma memberProdMap_id (W : SmallNoetherianSeparatedEtale B S hS) (l : E.I₀) :
    memberProdMap (𝟙 W) l = 𝟙 _ :=
  pullback.hom_ext (by simp) (by simp)

lemma memberProdMap_comp {W W' W'' : SmallNoetherianSeparatedEtale B S hS} (f' : W'' ⟶ W')
    (f : W' ⟶ W) (l : E.I₀) :
    memberProdMap (f' ≫ f) l = memberProdMap f' l ≫ memberProdMap f l :=
  pullback.hom_ext (by simp) (by simp)

variable (c : Stacks.CechSite.cechCochain E (locallyConstantPresheafAb B S hS A) 1)

/-- The condition `k_l = k_m + σ_{lm}` on `W ×_S V_l ×_S V_m` on a family
`k_l ∈ F_S(W ×_S V_l)`, read along all test maps. -/
def IsCocycleSection (W : SmallNoetherianSeparatedEtale B S hS)
    (k : ∀ l, LocallyConstant ((toScheme B S hS).obj (memberProd E W l)) A) : Prop :=
  ∀ (V : SmallNoetherianSeparatedEtale B S hS) (l m : E.I₀) (a : V ⟶ memberProd E W l)
    (b : V ⟶ memberProd E W m), a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ →
      lcRes a (k l) = lcRes b (k m) +
        lcRes (pairLift E (a ≫ pullback.snd _ _) (b ≫ pullback.snd _ _)) (c ![l, m])

variable (A) in
/-- The sections over `W` of the torsor of a cocycle `σ`: the families `k_l ∈ F_S(W ×_S V_l)` with
`k_l = k_m + σ_{lm}` on `W ×_S V_l ×_S V_m`. -/
def CocycleSection (W : SmallNoetherianSeparatedEtale B S hS) : Type (max u w) :=
  {k : ∀ l, LocallyConstant ((toScheme B S hS).obj (memberProd E W l)) A //
    IsCocycleSection c W k}

/-- Restriction of the sections of the torsor of a cocycle. -/
noncomputable def CocycleSection.map {W W' : SmallNoetherianSeparatedEtale B S hS} (f : W' ⟶ W)
    (k : CocycleSection A c W) : CocycleSection A c W' :=
  ⟨fun l ↦ lcRes (memberProdMap f l) (k.1 l), fun V l m a b hab ↦ by
    rw [← lcRes_comp, ← lcRes_comp]
    have := k.2 V l m (a ≫ memberProdMap f l) (b ≫ memberProdMap f m)
      (by simp only [Category.assoc, memberProdMap_fst, reassoc_of% hab])
    simpa only [Category.assoc, memberProdMap_snd] using this⟩

lemma CocycleSection.map_val {W W' : SmallNoetherianSeparatedEtale B S hS} (f : W' ⟶ W)
    (k : CocycleSection A c W) (l : E.I₀) :
    (k.map c f).1 l = lcRes (memberProdMap f l) (k.1 l) :=
  rfl

variable (A) in
/-- The presheaf of sets of the torsor of a cocycle. -/
noncomputable def cocyclePresheaf :
    (SmallNoetherianSeparatedEtale B S hS)ᵒᵖ ⥤ Type (max u w) where
  obj W := CocycleSection A c W.unop
  map f := TypeCat.ofHom (CocycleSection.map c f.unop)
  map_id W := by
    ext k
    refine Subtype.ext (funext fun l ↦ ?_)
    change lcRes (memberProdMap (𝟙 W.unop) l) (k.1 l) = k.1 l
    rw [memberProdMap_id, lcRes_id]
  map_comp f g := by
    ext k
    refine Subtype.ext (funext fun l ↦ ?_)
    change lcRes (memberProdMap (g.unop ≫ f.unop) l) (k.1 l) =
      lcRes (memberProdMap g.unop l) (lcRes (memberProdMap f.unop l) (k.1 l))
    rw [memberProdMap_comp, lcRes_comp]

lemma cocyclePresheaf_map_val {W W' : SmallNoetherianSeparatedEtale B S hS} (f : W' ⟶ W)
    (k : (cocyclePresheaf A c).obj (op W)) (l : E.I₀) :
    ((cocyclePresheaf A c).map f.op k).1 l = lcRes (memberProdMap f l) (k.1 l) :=
  rfl

/-- The action `k ↦ (k_l - g|)_l` of `F_S(W)` on the sections of the torsor of a cocycle. -/
noncomputable def cocycleAct (W : SmallNoetherianSeparatedEtale B S hS)
    (g : (constantGroupSheaf B S hS A).presheaf.obj (op W)) (k : CocycleSection A c W) :
    CocycleSection A c W :=
  ⟨fun l ↦ k.1 l - lcRes (pullback.fst _ _) (toAddSection g), fun V l m a b hab ↦ by
    have := k.2 V l m a b hab
    change lcRes a (k.1 l) - lcRes a (lcRes _ (toAddSection g)) =
      lcRes b (k.1 m) - lcRes b (lcRes _ (toAddSection g)) + _
    rw [← lcRes_comp, ← lcRes_comp, hab, this]
    abel⟩

lemma cocycleAct_val (W : SmallNoetherianSeparatedEtale B S hS)
    (g : (constantGroupSheaf B S hS A).presheaf.obj (op W)) (k : CocycleSection A c W) (l : E.I₀) :
    (cocycleAct c W g k).1 l = k.1 l - lcRes (pullback.fst _ _) (toAddSection g) :=
  rfl

end CocycleTorsor

/-- The sieve of the morphisms `V ⟶ W` such that `V` maps to a member of `E`. -/
def memberSieveOf [IsNoetherian S] [S.IsSeparated] (E : PreZeroHypercover.{0} (final B S hS))
    (W : SmallNoetherianSeparatedEtale B S hS) : Sieve W where
  arrows V _ := ∃ k, Nonempty (V ⟶ E.X k)
  downward_closed := by
    rintro V V' g ⟨k, ⟨h⟩⟩ e
    exact ⟨k, ⟨e ≫ h⟩⟩

lemma memberSieveOf_mem [IsNoetherian S] [S.IsSeparated] (𝔙 : CechCovering (final B S hS))
    (W : SmallNoetherianSeparatedEtale B S hS) :
    memberSieveOf 𝔙.toPreZeroHypercover W ∈ topology B S hS W :=
  memberSieve_mem 𝔙 W

section CocycleTorsorCovering

variable [IsNoetherian S] [S.IsSeparated] {A : Type w} [AddCommGroup A]
  {E : PreZeroHypercover.{0} (final B S hS)}
  (hE : ∀ W : SmallNoetherianSeparatedEtale B S hS, memberSieveOf E W ∈ topology B S hS W)
  (c : Stacks.CechSite.cechCochain E (locallyConstantPresheafAb B S hS A) 1)

include hE in
/-- The action of `F_S(W)` on the sections of the torsor of a cocycle is simply transitive. -/
lemma cocycleAct_simplyTransitive (W : SmallNoetherianSeparatedEtale B S hS)
    (k k' : CocycleSection A c W) : ∃! g, cocycleAct c W g k = k' := by
  let d : ∀ l, LocallyConstant ((toScheme B S hS).obj
      (memberProd E W l)) A := fun l ↦ k.1 l - k'.1 l
  have hd : ∀ (V : SmallNoetherianSeparatedEtale B S hS) (g : V ⟶ W) (l l' : E.I₀)
      (h : V ⟶ E.X l) (h' : V ⟶ E.X l'),
      lcRes (pullback.lift g h (hom_ext_final _ _) : V ⟶ memberProd E W l)
        (d l) =
      lcRes (pullback.lift g h' (hom_ext_final _ _) : V ⟶ memberProd E W l')
        (d l') := by
    intro V g l l' h h'
    have h1 := k.2 V l l' (pullback.lift g h (hom_ext_final _ _))
      (pullback.lift g h' (hom_ext_final _ _)) (by rw [pullback.lift_fst, pullback.lift_fst])
    have h2 := k'.2 V l l' (pullback.lift g h (hom_ext_final _ _))
      (pullback.lift g h' (hom_ext_final _ _)) (by rw [pullback.lift_fst, pullback.lift_fst])
    simp only [d, lcRes_sub, h1, h2]
    abel
  obtain ⟨m, hm⟩ := exists_lcRes_eq_of_mem (hE W)
    (fun V g hg ↦ lcRes (pullback.lift g hg.choose_spec.some (hom_ext_final _ _) :
      V ⟶ memberProd E W hg.choose) (d hg.choose))
    (fun V V' g e hg ↦ by
      rw [← lcRes_comp]
      have : e ≫ (pullback.lift g hg.choose_spec.some (hom_ext_final _ _) :
          V ⟶ memberProd E W hg.choose) =
          pullback.lift (e ≫ g) (e ≫ hg.choose_spec.some) (hom_ext_final _ _) :=
        pullback.hom_ext (by rw [Category.assoc, pullback.lift_fst, pullback.lift_fst])
          (by rw [Category.assoc, pullback.lift_snd, pullback.lift_snd])
      rw [this]
      exact hd _ _ _ _ _ _)
  have hfst : ∀ l, lcRes (pullback.fst _ _ : memberProd E W l ⟶ W) m =
      d l := by
    intro l
    rw [hm (pullback.fst _ _) ⟨l, ⟨pullback.snd _ _⟩⟩, hd _ _ _ l _ (pullback.snd _ _),
      pullback.lift_fst_snd, lcRes_id]
  refine ⟨toAddSection.symm m, Subtype.ext (funext fun l ↦ ?_), fun g' hg' ↦ ?_⟩
  · change k.1 l - lcRes _ (toAddSection (toAddSection.symm m)) = k'.1 l
    rw [Equiv.apply_symm_apply, hfst]
    exact sub_sub_cancel _ _
  · apply toAddSection.injective
    rw [Equiv.apply_symm_apply]
    refine lcRes_injective_of_mem (hE W) fun V e ⟨l, ⟨h⟩⟩ ↦ ?_
    have he : e = (pullback.lift e h (hom_ext_final _ _) :
        V ⟶ memberProd E W l) ≫ pullback.fst _ _ :=
      (pullback.lift_fst _ _ _).symm
    rw [he, lcRes_comp, lcRes_comp, hfst]
    congr 1
    have := congrArg (fun k ↦ k.1 l) hg'
    change k.1 l - lcRes _ (toAddSection g') = k'.1 l at this
    simp only [d, ← this, sub_sub_cancel]

lemma lift_comp_memberProdMap {V W : SmallNoetherianSeparatedEtale B S hS} (l : E.I₀)
    (h : V ⟶ memberProd E W l) {V' : SmallNoetherianSeparatedEtale B S hS} (e : V' ⟶ V) :
    (pullback.lift (𝟙 V') (e ≫ h ≫ pullback.snd _ _) (hom_ext_final _ _) :
        V' ⟶ memberProd E V' l) ≫ memberProdMap e l =
      e ≫ (pullback.lift (𝟙 V) (h ≫ pullback.snd _ _) (hom_ext_final _ _) :
        V ⟶ memberProd E V l) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, memberProdMap_fst]
    erw [pullback.lift_fst_assoc, pullback.lift_fst]
    rw [Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, memberProdMap_snd]
    erw [pullback.lift_snd, pullback.lift_snd]

lemma lift_comp_memberProdMap_fst {V W : SmallNoetherianSeparatedEtale B S hS} (l : E.I₀)
    (h : V ⟶ memberProd E W l) :
    (pullback.lift (𝟙 V) (h ≫ pullback.snd _ _) (hom_ext_final _ _) :
        V ⟶ memberProd E V l) ≫ memberProdMap (h ≫ pullback.fst _ _) l = h := by
  apply pullback.hom_ext
  · simp only [Category.assoc, memberProdMap_fst]
    erw [pullback.lift_fst_assoc]
    rw [Category.id_comp]
  · simp only [Category.assoc, memberProdMap_snd]
    erw [pullback.lift_snd]

/-- **The torsor of a cocycle is a sheaf**, because `F_S` is. -/
lemma isSheaf_cocyclePresheaf : Presheaf.IsSheaf (topology B S hS) (cocyclePresheaf A c) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro W R hR x hx
  rw [Presieve.compatible_iff_sieveCompatible] at hx
  have hxc : ∀ {V : SmallNoetherianSeparatedEtale B S hS} {g g' : V ⟶ W} (_ : g = g')
      (hg : R g) (hg' : R g'), x g hg = x g' hg' := by
    rintro V g _ rfl hg hg'
    rfl
  let y : ∀ (l : E.I₀) ⦃V : SmallNoetherianSeparatedEtale B S hS⦄ (h : V ⟶ memberProd E W l),
      (R.pullback (pullback.fst _ _)) h → LocallyConstant ((toScheme B S hS).obj V) A :=
    fun l V h hh ↦ lcRes (pullback.lift (𝟙 V) (h ≫ pullback.snd _ _) (hom_ext_final _ _) :
      V ⟶ memberProd E V l) ((x (h ≫ pullback.fst _ _) hh).1 l)
  have hy : ∀ (l : E.I₀) ⦃V V' : SmallNoetherianSeparatedEtale B S hS⦄
      (h : V ⟶ memberProd E W l) (e : V' ⟶ V) (hh : (R.pullback (pullback.fst _ _)) h),
      y l (e ≫ h) ((R.pullback (pullback.fst _ _)).downward_closed hh e) = lcRes e (y l h hh) := by
    intro l V V' h e hh
    simp only [y]
    erw [hxc (Category.assoc e h _) _ (R.downward_closed hh e)]
    rw [hx _ e hh, cocyclePresheaf_map_val, ← lcRes_comp, ← lcRes_comp,
      ← lift_comp_memberProdMap]
    simp only [Category.assoc]
  choose z hz using fun l ↦ exists_lcRes_eq_of_mem
    ((topology B S hS).pullback_stable (pullback.fst _ _ : memberProd E W l ⟶ W) hR) (y l) (hy l)
  have hzc : IsCocycleSection c W z := by
    intro V l m a b hab
    refine lcRes_injective_of_mem ((topology B S hS).pullback_stable
      (a ≫ pullback.fst _ _) hR) fun V' e he ↦ ?_
    have ha : (R.pullback (pullback.fst _ _)) (e ≫ a) := by
      change R ((e ≫ a) ≫ pullback.fst _ _)
      rw [Category.assoc]
      exact he
    have hb : (R.pullback (pullback.fst _ _)) (e ≫ b) := by
      change R ((e ≫ b) ≫ pullback.fst _ _)
      rw [Category.assoc, ← hab]
      exact he
    rw [← lcRes_comp, lcRes_add, ← lcRes_comp]
    erw [← lcRes_comp]
    rw [hz l (e ≫ a) ha, hz m (e ≫ b) hb]
    simp only [y]
    erw [hxc (show (e ≫ b) ≫ pullback.fst _ _ = (e ≫ a) ≫ pullback.fst _ _ by
      simp only [Category.assoc, hab]) hb ha]
    have key := (x ((e ≫ a) ≫ pullback.fst _ _) ha).2 V' l m
      (pullback.lift (𝟙 V') ((e ≫ a) ≫ pullback.snd _ _) (hom_ext_final _ _))
      (pullback.lift (𝟙 V') ((e ≫ b) ≫ pullback.snd _ _) (hom_ext_final _ _))
      (by erw [pullback.lift_fst, pullback.lift_fst])
    erw [pullback.lift_snd, pullback.lift_snd] at key
    refine key.trans (congrArg _ ?_)
    rw [← lcRes_comp_cochain, pairLift_comp]
    simp only [Category.assoc]
  refine ⟨⟨z, hzc⟩, fun V g hg ↦ ?_, fun t' ht' ↦ ?_⟩
  · refine Subtype.ext (funext fun l ↦ ?_)
    change lcRes (memberProdMap g l) (z l) = (x g hg).1 l
    have hm : (R.pullback (pullback.fst _ _)) (memberProdMap g l) := by
      change R (memberProdMap g l ≫ pullback.fst _ _)
      rw [memberProdMap_fst]
      exact R.downward_closed hg _
    rw [hz l _ hm]
    simp only [y]
    rw [hxc (memberProdMap_fst g l) hm (R.downward_closed hg _), hx _ _ hg,
      cocyclePresheaf_map_val, ← lcRes_comp]
    convert lcRes_id _ using 2
    apply pullback.hom_ext
    · simp only [Category.assoc, memberProdMap_fst]
      erw [pullback.lift_fst_assoc]
    · simp only [Category.assoc, memberProdMap_snd]
      erw [pullback.lift_snd]
      exact (Category.id_comp _).symm
  · refine Subtype.ext (funext fun l ↦ ?_)
    refine lcRes_injective_of_mem ((topology B S hS).pullback_stable
      (pullback.fst _ _ : memberProd E W l ⟶ W) hR) fun V h hh ↦ ?_
    rw [hz l h hh]
    simp only [y]
    rw [← ht' _ hh, cocyclePresheaf_map_val, ← lcRes_comp, lift_comp_memberProdMap_fst]

lemma cocycleAct_one (W : SmallNoetherianSeparatedEtale B S hS) (k : CocycleSection A c W) :
    cocycleAct c W 1 k = k :=
  Subtype.ext (funext fun l ↦ by
    rw [cocycleAct_val, toAddSection_one, lcRes_zero, sub_zero])

variable (hc : c ∈ Stacks.CechSite.cocycles1 E (locallyConstantPresheafAb B S hS A))

include hE in
/-- **The torsor of a cocycle** `σ`: over `W` the families `k_l ∈ F_S(W ×_S V_l)` with
`k_l = k_m + σ_{lm}`, with `F_S(W)` acting by translation. -/
noncomputable def cocycleTorsor : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A) where
  presheaf := cocyclePresheaf A c
  isSheaf := isSheaf_cocyclePresheaf c
  act U g k := cocycleAct c U.unop g k
  one_act U k := cocycleAct_one c U.unop k
  mul_act U g h k := Subtype.ext (funext fun l ↦ by
    change k.1 l - lcRes (pullback.fst _ _) (toAddSection (g * h)) =
      (k.1 l - lcRes (pullback.fst _ _) (toAddSection h)) -
        lcRes (pullback.fst _ _) (toAddSection g)
    rw [toAddSection_mul, lcRes_add]
    abel)
  naturality f g k := Subtype.ext (funext fun l ↦ by
    change lcRes (memberProdMap f.unop l) (k.1 l - lcRes (pullback.fst _ _) (toAddSection g)) =
      lcRes (memberProdMap f.unop l) (k.1 l) - lcRes (pullback.fst _ _)
        (toAddSection ((constantGroupSheaf B S hS A).presheaf.map f g))
    rw [lcRes_sub, ← lcRes_comp, memberProdMap_fst, lcRes_comp]
    rfl)
  simplyTransitive U _ k k' := cocycleAct_simplyTransitive hE c U.unop k k'

include hc in
/-- The section `(σ_{ln})_l` of the torsor of a cocycle over the member `V_n`. -/
noncomputable def cocycleSection (n : E.I₀) : CocycleSection A c (E.X n) :=
  ⟨fun l ↦ lcRes (pairLift E (pullback.snd _ _) (pullback.fst _ _)) (c ![l, n]),
    fun V l m a b hab ↦ by
      rw [← lcRes_comp_cochain, ← lcRes_comp_cochain, pairLift_comp, pairLift_comp, ← hab]
      exact cocycle_lcRes hc _ _ _⟩

include hc in
lemma isTorsor_cocycleTorsor : (cocycleTorsor hE c).IsTorsor := by
  intro U
  refine ⟨memberSieveOf E U, hE U, fun V f ⟨k, ⟨h⟩⟩ ↦ ⟨(cocycleSection c hc k).map c h⟩⟩

/-- The sections `(σ_{ln})_l` of the torsor of a cocycle `σ` have transition cochain `σ`. -/
theorem transitionCochain_cocycleTorsor :
    transitionCochain (cocycleTorsor hE c) E (fun n ↦ cocycleSection c hc n) = c := by
  funext ν
  have key : (cocycleTorsor hE c).act _ (toAddSection.symm (c ν))
      (restrictToProduct (cocycleTorsor hE c) E (fun n ↦ cocycleSection c hc n) ν 1) =
      restrictToProduct (cocycleTorsor hE c) E (fun n ↦ cocycleSection c hc n) ν 0 := by
    refine Subtype.ext (funext fun l ↦ ?_)
    change lcRes (memberProdMap (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 1).left l)
        (lcRes (pairLift E (pullback.snd _ _) (pullback.fst _ _)) (c ![l, ν 1])) -
        lcRes (pullback.fst _ _) (toAddSection (toAddSection.symm (c ν))) =
      lcRes (memberProdMap (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 0).left l)
        (lcRes (pairLift E (pullback.snd _ _) (pullback.fst _ _)) (c ![l, ν 0]))
    rw [← lcRes_comp_cochain, ← lcRes_comp_cochain, pairLift_comp, pairLift_comp]
    erw [memberProdMap_snd, memberProdMap_snd, memberProdMap_fst, memberProdMap_fst]
    erw [Equiv.apply_symm_apply,
      cocycle_lcRes hc (pullback.snd _ _)
        (pullback.fst _ _ ≫ (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 0).left)
        (pullback.fst _ _ ≫ (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 1).left)]
    have hν : lcRes (pairLift E (pullback.fst _ _ ≫ (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 0).left)
        (pullback.fst _ _ ≫ (Pi.π (fun a ↦ Over.mk (E.f (ν a))) 1).left)
        : memberProd E _ l ⟶ _) (c ![ν 0, ν 1]) = lcRes (pullback.fst _ _) (c ν) := by
      refine lcRes_cochain_congr c (by funext j; fin_cases j <;> rfl) _ _ fun j ↦ ?_
      fin_cases j
      · exact heq_of_eq (pairLift_fst E _ _)
      · exact heq_of_eq (pairLift_snd E _ _)
    erw [hν]
    abel
  change toAddSection ((cocycleTorsor hE c).diff _ _) = c ν
  rw [← (cocycleTorsor hE c).eq_diff key]
  exact Equiv.apply_symm_apply _ _

end CocycleTorsorCovering

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [IsNoetherian S] [S.IsSeparated] {A : Type w} [AddCommGroup A]

/-- **Surjectivity of `κ`.** Every Čech class is the class of a torsor. -/
theorem exists_torsorCechClass_eq
    (x : cechCohomologyOfObject (final B S hS) (locallyConstantPresheafAb B S hS A) 1) :
    ∃ (T : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A)) (hT : T.IsTorsor),
      torsorCechClass T hT = x := by
  obtain ⟨𝔙, z, rfl⟩ := exists_cechClass_eq _ 1 x
  have hc := (mem_cechCycles_iff_cochainEquiv _ z.1).mp z.2
  refine ⟨cocycleTorsor (memberSieveOf_mem 𝔙) (cochainEquiv A _ 1 z.1),
    isTorsor_cocycleTorsor (memberSieveOf_mem 𝔙) _ hc, ?_⟩
  rw [torsorCechClass_eq _ _ 𝔙 (fun n ↦ cocycleSection _ hc n)]
  congr 1
  apply Subtype.ext
  apply (cochainEquiv A _ 1).injective
  exact (cochainEquiv_transitionCycle _ 𝔙 _).trans (transitionCochain_cocycleTorsor _ _ hc)

/-- **Torsors and the first Čech cohomology** (FK I.2). Let `S` be a noetherian separated scheme
and `F` an abelian group. There is a bijection `κ` from the set of isomorphism classes of
`F_S`-torsors to `Ȟ¹(S, F_S)` such that for every torsor `𝒢`, every étale covering
`𝔙 = (V_l → S)_l`, all sections `t_l ∈ 𝒢(V_l)` and every family `σ = (σ_{lm})`,
`σ_{lm} ∈ F_S(V_l ×_S V_m)`, with `(t_l|_{V_l ×_S V_m}) ^ σ_{lm} = t_m|_{V_l ×_S V_m}` for all
`l, m`, the family `σ` is a `1`-cocycle and `κ[𝒢] = [σ]_𝔙`. -/
@[weil "lem_fk102_torsors_eq_cech_h1"]
theorem exists_torsorClasses_equiv_cechCohomologyOfObject :
    ∃ κ : SheafOfGroups.TorsorClasses.{max u w} (constantGroupSheaf B S hS A) ≃
        cechCohomologyOfObject (final B S hS) (locallyConstantPresheafAb B S hS A) 1,
      ∀ (T : PseudoTorsor.{max u w} (constantGroupSheaf B S hS A)) (hT : T.IsTorsor)
        (𝔙 : CechCovering (final B S hS)) (t : ∀ l, T.presheaf.obj (op (𝔙.X l)))
        (σ : (cechComplex 𝔙.toPreZeroHypercover (locallyConstantPresheafAb B S hS A)).X 1),
        (∀ ν : Fin 2 → Fin 𝔙.n, T.toRightAction.act _
            (T.presheaf.map (Pi.π (fun a ↦ Over.mk (𝔙.f (ν a))) 0).left.op (t (ν 0)))
            (toAddSection.symm (Pi.π (Stacks.CechSite.cochainFactor 𝔙.toPreZeroHypercover
              (locallyConstantPresheafAb B S hS A) 1) ν σ)) =
          T.presheaf.map (Pi.π (fun a ↦ Over.mk (𝔙.f (ν a))) 1).left.op (t (ν 1))) →
        ∃ hσ : σ ∈ cechCycles 𝔙.toPreZeroHypercover (locallyConstantPresheafAb B S hS A) 1,
          κ (SheafOfGroups.TorsorClasses.mk T hT) =
            cechClass (locallyConstantPresheafAb B S hS A) 1 𝔙 ⟨σ, hσ⟩ := by
  let κ₀ : SheafOfGroups.TorsorClasses.{max u w} (constantGroupSheaf B S hS A) →
      cechCohomologyOfObject (final B S hS) (locallyConstantPresheafAb B S hS A) 1 :=
    Quotient.lift (fun T ↦ torsorCechClass T.1 T.2)
      (fun T T' ⟨e, _⟩ ↦ torsorCechClass_eq_of_hom T.2 T'.2 e)
  have hκ₀ : Function.Bijective κ₀ := by
    refine ⟨fun a b hab ↦ ?_, fun x ↦ ?_⟩
    · induction a using Quotient.inductionOn with | h T => ?_
      induction b using Quotient.inductionOn with | h T' => ?_
      obtain ⟨e⟩ := nonempty_hom_of_torsorCechClass_eq T.2 T'.2 hab
      exact SheafOfGroups.TorsorClasses.mk_eq_mk_of_hom T.2 T'.2 e
    · obtain ⟨T, hT, rfl⟩ := exists_torsorCechClass_eq x
      exact ⟨SheafOfGroups.TorsorClasses.mk T hT, rfl⟩
  refine ⟨Equiv.ofBijective κ₀ hκ₀, fun T hT 𝔙 t σ hσ ↦ ?_⟩
  have heq : σ = (transitionCycle T 𝔙 t).1 := by
    apply (cochainEquiv A _ 1).injective
    refine Eq.trans ?_ (cochainEquiv_transitionCycle T 𝔙 t).symm
    funext ν
    have h := T.eq_diff (hσ ν)
    have h' := (inv_eq_iff_eq_inv.mp h).trans (T.diff_comm _ _).symm
    exact (Equiv.apply_symm_apply toAddSection _).symm.trans (congrArg toAddSection h')
  refine ⟨heq ▸ (transitionCycle T 𝔙 t).2, ?_⟩
  change torsorCechClass T hT = _
  rw [torsorCechClass_eq T hT 𝔙 t]
  congr 1
  exact Subtype.ext heq.symm

end AlgebraicGeometry.SmallNoetherianSeparatedEtale
