module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.LAdicSheaves
public import Weil.Defs.CategoryTheory.ObjectProperty.LAdicSystem
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.StalkSystem

/-!
# The stalks of an `l`-adic sheaf form an `l`-adic system

Let `X` be a scheme, `l` a natural number and `F = (F_n, u_n)_{n ∈ ℤ}` an `l`-adic sheaf on the
small étale site of `X`: every `F_n` is constructible, `F_n = 0` for `n < 0`, `l^{n+1} F_n = 0`
for `n ≥ 0`, and `u_{n+1}` exhibits `F_n` as `F_{n+1}/l^{n+1}F_{n+1}`. For a geometric point `s`
of `X`, the system of stalks `F_{•,s} = (F_{n,s}, (u_n)_s)_n` is then an `l`-adic system of
`ℤ`-modules. Indeed `F_{n,s} = 0` for `n < 0`; taking stalks is additive and commutes with
cokernels, so `l^{n+1}` kills `F_{n,s}` and `(u_{n+1})_s` is surjective with kernel
`l^{n+1}F_{n+1,s}`; and the stalks of the constructible sheaf `F_n` are finite, hence of finite
length over `ℤ`.

## Main results

* `AlgebraicGeometry.SmallEtale.IsLAdicSheaf.isLAdicSystem_stalkSystem_obj`: the system of
  stalks of an `l`-adic sheaf at a geometric point is an `l`-adic system.

## Implementation notes

The stalk is the fiber functor of the point of the small étale site attached to the geometric
point, and the abelian sheaves take values in the universe of the schemes, as for the system of
stalks `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.stalkSystem`. The finiteness of
the stalks of a constructible abelian sheaf is proved here for sheaves in that universe: at a
geometric point lying over a stratum on which the sheaf is finite locally constant, the stalk is
the stalk of the restriction to the stratum (Stacks, Tag 03Q1), and the stalk of a finite
locally constant sheaf is the image of its finite local value.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12][FreitagKiehl]
* [Stacks Project, Tag 03UQ](https://stacks.math.columbia.edu/tag/03UQ)
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The stalk of a finite locally constant abelian sheaf at a geometric point is finite: it is
the image of the finite value of the sheaf on a member of a trivializing covering through which
the point lifts. -/
private theorem finite_sheafFiber_of_isFiniteLocallyConstant
    (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})
    [hG : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS) G]
    (s : GeometricPoint S) :
    Finite (((geometricPointSitePoint B S hS s).sheafFiber (A := AddCommGrpCat.{u})).obj G) := by
  let Φ := geometricPointSitePoint B S hS s
  let J := SmallEtale.topology B S hS
  obtain ⟨I, X, f, hcov, hconst⟩ := hG.exists_finite_cover (SmallEtale.final B S hS)
  obtain ⟨W, g, hg, w, -⟩ := Φ.jointly_surjective _ hcov
    (Φ.uniqueFiberObj (SmallEtale.final B S hS) (SmallEtale.finalIsTerminal B S hS)).default
  obtain ⟨-, k, -, ⟨i⟩, rfl⟩ := hg
  obtain ⟨E, hE, ⟨ε⟩⟩ := hconst i
  let x := Φ.fiber.map k w
  let O : Over (X i) := Over.mk (𝟙 (X i))
  let σ : E → G.obj.obj (op (X i)) := fun e =>
    ε.hom.hom.app (op O) ((toSheafify (J.over (X i)) ((Functor.const _).obj E)).app (op O) e)
  refine Finite.of_surjective (fun e => Φ.toPresheafFiber (X i) x G.obj (σ e)) ?_
  intro p
  obtain ⟨Y, y, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
  obtain ⟨⟨V, v⟩, ⟨a, ha⟩, ⟨b, hb⟩, -⟩ :=
    IsCofilteredOrEmpty.cone_objs (C := Φ.fiber.Elements) ⟨Y, y⟩ ⟨X i, x⟩
  dsimp only at a b ha hb
  rw [← ha, ← GrothendieckTopology.Point.toPresheafFiber_w_apply]
  let Vo : Over (X i) := Over.mk b
  let z' : (((J.overPullback AddCommGrpCat.{u} (X i)).obj G).obj.obj (op Vo)) :=
    G.obj.map a.op z
  let q := ε.inv.hom.app (op Vo) z'
  have hR := Presheaf.imageSieve_mem (J.over (X i))
    (toSheafify (J.over (X i)) ((Functor.const _).obj E)) q
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨V', g', hg', v', hv'⟩ := Φ.jointly_surjective _ hR v
  rw [Sieve.overEquiv_iff] at hg'
  obtain ⟨t, ht⟩ := hg'
  refine ⟨t, ?_⟩
  let m : Over.mk (g' ≫ b) ⟶ Vo := Over.homMk g'
  let m₂ : Over.mk (g' ≫ b) ⟶ O := Over.homMk (g' ≫ b)
  have hz' : ε.hom.hom.app (op Vo) q = z' := by
    simp only [q]
    exact ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.hom.app (op Vo)) ε.inv_hom_id) z'
  have key : G.obj.map g'.op z' = G.obj.map (g' ≫ b).op (σ t) := by
    have h1 : G.obj.map g'.op z' =
        ε.hom.hom.app (op (Over.mk (g' ≫ b)))
          ((sheafify (J.over (X i)) ((Functor.const _).obj E)).map m.op q) := by
      rw [← hz']
      exact (NatTrans.naturality_apply ε.hom.hom m.op q).symm
    have h2 : (toSheafify (J.over (X i)) ((Functor.const _).obj E)).app
        (op (Over.mk (g' ≫ b))) t =
        (sheafify (J.over (X i)) ((Functor.const _).obj E)).map m₂.op
          ((toSheafify (J.over (X i)) ((Functor.const _).obj E)).app (op O) t) :=
      NatTrans.naturality_apply (toSheafify (J.over (X i)) ((Functor.const _).obj E)) m₂.op t
    rw [h1, ← ht]
    erw [h2]
    exact NatTrans.naturality_apply ε.hom.hom m₂.op _
  rw [← hv', ← GrothendieckTopology.Point.toPresheafFiber_w_apply]
  change _ = (Φ.toPresheafFiber V' v' G.obj) (G.obj.map g'.op z')
  rw [key, GrothendieckTopology.Point.toPresheafFiber_w_apply]
  have hx : Φ.fiber.map (g' ≫ b) v' = x := by
    rw [Functor.map_comp, types_comp_apply, hv', hb]
  rw [hx]

section Constructible

variable (X : B.Scheme)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u}]

/-- The stalks of a constructible abelian sheaf at the geometric points are finite. -/
private theorem finite_sheafFiber_of_isConstructibleAbelianSheaf
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u})
    (hG : IsConstructibleAbelianSheaf B X G) (t : GeometricPoint X.obj) :
    Finite (((geometricPointSitePoint B X.obj X.property t).sheafFiber
      (A := AddCommGrpCat.{u})).obj G) := by
  obtain ⟨U, hU⟩ : ∃ U : X.obj.affineOpens, t.hom default ∈ (U.1 : Set X.obj) := by
    have h : t.hom default ∈ (⊤ : X.obj.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X.obj] at h
    exact TopologicalSpace.Opens.mem_iSup.mp h
  obtain ⟨s, hs⟩ := hG U
  obtain ⟨i, z, hz⟩ : ∃ (i : Fin s.n) (z : (s.piece i).obj),
      (B.inclusion.map (s.inclusion i)).base z = t.hom default := by
    have hx : t.hom default ∈ ⋃ i, Set.range (B.inclusion.map (s.inclusion i)).base := by
      rwa [← s.covers]
    exact Set.mem_iUnion.mp hx
  let t' := GeometricPoint.ofPoint (s.piece i).obj z
  have hbase : (t'.map (B.inclusion.map (s.inclusion i))).hom default = t.hom default := by
    change (B.inclusion.map (s.inclusion i)).base (t'.hom default) = t.hom default
    rwa [show t'.hom default = z from GeometricPoint.ofPoint_liesOver (s.piece i).obj z]
  have hfin := @finite_sheafFiber_of_isFiniteLocallyConstant B (s.piece i).obj
    (s.piece i).property _ (hs i) t'
  let e := (smallEtalePullbackSheafFiberIso B (s.inclusion i) t' AddCommGrpCat.{u}).app G ≪≫
    (etaleStalkPresheafFunctorIsoOfEqBase B X.obj X.property hbase AddCommGrpCat.{u}).app G.obj
  exact @Finite.of_equiv _ _ hfin ((forget AddCommGrpCat.{u}).mapIso e).toEquiv

/-- **The system of stalks of an `l`-adic sheaf is an `l`-adic system.** For an `l`-adic sheaf
`F` on the small étale site of `X` and a geometric point `s` of `X`, the projective system of
stalks `F_{•,s}` is an `l`-adic system of `ℤ`-modules. -/
@[weil "lem_fk112_stalk_of_l_adic_is_l_adic"]
theorem SmallEtale.IsLAdicSheaf.isLAdicSystem_stalkSystem_obj {l : ℕ}
    {F : SmallEtale.LTorsionProjectiveSystem.{u} B X.obj X.property l}
    (hF : SmallEtale.IsLAdicSheaf B X l F) (s : GeometricPoint X.obj) :
    ((SmallEtale.LTorsionProjectiveSystem.stalkSystem s).obj F).IsLAdicSystem := by
  let K := SmallEtale.sheafFiberInt B X.obj X.property s
  have : PreservesColimitsOfSize.{0, 0}
      ((geometricPointSitePoint B X.obj X.property s).sheafFiber (A := AddCommGrpCat.{u})) :=
    inferInstance
  have : PreservesColimitsOfSize.{0, 0} Stacks.InjectiveAcyclic.ofAb.{u} :=
    Stacks.InjectiveAcyclic.ofAbAdj.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} K := inferInstanceAs
    (PreservesColimitsOfSize.{0, 0} ((geometricPointSitePoint B X.obj X.property s).sheafFiber ⋙
      Stacks.InjectiveAcyclic.ofAb.{u}))
  have hzero : ∀ n : ℕ, K.map ((l ^ (n + 1)) • 𝟙 (F.obj.obj (op ((n : ℤ) + 1)))) ≫
      K.map (F.obj.map (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op) = 0 := fun n => by
    rw [← K.map_comp, nsmul_id_comp_eq_zero _ _ (hF.nsmul_id_eq_zero n), K.map_zero]
  have hcok : ∀ n : ℕ, IsColimit (CokernelCofork.ofπ
      (K.map (F.obj.map (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op)) (hzero n)) := fun n =>
    CokernelCofork.mapIsColimit _ (hF.isColimit n).some K
  have hmap : ∀ (k : ℕ) (A : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u})
      (z : K.obj A), (K.map (k • 𝟙 A)).hom z = (k : ℤ) • z := by
    intro k A z
    rw [K.map_nsmul, K.map_id, natCast_zsmul]
    rfl
  have hpow : ∀ (n : ℕ) (x : ((SmallEtale.LTorsionProjectiveSystem.stalkSystem s).obj F).term n),
      (l : ℤ) ^ (n + 1) • x = 0 := by
    intro n x
    rw [← Nat.cast_pow]
    refine (hmap (l ^ (n + 1)) (F.obj.obj (op (n : ℤ))) x).symm.trans ?_
    rw [hF.nsmul_id_eq_zero n, K.map_zero]
    rfl
  refine ⟨fun n hn => K.map_isZero (hF.isZero_of_neg n hn), hpow, fun n => ?_,
    fun n => ?_, fun n => ?_⟩
  · exact (ModuleCat.epi_iff_surjective _).1 (epi_of_isColimit_cofork (hcok n))
  · refine le_antisymm (fun x hx => ?_) ?_
    · have hS := ShortComplex.exact_of_g_is_cokernel
        (ShortComplex.mk (K.map ((l ^ (n + 1)) • 𝟙 (F.obj.obj (op ((n : ℤ) + 1)))))
          (K.map (F.obj.map (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op)) (hzero n)) (hcok n)
      obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hS x hx
      refine ⟨y, ?_⟩
      change (l : ℤ) ^ (n + 1) • y = x
      rw [← hy, ← Nat.cast_pow]
      exact (hmap _ _ y).symm
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      change (K.map (F.obj.map (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op)).hom
        ((l : ℤ) ^ (n + 1) • y) = 0
      exact ((K.map (F.obj.map (homOfLE (show (n : ℤ) ≤ n + 1 by omega)).op)).hom.map_smul
        _ y).trans (hpow n _)
  · have : Finite (((SmallEtale.LTorsionProjectiveSystem.stalkSystem s).obj F).term n) :=
      finite_sheafFiber_of_isConstructibleAbelianSheaf B X _ (hF.isConstructible n) s
    exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, isArtinian_of_finite⟩

end Constructible

end AlgebraicGeometry
