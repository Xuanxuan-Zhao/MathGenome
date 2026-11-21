import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.PunctureCompletion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.PuncturedDiskLoops
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.MapsMultiplicity
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Tactic.FunProp
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Maps.Proper.Basic

/-! d12:20-08: biholomorphic classification and completion over a puncture.
For disconnected finite coverings the completed atlas adds exactly one point
per monodromy cycle, with the cycle length as its ramification multiplicity.
-/
noncomputable section
open Set Topology

namespace D12Complex.Ch20.PunctureCompletion
open PuncturedDiskLoops ModelCoverings

/-- A formulation of the lifting criterion using actual monodromy on loops.
It is sufficient for every source loop to return the chosen point of the fiber. -/
lemma exists_lift_of_monodromy {A E B : Type*} [TopologicalSpace A]
    [TopologicalSpace E] [TopologicalSpace B] [PathConnectedSpace A]
    [LocallyPathConnectedSpace A] {p : E → B} (cov : IsCoveringMap p)
    (f : C(A, B)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀)
    (hfix : ∀ γ : Path a₀ a₀,
      cov.monodromy (.mk (γ.map f.continuous)) ⟨e₀, he⟩ = ⟨e₀, he⟩) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f := by
  apply cov.isLocalHomeomorph.existsUnique_continuousMap_lifts f a₀ e₀ he
  · intro γ hγ
    simpa [and_comm] using cov.exists_path_lifts (f.comp γ) e₀ (by simp [hγ, he])
  · intro γ γ' Γ Γ' γ₀ γ'₀ Γ₀ Γ'₀ Γ_lifts Γ'_lifts γγ'₁
    rw [(cov.eq_liftPath_iff' (by simp [γ₀, he])).mpr ⟨Γ_lifts, Γ₀⟩,
      (cov.eq_liftPath_iff' (by simp [γ'₀, he])).mpr ⟨Γ'_lifts, Γ'₀⟩]
    let g : Path a₀ (γ 1) := ⟨γ, γ₀, rfl⟩
    let g' : Path a₀ (γ 1) := ⟨γ', γ'₀, γγ'₁.symm⟩
    change (cov.monodromy (.mk (g.map f.continuous)) ⟨e₀, he⟩).1 =
      (cov.monodromy (.mk (g'.map f.continuous)) ⟨e₀, he⟩).1
    rw [← Subtype.ext_iff]
    apply (cov.monodromy_bijective (.mk (g'.map f.continuous).symm)).1
    simp_rw [← cov.monodromy_trans_apply, ← Path.Homotopic.Quotient.mk_trans]
    conv_rhs => rw [← Path.Homotopic.Quotient.eq.2 ⟨.reflTransSymm _⟩,
      Path.Homotopic.Quotient.mk_refl, cov.monodromy_refl]
    rw [Path.map_symm, ← Path.map_trans]
    exact hfix (g.trans g'.symm)

/-- A logarithmic straight segment gives a path between any two disk points;
no branch of the logarithm on the whole punctured disk is assumed. -/
def diskPath {r : ℝ} (hr : 0 < r) (a b : Disk r) : Path a b where
  toFun t := ⟨Complex.exp
    ((1 - (t : ℝ) : ℂ) * Complex.log (a : ℂ) +
      (t : ℝ) * Complex.log (b : ℂ)),
    affine_exp_mem hr _ _ (by rw [Complex.exp_log (norm_pos_iff.mp a.property.1)]; exact a.property.2)
      (by rw [Complex.exp_log (norm_pos_iff.mp b.property.1)]; exact b.property.2) t⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; simp [Complex.exp_log (norm_pos_iff.mp a.property.1)]
  target' := by apply Subtype.ext; simp [Complex.exp_log (norm_pos_iff.mp b.property.1)]

lemma disk_pathConnected {r : ℝ} (hr : 0 < r) : PathConnectedSpace (Disk r) := by
  have hn : Nonempty (Disk r) := ⟨⟨(r / 2 : ℝ), by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact ⟨half_pos hr, half_lt_self hr⟩⟩⟩
  exact ⟨hn, fun a b => ⟨diskPath hr a b⟩⟩

lemma disk_locallyPathConnected (r : ℝ) : LocallyPathConnectedSpace (Disk r) := by
  have hopen : IsOpen {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  exact hopen.locallyPathConnectedSpace

/-- Surjectivity of a lift between connected coverings follows by lifting a
path in the target and comparing the two projected lifts. -/
lemma covering_lift_surjective {A E B : Type*} [TopologicalSpace A]
    [TopologicalSpace E] [TopologicalSpace B] [Nonempty A] [PathConnectedSpace E]
    {q : A → B} {p : E → B} (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    {f : A → E} (hf : Continuous f) (hcomm : p ∘ f = q) : Function.Surjective f := by
  intro y
  let a : A := Classical.choice inferInstance
  let Γ : Path (f a) y := PathConnectedSpace.somePath (f a) y
  let γ := Γ.map hp.continuous
  obtain ⟨L, hLq, hL₀⟩ := hq.exists_path_lifts γ.toContinuousMap a (by
    change p (Γ 0) = q a
    rw [Γ.source]
    exact congrFun hcomm a)
  have heq : f ∘ L = Γ := by
    have hproj : p ∘ (f ∘ L) = p ∘ Γ := by
      funext t
      exact (congrFun hcomm (L t)).trans (congrFun hLq t)
    exact hp.eq_of_comp_eq (hf.comp L.continuous) Γ.continuous hproj 0
      (by change f (L 0) = Γ 0; rw [hL₀, Γ.source])
  exact ⟨L 1, (congrFun heq 1).trans Γ.target⟩

theorem equal_degree_lift_homeomorphism :
    Specs.D12Complex.Ch20.PunctureCompletion.equal_degree_lift_homeomorphism_type := by
  intro A E B _ _ _ _ _ q p hq hp m hm hqcard hpcard f hf hcomm
  let cq := CoveringPaths.covering_bridge q hq
  let cp := CoveringPaths.covering_bridge p hp
  have hsurj : Function.Surjective f := covering_lift_surjective cq cp hf hcomm
  have hinj : Function.Injective f := by
    intro x y hxy
    let b := q x
    have hy : q y = b := by
      exact (congrFun hcomm y).symm.trans
        ((congrArg p hxy.symm).trans (congrFun hcomm x))
    let F : (q ⁻¹' {b}) → (p ⁻¹' {b}) :=
      fun z => ⟨f z, (congrFun hcomm z).trans z.property⟩
    have hFsurj : Function.Surjective F := by
      intro z
      obtain ⟨a, ha⟩ := hsurj z
      refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
      exact (congrFun hcomm a).symm.trans ((congrArg p ha).trans z.property)
    let : Finite (q ⁻¹' {b}) := Nat.finite_of_card_ne_zero (by rw [hqcard]; exact hm.ne')
    have hFbij : Function.Bijective F :=
      (Nat.bijective_iff_surjective_and_card F).mpr
        ⟨hFsurj, (hqcard b).trans (hpcard b).symm⟩
    exact congrArg Subtype.val (hFbij.1
      (show F ⟨x, rfl⟩ = F ⟨y, hy⟩ from Subtype.ext hxy))
  have hlocal : IsLocalHomeomorph f :=
    (hcomm.symm ▸ cq.isLocalHomeomorph).of_comp cp.isLocalHomeomorph hf
  exact ⟨hlocal.toHomeomorphOfBijective ⟨hinj, hsurj⟩, rfl⟩

theorem rootRadius_pos {r : ℝ} (hr : 0 < r) (m : ℕ) : 0 < rootRadius r m :=
  Real.rpow_pos_of_pos hr _

theorem rootRadius_pow {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m) :
    (rootRadius r m) ^ m = r := by
  simpa [rootRadius, one_div] using Real.rpow_inv_natCast_pow hr.le hm.ne'

theorem norm_lt_rootRadius_iff {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m)
    (t : ℂ) : ‖t‖ < rootRadius r m ↔ ‖t ^ m‖ < r := by
  constructor
  · exact power_norm_bound hr hm
  · intro h
    apply (pow_lt_pow_iff_left₀ (norm_nonneg t) (rootRadius_pos hr m).le hm.ne').mp
    simpa only [rootRadius_pow hr hm, norm_pow] using h

lemma continuous_powerMap {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m) :
    Continuous (powerMap hr hm) :=
  (continuous_subtype_val.pow m).subtype_mk _

/-- Identify the base disk with the open subset of the punctured plane. -/
def diskInPlane (r : ℝ) : Disk r ≃ₜ {z : PuncturedPlane // ‖(z : ℂ)‖ < r} where
  toFun z := ⟨⟨z, norm_pos_iff.mp z.property.1⟩, z.property.2⟩
  invFun z := ⟨z.val, norm_pos_iff.mpr z.val.property, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The source disk is precisely the preimage of the smaller base disk under
the punctured-plane power covering. -/
def sourceInPlane {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m) :
    Disk (rootRadius r m) ≃ₜ
      {z : PuncturedPlane // ‖((powerProjection m z) : ℂ)‖ < r} where
  toFun z := ⟨⟨z, norm_pos_iff.mp z.property.1⟩, power_norm_bound hr hm z.property.2⟩
  invFun z := ⟨z.val, norm_pos_iff.mpr z.val.property,
    (norm_lt_rootRadius_iff hr hm _).mpr z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem power_model_covering {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m) :
    IsCovering (powerMap hr hm) := by
  have cov := CoveringPaths.covering_bridge (powerProjection m) (power_covering m hm).2.1
  let U : Set PuncturedPlane := {z | ‖(z : ℂ)‖ < r}
  have hcov := ((cov.restrictPreimage U).comp_homeomorph (sourceInPlane hr hm)).homeomorph_comp
    (diskInPlane r).symm
  exact covering_of_isCoveringMap _ hcov

/-- Every punctured-plane root of a point of the disk lies in the parameter
disk. Thus restricting the model does not lose any element of its fibers. -/
def powerFiberEquiv {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m) (b : Disk r) :
    {t : Disk (rootRadius r m) // powerMap hr hm t = b} ≃
      {t : PuncturedPlane // powerProjection m t = puncturedInclusion b} where
  toFun t := ⟨puncturedInclusion t.val,
    Subtype.ext (congrArg (fun z : Disk r => (z : ℂ)) t.property)⟩
  invFun t := ⟨⟨t.val, norm_pos_iff.mpr t.val.property, by
    apply (norm_lt_rootRadius_iff hr hm _).mpr
    have h := congrArg (fun z : PuncturedPlane => ‖(z : ℂ)‖) t.property
    exact h ▸ b.property.2⟩,
    Subtype.ext (congrArg (fun z : PuncturedPlane => (z : ℂ)) t.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem power_model_fiber_card {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m)
    (b : Disk r) :
    Nat.card {t : Disk (rootRadius r m) // powerMap hr hm t = b} = m := by
  rw [Nat.card_congr (powerFiberEquiv hr hm b)]
  exact power_fiber_card m hm (puncturedInclusion b)

/-- Multiplication of a logarithmic lift by `m` needs a constant adjustment:
the principal logarithm of `b^m` need not be `m * log b`. -/
theorem power_model_winding {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 0 < m)
    (b : Disk (rootRadius r m)) (γ : Path b b) (k : ℤ)
    (hk : HasWinding γ k) :
    HasWinding (γ.map (continuous_powerMap hr hm)) ((m : ℤ) * k) := by
  obtain ⟨L, hL₀, hL, hL₁⟩ := hk
  let c : ℂ := Complex.log ((b : ℂ) ^ m) - (m : ℂ) * Complex.log (b : ℂ)
  have hc : Complex.exp c = 1 := by
    rw [Complex.exp_sub, Complex.exp_nat_mul, Complex.exp_log
      (pow_ne_zero m (norm_pos_iff.mp b.property.1)),
      Complex.exp_log (norm_pos_iff.mp b.property.1)]
    exact div_self (pow_ne_zero m (norm_pos_iff.mp b.property.1))
  let M : C(unitInterval, ℂ) := ⟨fun t => (m : ℂ) * L t + c, by fun_prop⟩
  refine ⟨M, ?_, ?_, ?_⟩
  · change (m : ℂ) * L 0 + c = Complex.log ((b : ℂ) ^ m)
    rw [hL₀]
    dsimp [c]
    ring
  · intro t
    change Complex.exp ((m : ℂ) * L t + c) = (γ t : ℂ) ^ m
    rw [Complex.exp_add, hc, mul_one, Complex.exp_nat_mul, hL]
  · change (m : ℂ) * L 1 + c = Complex.log ((b : ℂ) ^ m) +
      (((m : ℤ) * k : ℤ) : ℂ) * period
    rw [hL₁]
    dsimp [c]
    push_cast
    ring

/-- Winding multiplication and the full monodromy cycle make all parameter
loops lift closed. The covering lifting criterion then constructs the global
map, and equal finite degrees make it a homeomorphism. -/
theorem topological_classification :
    Specs.D12Complex.Ch20.PunctureCompletion.topological_classification_type := by
  intro r hr E _ S p hp m hm hcard b e₀ he₀
  let : PathConnectedSpace E := Surfaces.surface_pathConnected S
  let : PathConnectedSpace (Disk (rootRadius r m)) := disk_pathConnected (rootRadius_pos hr m)
  let : LocallyPathConnectedSpace (Disk (rootRadius r m)) := disk_locallyPathConnected _
  let cov := CoveringPaths.covering_bridge p hp
  let q := powerMap hr hm
  let c := q b
  let τ := cov.monodromyPerm c (circleClass c 1)
  let : Finite (p ⁻¹' {c}) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hm.ne')
  let := Fintype.ofFinite (p ⁻¹' {c})
  have hτpow : τ ^ m = 1 := by
    have hfull := full_cycle_of_transitive τ (generator_transitive hr cov c)
    have hc : Fintype.card (p ⁻¹' {c}) = m := by
      simpa only [Nat.card_eq_fintype_card] using hcard c
    simpa only [hc] using hfull.1
  have hfix (γ : Path b b) :
      cov.monodromy (.mk (γ.map (continuous_powerMap hr hm))) ⟨e₀, he₀⟩ = ⟨e₀, he₀⟩ := by
    obtain ⟨k, hk, _⟩ := logarithmic_lift (rootRadius_pos hr m) b γ
    have hwind := power_model_winding hr hm b γ k hk
    have hclass : (CategoryTheory.End.of (.mk (γ.map (continuous_powerMap hr hm))) :
        FundamentalGroup (Disk r) c) = circleClass c 1 ^ ((m : ℤ) * k) := by
      rw [← circleClass_eq_zpow hr c]
      apply CategoryTheory.End.ext
      exact Quotient.sound ((classification hr c _ _ _ _ hwind
        (circleLoop_winding c ((m : ℤ) * k))).mpr rfl)
    change cov.monodromyPerm c
      (CategoryTheory.End.of (.mk (γ.map (continuous_powerMap hr hm)))) ⟨e₀, he₀⟩ = _
    rw [hclass, map_zpow]
    have htriv : τ ^ ((m : ℤ) * k) = 1 := by
      rw [zpow_mul, zpow_natCast, hτpow, one_zpow]
    change (τ ^ ((m : ℤ) * k)) ⟨e₀, he₀⟩ = _
    rw [htriv]
    rfl
  obtain ⟨F, hF, _⟩ := exists_lift_of_monodromy cov ⟨q, continuous_powerMap hr hm⟩ b e₀ he₀ hfix
  obtain ⟨h, hh⟩ := equal_degree_lift_homeomorphism q p (power_model_covering hr hm) hp
    m hm (power_model_fiber_card hr hm) hcard F F.continuous hF.2
  refine ⟨h, ?_, ?_⟩
  · exact (congrFun hh b).trans hF.1
  · rw [hh]
    exact hF.2

open Filter Surfaces

/-- A continuous nonzero root of a scalar holomorphic function is holomorphic.
This uses the derivative of the power map, not a presumed inverse sheet. -/
lemma scalarHolomorphic_of_power {E : Type*} [TopologicalSpace E]
    (S : RiemannSurface E) {g : E → ℂ} (hg : Continuous g)
    {m : ℕ} (hm : 0 < m) (hne : ∀ x, g x ≠ 0)
    (hp : ScalarHolomorphic S (fun x => (g x) ^ m)) : ScalarHolomorphic S g := by
  refine ⟨hg, fun e he => ⟨e.val.open_target, fun z hz => ?_⟩⟩
  have hc : ContinuousAt (g ∘ e.val.symm) z :=
    hg.continuousAt.comp (e.val.symm.continuousAt hz)
  have hd := (hp.2 e he).2 z hz
  have hpow : HasDerivAt (fun w : ℂ => w ^ m)
      ((m : ℂ) * (g (e.val.symm z)) ^ (m - 1)) (g (e.val.symm z)) :=
    hasDerivAt_pow m _
  exact (HasDerivAt.of_comp_left hc hpow hd.hasDerivAt
    (mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') (pow_ne_zero _ (hne _)))
      (Filter.Eventually.of_forall fun _ => rfl)).differentiableAt

/-- The exact local fiber count forces the derivative of an injective
holomorphic function to be nonzero. -/
lemma deriv_ne_zero_of_injOn {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (hinj : InjOn f Ω) {a : ℂ} (ha : a ∈ Ω) :
    deriv f a ≠ 0 := by
  have hnc : ¬ (∀ᶠ z in 𝓝 a, f z = f a) := by
    intro h
    have heq : ∀ᶠ z in 𝓝 a, z = a := by
      filter_upwards [h, hf.1.mem_nhds ha] with z hz hΩ
      exact hinj hΩ ha hz
    have hpunct : ∀ᶠ z in 𝓝[≠] a, z = a := heq.filter_mono nhdsWithin_le_nhds
    have hnot : ∀ᶠ z in 𝓝[≠] a, z ≠ a := self_mem_nhdsWithin
    exact (hpunct.and hnot).exists.elim (fun _ h => h.2 h.1)
  obtain ⟨m, hm, r, hr, U, φ, ψ, haU, hUΩ, hpair, hφ0, hform,
    himage, hcount, _, horder⟩ :=
      LocalMappingNormalForm.local_mapping_normal_form Ω f a hf ha hnc
  let w : ℂ := f a + (r ^ m / 2 : ℝ)
  have hwne : w ≠ f a := by
    simpa [w] using (show (r ^ m / 2 : ℝ) ≠ 0 from ne_of_gt (half_pos (pow_pos hr m)))
  have hw : w ∈ Metric.ball (f a) (r ^ m) := by
    simpa [w, Metric.mem_ball, dist_eq_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr] using
      half_lt_self (pow_pos hr m)
  have hc := (hcount w hw hwne).2
  have hs : {z : ℂ | z ∈ U ∧ f z = w}.Subsingleton := by
    intro x hx y hy
    exact hinj (hUΩ hx.1) (hUΩ hy.1) (hx.2.trans hy.2.symm)
  have hm1 : m = 1 := by
    have hle := (Set.ncard_le_one (hcount w hw hwne).1).mpr hs
    rw [hc] at hle
    omega
  apply centered_order_one_deriv_ne_zero ⟨Ω, ha, hf⟩
  simpa only [hm1, Nat.cast_one] using horder

/-- A holomorphic open partial homeomorphism of plane sets has a holomorphic
inverse. No derivative condition is added to the input. -/
lemma holomorphicOn_symm (e : OpenPartialHomeomorph ℂ ℂ)
    (he : HolomorphicOn e.source e) : HolomorphicOn e.target e.symm := by
  refine ⟨e.open_target, fun z hz => ?_⟩
  exact (e.hasDerivAt_symm hz
    (deriv_ne_zero_of_injOn he e.injOn (e.map_target hz))
    (he.2 _ (e.map_target hz)).hasDerivAt).differentiableAt

/-- The global parameter chart provided by a homeomorphism with a plane domain. -/
def parameterChart {E : Type*} [TopologicalSpace E] {Ω : Set ℂ}
    (hΩ : IsDomain Ω) (h : Ω ≃ₜ E) : ComplexChart E := by
  let c := h.symm.toOpenPartialHomeomorph.trans (planeChart Ω hΩ).val
  refine ⟨c, ?_⟩
  simpa [c, OpenPartialHomeomorph.trans_target, planeChart_target] using hΩ

lemma parameterChart_source {E : Type*} [TopologicalSpace E] {Ω : Set ℂ}
    (hΩ : IsDomain Ω) (h : Ω ≃ₜ E) :
    (parameterChart hΩ h).val.source = univ := by
  simp [parameterChart, planeChart_source]

lemma parameterChart_target {E : Type*} [TopologicalSpace E] {Ω : Set ℂ}
    (hΩ : IsDomain Ω) (h : Ω ≃ₜ E) :
    (parameterChart hΩ h).val.target = Ω := by
  simp [parameterChart, planeChart_target]

lemma parameterChart_apply {E : Type*} [TopologicalSpace E] {Ω : Set ℂ}
    (hΩ : IsDomain Ω) (h : Ω ≃ₜ E) (x : E) :
    (parameterChart hΩ h).val x = (h.symm x : ℂ) := by
  simp [parameterChart, planeChart_apply]

/-- A globally defined scalar holomorphic parameter that is a homeomorphism
is a chart compatible with the original complex structure. -/
lemma parameterChart_mem_maximalAtlas {E : Type*} [TopologicalSpace E]
    (S : RiemannSurface E) {Ω : Set ℂ} (hΩ : IsDomain Ω) (h : Ω ≃ₜ E)
    (hg : ScalarHolomorphic S (fun x => (h.symm x : ℂ))) :
    parameterChart hΩ h ∈ maximalAtlas S.atlas := by
  intro e he
  apply compatibleCharts_symm
  let t := e.val.symm.trans (parameterChart hΩ h).val
  have ht : HolomorphicOn t.source t := by
    refine ⟨t.open_source, fun z hz => ?_⟩
    have hh := (hg.2 e he).2 z hz.1
    simpa only [t, OpenPartialHomeomorph.coe_trans, Function.comp_def,
      parameterChart_apply] using hh
  exact ⟨ht, holomorphicOn_symm t ht, t.mapsTo, t.symm.mapsTo,
    t.leftInvOn, t.rightInvOn⟩

/-- Upgrade a scalar holomorphic homeomorphic parameter to both holomorphic
maps, using the standard plane structure on the parameter domain. -/
lemma biholomorphic_of_scalar_parameter {E : Type*} [TopologicalSpace E]
    (S : RiemannSurface E) {Ω : Set ℂ} (hΩ : IsDomain Ω) (h : Ω ≃ₜ E)
    (hg : ScalarHolomorphic S (fun x => (h.symm x : ℂ))) :
    ∃ T : RiemannSurface Ω,
      (∀ e ∈ T.atlas, ∀ t ∈ e.val.source, e.val t = (t : ℂ)) ∧
      HolomorphicMap T S h ∧ HolomorphicMap S T h.symm := by
  obtain ⟨T, hT⟩ := plane_domain_surface Ω hΩ
  let d := planeChart Ω hΩ
  let c := parameterChart hΩ h
  have hd : d ∈ maximalAtlas T.atlas := subset_maximalAtlas T.isAtlas (by simp [hT, d])
  have hc : c ∈ maximalAtlas S.atlas := parameterChart_mem_maximalAtlas S hΩ h hg
  have hds : d.val.source = univ := planeChart_source Ω hΩ
  have hcs : c.val.source = univ := parameterChart_source hΩ h
  refine ⟨T, ?_, ?_, ?_⟩
  · intro e he t _
    have heq : e = d := by simpa [hT, d] using he
    rw [heq]
    exact planeChart_apply Ω hΩ t
  · intro a
    apply (holomorphicMapAt_iff_chart T S h a d hd c hc
      (by rw [hds]; trivial) (by rw [hcs]; trivial)).mpr
    refine ⟨h.continuous.continuousAt, ?_⟩
    have hdΩ : d.val a ∈ Ω := by rw [planeChart_apply]; exact a.property
    refine (show HolomorphicGermAt id (d.val a) from
      ⟨univ, mem_univ _, isOpen_univ, fun _ _ => differentiableAt_id⟩).congr ?_
    filter_upwards [hΩ.2.1.mem_nhds hdΩ] with z hz
    change z = c.val (h (d.val.symm z))
    rw [parameterChart_apply, h.symm_apply_apply]
    exact (d.val.right_inv (by simpa [d, planeChart_target] using hz)).symm
  · intro a
    apply (holomorphicMapAt_iff_chart S T h.symm a c hc d hd
      (by rw [hcs]; trivial) (by rw [hds]; trivial)).mpr
    refine ⟨h.symm.continuous.continuousAt, ?_⟩
    have hcΩ : c.val a ∈ Ω := by rw [parameterChart_apply]; exact (h.symm a).property
    refine (show HolomorphicGermAt id (c.val a) from
      ⟨univ, mem_univ _, isOpen_univ, fun _ _ => differentiableAt_id⟩).congr ?_
    filter_upwards [hΩ.2.1.mem_nhds hcΩ] with z hz
    change z = d.val (h.symm (c.val.symm z))
    rw [planeChart_apply]
    rw [← parameterChart_apply hΩ h]
    exact (c.val.right_inv (by simpa [c, parameterChart_target] using hz)).symm

lemma disk_isDomain {r : ℝ} (hr : 0 < r) :
    IsDomain {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} := by
  let : PathConnectedSpace (Disk r) := disk_pathConnected hr
  have hc : IsConnected {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < r} :=
    isConnected_iff_connectedSpace.mpr (show ConnectedSpace (Disk r) from PathConnectedSpace.connectedSpace)
  exact ⟨hc.nonempty, (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const), hc.isPreconnected⟩

/-- The full connected analytic classification from the original holomorphic
covering, with no initial fiber point or inverse-sheet certificate assumed. -/
theorem connected_classification :
    Specs.D12Complex.Ch20.PunctureCompletion.connected_classification_type := by
  intro r hr E _ S p hp hhol m hm hcard
  let : PathConnectedSpace (Disk (rootRadius r m)) := disk_pathConnected (rootRadius_pos hr m)
  let b : Disk (rootRadius r m) := Classical.choice inferInstance
  have hn : Nonempty (p ⁻¹' {powerMap hr hm b}) :=
    (Nat.card_pos_iff.mp (show 0 < Nat.card (p ⁻¹' {powerMap hr hm b}) by
      rw [hcard]; exact hm)).1
  obtain ⟨e₀, he₀⟩ := Classical.choice hn
  obtain ⟨h, _, hcomm⟩ := topological_classification hr S p hp hm hcard b e₀ he₀
  have hg : ScalarHolomorphic S (fun x => (h.symm x : ℂ)) := by
    apply scalarHolomorphic_of_power S (continuous_subtype_val.comp h.symm.continuous) hm
      (fun x => norm_pos_iff.mp (h.symm x).property.1)
    have heq : (fun x => (h.symm x : ℂ) ^ m) = (fun x => (p x : ℂ)) := by
      funext x
      have hc := congrArg (fun z : Disk r => (z : ℂ)) (congrFun hcomm (h.symm x))
      simpa only [Function.comp_apply, h.apply_symm_apply, powerMap] using hc.symm
    change ScalarHolomorphic S (fun x => (h.symm x : ℂ) ^ m)
    rwa [heq]
  obtain ⟨T, hT, hf, hg⟩ := biholomorphic_of_scalar_parameter S
    (disk_isDomain (rootRadius_pos hr m)) h hg
  exact ⟨T, h, hT, hf, hg, hcomm⟩

/-- Fill exactly the missing parameter center, on the prescribed set `Option E`. -/
def onePointEquiv {E : Type*} [TopologicalSpace E] {R : ℝ} (hR : 0 < R)
    (h : Disk R ≃ₜ E) : Option E ≃ Metric.ball (0 : ℂ) R where
  toFun x := match x with
    | none => ⟨0, Metric.mem_ball_self hR⟩
    | some e => ⟨h.symm e, by simpa [Metric.mem_ball, dist_zero_right] using
        (h.symm e).property.2⟩
  invFun z := if hz : (z : ℂ) = 0 then none else
    some (h ⟨z, norm_pos_iff.mpr hz,
      by simpa only [Metric.mem_ball, dist_zero_right] using z.property⟩)
  left_inv x := by
    cases x with
    | none => simp
    | some e =>
      dsimp
      rw [dite_eq_right (norm_pos_iff.mp (h.symm e).property.1)]
      simp
  right_inv z := by
    dsimp
    split_ifs with hz
    · exact Subtype.ext hz.symm
    · apply Subtype.ext
      simp

lemma onePointEquiv_none {E : Type*} [TopologicalSpace E] {R : ℝ}
    (hR : 0 < R) (h : Disk R ≃ₜ E) : (onePointEquiv hR h none : ℂ) = 0 := rfl

lemma onePointEquiv_some {E : Type*} [TopologicalSpace E] {R : ℝ}
    (hR : 0 < R) (h : Disk R ≃ₜ E) (e : E) :
    (onePointEquiv hR h (some e) : ℂ) = (h.symm e : ℂ) := rfl

/-- A global domain chart is an atlas on its own. -/
def surfaceOfGlobalChart {X : Type*} [TopologicalSpace X]
    [ConnectedSpace X] [T2Space X] [SecondCountableTopology X]
    (c : ComplexChart X) (hc : c.val.source = univ) : RiemannSurface X where
  connected := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  atlas := {c}
  isAtlas := ⟨fun x => ⟨c, rfl, by rw [hc]; trivial⟩, by
    intro e he f hf
    have he' : e = c := he
    have hf' : f = c := hf
    rw [he', hf']
    exact compatibleCharts_refl c⟩

lemma fullDisk_isDomain {R : ℝ} (hR : 0 < R) : IsDomain (Metric.ball (0 : ℂ) R) :=
  ⟨⟨0, Metric.mem_ball_self hR⟩, Metric.isOpen_ball, (convex_ball (0 : ℂ) R).isPreconnected⟩

/-- A topological power parameter is holomorphic in the original structure. -/
lemma inverse_parameter_holomorphic {r : ℝ} (hr : 0 < r)
    {E : Type*} [TopologicalSpace E] (S : RiemannSurface E) (p : E → Disk r)
    (hp : ScalarHolomorphic S (fun x => (p x : ℂ))) {m : ℕ} (hm : 0 < m)
    (h : Disk (rootRadius r m) ≃ₜ E) (hcomm : p ∘ h = powerMap hr hm) :
    ScalarHolomorphic S (fun x => (h.symm x : ℂ)) := by
  apply scalarHolomorphic_of_power S (continuous_subtype_val.comp h.symm.continuous) hm
    (fun x => norm_pos_iff.mp (h.symm x).property.1)
  change ScalarHolomorphic S (fun x => (h.symm x : ℂ) ^ m)
  have heq : (fun x => (h.symm x : ℂ) ^ m) = (fun x => (p x : ℂ)) := by
    funext x
    have hc := congrArg (fun z : Disk r => (z : ℂ)) (congrFun hcomm (h.symm x))
    simpa only [Function.comp_apply, h.apply_symm_apply, powerMap] using hc.symm
  rwa [heq]

/-- Connected one-point completion, constructed by transporting the full disk
onto exactly `Option E`, with the old complex structure retained. -/
theorem connected_completion :
    Specs.D12Complex.Ch20.PunctureCompletion.connected_completion_type := by
  intro r hr E _ S p hp hhol m hm hcard
  obtain ⟨_, h, _, _, _, hcomm⟩ := connected_classification hr S p hp hhol hm hcard
  have hg := inverse_parameter_holomorphic hr S p hhol hm h hcomm
  let R := rootRadius r m
  have hR : 0 < R := rootRadius_pos hr m
  let Q := onePointEquiv hR h
  let top : TopologicalSpace (Option E) := TopologicalSpace.induced Q inferInstance
  refine ⟨top, ?_⟩
  letI := top
  let H : Option E ≃ₜ Metric.ball (0 : ℂ) R := Q.toHomeomorphOfIsInducing ⟨rfl⟩
  let : ConnectedSpace (Metric.ball (0 : ℂ) R) :=
    isConnected_iff_connectedSpace.mp ⟨(fullDisk_isDomain hR).1, (fullDisk_isDomain hR).2.2⟩
  let : ConnectedSpace (Option E) := H.connectedSpace_iff.mpr inferInstance
  let : T2Space (Option E) := H.symm.t2Space
  let : SecondCountableTopology (Option E) := H.secondCountableTopology
  let c := parameterChart (fullDisk_isDomain hR) H.symm
  have hcs : c.val.source = univ := parameterChart_source _ _
  have hct : c.val.target = Metric.ball (0 : ℂ) R := parameterChart_target _ _
  have hc0 : c.val none = 0 := rfl
  have hcSome (e : E) : c.val (some e) = (h.symm e : ℂ) := rfl
  let C := surfaceOfGlobalChart c hcs
  have hcC : c ∈ C.atlas := rfl
  have hcm : c ∈ maximalAtlas C.atlas := subset_maximalAtlas C.isAtlas hcC
  let P : Option E → ℂ := fun x => match x with
    | none => 0
    | some e => (p e : ℂ)
  have hpow : ∀ x, P x = (c.val x) ^ m := by
    intro x
    cases x with
    | none => simp only [P, hc0, zero_pow hm.ne']
    | some e =>
      rw [hcSome]
      have heq := congrArg (fun z : Disk r => (z : ℂ)) (congrFun hcomm (h.symm e))
      simpa only [Function.comp_apply, h.apply_symm_apply, powerMap, P] using heq
  have hco : IsOpenEmbedding (c.val : Option E → ℂ) :=
    (fullDisk_isDomain hR).2.1.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding
  have hsome : IsOpenEmbedding (some : E → Option E) := by
    apply hco.of_comp some
    exact (disk_isDomain hR).2.1.isOpenEmbedding_subtypeVal.comp h.symm.isOpenEmbedding
  have hpHol : ScalarHolomorphic C P := by
    refine ⟨?_, ?_⟩
    · have heq : P = fun x => (c.val x) ^ m := funext hpow
      rw [heq]
      exact hco.continuous.pow m
    · intro e he
      have he' : e = c := he
      subst e
      refine ⟨c.val.open_target, fun z hz => ?_⟩
      have heq : (P ∘ c.val.symm) =ᶠ[𝓝 z] (fun z : ℂ => z ^ m) := by
        filter_upwards [c.val.open_target.mem_nhds hz] with w hw
        rw [Function.comp_apply, hpow, c.val.right_inv hw]
      exact (hasDerivAt_pow m z).differentiableAt.congr_of_eventuallyEq heq
  have hmax : parameterChart (disk_isDomain hR) h ∈ maximalAtlas S.atlas :=
    parameterChart_mem_maximalAtlas S (disk_isDomain hR) h hg
  have hloc (a : E) : LocallyBiholomorphicAt S C some a := by
    obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
    let g := parameterChart (disk_isDomain hR) h
    let t := e.val.symm.trans g.val
    have ht := compatibleCharts_symm (hmax e he)
    have heq : coordinateMap e c some = (t : ℂ → ℂ) := by
      funext z
      exact hcSome _
    have hsrc : t.source = e.val.target := by
      simp [t, g, parameterChart_source]
    have htarget : t.target ⊆ c.val.target := by
      intro z hz
      have hzR : z ∈ g.val.target := hz.1
      rw [parameterChart_target] at hzR
      rw [hct]
      simpa only [Metric.mem_ball, dist_zero_right] using hzR.2
    have hdom : t.source ⊆ coordinateDomain e c some := by
      intro z hz
      exact ⟨(hsrc ▸ hz), by rw [hcs]; trivial⟩
    refine ⟨e, he, c, hcC, ha, by rw [hcs]; trivial,
      t.source, t.target, t.symm, ?_, hdom, htarget, ?_⟩
    · rw [hsrc]; exact e.val.map_source ha
    · rw [heq]
      exact ht
  have hmap : HolomorphicMap S C some := by
    intro a
    obtain ⟨e, he, d, hd, ha, hda, U, V, g, haU, _, _, hpair⟩ := hloc a
    exact ⟨hsome.continuous.continuousAt, e, he, d, hd, ha, hda, U, haU, hpair.1⟩
  have hPlane : IsDomain (univ : Set ℂ) :=
    ⟨Set.univ_nonempty, isOpen_univ, isPreconnected_univ⟩
  let d : ComplexChart ℂ := ⟨(Homeomorph.refl ℂ).toOpenPartialHomeomorph, hPlane⟩
  let T := surfaceOfGlobalChart d rfl
  have hdT : d ∈ T.atlas := rfl
  have hdm : d ∈ maximalAtlas T.atlas := subset_maximalAtlas T.isAtlas hdT
  have hmapP : HolomorphicMap C T P := by
    intro a
    refine ⟨hpHol.1.continuousAt, c, hcC, d, hdT, ?_, mem_univ _, ?_⟩
    · rw [hcs]; trivial
    · exact ⟨c.val.target, c.val.map_source (by rw [hcs]; trivial), hpHol.2 c hcC⟩
  have horder : coordinateOrder c d P none = (m : ℕ∞) := by
    have heq : (fun z => coordinateMap c d P z - d.val (P none)) =ᶠ[𝓝 (0 : ℂ)]
        (fun z : ℂ => z ^ m) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)] with z hz
      change P (c.val.symm z) - 0 = z ^ m
      rw [sub_zero, hpow, c.val.right_inv (hct.symm ▸ hz)]
    change analyticOrderAt (fun z => coordinateMap c d P z - d.val (P none)) (c.val none) = _
    rw [hc0, analyticOrderAt_congr heq]
    simpa using! (analyticOrderAt_centeredMonomial (z₀ := (0 : ℂ)) (n := m))
  have hmult : HasMultiplicity C T P none m := by
    refine ⟨hm, fun e he f hf ha hfa => ?_⟩
    exact (coordinate_order_chart_independent C T P none (hmapP none)
      e he f hf c hcm d hdm ha hfa (by rw [hcs]; trivial) (mem_univ _)).trans horder
  refine ⟨C, T, c, ?_, hsome, hmap, hloc, hcm, hcs, hct, hc0, hpow, ?_, hpHol, hmult⟩
  · intro e he
    have he' : e = d := he
    subst e
    exact fun _ _ => rfl
  · intro x
    cases x with
    | none => simpa only [P, norm_zero] using hr
    | some e => exact (p e).property.2

/-- The disconnected monodromy correspondence needs only reachability,
not global connectedness of the covering space. -/
theorem joined_iff_monodromy_orbit :
    Specs.D12Complex.Ch20.PunctureCompletion.joined_iff_monodromy_orbit_type := by
  intro r hr E _ p cov b γ hγ x y
  have hclass : (CategoryTheory.End.of (Path.Homotopic.Quotient.mk γ) :
      FundamentalGroup (Disk r) b) = circleClass b 1 := by
    apply CategoryTheory.End.ext
    exact Quotient.sound ((classification hr b γ (circleLoop b 1) 1 1 hγ
      (circleLoop_winding b 1)).mpr rfl)
  rw [hclass]
  constructor
  · rintro ⟨Γ⟩
    let η : Path b b := (Γ.map cov.continuous).cast x.property.symm y.property.symm
    have hη : LiftEndpoint p η x y := ⟨Γ, fun _ => rfl⟩
    have hxy := (monodromy_endpoint_iff cov η x y).mpr hη
    obtain ⟨k, hk⟩ := fundamentalGroup_generator hr b (.of (.mk η))
    refine ⟨k, ?_⟩
    rw [← map_zpow, ← hk]
    exact hxy
  · rintro ⟨k, hk⟩
    have hxy : cov.monodromyPerm b (circleClass b k) x = y := by
      rw [circleClass_eq_zpow hr b, map_zpow]
      exact hk
    obtain ⟨Γ, _⟩ := (monodromy_endpoint_iff cov (circleLoop b k) x y).mp hxy
    exact ⟨Γ⟩

theorem fiber_meets_components :
    Specs.D12Complex.Ch20.PunctureCompletion.fiber_meets_components_type := by
  intro r hr E _ p cov b e
  let γ := diskPath hr (p e) b
  obtain ⟨L, hLp, hL0⟩ := cov.exists_path_lifts γ.toContinuousMap e γ.source
  let x : p ⁻¹' {b} := ⟨L 1, (congrFun hLp 1).trans γ.target⟩
  exact ⟨x, ⟨⟨L, hL0, rfl⟩⟩⟩

theorem finite_components :
    Specs.D12Complex.Ch20.PunctureCompletion.finite_components_type := by
  intro r hr E _ p cov b hfin
  let := hfin
  apply Finite.of_surjective (fun x : p ⁻¹' {b} => ConnectedComponents.mk (x : E))
  intro j
  obtain ⟨e, rfl⟩ := ConnectedComponents.surjective_coe j
  obtain ⟨x, hx⟩ := fiber_meets_components hr cov b e
  refine ⟨x, ConnectedComponents.coe_eq_coe.mpr ?_⟩
  exact connectedComponent_eq (pathComponent_subset_component _ hx.symm)

open private chartedSpaceOfAtlas from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.Surfaces

/-- A complex atlas is locally path connected even when the whole space is
empty or disconnected. Connectedness is not needed for this local fact. -/
lemma atlas_locallyPathConnected {E : Type*} [TopologicalSpace E]
    (A : Set (ComplexChart E)) (hA : IsAtlas A) : LocallyPathConnectedSpace E := by
  letI := chartedSpaceOfAtlas A hA
  exact ChartedSpace.locallyPathConnectedSpace ℂ E

theorem monodromy_components :
    Specs.D12Complex.Ch20.PunctureCompletion.monodromy_components_type := by
  intro r hr E _ A hA p cov b γ hγ hfin
  let := hfin
  let := atlas_locallyPathConnected A hA
  refine ⟨finite_components hr cov b hfin, ?_, ?_⟩
  · intro x y
    rw [ConnectedComponents.coe_eq_coe, connectedComponent_eq_iff_joined]
    exact joined_iff_monodromy_orbit hr cov b γ hγ x y
  · intro j
    obtain ⟨e, rfl⟩ := ConnectedComponents.surjective_coe j
    obtain ⟨x, hx⟩ := fiber_meets_components hr cov b e
    apply Nat.card_pos_iff.mpr
    refine ⟨⟨⟨x, ConnectedComponents.coe_eq_coe.mpr ?_⟩⟩, inferInstance⟩
    exact connectedComponent_eq (pathComponent_subset_component _ hx.symm)

/-- A finite covering is closed. Locally it is projection from a product
with a finite discrete fiber, which is compact. -/
lemma finite_covering_isClosedMap {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} (cov : IsCoveringMap p)
    (hfin : ∀ b, Finite (p ⁻¹' {b})) : IsClosedMap p := by
  intro F hF
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro b hb
  obtain ⟨_, U, hbU, hU, _, H, hH⟩ := cov b
  let := hfin b
  let V : Set U := Prod.fst '' (H '' ((Subtype.val : p ⁻¹' U → E) ⁻¹' F))
  have hV : IsClosed V :=
    isClosedMap_fst_of_compactSpace _ (H.isClosedMap _ (hF.preimage continuous_subtype_val))
  have hbV : (⟨b, hbU⟩ : U) ∉ V := by
    rintro ⟨_, ⟨z, hz, rfl⟩, heq⟩
    exact hb ⟨z, hz, (hH z).symm.trans (congrArg Subtype.val heq)⟩
  refine ⟨Subtype.val '' Vᶜ, ?_, hU.isOpenEmbedding_subtypeVal.isOpenMap _ hV.isOpen_compl,
    ⟨⟨b, hbU⟩, hbV, rfl⟩⟩
  rintro y ⟨z, hz, rfl⟩ ⟨e, heF, hey⟩
  apply hz
  refine ⟨H ⟨e, by simpa only [mem_preimage, hey] using z.property⟩, ⟨⟨e, by simpa only [mem_preimage, hey] using z.property⟩, heF, rfl⟩, ?_⟩
  apply Subtype.ext
  exact (hH _).trans hey

/-- Restricting a finite cover to a clopen subset is a covering. The
closedness is essential: an arbitrary open restriction need not be a cover. -/
lemma covering_restrict_clopen {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] [T2Space E] {p : E → B} (cov : IsCoveringMap p)
    (hfin : ∀ b, Finite (p ⁻¹' {b})) {U : Set E} (hU : IsClopen U) :
    IsCoveringMap (fun e : U => p e) := by
  have hclosed : IsClosedMap (fun e : U => p e) :=
    (finite_covering_isClosedMap cov hfin).comp hU.isClosed.isClosedEmbedding_subtypeVal.isClosedMap
  have hlocal : IsLocalHomeomorph (fun e : U => p e) :=
    cov.isLocalHomeomorph.comp hU.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply hclosed.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro b _
    have := hfin b
    have : Finite ((fun e : U => p e) ⁻¹' {b}) :=
      Finite.of_injective (fun e : (fun e : U => p e) ⁻¹' {b} =>
        (⟨e.val.val, e.property⟩ : p ⁻¹' {b})) (by
          intro x y h; exact Subtype.ext (Subtype.ext (congrArg (fun z : p ⁻¹' {b} => (z : E)) h)))
    exact Set.toFinite _
  · exact hlocal.isLocalHomeomorphOn

/-- The actual subset represented by a connected-component quotient point. -/
def componentSet {E : Type*} [TopologicalSpace E] (j : ConnectedComponents E) : Set E :=
  {e | ConnectedComponents.mk e = j}

lemma componentSet_eq {E : Type*} [TopologicalSpace E] (e : E) :
    componentSet (ConnectedComponents.mk e) = connectedComponent e := by
  ext x
  exact ConnectedComponents.coe_eq_coe'

lemma componentSet_connected {E : Type*} [TopologicalSpace E]
    (j : ConnectedComponents E) : IsConnected (componentSet j) := by
  obtain ⟨e, rfl⟩ := ConnectedComponents.surjective_coe j
  rw [componentSet_eq]
  exact isConnected_connectedComponent

lemma componentSet_clopen {E : Type*} [TopologicalSpace E]
    [LocallyConnectedSpace E] (j : ConnectedComponents E) : IsClopen (componentSet j) := by
  obtain ⟨e, rfl⟩ := ConnectedComponents.surjective_coe j
  rw [componentSet_eq]
  exact isClopen_connectedComponent

/-- A connected coordinate neighborhood lies in its point's component. -/
lemma chart_source_subset_component {E : Type*} [TopologicalSpace E]
    (e : ComplexChart E) {x : E} (hx : x ∈ e.val.source) :
    e.val.source ⊆ componentSet (ConnectedComponents.mk x) := by
  have hc : IsConnected e.val.source := by
    rw [← e.val.symm_image_target_eq_source]
    exact (show IsConnected e.val.target from ⟨e.property.1, e.property.2.2⟩).image
      e.val.symm e.val.symm.continuousOn
  intro y hy
  exact ConnectedComponents.coe_eq_coe'.mpr (hc.isPreconnected.subset_connectedComponent hx hy)

/-- Restrict a chart whose entire source belongs to the given open component. -/
def componentChart {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    (j : ConnectedComponents E) (e : ComplexChart E)
    (he : e.val.source ⊆ componentSet j) : ComplexChart (componentSet j) := by
  let U : TopologicalSpace.Opens E := ⟨componentSet j, (componentSet_clopen j).isOpen⟩
  let hn : Nonempty U := (componentSet_connected j).nonempty.to_subtype
  let d := e.val.subtypeRestr (s := U) hn
  have htarget : d.target = e.val.target := by
    ext z
    constructor
    · exact fun hz => hz.1
    · intro hz
      exact ⟨hz, by
        simp only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target, mem_preimage]
        exact he (e.val.map_target hz)⟩
  exact ⟨d, htarget.symm ▸ e.property⟩

lemma componentChart_target {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    (j : ConnectedComponents E) (e : ComplexChart E)
    (he : e.val.source ⊆ componentSet j) :
    (componentChart j e he).val.target = e.val.target := by
  ext z
  constructor
  · exact fun hz => hz.1
  · intro hz
    refine ⟨hz, ?_⟩
    simp only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target, mem_preimage]
    exact he (e.val.map_target hz)

lemma componentChart_source {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    (j : ConnectedComponents E) (e : ComplexChart E)
    (he : e.val.source ⊆ componentSet j) :
    (componentChart j e he).val.source = Subtype.val ⁻¹' e.val.source := by
  exact OpenPartialHomeomorph.subtypeRestr_source _ _

lemma componentChart_apply {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    (j : ConnectedComponents E) (e : ComplexChart E)
    (he : e.val.source ⊆ componentSet j) (x : componentSet j) :
    (componentChart j e he).val x = e.val x := rfl

lemma componentChart_symm {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    (j : ConnectedComponents E) (e : ComplexChart E)
    (he : e.val.source ⊆ componentSet j) {z : ℂ} (hz : z ∈ e.val.target) :
    ((componentChart j e he).val.symm z : E) = e.val.symm z := by
  apply OpenPartialHomeomorph.subtypeRestr_symm_apply
  change z ∈ (componentChart j e he).val.target
  rwa [componentChart_target j e he]

/-- The inherited atlas consists of the original coordinate neighborhoods
contained in this component. -/
def componentAtlas {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    (A : Set (ComplexChart E)) (j : ConnectedComponents E) :
    Set (ComplexChart (componentSet j)) :=
  {d | ∃ e ∈ A, ∃ he : e.val.source ⊆ componentSet j, d = componentChart j e he}

lemma componentAtlas_isAtlas {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E]
    (A : Set (ComplexChart E)) (hA : IsAtlas A) (j : ConnectedComponents E) :
    IsAtlas (componentAtlas A j) := by
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨e, he, hx⟩ := hA.1 x.val
    have hsub : e.val.source ⊆ componentSet j := by
      have h := chart_source_subset_component e hx
      have hxj : ConnectedComponents.mk (x : E) = j := x.property
      rwa [hxj] at h
    exact ⟨componentChart j e hsub, ⟨e, he, hsub, rfl⟩, by
      rwa [componentChart_source]⟩
  · rintro d ⟨e, he, hec, rfl⟩ d' ⟨f, hf, hfc, rfl⟩
    let t := (componentChart j e hec).val.symm.trans (componentChart j f hfc).val
    have ht : HolomorphicOn t.source t := by
      refine ⟨t.open_source, fun z hz => ?_⟩
      have hze : z ∈ e.val.target := (componentChart_target j e hec) ▸ hz.1
      have hzf : e.val.symm z ∈ f.val.source := by
        have hh := hz.2
        rw [componentChart_source] at hh
        simpa only [mem_preimage, OpenPartialHomeomorph.symm_symm,
          componentChart_symm j e hec hze] using hh
      have hd := (hA.2 e he f hf).1.2 z ⟨hze, hzf⟩
      apply hd.congr_of_eventuallyEq
      filter_upwards [e.val.open_target.mem_nhds hze] with w hw
      change f.val ((componentChart j e hec).val.symm w : E) = f.val (e.val.symm w)
      rw [componentChart_symm j e hec hw]
    exact ⟨ht, holomorphicOn_symm t ht, t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩

/-- The actual connected surface structure on an open component. -/
def componentSurface {E : Type*} [TopologicalSpace E] [T2Space E]
    [SecondCountableTopology E] [LocallyConnectedSpace E]
    (A : Set (ComplexChart E)) (hA : IsAtlas A) (j : ConnectedComponents E) :
    RiemannSurface (componentSet j) where
  connected := isConnected_iff_connectedSpace.mp (componentSet_connected j)
  hausdorff := inferInstance
  secondCountable := inferInstance
  atlas := componentAtlas A j
  isAtlas := componentAtlas_isAtlas A hA j

lemma component_scalarHolomorphic {E : Type*} [TopologicalSpace E] [T2Space E]
    [SecondCountableTopology E] [LocallyConnectedSpace E]
    (A : Set (ComplexChart E)) (hA : IsAtlas A) {f : E → ℂ}
    (hf : Continuous f ∧ ∀ e ∈ A, HolomorphicOn e.val.target (f ∘ e.val.symm))
    (j : ConnectedComponents E) :
    ScalarHolomorphic (componentSurface A hA j) (fun x => f x) := by
  refine ⟨hf.1.comp continuous_subtype_val, ?_⟩
  rintro d ⟨e, he, hec, rfl⟩
  rw [componentChart_target]
  refine ⟨e.val.open_target, fun z hz => ?_⟩
  apply ((hf.2 e he).2 z hz).congr_of_eventuallyEq
  filter_upwards [e.val.open_target.mem_nhds hz] with w hw
  exact congrArg f (componentChart_symm j e hec hw)

/-- Fiber transport preserves the actual connected component, as witnessed
by the lifted path itself. -/
lemma monodromy_component {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (cov : IsCoveringMap p) {b c : B} (γ : Path b c) (x : p ⁻¹' {b}) :
    ConnectedComponents.mk (cov.monodromy (.mk γ) x : E) = ConnectedComponents.mk (x : E) := by
  let L := cov.liftPath γ x (γ.source.trans x.property.symm)
  have hL : Joined (x : E) (cov.monodromy (.mk γ) x : E) :=
    ⟨⟨L, cov.liftPath_zero _ _ _, rfl⟩⟩
  exact ConnectedComponents.coe_eq_coe.mpr
    (connectedComponent_eq (pathComponent_subset_component _ hL.symm))

/-- Path transport identifies the fibers lying in a fixed component. -/
def componentFiberEquiv {r : ℝ} (hr : 0 < r) {E : Type*} [TopologicalSpace E]
    {p : E → Disk r} (cov : IsCoveringMap p) (j : ConnectedComponents E) (b c : Disk r) :
    {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j} ≃
      {x : p ⁻¹' {c} // ConnectedComponents.mk (x : E) = j} :=
  Equiv.subtypeEquiv (Equiv.ofBijective (cov.monodromy (.mk (diskPath hr b c)))
    (cov.monodromy_bijective _)) (fun x => by
      change ConnectedComponents.mk (x : E) = j ↔
        ConnectedComponents.mk (cov.monodromy (.mk (diskPath hr b c)) x : E) = j
      rw [monodromy_component])

/-- Reorder the two fiber conditions without changing either set. -/
def componentFiberShuffle {r : ℝ} {E : Type*} [TopologicalSpace E]
    (p : E → Disk r) (j : ConnectedComponents E) (b : Disk r) :
    ((fun x : componentSet j => p x) ⁻¹' {b}) ≃
      {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j} where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma component_cover_card {r : ℝ} (hr : 0 < r) {E : Type*} [TopologicalSpace E]
    {p : E → Disk r} (cov : IsCoveringMap p) (j : ConnectedComponents E) (b c : Disk r) :
    Nat.card ((fun x : componentSet j => p x) ⁻¹' {c}) =
      Nat.card {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j} := by
  rw [Nat.card_congr (componentFiberShuffle p j c)]
  exact Nat.card_congr (componentFiberEquiv hr cov j c b)

/-- The disjoint union of components carries exactly the original topology. -/
def componentHomeomorph {E : Type*} [TopologicalSpace E] [LocallyConnectedSpace E] :
    (Σ j : ConnectedComponents E, componentSet j) ≃ₜ E :=
  (Equiv.sigmaFiberEquiv (ConnectedComponents.mk : E → ConnectedComponents E)).toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ => continuous_subtype_val)
    (isOpenMap_sigma.mpr fun j => (componentSet_clopen j).isOpen.isOpenEmbedding_subtypeVal.isOpenMap)

/-- As a set the union of the one-point completions adds exactly one point
per old component. No quotient of old points is taken. -/
def completionSumEquiv {E : Type*} [TopologicalSpace E] :
    (Σ j : ConnectedComponents E, Option (componentSet j)) ≃ E ⊕ ConnectedComponents E where
  toFun x := match x with
    | ⟨_, none⟩ => Sum.inr x.1
    | ⟨_, some e⟩ => Sum.inl e.val
  invFun x := match x with
    | Sum.inl e => ⟨ConnectedComponents.mk e, some ⟨e, rfl⟩⟩
    | Sum.inr j => ⟨j, none⟩
  left_inv x := by
    rcases x with ⟨j, _ | ⟨e, he⟩⟩
    · rfl
    · change ConnectedComponents.mk e = j at he
      subst j
      rfl
  right_inv x := by cases x <;> rfl

/-- Push a full chart through an open embedding. Its source is exactly the
embedded component and its target is unchanged. -/
def embeddedChart {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] [Nonempty Y]
    (i : Y → X) (hi : IsOpenEmbedding i) (c : ComplexChart Y) (_hc : c.val.source = univ) :
    ComplexChart X := by
  let u := hi.toOpenPartialHomeomorph i
  let d := u.symm.trans c.val
  have ht : d.target = c.val.target := by simp [d, u]
  exact ⟨d, ht.symm ▸ c.property⟩

lemma embeddedChart_source {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] [Nonempty Y]
    (i : Y → X) (hi : IsOpenEmbedding i) (c : ComplexChart Y) (hc : c.val.source = univ) :
    (embeddedChart i hi c hc).val.source = range i := by
  simp [embeddedChart, hc]

lemma embeddedChart_target {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] [Nonempty Y]
    (i : Y → X) (hi : IsOpenEmbedding i) (c : ComplexChart Y) (hc : c.val.source = univ) :
    (embeddedChart i hi c hc).val.target = c.val.target := by
  simp [embeddedChart]

lemma embeddedChart_apply {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] [Nonempty Y]
    (i : Y → X) (hi : IsOpenEmbedding i) (c : ComplexChart Y) (hc : c.val.source = univ) (y : Y) :
    (embeddedChart i hi c hc).val (i y) = c.val y := by
  change c.val ((hi.toOpenPartialHomeomorph i).symm (i y)) = c.val y
  rw [hi.toOpenPartialHomeomorph_left_inv]

lemma embeddedChart_symm {Y X : Type*} [TopologicalSpace Y] [TopologicalSpace X] [Nonempty Y]
    (i : Y → X) (hi : IsOpenEmbedding i) (c : ComplexChart Y) (hc : c.val.source = univ) (z : ℂ) :
    (embeddedChart i hi c hc).val.symm z = i (c.val.symm z) := rfl

/-- Disjoint full charts have empty transitions and are compatible. -/
lemma compatibleCharts_of_disjoint {X : Type*} [TopologicalSpace X]
    (c d : ComplexChart X) (h : Disjoint c.val.source d.val.source) : CompatibleCharts c d := by
  let t := c.val.symm.trans d.val
  have hs : t.source = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact Set.disjoint_left.mp h (c.val.map_target hz.1) hz.2
  have ht : t.target = ∅ := by
    rw [← t.image_source_eq_target, hs, image_empty]
  refine ⟨⟨t.open_source, ?_⟩, ⟨t.open_target, ?_⟩, t.mapsTo, t.symm.mapsTo,
    t.leftInvOn, t.rightInvOn⟩
  · intro z hz
    change z ∈ t.source at hz
    simp only [hs, mem_empty_iff_false] at hz
  · intro z hz
    change z ∈ t.target at hz
    simp only [ht, mem_empty_iff_false] at hz

/-- Complete all monodromy cycles and assemble their full parameter charts
on exactly the old set plus one point per component. -/
theorem disconnected_completion :
    Specs.D12Complex.Ch20.PunctureCompletion.disconnected_completion_type := by
  intro r hr E _ _ _ A hA p hp hhol hfin b cov γ hγ
  let := atlas_locallyPathConnected A hA
  obtain ⟨hfinite, horbit, hpositive⟩ := monodromy_components hr A hA cov b γ hγ (hfin b)
  let := hfinite
  let n : ConnectedComponents E → ℕ := fun j =>
    Nat.card {x : p ⁻¹' {b} // ConnectedComponents.mk (x : E) = j}
  refine ⟨hfinite, horbit, hpositive, ?_⟩
  have completions (j : ConnectedComponents E) :=
    connected_completion hr (componentSurface A hA j) (fun x : componentSet j => p x)
      (covering_of_isCoveringMap _ (covering_restrict_clopen cov hfin (componentSet_clopen j)))
      (component_scalarHolomorphic A hA hhol j)
      (hpositive j) (fun z => component_cover_card hr cov j b z)
  choose top ht using completions
  letI optionTopology : ∀ j : ConnectedComponents E, TopologicalSpace (Option (componentSet j)) := top
  choose C T c hT hs hm hl hcm hcs hct hc0 hpow hbound hholC hmult using ht
  let X := E ⊕ ConnectedComponents E
  let Q : X ≃ (Σ j : ConnectedComponents E, Option (componentSet j)) := completionSumEquiv.symm
  let topX : TopologicalSpace X := TopologicalSpace.induced Q inferInstance
  refine ⟨topX, ?_⟩
  letI := topX
  let H : (Σ j : ConnectedComponents E, Option (componentSet j)) ≃ₜ X :=
    (Q.toHomeomorphOfIsInducing ⟨rfl⟩).symm
  let (j : ConnectedComponents E) : T2Space (Option (componentSet j)) := (C j).hausdorff
  let (j : ConnectedComponents E) : SecondCountableTopology (Option (componentSet j)) :=
    (C j).secondCountable
  let : T2Space X := H.t2Space
  let : SecondCountableTopology X := H.symm.secondCountableTopology
  refine ⟨inferInstance, inferInstance, ?_⟩
  let i (j : ConnectedComponents E) : Option (componentSet j) → X :=
    fun y => H (⟨j, y⟩ : Σ k : ConnectedComponents E, Option (componentSet k))
  have hi (j) : IsOpenEmbedding (i j) := H.isOpenEmbedding.comp .sigmaMk
  have hiNone (j) : i j none = Sum.inr j := rfl
  have hiSome (j) (e : componentSet j) : i j (some e) = Sum.inl e.val := rfl
  let d (j : ConnectedComponents E) : ComplexChart X := embeddedChart (i j) (hi j) (c j) (hcs j)
  have hds (j) : (d j).val.source = range (i j) := embeddedChart_source _ _ _ _
  have hdt (j) : (d j).val.target = Metric.ball (0 : ℂ) (rootRadius r (n j)) :=
    (embeddedChart_target _ _ _ _).trans (hct j)
  have hdi (j) (x : Option (componentSet j)) : (d j).val (i j x) = (c j).val x :=
    embeddedChart_apply _ _ _ _ x
  have hdsi (j) (z : ℂ) : (d j).val.symm z = i j ((c j).val.symm z) := rfl
  let B : Set (ComplexChart X) := range d
  have hB : IsAtlas B := by
    refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨⟨j, y⟩, rfl⟩ := H.surjective x
      exact ⟨d j, ⟨j, rfl⟩, by rw [hds]; exact ⟨y, rfl⟩⟩
    · rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩
      by_cases hjk : j = k
      · subst k; exact compatibleCharts_refl _
      apply compatibleCharts_of_disjoint
      rw [hds, hds]
      apply Set.disjoint_left.mpr
      rintro x ⟨y, hy⟩ ⟨z, hz⟩
      exact hjk (congrArg Sigma.fst (H.injective (hy.trans hz.symm)))
  let P : X → ℂ := fun x => match x with
    | Sum.inl e => (p e : ℂ)
    | Sum.inr _ => 0
  let Pj (j : ConnectedComponents E) : Option (componentSet j) → ℂ := fun x => match x with
    | none => 0
    | some e => (p e : ℂ)
  have hPi (j) : P ∘ i j = Pj j := by funext x; cases x <;> rfl
  have hholC' (j) : ScalarHolomorphic (C j) (Pj j) := by
    convert hholC j using 1
    funext x
    cases x <;> rfl
  have hpow' (j) (x : Option (componentSet j)) : Pj j x = (c j).val x ^ n j := by
    cases x with
    | none => exact hpow j none
    | some e => exact hpow j (some e)
  have hpcont : Continuous P := by
    have hh : Continuous (P ∘ H) := continuous_sigma fun j => by
      change Continuous (P ∘ i j)
      rw [hPi]
      exact (hholC' j).1
    exact (hh.comp H.symm.continuous).congr (fun _ => by simp)
  have hpB : ∀ e ∈ B, HolomorphicOn e.val.target (P ∘ e.val.symm) := by
    rintro _ ⟨j, rfl⟩
    rw [embeddedChart_target]
    have hEq : P ∘ (d j).val.symm = Pj j ∘ (c j).val.symm := by
      funext z
      change P (i j ((c j).val.symm z)) = Pj j ((c j).val.symm z)
      exact congrFun (hPi j) _
    rw [hEq]
    exact scalarHolomorphic_chart_independent (C j) (Pj j) (hholC' j) (c j) (hcm j)
  let D : IsDomain (univ : Set ℂ) := ⟨univ_nonempty, isOpen_univ, isPreconnected_univ⟩
  let e0 : ComplexChart ℂ := ⟨(Homeomorph.refl ℂ).toOpenPartialHomeomorph, D⟩
  let T0 := surfaceOfGlobalChart e0 rfl
  have he0 : e0 ∈ T0.atlas := rfl
  have hsome : IsOpenEmbedding (Sum.inl : E → X) := by
    let F : (Σ j : ConnectedComponents E, componentSet j) →
        (Σ j : ConnectedComponents E, Option (componentSet j)) := Sigma.map id fun _ => some
    have hF : IsOpenEmbedding F := (Topology.isOpenEmbedding_sigmaMap Function.injective_id).mpr hs
    have heq : (Sum.inl : E → X) = H ∘ F ∘ componentHomeomorph.symm := by
      funext x; rfl
    rw [heq]
    exact H.isOpenEmbedding.comp (hF.comp componentHomeomorph.symm.isOpenEmbedding)
  refine ⟨B, T0, hB, ?_, hsome, ?_, hpcont, hpB, ?_, ?_⟩
  · intro e he
    have he' : e = e0 := he
    subst e
    exact fun _ _ => rfl
  · intro a
    obtain ⟨e, he, ha⟩ := hA.1 a
    let j := ConnectedComponents.mk a
    have hec : e.val.source ⊆ componentSet j := chart_source_subset_component e ha
    let ec := componentChart j e hec
    have hecA : ec ∈ (componentSurface A hA j).atlas := ⟨e, he, hec, rfl⟩
    let : Nonempty E := ⟨a⟩
    let v := hsome.toOpenPartialHomeomorph (Sum.inl : E → X)
    let t := (e.val.symm.trans v).trans (d j).val
    have hsource : t.source = e.val.target := by
      ext z
      refine ⟨fun hz => hz.1.1, fun hz => ⟨⟨hz, mem_univ _⟩, ?_⟩⟩
      change Sum.inl (e.val.symm z) ∈ (d j).val.source
      rw [hds]
      exact ⟨some ⟨e.val.symm z, hec (e.val.map_target hz)⟩, rfl⟩
    have ht : HolomorphicOn t.source t := by
      refine ⟨t.open_source, fun z hz => ?_⟩
      have hze : z ∈ ec.val.target := by
        rw [componentChart_target]
        exact hz.1.1
      have hh := holomorphicMapAt_chart_independent (componentSurface A hA j) (C j) some
        (ec.val.symm z) (hm j _) ec (subset_maximalAtlas (componentSurface A hA j).isAtlas hecA)
        (c j) (hcm j) (ec.val.map_target hze) (by rw [hcs]; trivial)
      rw [ec.val.right_inv hze] at hh
      apply hh.differentiableAt.congr_of_eventuallyEq
      filter_upwards [e.val.open_target.mem_nhds hz.1.1] with w hw
      change (d j).val (Sum.inl (e.val.symm w)) = (c j).val (some (ec.val.symm w))
      rw [← componentChart_symm j e hec hw]
      exact hdi j (some (ec.val.symm w))
    have hdom : t.source ⊆ coordinateDomain e (d j) Sum.inl := fun _ hz => ⟨hz.1.1, hz.2⟩
    refine ⟨e, he, d j, ⟨j, rfl⟩, ha, ?_, t.source, t.target, t.symm,
      ?_, hdom, fun _ hz => hz.1, ?_⟩
    · rw [hds]; exact ⟨some ⟨a, rfl⟩, rfl⟩
    · rw [hsource]; exact e.val.map_source ha
    · exact ⟨ht, holomorphicOn_symm t ht, t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩
  · intro x
    cases x with
    | inl e => exact (p e).property.2
    | inr j => simpa only [P, norm_zero] using hr
  · intro j
    refine ⟨d j, subset_maximalAtlas hB ⟨j, rfl⟩, ?_, hdt j, ?_, ?_, ?_⟩
    · rw [hds]
      ext x
      cases x with
      | inl e =>
        constructor
        · rintro ⟨y, hy⟩
          cases y with
          | none => exact False.elim (by rw [hiNone] at hy; cases hy)
          | some y =>
            have he : y.val = e := Sum.inl.inj hy
            exact Or.inl ⟨y.val, y.property, congrArg Sum.inl he⟩
        · rintro (⟨y, hy, hye⟩ | h)
          · have he : y = e := Sum.inl.inj hye
            exact ⟨some ⟨e, he ▸ hy⟩, rfl⟩
          · exact False.elim (by simp only [Set.mem_singleton_iff, Sum.inl_ne_inr] at h)
      | inr k =>
        constructor
        · rintro ⟨y, hy⟩
          cases y with
          | none => exact Or.inr (by rw [← hy, hiNone]; exact mem_singleton _)
          | some y => exact False.elim (by rw [hiSome] at hy; cases hy)
        · rintro (⟨y, _, hy⟩ | h)
          · exact False.elim (by simp only [Sum.inl_ne_inr] at hy)
          · have hkj : k = j := Sum.inr.inj (Set.mem_singleton_iff.mp h)
            subst k; exact ⟨none, rfl⟩
    · rw [← hiNone j, hdi, hc0]
    · intro x hx
      rw [hds] at hx
      obtain ⟨y, rfl⟩ := hx
      rw [hdi]
      cases y with
      | none => exact hpow j none
      | some e => exact hpow j (some e)
    · intro e he f hf ha hfa
      have hj : Sum.inr j ∈ (d j).val.source := by rw [hds]; exact ⟨none, rfl⟩
      have hj0 : (d j).val (Sum.inr j) = 0 := by rw [← hiNone j, hdi, hc0]
      have hP0 : P (Sum.inr j) = 0 := rfl
      have hg : HolomorphicGermAt (coordinateMap (d j) e0 P) ((d j).val (Sum.inr j)) :=
        ⟨(d j).val.target, (d j).val.map_source hj, hpB (d j) ⟨j, rfl⟩⟩
      have ho : coordinateOrder (d j) e0 P (Sum.inr j) = (n j : ℕ∞) := by
        have heq : (fun z => coordinateMap (d j) e0 P z - e0.val (P (Sum.inr j))) =ᶠ[𝓝 (0 : ℂ)]
            (fun z : ℂ => z ^ n j) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds
            (Metric.mem_ball_self (rootRadius_pos hr (n j)))] with z hz
          change P ((d j).val.symm z) - 0 = z ^ n j
          rw [sub_zero, hdsi]
          rw [show P (i j ((c j).val.symm z)) = Pj j ((c j).val.symm z) from congrFun (hPi j) _]
          have hpowj : Pj j ((c j).val.symm z) = ((c j).val ((c j).val.symm z)) ^ n j := by
            exact hpow' j ((c j).val.symm z)
          rw [hpowj, (c j).val.right_inv (by rwa [hct])]
        change analyticOrderAt _ ((d j).val (Sum.inr j)) = _
        rw [hj0, analyticOrderAt_congr heq]
        simpa using! (analyticOrderAt_centeredMonomial (z₀ := (0 : ℂ)) (n := n j))
      exact (coordinate_order_change hpcont.continuousAt (he (d j) ⟨j, rfl⟩)
        (compatibleCharts_symm (hf e0 he0)) hj ha (mem_univ _) hfa hg).trans ho

end D12Complex.Ch20.PunctureCompletion
