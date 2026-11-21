import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.LogarithmRootMonodromy
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.GermsContinuation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.ContinuationUniqueOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LocalLogarithmsRoots
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexProperties
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

open Filter Set
open scoped Topology
noncomputable section
namespace D12Complex.LogarithmRootMonodromy

/-- Inverse relations are equations of neighborhood germs. -/
def IsInverseGerm (p : ℂ → ℂ) {a : ℂ} (φ : HolomorphicGerm a) : Prop :=
  φ.val.map p = ((fun z : ℂ => z) : Germ (𝓝 a) ℂ)

theorem inverseGerm_value {p : ℂ → ℂ} {a : ℂ} {φ : HolomorphicGerm a}
    (hφ : IsInverseGerm p φ) : p φ.value = a := by
  obtain ⟨U, f, ha, hf, he⟩ := φ.property
  have hv : φ.value = f a := by
    change φ.val.value = f a
    rw [← he]; rfl
  rw [hv]
  have h : (p ∘ f) =ᶠ[𝓝 a] (fun z : ℂ => z) := Germ.coe_eq.mp (by
    simpa only [IsInverseGerm, ← he, Germ.map_coe] using hφ)
  exact h.self_of_nhds

/-- A local inverse is fixed by its value, because its defining map is
injective on a neighborhood of that value. -/
theorem inverseGerm_eq {p : ℂ → ℂ} {a : ℂ} {φ ψ : HolomorphicGerm a}
    (hφ : IsInverseGerm p φ) (hψ : IsInverseGerm p ψ)
    (hv : φ.value = ψ.value)
    (hi : ∃ U ∈ 𝓝 φ.value, InjOn p U) : φ = ψ := by
  obtain ⟨V, f, ha, hf, he⟩ := φ.property
  obtain ⟨W, g, hb, hg, hd⟩ := ψ.property
  have hvf : φ.value = f a := by change φ.val.value = f a; rw [← he]; rfl
  have hvg : ψ.value = g a := by change ψ.val.value = g a; rw [← hd]; rfl
  obtain ⟨U, hU, hi⟩ := hi
  have hfu : ∀ᶠ z in 𝓝 a, f z ∈ U := by
    apply (hf.2 a ha).continuousAt.preimage_mem_nhds
    rwa [← hvf]
  have hgu : ∀ᶠ z in 𝓝 a, g z ∈ U := by
    apply (hg.2 a hb).continuousAt.preimage_mem_nhds
    rwa [← hvg, ← hv]
  have hp : (p ∘ f) =ᶠ[𝓝 a] (fun z : ℂ => z) := Germ.coe_eq.mp (by
    simpa only [IsInverseGerm, ← he, Germ.map_coe] using hφ)
  have hq : (p ∘ g) =ᶠ[𝓝 a] (fun z : ℂ => z) := Germ.coe_eq.mp (by
    simpa only [IsInverseGerm, ← hd, Germ.map_coe] using hψ)
  apply Subtype.ext
  rw [← he, ← hd]
  apply Germ.coe_eq.mpr
  filter_upwards [hfu, hgu, hp, hq] with z hz hw hp hq
  exact hi hz hw (hp.trans hq.symm)

/-- The usual inverse-branch interface, kept independent of a chosen branch. -/
def HasInverseBranches (p : ℂ → ℂ) : Prop :=
  ∀ a c : ℂ, a ≠ 0 → p c = a →
    ∃ (U V : Set ℂ) (f : ℂ → ℂ), c ∈ U ∧ a ∈ V ∧ f a = c ∧
      BiholomorphicPair U V p f

theorem inverseBranches_inj {p : ℂ → ℂ} (hp : HasInverseBranches p)
    {a c : ℂ} (ha : a ≠ 0) (hc : p c = a) :
    ∃ U ∈ 𝓝 c, InjOn p U := by
  obtain ⟨U,V,f,hcU,_,_,h⟩ := hp a c ha hc
  exact ⟨U, h.1.1.mem_nhds hcU, h.2.2.2.2.1.injOn⟩

theorem exists_inverseGerm {p : ℂ → ℂ} (hp : HasInverseBranches p)
    {a c : ℂ} (ha : a ≠ 0) (hc : p c = a) :
    ∃ φ : HolomorphicGerm a, IsInverseGerm p φ ∧ φ.value = c := by
  obtain ⟨U,V,f,hcU,haV,hfc,h⟩ := hp a c ha hc
  refine ⟨HolomorphicGerm.ofFunction f h.2.1 haV, ?_, hfc⟩
  apply Germ.coe_eq.mpr
  exact eventually_of_mem (h.2.1.1.mem_nhds haV) (fun z hz => h.2.2.2.2.2 hz)

/-- A continuous lift gives holomorphic continuation of an inverse germ.
Local injectivity of the defining map supplies local representation. -/
theorem continuation_of_lift {p : ℂ → ℂ} (hp : HasInverseBranches p)
    (γ : unitInterval → ℂ) (hγ : Continuous γ) (hne : ∀ t, γ t ≠ 0)
    (L : unitInterval → ℂ) (hL : Continuous L) (hlift : ∀ t, p (L t) = γ t)
    (φ : HolomorphicGerm (γ 0)) (hφ : IsInverseGerm p φ) (hzero : L 0 = φ.value) :
    ∃ Φ : GermFamily γ, IsContinuation {z : ℂ | z ≠ 0} γ φ Φ ∧
      (∀ t, IsInverseGerm p (Φ t)) ∧ (∀ t, (Φ t).value = L t) := by
  choose Φ hΦ hv using fun t => exists_inverseGerm hp (hne t) (hlift t)
  refine ⟨Φ, ⟨?_, hγ, hne, ?_, ?_⟩, hΦ, hv⟩
  · exact ⟨⟨1, one_ne_zero⟩, isOpen_ne_fun continuous_id continuous_const,
      (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) (0 : ℂ)).isPreconnected⟩
  · exact inverseGerm_eq (hΦ 0) hφ ((hv 0).trans hzero)
      (inverseBranches_inj hp (hne 0) (inverseGerm_value (hΦ 0)))
  · apply (locallyRepresented_iff γ Φ).mpr
    intro s
    obtain ⟨U,V,f,hcU,haV,hfc,h⟩ := hp (γ s) (L s) (hne s) (hlift s)
    refine ⟨V, f, h.2.1, ?_⟩
    have hU : ∀ᶠ t in 𝓝 s, L t ∈ U := (hL.tendsto s) (h.1.1.mem_nhds hcU)
    have hV : ∀ᶠ t in 𝓝 s, γ t ∈ V := (hγ.tendsto s) (h.2.1.1.mem_nhds haV)
    filter_upwards [hU, hV] with t ht htV
    refine ⟨htV, ?_⟩
    have hfg : IsInverseGerm p (HolomorphicGerm.ofFunction f h.2.1 htV) := by
      apply Germ.coe_eq.mpr
      exact eventually_of_mem (h.2.1.1.mem_nhds htV) (fun z hz => h.2.2.2.2.2 hz)
    apply inverseGerm_eq (hΦ t) hfg
    · change (Φ t).value = f (γ t)
      rw [hv t, ← hlift t]
      exact (h.2.2.2.2.1 ht).symm
    · exact inverseBranches_inj hp (hne t) (inverseGerm_value (hΦ t))

theorem exp_hasInverseBranches : HasInverseBranches Complex.exp := by
  intro a c ha hc
  obtain ⟨U,V,f,hcU,haV,hfa,h,hder⟩ :=
    LocalLogarithmsRoots.exponential_local_inverse a c (by simpa only [show _root_.D12Complex.E = Complex.exp from Exponential.E_eq_exp] using hc)
  exact ⟨U,V,f,hcU,haV,hfa,by simpa only [show _root_.D12Complex.E = Complex.exp from Exponential.E_eq_exp] using h⟩

theorem pow_hasInverseBranches (n : ℕ) (hn : 0 < n) :
    HasInverseBranches (fun z : ℂ => z ^ n) := by
  intro a c ha hc
  have hcn : c ≠ 0 := by
    intro he
    simp [he, Nat.ne_of_gt hn] at hc
    exact ha hc.symm
  obtain ⟨U,V,f,hcU,haV,hfa,h⟩ :=
    LocalLogarithmsRoots.power_local_inverse n c hn hcn
  exact ⟨U,V,f,hcU,hc ▸ haV,hc ▸ hfa,h⟩

theorem logarithm_continues :
    Specs.D12Complex.Ch19.LogarithmRootMonodromy.logarithm_continues_type := by
  intro γ hγ hne φ hφ
  let : LocallyPathConnectedSpace unitInterval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  obtain ⟨L, ⟨hzero, hlift⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
      ⟨γ,hγ⟩ (inverseGerm_value hφ) (by simpa using hne)
  obtain ⟨Φ,hΦ,hrel,_⟩ := continuation_of_lift exp_hasInverseBranches γ hγ hne
    L L.continuous (fun t => congrFun hlift t) φ hφ hzero
  exact ⟨Φ,hΦ,hrel⟩

theorem root_continues :
    Specs.D12Complex.Ch19.LogarithmRootMonodromy.root_continues_type := by
  intro n hn γ hγ hne φ hφ
  let : LocallyPathConnectedSpace unitInterval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace unitInterval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  obtain ⟨L, ⟨hzero, hlift⟩, _⟩ :=
    (isCoveringMapOn_npow n (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn) : (n : ℂ) ≠ 0)).existsUnique_continuousMap_lifts ⟨γ,hγ⟩ (inverseGerm_value hφ)
        (by simpa using hne)
  obtain ⟨Φ,hΦ,hrel,_⟩ := continuation_of_lift (pow_hasInverseBranches n hn) γ hγ hne
    L L.continuous (fun t => congrFun hlift t) φ hφ hzero
  exact ⟨Φ,hΦ,hrel⟩

theorem normalized_parameter_mem (γ : PiecewiseC1Path) (t : unitInterval) :
    γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ) ∈ Icc γ.path.a γ.path.b := by
  constructor <;> nlinarith [t.property.1, t.property.2, γ.path.ordered]

theorem normalizedPath_continuous (γ : PiecewiseC1Path) : Continuous (normalizedPath γ) := by
  exact γ.path.continuousOn.comp_continuous
    (by fun_prop) (normalized_parameter_mem γ)

@[simp] theorem normalizedPath_zero (γ : PiecewiseC1Path) :
    normalizedPath γ 0 = γ γ.path.a := by simp [normalizedPath]

@[simp] theorem normalizedPath_one (γ : PiecewiseC1Path) :
    normalizedPath γ 1 = γ γ.path.b := by simp [normalizedPath]

/-- The canonical one-path chain index has exactly the normalization in
the paper. This also relates it to the contour integral used below. -/
theorem pathIndex_eq_integral (γ : PiecewiseC1Path) (hne : 0 ∉ γ.trace) :
    pathIndex γ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * γ.integral (fun z => 1 / z) := by
  have htrace : 0 ∉ IntegralChain.trace (Finsupp.single γ 1) := by
    rintro ⟨δ,hδ,hzero⟩
    rw [Finsupp.support_single_ne_zero γ (one_ne_zero : (1 : ℤ) ≠ 0)] at hδ
    have hδγ := Finset.mem_singleton.mp hδ
    subst δ
    exact hne hzero
  rw [pathIndex,IntegralChain.index_eq_integral _ 0 htrace]
  simp [IntegralChain.integral]

/-- Lift on the original compact parameter interval, including a=b. The
constant extension is continuous on ℝ and used only on that interval. -/
theorem exists_interval_log_lift (γ : PiecewiseC1Path) (hne : 0 ∉ γ.trace)
    (c : ℂ) (hc : Complex.exp c = γ γ.path.a) :
    ∃ L : ℝ → ℂ, Continuous L ∧ L γ.path.a = c ∧
      ∀ t ∈ Icc γ.path.a γ.path.b, Complex.exp (L t) = γ t := by
  let A := Icc γ.path.a γ.path.b
  let a₀ : A := ⟨γ.path.a, le_rfl, γ.path.ordered⟩
  let : LocallyPathConnectedSpace A := (convex_Icc γ.path.a γ.path.b).locallyPathConnectedSpace
  let : ContractibleSpace A := (convex_Icc γ.path.a γ.path.b).contractibleSpace ⟨a₀,a₀.property⟩
  obtain ⟨F,⟨hzero,hF⟩,_⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
      (a₀ := a₀) γ.path.onInterval hc (fun t => by
        change γ t ≠ 0
        exact fun h => hne ⟨t,t.property,h⟩)
  let L := IccExtend γ.path.ordered F
  refine ⟨L,F.continuous.Icc_extend',?_,?_⟩
  · change IccExtend γ.path.ordered F γ.path.a = c
    rw [IccExtend_of_mem γ.path.ordered F a₀.property]
    exact hzero
  · intro t ht
    change Complex.exp (IccExtend γ.path.ordered F t) = γ t
    rw [IccExtend_of_mem γ.path.ordered F ht]
    exact congrFun hF ⟨t,ht⟩

/-- A continuous logarithm lift is differentiable wherever the base path is,
provided the exponential identity holds on a parameter neighborhood. -/
theorem log_lift_hasDerivAt {γ L : ℝ → ℂ} {t : ℝ}
    (hL : ContinuousAt L t) (hγ : DifferentiableAt ℝ γ t)
    (he : (fun u => Complex.exp (L u)) =ᶠ[𝓝 t] γ) :
    HasDerivAt L (1 / γ t * deriv γ t) t := by
  have he₀ := he.self_of_nhds
  obtain ⟨U,V,f,hU,hV,hf,hpair,hd⟩ :=
    LocalLogarithmsRoots.exponential_local_inverse (γ t) (L t)
      (by simpa only [show _root_.D12Complex.E = Complex.exp from Exponential.E_eq_exp] using he₀)
  have hnear : ∀ᶠ u in 𝓝 t, L u ∈ U := hL (hpair.1.1.mem_nhds hU)
  have hEq : (f ∘ γ) =ᶠ[𝓝 t] L := by
    filter_upwards [hnear,he] with u hu he
    rw [Function.comp_apply, ← he]
    simpa only [show _root_.D12Complex.E = Complex.exp from Exponential.E_eq_exp] using hpair.2.2.2.2.1 hu
  have hd' : HasDerivAt (f ∘ γ) (1 / γ t * deriv γ t) t := by
    simpa using (hd (γ t) hV).complexToReal_fderiv.comp_hasDerivAt t hγ.hasDerivAt
  exact hd'.congr_of_eventuallyEq hEq.symm

/-- FTC on the actual contour pieces; no differentiability is required at
corners, and a zero-piece partition telescopes to zero. -/
theorem log_lift_endpoint (γ : PiecewiseC1Path) (hne : 0 ∉ γ.trace)
    (L : ℝ → ℂ) (hL : Continuous L)
    (he : ∀ t ∈ Icc γ.path.a γ.path.b, Complex.exp (L t) = γ t) :
    γ.integral (fun z => 1 / z) = L γ.path.b - L γ.path.a := by
  let P := γ.partition
  have hf : ContinuousOn (fun z : ℂ => 1 / z) γ.trace :=
    continuousOn_const.div continuousOn_id (fun z hz => fun h => hne (h ▸ hz))
  have hpieces (i : Fin P.count) :
      (∫ t in P.node i.castSucc..P.node i.succ, 1 / γ t * deriv γ t) =
        L (P.node i.succ) - L (P.node i.castSucc) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (P.piece_lt i).le
      hL.continuousOn
    · intro t ht
      apply log_lift_hasDerivAt (hL.continuousAt) (P.differentiableAt_piece i ht)
      exact eventually_of_mem (Icc_mem_nhds ht.1 ht.2)
        (fun u hu => he u (P.piece_subset i hu))
    · exact P.piece_integrable_deriv _ hf i
  rw [PiecewiseC1Path.integral_eq_partition γ P _ hf,
    C1Partition.integral_eq_intervalIntegral γ.path P _ hf]
  rw [← P.first, ← P.last,
    ← (intervalIntegral_fin_partition P.node _ (P.piece_integrable_deriv _ hf)).2]
  simp_rw [hpieces]
  have htel := (Fin.sum_univ_succ (fun i => L (P.node i))).symm.trans
    (Fin.sum_univ_castSucc (fun i => L (P.node i)))
  rw [Finset.sum_sub_distrib]
  linear_combination htel

theorem logarithm_monodromy :
    Specs.D12Complex.Ch19.LogarithmRootMonodromy.logarithm_monodromy_type := by
  intro γ _hclosed hne φ Φ hφ hΦ
  obtain ⟨L,hL,hzero,he⟩ := exists_interval_log_lift γ hne φ.value
    (by simpa using inverseGerm_value hφ)
  let M := fun t : unitInterval => L (γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ))
  have hM : Continuous M := by fun_prop
  have hγne : ∀ t, normalizedPath γ t ≠ 0 := by
    intro t ht
    exact hne ⟨_,normalized_parameter_mem γ t,ht⟩
  obtain ⟨Ψ,hΨ,hrel,hv⟩ := continuation_of_lift exp_hasInverseBranches
    (normalizedPath γ) (normalizedPath_continuous γ) hγne M hM
    (fun t => he _ (normalized_parameter_mem γ t)) φ hφ (by simpa [M] using hzero)
  have huniq := ContinuationOperations.continuation_unique _ _ φ Φ Ψ hΦ hΨ 1
  have hval : (Φ 1).value = L γ.path.b := by
    rw [huniq,hv 1]; simp [M]
  have hend : (Φ 1).value - φ.value = γ.integral (fun z => 1 / z) := by
    rw [hval, ← hzero]
    exact (log_lift_endpoint γ hne L hL he).symm
  refine ⟨hend,?_⟩
  rw [hend,pathIndex_eq_integral γ hne]
  field_simp

/-- Equality of inverse-branch germs is equivalent to equality of values,
including when the two equal basepoints are presented by different terms. -/
theorem inverseGerm_heq_iff_value {p : ℂ → ℂ} (hp : HasInverseBranches p)
    {a b : ℂ} (hab : a = b) (ha : a ≠ 0) (φ : HolomorphicGerm a)
    (ψ : HolomorphicGerm b) (hφ : IsInverseGerm p φ) (hψ : IsInverseGerm p ψ) :
    HEq φ ψ ↔ φ.value = ψ.value := by
  subst b
  constructor
  · intro h; rw [eq_of_heq h]
  · intro h
    exact heq_of_eq (inverseGerm_eq hφ hψ h
      (inverseBranches_inj hp ha (inverseGerm_value hφ)))

/-- The value calculation implies the full local root relation. -/
theorem root_germ_relation_of_values (n : ℕ) (hn : 0 < n)
    {a b : ℂ} (hab : a = b) (ha : a ≠ 0)
    (φ : HolomorphicGerm a) (ψ : HolomorphicGerm b)
    (hφ : IsRootGerm n φ) (hψ : IsRootGerm n ψ)
    (c : ℂ) (hc : c ^ n = 1) (hv : ψ.value = c * φ.value) :
    ∀ f g : ℂ → ℂ, φ.val = (f : Germ (𝓝 a) ℂ) →
      ψ.val = (g : Germ (𝓝 b) ℂ) → g =ᶠ[𝓝 a] (fun z => c * f z) := by
  subst b
  obtain ⟨U,f₀,haU,hf₀,he₀⟩ := φ.property
  have hcf : HolomorphicOn U (fun z => c * f₀ z) :=
    ⟨hf₀.1,fun z hz => (hf₀.2 z hz).const_mul c⟩
  let χ := HolomorphicGerm.ofFunction (fun z => c * f₀ z) hcf haU
  have hpow : (fun z => f₀ z ^ n) =ᶠ[𝓝 a] (fun z : ℂ => z) :=
    Germ.coe_eq.mp (by simpa only [IsRootGerm,← he₀,Germ.map_coe,Function.comp_def] using hφ)
  have hχ : IsRootGerm n χ := by
    apply Germ.coe_eq.mpr
    filter_upwards [hpow] with z hz
    change (c * f₀ z) ^ n = z
    rw [mul_pow,hc,one_mul,hz]
  have hv₀ : φ.value = f₀ a := by change φ.val.value = f₀ a; rw [← he₀]; rfl
  have heq : ψ = χ := inverseGerm_eq hψ hχ (by
    change ψ.value = c * f₀ a
    rw [hv,hv₀]) (inverseBranches_inj (pow_hasInverseBranches n hn) ha (inverseGerm_value hψ))
  intro f g hf hg
  have hgf : g =ᶠ[𝓝 a] (fun z => c * f₀ z) := Germ.coe_eq.mp (by
    rw [← hg,heq]; rfl)
  have hff : f₀ =ᶠ[𝓝 a] f := Germ.coe_eq.mp (he₀.trans hf)
  filter_upwards [hgf,hff] with z hg hf
  rw [hg,hf]

/-- The exponential kernel gives the exact integer divisibility criterion,
with signed winding numbers. -/
theorem exp_period_div_eq_one_iff (n : ℕ) (hn : 0 < n) (k : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / n) = 1 ↔
      (n : ℤ) ∣ k := by
  let p : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hp : p ≠ 0 := by simp [p,Real.pi_ne_zero]
  have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m,hm⟩
    have he : p * (k : ℂ) = (m : ℂ) * p * (n : ℂ) := (div_eq_iff hn₀).mp hm
    have hk : (k : ℂ) = (n : ℂ) * (m : ℂ) :=
      mul_left_cancel₀ hp (he.trans (by ring))
    refine ⟨m,?_⟩
    exact_mod_cast hk
  · rintro ⟨m,hm⟩
    refine ⟨m,?_⟩
    rw [hm]
    push_cast
    field_simp

theorem root_monodromy :
    Specs.D12Complex.Ch19.LogarithmRootMonodromy.root_monodromy_type := by
  intro n hn γ hclosed hne φ Φ hφ hΦ
  let p : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hp : p ≠ 0 := by simp [p,Real.pi_ne_zero]
  have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  obtain ⟨k,hk⟩ := IndexProperties.closed_path_integral_integer γ hclosed 0 hne
  have hint : γ.integral (fun z => 1 / z) = (k : ℂ) * p := by simpa [p] using hk
  have hindex : pathIndex γ = (k : ℂ) := by
    rw [pathIndex_eq_integral γ hne,hint]
    change p⁻¹ * ((k : ℂ) * p) = (k : ℂ)
    field_simp
  have hγne : ∀ t, normalizedPath γ t ≠ 0 := by
    intro t ht
    exact hne ⟨_,normalized_parameter_mem γ t,ht⟩
  have hr : φ.value ≠ 0 := by
    intro he
    have hv := inverseGerm_value hφ
    rw [he,zero_pow hn.ne'] at hv
    exact hγne 0 hv.symm
  let c : ℂ := (n : ℂ) * Complex.log φ.value
  have hc : Complex.exp c = γ γ.path.a := by
    dsimp [c]
    rw [Complex.exp_nat_mul,Complex.exp_log hr]
    simpa using inverseGerm_value hφ
  obtain ⟨L,hL,hzero,he⟩ := exists_interval_log_lift γ hne c hc
  let R := fun t : unitInterval =>
    Complex.exp (L (γ.path.a + (γ.path.b - γ.path.a) * (t : ℝ)) / n)
  have hR : Continuous R := by fun_prop
  have hRpow : ∀ t, R t ^ n = normalizedPath γ t := by
    intro t
    dsimp [R]
    rw [← Complex.exp_nat_mul,mul_div_cancel₀ _ hn₀]
    exact he _ (normalized_parameter_mem γ t)
  have hRzero : R 0 = φ.value := by
    simp only [R,show ((0 : unitInterval) : ℝ) = 0 from rfl,mul_zero,add_zero,hzero,c,
      mul_div_cancel_left₀ _ hn₀,Complex.exp_log hr]
  obtain ⟨Ψ,hΨ,hrel,hv⟩ := continuation_of_lift (pow_hasInverseBranches n hn)
    (normalizedPath γ) (normalizedPath_continuous γ) hγne R hR hRpow φ hφ hRzero
  have huniq := ContinuationOperations.continuation_unique _ _ φ Φ Ψ hΦ hΨ
  have hΦrel : ∀ t, IsRootGerm n (Φ t) := by
    intro t; rw [huniq t]; exact hrel t
  have hLb : L γ.path.b = c + p * (k : ℂ) := by
    have hi := log_lift_endpoint γ hne L hL he
    rw [hint,hzero] at hi
    linear_combination -hi
  let q : ℂ := Complex.exp (p * (k : ℂ) / n)
  have hqpow : q ^ n = 1 := by
    dsimp [q]
    rw [← Complex.exp_nat_mul,mul_div_cancel₀ _ hn₀,Complex.exp_eq_one_iff]
    exact ⟨k,by ring⟩
  have hvalue : (Φ 1).value = q * φ.value := by
    rw [huniq 1,hv 1]
    simp only [R,show ((1 : unitInterval) : ℝ) = 1 from rfl,mul_one,add_sub_cancel,hLb,add_div,
      Complex.exp_add,c,mul_div_cancel_left₀ _ hn₀,Complex.exp_log hr]
    exact mul_comm _ _
  have hloop : normalizedPath γ 1 = normalizedPath γ 0 := by
    simpa only [normalizedPath_one,normalizedPath_zero,PiecewiseC1Path.IsClosed,
      ComplexPath.IsClosed,ComplexPath.target,ComplexPath.source] using hclosed
  refine ⟨k,hindex,?_,?_⟩
  · exact root_germ_relation_of_values n hn hloop.symm (hγne 0)
      φ (Φ 1) hφ (hΦrel 1) q hqpow hvalue
  · rw [inverseGerm_heq_iff_value (pow_hasInverseBranches n hn) hloop
      (hγne 1) (Φ 1) φ (hΦrel 1) hφ,hvalue]
    have hcancel : q * φ.value = φ.value ↔ q = 1 := by
      constructor
      · intro h; exact mul_right_cancel₀ hr (h.trans (one_mul _).symm)
      · intro h; rw [h,one_mul]
    exact hcancel.trans (exp_period_div_eq_one_iff n hn k)

end D12Complex.LogarithmRootMonodromy
