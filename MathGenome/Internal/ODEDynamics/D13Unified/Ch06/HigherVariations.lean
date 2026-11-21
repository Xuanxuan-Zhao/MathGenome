import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.HigherVariations
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.CkDependence
import MathGenome.MultivariableAnalysis.Topics.D04.C03
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch06.HigherVariations
open StateDerivative C1Dependence CkDependence

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A time slice of the joint flow has exactly the regularity of the field
at every point of its actual existence domain. -/
lemma contDiffAt_flow_state [FiniteDimensional ℝ E] (k : ℕ) (hk : 1 ≤ k)
    (F : AutonomousODE E) (hF : ContDiffOn ℝ k F.eval F.domain)
    {q : ℝ × E} (hq : q ∈ flowDomain F) : ContDiffAt ℝ k (flow F q.1) q.2 := by
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hc := (autonomous_joint_ck k hk F hF).contDiffAt
    ((isOpen_flowDomain F hF1).mem_nhds hq)
  exact hc.comp q.2 (contDiffAt_const.prodMk contDiffAt_id)

lemma flow_zero_eventually [FiniteDimensional ℝ E] (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {ξ : E} (hξ : ξ ∈ F.domain) :
    flow F 0 =ᶠ[𝓝 ξ] id := by
  filter_upwards [F.isOpen_domain.mem_nhds hξ] with η hη
  exact (flow_ivp F hF hη).2.2

lemma iteratedFDeriv_id_ge_two (j : ℕ) (hj : 2 ≤ j) (ξ : E) :
    iteratedFDeriv ℝ j (id : E → E) ξ = 0 := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hj
  have hjn : j = n+1+1 := by omega
  rw [hjn]
  ext v
  rw [iteratedFDeriv_succ_apply_right]
  simp only [fderiv_id]
  rw [iteratedFDeriv_const_of_ne (by omega)]
  simp

theorem initial_values : Specs.D13Unified.Ch06.HigherVariations.InitialValues.{u} := by
  intro E _ _ _ k hk F hF ξ hξ
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have heq := flow_zero_eventually F hF1 hξ
  constructor
  · intro v
    rw [H, heq.iteratedFDeriv ℝ 1 |>.eq_of_nhds]
    simp [iteratedFDeriv_one_apply]
  · intro j hj _
    rw [H, heq.iteratedFDeriv ℝ j |>.eq_of_nhds]
    exact iteratedFDeriv_id_ge_two j hj ξ

theorem spatial_chain_rule :
    Specs.D13Unified.Ch06.HigherVariations.SpatialChainRule.{u} := by
  intro E _ _ _ k hk F hF j _ hj q hq v
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hmem : flow F q.1 q.2 ∈ F.domain := (flow_ivp F hF1 hq.1).1.2.1 q.1 hq.2
  have hg := hF.contDiffAt (F.isOpen_domain.mem_nhds hmem)
  have hf := contDiffAt_flow_state k hk F hF hq
  rw [iteratedFDeriv_comp hg hf (by exact_mod_cast hj)]
  simp only [FormalMultilinearSeries.taylorComp,
    sum_apply, FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply]
  rfl

lemma partitionTerm_oneBlock (F : AutonomousODE E) (j : ℕ) (hj : 0 < j)
    (t : ℝ) (ξ : E) (v : Fin j → E) :
    partitionTerm F (oneBlock j hj) t ξ v =
      fderiv ℝ F.eval (flow F t ξ) (H F j t ξ v) := by
  change iteratedFDeriv ℝ 1 F.eval (flow F t ξ)
    (fun _ => H F j t ξ (v ∘ id)) = _
  rw [iteratedFDeriv_one_apply]
  rfl

/-- Summing block cardinalities counts every direction exactly once. -/
lemma sum_partSize {j : ℕ} (c : OrderedFinpartition j) :
    ∑ i, c.partSize i = j := by
  simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))

lemma partSize_lt_of_one_lt_length {j : ℕ} (c : OrderedFinpartition j)
    (hc : 1 < c.length) (i : Fin c.length) : c.partSize i < j := by
  obtain ⟨l,hl⟩ : ∃ l : Fin c.length, l ≠ i := by
    have : Nontrivial (Fin c.length) := Fin.nontrivial_iff_two_le.mpr hc
    exact exists_ne i
  have hsum : c.partSize i + c.partSize l ≤ ∑ a, c.partSize a := by
    exact Finset.add_le_sum (fun _ _ => Nat.zero_le _) (by simp) (by simp) (Ne.symm hl)
  rw [sum_partSize] at hsum
  have := c.partSize_pos l
  omega

lemma eq_oneBlock_of_length_eq_one {j : ℕ} (hj : 0 < j)
    (c : OrderedFinpartition j) (hc : c.length = 1) : c = oneBlock j hj := by
  rcases c with ⟨l,s,hpos,e,hmono,hparts,hdisj,hcover⟩
  change l = 1 at hc
  subst l
  have hs : s = fun _ => j := by
    funext i
    have hsum := sum_partSize
      (OrderedFinpartition.mk 1 s hpos e hmono hparts hdisj hcover)
    simpa only [Fin.sum_univ_one, Subsingleton.elim i 0] using hsum
  subst s
  have he : e = fun _ => id := by
    funext i
    exact (hmono i).eq_id
  subst e
  rfl

theorem partition_decomposition :
    Specs.D13Unified.Ch06.HigherVariations.PartitionDecomposition.{u} := by
  intro E _ _ F j hj t ξ v
  refine ⟨partitionTerm_oneBlock F j hj t ξ v, ?_,
    fun c hc i => partSize_lt_of_one_lt_length c hc i⟩
  classical
  have hsplit (c : OrderedFinpartition j) :
      partitionTerm F c t ξ v =
        (if c = oneBlock j hj then partitionTerm F c t ξ v else 0) +
        (if 1 < c.length then partitionTerm F c t ξ v else 0) := by
    by_cases hc : c = oneBlock j hj
    · subst c; simp [oneBlock]
    · have hl : 1 < c.length := by
        have hpos := c.length_pos hj
        by_contra! h
        exact hc (eq_oneBlock_of_length_eq_one hj c (by omega))
      simp [hc,hl]
  calc
    partitionSum F j t ξ v =
        (∑ c : OrderedFinpartition j,
          if c = oneBlock j hj then partitionTerm F c t ξ v else 0) +
        lowerForcing F j t ξ v := by
      simp only [partitionSum, lowerForcing, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c _ => hsplit c)
    _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      partitionTerm_oneBlock]; rfl

/-- Parameter-dependent higher state derivatives lose exactly j orders.
This is local, so arbitrary totalizations away from the domain are harmless. -/
lemma contDiffAt_iteratedFDeriv_param : ∀ (j : ℕ),
    ∀ {A B C : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
      [NormedAddCommGroup B] [NormedSpace ℝ B]
      [NormedAddCommGroup C] [NormedSpace ℝ C]
      {f : A → B → C} {g : A → B} {a : A} {m n : ℕ∞ω},
      ContDiffAt ℝ n (Function.uncurry f) (a,g a) →
      ContDiffAt ℝ m g a → m + j ≤ n →
      ContDiffAt ℝ m (fun x => iteratedFDeriv ℝ j (f x) (g x)) a := by
  intro j
  induction j with
  | zero =>
    intro A B C _ _ _ _ _ _ f g a m n hf hg hmn
    have hc := (hf.of_le (by simpa using hmn)).comp a (contDiffAt_id.prodMk hg)
    exact (continuousMultilinearCurryFin0 ℝ B C).symm.contDiff.contDiffAt.comp a hc
  | succ j ih =>
    intro A B C _ _ _ _ _ _ f g a m n hf hg hmn
    have hf' : ContDiffAt ℝ (m+1)
        (fun q : A × B => iteratedFDeriv ℝ j (f q.1) q.2) (a,g a) := by
      apply ih (f := fun q : A × B => f q.1) (g := Prod.snd)
        (n := n) (m := m+1)
      · exact hf.comp ((a,g a),g a)
          (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      · exact contDiffAt_snd
      · simpa only [Nat.cast_succ, add_comm (j : ℕ∞ω) 1, ← add_assoc] using hmn
    have hd := hf'.fderiv (f := fun a b => iteratedFDeriv ℝ j (f a) b) hg (le_refl (m+1))
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) C).symm.contDiff
      |>.contDiffAt.comp a hd

lemma continuousOn_H [FiniteDimensional ℝ E] (k : ℕ) (hk : 1 ≤ k)
    (F : AutonomousODE E) (hF : ContDiffOn ℝ k F.eval F.domain)
    {j : ℕ} (hj : j ≤ k) :
    ContinuousOn (fun q : ℝ × E => H F j q.1 q.2) (flowDomain F) := by
  intro q hq
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hc := (autonomous_joint_ck k hk F hF).contDiffAt
    ((isOpen_flowDomain F hF1).mem_nhds hq)
  have hc' : ContDiffAt ℝ k
      (Function.uncurry (fun q : ℝ × E => flow F q.1)) (q,q.2) :=
    hc.comp (q,q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (contDiffAt_iteratedFDeriv_param j hc' contDiffAt_snd
    (m := 0) (by exact_mod_cast (show 0+j ≤ k by omega))).continuousAt.continuousWithinAt

lemma continuousOn_H_apply [FiniteDimensional ℝ E] (k : ℕ) (hk : 1 ≤ k)
    (F : AutonomousODE E) (hF : ContDiffOn ℝ k F.eval F.domain)
    {j : ℕ} (hj : j ≤ k) (v : Fin j → E) :
    ContinuousOn (fun q : ℝ × E => H F j q.1 q.2 v) (flowDomain F) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E) E v).continuous.comp_continuousOn
    (continuousOn_H k hk F hF hj)

lemma continuousOn_partitionTerm [FiniteDimensional ℝ E] (k : ℕ) (hk : 1 ≤ k)
    (F : AutonomousODE E) (hF : ContDiffOn ℝ k F.eval F.domain)
    {j : ℕ} (hj : j ≤ k) (c : OrderedFinpartition j) (v : Fin j → E) :
    ContinuousOn (fun q : ℝ × E => partitionTerm F c q.1 q.2 v) (flowDomain F) := by
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have houter : ContinuousOn
      (fun q : ℝ × E => iteratedFDeriv ℝ c.length F.eval (flow F q.1 q.2))
      (flowDomain F) :=
    (ContinuousOn.continuousOn_iteratedFDeriv hF F.isOpen_domain
      (by exact_mod_cast c.length_le.trans hj)).comp (continuousOn_flow F hF1)
      (fun q hq => (flow_ivp F hF1 hq.1).1.2.1 q.1 hq.2)
  exact continuous_eval.comp_continuousOn
    (houter.prodMk (continuousOn_pi.mpr (fun i => continuousOn_H_apply k hk F hF
      ((c.partSize_le i).trans hj) (v ∘ c.emb i))))

lemma continuousOn_lowerForcing [FiniteDimensional ℝ E] (k : ℕ) (hk : 1 ≤ k)
    (F : AutonomousODE E) (hF : ContDiffOn ℝ k F.eval F.domain)
    {j : ℕ} (hj : j ≤ k) (v : Fin j → E) :
    ContinuousOn (fun q : ℝ × E => lowerForcing F j q.1 q.2 v) (flowDomain F) := by
  apply continuousOn_finsetSum
  intro c _
  by_cases hc : 1 < c.length
  · simpa only [hc, ite_true] using continuousOn_partitionTerm k hk F hF hj c v
  · simp only [hc, ite_false]; exact continuousOn_const

lemma H_initial_apply [FiniteDimensional ℝ E] (k : ℕ) (hk : 1 ≤ k)
    (F : AutonomousODE E) (hF : ContDiffOn ℝ k F.eval F.domain)
    {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {ξ : E} (hξ : ξ ∈ F.domain)
    (v : Fin j → E) : H F j 0 ξ v = initialValue v := by
  by_cases hj1 : j = 1
  · subst j
    rw [(initial_values k hk F hF ξ hξ).1 v]
    simp [initialValue]
  · have hz := (initial_values k hk F hF ξ hξ).2 j (by omega) hjk
    simp [hz, initialValue, hj1]

/-- Once the top-order time differentiation is established, all linear IVP
and uniqueness assertions follow on the original maximal interval. -/
theorem linear_hierarchy_of_time_equations
    (hTime : Specs.D13Unified.Ch06.HigherVariations.TimeEquations.{u}) :
    Specs.D13Unified.Ch06.HigherVariations.LinearHierarchy.{u} := by
  intro E _ _ _ k hk F hF j hj hjk ξ hξ v
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hx := flow_ivp F hF1 hξ
  have hpath : ContinuousOn (fun t => (t,ξ)) (flowInterval F ξ).carrier :=
    continuousOn_id.prodMk continuousOn_const
  have hmaps : MapsTo (fun t => (t,ξ)) (flowInterval F ξ).carrier (flowDomain F) :=
    fun _ ht => ⟨hξ,ht⟩
  have hH := (continuousOn_H_apply k hk F hF hjk v).comp hpath hmaps
  have hB := (continuousOn_lowerForcing k hk F hF hjk v).comp hpath hmaps
  have hA : ContinuousOn (coefficient F ξ) (flowInterval F ξ).carrier :=
    (hF1.continuousOn_fderiv_of_isOpen F.isOpen_domain le_rfl).comp
      hx.1.1.continuousOn (fun t ht => hx.1.2.1 t ht)
  have h0 := H_initial_apply k hk F hF hj hjk hξ v
  have hd (t : ℝ) (ht : t ∈ (flowInterval F ξ).carrier) :
      HasDerivAt (fun r => H F j r ξ v)
        (coefficient F ξ t (H F j t ξ v) + lowerForcing F j t ξ v) t := by
    have heq := (partition_decomposition F j (by omega) t ξ v).2.1
    have heq' : partitionSum F j t ξ v =
        coefficient F ξ t (H F j t ξ v) + lowerForcing F j t ξ v := heq
    rw [← heq']
    exact hTime k hk F hF j hj hjk (t,ξ) ⟨hξ,ht⟩ v
  refine ⟨hH,h0,hB,hd,?_⟩
  intro Y hY hY0 hYd
  exact linear_uniqueness (flowInterval F ξ) hx.2.1 (coefficient F ξ)
    (fun t => lowerForcing F j t ξ v) (initialValue v) hA hB
    Y (fun t => H F j t ξ v) hY hH hY0 h0 hYd hd

set_option backward.isDefEq.respectTransparency false in
lemma partitionSum_two (F : AutonomousODE E) (t : ℝ) (ξ : E) (v w : E) :
    partitionSum F 2 t ξ ![v,w] =
      coefficient F ξ t (H F 2 t ξ ![v,w]) +
        iteratedFDeriv ℝ 2 F.eval (flow F t ξ)
          ![H F 1 t ξ (fun _ => v), H F 1 t ξ (fun _ => w)] := by
  classical
  have he := (OrderedFinpartition.extendEquiv 1).sum_comp
    (fun c : OrderedFinpartition 2 => partitionTerm F c t ξ ![v,w])
  rw [Fintype.sum_sigma] at he
  simp only [Fintype.sum_unique, OrderedFinpartition.default_eq,
    Fintype.sum_option] at he
  rw [partitionSum, ← he]
  have hmid : (OrderedFinpartition.atomic 1).extend (some ⟨0, by change 0 < 1; omega⟩) = oneBlock 2 (by omega) :=
    eq_oneBlock_of_length_eq_one (by omega) _ rfl
  change partitionTerm F ((OrderedFinpartition.atomic 1).extend none) t ξ ![v,w] +
    (∑ x : Fin 1, partitionTerm F ((OrderedFinpartition.atomic 1).extend (some x)) t ξ ![v,w]) = _
  rw [Fin.sum_univ_one]
  erw [hmid, partitionTerm_oneBlock]
  rw [add_comm]
  congr 1
  change partitionTerm F ((OrderedFinpartition.atomic 1).extendLeft) t ξ ![v,w] = _
  simp [partitionTerm, OrderedFinpartition.extendLeft, OrderedFinpartition.atomic,
    Function.comp_def]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The explicit second equation follows from the two partitions, without
an extra smoothness assumption. -/
theorem second_variation_of_time_equations
    (hTime : Specs.D13Unified.Ch06.HigherVariations.TimeEquations.{u}) :
    Specs.D13Unified.Ch06.HigherVariations.SecondVariation.{u} := by
  intro E _ _ _ k hk F hF ξ hξ v w
  refine ⟨?_,?_⟩
  · rw [(initial_values k (by omega) F hF ξ hξ).2 2 le_rfl hk]
    rfl
  · intro t ht
    have hd := hTime k (by omega) F hF 2 (by omega) hk (t,ξ) ⟨hξ,ht⟩ ![v,w]
    rw [partitionSum_two] at hd
    exact hd

/-- Finite C^j regularity is sufficient for full symmetry. The prior calculus
library uses ordinary small real normed spaces, including all ℝ^n models. -/
theorem symmetry : Specs.D13Unified.Ch06.HigherVariations.Symmetry := by
  intro E _ _ _ k hk F hF j hj hjk q hq v σ
  have hc : ContDiffAt ℝ j (flow F q.1) q.2 :=
    (contDiffAt_flow_state k hk F hF hq).of_le (by exact_mod_cast hjk)
  obtain ⟨V,hV,hcV⟩ := hc.contDiffOn le_rfl (by simp)
  obtain ⟨U,hUV,hU,hqU⟩ := mem_nhds_iff.mp hV
  have hcr := (D04.crOn_iff_contDiffOn j U (flow F q.1) hU).mpr (hcV.mono hUV)
  have hd := D04.crOn_timesDifferentiableAt j U (flow F q.1) hU hcr q.2 hqU
  exact D04.higherDifferential_symmetric j U (flow F q.1) q.2 hd σ v

/-- A compact time interval gives a uniform local bound for a continuous
parameter derivative, hence permits differentiation under the oriented integral.
Only the parameter is differentiated. -/
lemma hasFDerivAt_intervalIntegral
    {B C : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]
    {U : Set B} (hU : IsOpen U) (a b : ℝ)
    (f : ℝ → B → C) (A : ℝ → B → B →L[ℝ] C)
    (hf : ContinuousOn (fun q : ℝ × B => f q.1 q.2) (uIcc a b ×ˢ U))
    (hA : ContinuousOn (fun q : ℝ × B => A q.1 q.2) (uIcc a b ×ˢ U))
    (hd : ∀ t ∈ uIcc a b, ∀ x ∈ U, HasFDerivAt (f t) (A t x) x)
    {x : B} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t in a..b, f t y) (∫ t in a..b, A t x) x := by
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hcomp : IsCompact (uIcc a b ×ˢ Metric.closedBall x r) :=
    isCompact_uIcc.prod (isCompact_closedBall x r)
  obtain ⟨M,hM⟩ := hcomp.exists_bound_of_continuousOn
    (hA.mono (prod_mono (Subset.rfl) hrU))
  have hfc (y : B) (hy : y ∈ U) : ContinuousOn (fun t => f t y) (uIcc a b) :=
    hf.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,hy⟩)
  have hAc : ContinuousOn (fun t => A t x) (uIcc a b) :=
    hA.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht => ⟨ht,hx⟩)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => f t y) (F' := fun y t => A t y)
    (μ := MeasureTheory.volume) (a := a) (b := b)
    (s := Metric.closedBall x r) (bound := fun _ => M)
    (Metric.closedBall_mem_nhds x hr)
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact ((hfc y hy).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact (hfc x hx).intervalIntegrable
  · exact (hAc.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · exact Filter.Eventually.of_forall (fun t ht y hy => hM (t,y) ⟨uIoc_subset_uIcc ht,hy⟩)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t ht y hy => hd t (uIoc_subset_uIcc ht) y (hrU hy))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1500000 in
/-- Finite repeated parameter differentiation of an oriented integral.
Pointwise C^k regularity on the compact-time product suffices; no time
derivative and no derivative of order k+1 is assumed. -/
lemma iteratedFDeriv_intervalIntegral
    {B C : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [CompleteSpace C]
    {U : Set B} (hU : IsOpen U) (a b : ℝ) (k : ℕ) (f : ℝ → B → C)
    (hf : ∀ q ∈ uIcc a b ×ˢ U,
      ContDiffAt ℝ k (fun q : ℝ × B => f q.1 q.2) q)
    (j : ℕ) (hj : j ≤ k) {x : B} (hx : x ∈ U) :
    iteratedFDeriv ℝ j (fun y => ∫ t in a..b, f t y) x =
      ∫ t in a..b, iteratedFDeriv ℝ j (f t) x := by
  have hjet (i : ℕ) (hi : i ≤ k) :
      ContinuousOn (fun q : ℝ × B => iteratedFDeriv ℝ i (f q.1) q.2)
        (uIcc a b ×ˢ U) := by
    intro q hq
    have hc : ContDiffAt ℝ k
        (Function.uncurry (fun q : ℝ × B => f q.1)) (q,q.2) :=
      (hf q hq).comp (q,q.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact (contDiffAt_iteratedFDeriv_param i hc contDiffAt_snd
      (m := 0) (by exact_mod_cast (show 0+i ≤ k by omega))).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun q : ℝ × B => f q.1 q.2) (uIcc a b ×ˢ U) :=
    fun q hq => (hf q hq).continuousAt.continuousWithinAt
  induction j generalizing x with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ B C).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hfc : ContinuousOn (fun t => f t x) (uIcc a b) :=
      hcont.comp (f := fun t : ℝ => (t,x)) (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨ht,hx⟩)
    exact (L.intervalIntegral_comp_comm (hfc.intervalIntegrable (μ := MeasureTheory.volume))).symm
  | succ j ih =>
    let : NormedAddCommGroup (B →L[ℝ] (B [×j]→L[ℝ] C)) := inferInstance
    have hj' : j ≤ k := by omega
    have hA : ContinuousOn
        (fun q : ℝ × B => (iteratedFDeriv ℝ (j+1) (f q.1) q.2).curryLeft)
        (uIcc a b ×ˢ U) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) C).continuous.comp_continuousOn
        (hjet (j+1) hj)
    have hd (t : ℝ) (ht : t ∈ uIcc a b) (y : B) (hy : y ∈ U) :
        HasFDerivAt (iteratedFDeriv ℝ j (f t))
          (iteratedFDeriv ℝ (j+1) (f t) y).curryLeft y := by
      have hc := (hf (t,y) ⟨ht,hy⟩).comp y (contDiffAt_const.prodMk contDiffAt_id)
      exact (hc.differentiableAt_iteratedFDeriv (by exact_mod_cast (show j < k by omega))).hasFDerivAt
    have hD := hasFDerivAt_intervalIntegral hU a b
      (fun t => iteratedFDeriv ℝ j (f t))
      (fun t y => (iteratedFDeriv ℝ (j+1) (f t) y).curryLeft)
      (hjet j hj') hA hd hx
    have heq : iteratedFDeriv ℝ j (fun y => ∫ t in a..b, f t y) =ᶠ[𝓝 x]
        (fun y => ∫ t in a..b, iteratedFDeriv ℝ j (f t) y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hj' hy
    let L : (B →L[ℝ] (B [×j]→L[ℝ] C)) →L[ℝ] (B [×(j+1)]→L[ℝ] C) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) C).symm.toContinuousLinearEquiv.toContinuousLinearMap
    change L (fderiv ℝ (iteratedFDeriv ℝ j (fun y => ∫ t in a..b, f t y)) x) = _
    rw [heq.fderiv_eq, hD.fderiv]
    have hAc : ContinuousOn
        (fun t => (iteratedFDeriv ℝ (j+1) (f t) x).curryLeft) (uIcc a b) :=
      hA.comp (f := fun t : ℝ => (t,x)) (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨ht,hx⟩)
    have hAi : IntervalIntegrable
        (fun t => (iteratedFDeriv ℝ (j+1) (f t) x).curryLeft) MeasureTheory.volume a b :=
      hAc.intervalIntegrable
    erw [← L.intervalIntegral_comp_comm (𝕜 := ℝ) hAi]
    apply intervalIntegral.integral_congr
    intro t _
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => B) C).symm_apply_apply _

set_option maxHeartbeats 1800000 in
/-- The highest available state derivative is differentiable in time even
when the joint flow is only C^k. This uses its integral equation on a compact
enclosure and a common open neighborhood of initial states. -/
lemma time_derivative_H [FiniteDimensional ℝ E] (k : ℕ) (hk : 1 ≤ k)
    (F : AutonomousODE E) (hF : ContDiffOn ℝ k F.eval F.domain)
    (j : ℕ) (hj : j ≤ k) {q : ℝ × E} (hq : q ∈ flowDomain F) :
    HasDerivAt (fun t => H F j t q.2)
      (iteratedFDeriv ℝ j (F.eval ∘ flow F q.1) q.2) q.1 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hx := flow_ivp F hF1 hq.1
  obtain ⟨a,b,h0,ht,hJ⟩ := Ch05.OpenDomain.compact_enclosure
    (flowInterval F q.2) hx.2.1 hq.2
  have h0' : 0 ∈ Icc a b := ⟨h0.1.le,h0.2.le⟩
  obtain ⟨V,hV,hξV,hVF,hVJ,_,_,_⟩ :=
    local_joint_variation F hF1 q.2 hq.1 a b h0' hJ
  let g : ℝ → E → E := fun r η => F.eval (flow F r η)
  have hg (p : ℝ × E) (hp : p ∈ Icc a b ×ˢ V) :
      ContDiffAt ℝ k (fun p : ℝ × E => g p.1 p.2) p := by
    have hpD : p ∈ flowDomain F := ⟨hVF hp.2,hVJ p.2 hp.2 hp.1⟩
    have hm : flow F p.1 p.2 ∈ F.domain :=
      (flow_ivp F hF1 hpD.1).1.2.1 p.1 hpD.2
    exact (hF.contDiffAt (F.isOpen_domain.mem_nhds hm)).comp p
      ((autonomous_joint_ck k hk F hF).contDiffAt ((isOpen_flowDomain F hF1).mem_nhds hpD))
  have hgi (r : ℝ) (hr : r ∈ Icc a b) (η : E) (hη : η ∈ V) :
      flow F r η = η + ∫ s in (0 : ℝ)..r, g s η := by
    have hy := flow_ivp F hF1 (hVF hη)
    have hgc : ContinuousOn (fun s => g s η) (flowInterval F η).carrier :=
      hF1.continuousOn.comp hy.1.1.continuousOn (fun s hs => hy.1.2.1 s hs)
    rw [integral_eq_sub_on_interval (flowInterval F η).ordConnected
      hy.1.1.continuousOn hgc (fun s hs => (hy.1.2.2 s hs).hasDerivWithinAt)
      hy.2.1 (hVJ η hη hr)]
    have hy0 : flow F 0 η = η := hy.2.2
    rw [hy0]
    exact (add_sub_cancel η (flow F r η)).symm
  have hident (r : ℝ) (hr : r ∈ Icc a b) :
      H F j r q.2 = iteratedFDeriv ℝ j (id : E → E) q.2 +
        ∫ s in (0 : ℝ)..r, iteratedFDeriv ℝ j (g s) q.2 := by
    have heq : (fun η => ∫ s in (0 : ℝ)..r, g s η) =ᶠ[𝓝 q.2]
        (fun η => flow F r η - η) := by
      filter_upwards [hV.mem_nhds hξV] with η hη
      have hv := hgi r hr η hη
      rw [hv]
      abel
    have hs : uIcc 0 r ⊆ Icc a b := ordConnected_Icc.uIcc_subset h0' hr
    have hcalc := iteratedFDeriv_intervalIntegral hV 0 r k g
      (fun p hp => hg p ⟨hs hp.1,hp.2⟩) j hj hξV
    have hstate : ContDiffAt ℝ j (flow F r) q.2 :=
      (contDiffAt_flow_state k hk F hF (q := (r,q.2)) ⟨hq.1,hJ hr⟩).of_le (by exact_mod_cast hj)
    have heq' := (heq.iteratedFDeriv ℝ j).eq_of_nhds
    rw [heq'] at hcalc
    erw [iteratedFDeriv_sub_apply hstate contDiffAt_id] at hcalc
    change H F j r q.2 - iteratedFDeriv ℝ j (id : E → E) q.2 = _ at hcalc
    rw [← hcalc]
    abel
  have hjc : ContinuousOn (fun r => iteratedFDeriv ℝ j (g r) q.2) (Icc a b) := by
    intro r hr
    have hc : ContDiffAt ℝ k
        (Function.uncurry (fun p : ℝ × E => g p.1)) ((r,q.2),q.2) :=
      (hg (r,q.2) ⟨hr,hξV⟩).comp ((r,q.2),q.2)
        (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hc' : ContinuousAt
        (fun p : ℝ × E => iteratedFDeriv ℝ j (g p.1) p.2) (r,q.2) :=
      (contDiffAt_iteratedFDeriv_param j hc contDiffAt_snd
        (m := 0) (by exact_mod_cast (show 0+j ≤ k by omega))).continuousAt
    exact (hc'.comp (f := fun s : ℝ => (s,q.2))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hd := (hasDerivWithinAt_integral_on_interval ordConnected_Icc hjc h0'
    (show q.1 ∈ Icc a b from ⟨ht.1.le,ht.2.le⟩)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hda := hd.const_add (iteratedFDeriv ℝ j (id : E → E) q.2)
  apply hda.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  exact hident r hr

theorem time_equations : Specs.D13Unified.Ch06.HigherVariations.TimeEquations.{u} := by
  intro E _ _ _ k hk F hF j hj hjk q hq v
  have hd := time_derivative_H k hk F hF j hjk hq
  have he := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E) E v).hasFDerivAt
    |>.comp_hasDerivAt q.1 hd
  have hsum := spatial_chain_rule k hk F hF j hj hjk q hq v
  exact hsum ▸ he

theorem linear_hierarchy : Specs.D13Unified.Ch06.HigherVariations.LinearHierarchy.{u} :=
  linear_hierarchy_of_time_equations time_equations

theorem second_variation : Specs.D13Unified.Ch06.HigherVariations.SecondVariation.{u} :=
  second_variation_of_time_equations time_equations

end D13Unified.Ch06.HigherVariations
