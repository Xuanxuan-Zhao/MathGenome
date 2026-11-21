import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.UnboundedSpectralCommutation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
import Batteries.Tactic.OpenPrivate

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace
namespace ExpandedFA.Unbounded.UnboundedSpectralCommutation
open MeasurableSpectralCalculus OperatorDomainsSpec HilbertAdjointSpec
open UnboundedNormalSpectralTheorem UnboundedNormalSpectralTheorem.SpectralRepresentation
open SpectralMeasure
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The geometric bound allows an arbitrary fixed prefactor. -/
theorem projected_zero_of_geometric_bound (M Q : H →L[ℂ] H)
    (a r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (har : a * r < 1)
    (hM : ‖M‖ ≤ a) (hQ : ∀ y, ‖Q y‖ ≤ ‖y‖) (hMQ : M * Q = M)
    (x : ℕ → H) (K : ℝ) (hstep : ∀ n, M (x (n + 1)) = Q (x n))
    (hbound : ∀ n, ‖x n‖ ≤ r ^ n * K) : Q (x 0) = 0 := by
  have heq (n : ℕ) : Q (x 0) = (M ^ n) (Q (x n)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp]
      have h := congrArg (fun T : H →L[ℂ] H => T (x (n + 1))) hMQ
      change M (Q (x (n + 1))) = M (x (n + 1)) at h
      rw [h, hstep n]
      exact ih
  have hMn (n : ℕ) (y : H) : ‖(M ^ n) y‖ ≤ a ^ n * ‖y‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      calc
        _ ≤ ‖M‖ * ‖(M ^ n) y‖ := M.le_opNorm _
        _ ≤ a * (a ^ n * ‖y‖) := mul_le_mul hM ih (norm_nonneg _) ha
        _ = a ^ (n + 1) * ‖y‖ := by rw [pow_succ]; ring
  have hb (n : ℕ) : ‖Q (x 0)‖ ≤ (a * r) ^ n * K := by
    rw [heq n]
    calc
      _ ≤ a ^ n * ‖Q (x n)‖ := hMn n _
      _ ≤ a ^ n * (r ^ n * K) := mul_le_mul_of_nonneg_left
        ((hQ _).trans (hbound n)) (pow_nonneg ha n)
      _ = (a * r) ^ n * K := by rw [mul_pow]; ring
  have ht : Tendsto (fun n : ℕ => (a * r) ^ n * K) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg ha hr) har).mul_const K
  have hn : ‖Q (x 0)‖ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Eventually.of_forall hb)
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))



/-- Intrinsic spectral-disk characterization with a fixed growth prefactor. -/
theorem disk_fixed_of_geometric_bound {E : ProjectionValuedMeasure ℂ H}
    (C : BoundedRealization E) (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (x : ℕ → H) (K : ℝ)
    (hx : ∀ n, x n ∈ (measurableIntegral C (fun w : ℂ => w)).domain)
    (hstep : ∀ n, measurableIntegral C (fun w : ℂ => w) ⟨x n, hx n⟩ =
      z • x n + x (n + 1))
    (hbound : ∀ n, ‖x n‖ ≤ r ^ n * K) :
    E (Metric.closedBall z r) (x 0) = x 0 := by
  classical
  have hout (s : ℝ) (hrs : r < s) : E (Metric.closedBall z s)ᶜ (x 0) = 0 := by
    have hs : 0 < s := hr.trans_lt hrs
    let B := (Metric.closedBall z s)ᶜ
    have hB : MeasurableSet B := measurableSet_closedBall.compl
    let g : ℂ → ℂ := B.indicator (fun w => (w - z)⁻¹)
    let b : ℂ → ℂ := B.indicator (fun _ => 1)
    have hb : SpectralMeasure.Spec.IsBoundedMeasurable b :=
      BorelNormSpectrum.bounded_indicator B hB (BorelNormSpectrum.bounded_const 1)
    have hdist (w : ℂ) (hw : w ∈ B) : s ≤ ‖w - z‖ := by
      have hnot : ¬ ‖w - z‖ ≤ s := by simpa [B, Metric.mem_closedBall, dist_eq_norm] using hw
      exact (lt_of_not_ge hnot).le
    have hne (w : ℂ) (hw : w ∈ B) : w - z ≠ 0 :=
      norm_pos_iff.mp (hs.trans_le (hdist w hw))
    have hgb (w : ℂ) : ‖g w‖ ≤ s⁻¹ := by
      by_cases hw : w ∈ B
      · simpa [g, hw, norm_inv] using inv_anti₀ hs (hdist w hw)
      · simp [g, hw, hs.le]
    have hg : SpectralMeasure.Spec.IsBoundedMeasurable g :=
      ⟨(measurable_id.sub measurable_const).inv.indicator hB, s⁻¹, hgb⟩
    have hprod : (fun w : ℂ => w) * g = z • g + b := by
      funext w
      by_cases hw : w ∈ B
      · simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          g, b, Set.indicator_of_mem hw]
        field_simp [hne w hw]
        ring
      · simp [g, b, hw]
    have hfg : SpectralMeasure.Spec.IsBoundedMeasurable ((fun w : ℂ => w) * g) := by
      rw [hprod]
      exact (hg.smul z).add hb
    let M := C.integral g
    let Q := E B
    have hi : C.integral ((fun w : ℂ => w) * g) = z • M + Q := by
      rw [hprod, C.add _ _ (hg.smul z) hb, C.smul z _ hg,
        integral_indicator_one C B hB]
    have hMQ : M * Q = M := by
      have hgg : B.indicator g = g := by
        funext w
        by_cases hw : w ∈ B <;> simp [g, hw]
      exact (integral_indicator C B hB g hg).symm.trans (congrArg C.integral hgg)
    have hrec (n : ℕ) : M (x (n + 1)) = Q (x n) := by
      have hh := bounded_product_commutes C measurable_id hg hfg ⟨x n, hx n⟩
      change M ((measurableIntegral C (fun w : ℂ => w)) ⟨x n, hx n⟩) =
        C.integral ((fun w : ℂ => w) * g) (x n) at hh
      rw [hstep n, map_add, map_smul, hi] at hh
      change z • M (x n) + M (x (n + 1)) = z • M (x n) + Q (x n) at hh
      exact add_left_cancel hh
    have har : s⁻¹ * r < 1 := by
      calc
        s⁻¹ * r = r / s := by rw [div_eq_mul_inv]; ring
        _ < 1 := (div_lt_one hs).mpr hrs
    exact projected_zero_of_geometric_bound M Q s⁻¹ r (inv_nonneg.mpr hs.le) hr har
      (C.bound g s⁻¹ hg (inv_nonneg.mpr hs.le) hgb)
      (fun y => E.norm_apply_le B hB y) hMQ x K hrec hbound
  let D := (Metric.closedBall z r)ᶜ
  let I := {s : ℝ // r < s}
  let B (s : I) := (Metric.closedBall z (s : ℝ))ᶜ
  have hcover : D ⊆ ⋃ s : I, B s := by
    intro w hw
    have hdist : r < dist w z := by simpa [D, Metric.mem_closedBall] using hw
    obtain ⟨s, hrs, hsw⟩ := exists_between hdist
    exact mem_iUnion.mpr ⟨⟨s, hrs⟩, by simpa [B, Metric.mem_closedBall] using hsw⟩
  obtain ⟨t, ht, htc⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover
    B (fun _ => Metric.isClosed_closedBall.isOpen_compl) hcover
  have hnull (s : I) : C.measure (x 0) (B s) = 0 := by
    rw [C.measure_apply _ _ measurableSet_closedBall.compl, hout s s.property]
    simp
  have hm : C.measure (x 0) D = 0 := measure_mono_null htc
    ((measure_biUnion_null_iff ht).mpr (fun s _ => hnull s))
  rw [C.measure_apply _ _ measurableSet_closedBall.compl, ENNReal.ofReal_eq_zero] at hm
  have hzero : E D (x 0) = 0 := by
    have hn : ‖E D (x 0)‖ = 0 := by
      nlinarith [sq_nonneg ‖E D (x 0)‖, norm_nonneg (E D (x 0))]
    exact norm_eq_zero.mp hn
  let A := Metric.closedBall z r
  have hA : MeasurableSet A := measurableSet_closedBall
  have hind : A.indicator (fun _ => (1 : ℂ)) + D.indicator (fun _ => 1) = fun _ => 1 := by
    funext w
    by_cases hw : w ∈ A <;> simp [D, A] at hw ⊢
  have hsum := C.add _ _ (BorelNormSpectrum.bounded_indicator A hA
    (BorelNormSpectrum.bounded_const 1)) (BorelNormSpectrum.bounded_indicator D hA.compl
      (BorelNormSpectrum.bounded_const 1))
  rw [hind, C.one, integral_indicator_one C A hA, integral_indicator_one C D hA.compl] at hsum
  have hh := congrArg (fun T : H →L[ℂ] H => T (x 0)) hsum
  change x 0 = E A (x 0) + E D (x 0) at hh
  rw [hzero, add_zero] at hh
  exact hh.symm



/-- Commutation as an operator inclusion is precisely invariance of its graph
under the diagonal action of the bounded map. -/
theorem product_le_iff_graph (A : Operator ℂ H H) (B : H →L[ℂ] H) :
    productValue (boundedOperator B) A ≤ productValue A (boundedOperator B) ↔
      ∀ x y, (x, y) ∈ A.graph → (B x, B y) ∈ A.graph := by
  have hb (x y : H) : (x, y) ∈ (boundedOperator B).graph ↔ B x = y := by
    simp [boundedOperator, LinearPMap.mem_graph_iff]
  constructor
  · intro h x y hxy
    have hp : (x, B y) ∈ (productValue (boundedOperator B) A).graph :=
      (mem_product_graph_iff _ _ _ _).mpr ⟨y, hxy, (hb _ _).mpr rfl⟩
    obtain ⟨v, hv, hvy⟩ := (mem_product_graph_iff _ _ _ _).mp
      (LinearPMap.le_graph_of_le h hp)
    rwa [← (hb _ _).mp hv] at hvy
  · intro h
    apply LinearPMap.le_of_le_graph
    rintro ⟨x, z⟩ hxz
    obtain ⟨y, hxy, hyz⟩ := (mem_product_graph_iff _ _ _ _).mp hxz
    refine (mem_product_graph_iff _ _ _ _).mpr ⟨B x, (hb _ _).mpr rfl, ?_⟩
    rw [← (hb _ _).mp hyz]
    exact h x y hxy

/-- Taking the bounded adjoint transfers graph invariance to the unbounded
adjoint. No manipulation of formally undefined operator products is used. -/
theorem adjoint_graph_preserving (A : Operator ℂ H H) (hd : DenselyDefined A)
    (B : H →L[ℂ] H)
    (hB : ∀ x y, (x, y) ∈ A.graph → (B x, B y) ∈ A.graph) :
    ∀ x y, (x, y) ∈ (hilbertAdjoint A).graph →
      (B.adjoint x, B.adjoint y) ∈ (hilbertAdjoint A).graph := by
  intro x y hxy
  apply (mem_hilbertAdjoint_graph_iff A hd _ _).mpr
  intro v
  have hv := hB _ _ (A.mem_graph v)
  obtain ⟨w, hw, hwv⟩ := A.mem_graph_iff.mp hv
  have ht := (mem_hilbertAdjoint_graph_iff A hd x y).mp hxy w
  dsimp only at hw hwv
  rw [B.adjoint_inner_right, B.adjoint_inner_right]
  rwa [hw, hwv] at ht

/-- Every bounded map preserving the coordinate operator graph preserves
each closed spectral disk. The norm of B only changes the prefactor. -/
theorem disk_invariant {E : ProjectionValuedMeasure ℂ H}
    (C : BoundedRealization E) (B : H →L[ℂ] H)
    (hB : ∀ x y, (x, y) ∈ (measurableIntegral C (fun z : ℂ => z)).graph →
      (B x, B y) ∈ (measurableIntegral C (fun z : ℂ => z)).graph)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (x : H)
    (hx : E (Metric.closedBall z r) x = x) :
    E (Metric.closedBall z r) (B x) = B x := by
  obtain ⟨a, ha0, _, hag, hab⟩ := disk_sequence C z r hr x hx
  let b : ℕ → H := fun n => B (a n)
  have hbg (n : ℕ) : (b n, z • b n + b (n + 1)) ∈
      (measurableIntegral C (fun z : ℂ => z)).graph := by
    simpa only [map_add, map_smul] using hB _ _ (hag n)
  have hbm (n : ℕ) : b n ∈ (measurableIntegral C (fun z : ℂ => z)).domain :=
    LinearPMap.mem_domain_of_mem_graph (hbg n)
  have hstep (n : ℕ) : measurableIntegral C (fun z : ℂ => z) ⟨b n, hbm n⟩ =
      z • b n + b (n + 1) :=
    (measurableIntegral C (fun z : ℂ => z)).mem_graph_snd_inj
      ((measurableIntegral C (fun z : ℂ => z)).mem_graph ⟨b n, hbm n⟩) (hbg n) rfl
  have hbound (n : ℕ) : ‖b n‖ ≤ r ^ n * (‖B‖ * ‖x‖) := by
    calc
      _ ≤ ‖B‖ * ‖a n‖ := B.le_opNorm _
      _ ≤ ‖B‖ * (r ^ n * ‖x‖) := mul_le_mul_of_nonneg_left (hab n) (norm_nonneg B)
      _ = _ := by ring
  simpa only [b, ha0] using
    disk_fixed_of_geometric_bound C z r hr b (‖B‖ * ‖x‖) hbm hstep hbound

/-- Invariance for B and its adjoint makes a spectral disk reducing. -/
theorem disk_commutes {E : ProjectionValuedMeasure ℂ H}
    (C : BoundedRealization E) (B : H →L[ℂ] H)
    (hB : ∀ x y, (x, y) ∈ (measurableIntegral C (fun z : ℂ => z)).graph →
      (B x, B y) ∈ (measurableIntegral C (fun z : ℂ => z)).graph)
    (hBadj : ∀ x y, (x, y) ∈ (measurableIntegral C (fun z : ℂ => z)).graph →
      (B.adjoint x, B.adjoint y) ∈ (measurableIntegral C (fun z : ℂ => z)).graph)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) : Commute B (E (Metric.closedBall z r)) := by
  let P := E (Metric.closedBall z r)
  have hp : P * P = P := E.idempotent _ measurableSet_closedBall
  have hleft : P * B * P = B * P := by
    ext x
    apply disk_invariant C B hB z r hr (P x)
    exact congrArg (fun T : H →L[ℂ] H => T x) hp
  have hright : P * B.adjoint * P = B.adjoint * P := by
    ext x
    apply disk_invariant C B.adjoint hBadj z r hr (P x)
    exact congrArg (fun T : H →L[ℂ] H => T x) hp
  have hstar := congrArg star hright
  have hPstar : star P = P := (E.selfAdjoint _ measurableSet_closedBall).star_eq
  simp only [star_mul, hPstar, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_adjoint] at hstar
  change B * P = P * B
  exact hleft.symm.trans ((mul_assoc _ _ _).trans hstar)


open private closedBalls borel_generateFrom_closedBalls from
  MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem

/-- Equality of the two scalar coefficient measures extends disk commutation
to the Borel sigma algebra. No common control measure is required. -/
theorem commutes_of_disks (E : ProjectionValuedMeasure ℂ H) (B : H →L[ℂ] H)
    (hballs : ∀ z : ℂ, ∀ r : ℝ, 0 ≤ r → Commute B (E (Metric.closedBall z r))) :
    ∀ S : Set ℂ, MeasurableSet S → Commute B (E S) := by
  have hbase (S : Set ℂ) (hS : S ∈ closedBalls) : Commute B (E S) := by
    obtain ⟨z, r, rfl⟩ := hS
    by_cases hr : 0 ≤ r
    · exact hballs z r hr
    · rw [Metric.closedBall_of_neg (not_le.mp hr), E.map_empty]
      exact Commute.zero_right B
  have hmeas (S : Set ℂ) (hS : S ∈ closedBalls) : MeasurableSet S := by
    obtain ⟨z, r, rfl⟩ := hS
    exact measurableSet_closedBall
  have hpi (S : Set ℂ) (hS : S ∈ generatePiSystem closedBalls) : Commute B (E S) := by
    induction hS using generatePiSystem_induction with
    | base S hS => exact hbase S hS
    | inter S T hS hT _ ihS ihT =>
      rw [← E.inter S T (generatePiSystem_measurableSet hmeas S hS)
        (generatePiSystem_measurableSet hmeas T hT)]
      exact ihS.mul_right ihT
  have hgen : (inferInstance : MeasurableSpace ℂ) =
      MeasurableSpace.generateFrom (generatePiSystem closedBalls) := by
    rw [generateFrom_generatePiSystem_eq]
    exact borel_generateFrom_closedBalls
  have hcoeff (x y : H) : E.coefficientMeasure (B.adjoint x) y = E.coefficientMeasure x (B y) := by
    refine VectorMeasure.ext_of_generateFrom (generatePiSystem closedBalls) ?_ hgen
      (isPiSystem_generatePiSystem closedBalls) ?_
    · intro S hS
      have hm := generatePiSystem_measurableSet hmeas S hS
      rw [E.coefficientMeasure_apply _ _ S hm, E.coefficientMeasure_apply _ _ S hm]
      change inner ℂ (B.adjoint x) (E S y) = inner ℂ x (E S (B y))
      rw [B.adjoint_inner_left]
      exact congrArg (fun T : H →L[ℂ] H => inner ℂ x (T y)) (hpi S hS).eq
    · rw [E.coefficientMeasure_apply _ _ univ MeasurableSet.univ,
        E.coefficientMeasure_apply _ _ univ MeasurableSet.univ]
      change inner ℂ (B.adjoint x) (E univ y) = inner ℂ x (E univ (B y))
      rw [E.univ]
      simpa only [one_apply_eq_self] using B.adjoint_inner_left y x
  intro S hS
  change B * E S = E S * B
  ext y
  apply ext_inner_left ℂ
  intro x
  have h := congrArg (fun μ : ComplexMeasure ℂ => μ S) (hcoeff x y)
  rw [E.coefficientMeasure_apply _ _ S hS, E.coefficientMeasure_apply _ _ S hS] at h
  change inner ℂ x (B (E S y)) = inner ℂ x (E S (B y))
  rw [← B.adjoint_inner_left]
  exact h

/-- Simple integrals commute term by term; their uniform limits commute too. -/
theorem bounded_integral_commutes {S : Type*} [MeasurableSpace S]
    {E : ProjectionValuedMeasure S H} (C : BoundedRealization E) (B : H →L[ℂ] H)
    (hB : ∀ A : Set S, MeasurableSet A → Commute B (E A))
    (f : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    Commute B (C.integral f) := by
  have hs (a : SimpleFunc S ℂ) : Commute B (SpectralMeasure.Spec.SimpleIntegralValue E a) := by
    classical
    unfold SpectralMeasure.Spec.SimpleIntegralValue
    change B * (∑ c ∈ a.range, c • E (a ⁻¹' {c})) =
      (∑ c ∈ a.range, c • E (a ⁻¹' {c})) * B
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    apply Finset.sum_congr rfl
    intro c hc
    rw [(hB _ (a.measurableSet_fiber c)).eq]
  obtain ⟨a, ha⟩ := SpectralMeasure.exists_uniform_simple_approx f hf
  have ht := C.uniform_limit f hf a ha
  exact tendsto_nhds_unique (tendsto_const_nhds.mul ht)
    ((ht.mul_const B).congr' (Eventually.of_forall fun n => (hs (a n)).eq.symm))

/-- Commuting with all bounded truncations passes to the full convergence
domain and its value. This proves domain preservation without an added
integrability assumption on Bx. -/
theorem measurable_graph_commutes {S : Type*} [MeasurableSpace S]
    {E : ProjectionValuedMeasure S H} (C : BoundedRealization E) (B : H →L[ℂ] H)
    (hB : ∀ A : Set S, MeasurableSet A → Commute B (E A))
    (f : S → ℂ) (hf : Measurable f) :
    ∀ x y, (x, y) ∈ (measurableIntegral C f).graph →
      (B x, B y) ∈ (measurableIntegral C f).graph := by
  intro x y hxy
  have ht := (mem_limitOperator_graph_iff _ x y).mp hxy
  apply (mem_limitOperator_graph_iff _ _ _).mpr
  have heq (n : ℕ) : C.integral (truncation f n) (B x) =
      B (C.integral (truncation f n) x) :=
    congrArg (fun T : H →L[ℂ] H => T x)
      (bounded_integral_commutes C B hB _ (boundedMeasurable_truncation hf n)).eq.symm
  simpa only [heq, Function.comp_def] using (B.continuous.tendsto y).comp ht

/-- Commutation in the unbounded Borel calculus, with exact product domains. -/
theorem spectral_commutation : Spec.SpectralCommutation.{u} := by
  intro H _ _ _ N hd hc hn B hBN hBNstar E C hCN
  have hB := (product_le_iff_graph N B).mp hBN
  have hBs := (product_le_iff_graph (hilbertAdjoint N) B).mp hBNstar
  have hds : DenselyDefined (hilbertAdjoint N) :=
    (isClosable_iff_dense_hilbertAdjoint N hd).mp hc.isClosable
  have hBadj := adjoint_graph_preserving (hilbertAdjoint N) hds B hBs
  rw [hilbertAdjoint_hilbertAdjoint_of_closed N hd hc] at hBadj
  have hcomm : ∀ S : Set ℂ, MeasurableSet S → Commute B (E S) := by
    apply commutes_of_disks E B
    intro z r hr
    apply disk_commutes C B
      (by simpa only [hCN] using hB) (by simpa only [hCN] using hBadj) z r hr
  refine ⟨hcomm, ?_⟩
  intro f hf
  have hg := measurable_graph_commutes C B hcomm f hf
  refine ⟨?_, (product_le_iff_graph _ _).mpr hg⟩
  intro x hx
  exact LinearPMap.mem_domain_of_mem_graph
    (hg x _ ((measurableIntegral C f).mem_graph ⟨x, hx⟩))

end ExpandedFA.Unbounded.UnboundedSpectralCommutation
