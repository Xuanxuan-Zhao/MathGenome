import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.PathAlgebra
import MathGenome.Internal.MultivariableAnalysis.D04.C09.Reparametrization
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace D04.C09.PathAlgebra
open Specs.D04.C01.EuclideanInterfaces.Model
open D04.C09
open D04.C09.Reparametrization
open SingleVariableAnalysis.Riemann

abbrev reverse := @Specs.D04.C09.PathAlgebra.Model.reverse
abbrev concatenate := @Specs.D04.C09.PathAlgebra.Model.concatenate
abbrev rescaledConcatenate := @Specs.D04.C09.PathAlgebra.Model.rescaledConcatenate

/-- Reflection is a regular change of parameters, also on a singleton. -/
def reverseChange {a b : ℝ} (hab : a ≤ b) : ParameterChange a b a b := by
  let P : Partition a b := Classical.choice (partition_exists hab)
  have hs : Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution.C1OnInterval
      (fun t => a+b-t) (fun _ => -1) a b := by
    refine ⟨by fun_prop, ?_⟩
    intro t _
    convert ((hasDerivAt_id t).const_sub (a+b)).hasDerivWithinAt using 1 <;> simp
  have hsm : ∀ i : Fin P.n,
      Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution.C1OnInterval
        (fun t => a+b-t) (fun _ => -1) (P.point i.castSucc) (P.point i.succ) := by
    intro i
    exact ⟨hs.1.mono (cell_subset_interval P i),
      fun t ht => (hs.2 t (cell_subset_interval P i ht)).mono (cell_subset_interval P i)⟩
  refine ⟨hab, hab, (fun t => a+b-t), (fun t => a+b-t), by fun_prop,
    by fun_prop, ?_, ?_, ?_, ?_, ⟨P, fun _ _ => -1, hsm⟩,
    ⟨P, fun _ _ => -1, hsm⟩, ?_⟩
  · intro t ht; constructor <;> linarith [ht.1, ht.2]
  · intro t ht; constructor <;> linarith [ht.1, ht.2]
  · intro t _; ring
  · intro t _; ring
  · intro i t _; norm_num

lemma reverseChange_anti {a b : ℝ} (hab : a ≤ b) :
    StrictAntiOn (reverseChange hab) (Icc a b) := by
  intro x _ y _ hxy
  change a+b-y < a+b-x
  linarith

theorem reverse_apply {n a b} (γ : IntervalPath n a b) t :
    reverse γ t = γ (a+b-t) := rfl

theorem reverse_piecewiseC1 {n a b} (γ : IntervalPath n a b) :
    PiecewiseC1 γ → PiecewiseC1 (reverse γ) :=
  piecewiseC1_reparametrize γ (reverseChange γ.ordered)

theorem length_reverse {n a b} (γ : IntervalPath n a b) :
    length (reverse γ) a b = length γ a b :=
  length_reparametrize γ (reverseChange γ.ordered)

theorem scalar_reverse {n a b} {γ : IntervalPath n a b}
    (v : PiecewiseC1Data γ) (w : PiecewiseC1Data (reverse γ)) (f : E n → ℝ)
    (hv : ScalarIntegrable v f) (hw : ScalarIntegrable w f) :
    scalarLineIntegral w f hw = scalarLineIntegral v f hv :=
  scalar_reparametrize (reverseChange γ.ordered) v w f hv hw

theorem covector_reverse {n a b} {γ : IntervalPath n a b}
    (v : PiecewiseC1Data γ) (w : PiecewiseC1Data (reverse γ))
    (α : E n → E n →L[ℝ] ℝ) (hv : CovectorIntegrable v α) (hw : CovectorIntegrable w α) :
    covectorLineIntegral w α hw = -covectorLineIntegral v α hv :=
  covector_reparametrize_decreasing (reverseChange γ.ordered)
    (reverseChange_anti γ.ordered) v w α hv hw

lemma concatenate_left {n a c b} (γ : IntervalPath n a c) (η : IntervalPath n c b)
    (h : γ c = η c) : EqOn (concatenate γ η h) γ (Icc a c) := by
  intro t ht
  exact ite_eq_left ht.2

lemma concatenate_right {n a c b} (γ : IntervalPath n a c) (η : IntervalPath n c b)
    (h : γ c = η c) : EqOn (concatenate γ η h) η (Icc c b) := by
  intro t ht
  change (if t ≤ c then γ t else η t) = η t
  split_ifs with hc
  · have : t = c := le_antisymm hc ht.1
    simpa [this] using h
  · rfl

lemma length_congr {n} {γ η : ℝ → E n} {a b} (hab : a ≤ b)
    (he : EqOn γ η (Icc a b)) : length γ a b = length η a b := by
  rw [length_eq_variation γ hab, length_eq_variation η hab]
  exact eVariationOn.congr he

theorem length_concatenate {n a c b} (γ : IntervalPath n a c) (η : IntervalPath n c b)
    (h : γ c = η c) :
    length (concatenate γ η h) a b = length γ a c + length η c b := by
  rw [length_add _ γ.ordered η.ordered,
    length_congr γ.ordered (concatenate_left γ η h),
    length_congr η.ordered (concatenate_right γ η h)]

/-- A uniform bound on the integrand by speed passes to its piece integral. -/
lemma pieceIntegral_bound {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (H : E n → E n → ℝ) (h : PieceIntegrable d H)
    (M : ℝ) (hM : ∀ i, ∀ t ∈ cell d.partition i,
      |H (γ t) (d.velocity i t)| ≤ M * ‖d.velocity i t‖) :
    |pieceIntegral d H h| ≤ M * (length γ a b).toReal := by
  have hv := speed_integrable d
  have hnonneg : 0 ≤ piecewiseSpeedIntegral d hv := by
    apply Finset.sum_nonneg
    intro i _
    obtain ⟨hz, hzero⟩ := real_zero_value (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le
    have := realIntegral_mono (fun _ => 0) (fun t => ‖d.velocity i t‖) hz (hv i)
      (fun _ _ => norm_nonneg _)
    simpa only [hzero] using this
  have hlen : (length γ a b).toReal = piecewiseSpeedIntegral d hv := by
    rw [(length_speed_integral d hv).1, ENNReal.toReal_ofReal hnonneg]
  rw [hlen]
  change |∑ i, realIntegral _ (h i)| ≤ M * ∑ i, realIntegral _ (hv i)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨hn, hnorm, _⟩ := real_norm_estimate _ (h i)
  obtain ⟨hg, hge⟩ := real_mul_value (hv i) M
  rw [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  rw [← hge]
  apply realIntegral_mono _ _ hn hg
  intro t ht
  simpa only [Real.norm_eq_abs] using hM i t ht

theorem scalar_bound {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (f : E n → ℝ) (h : ScalarIntegrable d f) (M : ℝ)
    (hM : ∀ x ∈ trace γ, |f x| ≤ M) :
    |scalarLineIntegral d f h| ≤ M * (length γ a b).toReal := by
  apply pieceIntegral_bound d _ h M
  intro i t ht
  rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (hM _ ⟨t, cell_subset_interval d.partition i ht, rfl⟩) (norm_nonneg _)

theorem covector_bound {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ)
    (h : CovectorIntegrable d α) (M : ℝ) (hM : ∀ x ∈ trace γ, ‖α x‖ ≤ M) :
    |covectorLineIntegral d α h| ≤ M * (length γ a b).toReal := by
  apply pieceIntegral_bound d _ h M
  intro i t ht
  have he : |α (γ t) (d.velocity i t)| ≤ ‖α (γ t)‖ * ‖d.velocity i t‖ := by
    simpa only [Real.norm_eq_abs] using (α (γ t)).le_opNorm (d.velocity i t)
  exact he.trans
    (mul_le_mul_of_nonneg_right
      (hM _ ⟨t, cell_subset_interval d.partition i ht, rfl⟩) (norm_nonneg _))

theorem scalar_sup_bound {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (f : E n → ℝ) (h : ScalarIntegrable d f)
    (hM : BddAbove ((fun x => |f x|) '' trace γ)) :
    |scalarLineIntegral d f h| ≤ sSup ((fun x => |f x|) '' trace γ) * (length γ a b).toReal := by
  apply scalar_bound d f h
  intro x hx
  exact le_csSup hM ⟨x, hx, rfl⟩

theorem covector_sup_bound {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ) (h : CovectorIntegrable d α)
    (hM : BddAbove ((fun x => ‖α x‖) '' trace γ)) :
    |covectorLineIntegral d α h| ≤ sSup ((fun x => ‖α x‖) '' trace γ) * (length γ a b).toReal := by
  apply covector_bound d α h
  intro x hx
  exact le_csSup hM ⟨x, hx, rfl⟩

@[simp] lemma join_left_start {a c b} (P : Partition a c) (Q : Partition c b) (i : Fin P.n) :
    (joinPartition P Q).point (i.castAdd Q.n).castSucc = P.point i.castSucc :=
  join_point_left P Q i.castSucc _ rfl
@[simp] lemma join_left_end {a c b} (P : Partition a c) (Q : Partition c b) (i : Fin P.n) :
    (joinPartition P Q).point (i.castAdd Q.n).succ = P.point i.succ :=
  join_point_left P Q i.succ _ rfl
@[simp] lemma join_right_start {a c b} (P : Partition a c) (Q : Partition c b) (i : Fin Q.n) :
    (joinPartition P Q).point (i.natAdd P.n).castSucc = Q.point i.castSucc :=
  join_point_right P Q i.castSucc _ rfl
@[simp] lemma join_right_end {a c b} (P : Partition a c) (Q : Partition c b) (i : Fin Q.n) :
    (joinPartition P Q).point (i.natAdd P.n).succ = Q.point i.succ :=
  join_point_right P Q i.succ _ (by change P.n + i.val + 1 = P.n + (i.val + 1); omega)

lemma join_cell_left {a c b} (P : Partition a c) (Q : Partition c b) (i : Fin P.n) :
    cell (joinPartition P Q) (i.castAdd Q.n) = cell P i := by
  change Icc _ _ = Icc _ _
  rw [join_point_left P Q i.castSucc _ rfl, join_point_left P Q i.succ _ rfl]

lemma join_cell_right {a c b} (P : Partition a c) (Q : Partition c b) (i : Fin Q.n) :
    cell (joinPartition P Q) (i.natAdd P.n) = cell Q i := by
  change Icc _ _ = Icc _ _
  rw [join_point_right P Q i.castSucc _ rfl,
    join_point_right P Q i.succ _ (by change P.n + i.val + 1 = P.n + (i.val + 1); omega)]

/-- The glued subdivision uses precisely the original velocities on its two parts. -/
def concatenateData {n a c b} {γ : IntervalPath n a c} {η : IntervalPath n c b}
    (h : γ c = η c) (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η) :
    PiecewiseC1Data (concatenate γ η h) where
  partition := joinPartition v.partition w.partition
  velocity := Fin.addCases v.velocity w.velocity
  smooth := by
    apply Fin.addCases
    · intro i
      simp only [Fin.addCases_left]
      change C1Piece (concatenate γ η h) (v.velocity i)
        ((joinPartition v.partition w.partition).point (i.castAdd w.partition.n).castSucc)
        ((joinPartition v.partition w.partition).point (i.castAdd w.partition.n).succ)
      rw [join_left_start, join_left_end]
      refine ⟨(v.smooth i).1, ?_⟩
      intro t ht
      exact ((v.smooth i).2 t ht).congr_of_mem
        (fun y hy => concatenate_left γ η h (cell_subset_interval v.partition i hy)) ht
    · intro i
      simp only [Fin.addCases_right]
      change C1Piece (concatenate γ η h) (w.velocity i)
        ((joinPartition v.partition w.partition).point (i.natAdd v.partition.n).castSucc)
        ((joinPartition v.partition w.partition).point (i.natAdd v.partition.n).succ)
      rw [join_right_start, join_right_end]
      refine ⟨(w.smooth i).1, ?_⟩
      intro t ht
      exact ((w.smooth i).2 t ht).congr_of_mem
        (fun y hy => concatenate_right γ η h (cell_subset_interval w.partition i hy)) ht

theorem concatenate_piecewiseC1 {n a c b} (γ : IntervalPath n a c) (η : IntervalPath n c b)
    (h : γ c = η c) :
    PiecewiseC1 γ → PiecewiseC1 η → PiecewiseC1 (concatenate γ η h) := by
  rintro ⟨v⟩ ⟨w⟩
  exact ⟨concatenateData h v w⟩

/-- Gluing preserves arbitrary proper Riemann data, without continuity of H. -/
lemma pieceIntegral_concatenateData {n a c b} {γ : IntervalPath n a c}
    {η : IntervalPath n c b} (h : γ c = η c) (v : PiecewiseC1Data γ)
    (w : PiecewiseC1Data η) (H : E n → E n → ℝ)
    (hv : PieceIntegrable v H) (hw : PieceIntegrable w H) :
    ∃ hz : PieceIntegrable (concatenateData h v w) H,
      pieceIntegral (concatenateData h v w) H hz = pieceIntegral v H hv + pieceIntegral w H hw := by
  have hl (i : Fin v.partition.n) := riemann_congr (hv i)
    (g := fun t => H ((concatenate γ η h) t) (v.velocity i t)) (by
      intro t ht
      dsimp only
      rw [concatenate_left γ η h (cell_subset_interval v.partition i ht)])
  have hr (i : Fin w.partition.n) := riemann_congr (hw i)
    (g := fun t => H ((concatenate γ η h) t) (w.velocity i t)) (by
      intro t ht
      dsimp only
      rw [concatenate_right γ η h (cell_subset_interval w.partition i ht)])
  choose hli hle using hl
  choose hri hre using hr
  have hz : PieceIntegrable (concatenateData h v w) H := by
    apply Fin.addCases
    · intro i
      simpa only [concatenateData, Fin.addCases_left, join_left_start, join_left_end] using hli i
    · intro i
      simpa only [concatenateData, Fin.addCases_right, join_right_start, join_right_end] using hri i
  refine ⟨hz, ?_⟩
  change (∑ i : Fin (v.partition.n + w.partition.n), realIntegral _ (hz i)) = _
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simpa only [concatenateData, Fin.addCases_left, join_left_start, join_left_end] using hle i
  · apply Finset.sum_congr rfl
    intro i _
    simpa only [concatenateData, Fin.addCases_right, join_right_start, join_right_end] using hre i

lemma pieceIntegral_concatenate {n a c b} {γ : IntervalPath n a c}
    {η : IntervalPath n c b} (h : γ c = η c) (v : PiecewiseC1Data γ)
    (w : PiecewiseC1Data η) (z : PiecewiseC1Data (concatenate γ η h))
    (H : E n → E n → ℝ) (hv : PieceIntegrable v H) (hw : PieceIntegrable w H)
    (hz : PieceIntegrable z H) :
    pieceIntegral z H hz = pieceIntegral v H hv + pieceIntegral w H hw := by
  obtain ⟨hz', he⟩ := pieceIntegral_concatenateData h v w H hv hw
  exact (pieceIntegral_independent z (concatenateData h v w) H hz hz').trans he

theorem scalar_concatenate {n a c b} {γ : IntervalPath n a c} {η : IntervalPath n c b}
    (h : γ c = η c) (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η)
    (z : PiecewiseC1Data (concatenate γ η h)) (f : E n → ℝ)
    (hv : ScalarIntegrable v f) (hw : ScalarIntegrable w f) (hz : ScalarIntegrable z f) :
    scalarLineIntegral z f hz = scalarLineIntegral v f hv + scalarLineIntegral w f hw :=
  pieceIntegral_concatenate h v w z _ hv hw hz

theorem covector_concatenate {n a c b} {γ : IntervalPath n a c} {η : IntervalPath n c b}
    (h : γ c = η c) (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η)
    (z : PiecewiseC1Data (concatenate γ η h)) (α : E n → E n →L[ℝ] ℝ)
    (hv : CovectorIntegrable v α) (hw : CovectorIntegrable w α) (hz : CovectorIntegrable z α) :
    covectorLineIntegral z α hz = covectorLineIntegral v α hv + covectorLineIntegral w α hw :=
  pieceIntegral_concatenate h v w z _ hv hw hz

lemma velocity_constant {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (x : E n) (hx : ∀ t ∈ Icc a b, γ t = x) (i : Fin d.partition.n)
    (t : ℝ) (ht : t ∈ cell d.partition i) : d.velocity i t = 0 := by
  have h0 : HasDerivWithinAt γ 0 (cell d.partition i) t :=
    (hasDerivWithinAt_const t (cell d.partition i) x).congr_of_mem
      (fun y hy => hx y (cell_subset_interval d.partition i hy)) ht
  have hu := uniqueDiffOn_Icc (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))) t ht
  exact (((d.smooth i).2 t ht).derivWithin hu).symm.trans (h0.derivWithin hu)

lemma pieceIntegral_zero {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (H : E n → E n → ℝ) (hH : ∀ i, ∀ t ∈ cell d.partition i,
      H (γ t) (d.velocity i t) = 0) :
    ∃ h : PieceIntegrable d H, pieceIntegral d H h = 0 := by
  have hz (i : Fin d.partition.n) := real_zero_value
    (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le
  choose hzero hval using hz
  have hg (i : Fin d.partition.n) := riemann_congr (hzero i)
    (g := fun t => H (γ t) (d.velocity i t)) (by intro t ht; exact (hH i t ht).symm)
  choose hi he using hg
  refine ⟨hi, ?_⟩
  change (∑ i, realIntegral _ (hi i)) = 0
  apply Finset.sum_eq_zero
  intro i _
  exact (he i).trans (hval i)

theorem constant_integrals {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (x : E n) (hx : ∀ t ∈ Icc a b, γ t = x)
    (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ) :
    ∃ hf : ScalarIntegrable d f, ∃ hα : CovectorIntegrable d α,
      length γ a b = 0 ∧ scalarLineIntegral d f hf = 0 ∧ covectorLineIntegral d α hα = 0 := by
  obtain ⟨hf, hfe⟩ := pieceIntegral_zero d (fun x v => f x * ‖v‖) (by
    intro i t ht; rw [velocity_constant d x hx i t ht]; simp)
  obtain ⟨hα, hαe⟩ := pieceIntegral_zero d (fun x v => α x v) (by
    intro i t ht; rw [velocity_constant d x hx i t ht]; simp)
  exact ⟨hf, hα, (length_congr γ.ordered hx).trans (length_constant x a b), hfe, hαe⟩

theorem degenerate_integrals {n a} {γ : IntervalPath n a a}
    (d : PiecewiseC1Data γ) (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ) :
    ∃ hf : ScalarIntegrable d f, ∃ hα : CovectorIntegrable d α,
      length γ a a = 0 ∧ scalarLineIntegral d f hf = 0 ∧ covectorLineIntegral d α hα = 0 := by
  exact ⟨pieceIntegrable_degenerate d _, pieceIntegrable_degenerate d _, length_degenerate γ a,
    scalarLineIntegral_degenerate d f _, covectorLineIntegral_degenerate d α _⟩

/-- Globally differentiable scalar affine maps provide closed-piece C¹ data. -/
def globalScalarData (f : ℝ → ℝ) (r : ℝ) (hf : ∀ t, HasDerivAt f r t)
    {a b : ℝ} (hab : a ≤ b) : ScalarC1Data f a b where
  partition := Classical.choice (partition_exists hab)
  derivative _ _ := r
  smooth _ := ⟨continuousOn_const, fun t _ => (hf t).hasDerivWithinAt⟩

/-- Increasing affine placement, including translations of a singleton interval. -/
def affineChange (r k : ℝ) (hr : 0 < r) {c d : ℝ} (hcd : c ≤ d) :
    ParameterChange (r*c+k) (r*d+k) c d := by
  have horder : r*c+k ≤ r*d+k := by nlinarith
  refine ⟨hcd, horder, (fun t => r*t+k), (fun t => (t-k)/r), by fun_prop,
    by fun_prop, ?_, ?_, ?_, ?_,
    globalScalarData (fun t => r*t+k) r ?_ hcd,
    globalScalarData (fun t => (t-k)/r) (1/r) ?_ horder, ?_⟩
  · intro t ht; constructor <;> nlinarith [ht.1, ht.2]
  · intro t ht
    constructor
    · apply (le_div_iff₀ hr).mpr; nlinarith [ht.1]
    · apply (div_le_iff₀ hr).mpr; nlinarith [ht.2]
  · intro t _; field_simp; ring
  · intro t _; field_simp; ring
  · intro t
    convert ((hasDerivAt_id t).const_mul r).add_const k using 1 <;> simp
  · intro t
    convert ((hasDerivAt_id t).sub_const k).div_const r using 1 <;> simp
  · intro i t _; exact ne_of_gt hr

theorem affine_parameter_exists {a b c d r k : ℝ} (hcd : c ≤ d) (hr : 0 < r)
    (ha : r*c+k = a) (hb : r*d+k = b) :
    ∃ h : ParameterChange a b c d, (∀ t, h t = r*t+k) ∧
      StrictMonoOn h (Icc c d) := by
  subst a; subst b
  refine ⟨affineChange r k hr hcd, fun _ => rfl, ?_⟩
  intro x _ y _ hxy
  change r*x+k < r*y+k
  nlinarith

theorem concatenate_integrable {n a c b} {γ : IntervalPath n a c}
    {η : IntervalPath n c b} (h : γ c = η c) (v : PiecewiseC1Data γ)
    (w : PiecewiseC1Data η) (H : E n → E n → ℝ)
    (hv : PieceIntegrable v H) (hw : PieceIntegrable w H) :
    ∃ z : PiecewiseC1Data (concatenate γ η h), ∃ hz : PieceIntegrable z H,
      pieceIntegral z H hz = pieceIntegral v H hv + pieceIntegral w H hw := by
  obtain ⟨hz, he⟩ := pieceIntegral_concatenateData h v w H hv hw
  exact ⟨concatenateData h v w, hz, he⟩

theorem rescaled_endpoints_match {n a₁ b₁ a₂ b₂ a c b}
    (γ : IntervalPath n a₁ b₁) (η : IntervalPath n a₂ b₂)
    (h₁ : ParameterChange a₁ b₁ a c) (h₂ : ParameterChange a₂ b₂ c b)
    (hm₁ : StrictMonoOn h₁ (Icc a c)) (hm₂ : StrictMonoOn h₂ (Icc c b))
    (h : γ b₁ = η a₂) : (reparametrize γ h₁) c = (reparametrize η h₂) c := by
  change γ (h₁ c) = η (h₂ c)
  rw [(endpoints_increasing h₁ hm₁).2, (endpoints_increasing h₂ hm₂).1]
  exact h

theorem rescaled_concatenate {n a₁ b₁ a₂ b₂ a c b}
    {γ : IntervalPath n a₁ b₁} {η : IntervalPath n a₂ b₂}
    (h₁ : ParameterChange a₁ b₁ a c) (h₂ : ParameterChange a₂ b₂ c b)
    (hm₁ : StrictMonoOn h₁ (Icc a c)) (hm₂ : StrictMonoOn h₂ (Icc c b))
    (h : (reparametrize γ h₁) c = (reparametrize η h₂) c)
    (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η)
    (v' : PiecewiseC1Data (reparametrize γ h₁)) (w' : PiecewiseC1Data (reparametrize η h₂))
    (z : PiecewiseC1Data (rescaledConcatenate γ η h₁ h₂ h))
    (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ)
    (hf : ScalarIntegrable v f) (hg : ScalarIntegrable w f)
    (hf' : ScalarIntegrable v' f) (hg' : ScalarIntegrable w' f) (hz : ScalarIntegrable z f)
    (hα : CovectorIntegrable v α) (hβ : CovectorIntegrable w α)
    (hα' : CovectorIntegrable v' α) (hβ' : CovectorIntegrable w' α) (hζ : CovectorIntegrable z α) :
    length (rescaledConcatenate γ η h₁ h₂ h) a b = length γ a₁ b₁ + length η a₂ b₂ ∧
    scalarLineIntegral z f hz = scalarLineIntegral v f hf + scalarLineIntegral w f hg ∧
    covectorLineIntegral z α hζ = covectorLineIntegral v α hα + covectorLineIntegral w α hβ := by
  refine ⟨?_, ?_, ?_⟩
  · exact (length_concatenate _ _ h).trans
      (congrArg₂ (· + ·) (length_reparametrize γ h₁) (length_reparametrize η h₂))
  · exact (scalar_concatenate h v' w' z f hf' hg' hz).trans
      (congrArg₂ (· + ·) (scalar_reparametrize h₁ v v' f hf hf')
        (scalar_reparametrize h₂ w w' f hg hg'))
  · exact (covector_concatenate h v' w' z α hα' hβ' hζ).trans
      (congrArg₂ (· + ·) (covector_reparametrize_increasing h₁ hm₁ v v' α hα hα')
        (covector_reparametrize_increasing h₂ hm₂ w w' α hβ hβ'))

/-- Substitution constructs integrable data for both kinds of line integral on
one common path partition. No continuity of the fields is needed. -/
lemma reparametrize_integrable_data {n a b c d} {γ : IntervalPath n a b}
    (h : ParameterChange a b c d) (inc : Bool) (hm : Oriented h inc)
    (v : PiecewiseC1Data γ) (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ)
    (hf : ScalarIntegrable v f) (hα : CovectorIntegrable v α) :
    ∃ w : PiecewiseC1Data (reparametrize γ h), ∃ hw : ScalarIntegrable w f,
      ∃ hβ : CovectorIntegrable w α,
      scalarLineIntegral w f hw = scalarLineIntegral v f hf ∧
      covectorLineIntegral w α hβ = (if inc then 1 else -1) * covectorLineIntegral v α hα := by
  obtain ⟨R, hR, hQ, _⟩ := joint_partition h inc hm v.partition
  have hH (x : E n) (r : ℝ) (z : E n) :
      f x * ‖r • z‖ = |r| * (f x * ‖z‖) := by
    rw [norm_smul, Real.norm_eq_abs]; ring
  have hA (x : E n) (r : ℝ) (z : E n) : α x (r • z) = r * α x z := by simp
  obtain ⟨hw, hwe⟩ := pieceIntegral_composeData h true inc hm v R hR hQ _ hH hf
  obtain ⟨hβ, hβe⟩ := pieceIntegral_composeData h false inc hm v R hR hQ _ hA hα
  refine ⟨composeData h inc hm v R hR hQ, hw, hβ, ?_, ?_⟩
  · simpa [scalarLineIntegral, Specs.D04.C09.LineIntegrals.Model.scalarLineIntegral] using hwe
  · simpa [covectorLineIntegral, Specs.D04.C09.LineIntegrals.Model.covectorLineIntegral] using hβe

theorem reverse_integrable {n a b} {γ : IntervalPath n a b} (v : PiecewiseC1Data γ)
    (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ)
    (hf : ScalarIntegrable v f) (hα : CovectorIntegrable v α) :
    ∃ w : PiecewiseC1Data (reverse γ), ∃ hw : ScalarIntegrable w f,
      ∃ hβ : CovectorIntegrable w α,
      scalarLineIntegral w f hw = scalarLineIntegral v f hf ∧
      covectorLineIntegral w α hβ = -covectorLineIntegral v α hα := by
  obtain ⟨w, hw, hβ, hwe, hβe⟩ := reparametrize_integrable_data (reverseChange γ.ordered) false
    (reverseChange_anti γ.ordered) v f α hf hα
  refine ⟨w, hw, hβ, hwe, ?_⟩
  simpa only [Bool.false_eq_true, ↓reduceIte, neg_one_mul] using hβe

theorem arbitrary_concatenate {n a₁ b₁ a₂ b₂} {γ : IntervalPath n a₁ b₁}
    {η : IntervalPath n a₂ b₂} (h : γ b₁ = η a₂)
    (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η)
    (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ)
    (hf : ScalarIntegrable v f) (hg : ScalarIntegrable w f)
    (hα : CovectorIntegrable v α) (hβ : CovectorIntegrable w α) :
    ∃ κ : IntervalPath n a₁ (b₁+(b₂-a₂)), ∃ z : PiecewiseC1Data κ,
      ∃ hz : ScalarIntegrable z f, ∃ hζ : CovectorIntegrable z α,
      (∀ t ∈ Icc a₁ b₁, κ t = γ t) ∧
      (∀ t ∈ Icc b₁ (b₁+(b₂-a₂)), κ t = η (t+a₂-b₁)) ∧
      length κ a₁ (b₁+(b₂-a₂)) = length γ a₁ b₁ + length η a₂ b₂ ∧
      scalarLineIntegral z f hz = scalarLineIntegral v f hf + scalarLineIntegral w f hg ∧
      covectorLineIntegral z α hζ = covectorLineIntegral v α hα + covectorLineIntegral w α hβ := by
  obtain ⟨h₂, hformula, hm₂⟩ := affine_parameter_exists
    (a := a₂) (b := b₂) (c := b₁) (d := b₁+(b₂-a₂)) (r := 1) (k := a₂-b₁)
    (by linarith [η.ordered]) (by norm_num) (by ring) (by ring)
  have hjoin : γ b₁ = (reparametrize η h₂) b₁ := by
    change γ b₁ = η (h₂ b₁)
    rw [(endpoints_increasing h₂ hm₂).1]
    exact h
  obtain ⟨w', hg', hβ', hge, hβe⟩ := reparametrize_integrable_data h₂ true hm₂ w f α hg hβ
  let z := concatenateData hjoin v w'
  obtain ⟨hz, hze⟩ := pieceIntegral_concatenateData hjoin v w' (fun x u => f x * ‖u‖) hf hg'
  obtain ⟨hζ, hζe⟩ := pieceIntegral_concatenateData hjoin v w' (fun x u => α x u) hα hβ'
  refine ⟨concatenate γ (reparametrize η h₂) hjoin, z, hz, hζ,
    concatenate_left γ (reparametrize η h₂) hjoin, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [concatenate_right γ (reparametrize η h₂) hjoin ht]
    change η (h₂ t) = η (t+a₂-b₁)
    rw [hformula]
    congr 1; ring
  · rw [length_concatenate, length_reparametrize]
  · exact hze.trans (congrArg (scalarLineIntegral v f hf + ·) hge)
  · exact hζe.trans (congrArg (covectorLineIntegral v α hα + ·) (by
      simpa [covectorLineIntegral, Specs.D04.C09.LineIntegrals.Model.covectorLineIntegral] using hβe))

end D04.C09.PathAlgebra
