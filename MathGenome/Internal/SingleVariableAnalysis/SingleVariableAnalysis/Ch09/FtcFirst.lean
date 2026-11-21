import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.FtcFirst
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Accumulation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative

/-! The first fundamental theorem for the proper Darboux accumulation.
The key estimate is proved directly from finite tagged sums and their
Darboux limits. No measure-integral comparison is used. -/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators Topology

/-- A pointwise bound relative to a constant bounds the same centered
quantity for the Darboux limit of tagged sums. -/
theorem FineTaggedLimit.sub_const_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b M : ℝ} {I c : E}
    (hab : a ≤ b) (hf : FineTaggedLimit f a b I)
    (hb : ∀ t ∈ Set.Icc a b, ‖f t - c‖ ≤ M) :
    ‖I - (b-a) • c‖ ≤ (b-a) * M := by
  classical
  have hs (P : Partition a b) (ξ : Tagging P) :
      ‖taggedSum P ξ f - (b-a) • c‖ ≤ (b-a) * M := by
    have he : taggedSum P ξ f - (b-a) • c =
        ∑ i : Fin P.n, cellLength P i • (f (ξ i) - c) := by
      simp only [taggedSum, S.sumValue, smul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_smul, sum_cellLength]
    rw [he]
    calc
      _ ≤ ∑ i : Fin P.n, ‖cellLength P i • (f (ξ i) - c)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin P.n, cellLength P i * M := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cell_positive P i)]
        exact mul_le_mul_of_nonneg_left
          (hb (ξ i) (cell_subset_interval P i (ξ i).property)) (cell_positive P i).le
      _ = (b-a) * M := by rw [← Finset.sum_mul, sum_cellLength]
  by_contra hnot
  have hp : 0 < ‖I - (b-a) • c‖ - (b-a) * M := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨δ, hδ, hc⟩ := hf ((‖I - (b-a) • c‖ - (b-a) * M) / 2) (by positivity)
  obtain ⟨P, hP⟩ := exists_fine_partition hab δ hδ
  obtain ⟨ξ⟩ := tags_exist P
  have herr := hc P ξ hP
  have ht := hs P ξ
  have hn := norm_sub_le_norm_sub_add_norm_sub I (taggedSum P ξ f) ((b-a) • c)
  change ‖taggedSum P ξ f - I‖ < _ at herr
  rw [norm_sub_rev (taggedSum P ξ f) I] at herr
  linarith

/-- The analytic part of FTC: ordered subinterval limits suffice.
This normed-space estimate applies in particular to both manuscript scalars. -/
theorem accumulation_hasRealIncrementDerivativeWithin {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f F : ℝ → E)
    {a b x : ℝ} (hx : x ∈ Set.Icc a b)
    (hc : ContinuousWithinAt f (Set.Icc a b) x)
    (hF : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b, u ≤ v →
      FineTaggedLimit f u v (F v - F u)) :
    HasRealIncrementDerivativeWithin F (f x) (Set.Icc a b) x := by
  apply (withinDerivative_epsilon_iff _ _ _ _).mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp hc (ε/2) (by positivity)
  refine ⟨δ, hδ, fun h hxh hpos hsmall => ?_⟩
  have hnz : h ≠ 0 := abs_pos.mp hpos
  have hbnd (t : ℝ) (ht : t ∈ Set.uIcc x (x+h)) : ‖f t - f x‖ ≤ ε/2 := by
    have htI : t ∈ Set.Icc a b :=
      ⟨(le_min hx.1 hxh.1).trans ht.1, ht.2.trans (max_le hx.2 hxh.2)⟩
    have hdist : |t-x| ≤ |h| := by
      rcases le_total 0 h with hh | hh
      · rw [Set.uIcc_of_le (by linarith)] at ht
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1), abs_of_nonneg hh]
        linarith [ht.1, ht.2]
      · rw [Set.uIcc_of_ge (by linarith)] at ht
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos hh]
        linarith [ht.1, ht.2]
    have htδ : dist t x < δ := by simpa only [Real.dist_eq] using hdist.trans_lt hsmall
    simpa only [dist_eq_norm] using (hd htI htδ).le
  have he : ‖F (x+h) - F x - h • f x‖ ≤ |h| * (ε/2) := by
    rcases le_total 0 h with hh | hh
    · have hb' : ∀ t ∈ Set.Icc x (x+h), ‖f t - f x‖ ≤ ε/2 := by
        simpa only [Set.uIcc_of_le (show x ≤ x+h by linarith)] using hbnd
      have he := (hF x hx (x+h) hxh (by linarith)).sub_const_bound (c := f x)
        (by linarith) hb'
      simpa only [add_sub_cancel_left, abs_of_nonneg hh] using he
    · have hb' : ∀ t ∈ Set.Icc (x+h) x, ‖f t - f x‖ ≤ ε/2 := by
        simpa only [Set.uIcc_of_ge (show x+h ≤ x by linarith)] using hbnd
      have he := (hF (x+h) hxh x hx (by linarith)).sub_const_bound (c := f x)
        (by linarith) hb'
      have hid : F (x+h) - F x - h • f x =
          -(F x - F (x+h) - (x-(x+h)) • f x) := by
        rw [show x-(x+h) = -h by ring, neg_smul]
        abel
      rw [hid, norm_neg, abs_of_nonpos hh]
      simpa only [show x-(x+h) = -h by ring] using he
  have hid : RealIncrementQuotient F x h - f x =
      h⁻¹ • (F (x+h) - F x - h • f x) := by
    rw [smul_sub, inv_smul_smul₀ hnz]
    rfl
  rw [hid, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    _ ≤ |h|⁻¹ * (|h| * (ε/2)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = ε/2 := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    _ < ε := by linarith

/-- Passing from the closed-interval increment filter to the whole right
half-line uses only the positive distance to the other endpoint. -/
theorem derivativeWithin_Icc_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ → E} {L : E} {a b : ℝ} (hab : a < b)
    (hd : HasRealIncrementDerivativeWithin F L (Set.Icc a b) a) :
    HasRealIncrementDerivativeWithin F L (Set.Ici a) a := by
  apply (withinDerivative_epsilon_iff _ _ _ _).mpr
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := (withinDerivative_epsilon_iff _ _ _ _).mp hd ε hε
  refine ⟨min δ (b-a), lt_min hδ (sub_pos.mpr hab), fun h hh hp hs => ?_⟩
  apply hc h ⟨hh, ?_⟩ hp (hs.trans_le (min_le_left _ _))
  have := hs.trans_le (min_le_right δ (b-a))
  linarith [le_abs_self h]

theorem derivativeWithin_Icc_right {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ → E} {L : E} {a b : ℝ} (hab : a < b)
    (hd : HasRealIncrementDerivativeWithin F L (Set.Icc a b) b) :
    HasRealIncrementDerivativeWithin F L (Set.Iic b) b := by
  apply (withinDerivative_epsilon_iff _ _ _ _).mpr
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := (withinDerivative_epsilon_iff _ _ _ _).mp hd ε hε
  refine ⟨min δ (b-a), lt_min hδ (sub_pos.mpr hab), fun h hh hp hs => ?_⟩
  apply hc h ⟨?_, hh⟩ hp (hs.trans_le (min_le_left _ _))
  have := hs.trans_le (min_le_right δ (b-a))
  linarith [neg_abs_le h]

/-- The ambient representation required below always exists; outside [a,b]
its values are unrestricted. -/
theorem real_accumulation_exists :
    Specs.SingleVariableAnalysis.Ch09.FtcFirst.realAccumulationExists := by
  intro f a b hf
  obtain ⟨H, _⟩ := real_accumulation f hf
  obtain ⟨F, hF⟩ := exists_ambientExtension (Set.Icc a b)
    (fun x => realIntegral f (H x))
  exact ⟨F, fun x hx => ⟨H ⟨x, hx⟩, hF ⟨x, hx⟩⟩⟩

theorem complex_accumulation_exists :
    Specs.SingleVariableAnalysis.Ch09.FtcFirst.complexAccumulationExists := by
  intro f a b hf
  obtain ⟨H, _⟩ := complex_accumulation f hf
  obtain ⟨F, hF⟩ := exists_ambientExtension (Set.Icc a b)
    (fun x => complexIntegral f (H x))
  exact ⟨F, fun x hx => ⟨H ⟨x, hx⟩, hF ⟨x, hx⟩⟩⟩

theorem real_ftc_first_within : Specs.SingleVariableAnalysis.Ch09.FtcFirst.realWithin := by
  intro f F a b hf hF x hx hc
  apply accumulation_hasRealIncrementDerivativeWithin f F hx hc
  intro u hu v hv huv
  obtain ⟨hau, hFu⟩ := hF u hu
  obtain ⟨hav, hFv⟩ := hF v hv
  have huvf := RealIntegrable.subinterval hf hu.1 huv hv.2
  have he := (real_split f hu.1 huv (RealIntegrable.bounded hav)).2 hav hau huvf
  have he' : F v - F u = realIntegral f huvf := by rw [hFu, hFv]; linarith
  rw [he']
  exact (real_tagged_equivalence f huv huvf.bounded _).mp ⟨huvf, rfl⟩

theorem complex_ftc_first_within : Specs.SingleVariableAnalysis.Ch09.FtcFirst.complexWithin := by
  intro f F a b hf hF x hx hc
  apply accumulation_hasRealIncrementDerivativeWithin f F hx hc
  intro u hu v hv huv
  obtain ⟨hau, hFu⟩ := hF u hu
  obtain ⟨hav, hFv⟩ := hF v hv
  have huvf := ComplexIntegrable.subinterval hf hu.1 huv hv.2
  have he := (complex_split f hu.1 huv (ComplexIntegrable.norm_bound hav)).2 hav hau huvf
  have he' : F v - F u = complexIntegral f huvf := by rw [hFu, hFv, he]; abel
  rw [he']
  exact (complex_tagged_equivalence f huv huvf.norm_bound _).mp ⟨huvf, rfl⟩

theorem real_ftc_first_interior : Specs.SingleVariableAnalysis.Ch09.FtcFirst.realInterior := by
  intro f F a b hf hF x hx hc
  apply (withinDerivative_interior_iff F (f x) (Set.Icc a b) x
    (by simpa only [interior_Icc] using hx)).mp
  exact real_ftc_first_within f F hf hF x ⟨hx.1.le, hx.2.le⟩ hc

theorem complex_ftc_first_interior : Specs.SingleVariableAnalysis.Ch09.FtcFirst.complexInterior := by
  intro f F a b hf hF x hx hc
  apply (withinDerivative_interior_iff F (f x) (Set.Icc a b) x
    (by simpa only [interior_Icc] using hx)).mp
  exact complex_ftc_first_within f F hf hF x ⟨hx.1.le, hx.2.le⟩ hc

theorem real_ftc_first_leftEndpoint : Specs.SingleVariableAnalysis.Ch09.FtcFirst.realLeftEndpoint := by
  intro f F a b hab hf hF hc
  exact derivativeWithin_Icc_left hab
    (real_ftc_first_within f F hf hF a ⟨le_rfl, hab.le⟩ hc)

theorem real_ftc_first_rightEndpoint : Specs.SingleVariableAnalysis.Ch09.FtcFirst.realRightEndpoint := by
  intro f F a b hab hf hF hc
  exact derivativeWithin_Icc_right hab
    (real_ftc_first_within f F hf hF b ⟨hab.le, le_rfl⟩ hc)

theorem complex_ftc_first_leftEndpoint : Specs.SingleVariableAnalysis.Ch09.FtcFirst.complexLeftEndpoint := by
  intro f F a b hab hf hF hc
  exact derivativeWithin_Icc_left hab
    (complex_ftc_first_within f F hf hF a ⟨le_rfl, hab.le⟩ hc)

theorem complex_ftc_first_rightEndpoint : Specs.SingleVariableAnalysis.Ch09.FtcFirst.complexRightEndpoint := by
  intro f F a b hab hf hF hc
  exact derivativeWithin_Icc_right hab
    (complex_ftc_first_within f F hf hF b ⟨hab.le, le_rfl⟩ hc)

end SingleVariableAnalysis.Riemann
