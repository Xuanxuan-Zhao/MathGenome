import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.ApproximateIdentity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Order
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Continuous
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.UniformContinuity

/-! Elementary approximate identities for the proper Darboux integral.
The uniform error estimate passes the finite triangle inequality for positive
weighted tagged sums to their fine-mesh limits. The normalization subtracts
exactly f(x). The modulus is a finite supremum because f is globally bounded;
uniform continuity makes it small at all sufficiently small positive radii.
The explicit triangular kernel is integrated by splitting at zero and using
a telescoping quadrature estimate for affine functions on each half.
-/
namespace SingleVariableAnalysis.ApproximateIdentity
open Filter
open scoped Topology BigOperators
open SingleVariableAnalysis.Riemann
namespace A
export Specs.SingleVariableAnalysis.Ch16.ApproximateIdentity
  (modulusType modulusValue triangleType triangleValue realApproximation complexApproximation triangularKernel)
end A

noncomputable def modulusOfContinuity : A.modulusType := A.modulusValue
noncomputable def triangleKernel : A.triangleType := A.triangleValue

variable {E : Type} [NormedAddCommGroup E]

lemma modulus_bdd {f : ℝ → E} (hb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) (δ : ℝ) :
    BddAbove {r : ℝ | ∃ x y : ℝ, |x-y| ≤ δ ∧ r = ‖f x-f y‖} := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨2*M, ?_⟩
  rintro r ⟨x,y,_,rfl⟩
  exact (norm_sub_le _ _).trans (by linarith [hM x, hM y])

lemma modulus_nonempty (f : ℝ → E) {δ : ℝ} (hδ : 0 ≤ δ) :
    {r : ℝ | ∃ x y : ℝ, |x-y| ≤ δ ∧ r = ‖f x-f y‖}.Nonempty :=
  ⟨0, 0, 0, by simpa using hδ, by simp⟩

lemma le_modulus {f : ℝ → E} (hb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    {δ x y : ℝ} (hxy : |x-y| ≤ δ) : ‖f x-f y‖ ≤ A.modulusValue f δ :=
  le_csSup (modulus_bdd hb δ) ⟨x,y,hxy,rfl⟩

lemma modulus_nonneg {f : ℝ → E} (hb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ A.modulusValue f δ := by
  simpa using le_modulus hb (x := 0) (y := 0) (by simpa using hδ)

lemma modulus_small {f : ℝ → E} (hu : UniformContinuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ δ, 0 ≤ δ → δ < η → A.modulusValue f δ ≤ ε := by
  obtain ⟨η,hη,hh⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨η,hη,fun δ hδ hd => csSup_le (modulus_nonempty f hδ) ?_⟩
  rintro r ⟨x,y,hxy,rfl⟩
  have hhxy := hh (a := x) (b := y) (show dist x y < η by
    simpa only [Real.dist_eq] using hxy.trans_lt hd)
  exact (show ‖f x-f y‖ < ε by simpa only [dist_eq_norm] using hhxy).le

lemma uniform_of_error {f : ℝ → E} (hu : UniformContinuous f)
    {δ : ℕ → ℝ} (hδ : ∀ j, 0 ≤ δ j) (ht : Tendsto δ atTop (𝓝 0))
    (T : ℕ → ℝ → E) (he : ∀ j x, ‖T j x-f x‖ ≤ A.modulusValue f (δ j)) :
    TendstoUniformly T f atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨η,hη,hh⟩ := modulus_small hu (half_pos hε)
  filter_upwards [ht.eventually (gt_mem_nhds hη)] with j hj x
  rw [dist_eq_norm, norm_sub_rev]
  exact (he j x).trans_lt ((hh _ (hδ j) hj).trans_lt (half_lt_self hε))

section TaggedEstimates
variable [NormedSpace ℝ E]

lemma tagged_smul_const (k : ℝ → ℝ) (c : E) {a b : ℝ}
    (P : Partition a b) (ξ : Tagging P) :
    taggedSum P ξ (fun t => k t • c) = taggedSum P ξ k • c := by
  simp only [taggedSum, S.sumValue, smul_smul, smul_eq_mul, Finset.sum_smul]

lemma limit_smul_const {k : ℝ → ℝ} {a b J : ℝ}
    (hk : FineTaggedLimit k a b J) (c : E) :
    FineTaggedLimit (fun t => k t • c) a b (J • c) := by
  intro ε hε
  obtain ⟨η,hη,hh⟩ := hk (ε / (‖c‖ + 1)) (by positivity)
  refine ⟨η,hη,fun P ξ hP => ?_⟩
  change ‖taggedSum P ξ (fun t => k t • c) - J • c‖ < ε
  rw [tagged_smul_const, ← sub_smul, norm_smul]
  have hd := (lt_div_iff₀ (by positivity : 0 < ‖c‖ + 1)).mp (hh P ξ hP)
  nlinarith [norm_nonneg (taggedSum P ξ k - J), norm_nonneg c]

lemma limit_congr {f g : ℝ → E} {a b : ℝ} {I : E}
    (hf : FineTaggedLimit f a b I) (hfg : ∀ t ∈ Set.Icc a b, f t = g t) :
    FineTaggedLimit g a b I := by
  intro ε hε
  obtain ⟨η,hη,hh⟩ := hf ε hε
  refine ⟨η,hη,fun P ξ hP => ?_⟩
  have he : taggedSum P ξ f = taggedSum P ξ g := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hfg (ξ i) (cell_subset_interval P i (ξ i).property)]
  change ‖taggedSum P ξ g - I‖ < ε
  rw [← he]
  exact hh P ξ hP

lemma weighted_limit_bound {h : ℝ → E} {k : ℝ → ℝ}
    {a b C J : ℝ} {I : E} (hab : a ≤ b) (hC : 0 ≤ C)
    (hh : FineTaggedLimit h a b I) (hk : FineTaggedLimit k a b J)
    (hb : ∀ t ∈ Set.Icc a b, ‖h t‖ ≤ C * k t) : ‖I‖ ≤ C * J := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε / (C + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δh,hδh,hch⟩ := hh η hη
  obtain ⟨δk,hδk,hck⟩ := hk η hη
  obtain ⟨P,hP⟩ := exists_fine_partition hab _ (lt_min hδh hδk)
  obtain ⟨ξ⟩ := tags_exist P
  have hv := hch P ξ (hP.trans_le (min_le_left _ _))
  have hw := hck P ξ (hP.trans_le (min_le_right _ _))
  have ht : ‖taggedSum P ξ h‖ ≤ C * taggedSum P ξ k := by
    apply (norm_taggedSum_le h P ξ).trans
    change (∑ i : Fin P.n, cellLength P i * ‖h (ξ i)‖) ≤
      C * ∑ i : Fin P.n, cellLength P i * k (ξ i)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ cellLength P i * (C * k (ξ i)) :=
        mul_le_mul_of_nonneg_left (hb _ (cell_subset_interval P i (ξ i).property))
          (cell_positive P i).le
      _ = _ := by ring
  have hn := norm_sub_norm_le I (taggedSum P ξ h)
  rw [norm_sub_rev] at hn
  have hw' : taggedSum P ξ k ≤ J + η := by
    have := (abs_lt.mp (show |taggedSum P ξ k - J| < η from hw)).2
    linarith
  have hm := mul_le_mul_of_nonneg_left hw' hC
  have he : η * (C + 1) = ε := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith

lemma convolution_bound {f : ℝ → E} (hb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    {δ : ℝ} (hδ : 0 < δ) {k : ℝ → ℝ} (hkpos : ∀ t, 0 ≤ k t)
    (hk : FineTaggedLimit k (-δ) δ 1) (x : ℝ) {I : E}
    (hi : FineTaggedLimit (fun t => k t • f (x-t)) (-δ) δ I) :
    ‖I - f x‖ ≤ A.modulusValue f δ := by
  have hc := limit_smul_const hk (-f x)
  simp only [one_smul] at hc
  have hd := hi.add hc
  have he : FineTaggedLimit (fun t => k t • (f (x-t)-f x)) (-δ) δ (I-f x) := by
    simpa only [sub_eq_add_neg, smul_add, smul_neg] using hd
  have hw := weighted_limit_bound (by linarith) (modulus_nonneg hb hδ.le) he hk
  rw [mul_one] at hw
  apply hw
  intro t ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hkpos t), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (hkpos t)
  apply le_modulus hb
  have : |t| ≤ δ := abs_le.mpr ⟨ht.1,ht.2⟩
  simpa only [sub_sub_cancel_left, abs_neg] using this

end TaggedEstimates

lemma real_integrable_of_continuous {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) : RealIntegrable g a b := by
  apply real_continuous_integrable g hab
  intro x hx
  exact (relativeContinuousAt_within_iff _ _ _).mpr hg.continuousAt.continuousWithinAt

lemma complex_integrable_of_continuous {g : ℝ → ℂ} (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) : ComplexIntegrable g a b := by
  apply complex_continuous_integrable g hab
  intro x hx
  exact (relativeContinuousAt_within_iff _ _ _).mpr hg.continuousAt.continuousWithinAt

lemma real_integral_limit {g : ℝ → ℝ} {a b : ℝ} (hg : RealIntegrable g a b) :
    FineTaggedLimit g a b (realIntegral g hg) :=
  (real_tagged_equivalence _ hg.ordered hg.bounded _).mp ⟨hg,rfl⟩

lemma complex_integral_limit {g : ℝ → ℂ} {a b : ℝ} (hg : ComplexIntegrable g a b) :
    FineTaggedLimit g a b (complexIntegral g hg) :=
  (complex_tagged_equivalence _ (RealIntegrable.ordered hg.1) hg.norm_bound _).mp ⟨hg,rfl⟩

theorem real_approximation : A.realApproximation := by
  intro f hb hu δ hδ _hdec ht k hkc hkpos _hks hk hkn
  have h (j : ℕ) (x : ℝ) : RealIntegrable (fun t => k j t • f (x-t)) (-δ j) (δ j) :=
    real_integrable_of_continuous
      ((hkc j).smul (hu.continuous.comp (continuous_const.sub continuous_id))) (by linarith [hδ j])
  have he (j : ℕ) (x : ℝ) :
      ‖realIntegral _ (h j x)-f x‖ ≤ A.modulusValue f (δ j) := by
    apply convolution_bound hb (hδ j) (hkpos j) _ x (real_integral_limit (h j x))
    simpa only [hkn j] using real_integral_limit (hk j)
  refine ⟨h,he,fun j => csSup_le (Set.range_nonempty _) ?_,
    uniform_of_error hu (fun j => (hδ j).le) ht _ he⟩
  rintro r ⟨x,rfl⟩
  exact he j x

theorem complex_approximation : A.complexApproximation := by
  intro f hb hu δ hδ _hdec ht k hkc hkpos _hks hk hkn
  have h (j : ℕ) (x : ℝ) : ComplexIntegrable (fun t => k j t • f (x-t)) (-δ j) (δ j) :=
    complex_integrable_of_continuous
      ((hkc j).smul (hu.continuous.comp (continuous_const.sub continuous_id))) (by linarith [hδ j])
  have he (j : ℕ) (x : ℝ) :
      ‖complexIntegral _ (h j x)-f x‖ ≤ A.modulusValue f (δ j) := by
    apply convolution_bound hb (hδ j) (hkpos j) _ x (complex_integral_limit (h j x))
    simpa only [hkn j] using real_integral_limit (hk j)
  refine ⟨h,he,fun j => csSup_le (Set.range_nonempty _) ?_,
    uniform_of_error hu (fun j => (hδ j).le) ht _ he⟩
  rintro r ⟨x,rfl⟩
  exact he j x

/-- Direct quadrature estimate for the identity function. This supplies the
 triangular area computation without a measure-integral identification. -/
lemma tagged_identity_error {a b : ℝ} (P : Partition a b) (ξ : Tagging P) :
    |taggedSum P ξ (fun t : ℝ => t) - (b^2-a^2)/2| ≤ mesh P * (b-a) := by
  have htel : (∑ i : Fin P.n, ((P.point i.succ)^2/2 - (P.point i.castSucc)^2/2)) =
      (b^2-a^2)/2 := by
    rw [sum_cell_differences (fun i => (P.point i)^2/2),P.last,P.first]
    ring
  have hi (i : Fin P.n) :
      |cellLength P i * (ξ i : ℝ) - ((P.point i.succ)^2/2 - (P.point i.castSucc)^2/2)| ≤
      cellLength P i * mesh P := by
    have hp := cell_positive P i
    have hmid : |(ξ i : ℝ) - (P.point i.castSucc + P.point i.succ)/2| ≤ cellLength P i := by
      rw [abs_le]
      change -(P.point i.succ - P.point i.castSucc) ≤ _ ∧
        _ ≤ P.point i.succ - P.point i.castSucc
      constructor <;> linarith [(ξ i).property.1,(ξ i).property.2]
    calc
      _ = |cellLength P i * ((ξ i : ℝ) - (P.point i.castSucc + P.point i.succ)/2)| := by
        congr 1
        dsimp [cellLength,S.lengthValue]
        ring
      _ = cellLength P i * |(ξ i : ℝ) - (P.point i.castSucc + P.point i.succ)/2| := by
        rw [abs_mul,abs_of_pos hp]
      _ ≤ cellLength P i * mesh P :=
        mul_le_mul_of_nonneg_left (hmid.trans (cellLength_le_mesh P i)) hp.le
  calc
    _ = |∑ i : Fin P.n, (cellLength P i * (ξ i : ℝ) -
          ((P.point i.succ)^2/2 - (P.point i.castSucc)^2/2))| := by
      rw [Finset.sum_sub_distrib,htel]
      rfl
    _ ≤ ∑ i : Fin P.n, |cellLength P i * (ξ i : ℝ) -
          ((P.point i.succ)^2/2 - (P.point i.castSucc)^2/2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n, cellLength P i * mesh P := Finset.sum_le_sum (fun i _ => hi i)
    _ = mesh P * (b-a) := by rw [← Finset.sum_mul,sum_cellLength,mul_comm]

lemma identity_limit {a b : ℝ} (hab : a ≤ b) :
    FineTaggedLimit (fun t : ℝ => t) a b ((b^2-a^2)/2) := by
  intro ε hε
  have hp : 0 < b-a+1 := by linarith
  refine ⟨ε/(b-a+1),div_pos hε hp,fun P ξ hP => ?_⟩
  have ht := tagged_identity_error P ξ
  change |taggedSum P ξ (fun t : ℝ => t) - (b^2-a^2)/2| < ε
  have hm := (lt_div_iff₀ hp).mp hP
  nlinarith [mesh_nonneg P]

lemma constant_limit (c : ℝ) (a b : ℝ) :
    FineTaggedLimit (fun _ => c) a b ((b-a)*c) := by
  intro ε hε
  refine ⟨1,zero_lt_one,fun P ξ _ => ?_⟩
  change ‖taggedSum P ξ (fun _ => c) - (b-a)*c‖ < ε
  have ht : taggedSum P ξ (fun _ => c) = (b-a)*c := by
    change (∑ i : Fin P.n, cellLength P i * c) = _
    rw [← Finset.sum_mul,sum_cellLength]
  simpa only [ht,sub_self,norm_zero] using hε

lemma affine_limit (α β : ℝ) {a b : ℝ} (hab : a ≤ b) :
    FineTaggedLimit (fun t => α*t+β) a b (α*((b^2-a^2)/2)+(b-a)*β) :=
  ((identity_limit hab).mul α).add (constant_limit β a b)

lemma triangle_continuous (δ : ℝ) : Continuous (A.triangleValue δ) := by
  exact continuous_const.mul ((continuous_const.sub (continuous_abs.div_const δ)).max continuous_const)

lemma triangle_nonnegative {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ A.triangleValue δ t :=
  mul_nonneg (inv_nonneg.mpr hδ.le) (le_max_right _ _)

lemma triangle_support {δ : ℝ} (hδ : 0 < δ) :
    Function.support (A.triangleValue δ) ⊆ Set.Icc (-δ) δ := by
  intro t ht
  by_contra hn
  have hh : δ < |t| := by
    by_contra hn'
    exact hn (abs_le.mp (le_of_not_gt hn'))
  have hz : A.triangleValue δ t = 0 := by
    dsimp [A.triangleValue]
    rw [max_eq_right (by have : 1 < |t| / δ := (one_lt_div hδ).mpr hh; linarith),mul_zero]
  exact ht hz

lemma triangle_left {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Set.Icc (-δ) 0) :
    A.triangleValue δ t = (δ⁻¹/δ)*t+δ⁻¹ := by
  have hh : |t| ≤ δ := abs_le.mpr ⟨ht.1, ht.2.trans hδ.le⟩
  have hm : 0 ≤ 1-|t|/δ := by
    have := (div_le_one hδ).mpr hh
    linarith
  dsimp [A.triangleValue]
  rw [max_eq_left hm,abs_of_nonpos ht.2]
  ring

lemma triangle_right {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Set.Icc 0 δ) :
    A.triangleValue δ t = -(δ⁻¹/δ)*t+δ⁻¹ := by
  have hh : |t| ≤ δ := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hm : 0 ≤ 1-|t|/δ := by
    have := (div_le_one hδ).mpr hh
    linarith
  dsimp [A.triangleValue]
  rw [max_eq_left hm,abs_of_nonneg ht.1]
  ring

theorem triangular_kernel : A.triangularKernel := by
  intro δ hδ
  have hs := triangle_support hδ
  have htop : tsupport (A.triangleValue δ) ⊆ Set.Icc (-δ) δ :=
    closure_minimal hs isClosed_Icc
  have h := real_integrable_of_continuous (triangle_continuous δ) (by linarith : -δ ≤ δ)
  have hl := real_integrable_of_continuous (triangle_continuous δ) (by linarith : -δ ≤ 0)
  have hr := real_integrable_of_continuous (triangle_continuous δ) hδ.le
  have hvl : realIntegral _ hl = 1/2 := by
    have ht := limit_congr (affine_limit (δ⁻¹/δ) (δ⁻¹) (by linarith : -δ ≤ 0))
      (fun t ht => (triangle_left hδ ht).symm)
    have he := fineTaggedLimit_unique (by linarith : -δ ≤ 0) (real_integral_limit hl) ht
    rw [he]
    field_simp
    ring
  have hvr : realIntegral _ hr = 1/2 := by
    have ht := limit_congr (affine_limit (-(δ⁻¹/δ)) (δ⁻¹) hδ.le)
      (fun t ht => (triangle_right hδ ht).symm)
    have he := fineTaggedLimit_unique hδ.le (real_integral_limit hr) ht
    rw [he]
    field_simp
    ring
  refine ⟨triangle_continuous δ,triangle_nonnegative hδ,hs,htop,h,?_⟩
  rw [(real_split _ (by linarith : -δ ≤ 0) hδ.le h.bounded).2 h hl hr]
  change realIntegral _ hl + realIntegral _ hr = 1
  rw [hvl,hvr]
  norm_num

end SingleVariableAnalysis.ApproximateIdentity
