import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ProperDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C08.ProperContinuity
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04.ProperDerivative
open Darboux JordanRegions ProperContinuity
variable {n m k : ℕ} {S : Set (E n)} {P : Set (E m)}

abbrev OperatorRegionIntegrable := @Specs.D04.C08.ProperDerivative.Model.OperatorRegionIntegrable
abbrev operatorRegionIntegral := @Specs.D04.C08.ProperDerivative.Model.operatorRegionIntegral

lemma vector_smul (c : ℝ) {f : S → E k} (hf : VectorRegionIntegrable f) :
    VectorRegionIntegrable (fun x => c • f x) ∧
    vectorRegionIntegral (fun x => c • f x) = c • vectorRegionIntegral f := by
  exact vector_integral_linear f (c • LinearMap.id) hf

lemma vector_add {f g : S → E k} (hf : VectorRegionIntegrable f)
    (hg : VectorRegionIntegrable g) :
    VectorRegionIntegrable (fun x => f x + g x) ∧
    vectorRegionIntegral (fun x => f x + g x) = vectorRegionIntegral f + vectorRegionIntegral g := by
  have hn := vector_smul (-1) hg
  simp only [neg_one_smul] at hn
  have hs := vector_sub_integrable hf hn.1
  have he := vector_integral_sub hf hn.1
  rw [hn.2] at he
  exact ⟨by simpa only [sub_neg_eq_add] using hs,
    by simpa only [sub_neg_eq_add] using he⟩

lemma vector_sum {ι : Type*} (s : Finset ι) (f : ι → S → E k)
    (hb : Bornology.IsBounded S) (hf : ∀ i ∈ s, VectorRegionIntegrable (f i)) :
    VectorRegionIntegrable (fun x => ∑ i ∈ s, f i x) ∧
    vectorRegionIntegral (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, vectorRegionIntegral (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz := vector_zero_target hb (fun _ => 0)
    have hv : VectorRegionIntegrable (fun _ : S => (0 : E k)) :=
      (vector_integral_linear (fun _ : S => (0 : E 0)) (0 : E 0 →ₗ[ℝ] E k) hz.1).1
    refine ⟨by simpa using hv, ?_⟩
    simpa using (vector_integral_linear (fun _ : S => (0 : E 0))
      (0 : E 0 →ₗ[ℝ] E k) hz.1).2
  | @insert i s hi ih =>
    have hh := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have ha := vector_add (hf i (Finset.mem_insert_self _ _)) hh.1
    simpa only [Finset.sum_insert hi] using
      ⟨ha.1, ha.2.trans (congrArg (vectorRegionIntegral (f i) + ·) hh.2)⟩

lemma integral_apply (A : S → E m →L[ℝ] E k) (hA : OperatorRegionIntegrable A)
    (h : E m) : VectorRegionIntegrable (fun x => A x h) ∧
    operatorRegionIntegral A h = vectorRegionIntegral (fun x => A x h) := by
  have he (x : S) : A x h = ∑ j : Fin m, h j • A x (standardBasis m j) := by
    have hh : h = ∑ j : Fin m, h j • standardBasis m j := by
      simpa [standardBasis, EuclideanSpace.basisFun_repr] using
        ((standardBasis m).sum_repr h).symm
    conv_lhs => rw [hh]
    simp only [map_sum, map_smul]
  have hs := vector_sum Finset.univ (fun j x => h j • A x (standardBasis m j))
    hA.1 (fun j _ => (vector_smul (h j) (hA.2 j)).1)
  have hfun : (fun x => A x h) = (fun x => ∑ j : Fin m, h j • A x (standardBasis m j)) := funext he
  refine ⟨hfun ▸ hs.1, ?_⟩
  rw [hfun, hs.2]
  ext i
  have hm := matrix_apply (m := k) (n := m)
    (fun i j => regionIntegral (fun x => A x (standardBasis m j) i)) h i
  change (matrixLinearEquiv k m _) h i = _
  apply hm.trans
  rw [show (∑ j : Fin m, vectorRegionIntegral (fun x => h j • A x (standardBasis m j))) i =
    ∑ j : Fin m, (vectorRegionIntegral (fun x => h j • A x (standardBasis m j))) i from
      map_sum ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin k => ℝ) i).toLinearMap) _ _]
  apply Finset.sum_congr rfl
  intro j _
  rw [(vector_smul (h j) (f := fun x => A x (standardBasis m j)) (hA.2 j)).2]
  change _ = h j * regionIntegral (fun x => A x (standardBasis m j) i)
  exact mul_comm _ _

lemma linear_expansion (A : E m →L[ℝ] E k) (h : E m) :
    A h = ∑ j : Fin m, h j • A (standardBasis m j) := by
  have hh : h = ∑ j : Fin m, h j • standardBasis m j := by
    simpa [standardBasis, EuclideanSpace.basisFun_repr] using
      ((standardBasis m).sum_repr h).symm
  conv_lhs => rw [hh]
  simp only [map_sum, map_smul]

lemma operator_bounded (A : S → E m →L[ℝ] E k) (hA : OperatorRegionIntegrable A) :
    RegionBounded A := by
  classical
  choose M hM using fun j => vector_region_bounded (hA.2 j)
  refine ⟨∑ j : Fin m, max (M j) 0, fun x => ?_⟩
  apply (A x).opNorm_le_bound (Finset.sum_nonneg fun j _ => le_max_right _ _)
  intro h
  rw [linear_expansion, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul, Real.norm_eq_abs]
  rw [mul_comm (max (M j) 0) ‖h‖]
  exact mul_le_mul (PiLp.norm_apply_le h j)
    ((hM j x).trans (le_max_left _ _)) (norm_nonneg _) (norm_nonneg _)

lemma operator_difference_bdd {A B : S → E m →L[ℝ] E k}
    (hA : OperatorRegionIntegrable A) (hB : OperatorRegionIntegrable B) :
    BddAbove (range (fun x => ‖A x - B x‖)) := by
  obtain ⟨M,hM⟩ := operator_bounded A hA
  obtain ⟨N,hN⟩ := operator_bounded B hB
  exact ⟨M+N, by rintro _ ⟨x,rfl⟩; exact (norm_sub_le _ _).trans (add_le_add (hM x) (hN x))⟩


/-- The uniform local hypothesis needed for a total, rather than directional,
derivative. It controls every parameter increment in a ball. -/
lemma integral_hasFDerivAt (hS : Jordan S) (f : S → E m → E k)
    (A : S → E m → E m →L[ℝ] E k)
    (hf : ∀ p ∈ P, VectorRegionIntegrable (fun x => f x p))
    (hA : ∀ p ∈ P, OperatorRegionIntegrable (fun x => A x p))
    (hd : ∀ x p, p ∈ P → HasFDerivAt (f x) (A x p) p)
    (p₀ : E m) (hp₀ : p₀ ∈ P)
    (hu : ∀ ε > 0, ∃ r > 0, Metric.ball p₀ r ⊆ P ∧
      ∀ p ∈ Metric.ball p₀ r, ∀ x, ‖A x p - A x p₀‖ ≤ ε) :
    HasFDerivAt (fun p => vectorRegionIntegral (fun x => f x p))
      (operatorRegionIntegral (fun x => A x p₀)) p₀ := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let δ := ε / (volume S + 1)
  have hv := volume_nonneg hS
  have hv1 : 0 < volume S + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hv1
  have hδε : volume S * δ ≤ ε := by
    have hh : δ * (volume S + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hv1)
    nlinarith
  obtain ⟨r, hr, hrP, hrA⟩ := hu δ hδ
  filter_upwards [Metric.ball_mem_nhds p₀ hr] with p hp
  have hpP := hrP hp
  have hrem (x : S) : ‖f x p - f x p₀ - A x p₀ (p - p₀)‖ ≤ δ * ‖p - p₀‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun q => f x q - A x p₀ q) (f' := fun q => A x q - A x p₀)
      (fun q hq => ((hd x q (hrP hq)).sub (A x p₀).hasFDerivAt).hasFDerivWithinAt)
      (fun q hq => hrA q hq x) (convex_ball p₀ r)
      (Metric.mem_ball_self hr) hp
    convert hh using 1
    congr 1
    rw [map_sub]
    abel
  have hi := (integral_apply (fun x => A x p₀) (hA p₀ hp₀) (p - p₀))
  have hsub := vector_sub_integrable (hf p hpP) (hf p₀ hp₀)
  have hri := vector_sub_integrable hsub hi.1
  have hb := vector_uniform_bound hS _ hri (δ * ‖p - p₀‖)
    (mul_nonneg hδ.le (norm_nonneg _)) hrem
  rw [vector_integral_sub hsub hi.1,
    vector_integral_sub (hf p hpP) (hf p₀ hp₀), ← hi.2] at hb
  exact hb.trans (by nlinarith [norm_nonneg (p - p₀)])

lemma proper_derivative (hS : Jordan S) (hP : IsOpen P)
    (f : S → E m → E k) (A : S → E m → E m →L[ℝ] E k)
    (hf : ∀ p ∈ P, VectorRegionIntegrable (fun x => f x p))
    (hd : ∀ x p, p ∈ P → HasFDerivAt (f x) (A x p) p)
    (hA : ∀ p ∈ P, OperatorRegionIntegrable (fun x => A x p))
    (p₀ : E m) (hp₀ : p₀ ∈ P)
    (hu : Tendsto (fun p : P => sSup (range (fun x => ‖A x p - A x p₀‖)))
      (𝓝 (⟨p₀,hp₀⟩ : P)) (𝓝 0)) :
    HasFDerivAt (fun p => vectorRegionIntegral (fun x => f x p))
      (operatorRegionIntegral (fun x => A x p₀)) p₀ ∧
    ∀ h, fderiv ℝ (fun p => vectorRegionIntegral (fun x => f x p)) p₀ h =
      vectorRegionIntegral (fun x => A x p₀ h) := by
  have hl : ∀ ε > 0, ∃ r > 0, Metric.ball p₀ r ⊆ P ∧
      ∀ p ∈ Metric.ball p₀ r, ∀ x, ‖A x p - A x p₀‖ ≤ ε := by
    intro ε hε
    have he : ∀ᶠ p : P in 𝓝 (⟨p₀,hp₀⟩ : P), ∀ x, ‖A x p - A x p₀‖ ≤ ε := by
      filter_upwards [(Metric.tendsto_nhds.mp hu) ε hε] with p hp x
      have hx := le_csSup (operator_difference_bdd (hA p p.property) (hA p₀ hp₀))
        (mem_range_self (f := fun x => ‖A x p - A x p₀‖) x)
      exact hx.trans ((le_abs_self _).trans (by simpa [Real.dist_eq] using hp.le))
    obtain ⟨r,hr,hh⟩ := Metric.eventually_nhds_iff.mp he
    obtain ⟨s,hs,hsP⟩ := Metric.isOpen_iff.mp hP p₀ hp₀
    refine ⟨min r s, lt_min hr hs, ?_, ?_⟩
    · intro p hp
      exact hsP (Metric.mem_ball.mp hp |>.trans_le (min_le_right _ _))
    · intro p hp x
      have hpP : p ∈ P := hsP (Metric.mem_ball.mp hp |>.trans_le (min_le_right _ _))
      exact hh (y := ⟨p,hpP⟩) (Metric.mem_ball.mp hp |>.trans_le (min_le_left _ _)) x
  have hdF := integral_hasFDerivAt hS f A hf hA hd p₀ hp₀ hl
  exact ⟨hdF, fun h => by rw [hdF.fderiv]; exact (integral_apply _ (hA p₀ hp₀) h).2⟩


lemma continuous_parameter_derivative (hS : Jordan S) (hP : IsOpen P)
    (f : closure S → E m → E k) (A : closure S → E m → E m →L[ℝ] E k)
    (hf : Continuous (fun z : closure S × P => f z.1 z.2))
    (hAc : Continuous (fun z : closure S × P => A z.1 z.2))
    (hd : ∀ x : S, ∀ p ∈ P, HasFDerivAt (f ⟨x, subset_closure x.property⟩)
      (A ⟨x, subset_closure x.property⟩ p) p) :
    let F := fun p => vectorRegionIntegral (fun x : S => f ⟨x, subset_closure x.property⟩ p)
    let G := fun p => operatorRegionIntegral (fun x : S => A ⟨x, subset_closure x.property⟩ p)
    (∀ p ∈ P, VectorRegionIntegrable (fun x : S => f ⟨x, subset_closure x.property⟩ p)) ∧
    CrOn 1 P F ∧ ContinuousOn G P ∧
    ∀ p ∈ P, HasFDerivAt F (G p) p ∧ ∀ h,
      fderiv ℝ F p h = vectorRegionIntegral (fun x : S => A ⟨x, subset_closure x.property⟩ p h) := by
  let F := fun p => vectorRegionIntegral (fun x : S => f ⟨x, subset_closure x.property⟩ p)
  let G := fun p => operatorRegionIntegral (fun x : S => A ⟨x, subset_closure x.property⟩ p)
  have hfi (p : E m) (hp : p ∈ P) :
      VectorRegionIntegrable (fun x : S => f ⟨x, subset_closure x.property⟩ p) :=
    (joint_continuity hS (fun z : closure S × P => f z.1 z.2) hf).1 ⟨p,hp⟩
  have hev (h : E m) := joint_continuity hS
    (fun z : closure S × P => A z.1 z.2 h) (continuous_clm_apply.mp hAc h)
  have hAi (p : E m) (hp : p ∈ P) :
      OperatorRegionIntegrable (fun x : S => A ⟨x, subset_closure x.property⟩ p) :=
    ⟨jordan_bounded hS, fun j => (hev (standardBasis m j)).1 ⟨p,hp⟩⟩
  have hGc : Continuous (fun p : P => G p) := by
    apply continuous_clm_apply.mpr
    intro h
    apply (hev h).2.congr
    intro p
    exact (integral_apply _ (hAi p p.property) h).2.symm
  have hG : ContinuousOn G P := continuousOn_iff_continuous_domRestrict.mpr hGc
  have hDF (p₀ : E m) (hp₀ : p₀ ∈ P) : HasFDerivAt F (G p₀) p₀ := by
    apply integral_hasFDerivAt hS
      (fun x : S => f ⟨x, subset_closure x.property⟩)
      (fun x : S => A ⟨x, subset_closure x.property⟩) hfi hAi hd p₀ hp₀
    let : CompactSpace (closure S) := isCompact_iff_compactSpace.mp
      (jordan_bounded hS).isCompact_closure
    let : LocallyCompactSpace P := hP.locallyCompactSpace
    have hu := Continuous.tendstoUniformly
      (fun p : P => fun x : closure S => A x p)
      (hAc.comp (continuous_snd.prodMk continuous_fst)) (⟨p₀,hp₀⟩ : P)
    intro ε hε
    have he : ∀ᶠ p : P in 𝓝 (⟨p₀,hp₀⟩ : P),
        ∀ x : closure S, ‖A x p - A x p₀‖ ≤ ε := by
      filter_upwards [(Metric.tendstoUniformly_iff.mp hu) ε hε] with p hp x
      simpa only [dist_eq_norm, norm_sub_rev] using (hp x).le
    obtain ⟨r,hr,hh⟩ := Metric.eventually_nhds_iff.mp he
    obtain ⟨s,hs,hsP⟩ := Metric.isOpen_iff.mp hP p₀ hp₀
    refine ⟨min r s, lt_min hr hs, ?_, ?_⟩
    · intro p hp
      exact hsP (Metric.mem_ball.mp hp |>.trans_le (min_le_right _ _))
    · intro p hp x
      have hpP : p ∈ P := hsP (Metric.mem_ball.mp hp |>.trans_le (min_le_right _ _))
      exact hh (y := ⟨p,hpP⟩) (Metric.mem_ball.mp hp |>.trans_le (min_le_left _ _))
        ⟨x, subset_closure x.property⟩
  have hCr : CrOn 1 P F := by
    change TotalDifferentiableOn P F ∧ ContinuousOn (totalDerivative F) P
    refine ⟨fun p hp => ⟨G p, ?_⟩, ?_⟩
    · exact (hasTotalDerivative_iff_hasFDerivAt P F (G p) p hP hp).mpr (hDF p hp)
    · exact hG.congr (fun p hp => (hDF p hp).fderiv)
  refine ⟨hfi, hCr, hG, fun p hp => ⟨hDF p hp, fun h => ?_⟩⟩
  rw [(hDF p hp).fderiv]
  exact (integral_apply _ (hAi p hp) h).2

end D04.ProperDerivative
