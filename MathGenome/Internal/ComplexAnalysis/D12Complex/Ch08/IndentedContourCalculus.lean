import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.IndentedContourCalculus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.OrderedIndentedDiameter
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexComputations
import Batteries.Tactic.OpenPrivate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace D12Complex.IndentedContourCalculus
open Specs.D12Complex.Ch08.IndentedContourCalculus
open Specs.D12Complex.Ch08.OrderedIndentedDiameter (Admissible Gaps Traversal Retained)
open private smoothPath from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexComputations

/-- The doubled-disk margins imply the ordinary ordered-diameter conditions. -/
theorem geometry_admissible (s : Finset ℝ) (r : ℝ) (ε : s → ℝ)
    (h : Geometry s r ε) : Admissible s (-r) r ε := by
  refine ⟨by linarith [h.1], ?_, ?_⟩
  · intro a
    have ha := h.2.1 a
    refine ⟨ha.1, ?_, ?_⟩
    · linarith [neg_abs_le a.val]
    · linarith [le_abs_self a.val]
  · intro a b hab
    have hne : a ≠ b := by intro he; subst b; exact lt_irrefl _ hab
    have hh := h.2.2 a b hne
    rw [abs_of_neg (sub_neg.mpr hab)] at hh
    linarith [(h.2.1 a).1, (h.2.1 b).1]

/-- A genuine smooth angular path, parameterized by its angle. -/
def arcPath (c : ℂ) (r : ℝ) : PiecewiseC1Path :=
  smoothPath 0 Real.pi Real.pi_pos.le (circleMap c r) (contDiff_circleMap c r)

@[simp] theorem arcPath_apply (c : ℂ) (r t : ℝ) : arcPath c r t = circleMap c r t := rfl
@[simp] theorem arcPath_a (c : ℂ) (r : ℝ) : (arcPath c r).path.a = 0 := rfl
@[simp] theorem arcPath_b (c : ℂ) (r : ℝ) : (arcPath c r).path.b = Real.pi := rfl
@[simp] theorem arcPath_trace (c : ℂ) (r : ℝ) :
    (arcPath c r).trace = circleMap c r '' Icc 0 Real.pi := rfl

/-- Trace of an actual concatenation; the two intervals both have positive duration. -/
theorem closing_trace (γ δ : PiecewiseC1Path) (r : ℝ)
    (hγ : γ.path.a < γ.path.b) (hd : ClosingTraversal γ δ)
    (ho : EqOn δ (fun t => circleMap 0 r (Real.pi*(t-1))) (Icc 1 2)) :
    δ.trace = γ.trace ∪ circleMap 0 r '' Icc 0 Real.pi := by
  rcases hd with ⟨ha,hb,hfirst⟩
  ext z
  constructor
  · rintro ⟨t,ht,rfl⟩
    rw [ha,hb] at ht
    by_cases ht1 : t ≤ 1
    · left
      refine ⟨γ.path.a + (γ.path.b-γ.path.a)*t, ?_, (hfirst ⟨ht.1,ht1⟩).symm⟩
      constructor <;> nlinarith [ht.1,ht1]
    · right
      refine ⟨Real.pi*(t-1), ?_, (ho ⟨by linarith,ht.2⟩).symm⟩
      constructor <;> nlinarith [Real.pi_pos, ht.2]
  · rintro (⟨u,hu,rfl⟩ | ⟨θ,hθ,rfl⟩)
    · let t := (u-γ.path.a)/(γ.path.b-γ.path.a)
      have ht0 : 0 ≤ t := div_nonneg (by linarith [hu.1]) (by linarith)
      have ht1 : t ≤ 1 := (div_le_one (sub_pos.mpr hγ)).mpr (by linarith [hu.2])
      refine ⟨t, by rw [ha,hb]; exact ⟨ht0,by linarith⟩, ?_⟩
      rw [hfirst ⟨ht0,ht1⟩]
      apply congrArg (γ : ℝ → ℂ)
      dsimp [t]
      field_simp
      ring
    · let t := 1+θ/Real.pi
      have ht : t ∈ Icc (1:ℝ) 2 := by
        have h0 := div_nonneg hθ.1 Real.pi_pos.le
        have h1 := (div_le_one Real.pi_pos).mpr hθ.2
        dsimp [t]; constructor <;> linarith
      refine ⟨t, by rw [ha,hb]; exact ⟨by linarith [ht.1],ht.2⟩, ?_⟩
      rw [ho ht]
      apply congrArg (circleMap 0 r)
      dsimp [t]
      field_simp
      ring

/-- Close the diameter without choosing or inspecting any integrand. -/
theorem contour_exists : contour_exists_type := by
  intro s r ε h
  obtain ⟨n,e,start,stop,γ,hg,ht,hs,hu,htrace⟩ :=
    OrderedIndentedDiameter.ordered_indented_diameter_exists s (-r) r ε
      (geometry_admissible s r ε h)
  have hc : γ.path.target = (arcPath 0 r).path.source := by
    rw [hu]
    simp [arcPath, ComplexPath.source, smoothPath, PiecewiseC1Path.path, circleMap]
  obtain ⟨δ,ha,hb,hfirst,hsecond⟩ := PiecewiseC1Path.exists_concatenation γ (arcPath 0 r) hc
  have hd : ClosingTraversal γ δ := ⟨ha,hb,hfirst⟩
  have ho : EqOn δ (fun t => circleMap 0 r (Real.pi*(t-1))) (Icc 1 2) := by
    simpa only [arcPath_a,arcPath_b,sub_zero,zero_add,arcPath_apply] using hsecond
  have hclosed : δ.IsClosed := by
    change δ δ.path.b = δ δ.path.a
    rw [ha,hb,ho (by norm_num),hfirst (by norm_num)]
    change circleMap 0 r (Real.pi*(2-1)) = γ (γ.path.a+(γ.path.b-γ.path.a)*0)
    norm_num only [sub_self, sub_zero, mul_zero, zero_mul, add_zero, sub_self, sub_self,
      show (2:ℝ)-1 = 1 by norm_num, mul_one, circleMap, Complex.ofReal_mul,
      Complex.ofReal_one, mul_one, Complex.exp_pi_mul_I, mul_neg_one, zero_add]
    simpa only [ComplexPath.source, Complex.ofReal_neg] using hs.symm
  refine ⟨n,e,start,stop,γ,δ,hg,ht,(by simpa using hs),hu,hd,ho,hclosed,?_⟩
  rw [closing_trace γ δ r (by
    rw [ht.1,ht.2.1]; positivity) hd ho, htrace]
  unfold Specs.D12Complex.Ch08.OrderedIndentedDiameter.TraceSet TraceSet
  ext z
  simp only [mem_union]
  tauto

/-- Angular integrability uses continuity only on the indicated arc. -/
theorem arc_integrable (c : ℂ) (r : ℝ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (circleMap c r '' Icc 0 Real.pi)) :
    IntervalIntegrable (ArcIntegrand c r f) volume 0 Real.pi := by
  apply ContinuousOn.intervalIntegrable_of_Icc Real.pi_pos.le
  apply ContinuousOn.mul
  · exact hf.comp (by fun_prop) (fun t ht => ⟨t,ht,rfl⟩)
  · unfold circleMap
    fun_prop

/-- Every displayed integral exists for arbitrary continuous boundary data. -/
theorem boundary_integrable (s : Finset ℝ) (r : ℝ) (ε : s → ℝ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (TraceSet s r ε)) : IntegrableBoundary s r ε f := by
  have hr : IsCompact (Retained s (-r) r ε) :=
    isCompact_Icc.inter_right (isOpen_iUnion (fun a : s =>
      isOpen_Ioo (a := a.val - ε a) (b := a.val + ε a))).isClosed_compl
  refine ⟨?_, arc_integrable 0 r f (hf.mono (by intro z hz; exact Or.inl (Or.inr hz))), ?_⟩
  · apply ContinuousOn.integrableOn_compact hr
    exact hf.comp Complex.continuous_ofReal.continuousOn
      (fun x hx => Or.inl (Or.inl ⟨x,hx,rfl⟩))
  · intro x
    apply arc_integrable
    exact hf.mono (by intro z hz; exact Or.inr (mem_iUnion.mpr ⟨x,hz⟩))

/-- The whole geometric trace lies in the closed upper half-plane. -/
theorem trace_im_nonneg (s : Finset ℝ) (r : ℝ) (ε : s → ℝ)
    (h : Geometry s r ε) : ∀ z ∈ TraceSet s r ε, 0 ≤ z.im := by
  rintro z ((⟨x,hx,rfl⟩ | ⟨t,ht,rfl⟩) | hz)
  · simp
  · simpa only [circleMap_zero_im] using
      mul_nonneg h.1.le (Real.sin_nonneg_of_mem_Icc ht)
  · obtain ⟨x,t,ht,rfl⟩ := mem_iUnion.mp hz
    simpa [circleMap, Complex.exp_im, Complex.mul_im] using
      mul_nonneg (h.2.1 x).1.le (Real.sin_nonneg_of_mem_Icc ht)

/-- The upper index hypotheses imply actual trace avoidance. -/
theorem upper_avoids (s : Finset ℝ) (r : ℝ) (ε : s → ℝ)
    (h : Geometry s r ε) (a : ℂ) (har : ‖a‖ < r) (hai : 0 < a.im)
    (haε : ∀ x : s, ε x < ‖a - (x.val : ℂ)‖) : a ∉ TraceSet s r ε := by
  rintro ((⟨x,hx,hxa⟩ | ⟨t,ht,hta⟩) | ha)
  · have := congrArg Complex.im hxa
    simp only [Complex.ofReal_im] at this
    linarith
  · have hn := norm_circleMap_zero r t
    rw [hta,abs_of_pos h.1] at hn
    linarith
  · obtain ⟨x,t,ht,hta⟩ := mem_iUnion.mp ha
    have hn : ‖a - (x.val : ℂ)‖ = ε x := by
      rw [← hta,circleMap_sub_center,norm_circleMap_zero,abs_of_pos (h.2.1 x).1]
    linarith [haε x]

/-- A downward ray proves zero index, including real starting points off the trace. -/
theorem closed_path_index_zero_below (δ : PiecewiseC1Path) (hc : δ.IsClosed)
    (hδ : ∀ z ∈ δ.trace, 0 ≤ z.im) (a : ℂ) (ha : a.im ≤ 0)
    (hne : a ∉ δ.trace) : δ.index a = 0 := by
  apply IndexComputations.closed_path_index_zero_of_avoids_ray δ a (-Complex.I) hc (by simp)
  intro t ht
  rintro ⟨u,hu,heq⟩
  have hmem : δ t ∈ δ.trace := ⟨t,ht,rfl⟩
  have hi := hδ (δ t) hmem
  have him := congrArg Complex.im heq
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.neg_im,
    Complex.I_im, Complex.ofReal_im, zero_mul, add_zero] at him
  have hu0 : u = 0 := by linarith
  rw [hu0, Complex.ofReal_zero,zero_mul] at heq
  exact hne ((sub_eq_zero.mp heq) ▸ hmem)

/-- Finite additivity over equal-duration parameter intervals. -/
theorem integral_units (m : ℕ) (g : ℝ → ℂ)
    (hi : IntervalIntegrable g volume 0 (m : ℝ)) :
    (∫ t in (0:ℝ)..(m:ℝ), g t) =
      ∑ k : Fin m, ∫ t in (k.val:ℝ)..((k.val:ℝ)+1), g t := by
  have hh := intervalIntegral_fin_partition (fun k : Fin (m+1) => (k.val:ℝ)) g (fun k => by
    apply hi.mono_set
    rw [uIcc_of_le (by exact_mod_cast (Nat.le_succ k.val)), uIcc_of_le (Nat.cast_nonneg m)]
    exact Icc_subset_Icc (Nat.cast_nonneg _) (by exact_mod_cast k.isLt))
  simpa only [Fin.val_zero, Nat.cast_zero, Fin.val_last, Fin.val_castSucc,
    Fin.val_succ, Nat.cast_add, Nat.cast_one] using hh.2.symm

theorem sum_range_alternating (n : ℕ) (g : ℕ → ℂ) :
    (∑ k ∈ Finset.range (2*n+1), g k) =
      (∑ j ∈ Finset.range (n+1), g (2*j)) +
      ∑ i ∈ Finset.range n, g (2*i+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega]
    simp only [Finset.sum_range_succ, Nat.mul_add, Nat.mul_one] at ih ⊢
    linear_combination ih

/-- Values on a closed interval determine the integral and a.e. derivative there. -/
theorem integral_on_piece (γ : ℝ → ℂ) (g : ℝ → ℂ) (u v : ℝ) (huv : u ≤ v)
    (he : EqOn γ g (Icc u v)) (f : ℂ → ℂ) :
    (∫ t in u..v, f (γ t) * deriv γ t) =
      ∫ t in u..v, f (g t) * deriv g t := by
  apply intervalIntegral.integral_congr_Ioo_of_le huv
  intro t ht
  change f (γ t) * deriv γ t = f (g t) * deriv g t
  rw [he ⟨ht.1.le,ht.2.le⟩,(he.mono Ioo_subset_Icc_self).deriv isOpen_Ioo ht]

/-- Distinct retained intervals are strictly separated, rather than merely a.e. disjoint. -/
theorem gaps_separated {s : Finset ℝ} {l u : ℝ} {ε : s → ℝ} {n : ℕ}
    {e : Fin n ≃ s} {start stop : Fin (n+1) → ℝ}
    (ha : Admissible s l u ε) (hg : Gaps l u ε e start stop)
    (j k : Fin (n+1)) (hjk : j < k) : stop j < start k := by
  revert hjk
  refine Fin.cases ?_ (fun i hjk => ?_) k
  · intro h; exact (not_lt_of_ge (Fin.zero_le j) h).elim
  · let q : Fin n := ⟨j.val,by have := i.isLt; change j.val < i.val+1 at hjk; omega⟩
    have hq : q.castSucc = j := Fin.ext rfl
    rw [← hq,hg.2.2.2.1 q,hg.2.2.2.2.1 i]
    have hqi : q ≤ i := by change j.val ≤ i.val; change j.val < i.val+1 at hjk; omega
    have hcent := hg.1.monotone hqi
    linarith [(ha.2.1 (e q)).1,(ha.2.1 (e i)).1]

/-- The literal retained-set integral is the sum of its ordered interval integrals. -/
theorem retained_integral_eq_sum (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ)
    (n : ℕ) (e : Fin n ≃ s) (start stop : Fin (n+1) → ℝ)
    (ha : Admissible s l u ε) (hg : Gaps l u ε e start stop)
    (g : ℝ → ℂ) (hf : ContinuousOn g (Retained s l u ε)) :
    (∫ x in Retained s l u ε, g x) = ∑ j, ∫ x in start j..stop j, g x := by
  have hret := OrderedIndentedDiameter.retained_eq_union_gaps s l u ε n e start stop ha hg
  have hcont (j) : ContinuousOn g (Icc (start j) (stop j)) :=
    hf.mono (by rw [hret]; exact subset_iUnion (fun j : Fin (n+1) => Icc (start j) (stop j)) j)
  have hdis : Pairwise (Disjoint on (fun j => Icc (start j) (stop j))) := by
    intro j k hjk
    apply disjoint_left.mpr
    intro x hxj hxk
    rcases lt_or_gt_of_ne hjk with h | h
    · linarith [gaps_separated ha hg j k h,hxj.2,hxk.1]
    · linarith [gaps_separated ha hg k j h,hxk.2,hxj.1]
  rw [hret, integral_iUnion_fintype (fun _ => measurableSet_Icc) hdis
    (fun j => (hcont j).integrableOn_Icc)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_of_le (hg.2.2.2.2.2 j).le,integral_Icc_eq_integral_Ioc]

/-- Affine real segments, with their actual parameter derivatives. -/
theorem line_affine_integral (p q u v : ℝ) (f : ℂ → ℂ) :
    (∫ t in u..v, f ((p+q*t : ℝ) : ℂ) *
      deriv (fun t : ℝ => ((p+q*t : ℝ) : ℂ)) t) =
      ∫ x in p+q*u..p+q*v, f (x : ℂ) := by
  have hd (t : ℝ) : deriv (fun t : ℝ => ((p+q*t : ℝ) : ℂ)) t = (q : ℂ) := by
    simpa using ((((hasDerivAt_id t).const_mul q).const_add p).ofReal_comp).deriv
  simp_rw [hd]
  have he (t : ℝ) : f ((p+q*t:ℝ):ℂ) * (q:ℂ) = q • f ((p+q*t:ℝ):ℂ) := by
    simp [Complex.real_smul,mul_comm]
  simp_rw [he]
  rw [intervalIntegral.integral_smul]
  exact intervalIntegral.smul_integral_comp_add_mul (fun x : ℝ => f (x : ℂ)) q p

/-- Angular affine substitution, valid for both directions. -/
theorem arc_affine_integral (c : ℂ) (r p q u v : ℝ) (f : ℂ → ℂ) :
    (∫ t in u..v, f (circleMap c r (p+q*t)) *
      deriv (fun t => circleMap c r (p+q*t)) t) =
      ∫ θ in p+q*u..p+q*v, ArcIntegrand c r f θ := by
  have hd (t : ℝ) : deriv (fun t => circleMap c r (p+q*t)) t =
      q • (circleMap 0 r (p+q*t) * Complex.I) := by
    simpa only [id_eq, mul_one, Function.comp_def] using
      ((hasDerivAt_circleMap c r (p+q*t)).scomp t
      (((hasDerivAt_id t).const_mul q).const_add p)).deriv
  simp_rw [hd,mul_smul_comm]
  rw [intervalIntegral.integral_smul]
  exact intervalIntegral.smul_integral_comp_add_mul (ArcIntegrand c r f) q p

/-- Integral of any representative of the accepted ordered diameter traversal. -/
theorem diameter_integral (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ)
    (n : ℕ) (e : Fin n ≃ s) (start stop : Fin (n+1) → ℝ)
    (γ : PiecewiseC1Path) (ha : Admissible s l u ε)
    (hg : Gaps l u ε e start stop) (ht : Traversal ε e start stop γ)
    (f : ℂ → ℂ) (hf : ContinuousOn f γ.trace) :
    γ.integral f = (∫ x in Retained s l u ε, f (x : ℂ)) -
      ∑ a : s, ∫ θ in (0:ℝ)..Real.pi, ArcIntegrand (a.val : ℂ) (ε a) f θ := by
  have hret := OrderedIndentedDiameter.trace_of_traversal s l u ε n e start stop γ ha hg ht
  have hreal : ContinuousOn (fun x : ℝ => f (x : ℂ)) (Retained s l u ε) := by
    apply hf.comp Complex.continuous_ofReal.continuousOn
    intro x hx
    rw [hret]
    exact Or.inl ⟨x,hx,rfl⟩
  have heven (j : Fin (n+1)) :
      (∫ t in 2*(j.val:ℝ)..2*(j.val:ℝ)+1, f (γ t) * deriv γ t) =
      ∫ x in start j..stop j, f (x : ℂ) := by
    let p := start j - (stop j-start j)*(2*(j.val:ℝ))
    let q := stop j-start j
    have he : EqOn γ (fun t => ((p+q*t:ℝ):ℂ))
        (Icc (2*(j.val:ℝ)) (2*(j.val:ℝ)+1)) := by
      intro t htm
      rw [ht.2.2.1 j t htm]
      congr 1
      dsimp [p,q]; ring
    rw [integral_on_piece γ _ _ _ (by linarith) he f,line_affine_integral]
    congr 1 <;> dsimp [p,q] <;> ring
  have hodd (i : Fin n) :
      (∫ t in 2*(i.val:ℝ)+1..2*(i.val:ℝ)+2, f (γ t) * deriv γ t) =
      -(∫ θ in (0:ℝ)..Real.pi, ArcIntegrand ((e i).val : ℂ) (ε (e i)) f θ) := by
    let p := Real.pi*(2*(i.val:ℝ)+2)
    let q := -Real.pi
    have he : EqOn γ (fun t => circleMap ((e i).val : ℂ) (ε (e i)) (p+q*t))
        (Icc (2*(i.val:ℝ)+1) (2*(i.val:ℝ)+2)) := by
      intro t htm
      rw [ht.2.2.2 i t htm]
      congr 1
      dsimp [p,q]; ring
    rw [integral_on_piece γ _ _ _ (by linarith) he f,arc_affine_integral]
    have hpa : p+q*(2*(i.val:ℝ)+1) = Real.pi := by dsimp [p,q]; ring
    have hpb : p+q*(2*(i.val:ℝ)+2) = 0 := by dsimp [p,q]; ring
    rw [hpa,hpb,intervalIntegral.integral_symm]
  have hi := C1Partition.parameter_integrable γ.path γ.partition f hf
  rw [PiecewiseC1Path.integral,
    C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hf, ht.1,ht.2.1]
  have hunit := integral_units (2*n+1) (fun t => f (γ t) * deriv γ t)
    (by simpa only [ht.1,ht.2.1] using hi)
  rw [hunit]
  let F : ℕ → ℂ := fun k => ∫ t in (k:ℝ)..(k:ℝ)+1, f (γ t) * deriv γ t
  change (∑ k : Fin (2*n+1), F k.val) = _
  rw [Fin.sum_univ_eq_sum_range F (2*n+1), sum_range_alternating,
    ← Fin.sum_univ_eq_sum_range (fun j => F (2*j)) (n+1),
    ← Fin.sum_univ_eq_sum_range (fun i => F (2*i+1)) n]
  dsimp only [F]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  simp_rw [show ∀ i : Fin n, (2*(i.val:ℝ)+1)+1 = 2*(i.val:ℝ)+2 by intro i; ring,
    heven,hodd,Finset.sum_neg_distrib]
  rw [retained_integral_eq_sum s l u ε n e start stop ha hg _ hreal]
  have hesum := e.sum_comp (fun a : s => ∫ θ in (0:ℝ)..Real.pi,
    ArcIntegrand (a.val : ℂ) (ε a) f θ)
  rw [hesum]
  rfl

/-- Angular integral of the canonical angular path. -/
theorem arcPath_integral (c : ℂ) (r : ℝ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (arcPath c r).trace) :
    (arcPath c r).integral f = ∫ t in (0:ℝ)..Real.pi, ArcIntegrand c r f t := by
  rw [PiecewiseC1Path.integral_congr_representative (arcPath c r) (circleMap c r) f hf
    (fun _ _ => rfl)]
  simp only [arcPath_a,arcPath_b,deriv_circleMap,ArcIntegrand]

/-- Exact calculus of a closing traversal. This uses no holomorphy. -/
theorem closing_integral (s : Finset ℝ) (r : ℝ) (ε : s → ℝ)
    (n : ℕ) (e : Fin n ≃ s) (start stop : Fin (n+1) → ℝ)
    (γ δ : PiecewiseC1Path) (h : Geometry s r ε)
    (hg : Gaps (-r) r ε e start stop) (ht : Traversal ε e start stop γ)
    (hu : γ.path.target = (r:ℂ)) (hd : ClosingTraversal γ δ)
    (ho : EqOn δ (fun t => circleMap 0 r (Real.pi*(t-1))) (Icc 1 2))
    (f : ℂ → ℂ) (hf : ContinuousOn f (TraceSet s r ε)) :
    δ.integral f = BoundaryIntegral s r ε f := by
  have htr := OrderedIndentedDiameter.trace_of_traversal s (-r) r ε n e start stop γ
    (geometry_admissible s r ε h) hg ht
  have hfγ : ContinuousOn f γ.trace := hf.mono (by
    rw [htr]
    intro z hz
    rcases hz with hreal | hsmall
    · exact Or.inl (Or.inl hreal)
    · exact Or.inr hsmall)
  have hfarc : ContinuousOn f (arcPath 0 r).trace :=
    hf.mono (by intro z hz; exact Or.inl (Or.inr hz))
  have hc : γ.path.target = (arcPath 0 r).path.source := by
    simpa [ComplexPath.source,circleMap] using hu
  have he : EqOn δ (fun t => arcPath 0 r (-Real.pi+Real.pi*t)) (Icc 1 2) := by
    intro t ht
    change δ t = circleMap 0 r (-Real.pi+Real.pi*t)
    rw [ho ht]
    apply congrArg (circleMap 0 r)
    ring
  have hh := PiecewiseC1Path.integral_concatenation γ (arcPath 0 r) δ 1
    γ.path.a (γ.path.b-γ.path.a) (-Real.pi) Real.pi f
    (by rw [hd.1,hd.2.1]; norm_num) (sub_nonneg.mpr γ.path.ordered) Real.pi_pos.le hc
    (by rw [hd.1]; ring) (by ring) (by simp) (by rw [hd.2.1]; simp; ring)
    (by simpa only [hd.1] using hd.2.2) (by simpa only [hd.2.1] using he) hfγ hfarc
  rw [hh, diameter_integral s (-r) r ε n e start stop γ
    (geometry_admissible s r ε h) hg ht f hfγ, arcPath_integral 0 r f hfarc]
  unfold BoundaryIntegral
  abel

/-- Deleting disjoint open intervals subtracts exactly their ordinary integrals.
This lemma is used for reciprocal kernels at nonreal points only. -/
theorem retained_integral_sub (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ)
    (ha : Admissible s l u ε) (g : ℝ → ℂ) (hf : ContinuousOn g (Icc l u)) :
    (∫ x in Retained s l u ε, g x) = (∫ x in l..u, g x) -
      ∑ a : s, ∫ x in a.val-ε a..a.val+ε a, g x := by
  have hsub (a : s) : Ioo (a.val-ε a) (a.val+ε a) ⊆ Icc l u := by
    intro x hx
    have hh := ha.2.1 a
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hdis : Pairwise (Disjoint on (fun a : s => Ioo (a.val-ε a) (a.val+ε a))) := by
    intro a b hab
    apply disjoint_left.mpr
    intro x hxa hxb
    have hv : a.val ≠ b.val := fun hh => hab (Subtype.ext hh)
    rcases lt_or_gt_of_ne hv with h | h
    · linarith [ha.2.2 a b h,hxa.2,hxb.1]
    · linarith [ha.2.2 b a h,hxb.2,hxa.1]
  unfold Retained
  rw [setIntegral_sdiff (MeasurableSet.iUnion (fun _ => measurableSet_Ioo))
    hf.integrableOn_Icc (iUnion_subset hsub),
    integral_iUnion_fintype (fun _ => measurableSet_Ioo) hdis
      (fun a => hf.integrableOn_Icc.mono_set (hsub a)),
    intervalIntegral.integral_of_le ha.1.le,integral_Icc_eq_integral_Ioc]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [intervalIntegral.integral_of_le (by linarith [(ha.2.1 a).1]), integral_Ioc_eq_integral_Ioo]

/-- Integral formula for the previously accepted unindented half-disk traversal. -/
theorem half_disk_integral (β : PiecewiseC1Path) (c r : ℝ)
    (ht : Specs.D12Complex.Ch04.IndexComputations.half_disk_traversal β (c:ℂ) 1 r)
    (f : ℂ → ℂ) (hf : ContinuousOn f β.trace) :
    β.integral f = (∫ x in c-r..c+r, f (x:ℂ)) +
      ∫ θ in (0:ℝ)..Real.pi, ArcIntegrand (c:ℂ) r f θ := by
  have h0 : EqOn β (fun t => ((c-r+(2*r)*t:ℝ):ℂ)) (Icc 0 1) := by
    intro t htm
    rw [ht.2.2.1 t htm]
    push_cast
    ring
  have h1 : EqOn β (fun t => circleMap (c:ℂ) r (-Real.pi+Real.pi*t)) (Icc 1 2) := by
    intro t htm
    rw [ht.2.2.2 t htm]
    have he : Real.pi*(t-1) = -Real.pi+Real.pi*t := by ring
    simp only [mul_one,he,circleMap]
  have hi := C1Partition.parameter_integrable β.path β.partition f hf
  rw [PiecewiseC1Path.integral,
    C1Partition.integral_eq_intervalIntegral β.path β.partition f hf,ht.1,ht.2.1]
  have hh := integral_units 2 (fun t => f (β t) * deriv β t)
    (by simpa only [ht.1,ht.2.1,Nat.cast_ofNat] using hi)
  norm_num only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one,
    zero_add,one_add_one_eq_two,Nat.cast_ofNat] at hh
  rw [hh, integral_on_piece β _ 0 1 (by norm_num) h0 f,
    integral_on_piece β _ 1 2 (by norm_num) h1 f,
    line_affine_integral, arc_affine_integral]
  simp only [mul_zero,add_zero,mul_one]
  have hp : c-r+2*r = c+r := by ring
  have hπ : -Real.pi+Real.pi*2 = Real.pi := by ring
  rw [hp,hπ,neg_add_cancel]

/-- Reciprocal kernels are continuous on every set that avoids their pole. -/
theorem reciprocal_continuous (a : ℂ) (T : Set ℂ) (ha : a ∉ T) :
    ContinuousOn (fun z : ℂ => 1/(z-a)) T := by
  apply continuousOn_const.div (continuous_id.sub continuous_const).continuousOn
  intro z hz
  exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz ha)

/-- Reciprocal-integral comparison at a strictly upper point. All auxiliary
half-disk indices are evaluated off their traces. No cycle subtraction is used
as an avoiding contour. -/
theorem upper_index (s : Finset ℝ) (r : ℝ) (ε : s → ℝ)
    (h : Geometry s r ε) (δ : PiecewiseC1Path) (htrace : δ.trace = TraceSet s r ε)
    (hcalc : ∀ f : ℂ → ℂ, ContinuousOn f (TraceSet s r ε) →
      δ.integral f = BoundaryIntegral s r ε f)
    (a : ℂ) (har : ‖a‖ < r) (hai : 0 < a.im)
    (haε : ∀ x : s, ε x < ‖a-(x.val:ℂ)‖) : a ∉ δ.trace ∧ δ.index a = 1 := by
  have havoid := upper_avoids s r ε h a har hai haε
  have hδavoid : a ∉ δ.trace := by rwa [htrace]
  refine ⟨hδavoid, ?_⟩
  let k : ℂ → ℂ := fun z => 1/(z-a)
  have hkreal : Continuous (fun x : ℝ => k (x:ℂ)) := by
    apply continuous_const.div (Complex.continuous_ofReal.sub continuous_const)
    intro x he
    have hh := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.ofReal_im] at hh
    linarith
  have hN : (2*(Real.pi:ℂ)*Complex.I)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hsmall (x : s) :
      (∫ t in x.val-ε x..x.val+ε x, k (t:ℂ)) +
        (∫ θ in (0:ℝ)..Real.pi, ArcIntegrand (x.val:ℂ) (ε x) k θ) = 0 := by
    obtain ⟨β,hβ⟩ := IndexComputations.half_disk_boundary_exists (x.val:ℂ) 1 (ε x)
      (by simp) (h.2.1 x).1
    have hβavoid : a ∉ β.trace := by
      intro hm
      have hh := (IndexComputations.half_disk_trace_coordinates β (by simp) (h.2.1 x).1 hβ a hm).1.1
      linarith [haε x]
    have hind := IndexComputations.half_disk_index_exterior β (x.val:ℂ) 1 a (ε x)
      (by simp) (h.2.1 x).1 hβ (Or.inl (haε x))
    have hnorm := IndexOperationsHomotopy.path_index_eq_integral β a hβavoid
    rw [hind] at hnorm
    have hz : β.integral k = 0 :=
      (mul_eq_zero.mp hnorm.symm).resolve_left hN
    rw [half_disk_integral β x.val (ε x) hβ k (reciprocal_continuous a β.trace hβavoid)] at hz
    exact hz
  obtain ⟨β,hβ⟩ := IndexComputations.half_disk_boundary_exists 0 1 r (by simp) h.1
  have hβavoid : a ∉ β.trace := by
    intro hm
    have hh := (IndexComputations.half_disk_trace_coordinates β (by simp) h.1 hβ a hm).2
    simp only [sub_zero,div_one] at hh
    rcases hh with hn | hi
    · linarith
    · linarith
  have hβindex : β.index a = 1 :=
    IndexComputations.half_disk_index_interior β 0 1 a r (by simp) h.1 hβ
      (by simpa using And.intro har hai)
  have hβint : β.integral k = (∫ t in -r..r, k (t:ℂ)) +
      ∫ θ in (0:ℝ)..Real.pi, ArcIntegrand 0 r k θ := by
    simpa only [zero_sub,zero_add,Complex.ofReal_zero] using
      half_disk_integral β 0 r hβ k (reciprocal_continuous a β.trace hβavoid)
  have hδint := hcalc k (reciprocal_continuous a (TraceSet s r ε) havoid)
  have hsum : (∑ x : s, ∫ t in x.val-ε x..x.val+ε x, k (t:ℂ)) +
      (∑ x : s, ∫ θ in (0:ℝ)..Real.pi, ArcIntegrand (x.val:ℂ) (ε x) k θ) = 0 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hsmall]
    simp
  have hcomparison : δ.integral k = β.integral k := by
    rw [hδint,BoundaryIntegral,
      retained_integral_sub s (-r) r ε (geometry_admissible s r ε h) _ hkreal.continuousOn,
      hβint]
    linear_combination -hsum
  rw [IndexOperationsHomotopy.path_index_eq_integral δ a hδavoid]
  change (2*(Real.pi:ℂ)*Complex.I)⁻¹ * δ.integral k = 1
  rw [hcomparison,← IndexOperationsHomotopy.path_index_eq_integral β a hβavoid,hβindex]

/-- The complete continuous-integrand calculus and index theorem for a finite
indented upper half-disk. The one witness works for every continuous integrand. -/
theorem contour_calculus : contour_calculus_type := by
  intro s r ε h
  obtain ⟨n,e,start,stop,γ,δ,hg,ht,hs,hu,hd,ho,hclosed,htrace⟩ := contour_exists s r ε h
  have hcalc := closing_integral s r ε n e start stop γ δ h hg ht hu hd ho
  refine ⟨n,e,start,stop,γ,δ,hg,ht,hs,hu,hd,ho,hclosed,htrace,?_,?_,?_⟩
  · intro f hf
    refine ⟨boundary_integrable s r ε f hf, ?_, hcalc f hf⟩
    apply C1Partition.parameter_integrable δ.path δ.partition f
    change ContinuousOn f δ.trace
    rwa [htrace]
  · exact fun a har hai haε => upper_index s r ε h δ htrace hcalc a har hai haε
  · intro a ha havoid
    apply closed_path_index_zero_below δ hclosed
    · intro z hz
      exact trace_im_nonneg s r ε h z (htrace ▸ hz)
    · exact ha
    · rwa [htrace]

end D12Complex.IndentedContourCalculus
