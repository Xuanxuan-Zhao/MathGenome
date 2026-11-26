import Specs.LinearAlgebraicGroups.Arithmetic.PadicLogarithmChart
import LinearAlgebraicGroups.Affine.LieBracket
import LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.NumberTheory.Padics.RingHoms
import Batteries.Tactic.OpenPrivate

noncomputable section

open NormedSpace Set Filter Topology

set_option linter.style.haveILetI false
open scoped ENNReal Topology Nat

namespace LinearAlgebraicGroups.Arithmetic.PadicLogarithmChart

open Specs.PadicLogarithmChart

variable (p : ℕ) [hp : Fact p.Prime]

private theorem norm_p_pos : 0 < ‖(p : ℚ_[p])‖ := by
  rw [Padic.norm_p]
  exact inv_pos.mpr (by exact_mod_cast hp.out.pos)

private theorem norm_p_lt_one : ‖(p : ℚ_[p])‖ < 1 := by
  rw [Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

private theorem norm_inv_natCast (m n : ℕ) (hm : m ≠ 0)
    (h : padicValNat p m ≤ n) :
    ‖(m : ℚ_[p])⁻¹‖ ≤ (p : ℝ) ^ n := by
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
  have hm' : (m : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [norm_inv, Padic.norm_eq_zpow_neg_valuation hm', Padic.valuation_natCast,
    ← zpow_neg, neg_neg, zpow_natCast]
  exact pow_le_pow_right₀ hp1 h

private theorem exp_coefficient_bound (n : ℕ) :
    ‖((n ! : ℚ_[p])⁻¹)‖ * ‖(p : ℚ_[p])‖ ^ n ≤ 1 := by
  calc
    _ ≤ (p : ℝ) ^ n * ‖(p : ℚ_[p])‖ ^ n :=
      mul_le_mul_of_nonneg_right
        (norm_inv_natCast p (n !) n n.factorial_ne_zero (padicValNat_factorial_le (p := p) n))
        (by positivity)
    _ = 1 := by
      rw [← mul_pow, Padic.norm_p, mul_inv_cancel₀ (by exact_mod_cast hp.out.ne_zero), one_pow]

theorem exponentialRadius : ExponentialRadius := by
  intro p hp A _ _
  apply FormalMultilinearSeries.le_radius_of_bound (C := max 1 ‖(1 : A)‖)
  intro n
  rw [expSeries, norm_smul]
  change ‖((n ! : ℚ_[p])⁻¹)‖ *
    ‖ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[p] n A‖ * ‖(p : ℚ_[p])‖ ^ n ≤ _
  rw [mul_right_comm]
  calc
    _ ≤ 1 * max 1 ‖(1 : A)‖ :=
      mul_le_mul (exp_coefficient_bound p n) ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
        (norm_nonneg (ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[p] n A))
        zero_le_one
    _ = _ := one_mul _

theorem logarithmRadius : LogarithmRadius := by
  intro p hp A _ _
  apply FormalMultilinearSeries.le_radius_of_bound (C := max 1 ‖(1 : A)‖)
  intro n
  rw [logSeries, norm_smul]
  change ‖((-1) ^ (n + 1) / n : ℚ_[p])‖ *
    ‖ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[p] n A‖ * ‖(p : ℚ_[p])‖ ^ n ≤ _
  have hn : ‖((-1) ^ (n + 1) / n : ℚ_[p])‖ * ‖(p : ℚ_[p])‖ ^ n ≤ 1 := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hval : padicValNat p n ≤ n :=
      (Nat.le_mul_of_pos_left _ hp.out.pos).trans mul_padicValNat_le
    rw [← norm_inv]
    calc
      _ ≤ (p : ℝ) ^ n * ‖(p : ℚ_[p])‖ ^ n :=
        mul_le_mul_of_nonneg_right (norm_inv_natCast p n n hn hval) (by positivity)
      _ = 1 := by
        rw [← mul_pow, Padic.norm_p, mul_inv_cancel₀ (by exact_mod_cast hp.out.ne_zero), one_pow]
  rw [mul_right_comm]
  calc
    _ ≤ 1 * max 1 ‖(1 : A)‖ :=
      mul_le_mul hn ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
        (norm_nonneg (ContinuousMultilinearMap.mkPiAlgebraFin ℚ_[p] n A))
        zero_le_one
    _ = _ := one_mul _

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A]

private theorem exp_radius_pos : 0 < (expSeries ℚ_[p] A).radius := by
  apply lt_of_lt_of_le _ (exponentialRadius p A)
  exact_mod_cast norm_p_pos p

theorem ambientExponentialChart : AmbientExponentialChart := by
  intro p _ A _ _ _
  let idEquiv := ContinuousLinearEquiv.refl ℚ_[p] A
  have h : HasStrictFDerivAt (exp : A → A) (idEquiv : A →L[ℚ_[p]] A) 0 :=
    hasStrictFDerivAt_exp_zero_of_radius_pos (exp_radius_pos p)
  exact ⟨h.toOpenPartialHomeomorph exp, h.mem_toOpenPartialHomeomorph_source, rfl, exp_zero⟩

theorem conjugationDerivative : ConjugationDerivative := by
  intro p _ A _ _ _ Y
  have he : HasStrictFDerivAt (exp : A → A) (1 : A →L[ℚ_[p]] A) 0 :=
    hasStrictFDerivAt_exp_zero_of_radius_pos (exp_radius_pos p)
  have hneg : HasStrictFDerivAt (fun x : A => -x) (-(1 : A →L[ℚ_[p]] A)) 0 :=
    (hasStrictFDerivAt_id (𝕜 := ℚ_[p]) (0 : A)).neg
  have hn := (show HasStrictFDerivAt (exp : A → A) (1 : A →L[ℚ_[p]] A) (-(0 : A)) by
    simpa using he).comp 0 hneg
  refine ((he.mul_const' Y).mul' hn).congr_fderiv ?_
  ext x
  simp [exp_zero, sub_eq_add_neg, add_comm]


section Subgroups

variable {p : ℕ} [Fact p.Prime] {B E J : Type*}
    [NormedRing B] [NormedAlgebra ℚ_[p] B]
    [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    [Group J] [TopologicalSpace J]
    {m : J →* Bˣ} {j : E →L[ℚ_[p]] B}

private theorem smul_mem_source (c : ExponentialChart p m j) {x : E}
    (hx : x ∈ c.chart.source) (t : ℚ_[p]) (ht : ‖t‖ ≤ 1) : t • x ∈ c.chart.source := by
  rw [c.source_eq, Metric.mem_ball, dist_zero_right] at hx ⊢
  exact lt_of_le_of_lt (norm_smul_le t x |>.trans (mul_le_of_le_one_left (norm_nonneg x) ht)) hx

private theorem zero_mem_source (c : ExponentialChart p m j) : 0 ∈ c.chart.source := by
  simpa [c.source_eq] using c.radius_pos

private theorem one_mem_target (c : ExponentialChart p m j) : 1 ∈ c.chart.target :=
  c.at_zero ▸ c.chart.map_source (zero_mem_source c)

private theorem log_one_chart (c : ExponentialChart p m j) : c.chart.symm 1 = 0 := by
  rw [← c.at_zero, c.chart.left_inv (zero_mem_source c)]

private theorem norm_natCast_le_one (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) (n : ℤ)

omit [TopologicalSpace J] in
private theorem units_coe_injective (hm : Function.Injective m) :
    Function.Injective (fun x : J => (m x : B)) := Units.val_injective.comp hm

variable [CompleteSpace B]

private theorem exp_nat_smul (c : ExponentialChart p m j) (hm : Function.Injective m)
    {x : E} (hx : x ∈ c.chart.source) (n : ℕ) :
    c.chart ((n : ℚ_[p]) • x) = c.chart x ^ n := by
  induction n with
  | zero => simp [c.at_zero]
  | succ n ih =>
    apply units_coe_injective hm
    dsimp only
    have hn := smul_mem_source c hx (n : ℚ_[p]) (norm_natCast_le_one n)
    rw [Nat.cast_succ, add_smul, one_smul]
    have hsn : (n : ℚ_[p]) • x + x ∈ c.chart.source := by
      simpa [Nat.cast_succ, add_smul] using
        smul_mem_source c hx (↑(n + 1) : ℚ_[p]) (norm_natCast_le_one (n + 1))
    rw [c.matrix_exp _ hsn, map_add, pow_succ, map_mul, Units.val_mul, ← ih,
      c.matrix_exp _ hn, c.matrix_exp _ hx]
    exact exp_add_of_commute_of_mem_ball
      (by rw [map_smul]; exact (Commute.refl _).smul_left _)
      (c.converges _ hn) (c.converges _ hx)

theorem padicIntegerLines : PadicIntegerLines := by
  intro p _ B E J _ _ _ _ _ _ _ m j c hm H hH x hx hxH s
  let f : ℤ_[p] → E := fun t => (t : ℚ_[p]) • x
  have hf : Continuous f := continuous_subtype_val.smul continuous_const
  have hmaps : MapsTo f univ c.chart.source := by
    intro t _
    apply smul_mem_source c hx
    simpa only [PadicInt.norm_coe] using PadicInt.norm_le_one t
  have hcont : Continuous (c.chart ∘ f) :=
    continuousOn_univ.mp (c.chart.continuousOn.comp hf.continuousOn hmaps)
  refine PadicInt.denseRange_natCast.induction_on s (hH.preimage hcont) fun n => ?_
  change c.chart (((n : ℤ_[p]) : ℚ_[p]) • x) ∈ H
  rw [PadicInt.coe_natCast, exp_nat_smul c hm hx]
  exact H.pow_mem hxH n


private theorem exp_conj_of_mem_ball (u : Bˣ) {x : B}
    (hx : x ∈ Metric.eball 0 (expSeries ℚ_[p] B).radius) :
    exp ((u : B) * x * (↑u⁻¹ : B)) = (u : B) * exp x * (↑u⁻¹ : B) := by
  let f : B →+* B := MulSemiringAction.toRingHom (ConjAct Bˣ) B (ConjAct.toConjAct u)
  have hf (y : B) : f y = (u : B) * y * (↑u⁻¹ : B) := by
    change ConjAct.toConjAct u • y = _
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  have hc : Continuous f := by
    simp_rw [show (f : B → B) = _ from funext hf]
    fun_prop
  simpa only [hf] using (map_exp_of_mem_ball (𝕂 := ℚ_[p]) f hc x hx).symm

end Subgroups

theorem nonzeroLogarithmSpan : NonzeroLogarithmSpan := by
  intro p _ B E J _ _ _ _ _ _ _ m j c H hnondiscrete hspan
  apply hnondiscrete
  apply discreteTopology_of_isOpen_singleton_one
  have heq : ((↑) : H → J) ⁻¹' c.chart.target = ({1} : Set H) := by
    ext h
    constructor
    · intro hh
      have hh' : c.chart.symm h ∈ smallLogarithmSpan c H :=
        Submodule.subset_span ⟨h, ⟨h.property, hh⟩, rfl⟩
      rw [hspan, Submodule.mem_bot] at hh'
      have := c.chart.right_inv hh
      rw [hh', c.at_zero] at this
      exact Set.mem_singleton_iff.mpr (Subtype.ext this.symm)
    · rintro h
      obtain rfl := Set.mem_singleton_iff.mp h
      exact one_mem_target c
  rw [← heq]
  exact c.chart.open_target.preimage continuous_subtype_val


theorem invarianceOfLogarithmSpan : InvarianceOfLogarithmSpan := by
  intro p _ B E J _ _ _ _ _ _ _ m j c hm H a ad had x hx
  refine Submodule.span_induction (fun y hy => ?_) ?_ ?_ ?_ hx
  · obtain ⟨g, ⟨hg, hgt⟩, rfl⟩ := hy
    let y : E := c.chart.symm g
    have hys : y ∈ c.chart.source := c.chart.map_target hgt
    have hgy : c.chart y = g := c.chart.right_inv hgt
    have hlim : Tendsto (fun n : ℕ => (p : ℚ_[p]) ^ n • ad y) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_p_lt_one p)).smul
        (tendsto_const_nhds (x := ad y))
    have hsource := c.chart.open_source.mem_nhds (zero_mem_source c)
    obtain ⟨n, hn⟩ := (hlim.eventually_mem hsource).exists
    let d := p ^ n
    have hcast : (d : ℚ_[p]) = (p : ℚ_[p]) ^ n := Nat.cast_pow _ _
    rw [← hcast] at hn
    have hds := smul_mem_source c hys (d : ℚ_[p]) (norm_natCast_le_one d)
    have hgpow : c.chart ((d : ℚ_[p]) • y) = g ^ d :=
      (exp_nat_smul c hm hys d).trans (by rw [hgy])
    have hconj : c.chart ((d : ℚ_[p]) • ad y) =
        (a : J) * c.chart ((d : ℚ_[p]) • y) * (a : J)⁻¹ := by
      apply units_coe_injective hm
      dsimp only
      rw [c.matrix_exp _ hn, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
        c.matrix_exp _ hds, ← exp_conj_of_mem_ball (m a) (c.converges _ hds)]
      congr 1
      rw [map_smul, map_smul, had, mul_smul_comm, smul_mul_assoc]
    have hmH : c.chart ((d : ℚ_[p]) • ad y) ∈ H := by
      rw [hconj, hgpow]
      exact H.mul_mem (H.mul_mem a.property (H.pow_mem hg d)) (H.inv_mem a.property)
    have hmem : (d : ℚ_[p]) • ad y ∈ smallLogarithmSpan c H :=
      Submodule.subset_span
        ⟨c.chart ((d : ℚ_[p]) • ad y), ⟨hmH, c.chart.map_source hn⟩, c.chart.left_inv hn⟩
    have hd : (d : ℚ_[p]) ≠ 0 := by
      rw [hcast]
      exact pow_ne_zero _ (norm_pos_iff.mp (norm_p_pos p))
    have hscaled := (smallLogarithmSpan c H).smul_mem (d : ℚ_[p])⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at hscaled
  · rw [map_zero]
    exact (smallLogarithmSpan c H).zero_mem
  · intro u v _ _ hu hv
    rw [map_add]
    exact (smallLogarithmSpan c H).add_mem hu hv
  · intro t u _ hu
    rw [map_smul]
    exact (smallLogarithmSpan c H).smul_mem t hu


private theorem strictDerivative_listProduct {k D B I : Type*} [NontriviallyNormedField k]
    [NormedAddCommGroup D] [NormedSpace k D] [NormedRing B] [NormedAlgebra k B]
    (f : I → D → B) (df : I → D →L[k] B)
    (h₀ : ∀ i, f i 0 = 1) (hd : ∀ i, HasStrictFDerivAt (f i) (df i) 0)
    (l : List I) :
    HasStrictFDerivAt (fun t => (l.map fun i => f i t).prod) (l.map df).sum 0 := by
  induction l with
  | nil => simpa using (hasStrictFDerivAt_const (𝕜 := k) (1 : B) (0 : D))
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ((hd i).mul' ih).congr_fderiv ?_
    ext z
    simp [h₀, add_comm]

private theorem listProduct_tendsto_one {I X J : Type*} [Group J] [TopologicalSpace J]
    [IsTopologicalGroup J] {l : Filter X} (f : I → X → J)
    (h : ∀ i, Tendsto (f i) l (𝓝 1)) (is : List I) :
    Tendsto (fun t => (is.map fun i => f i t).prod) l (𝓝 1) := by
  induction is with
  | nil => simpa using tendsto_const_nhds (x := (1 : J)) (f := l)
  | cons i is ih =>
    simpa only [List.map_cons, List.prod_cons, one_mul] using (h i).mul ih

theorem opennessOfFullSpan : OpennessOfFullSpan := by
  intro p _ B E J _ _ _ _ _ _ _ _ _ _ m j c hm hj H hH hspan
  classical
  let s := c.chart.symm '' ((H : Set J) ∩ c.chart.target)
  have hs : (⊤ : Submodule ℚ_[p] E) ≤ Submodule.span ℚ_[p] s := hspan.ge
  let ι : Set E := (linearIndepOn_empty ℚ_[p] id).extend (empty_subset s)
  let b₀ : Module.Basis ι ℚ_[p] E := Module.Basis.ofSpan hs
  letI := b₀.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℚ_[p] E)
  let n := Fintype.card ι
  let b : Module.Basis (Fin n) ℚ_[p] E := b₀.reindex (Fintype.equivFin ι)
  have hb (i : Fin n) : b i ∈ s := by
    rw [show b = b₀.reindex (Fintype.equivFin ι) from rfl, Module.Basis.reindex_apply]
    exact Module.Basis.ofSpan_subset hs ⟨_, rfl⟩
  have hbs (i : Fin n) : b i ∈ c.chart.source := by
    obtain ⟨g, ⟨_, hgt⟩, heq⟩ := hb i
    rw [← heq]
    exact c.chart.map_target hgt
  have hbH (i : Fin n) : c.chart (b i) ∈ H := by
    obtain ⟨g, ⟨hg, hgt⟩, heq⟩ := hb i
    rwa [← heq, c.chart.right_inv hgt]

  let D := Fin n → ℚ_[p]
  let unitFactor (i : Fin n) (t : D) := c.chart (t i • b i)
  let prodPoints (t : D) := ((List.finRange n).map fun i => unitFactor i t).prod
  have ht₀ (i : Fin n) : Tendsto (fun t : D => t i • b i) (𝓝 0) (𝓝 0) := by
    have h := ((continuous_apply i).continuousAt (x := (0 : D))).smul
      (continuousAt_const (x := (0 : D)) (y := b i))
    change Tendsto (fun t : D => t i • b i) (𝓝 0) (𝓝 ((0 : ℚ_[p]) • b i)) at h
    rwa [zero_smul] at h
  have htSource : ∀ᶠ t : D in 𝓝 0, ∀ i, t i • b i ∈ c.chart.source :=
    Filter.eventually_all.mpr fun i =>
      (ht₀ i).eventually_mem (c.chart.open_source.mem_nhds (zero_mem_source c))
  have hg : Tendsto prodPoints (𝓝 0) (𝓝 1) := by
    apply listProduct_tendsto_one
    intro i
    change Tendsto ((c.chart : E → J) ∘ (fun t : D => t i • b i)) (𝓝 0) (𝓝 1)
    rw [← c.at_zero]
    exact (c.chart.continuousAt (zero_mem_source c)).tendsto.comp (ht₀ i)
  have hg₀ : prodPoints 0 = 1 := by
    apply List.prod_eq_one
    rintro g hg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    change c.chart ((0 : ℚ_[p]) • b i) = 1
    rw [zero_smul, c.at_zero]
  have hgH : ∀ᶠ t : D in 𝓝 0, prodPoints t ∈ H := by
    have hcoords : ∀ᶠ t : D in 𝓝 0, ∀ i, ‖t i‖ < 1 :=
      Filter.eventually_all.mpr fun i => by
        have h := (continuous_apply i).continuousAt (x := (0 : D))
        exact h.norm.eventually_lt (continuousAt_const (x := (0 : D)) (y := (1 : ℝ)))
          (by change ‖(0 : ℚ_[p])‖ < 1; simp)
    filter_upwards [hcoords] with t ht
    apply H.list_prod_mem
    intro g hg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact padicIntegerLines p B E J c hm H hH (b i) (hbs i) (hbH i)
      ⟨t i, (ht i).le⟩

  let expFactor (i : Fin n) (t : D) := exp (t i • j (b i))
  let f (t : D) := ((List.finRange n).map fun i => expFactor i t).prod
  have hf₀ : f 0 = 1 := by
    apply List.prod_eq_one
    rintro g hg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    change exp ((0 : ℚ_[p]) • j (b i)) = 1
    rw [zero_smul, exp_zero]
  let bmap := (b.equivFunL.symm : D →L[ℚ_[p]] E)
  have hd : HasStrictFDerivAt f (j.comp bmap) 0 := by
    have he : HasStrictFDerivAt (exp : B → B) (1 : B →L[ℚ_[p]] B) 0 :=
      hasStrictFDerivAt_exp_zero_of_radius_pos (exp_radius_pos p)
    let d (i : Fin n) :=
      (ContinuousLinearMap.proj i : D →L[ℚ_[p]] ℚ_[p]).smulRight (j (b i))
    have h (i : Fin n) : HasStrictFDerivAt (expFactor i) (d i) 0 := by
      have he' : HasStrictFDerivAt (exp : B → B) (1 : B →L[ℚ_[p]] B) (d i 0) := by
        simpa only [map_zero] using he
      refine (he'.comp 0 (d i).hasStrictFDerivAt).congr_fderiv ?_
      ext t
      rfl
    have h₀ (i : Fin n) : expFactor i 0 = 1 := by
      change exp ((0 : ℚ_[p]) • j (b i)) = 1
      rw [zero_smul, exp_zero]
    refine (strictDerivative_listProduct expFactor d h₀ h
      (List.finRange n)).congr_fderiv ?_
    ext t
    change ((List.finRange n).map d).sum t = j (b.equivFun.symm t)
    rw [← List.ofFn_id, List.map_ofFn, List.sum_ofFn]
    simp [d, Module.Basis.equivFun_symm_apply, map_sum]

  obtain ⟨r, hr⟩ := j.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hj)
  let R := r.toContinuousLinearMap
  have hR (v : E) : R (j v) = v := LinearMap.congr_fun hr v
  let I := ContinuousLinearEquiv.refl ℚ_[p] B
  have he : HasStrictFDerivAt (exp : B → B) (I : B →L[ℚ_[p]] B) 0 :=
    hasStrictFDerivAt_exp_zero_of_radius_pos (exp_radius_pos p)
  let logB := he.localInverse exp I 0
  have hlog : HasStrictFDerivAt logB (I.symm : B →L[ℚ_[p]] B) (f 0) := by
    rw [hf₀, ← exp_zero (𝔸 := B)]
    exact he.to_localInverse
  let F := c.chart.symm ∘ prodPoints
  have hF₀ : F 0 = 0 := by
    change c.chart.symm (prodPoints 0) = 0
    rw [hg₀, log_one_chart]
  have hF : Tendsto F (𝓝 0) (𝓝 0) := by
    simpa only [log_one_chart c] using
      (c.chart.continuousAt_symm (one_mem_target c)).tendsto.comp hg
  have hproduct : ∀ᶠ t : D in 𝓝 0, f t = (m (prodPoints t) : B) := by
    filter_upwards [htSource] with t ht
    simp only [f, prodPoints, expFactor, unitFactor]
    change ((List.finRange n).map _).prod =
      ((Units.coeHom B).comp m) (((List.finRange n).map _).prod)
    rw [map_list_prod]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    change exp (t i • j (b i)) = (m (c.chart (t i • b i)) : B)
    rw [c.matrix_exp _ (ht i), map_smul]
  have htTarget := hg.eventually_mem (c.chart.open_target.mem_nhds (one_mem_target c))
  have heq : (fun t => R (logB (f t))) =ᶠ[𝓝 0] F := by
    have hleft : ∀ᶠ w in 𝓝 (0 : B), logB (exp w) = w := he.eventually_left_inverse
    have hlin : Tendsto (fun t => j (F t)) (𝓝 0) (𝓝 0) := by
      change Tendsto ((j : E → B) ∘ F) (𝓝 0) (𝓝 0)
      rw [← j.map_zero]
      exact j.continuous.continuousAt.tendsto.comp hF
    have htleft : ∀ᶠ t in 𝓝 (0 : D), logB (exp (j (F t))) = j (F t) :=
      hlin.eventually hleft
    filter_upwards [htTarget, hproduct, htleft] with t ht htprod htl
    have hsource := c.chart.map_target ht
    have hmat : (m (prodPoints t) : B) = exp (j (F t)) := by
      have h := c.matrix_exp _ hsource
      rwa [c.chart.right_inv ht] at h
    rw [htprod, hmat, htl, hR]

  have hDF : HasStrictFDerivAt F bmap 0 := by
    have hcomp := R.hasStrictFDerivAt.comp 0 (hlog.comp 0 hd)
    apply (hcomp.congr_fderiv ?_).congr_of_eventuallyEq heq
    ext t
    exact hR _
  letI : CompleteSpace E := FiniteDimensional.complete ℚ_[p] E
  have himage : F '' {t | prodPoints t ∈ H ∧ prodPoints t ∈ c.chart.target} ∈ 𝓝 0 := by
    rw [← hF₀, ← hDF.map_nhds_eq_of_surj]
    · exact Filter.image_mem_map (hgH.and htTarget)
    · exact LinearMap.range_eq_top.mpr b.equivFunL.symm.surjective
  apply H.isOpen_of_mem_nhds (g := 1)
  have hmem := (c.chart.continuousAt_symm (one_mem_target c)).tendsto
  rw [log_one_chart] at hmem
  filter_upwards [hmem.eventually_mem himage,
    c.chart.open_target.mem_nhds (one_mem_target c)] with g hg' hgt
  obtain ⟨t, ⟨htH, htt⟩, htg⟩ := hg'
  have : prodPoints t = g := by
    change c.chart.symm (prodPoints t) = c.chart.symm g at htg
    have heq := congrArg c.chart htg
    rwa [c.chart.right_inv htt, c.chart.right_inv hgt] at heq
  change g ∈ H
  rwa [this] at htH




private theorem smul_mem_expBall {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedRing B] [NormedAlgebra ℚ_[p] B] {X : B}
    (hX : X ∈ Metric.eball 0 (expSeries ℚ_[p] B).radius) (s : ℚ_[p]) (hs : ‖s‖ ≤ 1) :
    s • X ∈ Metric.eball 0 (expSeries ℚ_[p] B).radius := by
  simp only [Metric.mem_eball, edist_zero_right] at hX ⊢
  have hn : ‖s‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hs
  calc
    ‖s • X‖ₑ ≤ ‖s‖ₑ * ‖X‖ₑ := enorm_smul_le
    _ ≤ 1 * ‖X‖ₑ := by gcongr
    _ < (expSeries ℚ_[p] B).radius := by simpa only [one_mul] using hX

theorem ambientPadicIntegerLines : AmbientPadicIntegerLines := by
  intro p _ B _ _ _ H hH X hX hx s
  have hnorm (t : ℤ_[p]) : ‖(t : ℚ_[p])‖ ≤ 1 := by
    simpa only [PadicInt.norm_coe] using PadicInt.norm_le_one t
  let ball (t : ℤ_[p]) := smul_mem_expBall hX (t : ℚ_[p]) (hnorm t)
  let f (t : ℤ_[p]) : Bˣ :=
    { val := exp ((t : ℚ_[p]) • X)
      inv := exp (-((t : ℚ_[p]) • X))
      val_inv := (invertibleExpOfMemBall (ball t)).mul_invOf_self
      inv_val := (invertibleExpOfMemBall (ball t)).invOf_mul_self }
  have hc₁ : Continuous fun t : ℤ_[p] => (t : ℚ_[p]) • X :=
    continuous_subtype_val.smul continuous_const
  have hc₂ : Continuous fun t : ℤ_[p] => -((t : ℚ_[p]) • X) := hc₁.neg
  have hc : Continuous f := by
    apply Units.continuous_iff.mpr
    refine ⟨?_, ?_⟩
    · exact continuousOn_univ.mp (continuousOn_exp.comp hc₁.continuousOn (fun t _ => ball t))
    · exact continuousOn_univ.mp (continuousOn_exp.comp hc₂.continuousOn fun t _ => by
        simpa only [Metric.mem_eball, edist_zero_right, enorm_neg] using ball t)
  obtain ⟨u, huH, hu⟩ := hx
  have hf1 : f 1 = u := by
    apply Units.ext
    change exp (((1 : ℤ_[p]) : ℚ_[p]) • X) = (u : B)
    simpa using hu.symm
  have hnat (n : ℕ) : f (n : ℤ_[p]) = u ^ n := by
    induction n with
    | zero =>
      rw [Nat.cast_zero, pow_zero]
      apply Units.ext
      change exp (((0 : ℤ_[p]) : ℚ_[p]) • X) = 1
      simp
    | succ n ih =>
      have hmul : f (n + 1 : ℤ_[p]) = f (n : ℤ_[p]) * f 1 := by
        apply Units.ext
        change exp (((n + 1 : ℤ_[p]) : ℚ_[p]) • X) =
          exp (((n : ℤ_[p]) : ℚ_[p]) • X) * exp (((1 : ℤ_[p]) : ℚ_[p]) • X)
        rw [PadicInt.coe_add, add_smul]
        exact exp_add_of_commute_of_mem_ball
          (((Commute.refl X).smul_left _).smul_right _) (ball (n : ℤ_[p])) (ball 1)
      rw [Nat.cast_succ, hmul, ih, hf1, pow_succ]
  have hfH : f s ∈ H :=
    PadicInt.denseRange_natCast.induction_on s (hH.preimage hc) fun n => by
      rw [hnat]
      exact H.pow_mem huH n
  exact ⟨f s, hfH, rfl⟩

theorem derivativeAnnihilatesLogarithm : DerivativeAnnihilatesLogarithm := by
  intro p _ B V _ _ _ _ _ H hH X f d hd hf hX hex
  let u : ℚ_[p] →L[ℚ_[p]] B := (1 : ℚ_[p] →L[ℚ_[p]] ℚ_[p]).smulRight X
  have he : HasStrictFDerivAt (exp : B → B) (1 : B →L[ℚ_[p]] B) (u 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_exp_zero_of_radius_pos (exp_radius_pos p)
  have heval : exp (u 0) = 1 := by rw [map_zero, exp_zero]
  have hd' : HasFDerivAt f d (exp (u 0)) := heval ▸ hd
  have hg : HasDerivAt (fun t => f (exp (t • X))) (d X) (0 : ℚ_[p]) := by
    simpa [u, Function.comp_def] using ((hd'.comp (u 0) he.hasFDerivAt).comp 0 u.hasFDerivAt).hasDerivAt
  have hsmall : ∀ᶠ t : ℚ_[p] in 𝓝 0, ‖t‖ < 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by simp)
  have hz : (fun t : ℚ_[p] => f (exp (t • X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hsmall] with t ht
    obtain ⟨g, hg, hgt⟩ := ambientPadicIntegerLines p B H hH X hX hex ⟨t, ht.le⟩
    exact hgt ▸ hf ⟨g, hg⟩
  exact hg.unique ((hasDerivAt_const (x := (0 : ℚ_[p])) (0 : V)).congr_of_eventuallyEq hz)

section Logarithm

variable {B : Type*} [NormedRing B] [NormedAlgebra ℚ_[p] B] [CompleteSpace B]

private theorem arithmetic_logarithm_limit (u : B) (hu : ‖u‖ < ‖(p : ℚ_[p])‖) :
    Tendsto (fun n : ℕ => ((p : ℚ_[p]) ^ n)⁻¹ • ((u + 1) ^ (p ^ n) - 1))
      atTop (𝓝 (log (u + 1))) := by
  let b (n : ℕ) : ℤ_[p] := (p : ℤ_[p]) ^ n - 1
  let a (k : ℕ) : B := ((k + 1 : ℚ_[p])⁻¹) • u ^ (k + 1)
  let q : ℝ := p * ‖u‖
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg (mul_nonneg hpR.le (norm_nonneg u))]
    rw [Padic.norm_p] at hu
    exact (mul_lt_mul_of_pos_left hu hpR).trans_eq (mul_inv_cancel₀ hpR.ne')
  have hbound (k : ℕ) : ‖a k‖ ≤ q ^ (k + 1) := by
    have hk : padicValNat p (k + 1) ≤ k + 1 :=
      (Nat.le_mul_of_pos_left _ hp.out.pos).trans mul_padicValNat_le
    change ‖((k + 1 : ℚ_[p])⁻¹) • u ^ (k + 1)‖ ≤ _
    rw [← Nat.cast_succ (R := ℚ_[p])]
    exact (norm_smul_le _ _).trans
      ((mul_le_mul (norm_inv_natCast p _ _ (Nat.succ_ne_zero k) hk)
        (norm_pow_le' u (Nat.succ_pos k)) (norm_nonneg _) (by positivity)).trans_eq (mul_pow _ _ _).symm)
  have hsum : Summable (fun k : ℕ => q ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_norm_lt_one hq)
  have hb : Tendsto b atTop (𝓝 (-1)) := by
    have ha : Tendsto (fun n : ℕ => (p : ℤ_[p]) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
        simpa only [← PadicInt.norm_coe, PadicInt.coe_natCast] using norm_p_lt_one p)
    simpa only [zero_sub] using ha.sub tendsto_const_nhds
  let f (n k : ℕ) : B := ((mahler k (b n) : ℤ_[p]) : ℚ_[p]) • a k
  let g (k : ℕ) : B := (-1 : ℚ_[p]) ^ k • a k
  have hg (k : ℕ) : mahler k (-1 : ℤ_[p]) = (-1 : ℤ_[p]) ^ k := by
    rw [mahler_apply, Ring.choose_neg', Ring.multichoose_one]
    change ((↑((↑k : ℤ).negOnePow) : ℤ) • (1 : ℤ_[p])) = _
    rw [zsmul_one, Int.cast_negOnePow_natCast]
  have ht (k : ℕ) : Tendsto (fun n => f n k) atTop (𝓝 (g k)) := by
    have h : Tendsto (fun n => mahler k (b n)) atTop
        (𝓝 (mahler k (-1))) :=
      (mahler k).continuous.continuousAt.tendsto.comp hb
    rw [hg] at h
    have h' : Tendsto (fun n : ℕ => ((mahler k (b n) : ℤ_[p]) : ℚ_[p])) atTop
        (𝓝 ((-1 : ℚ_[p]) ^ k)) := by
      let v : ℤ_[p] → ℚ_[p] := fun g => (g : ℚ_[p])
      have hc : Continuous v := continuous_subtype_val
      have hf := (hc.tendsto _).comp h
      change Tendsto (fun n : ℕ => v (mahler k (b n))) atTop (𝓝 (v ((-1 : ℤ_[p]) ^ k))) at hf
      simpa only [v, PadicInt.coe_pow, PadicInt.coe_neg, PadicInt.coe_one] using hf
    exact h'.smul (tendsto_const_nhds (x := a k))
  have hfn (n k : ℕ) : ‖f n k‖ ≤ q ^ (k + 1) :=
    (norm_smul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      (by rw [PadicInt.norm_coe]; exact PadicInt.norm_le_one _)).trans (hbound k))
  have hT : Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, g k)) :=
    tendsto_tsum_of_dominated_convergence hsum ht (.of_forall hfn)
  have hG : (∑' k, g k) = log (u + 1) := by
    simp only [NormedSpace.log_eq_tsum ℚ_[p], add_sub_cancel_right]
    let z (n : ℕ) : B := ((-1) ^ (n + 1) / n : ℚ_[p]) • u ^ n
    have hz (k : ℕ) : z (k+1) = g k := by
      change ((-1) ^ ((k+1)+1) / (↑(k+1) : ℚ_[p])) • u ^ (k+1) = (-1 : ℚ_[p]) ^ k • a k
      simp only [a, Nat.cast_succ, div_eq_mul_inv, smul_smul]
      rw [show k + 1 + 1 = k + 2 by omega, pow_add, neg_one_sq, mul_one]
    have hgs : Summable g := (hsum.of_norm_bounded (fun k => by
      simpa [g, norm_smul] using hbound k))
    have hzs : Summable z := (summable_nat_add_iff 1).mp (hgs.congr fun k => (hz k).symm)
    change (∑' k, g k) = ∑' n, z n
    rw [hzs.tsum_eq_zero_add]
    simp only [z, Nat.cast_zero, div_zero, zero_smul, zero_add]
    exact tsum_congr fun k => (hz k).symm
  have hF (n : ℕ) :
      (∑' k, f n k) = ((p : ℚ_[p]) ^ n)⁻¹ • ((u + 1) ^ (p ^ n) - 1) := by
    let N := p ^ n
    have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n hp.out.ne_zero)
    have hb' : b n = ((N - 1 : ℕ) : ℤ_[p]) := by
      simp only [b, N, Nat.cast_sub hN, Nat.cast_pow, Nat.cast_one]
    have hf (k : ℕ) : f n k = ((N : ℚ_[p])⁻¹ * (N.choose (k+1) : ℚ_[p])) • u ^ (k+1) := by
      simp only [f, hb', mahler_natCast_eq, PadicInt.coe_natCast, a, smul_smul]
      congr 1
      have hn : N * (N - 1).choose k = N.choose (k + 1) * (k + 1) := by
        have h := Nat.add_one_mul_choose_eq (N - 1) k
        rwa [Nat.sub_add_cancel hN] at h
      have hn' : (N : ℚ_[p]) * ((N - 1).choose k : ℚ_[p]) =
          (N.choose (k+1) : ℚ_[p]) * (k+1 : ℚ_[p]) := by exact_mod_cast hn
      have hN' : (N : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hN)
      have hk' : (k+1 : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
      field_simp
      simpa [mul_comm, mul_left_comm] using hn'
    have hs : (∑' k, f n k) = ∑ k ∈ Finset.range N, f n k := by
      apply tsum_eq_sum
      intro k hk
      rw [hf, Nat.choose_eq_zero_of_lt (by simpa [Finset.mem_range] using hk), Nat.cast_zero,
        mul_zero, zero_smul]
    rw [hs, show (p : ℚ_[p]) ^ n = (N : ℚ_[p]) from (Nat.cast_pow p n).symm,
      (Commute.one_right u).add_pow, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
      add_sub_cancel_right, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hf, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul']
  simpa only [hF, hG] using hT

private theorem ambient_exp_nat_smul {X : B}
    (hX : X ∈ Metric.eball 0 (expSeries ℚ_[p] B).radius) (n : ℕ) :
    exp ((n : ℚ_[p]) • X) = exp X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_smul, one_smul,
      exp_add_of_commute_of_mem_ball ((Commute.refl X).smul_left _)
        (smul_mem_expBall hX _ (norm_natCast_le_one n)) hX, ih, pow_succ]

theorem logarithmExponentialGerm : LogarithmExponentialGerm := by
  intro p _ B _ _ _
  have hconv : ∀ᶠ X : B in 𝓝 0, X ∈ Metric.eball 0 (expSeries ℚ_[p] B).radius :=
    Metric.eball_mem_nhds _ (exp_radius_pos p)
  have he : HasStrictFDerivAt (exp : B → B) (1 : B →L[ℚ_[p]] B) 0 :=
    hasStrictFDerivAt_exp_zero_of_radius_pos (exp_radius_pos p)
  have hsmall : ∀ᶠ X : B in 𝓝 0, ‖exp X - 1‖ < ‖(p : ℚ_[p])‖ :=
    (he.continuousAt.sub continuousAt_const).norm.eventually_lt
      continuousAt_const (by simpa [exp_zero] using norm_p_pos p)
  filter_upwards [hconv, hsmall] with X hX hsmall
  have hlog := arithmetic_logarithm_limit p (exp X - 1) hsmall
  simp only [sub_add_cancel] at hlog
  let a : ℚ_[p] →L[ℚ_[p]] B := (1 : ℚ_[p] →L[ℚ_[p]] ℚ_[p]).smulRight X
  have ha : HasFDerivAt (exp : B → B) (1 : B →L[ℚ_[p]] B) (a 0) := by
    rw [map_zero]
    exact he.hasFDerivAt
  have hd : HasDerivAt (fun t : ℚ_[p] => exp (t • X)) X 0 := by
    simpa [a, Function.comp_def] using (ha.comp 0 a.hasFDerivAt).hasDerivAt
  have hn : Tendsto (fun n : ℕ => (p : ℚ_[p]) ^ n) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (norm_p_lt_one p),
      .of_forall fun n => pow_ne_zero _ (norm_pos_iff.mp (norm_p_pos p))⟩
  have hXlim := hd.tendsto_slope_zero.comp hn
  simp only [zero_add, zero_smul, exp_zero] at hXlim
  have hpEq (n : ℕ) : exp ((p : ℚ_[p]) ^ n • X) = exp X ^ (p ^ n) := by
    rw [← Nat.cast_pow]
    exact ambient_exp_nat_smul p hX _
  change Tendsto (fun n : ℕ => ((p : ℚ_[p]) ^ n)⁻¹ • (exp ((p : ℚ_[p]) ^ n • X) - 1))
    atTop (𝓝 X) at hXlim
  simp only [hpEq] at hXlim
  exact tendsto_nhds_unique hlog hXlim

end Logarithm

theorem restrictExponentialChart : RestrictExponentialChart := by
  intro p _ B E J _ _ _ _ _ _ _ _ m j hm hj h
  classical
  obtain ⟨e₀, h₀, he₀, _⟩ := ambientExponentialChart p B
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.nhds_basis_ball.eventually_iff.mp h
  let e := e₀.restr (Metric.ball 0 r₀)
  have heSource : e.source = e₀.source ∩ Metric.ball 0 r₀ :=
    e₀.restr_source' _ Metric.isOpen_ball
  have he (w : B) : e w = exp w := congrFun he₀ w
  have heInj (w : B) (hw : w ∈ e.source) :
      exp w ∈ Set.range (fun g : J => (m g : B)) ↔ w ∈ Set.range j :=
    hr₀sub (by rw [heSource] at hw; exact hw.2)
  have heZero : 0 ∈ e.source := by
    rw [heSource]
    exact ⟨h₀, Metric.mem_ball_self hr₀⟩
  obtain ⟨l, hl⟩ := j.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  let P := l.toContinuousLinearMap
  have hP (x : E) : P (j x) = x := LinearMap.congr_fun hl x
  have hjlim : Tendsto j (𝓝 0) (𝓝 0) := by
    rw [← j.map_zero]
    exact j.continuous.continuousAt
  have hsmall : ∀ᶠ x : E in 𝓝 0, j x ∈ e.source ∧
      j x ∈ Metric.eball 0 (expSeries ℚ_[p] B).radius ∧ log (exp (j x)) = j x :=
    (hjlim.eventually_mem (e.open_source.mem_nhds heZero)).and
      ((hjlim.eventually_mem (Metric.eball_mem_nhds (0 : B) (exp_radius_pos p))).and
        (hjlim.eventually (logarithmExponentialGerm p B)))
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_ball.eventually_iff.mp hsmall
  let S := Metric.ball (0 : E) r
  let v : J → B := fun g => (m g : B)
  let w : B → E := fun b => P (e.symm b)
  let T := v ⁻¹' (e.target ∩ w ⁻¹' S)
  have hw : ContinuousOn w e.target := P.continuous.comp_continuousOn e.continuousOn_symm
  have hT : IsOpen T :=
    (hw.isOpen_inter_preimage e.open_target Metric.isOpen_ball).preimage hm.continuous
  have hex (x : E) (hx : x ∈ S) : exp (j x) ∈ Set.range v :=
    (heInj _ (hrsub hx).1).mpr ⟨x, rfl⟩
  let toPoint (x : E) : J := if hx : x ∈ S then (hex x hx).choose else 1
  have hpoint (x : E) (hx : x ∈ S) : v (toPoint x) = exp (j x) := by
    change v (if hx : x ∈ S then (hex x hx).choose else 1) = _
    rw [dite_eq_left hx]
    exact (hex x hx).choose_spec
  let toTangent (g : J) : E := w (v g)
  have hto (x : E) (hx : x ∈ S) : toPoint x ∈ T := by
    change v (toPoint x) ∈ e.target ∩ w ⁻¹' S
    rw [hpoint x hx, ← he]
    refine ⟨e.map_source (hrsub hx).1, ?_⟩
    change P (e.symm (e (j x))) ∈ S
    rwa [e.left_inv (hrsub hx).1, hP]
  have hright (g : J) (hg : g ∈ T) : j (toTangent g) = e.symm (v g) := by
    have hsource := e.map_target hg.1
    have hmem : exp (e.symm (v g)) ∈ Set.range v := by
      rw [← he, e.right_inv hg.1]
      exact ⟨g, rfl⟩
    obtain ⟨x, hx⟩ := (heInj _ hsource).mp hmem
    change j (P (e.symm (v g))) = e.symm (v g)
    rw [← hx, hP]
  let c : OpenPartialHomeomorph E J :=
    { toFun := toPoint
      invFun := toTangent
      source := S
      target := T
      map_source' := hto
      map_target' := fun _ hg => hg.2
      left_inv' := fun _ hx => by
        change P (e.symm (v (toPoint _))) = _
        rw [hpoint _ hx, ← he, e.left_inv (hrsub hx).1, hP]
      right_inv' := fun g hg => by
        apply hm.injective
        change v (toPoint (toTangent g)) = v g
        rw [hpoint _ hg.2, hright _ hg, ← he, e.right_inv hg.1]
      continuousOn_toFun := by
        apply hm.isInducing.continuousOn_iff.mpr
        exact ((e.continuousOn.comp j.continuous.continuousOn
          (fun x hx => (hrsub hx).1))).congr (fun x hx => (hpoint x hx).trans (he _).symm)
      continuousOn_invFun := hw.comp hm.continuous.continuousOn (fun _ hg => hg.1)
      open_source := Metric.isOpen_ball
      open_target := hT }
  have hc₀ : c 0 = 1 := by
    apply hm.injective
    change v (toPoint 0) = v 1
    rw [hpoint 0 (Metric.mem_ball_self hr), map_zero, exp_zero]
    simp [v]
  refine ⟨⟨c, r, hr, rfl, hc₀, hpoint, fun x hx => (hrsub hx).2.1, ?_⟩⟩
  intro g hg
  have hsource : c.symm g ∈ S := hg.2
  have hlog := (hrsub hsource).2.2
  change j (c.symm g) = log (v g)
  rw [← hlog, ← hpoint _ hsource]
  change log (v (c (c.symm g))) = log (v g)
  rw [c.right_inv hg]

theorem chartConjugationDerivative : ChartConjugationDerivative := by
  intro p _ B E J _ _ _ _ _ _ _ m j c Y
  have h := conjugationDerivative p B Y
  let d := ContinuousLinearMap.mulLeftRight ℚ_[p] B 1 Y -
    ContinuousLinearMap.mulLeftRight ℚ_[p] B Y 1
  have h' : HasStrictFDerivAt (fun x : B => exp x * Y * exp (-x)) d (j 0) := by
    rw [map_zero]
    exact h
  refine (h'.comp 0 j.hasStrictFDerivAt).congr_of_eventuallyEq ?_
  filter_upwards [c.chart.open_source.mem_nhds (zero_mem_source c)] with x hx
  rw [c.matrix_exp _ hx]
  have hinv : exp (-j x) * (m (c.chart x) : B) = 1 := by
    have hneg : -j x ∈ Metric.eball 0 (expSeries ℚ_[p] B).radius := by
      simpa only [Metric.mem_eball, edist_zero_right, enorm_neg] using c.converges x hx
    rw [c.matrix_exp _ hx, ← exp_add_of_commute_of_mem_ball (Commute.refl (j x)).neg_left
      hneg (c.converges x hx), neg_add_cancel, exp_zero]
  rw [show exp (-j x) = (↑((m (c.chart x))⁻¹) : B) from
    (Units.mul_left_inj (m (c.chart x))).mp (hinv.trans (Units.inv_mul _).symm)]

theorem differentiatedInvariance : DifferentiatedInvariance := by
  intro p _ B E J _ _ _ _ _ _ _ m j c W hW h x Y hY
  let f (v : E) := (m (c.chart v) : B) * Y * (↑((m (c.chart v))⁻¹) : B)
  let u : ℚ_[p] →L[ℚ_[p]] E := (1 : ℚ_[p] →L[ℚ_[p]] ℚ_[p]).smulRight x
  have hu₀ : u 0 = 0 := map_zero u
  let d := ContinuousLinearMap.mulLeftRight ℚ_[p] B 1 Y -
    ContinuousLinearMap.mulLeftRight ℚ_[p] B Y 1
  have hd : HasFDerivAt f (d.comp j) (u 0) := by
    rw [hu₀]
    exact (chartConjugationDerivative p B E J c Y).hasFDerivAt
  have hd' : HasDerivAt (f ∘ u) (j x * Y - Y * j x) 0 := by
    have hv := (hd.comp (0 : ℚ_[p]) u.hasFDerivAt).hasDerivAt
    simpa [u, d, sub_eq_add_neg] using hv
  have hf₀ : (f ∘ u) 0 = Y := by simp [f, hu₀, c.at_zero]
  apply hW.mem_of_tendsto hd'.tendsto_slope_zero
  exact Filter.Eventually.of_forall fun t => by
    simp only [zero_add, hf₀]
    exact W.smul_mem _ (W.sub_mem (h _ Y hY) hY)


theorem polynomialDerivative : PolynomialDerivative := by
  intro k F I _ _ _ _ P x
  let evalDual (v : I → F) := polynomialDualEvaluation x v
  have evalX (v : I → F) (i : I) :
      evalDual v (MvPolynomial.X i) = ((x i, v i) : DualNumber F) :=
    MvPolynomial.aeval_X (R := F) (S₁ := DualNumber F) _ _
  have hfst (Q : MvPolynomial I F) (v : I → F) :
      (evalDual v Q).fst = MvPolynomial.aeval x Q := by
    have hEval : (TrivSqZeroExt.fstHom F F F).comp (evalDual v) = MvPolynomial.aeval x := by
      apply MvPolynomial.algHom_ext
      intro i
      change (evalDual v (MvPolynomial.X i)).fst = MvPolynomial.aeval x (MvPolynomial.X i)
      rw [evalX, MvPolynomial.aeval_X]
      rfl
    exact congrArg (fun f : MvPolynomial I F →ₐ[F] F => f Q) hEval
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_, ?_⟩
    · simpa using (hasStrictFDerivAt_const (𝕜 := k) a x)
    · intro v
      change (evalDual v (MvPolynomial.C a)).snd = 0
      have hc : evalDual v (MvPolynomial.C a) = algebraMap F (DualNumber F) a :=
        (evalDual v).commutes a
      rw [hc, TrivSqZeroExt.algebraMap_eq_inl']
      rfl
  | add P Q hP hQ =>
    obtain ⟨d, hd, hdv⟩ := hP
    obtain ⟨e, he, hev⟩ := hQ
    refine ⟨d + e, (hd.add he).congr_of_eventuallyEq (.of_forall fun y => ?_), ?_⟩
    · change MvPolynomial.aeval y P + MvPolynomial.aeval y Q = MvPolynomial.aeval y (P + Q)
      exact (map_add (MvPolynomial.aeval y) P Q).symm
    · intro v
      change (evalDual v (P + Q)).snd = d v + e v
      have hdv' : (evalDual v P).snd = d v := hdv v
      have hev' : (evalDual v Q).snd = e v := hev v
      rw [map_add, TrivSqZeroExt.snd_add, hdv', hev']
  | mul_X Q i hQ =>
    obtain ⟨d, hd, hdv⟩ := hQ
    let proj : (I → F) →L[k] F := ContinuousLinearMap.proj i
    refine ⟨(MvPolynomial.aeval x Q) • proj + x i • d,
      (hd.mul proj.hasStrictFDerivAt).congr_of_eventuallyEq (.of_forall fun y => ?_), ?_⟩
    · change MvPolynomial.aeval y Q * y i = MvPolynomial.aeval y (Q * MvPolynomial.X i)
      rw [map_mul, MvPolynomial.aeval_X]
    · intro v
      change (evalDual v (Q * MvPolynomial.X i)).snd =
        (MvPolynomial.aeval x Q) * v i + x i * d v
      have hdv' : (evalDual v Q).snd = d v := hdv v
      rw [map_mul, evalX]
      change (evalDual v Q).fst * v i + (evalDual v Q).snd * x i = _
      rw [hfst, hdv', mul_comm (d v)]

section Scheme

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs Arithmetic.AdelicGroups
  LinearAlgebraicGroups.Specs.IntegralModels InfinitesimalCommutator
open private matrixDifferentialLinear matrixDual matrixDual_kernel matrixPointMap
  from LinearAlgebraicGroups.Affine.LieBracket
open private matrixEvaluation glEvaluation glEvaluation_entry glCoordinates_ext
  isUnit_matrixEvaluation_det from LinearAlgebraicGroups.Affine.StandardGroups

universe u

set_option backward.isDefEq.respectTransparency false in
theorem matrixLieComparison : MatrixLieComparison.{u} := by
  intro k _ G i s
  haveI : IsAffine G.val.X.left := G.prop.1
  haveI : IsAffine i.ambient.val.X.left := i.ambient.prop.1
  let j₀ := matrixDifferentialLinear i.embedding i.matrix
  have hAdd (X Y : Specs.Lie k G.val) :
      matrixDifferential i.embedding i.matrix (X + Y) =
        matrixDifferential i.embedding i.matrix X + matrixDifferential i.embedding i.matrix Y :=
    j₀.map_add X Y
  have hSmul (a : k) (X : Specs.Lie k G.val) :
      matrixDifferential i.embedding i.matrix (a • X) =
        a • matrixDifferential i.embedding i.matrix X :=
    j₀.map_smul a X
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommMonoid (Specs.Lie k G.val) := s.lieRing.toAddCommGroup.toAddCommMonoid
  letI : Module k (Specs.Lie k G.val) := s.lieAlgebra.toModule
  let B := Matrix (Unipotent.Index.{u} i.size) (Unipotent.Index.{u} i.size) k
  let j : @LinearMap k k _ _ (RingHom.id k) (Specs.Lie k G.val) B
      s.lieRing.toAddCommGroup.toAddCommMonoid _ s.lieAlgebra.toModule _ :=
    { toFun := matrixDifferential i.embedding i.matrix
      map_add' := fun X Y => by
        have h := congrArg (fun g : AddGroup (PointKernel G.val) => g.toAdd.add X Y) s.group_law
        exact (congrArg _ h).trans (hAdd X Y)
      map_smul' := fun a X => by
        have h := congrFun (congrFun s.scalar_law a) X
        exact (congrArg _ h).trans (hSmul a X) }
  obtain ⟨hi, hb⟩ := identityLieBracketMatrix k G.val i.ambient.val _
    i.embedding i.matrix i.closed
  refine ⟨j, hi, fun _ => rfl, ?_, hb s⟩
  intro g Y
  let R := CommAlgCat.of k k
  let F := (groupPointsFunctor k).obj G.val
  let η := matrixPointMap i.embedding i.matrix
  let b : Matrix.GeneralLinearGroup (Unipotent.Index.{u} i.size) k →*
      Matrix.GeneralLinearGroup (Unipotent.Index.{u} i.size) (DualNumber k) :=
    Matrix.GeneralLinearGroup.map (AdjointRepresentation.constants R).hom.toRingHom
  let a : PointsIn i (DualNumber k) := (F.map (AdjointRepresentation.constants R)).hom g
  let y : PointsIn i (DualNumber k) := Y.toMul.val
  have ha : asMatrix i (DualNumber k) a = b (asMatrix i k g) := by
    have h := congrArg (fun z => z.hom g) (η.naturality (AdjointRepresentation.constants R))
    simp only [GrpCat.hom_comp] at h
    exact h
  have hc (M : Matrix.GeneralLinearGroup (Unipotent.Index.{u} i.size) k) :
      matrixDual (b M).val = (M.val, 0) := rfl
  change (matrixDual (asMatrix i (DualNumber k) (a * y * a⁻¹)).val).snd =
    (asMatrix i k g).val * j Y * (asMatrix i k g)⁻¹.val
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, map_mul, map_mul,
    ha, ← map_inv b, hc, hc]
  have hY := matrixDual_kernel (mapDualKernel η Y)
  change matrixDual (asMatrix i (DualNumber k) y).val = (1, j Y) at hY
  rw [hY]
  simp [TrivSqZeroExt.fst_mul]

open Opposite
open Specs.StandardGroups (GLCoordinates genericDeterminant universalMatrix)
open Specs.Unipotent (Index)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} (i : MatrixRealization G)

private abbrev MatrixPolynomial (k : Type u) [CommSemiring k] (n : ℕ) :=
  MvPolynomial (Index.{u} n × Index.{u} n) k

private def VanishesOnPoints (P : MatrixPolynomial k i.size) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] (g : PointsIn i R),
    matrixEvaluation (asMatrix i R g).val P = 0

open WithConv
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent
open private evaluatedGeneralLinear from LinearAlgebraicGroups.Affine.StandardGroups

set_option backward.isDefEq.respectTransparency false in
private theorem matrix_mem_range_iff {R : Type u} [CommRing R] [Algebra k R]
    (M : Matrix.GeneralLinearGroup (Index.{u} i.size) R) :
    M ∈ Set.range (asMatrix i R) ↔
      ∀ P, VanishesOnPoints i P → matrixEvaluation M.val P = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ P hP
    exact hP R g
  · intro h
    let ι := Index.{u} i.size
    letI := _root_.LinearAlgebraicGroups.StandardGroups.generalLinearHopf k ι
    let C := CommHopfAlgCat.of k (GLCoordinates k ι)
    let F := hopfSpec (CommRingCat.of k)
    let U := groupPointsFunctor k
    let standard := _root_.LinearAlgebraicGroups.StandardGroups.generalLinearGroup k ι
    let m := _root_.LinearAlgebraicGroups.StandardGroups.generalLinearGroupPointsIso k ι
    obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_hopfSpec.mpr G.prop.1
    letI : IsAffine i.ambient.val.X.left := i.ambient.prop.1
    letI : IsAffine standard.val.X.left := standard.prop.1
    let b : i.ambient.val ≅ standard.val := groupIsoOfPointIso (i.matrix ≪≫ m.symm)
    have hb : U.map b.hom = (i.matrix ≪≫ m.symm).hom :=
      (groupHomEquiv i.ambient.val standard.val i.ambient.prop.1).apply_symm_apply _
    let j : F.obj A ⟶ F.obj (op C) := e.hom ≫ i.embedding ≫ b.hom
    let a : C ⟶ A.unop := ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage j).unop
    have ha : F.map a.op = j := (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage j
    have hs : Function.Surjective a.hom := by
      let f := Grp.forget (SchemeOver k) ⋙ Over.forget _
      haveI : IsIso (f.map e.hom) := inferInstance
      haveI : IsIso (f.map b.hom) := inferInstance
      letI := i.closed
      apply (hopfMapClosedImmersion k a).mp
      change IsClosedImmersion (f.map (F.map a.op))
      rw [ha]
      change IsClosedImmersion (f.map e.hom ≫ i.embedding.hom.hom.left ≫ f.map b.hom)
      infer_instance
    obtain ⟨q, hq, hqmap⟩ := hopfSpecPoints k
    have hq' (B : HopfAlgebraCategory k) (S : TestAlgebra k) (v : WithConv (B →ₐ[k] S)) :
        (q B).hom.app S v = (hopfSpecPointIso B).hom.app S v := by
      apply Over.OverMorphism.ext
      exact hq B S v
    let point (S : Type u) [CommRing S] [Algebra k S] (v : A.unop →ₐ[k] S) : PointsIn i S :=
      (U.mapIso e).hom.app (CommAlgCat.of k S) ((q A.unop).hom.app _ (toConv v))
    have hpoint (S : Type u) [CommRing S] [Algebra k S] (v : A.unop →ₐ[k] S) :
        asMatrix i S (point S v) = evaluatedGeneralLinear (v.comp a.hom.toAlgHom) := by
      let V := CommAlgCat.of k S
      have hj := hqmap a V (toConv v)
      rw [ha] at hj
      change (q C).hom.app V (toConv (v.comp a.hom.toAlgHom)) =
        (U.map (e.hom ≫ i.embedding ≫ b.hom)).app V ((q A.unop).hom.app V (toConv v)) at hj
      rw [Functor.map_comp, Functor.map_comp, NatTrans.comp_app,
        NatTrans.comp_app, GrpCat.comp_apply, GrpCat.comp_apply, hb] at hj
      have hj' := congrArg (fun x => m.hom.app V x) hj
      rw [hq' C] at hj'
      change evaluatedGeneralLinear
          (((hopfSpecPointIso C).inv.app V ((hopfSpecPointIso C).hom.app V
            (toConv (v.comp a.hom.toAlgHom)))).ofConv) =
        m.hom.app V (m.inv.app V (asMatrix i S (point S v))) at hj'
      have hleft : (hopfSpecPointIso C).inv.app V
          ((hopfSpecPointIso C).hom.app V (toConv (v.comp a.hom.toAlgHom))) =
          toConv (v.comp a.hom.toAlgHom) :=
        GrpCat.inv_hom_apply ((hopfSpecPointIso C).app V) _
      have hright : m.hom.app V (m.inv.app V (asMatrix i S (point S v))) =
          asMatrix i S (point S v) := GrpCat.hom_inv_apply (m.app V) _
      rw [hleft, hright] at hj'
      exact hj'.symm
    have hgen (S : Type u) [CommRing S] [Algebra k S] (v : A.unop →ₐ[k] S) :
        glEvaluation (asMatrix i S (point S v)) = v.comp a.hom.toAlgHom := by
      rw [hpoint]
      apply glCoordinates_ext
      intro l n
      rw [glEvaluation_entry]
      rfl
    have hker : RingHom.ker a.hom.toAlgHom.toRingHom ≤
        RingHom.ker (glEvaluation (k := k) M).toRingHom := by
      intro c hc
      obtain ⟨n, P, hP⟩ := IsLocalization.Away.surj (genericDeterminant k ι) c
      have hzero : a.hom (algebraMap (MatrixPolynomial k i.size) (GLCoordinates k ι) P) = 0 := by
        have hc' : a.hom c = 0 := RingHom.mem_ker.mp hc
        rw [← hP, map_mul, hc', zero_mul]
      have hvan : VanishesOnPoints i P := by
        intro S _ _ g
        let V := CommAlgCat.of k S
        let eP := (q A.unop ≪≫ U.mapIso e).app V
        let v : A.unop →ₐ[k] S := (eP.inv g).ofConv
        have hg : point S v = g := GrpCat.hom_inv_apply eP g
        have heval := congrArg (fun f : GLCoordinates k ι →ₐ[k] S =>
          f (algebraMap (MatrixPolynomial k i.size) (GLCoordinates k ι) P)) (hgen S v)
        rw [hg] at heval
        change glEvaluation (asMatrix i S g) _ = v (a.hom (algebraMap _ _ P)) at heval
        rw [hzero, map_zero] at heval
        exact (IsLocalization.Away.lift_eq (S := GLCoordinates k ι) (genericDeterminant k ι)
          (g := (matrixEvaluation (asMatrix i S g).val).toRingHom)
          (isUnit_matrixEvaluation_det (asMatrix i S g)) P).symm.trans heval
      have hmul := congrArg (glEvaluation (k := k) M) hP
      rw [map_mul, map_pow] at hmul
      have hp : glEvaluation M (algebraMap (MatrixPolynomial k i.size) (GLCoordinates k ι) P) =
          matrixEvaluation M.val P :=
        IsLocalization.Away.lift_eq (S := GLCoordinates k ι) (genericDeterminant k ι)
          (g := (matrixEvaluation M.val).toRingHom) (isUnit_matrixEvaluation_det M) P
      rw [hp, h P hvan] at hmul
      have hunit : IsUnit ((glEvaluation (k := k) M)
          (algebraMap (MatrixPolynomial k i.size) (GLCoordinates k ι)
            (genericDeterminant k ι))) :=
        (IsLocalization.Away.algebraMap_isUnit (S := GLCoordinates k ι)
          (genericDeterminant k ι)).map (glEvaluation (k := k) M).toRingHom
      exact (hunit.pow n).mul_left_inj.mp (hmul.trans (zero_mul _).symm)
    let f := a.hom.toAlgHom.liftOfSurjective hs (glEvaluation (k := k) M) hker
    have hf := hgen R f
    rw [AlgHom.liftOfSurjective_comp] at hf
    refine ⟨point R f, Matrix.GeneralLinearGroup.ext fun l n => ?_⟩
    have h := congrArg (fun f : GLCoordinates k ι →ₐ[k] R => f (universalMatrix k ι l n)) hf
    exact (glEvaluation_entry (k := k) (asMatrix i R (point R f)) l n).symm.trans
      (h.trans (glEvaluation_entry (k := k) M l n))

set_option backward.isDefEq.respectTransparency false in
private theorem asMatrix_injective (R : Type u) [CommRing R] [Algebra k R] :
    Function.Injective (asMatrix i R) := by
  intro g h he
  let V := CommAlgCat.of k R
  have h' : g ≫ i.embedding.hom.hom = h ≫ i.embedding.hom.hom :=
    (i.matrix.app V).groupIsoToMulEquiv.injective he
  letI := i.closed
  apply Over.OverMorphism.ext
  exact (cancel_mono i.embedding.hom.hom.left).mp
    (congrArg (fun x : Points i.ambient.val.X V => x.left) h')

set_option backward.isDefEq.respectTransparency false in
private theorem asMatrix_naturality {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (g : PointsIn i R) :
    asMatrix i S ((((groupPointsFunctor k).obj G.val).map (CommAlgCat.ofHom f)).hom g) =
      Matrix.GeneralLinearGroup.map f.toRingHom (asMatrix i R g) := by
  have h := congrArg (fun z => z.hom g)
    ((matrixPointMap i.embedding i.matrix).naturality (CommAlgCat.ofHom f))
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at h
  exact h

private theorem matrixDual_tangent (Y : Specs.Lie k G.val) :
    matrixDual (asMatrix i (DualNumber k) Y.toMul.val).val =
      (1, matrixDifferential i.embedding i.matrix Y) :=
  matrixDual_kernel (mapDualKernel (matrixPointMap i.embedding i.matrix) Y)

private theorem matrixDual_injective {R ι : Type u} [CommRing R] [Fintype ι] [DecidableEq ι] :
    Function.Injective (matrixDual (ι := ι) (R := R)) := by
  intro A B h
  apply Matrix.ext
  intro l n
  exact TrivSqZeroExt.ext
    (congrArg (fun z : DualNumber (Matrix ι ι R) => z.fst l n) h)
    (congrArg (fun z : DualNumber (Matrix ι ι R) => z.snd l n) h)

private def dualMatrixValue {R ι : Type u} [CommRing R]
    [Fintype ι] [DecidableEq ι] (X : Matrix ι ι R) : Matrix ι ι (DualNumber R) :=
  fun l n => ((1 : Matrix ι ι R) l n, X l n)

set_option backward.isDefEq.respectTransparency false in
private theorem dualMatrixValue_mul_neg {R ι : Type u} [CommRing R]
    [Fintype ι] [DecidableEq ι] (X : Matrix ι ι R) :
    dualMatrixValue X * dualMatrixValue (-X) = 1 := by
  apply matrixDual_injective
  calc
    _ = matrixDual (dualMatrixValue X) * matrixDual (dualMatrixValue (-X)) :=
      matrixDual.map_mul _ _
    _ = 1 := by
      apply TrivSqZeroExt.ext
      · change (1 : Matrix ι ι R) * 1 = 1
        exact mul_one _
      · change (1 : Matrix ι ι R) * (-X) + X * 1 = 0
        simp
    _ = matrixDual 1 := matrixDual.map_one.symm

private def dualMatrix {R : Type u} (ι : Type u) [Fintype ι] [DecidableEq ι]
    [CommRing R] (X : Matrix ι ι R) : Matrix.GeneralLinearGroup ι (DualNumber R) where
  val := dualMatrixValue X
  inv := dualMatrixValue (-X)
  val_inv := dualMatrixValue_mul_neg X
  inv_val := by simpa only [neg_neg] using dualMatrixValue_mul_neg (-X)

open Specs.StandardGroups (genericMatrix)
open scoped PowerSeries

private theorem matrixEvaluation_map {R S ι : Type u} [Fintype ι]
    [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) (M : Matrix ι ι R) :
    f.comp (matrixEvaluation M) = matrixEvaluation (M.map f) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp [matrixEvaluation]

private def coefficientChange {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) :
    DualNumber R →ₐ[k] DualNumber S where
  toRingHom := mapCoefficients f.toRingHom
  commutes' r := by
    apply TrivSqZeroExt.ext
    · exact f.commutes r
    · exact map_zero f

private def rightMatrixDerivative {ι : Type u} [Fintype ι]
    (X : Matrix ι ι k) (P : MvPolynomial (ι × ι) k) : MvPolynomial (ι × ι) k :=
  let M := genericMatrix k ι
  let V := M * X.map (MvPolynomial.C : k →+* MvPolynomial (ι × ι) k)
  (matrixEvaluation (R := DualNumber (MvPolynomial (ι × ι) k)) (fun l n => (M l n, V l n)) P).snd

private theorem rightMatrixDerivative_eval {R ι : Type u} [CommRing R] [Algebra k R] [Fintype ι]
    (X : Matrix ι ι k) (P : MvPolynomial (ι × ι) k) (M : Matrix ι ι R) :
    matrixEvaluation M (rightMatrixDerivative X P) =
      (matrixEvaluation (k := k) (R := DualNumber R)
        (fun l n => (M l n, (M * X.map (algebraMap k R)) l n)) P).snd := by
  let f := matrixEvaluation (k := k) M
  let U := genericMatrix k ι
  let V := U * X.map (MvPolynomial.C : k →+* MvPolynomial (ι × ι) k)
  have hfU : U.map f = M := by
    ext l n
    exact MvPolynomial.aeval_X _ (l, n)
  have hfX : (X.map (MvPolynomial.C : k →+* MvPolynomial (ι × ι) k)).map f =
      X.map (algebraMap k R) := by
    ext l n
    exact f.commutes (X l n)
  have hfV : V.map f = M * X.map (algebraMap k R) := by
    change (U * X.map (MvPolynomial.C : k →+* MvPolynomial (ι × ι) k)).map f.toRingHom = _
    rw [Matrix.map_mul, ← hfU, ← hfX]
    rfl
  let T : Matrix ι ι (DualNumber (MvPolynomial (ι × ι) k)) := fun l n => (U l n, V l n)
  have heq : T.map (coefficientChange f) =
      (fun l n => (M l n, (M * X.map (algebraMap k R)) l n)) := by
    apply Matrix.ext
    intro l n
    exact TrivSqZeroExt.ext (congrFun (congrFun hfU l) n) (congrFun (congrFun hfV l) n)
  have hh := matrixEvaluation_map (k := k) (coefficientChange f) T
  rw [heq] at hh
  exact congrArg (fun g : MvPolynomial (ι × ι) k →ₐ[k] DualNumber R => (g P).snd) hh

private theorem matrixDual_coefficientChange {R S ι : Type u} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix ι ι (DualNumber R)) :
    matrixDual (M.map (mapCoefficients f)) = mapCoefficients (f.mapMatrix) (matrixDual M) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem rightMatrixDerivative_vanishes (Y : Specs.Lie k G.val)
    (P : MatrixPolynomial k i.size) (hP : VanishesOnPoints i P) :
    VanishesOnPoints i (rightMatrixDerivative (matrixDifferential i.embedding i.matrix Y) P) := by
  intro R _ _ g
  let ι := Index.{u} i.size
  let F := (groupPointsFunctor k).obj G.val
  let b := coefficientChange (Algebra.ofId k R)
  let a := (TrivSqZeroExt.inlAlgHom R R R).restrictScalars k
  let g' : PointsIn i (DualNumber R) := (F.map (CommAlgCat.ofHom a)).hom g
  let y : PointsIn i (DualNumber k) := Y.toMul.val
  let Y' : PointsIn i (DualNumber R) := (F.map (CommAlgCat.ofHom b)).hom y
  let M := (asMatrix i R g).val
  let X := matrixDifferential i.embedding i.matrix Y
  have hg : matrixDual (asMatrix i (DualNumber R) g').val =
      ((M, 0) : DualNumber (Matrix ι ι R)) := by
    change matrixDual (asMatrix i (DualNumber R) ((F.map (CommAlgCat.ofHom a)).hom g)).val = _
    rw [asMatrix_naturality]
    rfl
  have hy : matrixDual (asMatrix i (DualNumber R) Y').val =
      ((1, X.map (algebraMap k R)) : DualNumber (Matrix ι ι R)) := by
    rw [show asMatrix i (DualNumber R) Y' = _ from asMatrix_naturality i b y]
    change matrixDual ((asMatrix i (DualNumber k) Y.toMul.val).val.map
      (mapCoefficients (algebraMap k R))) = _
    rw [matrixDual_coefficientChange, matrixDual_tangent]
    exact TrivSqZeroExt.ext ((algebraMap k R).mapMatrix.map_one) rfl
  have hprod : matrixDual (asMatrix i (DualNumber R) (g' * Y')).val =
      ((M, M * X.map (algebraMap k R)) : DualNumber (Matrix ι ι R)) := by
    rw [map_mul, Units.val_mul, map_mul, hg, hy]
    exact TrivSqZeroExt.ext (by simp) (by simp)
  have hmat : (asMatrix i (DualNumber R) (g' * Y')).val =
      (fun l n => (M l n, (M * X.map (algebraMap k R)) l n) : Matrix ι ι (DualNumber R)) := by
    apply Matrix.ext
    intro l n
    exact TrivSqZeroExt.ext
      (congrArg (fun z : DualNumber (Matrix ι ι R) => z.fst l n) hprod)
      (congrArg (fun z : DualNumber (Matrix ι ι R) => z.snd l n) hprod)
  have hz := hP (DualNumber R) (g' * Y')
  rw [hmat] at hz
  rw [rightMatrixDerivative_eval, hz]
  rfl

private def derivativeJet (k : Type u) [Field k] :
    k⟦X⟧ →ₐ[k] DualNumber k⟦X⟧ where
  toFun f := (f, PowerSeries.derivative f)
  map_zero' := TrivSqZeroExt.ext rfl (map_zero PowerSeries.derivative)
  map_one' := TrivSqZeroExt.ext rfl (Derivation.map_one_eq_zero _)
  map_add' f g := TrivSqZeroExt.ext rfl (map_add PowerSeries.derivative f g)
  map_mul' f g := TrivSqZeroExt.ext rfl (by
    change PowerSeries.derivative (f * g) =
      f * PowerSeries.derivative g + PowerSeries.derivative f * g
    simp [PowerSeries.derivative.leibniz, mul_comm g])
  commutes' r := TrivSqZeroExt.ext rfl (Derivation.map_algebraMap _ r)

private def formalMatrixExp {ι : Type u} [Fintype ι] [DecidableEq ι] [CharZero k]
    (X : Matrix ι ι k) : Matrix ι ι k⟦X⟧ :=
  fun l n => PowerSeries.mk (fun m => (((m ! : k)⁻¹) • X ^ m) l n)

private theorem formalMatrixExp_constant {ι : Type u} [Fintype ι] [DecidableEq ι] [CharZero k]
    (X : Matrix ι ι k) : (formalMatrixExp X).map
      (PowerSeries.constantCoeff (R := k)) = 1 := by
  ext l n
  change PowerSeries.constantCoeff (formalMatrixExp X l n) = (1 : Matrix ι ι k) l n
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, formalMatrixExp, PowerSeries.coeff_mk]
  simp

private theorem formalMatrixExp_derivative {ι : Type u} [Fintype ι] [DecidableEq ι] [CharZero k]
    (X : Matrix ι ι k) (l r : ι) :
    PowerSeries.derivative (formalMatrixExp X l r) =
      (formalMatrixExp X * X.map (algebraMap k k⟦X⟧)) l r := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp only [formalMatrixExp, PowerSeries.coeff_mk, Matrix.mul_apply, map_sum,
    Matrix.map_apply, PowerSeries.algebraMap_apply, PowerSeries.coeff_mul_C]
  change (((((n + 1) ! : k)⁻¹) • X ^ (n + 1)) l r) * (↑n + 1) =
    ∑ m, (((n ! : k)⁻¹) • X ^ n) l m * X m r
  rw [← Matrix.mul_apply, Matrix.smul_mul, ← pow_succ]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hn : (n : k) + 1 ≠ 0 := by
    exact_mod_cast n.succ_ne_zero
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_inv]
  calc
    _ = ((↑n + 1)⁻¹ * (↑n + 1)) * ((n ! : k)⁻¹ * (X ^ (n + 1)) l r) := by ac_rfl
    _ = _ := by rw [inv_mul_cancel₀ hn, one_mul]

private theorem formalMatrixExp_vanishes [CharZero k] (Y : Specs.Lie k G.val)
    (P : MatrixPolynomial k i.size) (hP : VanishesOnPoints i P) :
    matrixEvaluation (formalMatrixExp (matrixDifferential i.embedding i.matrix Y)) P = 0 := by
  let X := matrixDifferential i.embedding i.matrix Y
  let E := formalMatrixExp X
  have hder (Q : MatrixPolynomial k i.size) :
      PowerSeries.derivative (matrixEvaluation E Q) =
        matrixEvaluation E (rightMatrixDerivative X Q) := by
    rw [rightMatrixDerivative_eval]
    have h := matrixEvaluation_map (k := k) (derivativeJet k) E
    have heq : E.map (derivativeJet k) =
        (fun l n => (E l n, (E * X.map (algebraMap k k⟦X⟧)) l n) :
          Matrix (Index.{u} i.size) (Index.{u} i.size) (DualNumber k⟦X⟧)) := by
      apply Matrix.ext
      intro l n
      exact TrivSqZeroExt.ext rfl (formalMatrixExp_derivative X l n)
    rw [heq] at h
    exact congrArg (fun f => (f Q).snd) h
  have hz (n : ℕ) (Q : MatrixPolynomial k i.size) (hQ : VanishesOnPoints i Q) :
      PowerSeries.coeff n (matrixEvaluation E Q) = 0 := by
    induction n generalizing Q with
    | zero =>
      let e : k⟦X⟧ →ₐ[k] k :=
        { toRingHom := PowerSeries.constantCoeff
          commutes' r := PowerSeries.constantCoeff_C r }
      have he : E.map e = 1 := formalMatrixExp_constant X
      have hev := congrArg (fun f => f Q) (matrixEvaluation_map e E)
      rw [he] at hev
      change PowerSeries.constantCoeff (matrixEvaluation E Q) = _ at hev
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hev, ← Units.val_one,
        ← (asMatrix i k).map_one]
      exact hQ k 1
    | succ n ih =>
      have h := ih (rightMatrixDerivative X Q) (rightMatrixDerivative_vanishes i Y Q hQ)
      rw [← hder, PowerSeries.coeff_derivative] at h
      exact (mul_eq_zero.mp h).resolve_right (by exact_mod_cast n.succ_ne_zero)
  ext n
  simpa using hz n P hP

private theorem evaluate_summable_series {F I : Type u} [NormedField F] [CompleteSpace F]
    (v : I → F⟦X⟧) (hv : ∀ i, Summable (fun n => ‖PowerSeries.coeff n (v i)‖))
    (P : MvPolynomial I F) :
    Summable (fun n => ‖PowerSeries.coeff n (MvPolynomial.aeval v P)‖) ∧
      (∑' n, PowerSeries.coeff n (MvPolynomial.aeval v P)) =
        MvPolynomial.aeval (fun i => ∑' n, PowerSeries.coeff n (v i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, PowerSeries.algebraMap_apply, PowerSeries.coeff_C,
      Algebra.algebraMap_self, RingHom.id_apply]
    have hnorm (n : ℕ) : ‖(if n = 0 then a else 0)‖ = if n = 0 then ‖a‖ else 0 := by
      split <;> simp
    refine ⟨?_, by simp⟩
    simp only [hnorm]
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := fun h => hn (Finset.mem_singleton.mpr h)
    rw [ite_eq_right hn0]
  | add P Q hP hQ =>
    simp only [map_add]
    exact ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun _ => norm_add_le _ _) (hP.1.add hQ.1),
      (hP.1.of_norm.tsum_add hQ.1.of_norm).trans (congrArg₂ (· + ·) hP.2 hQ.2)⟩
  | mul_X P i hP =>
    let f : ℕ → F := fun n => PowerSeries.coeff n (MvPolynomial.aeval v P)
    let g : ℕ → F := fun n => PowerSeries.coeff n (v i)
    have hf : Summable fun n => ‖f n‖ := hP.1
    have hg : Summable fun n => ‖g n‖ := hv i
    simp only [map_mul, MvPolynomial.aeval_X, PowerSeries.coeff_mul]
    refine ⟨summable_norm_sum_mul_antidiagonal_of_summable_norm (f := f) (g := g) hf hg, ?_⟩
    calc
      _ = (∑' n, f n) * (∑' n, g n) :=
        (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f := f) (g := g) hf hg).symm
      _ = _ := congrArg (fun x : F => x * (∑' n, g n)) hP.2

open scoped Matrix.Norms.Operator

variable (p : ℕ) [Fact p.Prime] {F : Type u} [NormedField F] [aF : NormedAlgebra ℚ_[p] F]
  [dF : FiniteDimensional ℚ_[p] F] {J : Specs.AffineAlgebraicGroup F} (j : MatrixRealization J)

private def matrixEntries (p : ℕ) [Fact p.Prime] {F ι : Type u}
    [NormedField F] [NormedAlgebra ℚ_[p] F] [Fintype ι] :
    Matrix ι ι F →L[ℚ_[p]] (ι × ι → F) :=
  ContinuousLinearMap.pi fun ij =>
    (ContinuousLinearMap.proj ij.2 : (ι → F) →L[ℚ_[p]] F).comp
      (ContinuousLinearMap.proj ij.1 : (ι → ι → F) →L[ℚ_[p]] (ι → F))

set_option backward.isDefEq.respectTransparency false in
include aF in
omit dF in
private theorem matrixPoints_isClosed :
    IsClosed (Set.range (asMatrix j F)) := by
  let ι := Index.{u} j.size
  let B := Matrix ι ι F
  let P := {P : MatrixPolynomial F j.size // VanishesOnPoints j P}
  have heq : Set.range (asMatrix j F) =
      ⋂ a : P, {m : Bˣ | matrixEvaluation m.val a.val = 0} := by
    ext m
    rw [matrix_mem_range_iff j, Set.mem_iInter]
    exact ⟨fun h a => h a.val a.property, fun h Q hQ => h ⟨Q, hQ⟩⟩
  rw [heq]
  apply isClosed_iInter
  intro a
  apply (isClosed_singleton (x := (0 : F))).preimage
  have hc : Continuous (fun M : B => matrixEvaluation M a.val) := by
    rw [continuous_iff_continuousAt]
    intro M
    let e := matrixEntries (F := F) (ι := ι) p
    obtain ⟨d, hd, _⟩ := polynomialDerivative ℚ_[p] F (ι × ι) a.val (e M)
    exact (hd.comp M e.hasStrictFDerivAt).continuousAt
  exact hc.comp Units.continuous_val

set_option backward.isDefEq.respectTransparency false in
include dF in
private theorem matrixPoints_isEmbedding [Algebra k F] :
    IsEmbedding (fun g : PointsIn i F => (asMatrix i F g).val) := by
  letI : CompleteSpace F := FiniteDimensional.complete ℚ_[p] F
  let ι := Index.{u} i.size
  let B := Matrix ι ι F
  letI : CompleteSpace B := inferInstanceAs (CompleteSpace (ι → ι → F))
  exact (Units.isOpenEmbedding_val (R := B)).isEmbedding.comp
    ⟨.induced _, asMatrix_injective i F⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exponential_point_mem_tangent
    (X : Matrix (Index.{u} j.size) (Index.{u} j.size) F)
    (hX : X ∈ Metric.eball 0 (expSeries ℚ_[p] (Matrix (Index.{u} j.size) (Index.{u} j.size) F)).radius)
    (hex : exp X ∈ Set.range (fun g : PointsIn j F => (asMatrix j F g).val)) :
    X ∈ Set.range (matrixDifferential j.embedding j.matrix) := by
  letI : CompleteSpace F := FiniteDimensional.complete ℚ_[p] F
  let ι := Index.{u} j.size
  let B := Matrix ι ι F
  letI : CompleteSpace B := inferInstanceAs (CompleteSpace (ι → ι → F))
  let H := (asMatrix j F).range
  have hH : IsClosed (H : Set Bˣ) := matrixPoints_isClosed p j
  have hx : exp X ∈ (fun m : Bˣ => (m : B)) '' (H : Set Bˣ) := by
    obtain ⟨g, hg⟩ := hex
    exact ⟨asMatrix j F g, ⟨g, rfl⟩, hg⟩
  have hvan : dualMatrix ι X ∈ Set.range (asMatrix j (DualNumber F)) := by
    apply (matrix_mem_range_iff j _).mpr
    intro P hP
    let L := matrixEntries (F := F) (ι := ι) p
    obtain ⟨d, hd, hdval⟩ := polynomialDerivative ℚ_[p] F (ι × ι) P (L 1)
    have hD : HasFDerivAt (fun M : B => matrixEvaluation M P) (d.comp L) 1 :=
      hd.hasFDerivAt.comp 1 L.hasFDerivAt
    have hz : (d.comp L) X = 0 :=
      derivativeAnnihilatesLogarithm p B F H hH X _ _ hD
        (fun g => by
          obtain ⟨y, hy⟩ := g.property
          exact hy ▸ hP F y) hX hx
    have hconst : (TrivSqZeroExt.fstHom F F F).comp
          (matrixEvaluation (dualMatrix ι X).val) = matrixEvaluation (1 : B) := by
      apply MvPolynomial.algHom_ext
      intro ij
      simp only [matrixEvaluation, AlgHom.comp_apply, MvPolynomial.aeval_X]
      rfl
    apply TrivSqZeroExt.ext
    · change (TrivSqZeroExt.fstHom F F F).comp (matrixEvaluation (dualMatrix ι X).val) P = 0
      rw [hconst]
      have h := hP F (1 : PointsIn j F)
      rw [map_one, Units.val_one] at h
      exact h
    · exact (hdval (L X)).trans hz
  obtain ⟨x, hx⟩ := hvan
  let a := TrivSqZeroExt.fstHom F F F
  have hred : ((((groupPointsFunctor F).obj J.val).map (CommAlgCat.ofHom a)).hom x) = 1 := by
    apply asMatrix_injective j F
    rw [asMatrix_naturality, hx, map_one]
    apply Units.ext
    rfl
  let Y : Specs.Lie F J.val := ⟨x, hred⟩
  refine ⟨Y, ?_⟩
  have hy := matrixDual_tangent j Y
  change matrixDual (asMatrix j (DualNumber F) x).val = _ at hy
  rw [hx] at hy
  exact (congrArg TrivSqZeroExt.snd hy).symm

set_option backward.isDefEq.respectTransparency false in
private theorem tangent_exponential_mem_points (Y : Specs.Lie F J.val)
    (hY : matrixDifferential j.embedding j.matrix Y ∈
      Metric.eball 0 (expSeries ℚ_[p] (Matrix (Index.{u} j.size) (Index.{u} j.size) F)).radius) :
    exp (matrixDifferential j.embedding j.matrix Y) ∈
      Set.range (fun g : PointsIn j F => (asMatrix j F g).val) := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  letI : CompleteSpace F := FiniteDimensional.complete ℚ_[p] F
  let ι := Index.{u} j.size
  let B := Matrix ι ι F
  letI : CompleteSpace B := inferInstanceAs (CompleteSpace (ι → ι → F))
  let X := matrixDifferential j.embedding j.matrix Y
  let E := formalMatrixExp X
  let u : Bˣ :=
    { val := exp X
      inv := exp (-X)
      val_inv := (invertibleExpOfMemBall hY).mul_invOf_self
      inv_val := (invertibleExpOfMemBall hY).invOf_mul_self }
  suffices hu : u ∈ Set.range (asMatrix j F) by
    obtain ⟨g, hg⟩ := hu
    exact ⟨g, congrArg Units.val hg⟩
  apply (matrix_mem_range_iff j _).mpr
  intro P hP
  let ev (ij : ι × ι) : B →L[ℚ_[p]] F :=
    (ContinuousLinearMap.proj ij : (ι × ι → F) →L[ℚ_[p]] F).comp
      (matrixEntries (F := F) (ι := ι) p)
  have hcoeff (ij : ι × ι) (n : ℕ) :
      PowerSeries.coeff n (E ij.1 ij.2) =
        ev ij (((n ! : ℚ_[p])⁻¹) • X ^ n) := by
    rw [show E ij.1 ij.2 = PowerSeries.mk
      (fun m => (((m ! : F)⁻¹) • X ^ m) ij.1 ij.2) from rfl, PowerSeries.coeff_mk]
    change (((n ! : F)⁻¹) • X ^ n) ij.1 ij.2 = (((n ! : ℚ_[p])⁻¹) • X ^ n) ij.1 ij.2
    simp only [Matrix.smul_apply, smul_eq_mul, Algebra.smul_def, map_inv₀, map_natCast]
  have hv (ij : ι × ι) :
      Summable (fun n => ‖PowerSeries.coeff n (E ij.1 ij.2)‖) := by
    simp only [hcoeff]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => (ev ij).le_opNorm _)
      ((norm_expSeries_summable_of_mem_ball' X hY).mul_left ‖ev ij‖)
  have ht (ij : ι × ι) :
      (∑' n, PowerSeries.coeff n (E ij.1 ij.2)) = (exp X) ij.1 ij.2 := by
    simp only [hcoeff]
    exact ((expSeries_hasSum_exp_of_mem_ball' X hY).mapL (ev ij)).tsum_eq
  have heval := (evaluate_summable_series (fun ij : ι × ι => E ij.1 ij.2) hv P).2
  simp_rw [ht] at heval
  change (∑' n, PowerSeries.coeff n (matrixEvaluation E P)) = matrixEvaluation u.val P at heval
  rw [formalMatrixExp_vanishes j Y P hP] at heval
  simpa using heval.symm


include dF in
/-- The convergent exponential identifies the scheme tangent with the germ of
the closed matrix point group at the identity. -/
private theorem matrix_exponential_germ :
    ∀ᶠ X : Matrix (Index.{u} j.size) (Index.{u} j.size) F in 𝓝 0,
      exp X ∈ Set.range (fun g : PointsIn j F => (asMatrix j F g).val) ↔
        X ∈ Set.range (matrixDifferential j.embedding j.matrix) := by
  have hr := Metric.eball_mem_nhds
    (0 : Matrix (Index.{u} j.size) (Index.{u} j.size) F)
    (exp_radius_pos (A := Matrix (Index.{u} j.size) (Index.{u} j.size) F) p)
  filter_upwards [hr] with X hX
  constructor
  · exact exponential_point_mem_tangent p j X hX
  · rintro ⟨Y, rfl⟩
    exact tangent_exponential_mem_points p j Y hX

set_option backward.isDefEq.respectTransparency false in
theorem schemeExponentialChart : SchemeExponentialChart.{u} := by
  intro p _ F _ _ _ G i _
  letI : CompleteSpace F := FiniteDimensional.complete ℚ_[p] F
  letI : IsAffine G.val.X.left := G.prop.1
  let ι := Index.{u} i.size
  let B := Matrix ι ι F
  letI : CompleteSpace B := inferInstanceAs (CompleteSpace (ι → ι → F))
  let δ := matrixDifferentialLinear i.embedding i.matrix
  let L : Submodule F B := LinearMap.range δ
  let t := (L.restrictScalars ℚ_[p]).subtypeL
  have hL : (L : Set B) = Set.range (matrixDifferential i.embedding i.matrix) := rfl
  have hm := matrixPoints_isEmbedding (p := p) (F := F) i
  refine ⟨L, hL, restrictExponentialChart p B (L.restrictScalars ℚ_[p]) _
    (asMatrix i F) t hm Subtype.val_injective ?_⟩
  have ht : Set.range t = (L : Set B) := by
    ext X
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun hX => ⟨⟨X, hX⟩, rfl⟩⟩
  rw [ht, hL]
  exact matrix_exponential_germ p i

set_option backward.isDefEq.respectTransparency false in
theorem schemeLogarithmSpan : SchemeLogarithmSpan.{u} := by
  intro p _ F _ _ _ G i L hL c H hH
  let ι := Index.{u} i.size
  let B := Matrix ι ι F
  let Lp := L.restrictScalars ℚ_[p]
  letI : CompleteSpace F := FiniteDimensional.complete ℚ_[p] F
  letI : CompleteSpace B := inferInstanceAs (CompleteSpace (ι → ι → F))
  letI : IsTopologicalGroup (PointsIn i F) :=
    IsInducing.isTopologicalGroup (asMatrix i F) (.induced _)
  have hm := asMatrix_injective i F
  refine ⟨nonzeroLogarithmSpan p B Lp _ c H, ?_,
    opennessOfFullSpan p B Lp _ c hm Subtype.val_injective H hH⟩
  obtain ⟨d, _, hd, hConj, _⟩ := matrixLieComparison F G i (identityLieStructure G)
  intro a x hx
  let A := asMatrix i F a
  let f : B →L[ℚ_[p]] B := ContinuousLinearMap.mulLeftRight ℚ_[p] B A.val A⁻¹.val
  have hpres (y : Lp) : f y ∈ Lp := by
    have hy : (y : B) ∈ (L : Set B) := y.property
    rw [hL] at hy
    obtain ⟨Y, hY⟩ := hy
    change A.val * (y : B) * A⁻¹.val ∈ (L : Set B)
    rw [hL]
    refine ⟨schemeConjugation (a : PointsIn i F) Y, ?_⟩
    rw [← hd, hConj, hd, hY]
  let g := (f.comp Lp.subtypeL).codRestrict Lp hpres
  have hg (y : Lp) : Lp.subtypeL (g y) = A.val * (y : B) * A⁻¹.val := rfl
  exact ⟨g x, invarianceOfLogarithmSpan p B Lp _ c hm H a g hg x hx, rfl⟩


end Scheme

section NumberPlaces

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups.Specs Arithmetic.AdelicGroups
  LinearAlgebraicGroups.Specs.IntegralModels InfinitesimalCommutator
open Specs.StandardGroups (generalLinearPoints)
open Specs.Unipotent (Index)
open IsDedekindDomain HeightOneSpectrum WithZero WithZeroMulInt Valuation.IsRankOneDiscrete
open scoped WithZero NNReal NumberField Matrix.Norms.Operator

universe u v

open private baseChangePointIso isAffine_baseChange from LinearAlgebraicGroups.Affine.IdentityTangent
open private matrixPointMap matrixDifferentialLinear from LinearAlgebraicGroups.Affine.LieBracket

theorem numberPlacePrime : NumberPlacePrime.{u} := by
  intro K _ _ w
  letI : w.asIdeal.IsPrime := w.isPrime
  letI : NeZero w.asIdeal := ⟨w.ne_bot⟩
  exact ⟨_, Nat.absNorm_under_prime w.asIdeal, Int.liesOver_span_absNorm w.asIdeal⟩

private theorem rationalPrime_valuation (p : ℕ) [hp : Fact p.Prime] (x : ℚ) :
    (rationalPrime p).valuation ℚ x = Rat.padicValuation p x := by
  let v := rationalPrime p
  have hz (z : ℤ) : v.valuation ℚ (algebraMap ℤ ℚ z) =
      Rat.padicValuation p (algebraMap ℤ ℚ z) := by
    rcases eq_or_ne z 0 with rfl | h
    · simp
    rw [valuation_of_algebraMap, intValuation_eq_exp_neg_multiplicity _ h]
    change WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {z}) : ℤ)) =
      if (z : ℚ) = 0 then 0 else WithZero.exp (-padicValRat p z)
    rw [ite_eq_right (Int.cast_ne_zero.mpr h), padicValRat.of_int, padicValInt.of_ne_one_ne_zero]
    have hm : emultiplicity v.asIdeal (Ideal.span {z}) = emultiplicity (p : ℤ) z := by
      apply emultiplicity_eq_emultiplicity_iff.mpr
      intro n
      change Ideal.span {(p : ℤ)} ^ n ∣ Ideal.span {z} ↔ _
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    have he := congrArg ENat.toNat hm
    simpa only [multiplicity] using congrArg (fun n : ℕ => WithZero.exp (-(n : ℤ))) he
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := ℤ) x
  change v.valuation ℚ _ = _
  simp only [map_div₀, hz]

section CompletionNorm

variable (p : ℕ) [hp : Fact p.Prime] {K : Type u} [Field K] [NumberField K]
  (w : NumberFinitePlace K) [w.asIdeal.LiesOver (rationalPrime p).asIdeal]

set_option backward.isDefEq.respectTransparency false in
private theorem completion_norm_ratCast (x : ℚ) :
    letI := completionNormedField p w
    ‖algebraMap ℚ (w.adicCompletion K) x‖ = ‖(x : ℚ_[p])‖ := by
  let C := w.adicCompletion K
  letI := completionNormedField p w
  let e := w.asIdeal.ramificationIdx ℤ
  let b := completionNormBase p w
  have hb : b ≠ 0 := (completionNormBase_gt_one p w).ne_zero
  have hnorm (y : C) : ‖y‖ = (WithZeroMulInt.toNNReal hb (Valued.v y) : ℝ) := by
    let v : Valuation C ℤᵐ⁰ := Valued.v
    change ((WithZeroMulInt.toNNReal hb) ((valueGroup₀_equiv_withZeroMulInt v) (v.restrict y)) : ℝ) =
      ((WithZeroMulInt.toNNReal hb) (v y) : ℝ)
    rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (valuedAdicCompletion_surjective K w)]
  have hbase : b ^ e = (p : ℝ≥0) := by
    have he : (e : ℝ) ≠ 0 := by exact_mod_cast
      (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal (rationalPrime p).ne_bot).ne'
    change ((p : ℝ≥0) ^ ((e : ℝ)⁻¹)) ^ e = _
    rw [← NNReal.rpow_mul_natCast, inv_mul_cancel₀ he, NNReal.rpow_one]
  by_cases hx : x = 0
  · simp [hx]
  have hv : (Valued.v : Valuation C ℤᵐ⁰) (algebraMap ℚ C x) = (Rat.padicValuation p x) ^ e := by
    have h := valuation_liesOver K (rationalPrime p) w x
    rw [rationalPrime_valuation] at h
    rw [IsScalarTower.algebraMap_apply ℚ K C]
    change (Valued.v : Valuation C ℤᵐ⁰) (↑(algebraMap ℚ K x) : C) = _
    rw [valuedAdicCompletion_eq_valuation', ← h]
  rw [hnorm, hv, map_pow, WithZeroMulInt.toNNReal_neg_apply hb
    ((Rat.padicValuation p).ne_zero_iff.mpr hx)]
  have hpval : WithZero.log (Rat.padicValuation p x) = -padicValRat p x := by
    simp [Rat.padicValuation, hx]
  have hpow (n : ℤ) : (b ^ n) ^ e = (b ^ e) ^ n := by
    calc
      _ = (b ^ n) ^ (e : ℤ) := (zpow_natCast _ _).symm
      _ = (b ^ (e : ℤ)) ^ n := by rw [← zpow_mul, mul_comm n, zpow_mul]
      _ = _ := by rw [zpow_natCast]
  rw [hpval, hpow, hbase, NNReal.coe_zpow, NNReal.coe_natCast,
    Padic.norm_eq_zpow_neg_valuation (Rat.cast_ne_zero.mpr hx), Padic.valuation_ratCast]

end CompletionNorm

set_option backward.isDefEq.respectTransparency false in
theorem numberCompletionPadic : NumberCompletionPadic.{u} := by
  intro p hp K _ _ w _
  let C := w.adicCompletion K
  letI := completionNormedField p w
  let V := WithVal (Rat.padicValuation p)
  let e := (WithVal.equiv (Rat.padicValuation p)).toRingHom
  let a : V →+* ℚ_[p] := (Rat.castHom ℚ_[p]).comp e
  let q : V →+* C := (algebraMap ℚ C).comp e
  have ha : IsUniformInducing a := Padic.isUniformInducing_cast_withVal
  have had : DenseRange a := Padic.isDenseInducing_cast_withVal.dense
  have hn (x : V) : ‖q x‖ = ‖a x‖ := completion_norm_ratCast p w (e x)
  have hq : UniformContinuous q := by
    rw [(ha.basis_uniformity Metric.uniformity_basis_dist).uniformContinuous_iff
      Metric.uniformity_basis_dist]
    intro ε hε
    refine ⟨ε, hε, fun x y h => ?_⟩
    change dist (q x) (q y) < ε
    change dist (a x) (a y) < ε at h
    rwa [dist_eq_norm, ← map_sub, hn, map_sub, ← dist_eq_norm]
  let f := IsDenseInducing.extendRingHom (i := a) (f := q) ha had hq
  have hf : Continuous f := (uniformContinuous_uniformly_extend ha had hq).continuous
  have hfn (x : ℚ_[p]) : ‖f x‖ = ‖x‖ := by
    refine had.induction_on x (isClosed_eq (continuous_norm.comp hf) continuous_norm) ?_
    intro y
    have heq : f (a y) = q y := (ha.isDenseInducing had).extend_eq hq.continuous y
    rw [heq, hn]
  let n : NormedAlgebra ℚ_[p] C :=
    { f.toAlgebra with
      norm_smul_le := fun r x => by
        change ‖f r * x‖ ≤ ‖r‖ * ‖x‖
        rw [norm_mul, hfn] }
  refine ⟨n, ?_⟩
  letI := n
  let b := Module.finBasis ℚ K
  let W := Submodule.span ℚ_[p] (Set.range (fun i => algebraMap K C (b i)))
  letI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range _)
  have hw : ∀ x : K, algebraMap K C x ∈ W := by
    intro x
    rw [← b.sum_repr x, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply ℚ K C]
    have hsc (r : ℚ) : algebraMap ℚ C r = algebraMap ℚ_[p] C (r : ℚ_[p]) := by
      let y : V := (WithVal.equiv (Rat.padicValuation p)).symm r
      have heq : f (a y) = q y := (ha.isDenseInducing had).extend_eq hq.continuous y
      exact heq.symm
    rw [hsc, ← Algebra.smul_def]
    exact W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hclosed : IsClosed (W : Set C) := Submodule.closed_of_finiteDimensional W
  have hW : W = ⊤ := by
    rw [← Submodule.coe_eq_univ, ← hclosed.closure_eq]
    apply Set.eq_univ_of_univ_subset
    rw [← (w.denseRange_algebraMap K).closure_range]
    exact closure_mono (Set.range_subset_iff.mpr hw)
  letI : Module.Finite ℚ_[p] (⊤ : Submodule ℚ_[p] C) := hW ▸
    (show Module.Finite ℚ_[p] W from inferInstance)
  exact Module.Finite.of_surjective
    (Submodule.topEquiv : (⊤ : Submodule ℚ_[p] C) ≃ₗ[ℚ_[p]] C).toLinearMap
    Submodule.topEquiv.surjective

section ScalarExtension

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
  {G : AffineAlgebraicGroup k} (i : MatrixRealization G)

private def extendAffineAlgebraicGroup (G : AffineAlgebraicGroup k) :
    AffineAlgebraicGroup F := by
  letI : IsAffine G.val.X.left := G.prop.1
  letI : LocallyOfFiniteType G.val.X.hom := G.prop.2.1
  letI : QuasiCompact G.val.X.hom := G.prop.2.2
  refine ⟨(groupBaseChange k F).obj G.val, isAffine_baseChange F G.val, ?_⟩
  change LocallyOfFiniteType (pullback.snd G.val.X.hom (fieldSpecMap k F)) ∧
    QuasiCompact (pullback.snd G.val.X.hom (fieldSpecMap k F))
  exact ⟨inferInstance, inferInstance⟩

private def extendMatrixRealization :
    MatrixRealization (extendAffineAlgebraicGroup (F := F) G) := by
  let K := Index.{u} i.size
  let σ := restrictTestAlgebra k F
  let c : generalLinearPoints F K ≅ σ ⋙ generalLinearPoints k K :=
    NatIso.ofComponents (fun R => Iso.refl _) (by
      intro R S a
      apply GrpCat.ext
      intro t
      rfl)
  exact
    { size := i.size
      ambient := extendAffineAlgebraicGroup i.ambient
      matrix := baseChangePointIso F i.ambient.val ≪≫ Functor.isoWhiskerLeft σ i.matrix ≪≫ c.symm
      embedding := (groupBaseChange k F).map i.embedding
      closed := LinearAlgebraicGroups.baseChangeClosedSubgroup k F i.embedding i.closed }

set_option backward.isDefEq.respectTransparency false in
private theorem extended_matrix (R : TestAlgebra F)
    (g : ((groupPointsFunctor F).obj ((groupBaseChange k F).obj G.val)).obj R) :
    ((matrixPointMap (extendMatrixRealization (F := F) i).embedding
      (extendMatrixRealization (F := F) i).matrix).app R).hom g =
    ((matrixPointMap i.embedding i.matrix).app ((restrictTestAlgebra k F).obj R)).hom
      (baseChangePoint k F G.val.X R g) := by
  change (i.matrix.hom.app ((restrictTestAlgebra k F).obj R)).hom
    (baseChangePoint k F i.ambient.val.X R (g ≫ ((baseChange k F).map i.embedding.hom.hom))) =
    (i.matrix.hom.app ((restrictTestAlgebra k F).obj R)).hom
      (baseChangePoint k F G.val.X R g ≫ i.embedding.hom.hom)
  rw [baseChangePointsSchemeNaturality]

set_option backward.isDefEq.respectTransparency false in
private theorem extended_matrixDifferential
    (Y : Lie F ((groupBaseChange k F).obj G.val)) :
    matrixDifferential (extendMatrixRealization (F := F) i).embedding
      (extendMatrixRealization (F := F) i).matrix Y = scalarExtendedDifferential i Y := by
  ext a b
  exact congrArg (fun M : Matrix.GeneralLinearGroup (Index.{u} i.size) (DualNumber F) =>
    (M.val a b).snd) (extended_matrix i (CommAlgCat.of F (DualNumber F)) Y.toMul.val)

set_option backward.isDefEq.respectTransparency false in
omit [Algebra k F] in
private theorem extended_matrix_range (f : k →+* F) :
    letI := f.toAlgebra
    Set.range (fun g : PointsIn (extendMatrixRealization (F := F) i) F =>
      (asMatrix (extendMatrixRealization (F := F) i) F g).val) =
    Set.range (fun g : PointsIn i F => (asMatrix i F g).val) := by
  letI := f.toAlgebra
  let K := extendMatrixRealization (F := F) i
  let R := CommAlgCat.of F F
  let e : PointsIn K F ≃* PointsIn i F := baseChangePointGroupEquiv F G.val R
  have h (g : PointsIn K F) :
      (asMatrix K F g).val = (asMatrix i F (e g)).val := by
    have hv := congrArg (fun m : Matrix.GeneralLinearGroup (Index.{u} i.size) F => m.val)
      (extended_matrix i R g)
    refine Eq.trans ?_ (hv.trans ?_)
    · rfl
    · rfl
  ext M
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, (h x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨e.symm x, ?_⟩
    change (asMatrix K F (e.symm x)).val = (asMatrix i F x).val
    rw [h, e.apply_symm_apply]

end ScalarExtension

set_option backward.isDefEq.respectTransparency false in
theorem numberPlaceSchemeExponentialChart : NumberPlaceSchemeExponentialChart.{v, u} := by
  intro p _ K _ _ w _ G i _
  let D : GlobalFieldData.{u, v} K := .number inferInstance
  let F := D.Completion (.inl w)
  letI : NormedField F := completionNormedField p w
  letI : Algebra K F := completionAlgebra D (.inl w)
  obtain ⟨a, ha⟩ := numberCompletionPadic p K w
  letI : NormedAlgebra ℚ_[p] F := a
  letI : FiniteDimensional ℚ_[p] F := ha
  letI : CompleteSpace F := FiniteDimensional.complete ℚ_[p] F
  let G' := extendAffineAlgebraicGroup (F := F) G
  let i' := extendMatrixRealization (F := F) i
  letI : IsAffine G'.val.X.left := G'.prop.1
  let ι := Index.{u} i.size
  let B := Matrix ι ι F
  letI : CompleteSpace B := inferInstanceAs (CompleteSpace (ι → ι → F))
  let L : Submodule F B := LinearMap.range (matrixDifferentialLinear i'.embedding i'.matrix)
  let t := (L.restrictScalars ℚ_[p]).subtypeL
  have hdiff : (fun Y => matrixDifferential i'.embedding i'.matrix Y) =
      scalarExtendedDifferential (E := F) i :=
    funext (extended_matrixDifferential i)
  have hL : (L : Set B) = Set.range (scalarExtendedDifferential (E := F) i) :=
    congrArg Set.range hdiff
  have ht : Set.range t = (L : Set B) := by
    ext X
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun hX => ⟨⟨X, hX⟩, rfl⟩⟩
  have hm := matrixPoints_isEmbedding (p := p) (F := F) i
  refine ⟨a, ha, L, hL, restrictExponentialChart p B (L.restrictScalars ℚ_[p]) _
    (asMatrix i F) t hm Subtype.val_injective ?_⟩
  rw [ht, hL]
  have h := matrix_exponential_germ p i'
  change ∀ᶠ X : B in 𝓝 0, NormedSpace.exp X ∈ Set.range (fun g : PointsIn i' F => (asMatrix i' F g).val) ↔
    X ∈ Set.range (fun Y => matrixDifferential i'.embedding i'.matrix Y) at h
  have hrange : Set.range (fun g : PointsIn i' F => (asMatrix i' F g).val) =
      Set.range (fun g : PointsIn i F => (asMatrix i F g).val) :=
    extended_matrix_range i (D.embedding (.inl w))
  rw [hrange, hdiff] at h
  exact h


end NumberPlaces

end LinearAlgebraicGroups.Arithmetic.PadicLogarithmChart
