import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Resolvent
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.Spectrum

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace D13Unified.Ch10.Resolvent
open RegularProblem
abbrev SpectralData := Specs.D13Unified.Ch10.Resolvent.SpectralData
abbrev IsSolution := Specs.D13Unified.Ch10.Resolvent.solutionValue

theorem eigenbasis_exists : Specs.D13Unified.Ch10.Resolvent.EigenbasisExists := by
  intro P
  obtain ⟨lam, phi, hm, B, hi, hd, hc, hr, he, _⟩ := Spectrum.spectrum P
  exact ⟨⟨lam, phi, hm, B, hi, hd, hc, hr, he⟩⟩

/-- Reciprocal gaps are bounded even with zero assigned to a vanishing gap.
Only finitely many indices precede the tail where the gap has norm at least 1. -/
lemma bounded_reciprocal (lam : ℕ → ℝ) (hd : Tendsto lam atTop atTop) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖((lam n : ℂ) - z)⁻¹‖ ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hd (z.re + 1))
  let C := 1 + ∑ n ∈ Finset.range N, ‖((lam n : ℂ) - z)⁻¹‖
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, ‖((lam n : ℂ) - z)⁻¹‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n
  by_cases hn : n < N
  · have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range N) =>
      norm_nonneg (((lam i : ℂ) - z)⁻¹)) (Finset.mem_range.mpr hn)
    dsimp [C]; linarith
  · have hr := Complex.re_le_norm ((lam n : ℂ) - z)
    have hh := hN n (Nat.le_of_not_gt hn)
    have hnorm : 1 ≤ ‖(lam n : ℂ) - z‖ := by
      simp only [Complex.sub_re, Complex.ofReal_re] at hr
      linarith
    have hi : ‖((lam n : ℂ) - z)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hnorm
    dsimp [C]; linarith

/-- Dividing the Hilbert coordinates really gives another square summable
sequence. This also constructs the zero-coordinate particular solution at resonance. -/
lemma divided_coordinates (P : Problem) (D : SpectralData P) (z : ℂ) (f : Hilbert P) :
    Memℓp (fun n => D.basis.repr f n / ((D.lam n : ℂ) - z)) 2 := by
  obtain ⟨C, hC, hbound⟩ := bounded_reciprocal D.lam D.divergent z
  apply ((lp.memℓp (D.basis.repr f)).norm.const_mul C).mono
  intro n
  rw [norm_div, div_eq_mul_inv, ← norm_inv]
  exact (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _)).trans_eq (mul_comm _ _)

def seriesClass (P : Problem) (D : SpectralData P) (z : ℂ) (f : Hilbert P) : Hilbert P :=
  D.basis.repr.symm ⟨_, divided_coordinates P D z f⟩

@[simp] lemma seriesClass_coordinate (P : Problem) (D : SpectralData P) (z : ℂ)
    (f : Hilbert P) (n : ℕ) :
    D.basis.repr (seriesClass P D z f) n = D.basis.repr f n / ((D.lam n : ℂ) - z) := by
  simp [seriesClass]

lemma seriesClass_hasSum (P : Problem) (D : SpectralData P) (z : ℂ) (f : Hilbert P) :
    HasSum (fun n => (paperInner P f (D.basis n) / ((D.lam n : ℂ) - z)) • D.basis n)
      (seriesClass P D z f) := by
  simpa only [seriesClass, HilbertBasis.repr_apply_apply, paperInner,
    Specs.D13Unified.Ch10.RegularProblem.paperInnerValue] using
    D.basis.hasSum_repr_symm ⟨_, divided_coordinates P D z f⟩

/-- The shifted Green inverse is diagonal in the actual Dirichlet basis. -/
lemma green_coordinate (P : Problem) (D : SpectralData P) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) (f : Hilbert P) (n : ℕ) :
    D.basis.repr (GreenWeakInverse.operator P c f) n =
      (((D.lam n + c)⁻¹ : ℝ) : ℂ) * D.basis.repr f n := by
  have he := (ClassicalEigenfunctionBridge.converse P c hc hQ _ _
    (D.classical n) (D.memLp n)).2.2.2
  rw [← D.represents n] at he
  rw [D.basis.repr_apply_apply, D.basis.repr_apply_apply]
  change paperInner P (GreenWeakInverse.operator P c f) (D.basis n) =
    (((D.lam n + c)⁻¹ : ℝ) : ℂ) * paperInner P f (D.basis n)
  have he' : GreenWeakInverse.operator P c (D.basis n) =
      (((D.lam n + c)⁻¹ : ℝ) : ℂ) • D.basis n := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_add] using he
  calc
    paperInner P (GreenWeakInverse.operator P c f) (D.basis n) =
        paperInner P f (GreenWeakInverse.operator P c (D.basis n)) :=
      GreenOperator.selfAdjoint P c hc hQ f (D.basis n)
    _ = _ := by
      rw [he']
      exact (inner_conjugate_second P _ f (D.basis n)).trans (by simp)

lemma shifted_eigenvalue_ne_zero (P : Problem) (D : SpectralData P) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) (n : ℕ) :
    ((D.lam n : ℂ) + (c : ℂ)) ≠ 0 := by
  have h := (ClassicalEigenfunctionBridge.converse P c hc hQ _ _
    (D.classical n) (D.memLp n)).2.1
  simpa only [Complex.ofReal_re, ← Complex.ofReal_add] using Complex.ofReal_ne_zero.mpr h.ne'

/-- The Hilbert inverse identity and the scalar equations are equivalent. -/
lemma inverse_iff_coordinates (P : Problem) (D : SpectralData P) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) (z : ℂ) (f u : Hilbert P) :
    u = GreenWeakInverse.operator P c (f + (z + (c : ℂ)) • u) ↔
      ∀ n, ((D.lam n : ℂ) - z) * D.basis.repr u n = D.basis.repr f n := by
  constructor
  · intro he n
    have h := congrArg (fun v => D.basis.repr v n) he
    rw [green_coordinate P D c hc hQ] at h
    simp only [map_add, map_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_inv, Complex.ofReal_add] at h
    have hh := shifted_eigenvalue_ne_zero P D c hc hQ n
    field_simp [hh] at h
    linear_combination h
  · intro h
    apply D.basis.repr.injective
    apply lp.ext
    funext n
    rw [green_coordinate P D c hc hQ]
    simp only [map_add, map_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_inv, Complex.ofReal_add]
    have hh := shifted_eigenvalue_ne_zero P D c hc hQ n
    field_simp [hh]
    linear_combination h n

/-- All coercion identities used below are AE identities for the actual L² quotient. -/
lemma forcing_ae (P : Problem) (z : ℂ) (f u : Hilbert P) :
    (f + z • u : Hilbert P) =ᵐ[baseMeasure P]
      (fun x => f x + z * u x) := by
  have ha := (weighted_ae P _).mp (Lp.coeFn_add f (z • u))
  have hs := (weighted_ae P _).mp (Lp.coeFn_smul z u)
  filter_upwards [ha, hs] with x hx hsx
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsx] using hx

lemma class_ae (P : Problem) (y : ℝ → ℂ) (hy : MemLp y 2 (weightedMeasure P)) :
    (toHilbert P y hy : ℝ → ℂ) =ᵐ[baseMeasure P] y :=
  (weighted_ae P _).mp (representative_ae P y hy)

/-- Changing from the resolvent equation to a coercive shifted equation
requires equality of forcing representatives only almost everywhere. -/
lemma solution_iff_shifted (P : Problem) (c : ℝ) (z : ℂ) (f : Hilbert P)
    (y : ℝ → ℂ) (hy : MemLp y 2 (weightedMeasure P)) :
    IsSolution P z f y ↔ GreenWeakInverse.IsWeakDirichletSolution P c
      (f + (z + (c : ℂ)) • toHilbert P y hy : Hilbert P) y := by
  have hg := forcing_ae P (z + (c : ℂ)) f (toHilbert P y hy)
  have hyAE := class_ae P y hy
  have hrhs : ∀ᵐ x ∂baseMeasure P,
      (((P.q x : ℂ) - z * (P.w x : ℂ)) * y x - (P.w x : ℂ) * f x) =
      (GreenKernel.Q P c x : ℂ) * y x - (P.w x : ℂ) *
        (f + (z + (c : ℂ)) • toHilbert P y hy : Hilbert P) x := by
    filter_upwards [hg, hyAE] with x hx hyx
    rw [hx, hyx]
    simp only [GreenKernel.Q, Complex.ofReal_add, Complex.ofReal_mul]
    ring
  constructor <;> intro h
  · refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    filter_upwards [h.2.2.2.2, hrhs] with x hd he
    rwa [← he]
  · refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    filter_upwards [h.2.2.2.2, hrhs] with x hd he
    rwa [he]

lemma solution_class_identity (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) (z : ℂ)
    (f : Hilbert P) (y : ℝ → ℂ) (hsol : IsSolution P z f y) :
    ∃ hy : MemLp y 2 (weightedMeasure P),
      toHilbert P y hy = GreenWeakInverse.operator P c
        (f + (z + (c : ℂ)) • toHilbert P y hy) := by
  let hy := continuous_memLp P y hsol.1.continuousOn
  have hw := (solution_iff_shifted P c z f y hy).mp hsol
  obtain ⟨_, hy', he⟩ := GreenWeakInverse.converse P c hc hQ _ y hw
  exact ⟨hy, he⟩

/-- The crucial representation bridge: the inverse identity produces an
actual C¹ representative with absolutely continuous flux, not a C² claim. -/
lemma representative_of_identity (P : Problem) (c : ℝ) (hc : 0 < c)
    (hQ : ∀ x ∈ interval P, 1 ≤ GreenKernel.Q P c x) (z : ℂ) (f u : Hilbert P)
    (he : u = GreenWeakInverse.operator P c (f + (z + (c : ℂ)) • u)) :
    ∃ (y : ℝ → ℂ) (hy : MemLp y 2 (weightedMeasure P)),
      IsSolution P z f y ∧ toHilbert P y hy = u := by
  let g := f + (z + (c : ℂ)) • u
  let y := GreenWeakInverse.representative P c g
  have hw := (GreenWeakInverse.inverse_weak P c hc hQ (g : ℝ → ℂ) (Lp.memLp g)).1
  have hym := (GreenWeakInverse.class_representative P c hc hQ g).1
  have hclass : toHilbert P y hym = u := by
    rw [he, ClassicalEigenfunctionBridge.operator_class P c hc hQ g]
  refine ⟨y, hym, ?_, hclass⟩
  apply (solution_iff_shifted P c z f y hym).mpr
  rw [hclass]
  exact hw

lemma solution_coordinates (P : Problem) (D : SpectralData P) (z : ℂ) (f : Hilbert P)
    (y : ℝ → ℂ) (hsol : IsSolution P z f y) :
    ∃ hy : MemLp y 2 (weightedMeasure P),
      ∀ n, ((D.lam n : ℂ) - z) * D.basis.repr (toHilbert P y hy) n =
        D.basis.repr f n := by
  obtain ⟨c, hc, hQ⟩ := GreenKernel.shift_exists P
  obtain ⟨hy, he⟩ := solution_class_identity P c hc hQ z f y hsol
  exact ⟨hy, (inverse_iff_coordinates P D c hc hQ z f _).mp he⟩

lemma solution_of_coordinates (P : Problem) (D : SpectralData P) (z : ℂ) (f u : Hilbert P)
    (h : ∀ n, ((D.lam n : ℂ) - z) * D.basis.repr u n = D.basis.repr f n) :
    ∃ (y : ℝ → ℂ) (hy : MemLp y 2 (weightedMeasure P)),
      IsSolution P z f y ∧ toHilbert P y hy = u := by
  obtain ⟨c, hc, hQ⟩ := GreenKernel.shift_exists P
  exact representative_of_identity P c hc hQ z f u
    ((inverse_iff_coordinates P D c hc hQ z f u).mpr h)

theorem equation : Specs.D13Unified.Ch10.Resolvent.Equation := by
  intro P z f y hy
  filter_upwards [hy.2.2.2.2, ae_restrict_mem measurableSet_Icc] with x hd hx
  have he := hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc P.a_lt_b x hx)
  change derivWithin (fun t => (P.p t : ℂ) * derivative P y t) (interval P) x = _ at he
  change -derivWithin (fun t => (P.p t : ℂ) * derivative P y t) (interval P) x +
    (P.q x : ℂ) * y x - z * (P.w x : ℂ) * y x = _
  rw [he]
  ring

/-- Uniqueness of Hilbert elements follows from all the coordinates, with no
pointwise convergence asserted for the expansion. -/
lemma coordinates_ext (P : Problem) (D : SpectralData P) (u v : Hilbert P)
    (h : ∀ n, D.basis.repr u n = D.basis.repr v n) : u = v := by
  apply D.basis.repr.injective
  apply lp.ext
  funext n
  exact h n

lemma series_coordinates (P : Problem) (D : SpectralData P) (z : ℂ) (f : Hilbert P)
    (hcompat : ∀ n, (D.lam n : ℂ) = z → D.basis.repr f n = 0) :
    ∀ n, ((D.lam n : ℂ) - z) * D.basis.repr (seriesClass P D z f) n =
      D.basis.repr f n := by
  intro n
  rw [seriesClass_coordinate]
  by_cases hn : (D.lam n : ℂ) = z
  · simp [hn, hcompat n hn]
  · exact mul_div_cancel₀ _ (sub_ne_zero.mpr hn)

theorem nonresonant : Specs.D13Unified.Ch10.Resolvent.Nonresonant := by
  intro P D z hz f
  have hcoef := series_coordinates P D z f (fun n hn => (hz n hn.symm).elim)
  obtain ⟨y, hy, hs, he⟩ := solution_of_coordinates P D z f (seriesClass P D z f) hcoef
  refine ⟨y, hy, hs, ?_, ?_⟩
  · change HasSum (fun n => (paperInner P f (D.basis n) / ((D.lam n : ℂ) - z)) •
      D.basis n) (toHilbert P y hy)
    rw [he]
    exact seriesClass_hasSum P D z f
  · intro v hv
    obtain ⟨hvm, hvc⟩ := solution_coordinates P D z f v hv
    apply (continuous_equality P v y hv.1.continuousOn hs.1.continuousOn hvm hy).mp
    rw [he]
    apply coordinates_ext P D
    intro n
    have hn : (D.lam n : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz n).symm
    exact mul_left_cancel₀ hn ((hvc n).trans (hcoef n).symm)

lemma resonance_gap (P : Problem) (D : SpectralData P) {n k : ℕ} (hn : n ≠ k) :
    (D.lam n : ℂ) - (D.lam k : ℂ) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  exact hn (D.increasing.injective (Complex.ofReal_injective h))

lemma resonant_compatibility (P : Problem) (D : SpectralData P) (k : ℕ)
    (f : Hilbert P) (y : ℝ → ℂ) (hy : IsSolution P (D.lam k : ℂ) f y) :
    paperInner P f (D.basis k) = 0 := by
  obtain ⟨hym, hh⟩ := solution_coordinates P D _ f y hy
  have hk := hh k
  simpa only [sub_self, zero_mul, HilbertBasis.repr_apply_apply, paperInner,
    Specs.D13Unified.Ch10.RegularProblem.paperInnerValue] using hk.symm

lemma resonant_particular (P : Problem) (D : SpectralData P) (k : ℕ) (f : Hilbert P)
    (hf : paperInner P f (D.basis k) = 0) :
    ∃ (y : ℝ → ℂ) (hy : MemLp y 2 (weightedMeasure P)),
      IsSolution P (D.lam k : ℂ) f y ∧
      toHilbert P y hy = seriesClass P D (D.lam k : ℂ) f := by
  apply solution_of_coordinates
  apply series_coordinates
  intro n hn
  have hnk : n = k := D.increasing.injective (Complex.ofReal_injective hn)
  subst n
  simpa only [HilbertBasis.repr_apply_apply, paperInner,
    Specs.D13Unified.Ch10.RegularProblem.paperInnerValue] using hf

lemma resonant_classification (P : Problem) (D : SpectralData P) (k : ℕ)
    (f v : Hilbert P)
    (hv : ∀ n, ((D.lam n : ℂ) - (D.lam k : ℂ)) * D.basis.repr v n =
      D.basis.repr f n) :
    v = seriesClass P D (D.lam k : ℂ) f + D.basis.repr v k • D.basis k := by
  apply coordinates_ext P D
  intro n
  simp only [map_add, map_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, D.basis.repr_self, lp.single_apply,
    Pi.single_apply, seriesClass_coordinate]
  by_cases hn : n = k
  · subst n
    simp
  · simp only [hn, ↓reduceIte, mul_zero, add_zero]
    apply (eq_div_iff (resonance_gap P D hn)).mpr
    simpa only [mul_comm] using hv n

/-- Adding any scalar multiple of a classical homogeneous mode preserves the
weak inhomogeneous equation and exactly its stated regularity. -/
lemma add_eigenfunction (P : Problem) (z : ℂ) (f : Hilbert P) (y v : ℝ → ℂ)
    (hy : IsSolution P z f y) (hv : IsClassicalEigenfunction P dirichlet z v) (t : ℂ) :
    IsSolution P z f (fun x => y x + t * v x) := by
  let S := interval P
  let Fv : ℝ → ℂ := fun x => (P.p x : ℂ) * derivative P v x
  have ud := uniqueDiffOn_Icc P.a_lt_b
  have hv1 : ContDiffOn ℝ 1 v S := hv.1.of_le (by norm_num)
  have hFv : ContDiffOn ℝ 1 Fv S :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn P.p_regular).mul
      (hv.1.derivWithin ud (by norm_num))
  have hFvac : AbsolutelyContinuousOnInterval Fv P.a P.b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le P.a_lt_b.le]
    exact hFv
  have hder : ∀ x ∈ S, derivative P (fun x => y x + t * v x) x =
      derivative P y x + t * derivative P v x := by
    intro x hx
    exact ((hy.1.differentiableOn (by norm_num) x hx).hasDerivWithinAt.add
      ((hv1.differentiableOn (by norm_num) x hx).hasDerivWithinAt.const_mul t)).derivWithin (ud x hx)
  have hflux : EqOn (fun x => (P.p x : ℂ) * derivative P (fun x => y x + t * v x) x)
      (fun x => (P.p x : ℂ) * derivative P y x + t * Fv x) S := by
    intro x hx
    change (P.p x : ℂ) * derivative P (fun x => y x + t * v x) x = _
    rw [hder x hx]
    dsimp [Fv]
    ring
  have hb := (dirichlet_boundary P v).mp hv.2.2.1
  refine ⟨hy.1.add (contDiffOn_const.mul hv1), ?_, by simp [hy.2.2.1, hb.1],
    by simp [hy.2.2.2.1, hb.2], ?_⟩
  · apply (hy.2.1.add (hFvac.const_smul t)).congr
    intro x hx
    rw [uIcc_of_le P.a_lt_b.le] at hx
    exact (hflux hx).symm
  · have hi := (ae_restrict_iff' measurableSet_Icc).mpr (GreenWeakInverse.ae_interior P.a P.b)
    filter_upwards [hy.2.2.2.2, ae_restrict_mem measurableSet_Icc, hi] with x hd hx hix
    have hn : S ∈ 𝓝 x := Icc_mem_nhds hix.1 hix.2
    have hvd := (hFv.differentiableOn (by norm_num) x hx).hasDerivWithinAt.hasDerivAt hn
    have he : derivWithin Fv S x = ((P.q x : ℂ) - z * (P.w x : ℂ)) * v x := by
      have hh := hv.2.2.2 x hx
      change -derivWithin Fv S x + (P.q x : ℂ) * v x = _ at hh
      linear_combination -hh
    rw [he] at hvd
    have hnew := (hd.add (hvd.const_mul t)).congr_of_eventuallyEq
      (show (fun x => (P.p x : ℂ) * derivative P (fun x => y x + t * v x) x) =ᶠ[𝓝 x]
        (fun x => (P.p x : ℂ) * derivative P y x + t * Fv x) from
          mem_of_superset hn hflux)
    convert hnew using 1
    ring

theorem resonant : Specs.D13Unified.Ch10.Resolvent.Resonant := by
  intro P D k f
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, hy⟩
    exact resonant_compatibility P D k f y hy
  · intro hf
    obtain ⟨y, _, hy, _⟩ := resonant_particular P D k f hf
    exact ⟨y, hy⟩
  · intro hf
    obtain ⟨y₀, hy₀, hs₀, he₀⟩ := resonant_particular P D k f hf
    refine ⟨y₀, hs₀, ?_, ?_⟩
    · intro t
      exact add_eigenfunction P _ f y₀ _ hs₀ (D.classical k) t
    · intro y hy
      obtain ⟨hym, hcoords⟩ := solution_coordinates P D _ f y hy
      let t : ℂ := D.basis.repr (toHilbert P y hym) k
      refine ⟨t, ?_⟩
      have hsum : MemLp (fun x => y₀ x + t * (D.phi k x : ℂ)) 2 (weightedMeasure P) :=
        hy₀.add ((D.memLp k).const_smul t)
      apply (continuous_equality P _ _ hy.1.continuousOn
        (hs₀.1.continuousOn.add (continuousOn_const.mul
          (D.classical k).1.continuousOn)) hym hsum).mp
      have hadd : toHilbert P (fun x => y₀ x + t * (D.phi k x : ℂ)) hsum =
          toHilbert P y₀ hy₀ + t • D.basis k := by
        rw [D.represents k]
        exact (MemLp.toLp_add hy₀ ((D.memLp k).const_smul t)).trans
          (congrArg (fun v => toHilbert P y₀ hy₀ + v)
            (MemLp.toLp_const_smul t (D.memLp k)))
      change toHilbert P y hym = toHilbert P (fun x => y₀ x + t * (D.phi k x : ℂ)) hsum
      rw [hadd, he₀]
      exact resonant_classification P D k f _ hcoords

end D13Unified.Ch10.Resolvent
