import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.Helix
import MathGenome.Internal.MultivariableAnalysis.D04.C09.GradientIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

noncomputable section
open Set
open scoped BigOperators
namespace D04.C09
open SingleVariableAnalysis.Riemann
abbrev helix := Specs.D04.C09.Helix.Model.helix
abbrev helixVelocity := Specs.D04.C09.Helix.Model.helixVelocity
abbrev height := Specs.D04.C09.Helix.Model.height

theorem helix_derivative (a b t : ℝ) :
    HasDerivAt (helix a b) (helixVelocity a b t) t := by
  have h : HasDerivAt (fun s => ![a * Real.cos s, a * Real.sin s, b * s])
      ![-a * Real.sin t, a * Real.cos t, b] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using (Real.hasDerivAt_cos t).const_mul a
    · simpa using (Real.hasDerivAt_sin t).const_mul a
    · simpa using (hasDerivAt_id t).const_mul b
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h

lemma helixVelocity_norm (a b t : ℝ) :
    ‖helixVelocity a b t‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [helixVelocity, Specs.D04.C09.Helix.Model.helixVelocity, Fin.sum_univ_succ,
    Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem helix_speed (a b t : ℝ) :
    ‖deriv (helix a b) t‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [(helix_derivative a b t).deriv, helixVelocity_norm]

theorem height_gradient (x : E 3) :
    scalarGradient height x = WithLp.toLp 2 ![0, 0, 1] := by
  apply ext_inner_right ℝ
  intro v
  rw [← scalarGradient_represents]
  change fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) x v = _
  rw [(EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt.fderiv]
  simp [inner, Fin.sum_univ_succ]

lemma helix_continuous (a b : ℝ) : Continuous (helix a b) :=
  continuous_iff_continuousAt.mpr (fun t => (helix_derivative a b t).continuousAt)

lemma helixVelocity_continuous (a b : ℝ) : Continuous (helixVelocity a b) := by
  change Continuous ((EuclideanSpace.equiv (Fin 3) ℝ).symm ∘
    (fun t => ![-a * Real.sin t, a * Real.cos t, b]))
  apply Continuous.comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

private def helixPath (a b T : ℝ) (hT : 0 ≤ T) : IntervalPath 3 0 T :=
  ⟨hT, helix a b, (helix_continuous a b).continuousOn⟩

private def helixData (a b T : ℝ) (hT : 0 ≤ T) :
    PiecewiseC1Data (helixPath a b T hT) where
  partition := Classical.choice (partition_exists hT)
  velocity := fun _ => helixVelocity a b
  smooth := fun _ => ⟨(helixVelocity_continuous a b).continuousOn,
    fun t _ => (helix_derivative a b t).hasDerivWithinAt⟩

/-- The shared proper FTC followed by finite endpoint cancellation. -/
lemma pieceIntegral_of_primitive {n l r} {γ : IntervalPath n l r}
    (d : PiecewiseC1Data γ) (H : E n → E n → ℝ) (hH : PieceIntegrable d H)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hd : ∀ i t, HasDerivAt F (H (γ t) (d.velocity i t)) t) :
    pieceIntegral d H hH = F r - F l := by
  change (∑ i, realIntegral _ (hH i)) = _
  have he (i : Fin d.partition.n) :
      realIntegral (fun t => H (γ t) (d.velocity i t)) (hH i) =
        F (d.partition.point i.succ) - F (d.partition.point i.castSucc) :=
    real_ftc_second F _ _ _
      (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le
      hF.continuousOn (fun t _ => hd i t) (hH i)
  simp_rw [he]
  simpa only [d.partition.first, d.partition.last] using
    sum_cell_differences (fun j => F (d.partition.point j))

lemma helix_speed_integral (a b T : ℝ) (hT : 0 ≤ T) :
    ∃ h : RealIntegrable (fun u => ‖deriv (helix a b) u‖) 0 T,
      realIntegral (fun u => ‖deriv (helix a b) u‖) h =
        T * Real.sqrt (a ^ 2 + b ^ 2) := by
  have hc : Continuous (fun u => ‖deriv (helix a b) u‖) := by
    simp_rw [helix_speed]
    exact continuous_const
  have hi := riemann_integrable_of_continuousOn hT hc.continuousOn
  refine ⟨hi, ?_⟩
  have he := real_ftc_second (fun t => t * Real.sqrt (a ^ 2 + b ^ 2))
    (fun u => ‖deriv (helix a b) u‖) 0 T hT (by fun_prop)
    (fun t _ => by simpa only [helix_speed, one_mul, id_eq] using
      (hasDerivAt_id t).mul_const (Real.sqrt (a ^ 2 + b ^ 2))) hi
  simpa using he

theorem helix_length (a b T : ℝ) (_ha : 0 < a) (hT : 0 ≤ T) :
    length (helix a b) 0 T = ENNReal.ofReal (T * Real.sqrt (a ^ 2 + b ^ 2)) := by
  let d := helixData a b T hT
  let h := speed_integrable d
  have he : piecewiseSpeedIntegral d h = T * Real.sqrt (a ^ 2 + b ^ 2) := by
    have he := pieceIntegral_of_primitive d (fun _ v => ‖v‖) h
      (fun t => t * Real.sqrt (a ^ 2 + b ^ 2)) (by fun_prop)
      (fun i t => by simpa only [helixData, d, helixVelocity_norm, one_mul, id_eq] using
        (hasDerivAt_id t).mul_const (Real.sqrt (a ^ 2 + b ^ 2)))
    simpa [pieceIntegral, Specs.D04.C09.LineIntegrals.Model.pieceIntegral,
      piecewiseSpeedIntegral, Specs.D04.C09.PathsLength.Model.piecewiseSpeedIntegral] using he
  exact (length_speed_integral d h).1.trans (congrArg ENNReal.ofReal he)

theorem helix_arclength : Specs.D04.C09.Helix.helix_arclengthType := by
  intro a b T ha _ t ht
  obtain ⟨h, he⟩ := helix_speed_integral a b t ht.1
  exact ⟨h, he, helix_length a b t ha ht.1⟩


lemma height_work (x v : E 3) : inner ℝ (scalarGradient height x) v = v 2 := by
  rw [height_gradient]
  simp [PiLp.inner_apply, Fin.sum_univ_succ]

theorem helix_integrals : Specs.D04.C09.Helix.helix_integralsType := by
  intro a b T _ha hT
  let γ := helixPath a b T hT
  let d := helixData a b T hT
  have hw : WorkIntegrable d (scalarGradient height) :=
    work_integrable d _ (by
      have hc : Continuous (scalarGradient height) := by
        have he : scalarGradient height = fun _ => WithLp.toLp 2 ![0, 0, 1] :=
          funext height_gradient
        rw [he]
        exact continuous_const
      exact hc.continuousOn)
  have hs : ScalarIntegrable d height := scalar_integrable d _
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.continuousOn
  refine ⟨γ, fun _ => rfl, d, fun _ _ => rfl, hw, hs, ?_, ?_⟩
  · have he := pieceIntegral_of_primitive d
      (fun x v => inner ℝ (scalarGradient height x) v) hw
      (fun t => b * t) (by fun_prop) (by
        intro i t
        rw [height_work]
        change HasDerivAt (fun t => b * t) b t
        simpa using (hasDerivAt_id t).const_mul b)
    change pieceIntegral d (fun x v => inner ℝ (scalarGradient height x) v) hw = b * T
    simpa only [mul_zero, sub_zero] using he
  · have he := pieceIntegral_of_primitive d (fun x v => height x * ‖v‖) hs
      (fun t => b * t ^ 2 * Real.sqrt (a ^ 2 + b ^ 2) / 2) (by fun_prop) (by
        intro i t
        change HasDerivAt (fun t => b * t ^ 2 * Real.sqrt (a ^ 2 + b ^ 2) / 2)
          (b * t * ‖helixVelocity a b t‖) t
        rw [helixVelocity_norm]
        convert ((((hasDerivAt_id t).pow 2).const_mul b).mul_const
          (Real.sqrt (a ^ 2 + b ^ 2))).div_const 2 using 1 <;>
            (try funext u) <;> dsimp <;> ring)
    change pieceIntegral d (fun x v => height x * ‖v‖) hs = _
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, zero_div, sub_zero] using he

theorem helix_zero : Specs.D04.C09.Helix.helix_zeroType := by
  intro a b ha
  refine ⟨length_degenerate _ _, ?_⟩
  obtain ⟨γ, hγ, d, _, hw, hs, hew, hes⟩ := helix_integrals a b 0 ha le_rfl
  exact ⟨γ, hγ, d, hw, hs, by simpa using hew, by simpa using hes⟩

end D04.C09


