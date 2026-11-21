import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Substitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.ContinuousPrimitive
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Chain
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.Compact

/-! Substitution for continuous real or complex integrands, using only the
proper Darboux integral. A constant extension from the compact image hull
supplies a primitive on the open domain ℝ, so the chain rule applies even
where φ turns at the boundary of the original domain of f. -/
namespace SingleVariableAnalysis.Riemann
open Set

/-- Clamp to a closed interval, including the singleton case. -/
theorem continuous_extension_from_Icc {E : Type*} [TopologicalSpace E]
    {f : ℝ → E} {m M : ℝ} (hmM : m ≤ M) (hf : ContinuousOn f (Icc m M)) :
    ∃ g : ℝ → E, Continuous g ∧ EqOn g f (Icc m M) := by
  refine ⟨IccExtend hmM (fun x : Icc m M => f x), ?_, ?_⟩
  · exact (continuousOn_iff_continuous_domRestrict.mp hf).Icc_extend'
  · intro x hx
    exact IccExtend_of_mem hmM _ hx

/-- The extreme values belong to the original interval, so its interval
property places the entire compact image hull inside that domain. -/
theorem continuous_extension_on_image_hull {E : Type*} [TopologicalSpace E]
    {φ : ℝ → ℝ} {f : ℝ → E} {a b : ℝ} {I : Set ℝ} (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (hI : I.OrdConnected)
    (hf : ContinuousOn f I) (hmap : MapsTo φ (Icc a b) I) :
    ∃ g : ℝ → E, Continuous g ∧
      (∀ t ∈ Icc a b, g (φ t) = f (φ t)) ∧
      EqOn g f (uIcc (φ a) (φ b)) := by
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hφ
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hφ
  have hle : φ u ≤ φ v := hmin hv
  have hsub : Icc (φ u) (φ v) ⊆ I := by
    simpa only [uIcc_of_le hle] using hI.uIcc_subset (hmap hu) (hmap hv)
  obtain ⟨g, hg, he⟩ := continuous_extension_from_Icc hle (hf.mono hsub)
  have himage (t : ℝ) (ht : t ∈ Icc a b) : φ t ∈ Icc (φ u) (φ v) :=
    ⟨hmin ht, hmax ht⟩
  refine ⟨g, hg, fun t ht => he (himage t ht), ?_⟩
  exact he.mono (ordConnected_Icc.uIcc_subset
    (himage a (left_mem_Icc.mpr hab)) (himage b (right_mem_Icc.mpr hab)))

/-- FTC on an oriented compact hull, without a measure-integral bridge. -/
theorem real_oriented_ftc_of_hasDerivAt {F f : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (uIcc a b))
    (hd : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt F (f x) x)
    (hf : OrientedRealIntegrable f a b) :
    orientedRealIntegral f hf = F b - F a := by
  have he : realIntegral f hf = F (max a b) - F (min a b) :=
    real_ftc_second F f (min a b) (max a b) min_le_max hF hd hf
  change (if a ≤ b then realIntegral f hf else -realIntegral f hf) = F b - F a
  rw [he]
  split_ifs with hab
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right (le_of_not_ge hab), max_eq_left (le_of_not_ge hab), neg_sub]

theorem complex_oriented_ftc_of_hasDerivAt {F f : ℝ → ℂ} {a b : ℝ}
    (hF : ContinuousOn F (uIcc a b))
    (hd : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt F (f x) x)
    (hf : OrientedComplexIntegrable f a b) :
    orientedComplexIntegral f hf = F b - F a := by
  have he : complexIntegral f hf = F (max a b) - F (min a b) :=
    complex_ftc_second F f (min a b) (max a b) min_le_max hF hd hf
  change (if a ≤ b then complexIntegral f hf else -complexIntegral f hf) = F b - F a
  rw [he]
  split_ifs with hab
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right (le_of_not_ge hab), max_eq_left (le_of_not_ge hab), neg_sub]

theorem real_substitution :
    Specs.SingleVariableAnalysis.Ch09.Substitution.realSubstitution := by
  intro φ φ' f a b I hab hφ hφ' hd hI hf hmap
  obtain ⟨g, hg, heφ, he⟩ := continuous_extension_on_image_hull hab hφ hI hf hmap
  obtain ⟨H, hHc, hHd⟩ := real_continuous_primitive g univ ordConnected_univ hg.continuousOn
  have hHd' (x : ℝ) : HasDerivAt H (g x) x := hHd x (by simp)
  have hH : Continuous H := continuousOn_univ.mp hHc
  have hc : ContinuousOn (fun t => f (φ t) * φ' t) (Icc a b) :=
    (hf.comp hφ hmap).mul hφ'
  have hint : RealIntegrable (fun t => f (φ t) * φ' t) a b := by
    apply real_continuous_integrable _ hab
    intro t ht
    exact (relativeContinuousAt_within_iff _ _ _).mpr (hc t ht)
  have hfi := real_continuous_integrable_between hI hf
    (hmap (left_mem_Icc.mpr hab)) (hmap (right_mem_Icc.mpr hab))
  refine ⟨hint, hfi, ?_⟩
  have hleft : realIntegral _ hint = H (φ b) - H (φ a) := by
    apply real_ftc_second (H ∘ φ) _ a b hab (hH.comp_continuousOn hφ)
    intro t ht
    have hdt := (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    simpa only [heφ t ⟨ht.1.le, ht.2.le⟩] using (hHd' (φ t)).comp t hdt
  change realIntegral _ hint = orientedRealIntegral f hfi
  rw [hleft]
  symm
  apply real_oriented_ftc_of_hasDerivAt (hH.continuousOn) _ hfi
  intro x hx
  simpa only [he ⟨hx.1.le, hx.2.le⟩] using hHd' x

theorem complex_substitution :
    Specs.SingleVariableAnalysis.Ch09.Substitution.complexSubstitution := by
  intro φ φ' f a b I hab hφ hφ' hd hI hf hmap
  obtain ⟨g, hg, heφ, he⟩ := continuous_extension_on_image_hull hab hφ hI hf hmap
  obtain ⟨H, hHc, hHd⟩ := complex_continuous_primitive g univ ordConnected_univ hg.continuousOn
  have hHd' (x : ℝ) : HasDerivAt H (g x) x := hHd x (by simp)
  have hH : Continuous H := continuousOn_univ.mp hHc
  have hc : ContinuousOn (fun t => f (φ t) * (φ' t : ℂ)) (Icc a b) :=
    (hf.comp hφ hmap).mul (Complex.continuous_ofReal.comp_continuousOn hφ')
  have hint : ComplexIntegrable (fun t => f (φ t) * (φ' t : ℂ)) a b := by
    apply complex_continuous_integrable _ hab
    intro t ht
    exact (relativeContinuousAt_within_iff _ _ _).mpr (hc t ht)
  have hfi := complex_continuous_integrable_between hI hf
    (hmap (left_mem_Icc.mpr hab)) (hmap (right_mem_Icc.mpr hab))
  refine ⟨hint, hfi, ?_⟩
  have hleft : complexIntegral _ hint = H (φ b) - H (φ a) := by
    apply complex_ftc_second (H ∘ φ) _ a b hab (hH.comp_continuousOn hφ)
    intro t ht
    have hdt := (hd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    simpa only [heφ t ⟨ht.1.le, ht.2.le⟩, Complex.real_smul, mul_comm] using
      (hHd' (φ t)).scomp t hdt
  change complexIntegral _ hint = orientedComplexIntegral f hfi
  rw [hleft]
  symm
  apply complex_oriented_ftc_of_hasDerivAt (hH.continuousOn) _ hfi
  intro x hx
  simpa only [he ⟨hx.1.le, hx.2.le⟩] using hHd' x

end SingleVariableAnalysis.Riemann
