import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.PrincipalLogarithm
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
The principal polar logarithm on the exact slit plane, and its inverse
relationship with the factorial-series exponential on the strict strip.
Mathlib's logarithm is defined by the same polar formula. Its derivative
theorem requires exactly the slit-plane hypothesis established below.
-/

noncomputable section

namespace D12Complex.PrincipalLogarithm

abbrev PrincipalSlitPlane : Specs.D12Complex.Ch02.PrincipalLogarithm.PrincipalSlitPlane_type :=
  _root_.D12Complex.PrincipalSlitPlane

abbrev PrincipalStrip : Specs.D12Complex.Ch02.PrincipalLogarithm.PrincipalStrip_type :=
  _root_.D12Complex.PrincipalStrip

abbrev PrincipalLog : Specs.D12Complex.Ch02.PrincipalLogarithm.PrincipalLog_type :=
  _root_.D12Complex.PrincipalLog

theorem principalSlitPlane_eq_slitPlane :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalSlitPlane_eq_slitPlane_type := by
  ext z
  simp only [_root_.D12Complex.PrincipalSlitPlane, Set.mem_compl_iff,
    Set.mem_image, Set.mem_Iic, Complex.mem_slitPlane_iff]
  constructor
  · intro hz
    by_contra hn
    push Not at hn
    apply hz
    exact ⟨z.re, hn.1, by simpa [hn.2] using z.re_add_im⟩
  · intro hz
    rintro ⟨x, hx, rfl⟩
    exact (not_lt.mpr hx) (by simpa using hz)

theorem mem_principalSlitPlane_iff :
    Specs.D12Complex.Ch02.PrincipalLogarithm.mem_principalSlitPlane_iff_type := by
  intro z
  rw [principalSlitPlane_eq_slitPlane]
  exact Complex.mem_slitPlane_iff

theorem principalSlitPlane_ne_zero :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalSlitPlane_ne_zero_type := by
  intro z hz
  rw [principalSlitPlane_eq_slitPlane] at hz
  exact Complex.slitPlane_ne_zero hz

theorem isOpen_principalSlitPlane :
    Specs.D12Complex.Ch02.PrincipalLogarithm.isOpen_principalSlitPlane_type := by
  rw [Specs.D12Complex.Ch02.PrincipalLogarithm.isOpen_principalSlitPlane_type,
    principalSlitPlane_eq_slitPlane]
  exact Complex.isOpen_slitPlane

theorem mem_principalStrip_iff :
    Specs.D12Complex.Ch02.PrincipalLogarithm.mem_principalStrip_iff_type := by
  intro w
  change |w.im| < Real.pi ↔ -Real.pi < w.im ∧ w.im < Real.pi
  exact abs_lt

theorem isOpen_principalStrip :
    Specs.D12Complex.Ch02.PrincipalLogarithm.isOpen_principalStrip_type := by
  have hs : _root_.D12Complex.PrincipalStrip =
      Complex.im ⁻¹' Set.Ioo (-Real.pi) Real.pi := by
    ext w
    exact mem_principalStrip_iff w
  change IsOpen _root_.D12Complex.PrincipalStrip
  rw [hs]
  exact isOpen_Ioo.preimage Complex.continuous_im

theorem principalArg_bounds :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalArg_bounds_type := by
  intro z hz
  rw [principalSlitPlane_eq_slitPlane] at hz
  exact ⟨Complex.neg_pi_lt_arg z,
    lt_of_le_of_ne (Complex.arg_le_pi z) (Complex.slitPlane_arg_ne_pi hz)⟩

theorem principalLog_eq_log :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalLog_eq_log_type := by
  intro z _
  rfl

theorem principalLog_parts :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalLog_parts_type := by
  intro z hz
  rw [principalLog_eq_log z hz]
  exact ⟨Complex.log_re z, Complex.log_im z⟩

theorem hasDerivAt_principalLog :
    Specs.D12Complex.Ch02.PrincipalLogarithm.hasDerivAt_principalLog_type := by
  intro z hz
  rw [principalSlitPlane_eq_slitPlane] at hz
  change HasDerivAt Complex.log (1 / z) z
  simpa only [one_div] using Complex.hasDerivAt_log hz

theorem hasComplexDerivativeAt_principalLog :
    Specs.D12Complex.Ch02.PrincipalLogarithm.hasComplexDerivativeAt_principalLog_type := by
  intro z hz
  exact (hasComplexDerivativeAt_iff PrincipalLog (1 / z) z).mpr
    (hasDerivAt_principalLog z hz)

theorem deriv_principalLog :
    Specs.D12Complex.Ch02.PrincipalLogarithm.deriv_principalLog_type := by
  intro z hz
  exact (hasDerivAt_principalLog z hz).deriv

theorem holomorphicOn_principalLog :
    Specs.D12Complex.Ch02.PrincipalLogarithm.holomorphicOn_principalLog_type := by
  exact ⟨isOpen_principalSlitPlane,
    fun z hz => (hasDerivAt_principalLog z hz).differentiableAt⟩

theorem E_principalLog :
    Specs.D12Complex.Ch02.PrincipalLogarithm.E_principalLog_type := by
  intro z hz
  rw [Exponential.E_eq_exp, principalLog_eq_log z hz]
  exact Complex.exp_log (principalSlitPlane_ne_zero z hz)

theorem principalLog_one :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalLog_one_type := by
  exact Complex.log_one

theorem principalLog_mapsTo :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalLog_mapsTo_type := by
  intro z hz
  apply (mem_principalStrip_iff _).mpr
  rw [(principalLog_parts z hz).2]
  exact principalArg_bounds z hz

theorem E_mapsTo_principalStrip :
    Specs.D12Complex.Ch02.PrincipalLogarithm.E_mapsTo_principalStrip_type := by
  intro w hw
  rw [principalSlitPlane_eq_slitPlane, Exponential.E_eq_exp]
  exact Complex.expOpenPartialHomeomorph.map_source ((mem_principalStrip_iff w).mp hw)

theorem principalLog_E :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalLog_E_type := by
  intro w hw
  rw [principalLog_eq_log (E w) (E_mapsTo_principalStrip hw), Exponential.E_eq_exp]
  have h := (mem_principalStrip_iff w).mp hw
  exact Complex.log_exp h.1 h.2.le

theorem principalLog_biholomorphicPair :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalLog_biholomorphicPair_type := by
  refine ⟨holomorphicOn_principalLog, ?_, principalLog_mapsTo, E_mapsTo_principalStrip,
    E_principalLog, principalLog_E⟩
  exact ⟨isOpen_principalStrip, fun w _ => (Exponential.hasDerivAt_E w).differentiableAt⟩

theorem principalLog_bijOn :
    Specs.D12Complex.Ch02.PrincipalLogarithm.principalLog_bijOn_type := by
  exact (biholomorphicPair_bijOn _ _ _ _ principalLog_biholomorphicPair).1

theorem E_bijOn_principalStrip :
    Specs.D12Complex.Ch02.PrincipalLogarithm.E_bijOn_principalStrip_type := by
  exact (biholomorphicPair_bijOn _ _ _ _ principalLog_biholomorphicPair).2

end D12Complex.PrincipalLogarithm
