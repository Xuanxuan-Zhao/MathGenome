import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Independent specifications for the real derivative and endpoint secant magnitudes
in paper.tex, section `inverse-endpoint-support` (original lines 1739–1742).
These are total real-valued definitions; no endpoint limit is assumed here.
-/

namespace Specs.D03SupportRepairs

def derivativeMagnitudeType : Type := (ℝ → ℝ) → ℝ → ℝ

noncomputable def derivativeMagnitudeValue : derivativeMagnitudeType :=
  fun F x => |deriv F x|

def secantMagnitudeType : Type := (ℝ → ℝ) → ℝ → ℝ → ℝ

noncomputable def secantMagnitudeValue : secantMagnitudeType :=
  fun F a x => |(F x - F a) / (x - a)|

end Specs.D03SupportRepairs
