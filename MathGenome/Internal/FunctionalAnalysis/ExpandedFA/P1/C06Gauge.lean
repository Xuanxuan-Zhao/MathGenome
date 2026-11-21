import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Gauge

/-! The Minkowski functional, `paper.tex:1041–1047` (`fa2:p1:c06:gauge`). -/

namespace ExpandedFA.P1.C06

universe u
variable {E : Type u} [AddCommGroup E] [Module ℝ E]
open scoped Pointwise

/-- Positive real scales for which `x` belongs to the dilation of `U`.
Pointwise scalar multiplication means `t • U = {t • y | y ∈ U}`. -/
def gaugeScales (U : Set E) (x : E) : Set ℝ :=
  {t : ℝ | 0 < t ∧ x ∈ t • U}

/-- Absorption as defined in the manuscript: every vector belongs to some
strictly positive dilation. -/
def GaugeAbsorbing (U : Set E) : Prop :=
  ∀ x, (gaugeScales U x).Nonempty

/-- The domain in the source: absorbing convex sets containing zero. -/
def GaugeAdmissible (U : Set E) : Prop :=
  GaugeAbsorbing U ∧ Convex ℝ U ∧ (0 : E) ∈ U

/-- The gauge `p_U(x) = inf {t > 0 | x ∈ tU}`.

The expression is defined for all subsets using the real `sInf` convention
(in particular, `sInf ∅ = 0`). For `GaugeAdmissible U`, the scale set is
nonempty and bounded below, so this is its ordinary finite real infimum.
The formula does not depend on proof arguments for the domain hypotheses. -/
noncomputable def minkowskiGauge (U : Set E) (x : E) : ℝ :=
  sInf (gaugeScales U x)

/-- Membership uses actual real scalar multiplication of an element of `U`. -/
theorem mem_gaugeScales_iff (U : Set E) (x : E) (t : ℝ) :
    t ∈ gaugeScales U x ↔ 0 < t ∧ ∃ y ∈ U, t • y = x :=
  Iff.rfl

/-- Zero is always a lower bound for the positive scale set. -/
theorem gaugeScales_bddBelow (U : Set E) (x : E) :
    BddBelow (gaugeScales U x) :=
  ⟨0, fun _ ht => ht.1.le⟩

/-- Absorption ensures that the defining infimum is a greatest lower bound;
the empty-set convention is never used on the source domain. -/
theorem minkowskiGauge_isGLB (U : Set E) (hU : GaugeAbsorbing U) (x : E) :
    IsGLB (gaugeScales U x) (minkowskiGauge U x) :=
  isGLB_csInf (hU x) (gaugeScales_bddBelow U x)

end ExpandedFA.P1.C06
