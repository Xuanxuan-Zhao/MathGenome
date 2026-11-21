import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.HilleYosida
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.YosidaConstruction

noncomputable section
open Filter Topology Set
open scoped NNReal

namespace ExpandedFA.Semigroups.HilleYosida
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- A − cI, on exactly D(A). -/
def translate (A : Unbounded.Operator 𝕜 X X) (c : ℝ) : Unbounded.Operator 𝕜 X X :=
  { domain := A.domain
    toFun := A.toFun - algebraMap ℝ 𝕜 c • A.domain.subtype }

omit [CompleteSpace X] in
@[simp] theorem translate_apply (A : Unbounded.Operator 𝕜 X X) (c : ℝ) (x : A.domain) :
    translate A c x = A x - algebraMap ℝ 𝕜 c • (x : X) := rfl

omit [CompleteSpace X] in
theorem translate_closed (A : Unbounded.Operator 𝕜 X X) (c : ℝ) (hA : A.IsClosed) :
    (translate A c).IsClosed := by
  have heq : ((translate A c).graph : Set (X × X)) =
      (fun p : X × X => (p.1, p.2 + algebraMap ℝ 𝕜 c • p.1)) ⁻¹' (A.graph : Set (X × X)) := by
    ext p
    change p ∈ (translate A c).graph ↔
      (p.1, p.2 + algebraMap ℝ 𝕜 c • p.1) ∈ A.graph
    constructor
    · intro hp
      obtain ⟨hx, hv⟩ := (Unbounded.mem_graph_iff (translate A c) p).mp hp
      apply (Unbounded.mem_graph_iff A _).mpr
      refine ⟨hx, ?_⟩
      change A ⟨p.1, hx⟩ - algebraMap ℝ 𝕜 c • p.1 = p.2 at hv
      exact sub_eq_iff_eq_add.mp hv
    · intro hp
      obtain ⟨hx, hv⟩ := (Unbounded.mem_graph_iff A _).mp hp
      apply (Unbounded.mem_graph_iff (translate A c) p).mpr
      exact ⟨hx, sub_eq_iff_eq_add.mpr hv⟩
  change IsClosed ((translate A c).graph : Set (X × X))
  rw [heq]
  exact hA.preimage (continuous_fst.prodMk (continuous_snd.add (continuous_const.smul continuous_fst)))

/-- Shifting the spectral parameter preserves the actual two-sided inverse. -/
def translateInverse (A : Unbounded.Operator 𝕜 X X) (c r : ℝ)
    (R : Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 (r + c))) :
    Unbounded.ResolventInverse (translate A c) (algebraMap ℝ 𝕜 r) where
  inverse := R.inverse
  mem_domain := R.mem_domain
  right_inverse y := by
    change algebraMap ℝ 𝕜 r • R.inverse y -
      (A ⟨R.inverse y, R.mem_domain y⟩ - algebraMap ℝ 𝕜 c • R.inverse y) = y
    have h := R.right_inverse y
    simp only [map_add, add_smul] at h
    convert h using 1
    abel
  left_inverse x := by
    change R.inverse (algebraMap ℝ 𝕜 r • (x : X) -
      (A x - algebraMap ℝ 𝕜 c • (x : X))) = (x : X)
    have h := R.left_inverse x
    simp only [map_add, add_smul] at h
    convert h using 2
    abel

omit [CompleteSpace X] in
/-- Resolvents of A − cI at r and A at r + c coincide. -/
theorem translate_resolvent (A : Unbounded.Operator 𝕜 X X) (c r : ℝ)
    (h : Nonempty (Unbounded.ResolventInverse A (algebraMap ℝ 𝕜 (r + c)))) :
    Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ 𝕜 r) (translate A c) =
      Unbounded.OperatorDomainsSpec.resolventValue (algebraMap ℝ 𝕜 (r + c)) A := by
  let S := translateInverse A c r h.some
  have hs : Nonempty (Unbounded.ResolventInverse (translate A c) (algebraMap ℝ 𝕜 r)) := ⟨S⟩
  simp only [Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left h, dite_eq_left hs]
  exact Unbounded.resolvent_inverse_unique _ _ hs.some S

omit [CompleteSpace X] in
theorem translate_hypotheses (A : Unbounded.Operator 𝕜 X X) (M ω : ℝ)
    (hd : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (h : HilleYosidaSpec.ResolventEstimates A M ω) :
    YosidaConstructionSpec.Hypotheses (translate A ω) M := by
  refine ⟨hd, translate_closed A ω hc, ?_, ?_⟩
  · intro r hr
    exact ⟨translateInverse A ω r (h.1 (r + ω) (by linarith)).some⟩
  · intro r hr n
    rw [YosidaConstructionSpec.positiveResolvent, translate_resolvent A ω r
      (h.1 (r + ω) (by linarith))]
    simpa only [add_sub_cancel_right] using h.2 (r + ω) (by linarith) n

/-- Necessity, retaining the common M for all powers. -/
theorem necessary (T : C0Semigroup 𝕜 X) (M ω : ℝ)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) :
    HilleYosidaSpec.ResolventEstimates (C0SemigroupSpec.generatorValue T) M ω := by
  constructor
  · intro r hr
    exact (LaplaceResolvent.canonical_resolvent T M ω (algebraMap ℝ 𝕜 r) hT
      (by simpa using hr)).1
  · intro r hr n
    simpa using ((LaplaceResolvent.canonical_resolvent T M ω (algebraMap ℝ 𝕜 r) hT
      (by simpa using hr)).2.2 n).2

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

/-- Multiplication of a semigroup by exp(ct). -/
def rescale (T : C0Semigroup 𝕜 X) (c : ℝ) : C0Semigroup 𝕜 X where
  operators t := Real.exp (c * (t : ℝ)) • T.operators t
  at_zero := by simp [T.at_zero]
  add_time t s := by
    ext x
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      NNReal.coe_add, mul_add, Real.exp_add, T.add_time,
      (T.operators t).map_smul_of_tower, smul_smul]
  strong_zero x := by
    have hc : Tendsto (fun h : ℝ => Real.exp (c * h)) (𝓝[>] 0) (𝓝 1) := by
      have hcont : Continuous (fun h : ℝ => Real.exp (c * h)) :=
        Real.continuous_exp.comp (continuous_const.mul continuous_id)
      simpa only [mul_zero, Real.exp_zero] using
        (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    apply (show Tendsto (fun h : ℝ => Real.exp (c * h) • T.operators h.toNNReal x)
      (𝓝[>] 0) (𝓝 x) from by simpa using hc.smul (T.strong_zero x)).congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [smul_apply, Real.coe_toNNReal _ (le_of_lt hh)]

/-- The growth constant is preserved under the scalar shift. -/
theorem rescale_bound (T : C0Semigroup 𝕜 X) (c M : ℝ) (hM : 1 ≤ M)
    (hT : ∀ t, ‖T.operators t‖ ≤ M) :
    C0SemigroupSpec.exponentialBoundValue (rescale T c) M c := by
  refine ⟨hM, ?_⟩
  intro t
  change ‖Real.exp (c * (t : ℝ)) • T.operators t‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm M]
  exact mul_le_mul_of_nonneg_left (hT t) (Real.exp_pos _).le

/-- The original generator derivative shifts by cx. This direction will suffice:
a common resolvent point below proves equality of the full domains. -/
theorem hasGeneratorLimit_rescale (T : C0Semigroup 𝕜 X) (c : ℝ) (x y : X)
    (h : HasGeneratorLimit T x y) :
    HasGeneratorLimit (rescale T c) x (y + c • x) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (c * t)) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).exp
  have hs : Tendsto (fun h : ℝ => h⁻¹ * (Real.exp (c * h) - 1))
      (𝓝[>] 0) (𝓝 c) := by
    simpa only [zero_add, mul_zero, Real.exp_zero, smul_eq_mul] using
      hd.tendsto_slope_zero_right
  have he : Tendsto (fun h : ℝ => Real.exp (c * h)) (𝓝[>] 0) (𝓝 1) := by
    simpa using hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  change Tendsto (fun h => differenceQuotient T h x) (𝓝[>] 0) (𝓝 y) at h
  have hl := (he.smul h).add (hs.smul_const x)
  change Tendsto (fun h => differenceQuotient (rescale T c) h x) (𝓝[>] 0)
    (𝓝 (y + c • x))
  apply (show Tendsto (fun h : ℝ => Real.exp (c * h) • differenceQuotient T h x +
    (h⁻¹ * (Real.exp (c * h) - 1)) • x) (𝓝[>] 0) (𝓝 (y + c • x)) from
    by simpa only [one_smul] using hl).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [(rescale T c).differenceQuotient_real, T.differenceQuotient_real]
  change Real.exp (c * r) • (r⁻¹ • (T.operators r.toNNReal x - x)) +
    (r⁻¹ * (Real.exp (c * r) - 1)) • x =
    r⁻¹ • (Real.exp (c * (r.toNNReal : ℝ)) • T.operators r.toNNReal x - x)
  rw [Real.coe_toNNReal _ hr.le]
  simp only [smul_sub, mul_smul, sub_smul, one_smul, smul_comm (Real.exp _) r⁻¹]
  abel

/-- The general sufficiency direction, obtained from the zero-shift construction. -/
theorem sufficient (A : Unbounded.Operator 𝕜 X X) (M ω : ℝ) (hM : 1 ≤ M)
    (hd : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (h : HilleYosidaSpec.ResolventEstimates A M ω) :
    ∃ T : C0Semigroup 𝕜 X, C0SemigroupSpec.generatorValue T = A ∧
      C0SemigroupSpec.exponentialBoundValue T M ω := by
  have hB := translate_hypotheses A M ω hd hc h
  obtain ⟨S, hS, hbS, _⟩ := YosidaConstruction.generation (translate A ω) M hB
  let T := rescale S ω
  have hbT : C0SemigroupSpec.exponentialBoundValue T M ω := rescale_bound S ω M hM hbS
  have hlim (x : A.domain) : HasGeneratorLimit T x (A x) := by
    have hg : ((x : X), translate A ω x) ∈ (generator S).graph := by
      rw [show generator S = translate A ω from hS]
      exact (translate A ω).mem_graph x
    have hl := hasGeneratorLimit_rescale S ω x (translate A ω x)
      ((mem_generator_graph_iff S x (translate A ω x)).mp hg)
    simpa only [translate_apply, Algebra.algebraMap_eq_smul_one, smul_assoc,
      one_smul, sub_add_cancel] using hl
  have hle : A ≤ generator T := by
    constructor
    · intro x hx
      exact ⟨A ⟨x, hx⟩, hlim ⟨x, hx⟩⟩
    · intro x y hxy
      apply generator_limit_unique T (y : X) (A x) (generator T y)
      · rw [← hxy]
        exact hlim x
      · exact generator_has_limit T y
  let z : 𝕜 := algebraMap ℝ 𝕜 (ω + 1)
  let R : Unbounded.ResolventInverse A z := (h.1 (ω + 1) (by linarith)).some
  let Q : Unbounded.ResolventInverse (generator T) z :=
    LaplaceResolvent.inverse T M ω z hbT (by dsimp [z]; simp)
  have hEq := YosidaConstruction.eq_of_extension_of_resolvents A (generator T) hle z R Q
  exact ⟨T, hEq.symm, hbT⟩

/-- General Hille–Yosida with the same M and ω in both directions. -/
theorem characterization : HilleYosidaSpec.Characterization (𝕜 := 𝕜) (X := X) := by
  intro A M ω hM hd hc
  constructor
  · rintro ⟨T, hA, hT⟩
    rw [← hA]
    exact necessary T M ω hT
  · exact sufficient A M ω hM hd hc

/-- The zero-shift Yosida approximants converge to the semigroup generated by A,
uniformly on every bounded nonnegative time interval for each vector. -/
theorem zero_shift_approximation :
    HilleYosidaSpec.ZeroShiftApproximation (𝕜 := 𝕜) (X := X) := by
  intro A M T hd hc hgen hb x b hb0
  have hn := necessary T M 0 hb
  rw [hgen] at hn
  have hY : YosidaConstructionSpec.Hypotheses A M := by
    refine ⟨hd, hc, hn.1, ?_⟩
    intro r hr n
    simpa only [sub_zero, YosidaConstructionSpec.positiveResolvent] using hn.2 r hr n
  obtain ⟨S, hS, _, hlim⟩ := YosidaConstruction.generation A M hY
  have heq : ∀ t, S.operators t = T.operators t :=
    GeneratorDeterminesSemigroup.generator_determines_semigroup S T (hS.trans hgen.symm)
  simpa only [heq] using hlim x b hb0

end ExpandedFA.Semigroups.HilleYosida
