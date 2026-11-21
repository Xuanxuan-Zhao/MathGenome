import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.KatoRellich
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Concrete real-line objects for `fa2:p3:schrodinger-potential`,
paper.tex:13642–13673. Both scalar fields use actual scalar-valued L²(ℝ).
Weak derivatives are scalar-linear test distributions, with the transpose
minus sign. H² includes the first and second weak derivatives in L².
No relative-bound, form-bound, self-adjointness or core certificate is data. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace ExpandedFA.Unbounded.SchrodingerPotential

abbrev L2 (𝕜 : Type) [RCLike 𝕜] := Lp 𝕜 2 (volume : Measure ℝ)
abbrev Tests (𝕜 : Type) [RCLike 𝕜] := TestFunction (⊤ : Opens ℝ) 𝕜 ⊤
abbrev Distribution (𝕜 : Type) [RCLike 𝕜] := Tests 𝕜 →L[𝕜] 𝕜

variable {𝕜 : Type} [RCLike 𝕜]

/-- Regular distribution of the actual real-line L² class. -/
def regular (u : L2 𝕜) : Distribution 𝕜 :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul 𝕜 𝕜) volume u

theorem regular_apply (u : L2 𝕜) (φ : Tests 𝕜) :
    regular u φ = ∫ x, φ x * u x := by
  apply TestFunction.integralAgainstBilinCLM_eq_integral
  exact ((Lp.memLp u).locallyIntegrable (by norm_num)).locallyIntegrableOn _

/-- The inclusion into distributions is scalar-linear. -/
def regularLM : L2 𝕜 →ₗ[𝕜] Distribution 𝕜 where
  toFun := regular
  map_add' u v := by
    ext φ
    simp only [regular_apply, add_apply]
    have hu := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      (((Lp.memLp u).locallyIntegrable (by norm_num)).locallyIntegrableOn
        (⊤ : Opens ℝ))
    have hv := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      (((Lp.memLp v).locallyIntegrable (by norm_num)).locallyIntegrableOn
        (⊤ : Opens ℝ))
    change Integrable (fun x => φ x * u x) volume at hu
    change Integrable (fun x => φ x * v x) volume at hv
    rw [← integral_add hu hv]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add u v] with x hx
    exact (congrArg (φ x * ·) hx).trans (mul_add _ _ _)
  map_smul' c u := by
    ext φ
    simp only [regular_apply, smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simp [hx, mul_left_comm]

/-- The distribution derivative on the real line; tests remain C∞_c. -/
def distributionDerivative (T : Distribution 𝕜) : Distribution 𝕜 :=
  -T.comp (TestFunction.lineDerivCLM 𝕜 (1 : ℝ))

/-- `v` is the weak first derivative of `u`. -/
def WeakDerivative (u v : L2 𝕜) : Prop :=
  regularLM v = distributionDerivative (regularLM u)

/-- The graph of -u″ with u,u′,u″ in L². -/
def freeGraph (𝕜 : Type) [RCLike 𝕜] : Submodule 𝕜 (L2 𝕜 × L2 𝕜) where
  carrier := {p | ∃ v : L2 𝕜, WeakDerivative p.1 v ∧ WeakDerivative v (-p.2)}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩ <;>
      simp [WeakDerivative, distributionDerivative]
  add_mem' := by
    rintro ⟨u, f⟩ ⟨w, g⟩ ⟨v, huv, hvf⟩ ⟨z, hwz, hzg⟩
    refine ⟨v + z, ?_, ?_⟩
    · simpa [WeakDerivative, distributionDerivative, map_add, ContinuousLinearMap.add_comp,
        neg_add, add_comm] using congrArg₂ (· + ·) huv hwz
    · simpa [WeakDerivative, distributionDerivative, map_add, ContinuousLinearMap.add_comp,
        neg_add, add_comm] using congrArg₂ (· + ·) hvf hzg
  smul_mem' := by
    rintro c ⟨u, f⟩ ⟨v, huv, hvf⟩
    refine ⟨c • v, ?_, ?_⟩
    · simpa [WeakDerivative, distributionDerivative, map_smul,
        ContinuousLinearMap.smul_comp, smul_neg] using congrArg (c • ·) huv
    · simpa [WeakDerivative, distributionDerivative, map_smul,
        ContinuousLinearMap.smul_comp, smul_neg] using congrArg (c • ·) hvf

/-- The usual H² space, represented by its underlying L² class. -/
def H2 (𝕜 : Type) [RCLike 𝕜] : Submodule 𝕜 (L2 𝕜) :=
  (freeGraph 𝕜).map (LinearMap.fst 𝕜 (L2 𝕜) (L2 𝕜))

/-- Canonical partial free Laplacian. The graph and exact domain are verified
by the implementation rather than assumed in this construction. -/
def freeLaplacian (𝕜 : Type) [RCLike 𝕜] : Operator 𝕜 (L2 𝕜) (L2 𝕜) :=
  (freeGraph 𝕜).toLinearPMap

/-- Scalar-valued compactly supported smooth classes on ℝ. -/
def smoothCompact (𝕜 : Type) [RCLike 𝕜] : Submodule 𝕜 (L2 𝕜) where
  carrier := {u | ∃ f : ℝ → 𝕜, ContDiff ℝ (⊤ : ℕ∞) f ∧
    HasCompactSupport f ∧ (u : ℝ → 𝕜) =ᵐ[volume] f}
  zero_mem' := ⟨0, contDiff_const, HasCompactSupport.zero, Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro u v ⟨f, hf, hfc, huf⟩ ⟨g, hg, hgc, hvg⟩
    refine ⟨f + g, hf.add hg, hfc.add hgc, ?_⟩
    filter_upwards [Lp.coeFn_add u v, huf, hvg] with x hx hfx hgx
    change (u + v : L2 𝕜) x = f x + g x
    exact hx.trans (congrArg₂ (· + ·) hfx hgx)
  smul_mem' := by
    rintro c u ⟨f, hf, hfc, huf⟩
    refine ⟨c • f, hf.const_smul c, hfc.smul_left, ?_⟩
    filter_upwards [Lp.coeFn_smul c u, huf] with x hx hfx
    simp [hx, hfx]

/-- The hypotheses on the potential, allowing any a.e. representative. -/
def Admissible (q : ℝ → ℝ) : Prop :=
  ∃ q₂ qInf : ℝ → ℝ, MemLp q₂ 2 volume ∧ MemLp qInf ∞ volume ∧
    q =ᵐ[volume] fun x => q₂ x + qInf x

/-- Maximal graph of real multiplication on the genuine scalar-valued L². -/
def potentialGraph (𝕜 : Type) [RCLike 𝕜] (q : ℝ → ℝ) :
    Submodule 𝕜 (L2 𝕜 × L2 𝕜) where
  carrier := {p | (p.2 : ℝ → 𝕜) =ᵐ[volume] fun x => (q x : 𝕜) * p.1 x}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero 𝕜 2 volume] with x hx
    simp [hx]
  add_mem' := by
    intro p r hp hr
    change ((p.2 + r.2 : L2 𝕜) : ℝ → 𝕜) =ᵐ[volume]
      fun x => (q x : 𝕜) * (p.1 + r.1 : L2 𝕜) x
    filter_upwards [Lp.coeFn_add p.1 r.1, Lp.coeFn_add p.2 r.2, hp, hr]
      with x hx hy hpx hrx
    exact hy.trans ((congrArg₂ (· + ·) hpx hrx).trans
      ((mul_add _ _ _).symm.trans (congrArg ((q x : 𝕜) * ·) hx.symm)))
  smul_mem' := by
    intro c p hp
    change ((c • p.2 : L2 𝕜) : ℝ → 𝕜) =ᵐ[volume]
      fun x => (q x : 𝕜) * (c • p.1 : L2 𝕜) x
    filter_upwards [Lp.coeFn_smul c p.1, Lp.coeFn_smul c p.2, hp] with x hx hy hpx
    simp [hx, hy, hpx, smul_eq_mul, mul_left_comm]

/-- No regularity or boundedness hypothesis is hidden in this operator. -/
def potential (𝕜 : Type) [RCLike 𝕜] (q : ℝ → ℝ) : Operator 𝕜 (L2 𝕜) (L2 𝕜) :=
  (potentialGraph 𝕜 q).toLinearPMap

/-- The operator sum, including its actual intersection domain. -/
def schrodinger (𝕜 : Type) [RCLike 𝕜] (q : ℝ → ℝ) : Operator 𝕜 (L2 𝕜) (L2 𝕜) :=
  freeLaplacian 𝕜 + potential 𝕜 q

/-- Generic form of the accepted real and complex self-adjointness predicates. -/
def SelfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H] (A : Operator 𝕜 H H) : Prop :=
  Dense (A.domain : Set H) ∧ A = HilbertAdjointSpec.adjointValue A

namespace Spec

/-- The concrete distribution realization is injective. -/
def RegularInjective : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  Function.Injective (regular (𝕜 := 𝕜))

/-- The chosen H² submodule has the usual iterated weak-derivative meaning. -/
def H2Identification : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (u : L2 𝕜),
  u ∈ H2 𝕜 ↔ ∃ v w : L2 𝕜, WeakDerivative u v ∧ WeakDerivative v w

/-- Actual pointwise multiplication satisfies the formal symmetry identity. -/
def PotentialInner : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (q : ℝ → ℝ)
    (u v : (potential 𝕜 q).domain),
  inner 𝕜 (potential 𝕜 q u) v.val = inner 𝕜 u.val (potential 𝕜 q v)

/-- Concrete graph identities, including the exact H² domain. -/
def FreeGraph : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  (freeLaplacian 𝕜).graph = freeGraph 𝕜 ∧ (freeLaplacian 𝕜).domain = H2 𝕜

def PotentialGraph : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (q : ℝ → ℝ),
  (potential 𝕜 q).graph = potentialGraph 𝕜 q

/-- The infinitesimal relative bound must be proved from Admissible alone. -/
def RelativeBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (q : ℝ → ℝ),
  Admissible q → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ u : (freeLaplacian 𝕜).domain,
      ∃ v : L2 𝕜, (u.val, v) ∈ (potential 𝕜 q).graph ∧
        ‖v‖ ≤ ε * ‖freeLaplacian 𝕜 u‖ + C * ‖u.val‖

/-- Infinitesimal quadratic-form bound on the full H¹ form domain. -/
def FormBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (q : ℝ → ℝ),
  Admissible q → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
    ∀ u v : L2 𝕜, WeakDerivative u v →
      Integrable (fun x => q x * ‖u x‖ ^ 2) volume ∧
        |∫ x, q x * ‖u x‖ ^ 2| ≤ ε * ‖v‖ ^ 2 + C * ‖u‖ ^ 2

/-- The free operator facts used in final assembly. The energy identity is
on the actual weak first derivative, not an assumed positivity certificate. -/
def FreeFacts (𝕜 : Type) [RCLike 𝕜] : Prop :=
  SelfAdjoint (freeLaplacian 𝕜) ∧
  OperatorDomainsSpec.coreValue (freeLaplacian 𝕜) (smoothCompact 𝕜) ∧
  ∀ u : (freeLaplacian 𝕜).domain, ∃ v : L2 𝕜,
    WeakDerivative u.val v ∧
      RCLike.re (inner 𝕜 u.val (freeLaplacian 𝕜 u)) = ‖v‖ ^ 2

/-- The free energy identity on every vector of the canonical domain.
The witness is an actual weak derivative in the same scalar-valued L² space. -/
def FreeEnergy : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ∀ u : (freeLaplacian 𝕜).domain, ∃ v : L2 𝕜,
    WeakDerivative u.val v ∧
      RCLike.re (inner 𝕜 u.val (freeLaplacian 𝕜 u)) = ‖v‖ ^ 2

/-- Every clause of the conclusion for a specified scalar field. -/
def SchrodingerFor (𝕜 : Type) [RCLike 𝕜] (q : ℝ → ℝ) : Prop :=
    SelfAdjoint (schrodinger 𝕜 q) ∧
    (schrodinger 𝕜 q).domain = H2 𝕜 ∧
    (∃ c : ℝ, ∀ u : (schrodinger 𝕜 q).domain,
      c * ‖u.val‖ ^ 2 ≤ RCLike.re (inner 𝕜 u.val (schrodinger 𝕜 q u))) ∧
    OperatorDomainsSpec.coreValue (schrodinger 𝕜 q) (smoothCompact 𝕜)

/-- The complete original conclusion on both actual real and complex L²(ℝ). -/
def Schrodinger : Prop := ∀ q : ℝ → ℝ, Admissible q →
  SchrodingerFor ℝ q ∧ SchrodingerFor ℂ q

/-- An assembly lemma, deliberately conditional. It is not a substitute for
proving FreeFacts, RelativeBound and FormBound from the source hypotheses. -/
def Assembly : Prop := FreeFacts ℝ → FreeFacts ℂ → RelativeBound → FormBound → Schrodinger

end Spec
end ExpandedFA.Unbounded.SchrodingerPotential
