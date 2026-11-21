import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.Reparametrization
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith

/-! Independent obligations for paper.tex, d04:09:path-algebra.
The adjacent-interval construction includes singleton intervals. Rescaling is
expressed by actual increasing parameter changes, preserving the shared paths
and the proper Riemann integrals. -/
noncomputable section
open Set
namespace Specs.D04.C09.PathAlgebra
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
open Specs.D04.C09.Reparametrization.Model
namespace Model

def reverse {n a b} (γ : IntervalPath n a b) : IntervalPath n a b where
  ordered := γ.ordered
  toFun t := γ (a + b - t)
  continuousOn := γ.continuousOn.comp (by fun_prop) (by
    intro t ht; constructor <;> linarith [ht.1, ht.2])

/-- Glue paths on adjacent intervals, retaining the join only once. -/
def concatenate {n a c b} (γ : IntervalPath n a c) (η : IntervalPath n c b)
    (h : γ c = η c) : IntervalPath n a b where
  ordered := γ.ordered.trans η.ordered
  toFun t := if t ≤ c then γ t else η t
  continuousOn := by
    apply ContinuousOn.if (p := fun t => t ≤ c)
    · intro t ht
      have : t = c := by simpa only [show {t : ℝ | t ≤ c} = Iic c from rfl,
        frontier_Iic, mem_inter_iff, mem_singleton_iff] using ht.2
      simpa [this] using h
    · apply γ.continuousOn.mono
      intro t ht
      exact ⟨ht.1.1, by simpa only [show {t : ℝ | t ≤ c} = Iic c from rfl,
        closure_Iic, mem_Iic] using ht.2⟩
    · apply η.continuousOn.mono
      intro t ht
      exact ⟨by simpa only [show {t : ℝ | ¬t ≤ c} = Ioi c from by ext; simp,
        closure_Ioi, mem_Ici] using ht.2, ht.1.2⟩

end Model
open Model
abbrev reverseType := {n : ℕ} → {a b : ℝ} → IntervalPath n a b → IntervalPath n a b
def reverseValue : reverseType := @Model.reverse
abbrev concatenateType := {n : ℕ} → {a c b : ℝ} →
  (γ : IntervalPath n a c) → (η : IntervalPath n c b) → γ c = η c → IntervalPath n a b
def concatenateValue : concatenateType := @Model.concatenate

/-- Actual concatenation after the two supplied placements onto adjacent intervals. -/
def Model.rescaledConcatenate {n a₁ b₁ a₂ b₂ a c b}
    (γ : IntervalPath n a₁ b₁) (η : IntervalPath n a₂ b₂)
    (h₁ : ParameterChange a₁ b₁ a c) (h₂ : ParameterChange a₂ b₂ c b)
    (h : (reparametrize γ h₁) c = (reparametrize η h₂) c) : IntervalPath n a b :=
  concatenate (reparametrize γ h₁) (reparametrize η h₂) h
abbrev rescaledConcatenateType := {n : ℕ} → {a₁ b₁ a₂ b₂ a c b : ℝ} →
  (γ : IntervalPath n a₁ b₁) → (η : IntervalPath n a₂ b₂) →
  (h₁ : ParameterChange a₁ b₁ a c) → (h₂ : ParameterChange a₂ b₂ c b) →
  (reparametrize γ h₁) c = (reparametrize η h₂) c → IntervalPath n a b
def rescaledConcatenateValue : rescaledConcatenateType := @Model.rescaledConcatenate

def affine_parameter_existsType : Prop := ∀ {a b c d r k : ℝ}, c ≤ d → 0 < r →
  r*c+k = a → r*d+k = b → ∃ h : ParameterChange a b c d,
    (∀ t, h t = r*t+k) ∧ StrictMonoOn h (Icc c d)

def rescaled_endpoints_matchType : Prop := ∀ {n a₁ b₁ a₂ b₂ a c b}
  (γ : IntervalPath n a₁ b₁) (η : IntervalPath n a₂ b₂)
  (h₁ : ParameterChange a₁ b₁ a c) (h₂ : ParameterChange a₂ b₂ c b),
  StrictMonoOn h₁ (Icc a c) → StrictMonoOn h₂ (Icc c b) →
  γ b₁ = η a₂ → (reparametrize γ h₁) c = (reparametrize η h₂) c

/-- This version covers bounded Riemann data on all indicated intervals.
The affine constructor above supplies the ordinary placements; allowing all
increasing parameter changes is a stronger statement. -/
def rescaled_concatenateType : Prop := ∀ {n a₁ b₁ a₂ b₂ a c b}
  {γ : IntervalPath n a₁ b₁} {η : IntervalPath n a₂ b₂}
  (h₁ : ParameterChange a₁ b₁ a c) (h₂ : ParameterChange a₂ b₂ c b),
  StrictMonoOn h₁ (Icc a c) → StrictMonoOn h₂ (Icc c b) →
  ∀ (h : (reparametrize γ h₁) c = (reparametrize η h₂) c)
  (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η)
  (v' : PiecewiseC1Data (reparametrize γ h₁)) (w' : PiecewiseC1Data (reparametrize η h₂))
  (z : PiecewiseC1Data (Model.rescaledConcatenate γ η h₁ h₂ h))
  (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ)
  (hf : ScalarIntegrable v f) (hg : ScalarIntegrable w f)
  (hf' : ScalarIntegrable v' f) (hg' : ScalarIntegrable w' f) (hz : ScalarIntegrable z f)
  (hα : CovectorIntegrable v α) (hβ : CovectorIntegrable w α)
  (hα' : CovectorIntegrable v' α) (hβ' : CovectorIntegrable w' α) (hζ : CovectorIntegrable z α),
  length (Model.rescaledConcatenate γ η h₁ h₂ h) a b = length γ a₁ b₁ + length η a₂ b₂ ∧
  scalarLineIntegral z f hz = scalarLineIntegral v f hf + scalarLineIntegral w f hg ∧
  covectorLineIntegral z α hζ = covectorLineIntegral v α hα + covectorLineIntegral w α hβ

def concatenate_integrableType : Prop := ∀ {n a c b}
  {γ : IntervalPath n a c} {η : IntervalPath n c b} (h : γ c = η c)
  (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η) (H : E n → E n → ℝ),
  ∀ (hv : PieceIntegrable v H) (hw : PieceIntegrable w H),
  ∃ z : PiecewiseC1Data (concatenate γ η h), ∃ hz : PieceIntegrable z H,
    pieceIntegral z H hz = pieceIntegral v H hv + pieceIntegral w H hw


def reverse_applyType : Prop := ∀ {n a b} (γ : IntervalPath n a b) t,
  reverse γ t = γ (a+b-t)
def reverse_piecewiseC1Type : Prop := ∀ {n a b} (γ : IntervalPath n a b),
  PiecewiseC1 γ → PiecewiseC1 (reverse γ)
def length_reverseType : Prop := ∀ {n a b} (γ : IntervalPath n a b),
  length (reverse γ) a b = length γ a b
def scalar_reverseType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (v : PiecewiseC1Data γ) (w : PiecewiseC1Data (reverse γ)) (f : E n → ℝ)
  (hv : ScalarIntegrable v f) (hw : ScalarIntegrable w f),
  scalarLineIntegral w f hw = scalarLineIntegral v f hv
def covector_reverseType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (v : PiecewiseC1Data γ) (w : PiecewiseC1Data (reverse γ))
  (α : E n → E n →L[ℝ] ℝ) (hv : CovectorIntegrable v α) (hw : CovectorIntegrable w α),
  covectorLineIntegral w α hw = -covectorLineIntegral v α hv

def concatenate_piecewiseC1Type : Prop := ∀ {n a c b}
  (γ : IntervalPath n a c) (η : IntervalPath n c b) (h : γ c = η c),
  PiecewiseC1 γ → PiecewiseC1 η → PiecewiseC1 (concatenate γ η h)
def length_concatenateType : Prop := ∀ {n a c b}
  (γ : IntervalPath n a c) (η : IntervalPath n c b) (h : γ c = η c),
  length (concatenate γ η h) a b = length γ a c + length η c b
def scalar_concatenateType : Prop := ∀ {n a c b}
  {γ : IntervalPath n a c} {η : IntervalPath n c b} (h : γ c = η c)
  (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η)
  (z : PiecewiseC1Data (concatenate γ η h)) (f : E n → ℝ)
  (hv : ScalarIntegrable v f) (hw : ScalarIntegrable w f) (hz : ScalarIntegrable z f),
  scalarLineIntegral z f hz = scalarLineIntegral v f hv + scalarLineIntegral w f hw
def covector_concatenateType : Prop := ∀ {n a c b}
  {γ : IntervalPath n a c} {η : IntervalPath n c b} (h : γ c = η c)
  (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η)
  (z : PiecewiseC1Data (concatenate γ η h)) (α : E n → E n →L[ℝ] ℝ)
  (hv : CovectorIntegrable v α) (hw : CovectorIntegrable w α) (hz : CovectorIntegrable z α),
  covectorLineIntegral z α hz = covectorLineIntegral v α hv + covectorLineIntegral w α hw

def scalar_boundType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (f : E n → ℝ) (h : ScalarIntegrable d f) (M : ℝ),
  (∀ x ∈ trace γ, |f x| ≤ M) →
  |scalarLineIntegral d f h| ≤ M * (length γ a b).toReal
def covector_boundType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ)
  (h : CovectorIntegrable d α) (M : ℝ), (∀ x ∈ trace γ, ‖α x‖ ≤ M) →
  |covectorLineIntegral d α h| ≤ M * (length γ a b).toReal

def scalar_sup_boundType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (f : E n → ℝ) (h : ScalarIntegrable d f),
  BddAbove ((fun x => |f x|) '' trace γ) →
  |scalarLineIntegral d f h| ≤ sSup ((fun x => |f x|) '' trace γ) * (length γ a b).toReal
def covector_sup_boundType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (α : E n → E n →L[ℝ] ℝ) (h : CovectorIntegrable d α),
  BddAbove ((fun x => ‖α x‖) '' trace γ) →
  |covectorLineIntegral d α h| ≤ sSup ((fun x => ‖α x‖) '' trace γ) * (length γ a b).toReal

def constant_integralsType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (x : E n), (∀ t ∈ Icc a b, γ t = x) →
  ∀ (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ),
  ∃ hf : ScalarIntegrable d f, ∃ hα : CovectorIntegrable d α,
    length γ a b = 0 ∧ scalarLineIntegral d f hf = 0 ∧ covectorLineIntegral d α hα = 0

def degenerate_integralsType : Prop := ∀ {n a} {γ : IntervalPath n a a}
  (d : PiecewiseC1Data γ) (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ),
  ∃ hf : ScalarIntegrable d f, ∃ hα : CovectorIntegrable d α,
    length γ a a = 0 ∧ scalarLineIntegral d f hf = 0 ∧ covectorLineIntegral d α hα = 0
/-- No integrability of the newly constructed path is presupposed. -/
def reverse_integrableType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (v : PiecewiseC1Data γ) (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ)
  (hf : ScalarIntegrable v f) (hα : CovectorIntegrable v α),
  ∃ w : PiecewiseC1Data (reverse γ), ∃ hw : ScalarIntegrable w f,
    ∃ hβ : CovectorIntegrable w α,
    scalarLineIntegral w f hw = scalarLineIntegral v f hf ∧
    covectorLineIntegral w α hβ = -covectorLineIntegral v α hα

/-- Arbitrary original intervals are placed adjacently by increasing affine
translations. This includes zero-duration summands without a division by duration. -/
def arbitrary_concatenateType : Prop := ∀ {n a₁ b₁ a₂ b₂}
  {γ : IntervalPath n a₁ b₁} {η : IntervalPath n a₂ b₂} (h : γ b₁ = η a₂)
  (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η)
  (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ)
  (hf : ScalarIntegrable v f) (hg : ScalarIntegrable w f)
  (hα : CovectorIntegrable v α) (hβ : CovectorIntegrable w α),
  ∃ κ : IntervalPath n a₁ (b₁+(b₂-a₂)), ∃ z : PiecewiseC1Data κ,
    ∃ hz : ScalarIntegrable z f, ∃ hζ : CovectorIntegrable z α,
    (∀ t ∈ Icc a₁ b₁, κ t = γ t) ∧
    (∀ t ∈ Icc b₁ (b₁+(b₂-a₂)), κ t = η (t+a₂-b₁)) ∧
    length κ a₁ (b₁+(b₂-a₂)) = length γ a₁ b₁ + length η a₂ b₂ ∧
    scalarLineIntegral z f hz = scalarLineIntegral v f hf + scalarLineIntegral w f hg ∧
    covectorLineIntegral z α hζ = covectorLineIntegral v α hα + covectorLineIntegral w α hβ
end Specs.D04.C09.PathAlgebra
