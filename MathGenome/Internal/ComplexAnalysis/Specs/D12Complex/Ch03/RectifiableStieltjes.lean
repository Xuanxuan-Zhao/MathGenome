import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathsChains
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsExistence

/-! D12.03.06, existence and sum laws. No derivative occurs in the definitions.
Strict endpoint partitions include the zero-cell partition when a=b. Tags range
independently over the entire closed cell. Length and variation retain ∞.
Ambient functions represent their restrictions to [a,b], including endpoints.
The integral is the unique unrestricted mesh limit, totalized by zero when no
limit exists. Its contour specialization uses the upstream continuous path.
-/
noncomputable section
open scoped BigOperators ENNReal
open Set

namespace D12Complex.Stieltjes

abbrev Partition := SingleVariableAnalysis.Riemann.PartitionData
abbrev Tags := @Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue
abbrev mesh := @Specs.SingleVariableAnalysis.Ch08.Partitions.meshValue

/-- The literal supremum of sums of Euclidean complex chord lengths. -/
def totalVariation (γ : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ P : Partition a b, ∑ i : Fin P.n,
    ENNReal.ofReal ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖

def polygonalLength (γ : ComplexPath) : ℝ≥0∞ := totalVariation γ γ.a γ.b

def Rectifiable (γ : ComplexPath) : Prop := polygonalLength γ < ⊤

def taggedSum {a b : ℝ} (P : Partition a b) (t : Tags P)
    (u γ : ℝ → ℂ) : ℂ :=
  ∑ i : Fin P.n, u (t i) * (γ (P.point i.succ) - γ (P.point i.castSucc))

/-- Quantifies over all partitions and all closed-cell taggings. -/
def MeshConverges {a b : ℝ} (S : (P : Partition a b) → Tags P → ℂ) (I : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ P : Partition a b, mesh P < δ → ∀ t : Tags P, ‖S P t - I‖ < ε

def HasIntegral (a b : ℝ) (u γ : ℝ → ℂ) (I : ℂ) : Prop :=
  MeshConverges (a := a) (b := b) (fun P t => taggedSum P t u γ) I

/-- Choice of the mesh limit, rather than a derivative or measure formula. -/
def integral (a b : ℝ) (u γ : ℝ → ℂ) : ℂ := by
  classical
  exact if h : ∃ I, HasIntegral a b u γ I then h.choose else 0

def contourIntegral (γ : ComplexPath) (f : ℂ → ℂ) : ℂ :=
  integral γ.a γ.b (f ∘ γ) γ

def supNorm (a b : ℝ) (u : ℝ → ℂ) : ℝ :=
  sSup ((fun x => ‖u x‖) '' Icc a b)

end D12Complex.Stieltjes

namespace Specs.D12Complex.Ch03.RectifiableStieltjes
open _root_.D12Complex _root_.D12Complex.Stieltjes

def Partition_type := ℝ → ℝ → Type
def Partition_value : Partition_type := @_root_.D12Complex.Stieltjes.Partition

def Tags_type := {a b : ℝ} → Partition a b → Type
def Tags_value : Tags_type := @_root_.D12Complex.Stieltjes.Tags

def mesh_type := {a b : ℝ} → Partition a b → ℝ
def mesh_value : mesh_type := @_root_.D12Complex.Stieltjes.mesh

def totalVariation_type := (ℝ → ℂ) → ℝ → ℝ → ℝ≥0∞
def totalVariation_value : totalVariation_type := @_root_.D12Complex.Stieltjes.totalVariation

def polygonalLength_type := ComplexPath → ℝ≥0∞
def polygonalLength_value : polygonalLength_type := @_root_.D12Complex.Stieltjes.polygonalLength

def Rectifiable_type := ComplexPath → Prop
def Rectifiable_value : Rectifiable_type := @_root_.D12Complex.Stieltjes.Rectifiable

def taggedSum_type := {a b : ℝ} → (P : Partition a b) → Tags P → (ℝ → ℂ) → (ℝ → ℂ) → ℂ
def taggedSum_value : taggedSum_type := @_root_.D12Complex.Stieltjes.taggedSum

def MeshConverges_type := {a b : ℝ} → ((P : Partition a b) → Tags P → ℂ) → ℂ → Prop
def MeshConverges_value : MeshConverges_type := @_root_.D12Complex.Stieltjes.MeshConverges

def HasIntegral_type := ℝ → ℝ → (ℝ → ℂ) → (ℝ → ℂ) → ℂ → Prop
def HasIntegral_value : HasIntegral_type := @_root_.D12Complex.Stieltjes.HasIntegral

def integral_type := ℝ → ℝ → (ℝ → ℂ) → (ℝ → ℂ) → ℂ
def integral_value : integral_type := @_root_.D12Complex.Stieltjes.integral

def contourIntegral_type := ComplexPath → (ℂ → ℂ) → ℂ
def contourIntegral_value : contourIntegral_type := @_root_.D12Complex.Stieltjes.contourIntegral

def supNorm_type := ℝ → ℝ → (ℝ → ℂ) → ℝ
def supNorm_value : supNorm_type := @_root_.D12Complex.Stieltjes.supNorm

def totalVariation_eq_eVariationOn_type : Prop :=
  ∀ (γ : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    totalVariation γ a b = eVariationOn γ (Icc a b)

def polygonalLength_eq_variation_type : Prop :=
  ∀ γ : ComplexPath,
    polygonalLength γ = totalVariation γ γ.a γ.b

def rectifiable_iff_type : Prop :=
  ∀ γ : ComplexPath,
    Rectifiable γ ↔ BoundedVariationOn γ (Icc γ.a γ.b)

def rectifiable_iff_finite_variation_type : Prop :=
  ∀ γ : ComplexPath,
    Rectifiable γ ↔ totalVariation γ γ.a γ.b < ⊤

def exists_integral_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ u γ : ℝ → ℂ,
    ContinuousOn u (Icc a b) → totalVariation γ a b < ⊤ →
    ∃ I, HasIntegral a b u γ I

def exists_unique_integral_type : Prop :=
  ∀ (γ : ComplexPath), Rectifiable γ → ∀ u : ℝ → ℂ,
    ContinuousOn u (Icc γ.a γ.b) → ∃! I, HasIntegral γ.a γ.b u γ I

def hasIntegral_unique_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ {u γ : ℝ → ℂ} {I J : ℂ},
    HasIntegral a b u γ I → HasIntegral a b u γ J → I = J

def integral_eq_of_hasIntegral_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ {u γ : ℝ → ℂ} {I : ℂ},
    HasIntegral a b u γ I → integral a b u γ = I

def hasIntegral_integral_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ u γ : ℝ → ℂ,
    ContinuousOn u (Icc a b) → totalVariation γ a b < ⊤ →
    HasIntegral a b u γ (integral a b u γ)

def integral_integrand_linearity_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ (u v γ : ℝ → ℂ) (r s : ℂ),
    (∃ I, HasIntegral a b u γ I) → (∃ J, HasIntegral a b v γ J) →
    integral a b (fun x => r * u x + s * v x) γ =
      r * integral a b u γ + s * integral a b v γ

def integral_integrator_linearity_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ (u γ η : ℝ → ℂ) (r s : ℂ),
    (∃ I, HasIntegral a b u γ I) → (∃ J, HasIntegral a b u η J) →
    integral a b u (fun x => r * γ x + s * η x) =
      r * integral a b u γ + s * integral a b u η

def continuous_integrand_linearity_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ (u v γ : ℝ → ℂ) (r s : ℂ),
    ContinuousOn u (Icc a b) → ContinuousOn v (Icc a b) → totalVariation γ a b < ⊤ →
    integral a b (fun x => r * u x + s * v x) γ =
      r * integral a b u γ + s * integral a b v γ

def continuous_integrator_linearity_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ (u γ η : ℝ → ℂ) (r s : ℂ),
    ContinuousOn u (Icc a b) → totalVariation γ a b < ⊤ → totalVariation η a b < ⊤ →
    integral a b u (fun x => r * γ x + s * η x) =
      r * integral a b u γ + s * integral a b u η

def integral_add_subinterval_type : Prop :=
  ∀ {a b c : ℝ}, a ≤ c → c ≤ b → ∀ u γ : ℝ → ℂ,
    ContinuousOn u (Icc a b) → totalVariation γ a b < ⊤ →
    integral a b u γ = integral a c u γ + integral c b u γ

def taggedSum_norm_le_type : Prop :=
  ∀ {a b : ℝ} (P : Partition a b) (t : Tags P) (u γ : ℝ → ℂ),
    totalVariation γ a b < ⊤ → ∀ {M : ℝ}, 0 ≤ M →
    (∀ x ∈ Icc a b, ‖u x‖ ≤ M) →
    ‖taggedSum P t u γ‖ ≤ M * (totalVariation γ a b).toReal

def integral_norm_le_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ u γ : ℝ → ℂ,
    ContinuousOn u (Icc a b) → totalVariation γ a b < ⊤ →
    ‖integral a b u γ‖ ≤ (totalVariation γ a b).toReal * supNorm a b u

def totalVariation_degenerate_type : Prop :=
  ∀ (a : ℝ) (γ : ℝ → ℂ), totalVariation γ a a = 0

def constant_of_zero_variation_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ γ : ℝ → ℂ,
    totalVariation γ a b = 0 → ∀ x ∈ Icc a b, γ x = γ a

def integral_of_constant_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ (u γ : ℝ → ℂ) (z : ℂ),
    (∀ x ∈ Icc a b, γ x = z) → integral a b u γ = 0

def integral_zero_variation_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ u γ : ℝ → ℂ,
    totalVariation γ a b = 0 → integral a b u γ = 0

def integral_degenerate_type : Prop :=
  ∀ (a : ℝ) (u γ : ℝ → ℂ), integral a a u γ = 0

def contourIntegral_hasIntegral_type : Prop :=
  ∀ (γ : ComplexPath), Rectifiable γ → ∀ f : ℂ → ℂ,
    ContinuousOn f γ.trace →
    HasIntegral γ.a γ.b (f ∘ γ) γ (contourIntegral γ f)

def contourIntegral_norm_le_type : Prop :=
  ∀ (γ : ComplexPath), Rectifiable γ → ∀ f : ℂ → ℂ,
    ContinuousOn f γ.trace →
    ‖contourIntegral γ f‖ ≤ (polygonalLength γ).toReal * sSup ((fun z => ‖f z‖) '' γ.trace)

end Specs.D12Complex.Ch03.RectifiableStieltjes
