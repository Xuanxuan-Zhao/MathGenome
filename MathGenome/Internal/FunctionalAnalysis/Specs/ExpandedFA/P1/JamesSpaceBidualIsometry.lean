import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceBidual

/-!
The last paragraph of `fa2:p1:james-space`, paper.tex:4580–4599.
The real cyclic James norm and actual continuous bidual are those of the
upstream Specs. Coordinate zero is manuscript coordinate one.
The displayed forward and inverse formulas fix the map, including the limit
term; the equivalence uses the original norms, not equivalent renormings.
-/
noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.P1.JamesBidualIsometrySpec
open JamesBidualSpec

local instance (m : JamesBanachBasisSpec.BanachBasisModel) : NormedAddCommGroup (Dual m) := inferInstance
local instance (m : JamesBanachBasisSpec.BanachBasisModel) : NormedSpace ℝ (Dual m) := inferInstance
local instance (m : JamesBanachBasisSpec.BanachBasisModel) : NormedAddCommGroup (Bidual m) := inferInstance
local instance (m : JamesBanachBasisSpec.BanachBasisModel) : NormedSpace ℝ (Bidual m) := inferInstance

/-- The explicitly prescribed surjective real-linear isometry and its inverse. -/
def ExplicitIsometry : Prop :=
  ∀ (m : JamesBanachBasisSpec.BanachBasisModel)
    (b : SchauderBasis ℝ (ModelSpace m)),
    b.basis = m.e → (∀ i x, b.coord i x = x.val i) →
    ∃ e : Bidual m ≃ₗᵢ[ℝ] ModelSpace m,
      (∀ (Φ : Bidual m) (L : ℝ),
        Tendsto (coefficientMap m b Φ) atTop (𝓝 L) →
        (e Φ).val 0 = -L ∧
          ∀ n, (e Φ).val (n+1) = coefficientMap m b Φ n - L) ∧
      (∀ (x : ModelSpace m) (n : ℕ),
        coefficientMap m b (e.symm x) n = x.val (n+1) - x.val 0)

/-- Abstract isometry with the bidual coexists with a codimension-one canonical
image and failure of reflexivity (surjectivity of canonical evaluation). -/
def NonreflexiveIsometric : Prop :=
  ∀ m : JamesBanachBasisSpec.BanachBasisModel,
    Nonempty (Bidual m ≃ₗᵢ[ℝ] ModelSpace m) ∧
      Nonempty ((Bidual m ⧸ (canonical m).range) ≃ₗ[ℝ] ℝ) ∧
      ¬ C04CanonicalMap.Spec.IsReflexiveValue ℝ (ModelSpace m)

end ExpandedFA.P1.JamesBidualIsometrySpec
