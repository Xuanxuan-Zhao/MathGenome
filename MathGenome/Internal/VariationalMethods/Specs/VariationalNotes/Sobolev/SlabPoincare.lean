import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Structure
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.ZeroExtension
import Mathlib.MeasureTheory.Function.L2Space

/-! The strip estimate of prop:sobolev-affine and the gradient Hilbert norm
in §v09-03. We allow any coordinate strip and any open set contained in it;
boundedness of the entire domain is unnecessary. In particular this includes
all bounded open domains, the empty domain, and every source exponent. -/
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped InnerProductSpace
namespace VariationalNotes.Sobolev

/-- Extract a column of the weak-gradient matrix, keeping its Euclidean norm. -/
def gradientColumn {d m : ℕ} (j : Fin d) : Gradient m d →L[ℝ] Vector m :=
  LinearMap.mkContinuous
    { toFun := fun A => WithLp.toLp 2 (fun i => A (i,j))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun A => by
      simp only [one_mul]
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
        EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
        Fintype.sum_prod_type]
      exact Finset.sum_le_sum fun i _ => Finset.single_le_sum
        (fun k _ => sq_nonneg (A (i,k))) (Finset.mem_univ j))

/-- The vector field ∂ⱼu, as an Lp equivalence class. -/
def partialVector {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (j : Fin d) : W1p Ω m p →L[ℝ] ValueLp Ω m p :=
  ((gradientColumn (m := m) j).compLpL p.ennreal (domainMeasure Ω)).comp
    (gradient Ω m p)

def InCoordinateStrip {d : ℕ} (Ω : Opens (Domain d)) (j : Fin d)
    (a b : ℝ) : Prop := ∀ x ∈ Ω, a < x j ∧ x j < b

namespace SlabExpected

def Inequality : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (j : Fin d)
    (a b : ℝ), a < b → InCoordinateStrip Ω j a b →
    ∀ u : W1pZero Ω m p,
      ‖value Ω m p u.val‖ ≤ (b-a) * ‖partialVector Ω p j u.val‖

/-- The same width controls values by the full Frobenius gradient. -/
def GradientControl : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (j : Fin d)
    (a b : ℝ), a < b → InCoordinateStrip Ω j a b →
    ∀ u : W1pZero Ω m p,
      ‖value Ω m p u.val‖ ≤ (b-a) * ‖gradient Ω m p u.val‖

/-- Two-sided quantitative comparison of the gradient and full source norms. -/
def NormEquivalence : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent) (j : Fin d)
    (a b : ℝ), a < b → InCoordinateStrip Ω j a b →
    ∀ u : W1pZero Ω m p,
      ‖gradient Ω m p u.val‖ ≤ ‖u‖ ∧
      ‖u‖ ≤ (b-a+1) * ‖gradient Ω m p u.val‖

/-- A complete gradient inner product on the original real vector space,
with the same topology as its full Sobolev norm. -/
def Hilbert : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (j : Fin d) (a b : ℝ),
    a < b → InCoordinateStrip Ω j a b →
    ∃ (N : NormedAddCommGroup (H1Zero Ω m))
      (I : @InnerProductSpace ℝ (H1Zero Ω m) _ N.toSeminormedAddCommGroup),
      N.toAddCommGroup = (inferInstance : AddCommGroup (H1Zero Ω m)) ∧
      (∀ (c : ℝ) (u : H1Zero Ω m), @SMul.smul _ _ I.toSMul c u = c • u) ∧
      @CompleteSpace (H1Zero Ω m) N.toUniformSpace ∧
      N.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (H1Zero Ω m)) ∧
      (∀ u, @norm _ N.toNorm u = ‖gradient Ω m Exponent.two u.val‖) ∧
      (∀ u v, @inner ℝ _ I.toInner u v =
        ∫ x, frobenius (gradient Ω m Exponent.two u.val x)
          (gradient Ω m Exponent.two v.val x) ∂domainMeasure Ω)

/-- All assertions of prop:sobolev-affine, retaining the separate exponent
ranges of its Banach and reflexivity conclusions. -/
def SobolevAffine : Prop :=
  StructureExpected.Banach ∧ StructureExpected.Reflexive ∧
  StructureExpected.AffineClosed ∧ ZeroExtensionExpected.Extension ∧ Inequality

end SlabExpected
end VariationalNotes.Sobolev
