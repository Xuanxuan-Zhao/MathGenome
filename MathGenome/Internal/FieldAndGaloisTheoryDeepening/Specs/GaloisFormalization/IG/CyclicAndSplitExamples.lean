import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.LiftCoordinates
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.ProperSplitSolutions
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Instances.ZMod

/-! The cyclic and split finite embedding problems of Example IG07. -/

namespace Specs.GaloisFormalization.IG.CyclicAndSplitExamples

open FiniteEmbeddingProblem
open _root_.GaloisFormalization.GH.Model
open scoped IsMulCommutative

local notation "C₂" => Multiplicative (ZMod 2)
local notation "C₄" => Multiplicative (ZMod 4)
local notation "g₂" => (Multiplicative.ofAdd (1 : ZMod 2))

abbrev CyclicProblemType := FiniteEmbeddingProblem C₂ C₄ C₂

/-- The identity on the domain, with reduction modulo two on the middle group. -/
def cyclicProblem : CyclicProblemType where
  rho := ContinuousMonoidHom.id C₂
  pi := ⟨(ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom.toMultiplicative,
    continuous_of_discreteTopology⟩
  rho_surjective := Function.surjective_id
  pi_surjective := ZMod.castHom_surjective (by decide : 2 ∣ 4)

abbrev SplitProblemType := FiniteEmbeddingProblem C₂ (C₂ × C₂) C₂

/-- The identity on the domain, with projection onto the first factor on the middle group. -/
def splitProblem : SplitProblemType where
  rho := ContinuousMonoidHom.id C₂
  pi := ContinuousMonoidHom.fst C₂ C₂
  rho_surjective := Function.surjective_id
  pi_surjective q := ⟨(q, 1), rfl⟩

abbrev FirstFactorSolutionType := splitProblem.WeakSolution

def firstFactorSolution : FirstFactorSolutionType where
  lift := ContinuousMonoidHom.inl C₂ C₂
  commutes := ContinuousMonoidHom.ext fun _ => rfl

def CyclicCentral : Prop := isCentralValue cyclicProblem

def CyclicKernel : Prop :=
  ∀ b : C₄, b ∈ cyclicProblem.kernel ↔ b.toAdd = 0 ∨ b.toAdd = 2

def CyclicGeneratorFibre : Prop :=
  ∀ b : C₄, cyclicProblem.pi b = g₂ ↔ b.toAdd = 1 ∨ b.toAdd = 3

def CyclicGeneratorLiftOrder : Prop :=
  ∀ b : C₄, cyclicProblem.pi b = g₂ → orderOf b = 4

def CyclicNoWeakSolution : Prop := ¬ Nonempty cyclicProblem.WeakSolution

def CyclicFactorSetValue : Prop :=
  ∀ s : NormalizedSection cyclicProblem,
    ((factorSet cyclicProblem s g₂ g₂).toMul.val : C₄).toAdd = (2 : ZMod 4)

local notation "A" => Additive cyclicProblem.kernel

local instance : IsMulCommutative cyclicProblem.kernel := inferInstance

noncomputable local instance : DistribMulAction C₂ A := cyclicProblem.quotientKernelActionValue

def CyclicNormalizedDifferential : Prop :=
  ∀ z : continuousCochains C₂ A 1, z.val ![1] = 0 →
    (continuousDifferential C₂ A 1 z).val ![g₂, g₂] = 2 • z.val ![g₂] ∧
    2 • z.val ![g₂] = 0

def CyclicNonzeroClasses : Prop :=
  continuousExtensionClass cyclicProblem ≠ 0 ∧
    extensionClass cyclicProblem ≠ 0 ∧ weakLiftObstruction cyclicProblem ≠ 0

def ProductIsSplit : Prop := isSplitValue splitProblem

def ProductNoProperSolution : Prop :=
  ¬ ∃ sol : splitProblem.WeakSolution, isProperValue sol

end Specs.GaloisFormalization.IG.CyclicAndSplitExamples
