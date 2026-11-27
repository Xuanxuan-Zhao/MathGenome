import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.EmbeddingProblem
import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Topology.Algebra.MulAction

/-! The kernel action in IG03 and its pullback and central case in IG04. -/

namespace Specs.GaloisFormalization.IG.FiniteEmbeddingProblem

universe u v w

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]

variable (P : FiniteEmbeddingProblem Γ B Q)

/-- Conjugation on the abelian kernel descends along the finite quotient map. -/
noncomputable def quotientConjugationValue [IsMulCommutative P.kernel] :
    Q →* MulAut P.kernel :=
  P.pi.toMonoidHom.liftOfSurjective P.pi_surjective
    ⟨MulAut.conjNormal, fun b hb => by
      rw [MonoidHom.mem_ker, MulAut.conjNormal_val (h := (⟨b, hb⟩ : P.kernel))]
      apply MulEquiv.ext
      intro a
      change (⟨b, hb⟩ : P.kernel) * a * (⟨b, hb⟩ : P.kernel)⁻¹ = a
      rw [mul_comm' (⟨b, hb⟩ : P.kernel) a, mul_inv_cancel_right]⟩

/-- The action on additive kernel coordinates induced by the descended automorphisms. -/
@[instance_reducible]
noncomputable def quotientKernelActionValue [IsMulCommutative P.kernel] :
    DistribMulAction Q (Additive P.kernel) where
  smul q a := Additive.ofMul (P.quotientConjugationValue q a.toMul)
  one_smul a := by
    change Additive.ofMul (P.quotientConjugationValue 1 a.toMul) = a
    rw [map_one]
    rfl
  mul_smul q r a := by
    change Additive.ofMul (P.quotientConjugationValue (q * r) a.toMul) =
      Additive.ofMul (P.quotientConjugationValue q (P.quotientConjugationValue r a.toMul))
    rw [map_mul]
    rfl
  smul_zero q := congrArg Additive.ofMul (map_one (P.quotientConjugationValue q))
  smul_add q a b := congrArg Additive.ofMul (map_mul (P.quotientConjugationValue q) a.toMul b.toMul)

/-- The action on kernel coordinates restricted along the prescribed map from Γ. -/
@[instance_reducible]
noncomputable def pullbackKernelActionValue [IsMulCommutative P.kernel] :
    DistribMulAction Γ (Additive P.kernel) :=
  letI := P.quotientKernelActionValue
  DistribMulAction.compHom (Additive P.kernel) P.rho.toMonoidHom

-- The three group types retain independent universes.
set_option linter.checkUnivs false in
def QuotientKernelActionType :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel],
    DistribMulAction Q (Additive P.kernel)

set_option linter.checkUnivs false in
def PullbackKernelActionType :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel],
    DistribMulAction Γ (Additive P.kernel)

def QuotientKernelActionFormula : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel],
    letI := P.quotientKernelActionValue
    ∀ (b : B) (a : Additive P.kernel),
      ((P.pi b • a).toMul : B) = b * (a.toMul : B) * b⁻¹

def QuotientKernelActionUnique : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel]
    (action : DistribMulAction Q (Additive P.kernel)),
    (letI := action
     ∀ (b : B) (a : Additive P.kernel),
       ((P.pi b • a).toMul : B) = b * (a.toMul : B) * b⁻¹) →
    action = P.quotientKernelActionValue

def PullbackKernelActionFormula : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel],
    letI := P.quotientKernelActionValue
    letI := P.pullbackKernelActionValue
    ∀ (γ : Γ) (a : Additive P.kernel), γ • a = P.rho γ • a

def ContinuousQuotientKernelAction : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel],
    letI := P.quotientKernelActionValue
    ContinuousSMul Q (Additive P.kernel)

def ContinuousPullbackKernelAction : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel],
    letI := P.pullbackKernelActionValue
    ContinuousSMul Γ (Additive P.kernel)

def KernelCommutativeOfCentral : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q), isCentralValue P → IsMulCommutative P.kernel

/-- Centrality supplies the commutativity of the actual kernel. -/
theorem kernelCommutativeOfCentral (h : isCentralValue P) : IsMulCommutative P.kernel :=
  IsMulCommutative.of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.property) a)

def QuotientKernelActionOfCentral : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) (h : isCentralValue P),
    letI := P.kernelCommutativeOfCentral h
    letI := P.quotientKernelActionValue
    ∀ (q : Q) (a : Additive P.kernel), q • a = a

def PullbackKernelActionOfCentral : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) (h : isCentralValue P),
    letI := P.kernelCommutativeOfCentral h
    letI := P.pullbackKernelActionValue
    ∀ (γ : Γ) (a : Additive P.kernel), γ • a = a

end Specs.GaloisFormalization.IG.FiniteEmbeddingProblem
