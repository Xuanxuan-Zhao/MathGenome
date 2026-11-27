import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.AbelianKernelAction
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import Mathlib.Tactic.Group

/-! The factor set and extension class in Lemma IG03. -/

namespace Specs.GaloisFormalization.IG.FiniteEmbeddingProblem

open scoped IsMulCommutative
open _root_.GaloisFormalization.GH.Model

universe u v w

noncomputable section

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (P : FiniteEmbeddingProblem Γ B Q)

/-- A set section of the given quotient map sending the identity to the identity. -/
structure NormalizedSection where
  toFun : Q → B
  rightInverse : Function.RightInverse toFun P.pi
  map_one : toFun 1 = 1

instance : CoeFun (NormalizedSection P) (fun _ => Q → B) := ⟨NormalizedSection.toFun⟩

/-- Choose a section of the surjection, taking the identity as the lift of the identity. -/
noncomputable def normalizedSection : NormalizedSection P := by
  classical
  let s := Function.surjInv P.pi_surjective
  exact ⟨fun q => if q = 1 then 1 else s q, fun q => by
    by_cases h : q = 1
    · simp [h]
    · simpa only [ite_eq_right h] using Function.rightInverse_surjInv P.pi_surjective q, ite_eq_left rfl⟩

variable (s : NormalizedSection P)

local notation "A" => Additive P.kernel

@[simp] theorem NormalizedSection.pi_apply (q : Q) : P.pi (s q) = q :=
  s.rightInverse q

/-- The kernel element that measures the defect of multiplicativity of the section. -/
def factorSet (q r : Q) : A :=
  Additive.ofMul ⟨s q * s r * (s (q * r))⁻¹, by
    change P.pi (s q * s r * (s (q * r))⁻¹) = 1
    simp only [map_mul, map_inv, s.pi_apply, mul_inv_cancel]⟩

/-- The kernel coordinate of an element of the middle group relative to a section. -/
def kernelCoordinate (b : B) : A :=
  Additive.ofMul ⟨b * (s (P.pi b))⁻¹, by
    change P.pi (b * (s (P.pi b))⁻¹) = 1
    simp only [map_mul, map_inv, s.pi_apply, mul_inv_cancel]⟩

/-- Coordinates for the middle group, with the kernel factor on the left. -/
def sectionCoordinates : A × Q ≃ B where
  toFun x := (x.1.toMul : B) * s x.2
  invFun b := (kernelCoordinate P s b, P.pi b)
  left_inv := by
    rintro ⟨a, q⟩
    have h : P.pi ((a.toMul : B) * s q) = q := by
      rw [map_mul, s.pi_apply]
      have ha : P.pi (a.toMul : B) = 1 := a.toMul.property
      rw [ha, one_mul]
    refine Prod.ext ?_ h
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a.toMul : B) * s q * (s (P.pi ((a.toMul : B) * s q)))⁻¹ = a.toMul
    rw [h, mul_inv_cancel_right]
  right_inv b := by
    change b * (s (P.pi b))⁻¹ * s (P.pi b) = b
    exact inv_mul_cancel_right _ _

section Abelian

variable [IsMulCommutative P.kernel]

local instance kernelAction : DistribMulAction Q A := P.quotientKernelActionValue

private theorem smul_section (q : Q) (a : A) :
    ((q • a).toMul : B) = s q * (a.toMul : B) * (s q)⁻¹ := by
  have h : P.quotientConjugationValue (P.pi (s q)) = MulAut.conjNormal (s q) :=
    P.pi.toMonoidHom.liftOfRightInverse_comp_apply _
      (Function.rightInverse_surjInv P.pi_surjective) _ _
  rw [s.pi_apply] at h
  change (P.quotientConjugationValue q a.toMul : B) = _
  rw [h, MulAut.conjNormal_apply]

theorem factorSet_identity (q r t : Q) :
    factorSet P s q r + factorSet P s (q * r) t =
      q • factorSet P s r t + factorSet P s q (r * t) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change (factorSet P s q r).toMul.val * (factorSet P s (q * r) t).toMul.val =
    ((q • factorSet P s r t).toMul : B) * (factorSet P s q (r * t)).toMul.val
  rw [smul_section P s]
  change (s q * s r * (s (q * r))⁻¹) * (s (q * r) * s t * (s ((q * r) * t))⁻¹) =
    (s q * (s r * s t * (s (r * t))⁻¹) * (s q)⁻¹) *
      (s q * s (r * t) * (s (q * (r * t)))⁻¹)
  rw [mul_assoc q r t]
  group

/-- The factor set viewed as a continuous degree-two cochain on the discrete quotient. -/
def factorCochain : continuousCochains Q A 2 :=
  cochainTwo (fun qr => factorSet P s qr.1 qr.2) continuous_of_discreteTopology

/-- The factor cochain lies in the kernel of the inhomogeneous differential. -/
def factorCocycle : continuousCocycles Q A 2 :=
  ⟨factorCochain P s, by
    change continuousDifferential Q A 2 (factorCochain P s) = 0
    apply Subtype.ext
    funext x
    change differentialFormula Q A 2 (factorCochain P s).val x = 0
    rw [differentialFormula, Fin.sum_univ_three]
    change x 0 • factorSet P s (x 1) (x 2) +
      ((-1 : ℤ) ^ (0 + 1) • factorSet P s (x 0 * x 1) (x 2) +
       (-1 : ℤ) ^ (1 + 1) • factorSet P s (x 0) (x 1 * x 2) +
       (-1 : ℤ) ^ (2 + 1) • factorSet P s (x 0) (x 1)) = 0
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (sub_eq_zero.mpr (factorSet_identity P s (x 0) (x 1) (x 2)).symm :
        x 0 • factorSet P s (x 1) (x 2) + factorSet P s (x 0) (x 1 * x 2) -
          (factorSet P s (x 0) (x 1) + factorSet P s (x 0 * x 1) (x 2)) = 0)⟩

/-- The class of a chosen factor set in the continuous cochain model. -/
noncomputable def continuousExtensionClass : ContinuousH Q A 2 :=
  continuousClass Q A 2 (factorCocycle P (normalizedSection P))

/-- The ordinary degree-two cohomology class of the chosen factor set.
The representation uses the universe lifts of the shared cochain model. -/
noncomputable def extensionClass :
    groupCohomology (integralRepresentation.{w,v,max w v} Q A) 2 :=
  groupCohomology.π (integralRepresentation.{w,v,max w v} Q A) 2
    (ordinaryCyclesMk.{w,v,0} Q A 2 (factorCocycle P (normalizedSection P)))

end Abelian

namespace Specification

private abbrev declarationType {α : Sort*} (_ : α) : Sort _ := α

set_option linter.checkUnivs false

def NormalizedSectionType := declarationType (@NormalizedSection.{u,v,w})
def normalizedSectionTypeValue : NormalizedSectionType.{u,v,w} := @NormalizedSection.{u,v,w}
def ChooseSectionType := declarationType (@normalizedSection.{u,v,w})
def FactorSetType := declarationType (@factorSet.{u,v,w})
def KernelCoordinateType := declarationType (@kernelCoordinate.{u,v,w})
def SectionCoordinatesType := declarationType (@sectionCoordinates.{u,v,w})
def FactorCochainType := declarationType (@factorCochain.{u,v,w})
def FactorCocycleType := declarationType (@factorCocycle.{u,v,w})
def ContinuousExtensionClassType := declarationType (@continuousExtensionClass.{u,v,w})
def ExtensionClassType := declarationType (@extensionClass.{u,v,w})

def FactorSetFormula : Prop :=
  ∀ (q r : Q), ((factorSet P s q r).toMul : B) = s q * s r * (s (q * r))⁻¹

def FactorSetNormalized : Prop :=
  (∀ q : Q, factorSet P s 1 q = 0) ∧ (∀ q : Q, factorSet P s q 1 = 0)

def SectionCoordinatesFormula : Prop :=
  ∀ (a : A) (q : Q), sectionCoordinates P s (a, q) = (a.toMul : B) * s q

def SectionCoordinatesInverse : Prop :=
  ∀ b : B, (sectionCoordinates P s).symm b = (kernelCoordinate P s b, P.pi b)

variable [IsMulCommutative P.kernel]

local instance kernelAction : DistribMulAction Q A := P.quotientKernelActionValue

def FactorSetIdentity : Prop :=
  ∀ q r t : Q, factorSet P s q r + factorSet P s (q * r) t =
    q • factorSet P s r t + factorSet P s q (r * t)

def FactorCocycleFormula : Prop :=
  ∀ q r : Q, (factorCocycle P s).val.val ![q, r] = factorSet P s q r

def SectionCoordinatesMul : Prop :=
  ∀ (a b : A) (q r : Q),
    sectionCoordinates P s (a, q) * sectionCoordinates P s (b, r) =
      sectionCoordinates P s (a + q • b + factorSet P s q r, q * r)

def FactorSetChange : Prop :=
  ∀ (s' : NormalizedSection P) (b : Q → A),
    (∀ q, s' q = (b q).toMul.val * s q) →
    ∀ q r, factorSet P s' q r =
      factorSet P s q r + (b q + q • b r - b (q * r))

def ContinuousClassOfSection : Prop :=
  continuousClass Q A 2 (factorCocycle P s) = continuousExtensionClass P

def OrdinaryClassOfSection : Prop :=
  groupCohomology.π (integralRepresentation.{w,v,max w v} Q A) 2
    (ordinaryCyclesMk.{w,v,0} Q A 2 (factorCocycle P s)) = extensionClass P

def OrdinaryClassComparison : Prop :=
  ∃ e : ContinuousH Q A 2 ≃+ groupCohomology (integralRepresentation.{w,v,max w v} Q A) 2,
    _root_.GaloisFormalization.GH.Specification.IsOrdinaryClassComparison.{w,v,0} Q A 2 e ∧
    e (continuousExtensionClass P) = extensionClass P

def ContinuousClassZeroIffSplit : Prop :=
  continuousExtensionClass P = 0 ↔ isSplitValue P

def ExtensionClassZeroIffSplit : Prop :=
  extensionClass P = 0 ↔ isSplitValue P

private abbrev forEveryProblem
    (statement : ∀ {Γ : Type u} {B : Type v} {Q : Type w}
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
      [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
      [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
      [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q],
      FiniteEmbeddingProblem Γ B Q → Prop) : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q), statement P

def FactorSetFormulaStatement : Prop :=
  forEveryProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, FactorSetFormula P s

def FactorSetNormalizedStatement : Prop :=
  forEveryProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, FactorSetNormalized P s

def SectionCoordinatesFormulaStatement : Prop :=
  forEveryProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, SectionCoordinatesFormula P s

def SectionCoordinatesInverseStatement : Prop :=
  forEveryProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, SectionCoordinatesInverse P s

def FactorSetIdentityStatement : Prop :=
  forEveryProblem.{u,v,w} fun P =>
    ∀ (s : NormalizedSection P) [IsMulCommutative P.kernel], FactorSetIdentity P s

def FactorCocycleFormulaStatement : Prop :=
  forEveryProblem.{u,v,w} fun P =>
    ∀ (s : NormalizedSection P) [IsMulCommutative P.kernel], FactorCocycleFormula P s

def SectionCoordinatesMulStatement : Prop :=
  forEveryProblem.{u,v,w} fun P =>
    ∀ (s : NormalizedSection P) [IsMulCommutative P.kernel], SectionCoordinatesMul P s

def FactorSetChangeStatement : Prop :=
  forEveryProblem.{u,v,w} fun P =>
    ∀ (s : NormalizedSection P) [IsMulCommutative P.kernel], FactorSetChange P s

def ContinuousClassOfSectionStatement : Prop :=
  forEveryProblem.{u,v,w} fun P =>
    ∀ (s : NormalizedSection P) [IsMulCommutative P.kernel], ContinuousClassOfSection P s

def OrdinaryClassOfSectionStatement : Prop :=
  forEveryProblem.{u,v,w} fun P =>
    ∀ (s : NormalizedSection P) [IsMulCommutative P.kernel], OrdinaryClassOfSection P s

def OrdinaryClassComparisonStatement : Prop :=
  forEveryProblem.{u,v,w} fun P => ∀ [IsMulCommutative P.kernel], OrdinaryClassComparison P

def ContinuousClassZeroIffSplitStatement : Prop :=
  forEveryProblem.{u,v,w} fun P => ∀ [IsMulCommutative P.kernel], ContinuousClassZeroIffSplit P

def ExtensionClassZeroIffSplitStatement : Prop :=
  forEveryProblem.{u,v,w} fun P => ∀ [IsMulCommutative P.kernel], ExtensionClassZeroIffSplit P

end Specification

end

end Specs.GaloisFormalization.IG.FiniteEmbeddingProblem
