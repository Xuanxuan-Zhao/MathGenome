import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperMatrices
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Specs.LieNotes.SuperRestricted.SuperRankOneSimples

open _root_.LieNotes.SuperRestricted
open Specs.LieNotes.SuperRestricted.SuperMatrices
  (Mat gradingValue bracketValue zValue hValue eValue fValue)

universe u v

abbrev Algebra := LieSuperalgebra ℂ (Mat ℂ)

/-- The two data fields of the matrix Lie superalgebra of SR02. -/
def MatrixModel (L : Algebra) : Prop :=
  L.grading = gradingValue ℂ ∧ L.bracket = bracketValue ℂ

variable {L : Algebra}
variable {M : Type u} [AddCommGroup M] [Module ℂ M] {G : Grading ℂ M}
variable {N : Type v} [AddCommGroup N] [Module ℂ N] {J : Grading ℂ N}

def Stable (A : GradedModule L G) (S : Submodule ℂ M) : Prop :=
  ∀ (x : Mat ℂ) ⦃m : M⦄, m ∈ S → A.act x m ∈ S

def IsGraded (G : Grading ℂ M) (S : Submodule ℂ M) : Prop :=
  ∀ m ∈ S, ∃ a ∈ G.piece 0, ∃ b ∈ G.piece 1, a ∈ S ∧ b ∈ S ∧ a + b = m

/-- Simplicity in the parity-preserving category includes nonzero underlying space. -/
def Simple (A : GradedModule L G) : Prop :=
  (∃ m : M, m ≠ 0) ∧ ∀ S : Submodule ℂ M,
    IsGraded G S → Stable A S → S = ⊥ ∨ S = ⊤

/-- A bijective graded intertwiner. Its inverse preserves parity by uniqueness
of the decomposition into the two grading pieces. -/
def GradedIso (A : GradedModule L G) (B : GradedModule L J) : Prop :=
  ∃ T : GradedModule.Hom A B, Function.Bijective T.toLinearMap

/-- The one-dimensional form is represented by (w=0). In the other case the
two vectors span and the action of (e) forces (w) to be nonzero. -/
structure Form (A : GradedModule L G) (γ lam : ℂ) (p : ZMod 2) where
  v : M
  w : M
  v_ne : v ≠ 0
  v_mem : v ∈ G.piece p
  w_mem : w ∈ G.piece (1 + p)
  generates : (ℂ ∙ v) ⊔ (ℂ ∙ w) = ⊤
  w_zero : γ = 0 → w = 0
  hv : A.act (hValue ℂ) v = lam • v
  hw : A.act (hValue ℂ) w = (lam - 1) • w
  fv : A.act (fValue ℂ) v = w
  fw : A.act (fValue ℂ) w = 0
  ev : A.act (eValue ℂ) v = 0
  ew : A.act (eValue ℂ) w = γ • v
  zv : A.act (zValue ℂ) v = γ • v
  zw : A.act (zValue ℂ) w = γ • w

def exhaustType : Prop :=
  ∀ {L : Algebra}, MatrixModel L →
    ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
      {G : Grading ℂ M} (A : GradedModule L G), Simple A →
    ∃ (γ lam : ℂ) (p : ZMod 2),
      (∀ m : M, A.act (zValue ℂ) m = γ • m) ∧ Nonempty (Form A γ lam p)

def existenceType : Prop :=
  ∀ {L : Algebra}, MatrixModel L → ∀ (γ lam : ℂ) (p : ZMod 2),
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (_ : FiniteDimensional ℂ M)
      (G : Grading ℂ M) (A : GradedModule L G), Simple A ∧ Nonempty (Form A γ lam p)

def formsSimpleType : Prop :=
  ∀ {L : Algebra}, MatrixModel L →
    ∀ {M : Type u} [AddCommGroup M] [Module ℂ M]
      {G : Grading ℂ M} {A : GradedModule L G} {γ lam : ℂ} {p : ZMod 2},
      Form A γ lam p → Simple A

def basisType : Prop :=
  ∀ {L : Algebra} {M : Type u} [AddCommGroup M] [Module ℂ M]
    {G : Grading ℂ M} {A : GradedModule L G} {γ lam : ℂ} {p : ZMod 2}
    (P : Form A γ lam p),
    (γ = 0 → ∃ b : Module.Basis (Fin 1) ℂ M, b 0 = P.v) ∧
    (γ ≠ 0 → ∃ b : Module.Basis (Fin 2) ℂ M, b 0 = P.v ∧ b 1 = P.w)

def isomorphicType : Prop :=
  ∀ {L : Algebra}, MatrixModel L →
    ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] {G : Grading ℂ M}
      {N : Type v} [AddCommGroup N] [Module ℂ N] {J : Grading ℂ N}
      {A : GradedModule L G} {B : GradedModule L J}
      {γ lam γ' lam' : ℂ} {p p' : ZMod 2},
    Form A γ lam p → Form B γ' lam' p' →
    (GradedIso A B ↔ γ = γ' ∧ lam = lam' ∧ p = p')

/-- Changing the positive odd root replaces its kernel by the other highest line. -/
def oppositeType : Prop :=
  ∀ {L : Algebra} {M : Type u} [AddCommGroup M] [Module ℂ M]
    {G : Grading ℂ M} {A : GradedModule L G} {γ lam : ℂ} {p : ZMod 2}
    (P : Form A γ lam p),
    (A.act (eValue ℂ)).ker = ℂ ∙ P.v ∧
    (γ = 0 → (A.act (fValue ℂ)).ker = ℂ ∙ P.v ∧
      P.v ≠ 0 ∧ P.v ∈ G.piece p ∧ A.act (hValue ℂ) P.v = lam • P.v) ∧
    (γ ≠ 0 → (A.act (fValue ℂ)).ker = ℂ ∙ P.w ∧
      P.w ≠ 0 ∧ P.w ∈ G.piece (1 + p) ∧ 1 + p ≠ p ∧
      A.act (hValue ℂ) P.w = (lam - 1) • P.w)

end Specs.LieNotes.SuperRestricted.SuperRankOneSimples
