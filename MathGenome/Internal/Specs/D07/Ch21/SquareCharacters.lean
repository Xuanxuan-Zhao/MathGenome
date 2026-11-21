import MathGenome.Internal.Specs.D07.Ch21.DualTensor
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Projection

/-!
K07.21.square_characters (paper.tex:6226–6250).
We use the images of the two ordinary binary tensor projectors as the square
models. `QuotientModels` explicitly identifies them with the quotients by the
symmetric and alternating relations, including the normalization on generators.
No nonzero-space assumption is made. The character assertions apply to every
finite-dimensional complex representation of every finite group.
-/
namespace Specs.D07.Ch21.SquareCharacters
universe u v w
noncomputable section
open scoped TensorProduct

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

abbrev TensorSquare := V ⊗[ℂ] V

def flip : Module.End ℂ (TensorSquare V) :=
  (TensorProduct.comm ℂ V V).toLinearMap

/-- s = 1 gives (I+F)/2, s = -1 gives (I-F)/2. -/
def projector (s : ℂ) : Module.End ℂ (TensorSquare V) :=
  (2 : ℂ)⁻¹ • (1 + s • flip V)

abbrev squareSpace (s : ℂ) := LinearMap.range (projector V s)
abbrev SymmetricSquare := squareSpace V 1
abbrev ExteriorSquare := squareSpace V (-1)

def symmetricRelations : Submodule ℂ (TensorSquare V) :=
  Submodule.span ℂ {x | ∃ a b : V, x = a ⊗ₜ[ℂ] b - b ⊗ₜ[ℂ] a}

def exteriorRelations : Submodule ℂ (TensorSquare V) :=
  Submodule.span ℂ {x | ∃ a : V, x = a ⊗ₜ[ℂ] a}

abbrev SymmetricQuotient := TensorSquare V ⧸ symmetricRelations V
abbrev ExteriorQuotient := TensorSquare V ⧸ exteriorRelations V

variable {V}

def squareSubrepresentation {G : Type v} [Group G]
    (ρ : Representation ℂ G V) (s : ℂ) : Subrepresentation (ρ.tprod ρ) where
  toSubmodule := squareSpace V s
  apply_mem_toSubmodule g := by
    rintro x ⟨y, rfl⟩
    refine ⟨(ρ.tprod ρ) g y, ?_⟩
    change projector V s (TensorProduct.map (ρ g) (ρ g) y) =
      TensorProduct.map (ρ g) (ρ g) (projector V s y)
    simp [projector, flip, TensorProduct.map_comm]

def squareRepresentation {G : Type v} [Group G]
    (ρ : Representation ℂ G V) (s : ℂ) : Representation ℂ G (squareSpace V s) :=
  (squareSubrepresentation ρ s).toRepresentation

abbrev symmetricRepresentation {G : Type v} [Group G] (ρ : Representation ℂ G V) :=
  squareRepresentation ρ 1
abbrev exteriorRepresentation {G : Type v} [Group G] (ρ : Representation ℂ G V) :=
  squareRepresentation ρ (-1)

def FlipLaws : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V],
    (∀ a b : V, flip V (a ⊗ₜ[ℂ] b) = b ⊗ₜ[ℂ] a) ∧
    flip V * flip V = 1 ∧
    ∀ A : Module.End ℂ V, Commute (TensorProduct.map A A) (flip V)

def ProjectorLaws : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V],
    IsIdempotentElem (projector V 1) ∧
    IsIdempotentElem (projector V (-1)) ∧
    projector V 1 + projector V (-1) = 1 ∧
    projector V 1 * projector V (-1) = 0 ∧
    projector V (-1) * projector V 1 = 0 ∧
    IsCompl (squareSpace V 1) (squareSpace V (-1)) ∧
    (∀ x : TensorSquare V, x ∈ squareSpace V 1 ↔ flip V x = x) ∧
    (∀ x : TensorSquare V, x ∈ squareSpace V (-1) ↔ flip V x = -x)

def QuotientModels : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V],
    (∃ e : SymmetricQuotient V ≃ₗ[ℂ] SymmetricSquare V,
      ∀ t, (e ((symmetricRelations V).mkQ t) : TensorSquare V) = projector V 1 t) ∧
    (∃ e : ExteriorQuotient V ≃ₗ[ℂ] ExteriorSquare V,
      ∀ t, (e ((exteriorRelations V).mkQ t) : TensorSquare V) = projector V (-1) t)

def SquareActionLaws : Prop :=
  ∀ (V : Type u) (G : Type v) [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (s : ℂ),
    (∀ g (x : squareSpace V s),
      (squareRepresentation ρ s g x : TensorSquare V) = (ρ.tprod ρ) g x) ∧
    squareRepresentation ρ s 1 = 1 ∧
    (∀ g h, squareRepresentation ρ s (g * h) =
      squareRepresentation ρ s g * squareRepresentation ρ s h) ∧
    (∀ g, squareRepresentation ρ s g * squareRepresentation ρ s g⁻¹ = 1 ∧
      squareRepresentation ρ s g⁻¹ * squareRepresentation ρ s g = 1)

/-- The image models carry precisely the actions induced on the two usual
relation quotients. The identifications are equivariant and normalized on all
tensor representatives, not just abstract vector-space isomorphisms. -/
def QuotientActions : Prop :=
  ∀ (V : Type u) (G : Type v) [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V),
    (∃ τ : Representation ℂ G (SymmetricQuotient V),
      ∃ e : τ.Equiv (symmetricRepresentation ρ),
        (∀ t, (e ((symmetricRelations V).mkQ t) : TensorSquare V) = projector V 1 t) ∧
        ∀ g t, τ g ((symmetricRelations V).mkQ t) =
          (symmetricRelations V).mkQ ((ρ.tprod ρ) g t)) ∧
    (∃ τ : Representation ℂ G (ExteriorQuotient V),
      ∃ e : τ.Equiv (exteriorRepresentation ρ),
        (∀ t, (e ((exteriorRelations V).mkQ t) : TensorSquare V) = projector V (-1) t) ∧
        ∀ g t, τ g ((exteriorRelations V).mkQ t) =
          (exteriorRelations V).mkQ ((ρ.tprod ρ) g t))

/-- In the internal direct sum of image and kernel, T has two diagonal
blocks, and TP has blocks T restricted to the image and zero. -/
def ProjectionBlocks : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E]
    (P T : Module.End ℂ E), IsIdempotentElem P → Commute T P →
    IsCompl (LinearMap.range P) (LinearMap.ker P) ∧
    ∃ (hR : ∀ x, x ∈ LinearMap.range P → T x ∈ LinearMap.range P)
      (hK : ∀ x, x ∈ LinearMap.ker P → T x ∈ LinearMap.ker P),
      (∀ (x : LinearMap.range P) (y : LinearMap.ker P),
        T ((x : E) + y) = (T.restrict hR x : E) + (T.restrict hK y : E)) ∧
      ∀ (x : LinearMap.range P) (y : LinearMap.ker P),
        (T * P) ((x : E) + y) = (T.restrict hR x : E)

/-- General trace-on-the-image identity; no assumption of invertibility on T. -/
def ProjectionTrace : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (P T : Module.End ℂ E), IsIdempotentElem P → Commute T P →
    ∃ h : ∀ x, x ∈ LinearMap.range P → T x ∈ LinearMap.range P,
      LinearMap.trace ℂ E (T * P) =
        LinearMap.trace ℂ (LinearMap.range P) (T.restrict h)

/-- Product-basis entries and their diagonal sum, with an arbitrary finite
basis (possibly empty). -/
def FlipMatrixTrace : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
    (ι : Type w) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) (A : Module.End ℂ V),
    (∀ i j : ι × ι,
      LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b)
          (TensorProduct.map A A * flip V) i j =
        LinearMap.toMatrix b b A i.1 j.2 * LinearMap.toMatrix b b A i.2 j.1) ∧
    LinearMap.trace ℂ (TensorSquare V) (TensorProduct.map A A * flip V) =
      ∑ i, ∑ j, LinearMap.toMatrix b b A i j * LinearMap.toMatrix b b A j i ∧
    (∑ i, ∑ j, LinearMap.toMatrix b b A i j * LinearMap.toMatrix b b A j i) =
      LinearMap.trace ℂ V (A * A)

def CharacterFormulas : Prop :=
  ∀ (V : Type u) (G : Type v) [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G),
    Ch17.Characters.characterValue ℂ G (SymmetricSquare V) (symmetricRepresentation ρ) g =
      (Ch17.Characters.characterValue ℂ G V ρ g ^ 2 +
        Ch17.Characters.characterValue ℂ G V ρ (g ^ 2)) / 2 ∧
    Ch17.Characters.characterValue ℂ G (ExteriorSquare V) (exteriorRepresentation ρ) g =
      (Ch17.Characters.characterValue ℂ G V ρ g ^ 2 -
        Ch17.Characters.characterValue ℂ G V ρ (g ^ 2)) / 2

end
end Specs.D07.Ch21.SquareCharacters
