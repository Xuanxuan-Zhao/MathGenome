import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CharacterConstructions

/-! Symmetric and exterior squares in the explicit degree-two quotient models.
All groups are arbitrary. The sole characteristic assumption is `2 ≠ 0`. -/
noncomputable section
universe u v w
namespace P103.Ch08.SquareSpecs

variable (k : Type u) (V : Type w) [Field k] [AddCommGroup V] [Module k V]

abbrev TensorSquare := TensorProduct k V V

def flip : Module.End k (TensorSquare k V) := (TensorProduct.comm k V V).toLinearMap

def symmetricRelations : Submodule k (TensorSquare k V) :=
  Submodule.span k {z | ∃ v w : V, z = TensorProduct.tmul k v w - TensorProduct.tmul k w v}

def exteriorRelations : Submodule k (TensorSquare k V) :=
  Submodule.span k {z | ∃ v : V, z = TensorProduct.tmul k v v}

abbrev SymmetricSquare := TensorSquare k V ⧸ symmetricRelations k V
abbrev ExteriorSquare := TensorSquare k V ⧸ exteriorRelations k V

def plusSpace : Submodule k (TensorSquare k V) :=
  LinearMap.ker (flip k V - LinearMap.id)

def minusSpace : Submodule k (TensorSquare k V) :=
  LinearMap.ker (flip k V + LinearMap.id)

def plusProjection : Module.End k (TensorSquare k V) :=
  (2 : k)⁻¹ • (LinearMap.id + flip k V)

def minusProjection : Module.End k (TensorSquare k V) :=
  (2 : k)⁻¹ • (LinearMap.id - flip k V)

variable {k V} {G : Type v} [Group G]

/-- Actual quotient actions, actual eigenspace actions, and the projection-induced
linear equivalences between them. The formulas specify the inherited actions on
all tensors, and equivariance is asserted for the very same equivalences. -/
structure SquareActions (ρ : Representation k G V) where
  symmetric : Representation k G (SymmetricSquare k V)
  exterior : Representation k G (ExteriorSquare k V)
  plus : Representation k G (plusSpace k V)
  minus : Representation k G (minusSpace k V)
  symmetricEquiv : SymmetricSquare k V ≃ₗ[k] plusSpace k V
  exteriorEquiv : ExteriorSquare k V ≃ₗ[k] minusSpace k V
  symmetric_action : ∀ g z,
    symmetric g ((symmetricRelations k V).mkQ z) =
      (symmetricRelations k V).mkQ (CharacterSpecs.tensorValue ρ ρ g z)
  exterior_action : ∀ g z,
    exterior g ((exteriorRelations k V).mkQ z) =
      (exteriorRelations k V).mkQ (CharacterSpecs.tensorValue ρ ρ g z)
  plus_action : ∀ g (z : plusSpace k V),
    (plus g z : TensorSquare k V) = CharacterSpecs.tensorValue ρ ρ g z
  minus_action : ∀ g (z : minusSpace k V),
    (minus g z : TensorSquare k V) = CharacterSpecs.tensorValue ρ ρ g z
  symmetric_projection : ∀ z,
    (symmetricEquiv ((symmetricRelations k V).mkQ z) : TensorSquare k V) =
      plusProjection k V z
  exterior_projection : ∀ z,
    (exteriorEquiv ((exteriorRelations k V).mkQ z) : TensorSquare k V) =
      minusProjection k V z
  symmetric_equivariant : ∀ g z,
    symmetricEquiv (symmetric g z) = plus g (symmetricEquiv z)
  exterior_equivariant : ∀ g z,
    exteriorEquiv (exterior g z) = minus g (exteriorEquiv z)

/-- Existence includes stability of both relation spaces and both eigenspaces,
with the usual quotient models and the specified half-sum/half-difference maps. -/
def constructionType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (h2 : (2 : k) ≠ 0) (ρ : Representation k G V), Nonempty (SquareActions ρ)

/-- The characters of these very quotient representations, for every group
element. In particular there are no finite-group or complex-field hypotheses. -/
def charactersType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (h2 : (2 : k) ≠ 0) (ρ : Representation k G V) (S : SquareActions ρ) (g : G),
    CharacterSpecs.characterValue S.symmetric g =
      (CharacterSpecs.characterValue ρ g ^ 2 + CharacterSpecs.characterValue ρ (g ^ 2)) / 2 ∧
    CharacterSpecs.characterValue S.exterior g =
      (CharacterSpecs.characterValue ρ g ^ 2 - CharacterSpecs.characterValue ρ (g ^ 2)) / 2

end P103.Ch08.SquareSpecs
