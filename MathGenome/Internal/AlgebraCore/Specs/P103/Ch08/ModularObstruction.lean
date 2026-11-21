import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.RepresentationModules

/-! The augmentation of the finite-support group algebra, and the general
modular obstruction for the left regular representation. -/
noncomputable section
universe u v
namespace P103.Ch08
open scoped MonoidAlgebra
namespace Specs

/-- Sum of coefficients, as a linear map on the original group algebra. -/
def augmentationMap (k : Type u) (G : Type v) [Field k] [Group G] : k[G] →ₗ[k] k :=
  Finsupp.linearCombination k (fun _ : G => (1 : k)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

def augmentationType : Type (max (u + 1) (v + 1)) :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G], k[G] →ₗ[k] k

def augmentationValue : augmentationType.{u,v} :=
  fun {k G} _ _ => augmentationMap k G

def augmentationFormulaType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (x : k[G]),
    augmentationMap k G x = x.coeff.sum (fun _ c => c)

def augmentationSurjectiveType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G],
    Function.Surjective (augmentationMap k G)

def augmentationEquivariantType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] (g : G) (x : k[G]),
    augmentationMap k G (Representation.leftRegular k G g x) =
      Representation.trivial k G k g (augmentationMap k G x)

/-- No equivariant k-linear right inverse exists in modular characteristic.
`Finite G` imposes no chosen enumeration of the finite group. -/
def augmentationNoSectionType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] [Finite G],
    (Nat.card G : k) = 0 →
    ¬ ∃ s : (Representation.trivial k G k).IntertwiningMap
      (Representation.leftRegular k G),
      Function.RightInverse s (augmentationMap k G)

end Specs
end P103.Ch08
