import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Rep.Iso
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions

/-! HA A10, lines 3403–3416 and 3440–3447. All groups are discrete, and
`k` is an arbitrary commutative ring. Right modules are modules over the opposite.
The scalar restriction in `coefficientRepresentation` imposes no extra hypothesis. -/
noncomputable section
open CategoryTheory
open scoped MonoidAlgebra
set_option backward.isDefEq.respectTransparency false
namespace AdvancedHomologicalAlgebra.GroupCoinvariants
universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

/-- The augmentation sends each group element to one. -/
def augmentation : k[G] →+* k :=
  MonoidAlgebra.liftNCRingHom (RingHom.id k) (1 : G →* k) (fun _ _ => Commute.all _ _)

/-- The trivial right module, with its usual underlying `k`-module. -/
@[nolint unusedArguments]
def TrivialRight (k : Type u) (G : Type v) := k
instance : One (TrivialRight k G) := inferInstanceAs (One k)
instance : AddCommGroup (TrivialRight k G) := inferInstanceAs (AddCommGroup k)
instance : Module k (TrivialRight k G) := inferInstanceAs (Module k k)
instance : Module k[G]ᵐᵒᵖ (TrivialRight k G) :=
  Module.compHom k ((augmentation k G).fromOpposite (fun _ _ => Commute.all _ _))
instance : SMulCommClass k k[G]ᵐᵒᵖ (TrivialRight k G) where
  smul_comm a r b := mul_left_comm a ((augmentation k G) r.unop) b

/-- Its underlying scalar is an element of `k`. -/
def trivialScalar (a : TrivialRight k G) : k := a

/-- Every left group-algebra module, with scalars restricted to `k`. -/
abbrev coefficientRepresentation (M : ModuleCat.{w} k[G]) :=
  Representation.ofModule (k := k) (G := G) M

/-- The span of `gm-m`, over `k`, not merely an additive subgroup. -/
abbrev coinvariantRelations (M : ModuleCat.{w} k[G]) :=
  Representation.Coinvariants.ker (coefficientRepresentation k G M)

/-- `M_G = M / span_k {gm-m}`. -/
abbrev Coinvariants (M : ModuleCat.{w} k[G]) :=
  Representation.Coinvariants (coefficientRepresentation k G M)

abbrev quotientMap (M : ModuleCat.{w} k[G]) :=
  Representation.Coinvariants.mk (coefficientRepresentation k G M)

/-- The actual noncommutative right-left balanced tensor. -/
abbrev TrivialTensor (M : ModuleCat.{w} k[G]) :=
  P103.BalancedTensor.Tensor k[G] (TrivialRight k G) M

instance (M : ModuleCat.{w} k[G]) : Module k (TrivialTensor k G M) :=
  P103.BalancedTensor.leftModule

/-- The coinvariant functor on all left group-algebra modules. -/
def coinvariantsFunctor : ModuleCat.{w} k[G] ⥤ ModuleCat k :=
  Rep.ofModuleMonoidAlgebra ⋙ Rep.coinvariantsFunctor k G

abbrev coinvariantsMap {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) :=
  (coinvariantsFunctor k G).map f

/-- Coefficient group homology in every nonnegative degree. The imported Tor
uses projective right resolutions and the same balanced tensor as above. -/
abbrev GroupHomology (M : ModuleCat.{w} k[G]) (n : ℕ) :=
  P103.Ch11.ExtTorDefinitions.Tor k[G]
    (ModuleCat.of k[G]ᵐᵒᵖ (TrivialRight k G)) M n

namespace Specification

/-- The expected value is the quotient by the actual k-linear action relations. -/
def coinvariantsType :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ModuleCat.{w} k[G] → Type w

def coinvariantsValue : coinvariantsType.{u,v,w} :=
  fun k G _ _ M => Coinvariants k G M

/-- The expected value uses Tor of the trivial RIGHT module and the original
LEFT module, without treating the group ring as commutative. -/
def groupHomologyType :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ModuleCat.{w} k[G] → ℕ → Type (max u v w)

def groupHomologyValue : groupHomologyType.{u,v,w} :=
  fun k G _ _ M n =>
    P103.Ch11.ExtTorDefinitions.Tor k[G]
      (ModuleCat.of k[G]ᵐᵒᵖ (TrivialRight k G)) M n

/-- A family of linear isomorphisms with both canonical formulas and the full
naturality square for every homomorphism of left group-algebra modules. -/
def tensorComparisonType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G],
    ∃ e : ∀ M : ModuleCat.{w} k[G], Coinvariants k G M ≃ₗ[k] TrivialTensor k G M,
      (∀ (M : ModuleCat.{w} k[G]) (m : RestrictScalars k k[G] M),
        e M (quotientMap k G M m) =
          P103.BalancedTensor.tmul k[G] (1 : TrivialRight k G)
            (RestrictScalars.addEquiv k k[G] M m)) ∧
      (∀ (M : ModuleCat.{w} k[G]) (a : TrivialRight k G) (m : M),
        (e M).symm (P103.BalancedTensor.tmul k[G] a m) =
          trivialScalar k G a • quotientMap k G M
            ((RestrictScalars.addEquiv k k[G] M).symm m)) ∧
      (∀ {M N : ModuleCat.{w} k[G]} (f : M ⟶ N) (z : Coinvariants k G M),
        e N (coinvariantsMap k G f z) =
          P103.BalancedTensor.map LinearMap.id f.hom (e M z))

/-- Exact at the middle and onto at the right, for every right exact pair of
coefficient maps. No injectivity hypothesis on the first map is needed. -/
def rightExactType : Prop :=
  ∀ (k : Type u) (G : Type v) [CommRing k] [Group G]
    {L M N : ModuleCat.{w} k[G]} (f : L ⟶ M) (g : M ⟶ N),
    Function.Exact f g → Function.Surjective g →
      Function.Exact (coinvariantsMap k G f) (coinvariantsMap k G g) ∧
        Function.Surjective (coinvariantsMap k G g)

end Specification
end AdvancedHomologicalAlgebra.GroupCoinvariants
