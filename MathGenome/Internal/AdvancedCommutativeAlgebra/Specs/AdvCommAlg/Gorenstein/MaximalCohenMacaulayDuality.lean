import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.HomDualPreservesMCM

/-! GC-12, paper.tex:4775–4822. The dual is ordinary Hom with values in the
canonical module. All module predicates include the zero module. Evaluation
and scalar multiplication are specified as maps, not arbitrary isomorphisms. -/
noncomputable section
universe u
namespace AdvCommAlg.Gorenstein.MCMDualitySpec

abbrev closureType : Prop := HomDualSpec.preservesMCMType.{u}

def bidualityType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R M →
    ∃ e : M ≃ₗ[R] ((M →ₗ[R] W) →ₗ[R] W),
      e.toLinearMap = envelopeEvaluation R W M

def exactnessType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    ∀ (A B C : Type u) [AddCommGroup A] [Module R A]
      [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
      [Module.Finite R A] [Module.Finite R B] [Module.Finite R C],
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R A →
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R B →
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R C →
    ∀ (f : A →ₗ[R] B) (g : B →ₗ[R] C),
      Function.Injective f → Function.Surjective g → Function.Exact f g →
      Function.Injective (LinearMap.lcomp R W g) ∧
      Function.Surjective (LinearMap.lcomp R W f) ∧
      Function.Exact (LinearMap.lcomp R W g) (LinearMap.lcomp R W f)

abbrev naturalityType : Prop := FiniteLengthDualitySpec.naturality.{u}
abbrev triangleType : Prop := FiniteLengthDualitySpec.triangle.{u}

def fullyFaithfulType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    ∀ (M N : Type u) [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N],
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R M →
    CohenMacaulay.Specs.MaximalCohenMacaulayValue R N →
    Function.Bijective (fun f : M →ₗ[R] N => LinearMap.lcomp R W f)

/-- An algebra isomorphism whose underlying map is the scalar action. -/
def scalarType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    ∃ e : R ≃ₐ[R] Module.End R W, ∀ (r : R) (w : W), e r w = r • w

/-- Closure and exactness, with natural self-inverse evaluation, full faithfulness,
and the scalar algebra identification. These give essential surjectivity too:
the dual of any finite MCM module is a preimage of that module. -/
def exactDualityType : Prop :=
  closureType.{u} ∧ exactnessType.{u} ∧ bidualityType.{u} ∧ naturalityType.{u} ∧
    fullyFaithfulType.{u} ∧ triangleType.{u} ∧ scalarType.{u}

end AdvCommAlg.Gorenstein.MCMDualitySpec
