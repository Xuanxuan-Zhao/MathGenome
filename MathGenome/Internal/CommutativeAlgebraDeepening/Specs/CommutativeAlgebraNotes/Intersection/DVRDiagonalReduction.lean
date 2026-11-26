import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.DVRExteriorTensorResolution
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorDimensionAndMultiplicity
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport

namespace CommutativeAlgebraNotes.Intersection.DVRDiagonalReduction.Spec

open CategoryTheory IsLocalRing ExteriorTensorProduct DVRExteriorTensorResolution
open PowerSeriesDiagonal (diagonalReduction restrictDiagonal difference)
open IsolatedTorSupport.Specs (Tor)
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open scoped TensorProduct ExteriorTensorProduct DVRExteriorTensorResolution

universe u v w

noncomputable section

/-- Multiplication by the uniformizer remains injective on the exterior product. -/
def UniformizerInjective : Prop :=
  DVRExteriorTensorResolution.Spec.DiagonalUniformizerInjective.{u,v,w}

/-- Specialization of the exterior product to the residue field, on pure tensors. -/
def SpecialFibre : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (π : V), Irreducible π → ∀ (a : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (X V a) M] [AddCommGroup N] [Module (X V a) N],
    let σ := Fin a ⊕ YIndex a
    let T := ExteriorTensorProduct.Spec.diagonalValue V a M N
    let Tk := ExteriorTensorProduct.Spec.productValue (ResidueField V) a a
      (Fibre V (Fin a) M) (Fibre V (YIndex a) (OnY N))
    letI : Module (S V a a) Tk := Module.compHom Tk (reduce V σ)
    ∃ e : QuotSMulTop (MvPowerSeries.C π : S V a a) T ≃ₗ[S V a a] Tk,
      ∀ (s : S V a a) (m : M) (n : N),
        e (Submodule.Quotient.mk ((s ⊗ₜ[X V a] m) ⊗ₜ[Y V a] toY n)) =
          ((reduce V σ s) ⊗ₜ[X (ResidueField V) a] fibreMk V (Fin a) m)
            ⊗ₜ[Y (ResidueField V) a] fibreMk V (YIndex a) (toY n)

/-- The dimension formula in additive form, so dimensions need no truncated subtraction. -/
def Dimension : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (π : V), Irreducible π → ∀ (a : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (X V a) M] [Module.Finite (X V a) M] [Nontrivial M]
    [AddCommGroup N] [Module (X V a) N] [Module.Finite (X V a) N] [Nontrivial N],
    Function.Injective (fun m : M => (MvPowerSeries.C π : X V a) • m) →
    Function.Injective (fun n : N => (MvPowerSeries.C π : X V a) • n) →
      moduleDimensionValue (S V a a) (ExteriorTensorProduct.Spec.diagonalValue V a M N) + 1 =
        moduleDimensionValue (X V a) M + moduleDimensionValue (X V a) N

/-- In degree zero the diagonal quotient is the ordinary tensor product. -/
def TensorQuotient : Prop :=
  PowerSeriesDiagonal.Spec.TensorQuotient.{u,v,w}

/-- Koszul homology computes ordinary Tor, with the joint-ring action given by
identifying the two sets of variables on the Tor side. -/
def KoszulHomologyTor : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (π : V), Irreducible π → ∀ (a : ℕ) (M N : ModuleCat.{u} (X V a))
    [Module.Finite (X V a) M] [Nontrivial M]
    [Module.Finite (X V a) N] [Nontrivial N],
    Function.Injective (fun m : M => (MvPowerSeries.C π : X V a) • m) →
    Function.Injective (fun n : N => (MvPowerSeries.C π : X V a) • n) →
    ∀ i : ℕ, Nonempty
      (AdvCommAlg.Koszul.homology (PowerSeriesDiagonal.exteriorPair M N)
          (List.ofFn (difference V a)) i ≃ₗ[S V a a]
        ↥((restrictDiagonal V a).obj (ModuleCat.of (X V a) (Tor M N i))))

end

end CommutativeAlgebraNotes.Intersection.DVRDiagonalReduction.Spec
