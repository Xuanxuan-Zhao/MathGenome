import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Hypersurfaces
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions

/-! ET-16, paper.tex 1978–1984. The same literal ring k[X]/(X²) is
used with its k-algebra structure and its quotient k[X]-algebra structure.
There is no restriction on the characteristic of the field. -/
namespace Specs.AdvCommAlg.Etale.DualNumbers

universe u
noncomputable section
open Specs.AdvCommAlg.Differentials

abbrev relationIdeal (K : Type u) [CommRing K] : Ideal (Polynomial K) :=
  Ideal.span {Polynomial.X ^ 2}

/-- The second base structure is the quotient map, rather than evaluation in k. -/
instance polynomialBaseAlgebra (K : Type u) [CommRing K] :
    Algebra (Polynomial K) (DualQuotient K) :=
  inferInstanceAs (Algebra (Polynomial K) (Polynomial K ⧸ relationIdeal K))

def baseMapDescription : Prop := ∀ (K : Type u) [Field K],
  algebraMap (Polynomial K) (DualQuotient K) Polynomial.X = epsilon K ∧
  RingHom.ker (algebraMap (Polynomial K) (DualQuotient K)) = relationIdeal K

def fieldDifferentialsNonzero : Prop := ∀ (K : Type u) [Field K],
  ¬ Subsingleton (KaehlerDifferential K (DualQuotient K))

def polynomialDifferentialsZero : Prop := ∀ (K : Type u) [Field K],
  Subsingleton (KaehlerDifferential (Polynomial K) (DualQuotient K))

def kernelNotIdempotent : Prop := ∀ (K : Type u) [Field K],
  (relationIdeal K) ^ 2 ≠ relationIdeal K

def polynomialFinitelyPresentedUnramified : Prop := ∀ (K : Type u) [Field K],
  finitelyPresentedUnramifiedValue (Polynomial K) (DualQuotient K)

def polynomialNotEtale : Prop := ∀ (K : Type u) [Field K],
  ¬ etaleValue (Polynomial K) (DualQuotient K)

def fieldNotUnramified : Prop := ∀ (K : Type u) [Field K],
  ¬ unramifiedValue K (DualQuotient K)

end
end Specs.AdvCommAlg.Etale.DualNumbers
