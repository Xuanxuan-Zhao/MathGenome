import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Presentation
import Mathlib.Algebra.Algebra.Opposite

noncomputable section

namespace Specs.LieNotes.Quantum.AntipodeMap

open Specs.LieNotes.Quantum.Presentation
open MulOpposite

universe u v

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

/-- The antipode is an algebra homomorphism into the multiplicative opposite. -/
def GeneratorFormulas (C : Cartan A T) (S : U C →ₐ[A] (U C)ᵐᵒᵖ) : Prop :=
  (∀ t, (S (cartan C t)).unop = cartan C (C.kappa t)) ∧
  (∀ i, (S (E C i)).unop = -(cartan C (↑((C.K i)⁻¹)) * E C i)) ∧
  (∀ i, (S (F C i)).unop = -(F C i * cartan C (↑(C.K i))))

def SquareFormulas (C : Cartan A T) (S : U C →ₐ[A] (U C)ᵐᵒᵖ) : Prop :=
  (∀ t, (S (S (cartan C t)).unop).unop = cartan C t) ∧
  (∀ i, (S (S (E C i)).unop).unop = (↑(C.q ^ (-2 : ℤ)) : A) • E C i) ∧
  (∀ i, (S (S (F C i)).unop).unop = (↑(C.q ^ (2 : ℤ)) : A) • F C i)

def genericAntipodeProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    let C := generic q hq
    ∃! S : U C →ₐ[k] (U C)ᵐᵒᵖ,
      GeneratorFormulas C S ∧ SquareFormulas C S ∧ Function.Bijective S ∧
        ∀ i, (S (cartan C (↑(C.K i)))).unop = cartan C (↑((C.K i)⁻¹))

def indeterminateAntipodeProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    let C := indeterminate k
    ∃! S : U C →ₐ[RatFunc k] (U C)ᵐᵒᵖ,
      GeneratorFormulas C S ∧ SquareFormulas C S ∧ Function.Bijective S ∧
        ∀ i, (S (cartan C (↑(C.K i)))).unop = cartan C (↑((C.K i)⁻¹))

def truncatedAntipodeProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (N : ℕ),
    let C := truncated k N
    ∃! S : Uₙ k N →ₐ[Truncations.A k N] (Uₙ k N)ᵐᵒᵖ,
      GeneratorFormulas C S ∧ SquareFormulas C S ∧ Function.Bijective S ∧
        (∀ i, (S (cartan C (MvPolynomial.X i))).unop = -(cartan C (MvPolynomial.X i))) ∧
        (∀ i, (S (cartan C (↑(C.K i)))).unop = cartan C (↑((C.K i)⁻¹)))

def reduceAntipodeProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {M N : ℕ} (h : M ≤ N)
    (SN : Uₙ k N →ₐ[Truncations.A k N] (Uₙ k N)ᵐᵒᵖ)
    (SM : Uₙ k M →ₐ[Truncations.A k M] (Uₙ k M)ᵐᵒᵖ),
    GeneratorFormulas (truncated k N) SN → GeneratorFormulas (truncated k M) SM →
    ∀ x, reduce h (SN x).unop = (SM (reduce h x)).unop

end Specs.LieNotes.Quantum.AntipodeMap
