import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedNorm

open scoped Polynomial RatFunc LaurentSeries WithZero

namespace LinearAlgebraicGroups.Arithmetic.FunctionFieldForms

universe u v w

/-- The homogeneous degree-`d` isotropy bound over `K`, including the zero polynomial. -/
def HasIsotropyBound (K : Type u) [Field K] (d : ℕ) : Prop :=
  ∀ (n : ℕ), d ^ 2 < n → ∀ f : MvPolynomial (Fin n) K, f.IsHomogeneous d →
    ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0

/-- Every finite extension of a rational function field over a finite field satisfies
the degree-squared bound. The finite-extension presentation need not be separable. -/
def GlobalBound : Prop :=
  ∀ {K : Type u} [Field K] {k : Type v} [Field k] [Finite k]
    [Algebra k⟮X⟯ K] [FiniteDimensional k⟮X⟯ K] (d : ℕ), 0 < d →
    HasIsotropyBound K d

/-- The quadratic bound over the Laurent series field of any finite field. -/
def LaurentQuadraticBound : Prop :=
  ∀ (k : Type u) [Field k] [Finite k], HasIsotropyBound k⸨X⸩ 2

/-- In positive characteristic the actual residue field embeds as a coefficient
field. A uniformizer and this embedding identify the field with the Laurent
series field, with the valuation normalized to send the uniformizer to `exp (-1)`. -/
def LaurentPresentation : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [CharP F p],
    let O := LocalDivisionAlgebras.Integers F
    let k := IsLocalRing.ResidueField O
    ∃ s : k →+* O, (IsLocalRing.residue O).comp s = RingHom.id k ∧
      ∃ (t : F) (e : k⸨X⸩ ≃+* F),
        LocalDivisionAlgebras.baseValue F t = WithZero.exp (-1) ∧
        e (HahnSeries.single 1 1) = t ∧
        (∀ a : k, e (HahnSeries.C a) = (s a : F)) ∧
        ∀ a : k⸨X⸩, LocalDivisionAlgebras.baseValue F (e a) = Valued.v a

/-- The quadratic bound over every equal-characteristic nonarchimedean local field. -/
def LocalQuadraticBound : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [CharP F p],
    HasIsotropyBound F 2

/-- The local bound at every finite place of a global function field. -/
def CompletionQuadraticBound : Prop :=
  ∀ {K : Type u} [Field K] {k : Type v} [Field k] [Finite k] [Algebra k K]
    (_t : SeparatingParameter k K) (w : FunctionPlace K),
    HasIsotropyBound w.Completion 2

/-- The reduced norm of a quaternion division algebra over a global function
field represents every nonzero scalar. -/
def GlobalQuaternionNorm : Prop :=
  ∀ {K : Type u} [Field K] {k : Type v} [Field k] [Finite k]
    [Algebra k⟮X⟯ K] [FiniteDimensional k⟮X⟯ K]
    {B : Type w} [DivisionRing B] [Algebra K B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple K B),
    _root_.Specs.RM03.CSA.degree K B = 2 →
    ∀ a : K, a ≠ 0 → ∃ x : Bˣ, _root_.Specs.RM03.CSA.reducedNorm hB (x : B) = a

/-- The reduced norm of a quaternion division algebra over an equal-characteristic
nonarchimedean local field represents every nonzero scalar. -/
def LocalQuaternionNorm : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [CharP F p]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    _root_.Specs.RM03.CSA.degree F B = 2 →
    ∀ a : F, a ≠ 0 → ∃ x : Bˣ, _root_.Specs.RM03.CSA.reducedNorm hB (x : B) = a

end LinearAlgebraicGroups.Arithmetic.FunctionFieldForms
