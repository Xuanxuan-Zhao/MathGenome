import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionHyperbolicRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionScalarCliffordLift

open CategoryTheory MulOpposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct commutatorElement

universe u v w

namespace LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinCharacteristicTwo

open _root_.Specs.RM03.CSA (isCentralSimple degree reducedNorm)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)
open LinearAlgebraicGroups.Arithmetic (GlobalFieldData SeparatingParameter)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn StrongApproximation)
open LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction (reducedTrace)
open CharacterDescent (Cocharacter)
open AdjointRepresentation (GroupPoints)
open IntegralModels (MatrixRealization)
open SymplecticDivisionForms (antiValue)
open SymplecticInvolutionModels (HermitianPairing quaternionConjugate)
open NontrialitarianSpinModels (DescendedQuadraticPair SpinModel HasFixedVectorVertex)
open CharacteristicTwoQuadraticPairs (ScalarClasses scalarClass refinement IsTraceOne)
open QuaternionSpinScaleCover
  (QuaternionHyperbolicPresentation quaternionScale spinVectorProjection spinScalePreimage)
open QuaternionHyperbolicRadicals (ComplementRefinement ActsOnColumns)
open QuaternionScalarCliffordLift (IsPairDiagonal)
open LinearAlgebraicGroups.CocharacterDynamics (oppositeCocharacter HasLimit)
open OppositeRadicals (IsNoncentral)

noncomputable section

section Columns

variable {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]
  {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V]
  {s : B ≃ₐ[F] Bᵐᵒᵖ}

/-- The polar form of the hyperbolic quaternion plane orthogonally summed with `V`. -/
def columnHermitian (h : HermitianPairing s V) (p q : B × V × B) : B :=
  antiValue s p.1 * q.2.2 + h.value p.2.1 q.2.1 + antiValue s p.2.2 * q.1

/-- The generalized quadratic form in hyperbolic column coordinates. -/
def columnQuadratic (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V)
    (p : B × V × B) : ScalarClasses F B :=
  scalarClass F (antiValue s p.1 * p.2.2) + refinement h ell p.2.1

def upper (h : HermitianPairing s V) (w₀ : V) (b : B) :
    B × V × B → B × V × B :=
  fun (x, y, z) => (x + h.value w₀ y + b * z, y + op z • w₀, z)

def lower (h : HermitianPairing s V) (w₀ : V) (b : B) :
    B × V × B → B × V × B :=
  fun (x, y, z) => (x, y + op x • w₀, z + h.value w₀ y + b * x)

def perpendicularRotation (h : HermitianPairing s V) (w₀ : V) (b : B) : V → V :=
  fun y => y + op (b⁻¹ * h.value w₀ y) • w₀

def weylWord (h : HermitianPairing s V) (w₀ : V) (b : B) :
    B × V × B → B × V × B :=
  lower h (op b⁻¹ • w₀) (antiValue s b)⁻¹ ∘ upper h w₀ b ∘
    lower h (op ((antiValue s b)⁻¹) • w₀) (antiValue s b)⁻¹

/-- The opposite radical formulas preserve the actual forms. The word acts
on both hyperbolic lines and the whole perpendicular summand. -/
def RadicalWords : Prop :=
  ∀ {F : Type u} [Field F] [CharP F 2] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {s : B ≃ₐ[F] Bᵐᵒᵖ}, (∀ a, antiValue s a = quaternionConjugate hB a) →
    ∀ {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] (h : HermitianPairing s V)
      (ell : V →ₗ[Bᵐᵒᵖ] V), IsTraceOne h ell →
    ∀ (w₀ : V) (b : B), scalarClass F b = refinement h ell w₀ →
      (∀ p q, columnHermitian h (upper h w₀ b p) (upper h w₀ b q) =
        columnHermitian h p q ∧ columnHermitian h (lower h w₀ b p) (lower h w₀ b q) =
        columnHermitian h p q) ∧
      (∀ p, columnQuadratic h ell (upper h w₀ b p) = columnQuadratic h ell p ∧
        columnQuadratic h ell (lower h w₀ b p) = columnQuadratic h ell p) ∧
      (b ≠ 0 →
        scalarClass F ((antiValue s b)⁻¹) = refinement h ell (op b⁻¹ • w₀) ∧
        scalarClass F ((antiValue s b)⁻¹) = refinement h ell (op ((antiValue s b)⁻¹) • w₀) ∧
        ∀ x y z, weylWord h w₀ b (x, y, z) =
          (b * z, perpendicularRotation h w₀ b y, (antiValue s b)⁻¹ * x))

/-- The full generalized quadratic isometry on the perpendicular summand
can be removed by finitely many of the displayed rank-one rotations. -/
def PerpendicularGeneration : Prop :=
  ∀ {F : Type u} [Field F] [CharP F 2] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {s : B ≃ₐ[F] Bᵐᵒᵖ}, (∀ a, antiValue s a = quaternionConjugate hB a) →
    ∀ {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] [Module.Finite Bᵐᵒᵖ V]
      (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V), IsTraceOne h ell →
    ∀ g : V ≃ₗ[Bᵐᵒᵖ] V,
      (∀ x, refinement h ell (g x) = refinement h ell x) →
      ∃ l : List (V × Bˣ),
        (∀ p ∈ l, scalarClass F (p.2 : B) = refinement h ell p.1) ∧
        ∀ y, g y = l.foldr (fun p y₀ => perpendicularRotation h p.1 (p.2 : B) y₀) y

/-- A single nonzero-norm line supplies a fixed separable quadratic field.
Translation of its representative by scalars gives the entire second-entry
family modulo central units. The equality uses the norm-corrected word
ratio, expressed as the equality after multiplying by the original word. -/
def FixedFieldWords : Prop :=
  ∀ {F : Type u} [Field F] [CharP F 2] {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {s : B ≃ₐ[F] Bᵐᵒᵖ}, (∀ a, antiValue s a = quaternionConjugate hB a) →
    ∀ {V : Type w} [AddCommGroup V] [Module Bᵐᵒᵖ V] [Nontrivial V]
      (h : HermitianPairing s V) (ell : V →ₗ[Bᵐᵒᵖ] V), IsTraceOne h ell →
      ∃ (w₀ : V) (b : B) (E : Type v) (_ : Field E) (_ : Algebra F E)
        (_ : Algebra.IsSeparable F E) (i : E →ₐ[F] B),
        h.value w₀ w₀ ≠ 0 ∧ scalarClass F b = refinement h ell w₀ ∧ reducedTrace hB b ≠ 0 ∧
        b ∈ Set.range i ∧ Module.finrank F E = 2 ∧
        (∀ e : Eˣ, (i (e : E)) ∉ Set.range (algebraMap F B) →
          ∃ (c : F) (r : Fˣ), i (e : E) = algebraMap F B (r : F) * (b + algebraMap F B c)) ∧
        ∀ c : F,
          ∃ b₀ : Bˣ, (b₀ : B) = b + algebraMap F B c ∧
          ∀ a : Bˣ,
            let aBar := (Units.opEquiv (Units.map s.toMonoidHom a)).unop
            let t := ⁅aBar, b₀⁆
            let b₁ := antiValue s (a : B) * (b₀ : B) * (a : B)
            scalarClass F b₁ = refinement h ell (op (a : B) • w₀) ∧
            perpendicularRotation h (op (a : B) • w₀) b₁ =
              perpendicularRotation h w₀ (b₀ : B) ∧
            ∀ p : B × V × B,
              let q := weylWord h w₀ (b₀ : B) p
              weylWord h (op (a : B) • w₀) b₁ p =
                (algebraMap F B (reducedNorm hB (a : B)) * (t : B) * q.1,
                  q.2.1, (algebraMap F B (reducedNorm hB (a : B)) * antiValue s (t : B))⁻¹ * q.2.2)

end Columns

/-- The split Clifford rank-one lift on the marked quaternionic plane. -/
def ScalarPairLift : Prop := QuaternionScalarCliffordLift.ScalarCliffordLift.{u}

section SpinModel

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

/-- The subgroup generated by the two actual opposite contracting radicals. -/
def oppositeWords (c : Cocharacter G.val) : Subgroup (GroupPoints G.val (CommAlgCat.of F F)) :=
  Subgroup.closure {g | HasLimit c g 1 ∨ HasLimit (oppositeCocharacter c) g 1}

/-- The closure of the radical-generated subgroup in the local matrix topology. -/
def oppositeClosure [TopologicalSpace F] (i : MatrixRealization G)
    (c : Cocharacter G.val) : Set (PointsIn i F) :=
  closure {g : PointsIn i F | (show GroupPoints G.val (CommAlgCat.of F F) from g) ∈ oppositeWords c}

/-- In the local quaternionic spin model, admissible column maps lift to the
opposite radicals. Radical words remove the complement action of any Levi
point. Their closure contains the full scale preimage on field points, the
entire Levi, and the whole local group. -/
def QuaternionLocalGeneration : Prop :=
  ∀ {F K I B : Type u} [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (M : SpinModel G D), 4 ≤ Fintype.card I →
    ∀ (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d) (i : MatrixRealization G),
      ∃ (W : ComplementRefinement Q) (c : Cocharacter G.val),
        IsPairDiagonal M Q c ∧ IsNoncentral c ∧
        let R := CommAlgCat.of F F
        (∀ (w₀ : Fin d → B) (b : B),
          scalarClass F b = refinement W.pairing W.complementAction w₀ →
          ∃ gPlus gMinus : GroupPoints G.val R,
            HasLimit c gPlus 1 ∧ HasLimit (oppositeCocharacter c) gMinus 1 ∧
            ActsOnColumns M Q gPlus (upper W.pairing w₀ b) ∧
            ActsOnColumns M Q gMinus (lower W.pairing w₀ b)) ∧
        (∀ x : GroupPoints G.val R, Centralizes c x →
          ∃ y ∈ oppositeWords c, ∃ t : (R ⊗[F] B)ˣ,
            spinVectorProjection M R (y⁻¹ * x) = quaternionScale Q R t) ∧
        (∀ x : spinScalePreimage M Q R, x.val.1 ∈ oppositeClosure i c) ∧
        (∀ x : GroupPoints G.val R, Centralizes c x → x ∈ oppositeClosure i c) ∧
        oppositeClosure i c = Set.univ

end SpinModel

/-- Local density for the original nontrialitarian group, including both the
scalar and the quaternion division-factor models. -/
def NontrialitarianLocalGeneration : Prop :=
  ∀ (F : Type u) [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : AffineAlgebraicGroup F) (n : ℕ), 4 ≤ n →
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    SimplyConnectedLattice.GeometricallySimplyConnected G →
    HasFixedVectorVertex G n →
    ∀ i : MatrixRealization G,
      Dense {g : PointsIn i F | ∃ p ∈ RelativeRayGeneration.unipotentGenerated G,
        toUnit ((testSpec F).obj (Opposite.op (CommAlgCat.of F F))) ≫ p = g}

/-- Strong approximation for the original group over a global function field
of characteristic two, away from every finite nonempty set of places. -/
def NontrialitarianStrongApproximation : Prop :=
  ∀ (F : Type u) [Field F] [CharP F 2] (k : Type v) [Field k] [Finite k] [Algebra k F]
    (t : SeparatingParameter k F)
    (G : AffineAlgebraicGroup F) (n : ℕ), 4 ≤ n →
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    SimplyConnectedLattice.GeometricallySimplyConnected G →
    HasFixedVectorVertex G n →
    ∀ (i : MatrixRealization G) (S : Finset (GlobalFieldData.function k t).Place),
      S.Nonempty → StrongApproximation (GlobalFieldData.function k t) i S

end
end LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinCharacteristicTwo
