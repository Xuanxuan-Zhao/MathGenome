import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RingTheory.Spectrum.Prime.Topology

noncomputable section

open scoped TensorProduct commutatorElement

namespace LinearAlgebraicGroups.Arithmetic.UnitaryCayleyChart

open SymplecticIsometryDescent (Involution)
open UnitaryNormEquations (SecondKind)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (SplitComparison)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open _root_.Specs.RM03.CSA (isCentralSimple)

universe u v w

/-- The full isometry points on which `1 - g` is invertible. -/
abbrev CayleyOpen {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    (s : Involution R A) :=
  {g : s.isometries // IsUnit (1 - (g.val : A))}

/-- The invertible points of the affine equation `y + s(y) = 1`. -/
abbrev CayleyParameters {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    (s : Involution R A) :=
  {y : Aˣ // (y : A) + s.toLinearMap (y : A) = 1}

/-- The involution of the second kind viewed over its fixed ground field. -/
def groundInvolution {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [Ring A] [Algebra F A] [Algebra E A] (s : SecondKind F E A) : Involution F A where
  toLinearMap := MulOpposite.opLinearEquiv F |>.symm.toLinearMap.comp s.adjoint.toLinearMap
  map_one := by change MulOpposite.unop (s.adjoint 1) = 1; simp
  map_mul x y := by change MulOpposite.unop (s.adjoint (x * y)) = _; rw [map_mul]; rfl
  involutive := s.adjoint_adjoint

/-- Inclusion into a scalar extension of the isometry group. -/
def isometryExtension {K F A : Type u} [Field K] [Field F] [Algebra K F]
    [Ring A] [Algebra K A] (s : Involution K A) :
    s.isometries →* (s.baseChange F).isometries :=
  s.mapIsometries (s.baseChange F)
    (Algebra.TensorProduct.includeRight (R := K) (A := F)).toRingHom
    (fun x => (s.baseChange_tmul F 1 x).symm)

/-- Every isometry is a quotient of two points in the Cayley open. -/
def CayleyQuotients {F A : Type u} [Field F] [Ring A] [Algebra F A]
    (s : Involution F A) : Prop :=
  ∀ g : s.isometries, ∃ a b : CayleyOpen s, a.val / b.val = g

/-- The diagonal on full isometry groups is dense at every finite set of
completions, with the usual finite-dimensional local topology. -/
def WeakApproximation {K A : Type u} [Field K] [Ring A] [Algebra K A]
    (D : GlobalFieldData.{u,v} K) (s : Involution K A) : Prop :=
  ∀ T : Finset D.Place,
    letI (p : T) : Algebra K (D.Completion p.1) := (D.embedding p.1).toAlgebra
    let Aₚ (p : T) := D.Completion p.1 ⊗[K] A
    ∀ (b : ∀ p : T, Module.Basis (Fin (Module.finrank (D.Completion p.1) (Aₚ p)))
        (D.Completion p.1) (Aₚ p)),
      letI (p : T) := LocalNormOneCommutators.Spec.coordinateTopology (b p)
      DenseRange (fun g : s.isometries => fun p : T =>
        isometryExtension (F := D.Completion p.1) s g)

namespace Spec

def NaturalChart : Prop :=
  ∀ {R S A B : Type u} [CommRing R] [CommRing S] [Ring A] [Ring B]
    [Algebra R A] [Algebra S B] (s : Involution R A) (t : Involution S B)
    (f : A →+* B) (hf : ∀ x, f (s.toLinearMap x) = t.toLinearMap (f x)),
    ∃ (e : CayleyOpen s ≃ CayleyParameters s) (e' : CayleyOpen t ≃ CayleyParameters t),
      (∀ g : CayleyOpen s, ((e g).val⁻¹).val = 1 - g.val.val.val) ∧
      (∀ g : CayleyOpen t, ((e' g).val⁻¹).val = 1 - g.val.val.val) ∧
      ∀ (g : CayleyOpen s) (g' : CayleyOpen t),
        g'.val = s.mapIsometries t f hf g.val →
        (e' g').val = Units.map f.toMonoidHom (e g).val

/-- Translating by a trace-one point identifies the full solution functor with
the vector space of skew elements. The chart is the principal open given by
the determinant of left multiplication. -/
def AffineParameterSpace : Prop :=
  ∀ {F A : Type u} [Field F] [Ring A] [Algebra F A] [Module.Finite F A]
    (s : Involution F A) (z : A), z + s.toLinearMap z = 1 →
    ∀ (R : Type u) [CommRing R] [Algebra F R],
      let V := LinearMap.ker (LinearMap.id + s.toLinearMap)
      let b := (Module.finBasis F A).baseChange R
      ∃ e : (R ⊗[F] V) ≃ {y : R ⊗[F] A // y + (s.baseChange R).toLinearMap y = 1},
        (∀ x, (e x).val = (1 : R) ⊗ₜ[F] z + V.subtype.baseChange R x) ∧
        ∀ x, IsUnit (e x).val ↔
          IsUnit (Algebra.leftMulMatrix b (e x).val).det

def Chart : Prop :=
  ∀ {R A : Type u} [CommRing R] [Ring A] [Algebra R A] (s : Involution R A),
    ∃ e : CayleyOpen s ≃ CayleyParameters s,
      (∀ g : CayleyOpen s, ((e g).val⁻¹).val = 1 - g.val.val.val) ∧
      (∀ y : CayleyParameters s, (e.symm y).val.val.val = 1 - (y.val⁻¹).val)

/-- Rational points of a nonempty principal open in affine space are dense
also after extending the coefficients to any field. -/
def PrincipalOpenRationalDensity : Prop :=
  ∀ {F : Type u} {L : Type v} {ι : Type w} [Field F] [Field L] [Algebra F L]
    [Infinite F] (p : MvPolynomial ι F), p ≠ 0 →
    DenseRange (fun x : {a : ι → F // MvPolynomial.eval a p ≠ 0} =>
      PrimeSpectrum.comap
        (MvPolynomial.eval (algebraMap F L ∘ x.val))
        (⟨⊥, inferInstance⟩ : PrimeSpectrum L))

def UnitaryTraceOne : Prop :=
  ∀ {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    [Nontrivial A] (s : SecondKind F E A),
    ∃ z : Aˣ, (z : A) + MulOpposite.unop (s.adjoint z) = 1

def UnitaryChartNonempty : Prop :=
  ∀ {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    [Nontrivial A] (s : SecondKind F E A),
    Nonempty (CayleyOpen (groundInvolution s))

/-- Existence of two parameters representing every point as a quotient, where
geometric intersection is tested after scalar extension. -/
def QuotientsFromExtension : Prop :=
  ∀ {F L A : Type u} [Field F] [Infinite F] [Field L] [Algebra F L]
    [Ring A] [Algebra F A] [Module.Finite F A] (s : Involution F A)
    (z : A), z + s.toLinearMap z = 1 →
    ∀ (g : s.isometries),
    let f : A →ₐ[F] L ⊗[F] A := Algebra.TensorProduct.includeRight
    (∃ y : CayleyParameters (s.baseChange L),
      IsUnit ((1 - f g.val.val) * y.val.val + f g.val.val)) →
    ∃ a b : CayleyOpen s, a.val / b.val = g

/-- The coordinate argument applies whenever the local charts supply quotient
representations. The trace-one and quotient hypotheses are proved for the two
models of involutions separately. -/
def WeakApproximationFromChart : Prop :=
  ∀ {K A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Ring A] [Algebra K A] [Module.Finite K A] (s : Involution K A)
    (z : A), z + s.toLinearMap z = 1 →
    ∀ T : Finset D.Place,
      letI (p : T) : Algebra K (D.Completion p.1) := (D.embedding p.1).toAlgebra
      let Aₚ (p : T) := D.Completion p.1 ⊗[K] A
      ∀ (b : ∀ p : T, Module.Basis (Fin (Module.finrank (D.Completion p.1) (Aₚ p)))
          (D.Completion p.1) (Aₚ p)),
        letI (p : T) := LocalNormOneCommutators.Spec.coordinateTopology (b p)
        (∀ (p : T) (g : (s.baseChange (D.Completion p.1)).isometries),
          ∃ a b : CayleyOpen (s.baseChange (D.Completion p.1)), a.val / b.val = g) →
        DenseRange (fun g : s.isometries => fun p : T => isometryExtension (F := D.Completion p.1) s g)

/-- The symplectic chart works over every infinite base field, given a
splitting of the involutive algebra to the standard alternating adjoint. -/
def SymplecticQuotients : Prop :=
  ∀ {F L A : Type u} [Field F] [Infinite F] [Field L] [Algebra F L]
    [Ring A] [Algebra F A] [Module.Finite F A] (s : Involution F A) (n : ℕ),
    SplitComparison (toDivisionInvolution s) L n → CayleyQuotients s

/-- The chart is nonempty over an infinite splitting field and over an infinite ground field. -/
def SymplecticChartNonempty : Prop :=
  ∀ {F L A : Type u} [Field F] [Field L] [Infinite L] [Algebra F L]
    [Ring A] [Algebra F A] [Module.Finite F A] (s : Involution F A) (n : ℕ),
    SplitComparison (toDivisionInvolution s) L n →
    Nonempty (CayleyOpen (s.baseChange L)) ∧ (Infinite F → Nonempty (CayleyOpen s))

/-- This includes both possibilities for the centre over the local field. -/
def UnitaryQuotients : Prop :=
  ∀ {k E A F : Type u} [Field k] [Field E] [Algebra k E]
    [Algebra.IsQuadraticExtension k E] [Algebra.IsSeparable k E]
    [Ring A] [Algebra k A] [Algebra E A] [IsScalarTower k E A]
    [Field F] [Algebra k F] [Infinite F] (_hA : isCentralSimple E A) (s : SecondKind k E A),
    CayleyQuotients ((groundInvolution s).baseChange F)

def SymplecticWeakApproximation : Prop :=
  ∀ {K A L : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Ring A] [Algebra K A] [Module.Finite K A] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (s : Involution K A) (n : ℕ),
    SplitComparison (toDivisionInvolution s) L n → WeakApproximation D s

def UnitaryWeakApproximation : Prop :=
  ∀ {K E A : Type u} [Field K] (D : GlobalFieldData.{u,v} K) [Field E] [Algebra K E]
    [Algebra.IsQuadraticExtension K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    isCentralSimple E A → ∀ s : SecondKind K E A, WeakApproximation D (groundInvolution s)

/-- At a finite place where the centre has split, special unitary points lie
in the closure of products of commutators of full unitary points. -/
def FiniteSplitCentreCommutators : Prop :=
  ∀ {k E A F : Type u} [Field k] [Field E] [Algebra k E]
    [Algebra.IsQuadraticExtension k E] [Algebra.IsSeparable k E]
    [Ring A] [Algebra k A] [Algebra E A] [IsScalarTower k E A]
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra k F] [Algebra E F] [IsScalarTower k E F]
    (hA : isCentralSimple E A) {ι : Type u} [Fintype ι] (b : Module.Basis ι E A)
    (s : SecondKind k E A),
    let B := F ⊗[k] A
    ∀ c : Module.Basis (Fin (Module.finrank F B)) F B,
      letI := LocalNormOneCommutators.Spec.coordinateTopology c
      let U := ((groundInvolution s).baseChange F).isometries
      ∀ g : U, UnitaryNormEquations.IsSpecialUnitary hA b s g.val →
        g ∈ closure (commutator U : Set U)

/-- Weak approximation of the full group permits simultaneous approximation by
rational reduced-norm-one elements at places where the local targets belong to
the closures of their commutator subgroups. -/
def SimultaneousNormOneApproximation : Prop :=
  ∀ {K E A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    (hA : isCentralSimple E A) (s : SecondKind K E A) (T : Finset D.Place),
    letI (p : T) : Algebra K (D.Completion p.1) := (D.embedding p.1).toAlgebra
    let Aₚ (p : T) := D.Completion p.1 ⊗[K] A
    let Uₚ (p : T) := ((groundInvolution s).baseChange (D.Completion p.1)).isometries
    ∀ (b : ∀ p : T, Module.Basis (Fin (Module.finrank (D.Completion p.1) (Aₚ p)))
        (D.Completion p.1) (Aₚ p)),
      letI (p : T) := LocalNormOneCommutators.Spec.coordinateTopology (b p)
      ∀ x : ∀ p, Uₚ p, (∀ p, x p ∈ closure (commutator (Uₚ p) : Set (Uₚ p))) →
        x ∈ closure (Set.range (fun
          g : {g : (groundInvolution s).isometries // _root_.Specs.RM03.CSA.reducedNorm hA g.val.val = 1} =>
          fun p : T => isometryExtension (F := D.Completion p.1) (groundInvolution s) g.val))

def CompactRealCommutators : Prop :=
  ∀ (n : ℕ) (g : Matrix.unitaryGroup (Fin n) ℂ), g.val.det = 1 →
    ∃ a b : Matrix.unitaryGroup (Fin n) ℂ, ⁅a, b⁆ = g


/-- The commutator description applies through the unitary comparison at a compact real place. -/
def CompactRealCommutatorClosure : Prop :=
  ∀ {U : Type u} [Group U] [TopologicalSpace U] (n : ℕ)
    (e : U ≃* Matrix.unitaryGroup (Fin n) ℂ) (g : U), (e g).val.det = 1 →
    g ∈ closure (commutator U : Set U)

end Spec
end LinearAlgebraicGroups.Arithmetic.UnitaryCayleyChart
