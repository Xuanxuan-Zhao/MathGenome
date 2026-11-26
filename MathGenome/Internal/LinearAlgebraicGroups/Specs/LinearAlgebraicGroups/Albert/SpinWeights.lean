import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitSpin
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Pi

namespace LinearAlgebraicGroups.Specs.SpinWeights

open scoped BigOperators

universe u

/-- The ordinary coordinates of the vector torus, with standard basis `εᵢ`. -/
abbrev VectorExponents := Fin 4 → ℤ

def coordinate (i : Fin 4) : VectorExponents := Pi.single i 1

/-- The character lattice in the free coordinates `(u,a₁,a₂,a₃)` of the
diagonal Clifford chart; the omitted coordinate is `a₀ = u⁻² ∏ aᵢ⁻¹`. -/
abbrev CharacterExponents := ℤ × (Fin 3 → ℤ)

def vectorPullback : VectorExponents →ₗ[ℤ] CharacterExponents where
  toFun x := (-2 * x 0, fun i => x i.succ - x 0)
  map_add' x y := by
    refine Prod.ext ?_ (funext fun i => ?_)
    · change -2 * (x 0 + y 0) = -2 * x 0 + -2 * y 0
      rw [mul_add]
    · change x i.succ + y i.succ - (x 0 + y 0) = x i.succ - x 0 + (y i.succ - y 0)
      exact add_sub_add_comm _ _ _ _
  map_smul' n x := by
    refine Prod.ext ?_ (funext fun i => ?_)
    · change -2 * (n * x 0) = n * (-2 * x 0)
      rw [mul_left_comm]
    · change n * x i.succ - n * x 0 = n * (x i.succ - x 0)
      rw [mul_sub]

def epsilon (i : Fin 4) : CharacterExponents := vectorPullback (coordinate i)

/-- The inverse of the scalar coordinate `u` is the half-sum character. -/
def halfSum : CharacterExponents := (-1, 0)

def exteriorWeight (I : Finset (Fin 4)) : CharacterExponents :=
  (∑ i ∈ I, epsilon i) - halfSum

/-- The roots and coroots in the ordinary vector coordinates. The coordinate
dot product makes the two realizations agree, as all roots have square length two. -/
def vectorRoots : Set VectorExponents :=
  {x | ∃ i j : Fin 4, i ≠ j ∧
    (x = coordinate i + coordinate j ∨ x = coordinate i - coordinate j ∨
      x = -coordinate i - coordinate j)}

def rootCharacters : Set CharacterExponents := vectorPullback '' vectorRoots

def parityMap : VectorExponents →ₗ[ℤ] ZMod 2 where
  toFun x := (∑ i, x i : ℤ)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' n x := by simp [Finset.mul_sum, zsmul_eq_mul]

/-- Exponents of diagonal cocharacters in the vector representation. -/
def evenSumLattice : Submodule ℤ VectorExponents := parityMap.ker

/-- The coordinates of the central character are the exponent of the scalar
`u` and the sum of the exponents of `a₁,a₂,a₃`, both modulo two. -/
def centralClass : CharacterExponents →ₗ[ℤ] ZMod 2 × ZMod 2 where
  toFun x := ((x.1 : ZMod 2), (∑ i, x.2 i : ℤ))
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' n x := by
    refine Prod.ext ?_ ?_
    · change ((n * x.1 : ℤ) : ZMod 2) = n • (x.1 : ZMod 2)
      simp [zsmul_eq_mul]
    · change ((∑ i, n * x.2 i : ℤ) : ZMod 2) = n • ((∑ i, x.2 i : ℤ) : ZMod 2)
      simp [Finset.mul_sum, zsmul_eq_mul]

def HalfSumRelation : Prop :=
  (2 : ℤ) • halfSum = ∑ i, epsilon i

def CharacterGenerators : Prop :=
  Submodule.span ℤ (insert halfSum (Set.range epsilon)) = ⊤

def CorootSpan : Prop :=
  Submodule.span ℤ vectorRoots = evenSumLattice

/-- The map to the two central exponents presents the root quotient, and the
three systems restrict to the three different nontrivial characters. -/
def CentralClasses : Prop :=
  Function.Surjective centralClass ∧ Submodule.span ℤ rootCharacters = centralClass.ker ∧
  (∀ i, centralClass (epsilon i) = (0, 1) ∧ centralClass (-epsilon i) = (0, 1)) ∧
  ∀ I : Finset (Fin 4), centralClass (exteriorWeight I) = (1, (I.card : ZMod 2))

section Torus

open LinearAlgebraicGroups.Albert
open SplitSpinSpecification
open scoped Matrix

variable (R : Type u) [CommRing R]

/-- The diagonal coordinates and the scalar multiplying the exterior action. -/
def diagonalNorm : ((Fin 4 → Rˣ) × Rˣ) →* Rˣ where
  toFun p := p.2 ^ 2 * ∏ i, p.1 i
  map_one' := by simp
  map_mul' x y := by
    change (x.2 * y.2) ^ 2 * (∏ i, x.1 i * y.1 i) =
      (x.2 ^ 2 * ∏ i, x.1 i) * (y.2 ^ 2 * ∏ i, y.1 i)
    rw [mul_pow, Finset.prod_mul_distrib]
    ac_rfl

abbrev DiagonalPoints := (diagonalNorm R).ker

variable {R}

def scales (t : DiagonalPoints R) : Fin 4 → Rˣ := t.val.1

def scalar (t : DiagonalPoints R) : Rˣ := t.val.2

def diagonalBlock (t : DiagonalPoints R) : Block 4 R :=
  Matrix.diagonal fun i => (scales t i : R)

/-- The tuple `(u,a₁,a₂,a₃)` is free over every test ring. -/
def DiagonalParameters : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ e : DiagonalPoints R ≃* Rˣ × (Fin 3 → Rˣ),
      ∀ t, e t = (scalar t, fun i => scales t i.succ)

/-- Evaluate a character in the free coordinates of the diagonal chart. -/
def evaluate (t : DiagonalPoints R) : CharacterExponents →+ Additive Rˣ where
  toFun x := Additive.ofMul (scalar t ^ x.1 * ∏ i, scales t i.succ ^ x.2 i)
  map_zero' := by
    change scalar t ^ (0 : ℤ) * (∏ i : Fin 3, scales t i.succ ^ (0 : ℤ)) = 1
    simp
  map_add' x y := by
    change scalar t ^ (x.1 + y.1) * (∏ i, scales t i.succ ^ (x.2 i + y.2 i)) =
      (scalar t ^ x.1 * ∏ i, scales t i.succ ^ x.2 i) *
        (scalar t ^ y.1 * ∏ i, scales t i.succ ^ y.2 i)
    simp only [zpow_add, Finset.prod_mul_distrib]
    ac_rfl

/-- The vector and exterior weight monomials, over arbitrary test algebras. -/
def WeightEvaluation : Prop :=
  ∀ (R : Type u) [CommRing R] (t : DiagonalPoints R),
    (∀ i, Additive.toMul (evaluate t (epsilon i)) = scales t i ∧
      Additive.toMul (evaluate t (-epsilon i)) = (scales t i)⁻¹) ∧
    ∀ I, Additive.toMul (evaluate t (exteriorWeight I)) = scalar t * ∏ i ∈ I, scales t i

/-- All-root kernel on the diagonal torus, calculated on arbitrary rings. -/
def DiagonalCentralCharacters : Prop :=
  ∀ (R : Type u) [CommRing R] (t : DiagonalPoints R),
    (∀ α ∈ rootCharacters, Additive.toMul (evaluate t α) = 1) ↔
      ∃ b : Rˣ, b ^ 2 = 1 ∧ (scalar t) ^ 2 = 1 ∧ ∀ i, scales t i = b

/-- The free hyperbolic exterior algebra in the creation coordinates. -/
abbrev ExteriorSpace (R : Type u) [CommRing R] := ExteriorAlgebra R (FreeModule R 4)

/-- The diagonal torus inside the Clifford spin functor, with its vector and
full exterior actions expressed in the prescribed bases. -/
def DiagonalCliffordAction : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra ℤ R],
    ∃ e : ScalarClifford 4 R ≃ₐ[R] Module.End R (ExteriorSpace R),
      (∀ x : ExtendedModule 4 R,
        e (SpinSpecification.vectors (integralForm 4) R x) =
          CliffordSpecification.hyperbolicOperator
            ((hyperbolicBasis R 4).equivFun.symm (((hyperbolicBasis ℤ 4).baseChange R).equivFun x))) ∧
      ∀ t : DiagonalPoints R, ∃ a : (ScalarClifford 4 R)ˣ,
        a ∈ SpinSpecification.spinUnits (integralForm 4) R ∧
        HasActionMatrix 4 a (middle (diagonalBlock t)) ∧
        ∀ I : Finset (Fin 4),
          e a ((Pi.basisFun R (Fin 4)).ExteriorAlgebra I) =
            ((Additive.toMul (evaluate t (exteriorWeight I)) : Rˣ) : R) •
              (Pi.basisFun R (Fin 4)).ExteriorAlgebra I

end Torus

section Irreducibility

open LinearAlgebraicGroups.Albert SplitSpinSpecification
open scoped Matrix

/-- Geometric irreducibility of the vector representation, in the hyperbolic basis. -/
def VectorIrreducibility : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra ℤ K]
    (W : Submodule K (PairIndex 4 → K)),
    (∀ (a : (ScalarClifford 4 K)ˣ), a ∈ SpinSpecification.spinUnits (integralForm 4) K →
      ∀ M, HasActionMatrix 4 a M → ∀ x ∈ W, M *ᵥ x ∈ W) →
    W = ⊥ ∨ W = ⊤

/-- Both actual exterior parity blocks are invariant and geometrically irreducible. -/
def HalfSpinIrreducibility : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra ℤ K],
    ∃ e : ScalarClifford 4 K ≃ₐ[K] Module.End K (ExteriorSpace K),
      (∀ x : ExtendedModule 4 K,
        e (SpinSpecification.vectors (integralForm 4) K x) =
          CliffordSpecification.hyperbolicOperator
            ((hyperbolicBasis K 4).equivFun.symm (((hyperbolicBasis ℤ 4).baseChange K).equivFun x))) ∧
      ∀ p : ZMod 2,
        let V := CliffordAlgebra.evenOdd (0 : QuadraticForm K (FreeModule K 4)) p
        let Stable := fun W : Submodule K (ExteriorSpace K) =>
          ∀ (a : (ScalarClifford 4 K)ˣ), a ∈ SpinSpecification.spinUnits (integralForm 4) K →
            ∀ x ∈ W, e a x ∈ W
        Stable V ∧ ∀ W, W ≤ V → Stable W → W = ⊥ ∨ W = V

end Irreducibility

section GroupScheme

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Albert SplitSpinSpecification
open GeometricRadicals (IsReductive IsSemisimple IsSplitTorus)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open RankOneFlag (IsGeometricallyMaximal)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots characterValue pairing)
open scoped CategoryTheory.MonObj

variable {R S : Type u} [CommRing R] [CommRing S]

def mapDiagonal (f : R →+* S) : DiagonalPoints R →* DiagonalPoints S where
  toFun t := ⟨(fun i => Units.map f.toMonoidHom (scales t i),
    Units.map f.toMonoidHom (scalar t)), by
    have h : (scalar t) ^ 2 * ∏ i, scales t i = 1 := t.property
    change (Units.map f.toMonoidHom (scalar t)) ^ 2 *
      (∏ i, Units.map f.toMonoidHom (scales t i)) = 1
    simpa only [map_mul, map_pow, map_prod, map_one] using
      congrArg (Units.map f.toMonoidHom) h⟩
  map_one' := by
    apply Subtype.ext
    exact Prod.ext (funext fun _ => map_one _) (map_one _)
  map_mul' x y := by
    apply Subtype.ext
    exact Prod.ext (funext fun _ => map_mul _ _ _) (map_mul _ _ _)

/-- The character pairing in the free torus coordinates. A vector cocharacter
has scalar exponent minus half the sum of its four vector exponents. -/
def latticePairing (χ : CharacterExponents) (y : evenSumLattice) : ℤ :=
  χ.1 * (-(∑ i, y.val i) / 2) + ∑ i : Fin 3, χ.2 i * y.val i.succ

/-- The exterior Clifford model is marked by its action on the vector generators. -/
def IsExteriorModel {R : Type u} [CommRing R] [Algebra ℤ R]
    (e : ScalarClifford 4 R ≃ₐ[R] Module.End R (ExteriorSpace R)) : Prop :=
  ∀ x : ExtendedModule 4 R,
    e (SpinSpecification.vectors (integralForm 4) R x) =
      CliffordSpecification.hyperbolicOperator
        ((hyperbolicBasis R 4).equivFun.symm (((hyperbolicBasis ℤ 4).baseChange R).equivFun x))

/-- Presentation of the split spin group over a field by the integral
hyperbolic Clifford functor evaluated on its test algebras. -/
def SpinPointPresentation {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (e : ∀ R : TestAlgebra k, Points G.val.X R →* (ScalarClifford 4 R)ˣ) : Prop :=
  (∀ R, Function.Injective (e R) ∧
    Set.range (e R) = SpinSpecification.spinUnits (integralForm 4) R) ∧
  ∀ {R S : TestAlgebra k} (f : R ⟶ S) (g : Points G.val.X R),
    e S (mapPoints f g) =
      Units.map (SpinSpecification.coefficientMap (integralForm 4) R
        (f.hom.restrictScalars ℤ)).toMonoidHom (e R g)

/-- The marked diagonal subgroup, including the normalization of its scalar
coordinate by the action on the empty wedge. -/
def TorusPointPresentation {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (e : ∀ R : TestAlgebra k, Points G.val.X R →* (ScalarClifford 4 R)ˣ)
    (T : ClosedSubgroup G.val)
    (d : ∀ R : TestAlgebra k, Points T.group.X R ≃* DiagonalPoints R) : Prop :=
  (∀ {R S : TestAlgebra k} (f : R ⟶ S) (t : Points T.group.X R),
    d S (mapPoints f t) = mapDiagonal f.hom.toRingHom (d R t)) ∧
  (∀ (R : TestAlgebra k) (g : Points G.val.X R),
    (∃ t : Points T.group.X R, t ≫ T.inclusion.hom.hom = g) ↔
      ∃ p : DiagonalPoints R, HasActionMatrix 4 (e R g) (middle (diagonalBlock p))) ∧
  ∀ R : TestAlgebra k,
    ∃ E : ScalarClifford 4 R ≃ₐ[R] Module.End R (ExteriorSpace R),
      IsExteriorModel E ∧ ∀ t : Points T.group.X R,
        let a := e R (t ≫ T.inclusion.hom.hom)
        let p := d R t
        HasActionMatrix 4 a (middle (diagonalBlock p)) ∧
        ∀ I : Finset (Fin 4),
          E a ((Pi.basisFun R (Fin 4)).ExteriorAlgebra I) =
            ((Additive.toMul (evaluate p (exteriorWeight I)) : Rˣ) : R) •
              (Pi.basisFun R (Fin 4)).ExteriorAlgebra I

/-- The centre is identified on all test rings, so in characteristic two
its two factors still retain their infinitesimal points. -/
def CentreCoordinates {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val)
    (d : ∀ R : TestAlgebra k, Points T.group.X R ≃* DiagonalPoints R) : Prop :=
  ∃ (Z : ClosedSubgroup G.val) (i : Z.group ⟶ T.group),
    RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 G.val) z) ∧
    i ≫ T.inclusion = Z.inclusion ∧
    ∃ e : ∀ R : TestAlgebra k, Points Z.group.X R ≃* rootsOfUnity 2 R × rootsOfUnity 2 R,
      ∀ (R : TestAlgebra k) (z : Points Z.group.X R),
        let p := d R (z ≫ i.hom.hom)
        (∀ j, scales p j = (e R z).1.val) ∧ scalar p = (e R z).2.val

/-- Rank-eight split Clifford spin over each field, with its actual
maximal torus, root datum, simply connectedness and scheme centre. -/
def FieldStructure : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (G : AffineAlgebraicGroup k)
      (e : ∀ R : TestAlgebra k, Points G.val.X R →* (ScalarClifford 4 R)ˣ),
      SpinPointPresentation G e ∧ IsReductive G ∧ IsSemisimple G ∧
      GeometricallySimplyConnected G ∧
      ∃ (T : ClosedSubgroup G.val)
        (d : ∀ R : TestAlgebra k, Points T.group.X R ≃* DiagonalPoints R),
        TorusPointPresentation e T d ∧ IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧
        CentreCoordinates T d ∧
        ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ (C : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
          (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] evenSumLattice)
          (D : AbstractPairing.Datum T),
          (∀ (R : TestAlgebra k) (t : Points T.group.X R) (χ : Character T.group),
            characterValue χ R t = ((Additive.toMul (evaluate (d R t) (C (Additive.ofMul χ))) : Rˣ) : R)) ∧
          (∀ (χ : Character T.group) (ψ : Cocharacter T.group),
            pairing T.group χ ψ = latticePairing (C (Additive.ofMul χ)) (Y (Additive.ofMul ψ))) ∧
          Set.BijOn (fun χ : Character T.group => C (Additive.ofMul χ))
            (absoluteRoots T) rootCharacters ∧
          ∀ α : AbstractPairing.Root T,
            vectorPullback (Y (D.rootDatum.coroot α)).val = C (Additive.ofMul α.val)

end GroupScheme

end LinearAlgebraicGroups.Specs.SpinWeights
