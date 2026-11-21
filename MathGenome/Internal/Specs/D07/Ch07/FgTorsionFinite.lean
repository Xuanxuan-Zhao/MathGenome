import MathGenome.Internal.Specs.D07.Ch07.FgAbelianExtension
import MathGenome.Internal.Specs.D07.Ch04.DirectProducts

/-!
Independent statements for K07.07.fg_torsion_finite, paper.tex:3518–3525.
The main theorem retains both finite generation and commutativity.
The counterexample uses the additive direct sum, whose underlying functions
have finite support, for every prime and every infinite index type.
-/
namespace Specs.D07.Ch07.FgTorsionFinite

universe u

/-- The direct sum of copies of the additive cyclic group C_p. -/
abbrev PrimeSum (I : Type u) (p : ℕ) := DirectSum I (fun _ => ZMod p)

/-- The tuple with residue 1 at i and residue 0 elsewhere. -/
noncomputable def coordinateGenerator (I : Type u) (p : ℕ) (i : I) : PrimeSum I p := by
  classical
  exact DirectSum.of (fun _ : I => ZMod p) i 1

def FiniteOfFgTorsion : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [AddGroup.FG A], IsAddTorsion A → Finite A

/-- In every normalized finitely generated decomposition, torsion means rank zero. -/
def TorsionIffRankZero : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [AddGroup.FG A] (r : ℕ) (d : List ℕ),
    D07.Ch07.ClassificationDataConversion.IsInvariant d →
    (A ≃+ FgAbelianExtension.Model r d) → (IsAddTorsion A ↔ r = 0)

/-- The natural map identifies B with exactly the finite-support functions. -/
def FiniteSupportDescription : Prop :=
  ∀ (I : Type u) (p : ℕ),
    Function.Injective (DirectSum.coeFnAddMonoidHom (fun _ : I => ZMod p)) ∧
    ∀ x : I → ZMod p,
      (∃ b : PrimeSum I p, DirectSum.coeFnAddMonoidHom (fun _ : I => ZMod p) b = x) ↔
        Set.Finite {i : I | x i ≠ 0}

def PointwiseOperations : Prop :=
  ∀ (I : Type u) (p : ℕ),
    (∀ (x y : PrimeSum I p) (i : I), (x + y) i = x i + y i) ∧
    (∀ i : I, (0 : PrimeSum I p) i = 0) ∧
    (∀ (x : PrimeSum I p) (i : I), (-x) i = -(x i))

def Annihilation : Prop :=
  ∀ (I : Type u) (p : ℕ), p.Prime → ∀ b : PrimeSum I p, p • b = 0

def TorsionWithPositiveAnnihilator : Prop :=
  ∀ (I : Type u) (p : ℕ), p.Prime →
    0 < p ∧ IsAddTorsion (PrimeSum I p) ∧ ∀ b : PrimeSum I p, p • b = 0

def CoordinateGeneratorValues : Prop :=
  ∀ (I : Type u) (p : ℕ) (i : I),
    coordinateGenerator I p i i = 1 ∧
    ∀ j : I, j ≠ i → coordinateGenerator I p i j = 0

def CoordinateGeneratorsInjective : Prop :=
  ∀ (I : Type u) (p : ℕ), p.Prime → Function.Injective (coordinateGenerator I p)

def InfiniteCounterexample : Prop :=
  ∀ (I : Type u) [Infinite I] (p : ℕ), p.Prime → Infinite (PrimeSum I p)

def NotFinitelyGenerated : Prop :=
  ∀ (I : Type u) [Infinite I] (p : ℕ), p.Prime → ¬ AddGroup.FG (PrimeSum I p)

end Specs.D07.Ch07.FgTorsionFinite
