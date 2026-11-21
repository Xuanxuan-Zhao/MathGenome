import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.LpTranslationContinuity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.Trigonometric

/-!
Independent interface for the definition and concrete model in
paper.tex:16324–16350 (fa2:p3:stone-von-neumann). The coordinates are ordered
(position, momentum). Momentum is angular frequency: the exponent contains
no factor of 2π. Linear isometric equivalences of complex Hilbert spaces
are the unitary operators. Strong continuity means continuity of each vector
orbit, not continuity in operator norm.

Canonical coordinate and representation types live here so later Gaussian
integration and multiplicity goals can use the same objects. The concrete
model is defined on the accepted a.e. quotient `Lp ℂ 2 volume`; its simple
well-definedness proof uses only equality of pointwise norms and translation
invariance of Lebesgue measure, and does not assume any Weyl identity.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u

namespace ExpandedFA.Weyl.RegularWeylRepresentationSpec

abbrev Configuration (d : ℕ) := Fin d → ℝ
abbrev PhaseSpace (d : ℕ) := Configuration d × Configuration d
abbrev SchrodingerSpace (d : ℕ) := Lp ℂ 2 (volume : Measure (Configuration d))

def SymplecticFormType := ∀ {d : ℕ}, PhaseSpace d → PhaseSpace d → ℝ

def SymplecticFormValue : SymplecticFormType := fun z w =>
  ∑ j, (z.2 j * w.1 j - w.2 j * z.1 j)

def WeylPhaseType := ∀ {d : ℕ}, PhaseSpace d → PhaseSpace d → ℂ

def WeylPhaseValue : WeylPhaseType := fun z w =>
  Complex.exp ((SymplecticFormValue z w / 2 : ℝ) * Complex.I)

/-- The multiplier in the symmetric (Weyl) ordering. -/
def multiplier {d : ℕ} (z : PhaseSpace d) (t : Configuration d) : ℂ :=
  Complex.exp (((∑ j, z.2 j * (t j - z.1 j / 2)) : ℝ) * Complex.I)

theorem multiplier_continuous {d : ℕ} (z : PhaseSpace d) : Continuous (multiplier z) := by
  unfold multiplier
  fun_prop

theorem multiplier_norm {d : ℕ} (z : PhaseSpace d) (t : Configuration d) :
    ‖multiplier z t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- The exact Schrödinger operator on the a.e. quotient. -/
def SchrodingerActionType := ∀ {d : ℕ}, PhaseSpace d → SchrodingerSpace d → SchrodingerSpace d

def SchrodingerActionValue : SchrodingerActionType := fun z f =>
  let g := Lp.compMeasurePreserving (p := (2 : ℝ≥0∞)) (fun t => t - z.1)
    (measurePreserving_sub_right volume z.1) f
  ((Lp.memLp g).congr_norm
    ((multiplier_continuous z).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
    (.of_forall fun t => by simp only [Pi.mul_apply, norm_mul, multiplier_norm, one_mul])).toLp
    (fun t => multiplier z t * g t)

/-- A regular representation has positive finite dimension and a nonzero
complex Hilbert space. No separability hypothesis is included. -/
structure RegularRepresentation (d : ℕ) (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  dimension_pos : 0 < d
  nontrivial_space : Nontrivial H
  W : PhaseSpace d → H ≃ₗᵢ[ℂ] H
  zero : ∀ x, W 0 x = x
  mul : ∀ z w x, W z (W w x) = WeylPhaseValue z w • W (z + w) x
  strong_continuous : ∀ x, Continuous (fun z => W z x)

def RegularRepresentationType := ∀ (_d : ℕ) (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H], Type u

def RegularRepresentationValue : RegularRepresentationType.{u} := RegularRepresentation

def SchrodingerRepresentative : Prop :=
  ∀ {d : ℕ} (z : PhaseSpace d) (f : SchrodingerSpace d),
    SchrodingerActionValue z f =ᵐ[volume] fun t => multiplier z t * f (t - z.1)

def SchrodingerZero : Prop :=
  ∀ {d : ℕ} (f : SchrodingerSpace d), SchrodingerActionValue 0 f = f

def SchrodingerWeylLaw : Prop :=
  ∀ {d : ℕ} (z w : PhaseSpace d) (f : SchrodingerSpace d),
    SchrodingerActionValue z (SchrodingerActionValue w f) =
      WeylPhaseValue z w • SchrodingerActionValue (z + w) f

def SchrodingerUnitary : Prop :=
  ∀ {d : ℕ} (z : PhaseSpace d), ∃ U : SchrodingerSpace d ≃ₗᵢ[ℂ] SchrodingerSpace d,
    ∀ f, U f = SchrodingerActionValue z f

def SchrodingerStrongContinuous : Prop :=
  ∀ {d : ℕ} (f : SchrodingerSpace d), Continuous (fun z => SchrodingerActionValue z f)

def SchrodingerRegular : Prop :=
  ∀ (d : ℕ) (_hd : 0 < d), ∃ R : RegularRepresentation d (SchrodingerSpace d),
    ∀ z f, R.W z f = SchrodingerActionValue z f

end ExpandedFA.Weyl.RegularWeylRepresentationSpec
