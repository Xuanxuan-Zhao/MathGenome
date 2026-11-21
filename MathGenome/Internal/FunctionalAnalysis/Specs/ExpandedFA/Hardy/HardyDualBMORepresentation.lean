import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyPAtoms
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.BMOQuotient
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.MeasureTheory.Function.L2Space

/-!
Independent statements for the representation half of fa2:p4:hardy-bmo-dual,
paper.tex:18526–18552, with uniqueness at 18566–18569. The scalar field is
real or complex, the functional is scalar-linear, and dimension zero is included.
Pairing below is asserted only on finite atomic sums. No global absolute
integrability assertion for arbitrary H¹/BMO pairs is made.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

namespace ExpandedFA.Hardy.HardyDualBMORepresentationSpec

abbrev Point := HardyPAtomsSpec.Point
abbrev H1 := HardyPAtomsSpec.H1
abbrev L1 := HardyPAtomsSpec.L1
abbrev Atom := HardyPAtomsSpec.InfinityAtom
abbrev L2 (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :=
  Lp 𝕜 2 (volume : Measure (Point d))

/-- The actual ball-supported mean-zero subspace of the global L² space.
Both conditions are kernels of continuous linear maps, so this is a Hilbert
subspace; no representation or Hardy estimate is assumed in its definition. -/
def ballTests (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (c : Point d) (r : ℝ) :
    Submodule 𝕜 (L2 d 𝕜) :=
  (LpToLpRestrictCLM (Point d) 𝕜 𝕜 volume 2 (Metric.ball c r)ᶜ).ker ⊓
    (innerSL 𝕜 (indicatorConstLp (s := Metric.ball c r) 2 Metric.isOpen_ball.measurableSet
      measure_ball_ne_top (1 : 𝕜) : L2 d 𝕜)).ker

/-- Equality with the ordinary integral for every finite linear combination
of the accepted infinity-atoms, including the empty sum. Grouping repetitions
into a finite set of atoms does not change this condition. -/
def Represents {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (L : H1 d 𝕜 →L[𝕜] 𝕜) (g : Point d → 𝕜) : Prop :=
  ∀ (s : Finset (Atom d 𝕜)) (a : Atom d 𝕜 → 𝕜) (h : H1 d 𝕜),
    AtomicHardySpaceSpec.EmbeddingValue volume h = ∑ b ∈ s, a b • b.val →
    Integrable (fun x => AtomicHardySpaceSpec.EmbeddingValue volume h x * g x) volume ∧
    L h = ∫ x, AtomicHardySpaceSpec.EmbeddingValue volume h x * g x

/-- Quantitative local Hilbert representation, before any gluing. The
representing vector lies in the same supported mean-zero L² subspace.
The conjugation in the formula converts Riesz's conjugate-first inner
product into the scalar-linear product pairing in the source. -/
def LocalRepresentation : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
    (L : H1 d 𝕜 →L[𝕜] 𝕜) (c : Point d) (r : ℝ), 0 < r →
    ∃ v : ballTests d 𝕜 c r,
      ‖v.val‖ ≤ C * (volume.real (Metric.ball c r)) ^ (1 / 2 : ℝ) * ‖L‖ ∧
      ∀ (h : H1 d 𝕜) (f : ballTests d 𝕜 c r),
        AtomicHardySpaceSpec.EmbeddingValue volume h =ᵐ[volume] f.val →
        L h = ∫ x, f.val x * star (v.val x)

/-- The complete assigned conclusion, with one constant depending only on
dimension and uniqueness among all BMO representatives of the functional. -/
def Representation : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
    (L : H1 d 𝕜 →L[𝕜] 𝕜),
    ∃ g : BMOQuotientSpec.BMOFunctionValue d 𝕜,
      Represents L g.val ∧
      BMOQuotientSpec.BMOENormValue g.val ≤ ENNReal.ofReal (C * ‖L‖) ∧
      ∀ g' : BMOQuotientSpec.BMOFunctionValue d 𝕜,
        Represents L g'.val → BMOQuotientSpec.ModConstantsValue g' g

/-- The global existence branch, stated on individual atoms. Finite sums
are a proved linear assembly step, rather than a further analytic assumption. -/
def AtomicExistence : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
    (L : H1 d 𝕜 →L[𝕜] 𝕜),
    ∃ g : BMOQuotientSpec.BMOFunctionValue d 𝕜,
      BMOQuotientSpec.BMOENormValue g.val ≤ ENNReal.ofReal (C * ‖L‖) ∧
      ∀ (a : Atom d 𝕜) (h : H1 d 𝕜),
        AtomicHardySpaceSpec.EmbeddingValue volume h = a.val →
        L h = ∫ x, a.val x * g.val x

/-- The independent uniqueness branch. The functions need only be locally
integrable, not L² or bounded; atoms separate them modulo a.e. constants. -/
def AtomSeparation : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (g g' : Point d → 𝕜),
    LocallyIntegrable g volume → LocallyIntegrable g' volume →
    (∀ a : Atom d 𝕜, (∫ x, a.val x * g x) = ∫ x, a.val x * g' x) →
    ∃ k : 𝕜, ∀ᵐ x ∂volume, g' x = g x + k

/-- This conditional assembly is not the unconditional representation
result. Both analytic premises remain explicit proof obligations. -/
def Assembly : Prop := AtomicExistence → AtomSeparation → Representation

end ExpandedFA.Hardy.HardyDualBMORepresentationSpec
