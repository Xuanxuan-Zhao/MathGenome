# Third-party sources and licenses

MathGenome uses the Lean toolchain and fixed Mathlib packages as separately
versioned dependencies. Their source histories, copyright notices and licenses
remain with those projects. Mathlib's fixed source commit is
`56a005855ea17e0b0958f73ec801ae140b0a1679` and uses the Apache License 2.0.
The Lean toolchain carries its own Apache 2.0 license and third-party notices.

The exact dependency repositories and revisions are recorded in
[`lake-manifest.json`](lake-manifest.json). Lake obtains dependency source
from the listed repositories, where their license files are available.

The D05 and D07 manuscripts are the separately audited unified notes
identified in the provenance records. Textbook titles and source locations
in the notes are bibliographic citations. The cited textbooks and their
contents remain subject to their respective rights. The lecture-note license
covers the original portions of the manuscripts. Any separately credited
material retains its own license and attribution.
Each adapted source file retains its upstream copyright and license information.

## Fundamental groupoid van Kampen theorem

[`VanKampen.lean`](MathGenome/Internal/TopologyRiemannianGeometry/P202/Topology/VanKampen.lean)
includes a local adaptation of Thomas Zhu's fundamental groupoid van Kampen
development proposed in [Mathlib PR #41603](https://github.com/leanprover-community/mathlib4/pull/41603).
The original source is available at
[Paul-Lez/mathlib4, commit `97d303eb50436be7c4bac4388bdb49459ae9140b`](https://github.com/Paul-Lez/mathlib4/tree/97d303eb50436be7c4bac4388bdb49459ae9140b/Mathlib/AlgebraicTopology/FundamentalGroupoid/VanKampen).
The compatibility port consulted was
[`vendor/VanKampen` in deancureton/sphere-six-complex](https://github.com/deancureton/sphere-six-complex/tree/b783b990d46c5f5ce02a4ecbbb2c02408b452cde/vendor/VanKampen),
which documents its changes and includes its own copy of the Apache 2.0 license.

The adapted source is distributed under the [Apache License 2.0](LICENSE).
MathGenome combined the helper modules in one file, relocated private helpers,
retained compatibility repairs, and added the wrappers for the P2-02 specification.

## Vizing's edge-coloring theorem

[`Vizing.lean`](MathGenome/Internal/FiniteCombinatorics/FiniteCombinatorics/Graph/EdgeColoring/Vizing.lean) retains the copyright notice of Juan Pablo Traverso Gianini for the partial-coloring, endpoint, Kempe, fan, and extension arguments adapted from the [`jtraverso/vizing` at `33b2de836095cf92bc1dec33b6f8787e4036bbc6`](https://github.com/jtraverso/vizing/tree/33b2de836095cf92bc1dec33b6f8787e4036bbc6/LeanPool/Vizing) (`LeanPool/Vizing/{Basic,Endpoints,Kempe,Fan,Step,Main}.lean`, retrieved 2026-11-16). The [original Lean Pool contribution](https://github.com/LeanPool/lean-pool/tree/26ce45d3871e5560a8baffa4d49a8942b1d20a24/LeanPool/Vizing) was submitted as [PR #578](https://github.com/LeanPool/lean-pool/pull/578). The accepted project adapts the proof to its edge-set and degree conventions. The library relocates its module imports. The adapted source is distributed under the [Apache License 2.0](LICENSES/Apache-2.0.txt).

## Functional analysis

### Double commutant theorem

[`DoubleCommutant.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/OperatorTopology/DoubleCommutant.lean) adapts
the finite diagonal amplification and simultaneous-orbit projection proof
from [OpenAI's `Bicommutant.lean`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/FactorGeneration/Bicommutant.lean).
The source snapshot verified here is commit `4eaee87548250b2682affda7d05d947c05554bae`.
The MathGenome file records that the source was retrieved on 2026-11-06.
MathGenome generalizes the finite-amplification argument from complex
Hilbert spaces to `RCLike` scalars and connects it to its real and
complex double-commutant statements.
The upstream code is licensed under [Apache License 2.0](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/LICENSE).

### Poisson summation

[`PoissonSummation.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/PartIV/PoissonSummation.lean) adapts
torus periodization and Fourier helpers from math-inc/Sphere-Packing-Lean
at commit `1e98fb493088948ca7bbf47d7faed49cc5b39fc4`.
The upstream files are
- [UnitAddTorus.lean](https://github.com/math-inc/Sphere-Packing-Lean/blob/1e98fb493088948ca7bbf47d7faed49cc5b39fc4/SpherePacking/CohnElkies/PoissonSummationLattices/UnitAddTorus.lean)
- [Lattice PoissonSummation.lean](https://github.com/math-inc/Sphere-Packing-Lean/blob/1e98fb493088948ca7bbf47d7faed49cc5b39fc4/SpherePacking/CohnElkies/PoissonSummationLattices/PoissonSummation.lean)
- [Schwartz Basic.lean](https://github.com/math-inc/Sphere-Packing-Lean/blob/1e98fb493088948ca7bbf47d7faed49cc5b39fc4/SpherePacking/CohnElkies/PoissonSummationSchwartz/Basic.lean)
- [Schwartz PoissonSummation.lean](https://github.com/math-inc/Sphere-Packing-Lean/blob/1e98fb493088948ca7bbf47d7faed49cc5b39fc4/SpherePacking/CohnElkies/PoissonSummationSchwartz/PoissonSummation.lean)
- [FourierLinearEquiv.lean](https://github.com/math-inc/Sphere-Packing-Lean/blob/1e98fb493088948ca7bbf47d7faed49cc5b39fc4/SpherePacking/ForMathlib/FourierLinearEquiv.lean)

MathGenome adapts the proof to its Euclidean and Fourier definitions and
adds matrix and absolute-convergence bridges for its statements.
The upstream code is licensed under [Apache License 2.0](https://github.com/math-inc/Sphere-Packing-Lean/blob/1e98fb493088948ca7bbf47d7faed49cc5b39fc4/LICENSE).

A copy of the license is included in [`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt).

## Mathlib proof adaptations

The proof portions listed below retain or adapt Lean code from Mathlib. The
credits describe the matching upstream source and the local changes. Where a
proof appears in several MathGenome files, the list records every affected
file without implying that each was ported independently.

The upstream files use the [Apache License 2.0](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/LICENSE).
All entries refer to Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`,
except the Schwartz approximation, which is credited to a later Mathlib commit.

### D10 · DyadicChains

[Topology/Metrizable/Uniformity.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Metrizable/Uniformity.lean#L200) · Yury Kudryashov. Copyright (c) 2022 Yury Kudryashov. All rights reserved.

- [`DyadicChains.lean`](MathGenome/Internal/PointSetTopology/D10Topology/Ch12/DyadicChains.lean#L14). The Nat.find dyadic distance and the estimates constructing its pseudometric, adapted to the given relation sequence.

### D11 · FiniteDirectedLscIntegral

[MeasureTheory/Integral/Lebesgue/Add.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean#L34) · Mario Carneiro, Johannes Hölzl. Copyright (c) 2018 Mario Carneiro. All rights reserved.

- [`FiniteDirectedLscIntegral.lean`](MathGenome/Internal/RealAnalysis/D11/Ch18/FiniteDirectedLscIntegral.lean#L48). The simple-function minorant and scaling steps in the integral argument, adapted to finite Radon measure and directed lower semicontinuous families.

### D13 / D16 / P2-01 · Picard–Lindelöf iteration

[Analysis/ODE/PicardLindelof.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/ODE/PicardLindelof.lean#L329) · Yury Kudryashov, Winston Yin. Copyright (c) 2021 Yury Kudryashov. All rights reserved.

- [`LinearVolterra.lean`](MathGenome/Internal/ODEDynamics/D13Unified/Ch06/LinearVolterra.lean#L344). The factorial estimate for the iterated approximation, adapted to the linear Volterra construction.
- [`ParabolicGalerkinExistence.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/Evolution/ParabolicGalerkinExistence.lean#L434). The factorial estimate for the iterated approximation in the parabolic Galerkin construction.
- [`HyperbolicWeakEnergyExistence.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/Evolution/HyperbolicWeakEnergyExistence.lean#L1279). The induction and factorial estimate for the iterated approximation in the hyperbolic energy construction.
- [`SymmetricApproximation.lean`](MathGenome/Internal/LinearPDE/P201/Hyperbolic/SymmetricApproximation.lean#L599). The factorial estimate for the iterated approximation in the symmetric hyperbolic construction.

### D16 · SpectralRadius

[Analysis/Normed/Algebra/GelfandFormula.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean#L101) · Jireh Loreaux. Copyright (c) 2021 Jireh Loreaux. All rights reserved.

- [`SpectralRadius.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/BanachAlgebra/SpectralRadius.lean#L62). The Cauchy estimate and power-series radius argument in the Gelfand spectral-radius formula.

### D16 · GroupAlgebraCharacters

[MeasureTheory/Function/ContinuousMapDense.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean#L84) · Heather Macbeth. Copyright (c) 2021 Heather Macbeth. All rights reserved.

- [`GroupAlgebraCharacters.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/BanachAlgebra/GroupAlgebraCharacters.lean#L149). The continuous compactly supported approximation and density arguments used for group algebra characters.

### D16 · Banach open mapping argument

[Analysis/Normed/Operator/Banach.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Operator/Banach.lean#L92) · Sébastien Gouëzel. Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.

- [`NonmeagreImage.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/Supplements/NonmeagreImage.lean#L50). The successive approximation and series construction in the nonmeagre-image argument.
- [`AbsoluteSynthesis.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/PartV/AbsoluteSynthesis.lean#L126). The successive lifts and summation construction for absolute synthesis.

### D16 · PreHilbertBesselParseval

[Analysis/InnerProductSpace/Orthonormal.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean#L437) · Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis. Copyright (c) 2019 Zhouhang Zhou. All rights reserved.

- [`PreHilbertBesselParseval.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/Hilbert/PreHilbertBesselParseval.lean#L12). The finite orthonormal expansion and squared-norm calculation for Bessel's inequality.

### D16 · IntervalL2Constants

[Analysis/Fourier/AddCircle.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Fourier/AddCircle.lean#L558) · Heather Macbeth, David Loeffler. Copyright (c) 2021 Heather Macbeth. All rights reserved.

- [`IntervalL2Constants.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/PartIV/IntervalL2Constants.lean#L529). The Fourier-coefficient integration-by-parts argument, adapted to the local absolute continuity and a.e. derivative formulation.

### D16 · Haar

[MeasureTheory/Group/Measure.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Group/Measure.lean#L385) · Floris van Doorn. Copyright (c) 2020 Floris van Doorn. All rights reserved.

- [`Haar.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/PartV/Haar.lean#L125). The proof of left invariance after inversion, adapted to separate measurability of translations.

### D16 · Definitions

[Analysis/Normed/Group/Quotient.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Normed/Group/Quotient.lean#L498) · Patrick Massot, Riccardo Brasca. Copyright (c) 2021 Patrick Massot. All rights reserved.

- [`Definitions.lean`](MathGenome/Internal/FunctionalAnalysis/ExpandedFA/Fredholm/Definitions.lean#L158). The approximate-representative proof of quotient norm submultiplicativity, adapted from an ideal quotient to the operator quotient.

### P1-02 · Schwartz approximation

[Analysis/Distribution/SchwartzSpace/CompactSupport.lean](https://github.com/leanprover-community/mathlib4/blob/b2115b96757894e56b53fd0f94bd63acd64d8025/Mathlib/Analysis/Distribution/SchwartzSpace/CompactSupport.lean#L39) · Terence Tao. Copyright (c) 2026 Terence Tao. All rights reserved.

The later source is from [Mathlib PR #43046](https://github.com/leanprover-community/mathlib4/pull/43046).

- [`SchwartzRestriction.lean`](MathGenome/Internal/FourierSobolev/P102/U4/SchwartzRestriction.lean#L30). The compactly supported approximation in Schwartz space, adapted to real and complex cutoffs.

### P1-02 · GraphFractionalTransport

[Probability/Kernel/WithDensity.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/WithDensity.lean#L196) · Rémy Degenne. Copyright (c) 2023 Rémy Degenne. All rights reserved.

- [`GraphFractionalTransport.lean`](MathGenome/Internal/FourierSobolev/P102/Trace/GraphFractionalTransport.lean#L143). The layer-sum argument for change of density, adapted to the graph gauge.

### P1-03 · Projective and injective resolutions

[CategoryTheory/Abelian/Projective/Resolution.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean#L81) · Markus Himmel, Kim Morrison, Jakob von Raumer, Joël Riou. Copyright (c) 2022 Jujian Zhang. All rights reserved.

[CategoryTheory/Abelian/Injective/Resolution.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean#L84) · Jujian Zhang, Kim Morrison. Copyright (c) 2022 Jujian Zhang. All rights reserved.

- [`Comparison.lean`](MathGenome/Internal/AlgebraCore/P103/Ch10/Comparison.lean#L98). The recursive comparison maps and null-homotopy constructions for projective and injective resolutions, adapted to the local hypotheses on the resolutions.

### P2-02 · OrientedSimplicialAlgebra

[AlgebraicTopology/AlternatingFaceMapComplex.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean#L75) · Joël Riou, Adam Topaz, Johan Commelin. Copyright (c) 2021 Joël Riou. All rights reserved.

- [`OrientedSimplicialAlgebra.lean`](MathGenome/Internal/TopologyRiemannianGeometry/P202Specs/Homology/OrientedSimplicialAlgebra.lean#L150). The face-index pairing and Finset.sum_bij argument for the squared differential in oriented simplicial chains.
- [`SimplicialRelativeParametrizations.lean`](MathGenome/Internal/TopologyRiemannianGeometry/P202Specs/Homology/SimplicialRelativeParametrizations.lean#L81). The face-index pairing and Finset.sum_bij argument for the squared differential in the relative parametrization construction.

### ALG-05 · PointwiseFlatSeparableCriterion

[RingTheory/Smooth/Fiber.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Smooth/Fiber.lean#L193) · Andrew Yang. Copyright (c) 2026 Andrew Yang. All rights reserved.

- [`PointwiseFlatSeparableCriterion.lean`](MathGenome/Internal/AdvancedCommutativeAlgebra/AdvCommAlg/Etale/PointwiseFlatSeparableCriterion.lean#L42). The localization and finite-presentation construction, adapted to prove the pointwise etale criterion.

### ALG-10 · Sheaf extension by zero

[Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean#L79-L96) · Joël Riou. Copyright (c) 2024 Joël Riou. All rights reserved. [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/LICENSE).

- [`SheafInjectivesAndRestriction.lean`](MathGenome/Internal/AdvancedHomologicalAlgebra/AdvancedHomologicalAlgebra/SheafInjectivesAndRestriction.lean#L502-L518). Adapts the composite Hom equivalence and its naturality proof to extension by zero.

### ALG-10 · Truncation in complex replacements

[Algebra/Homology/Factorizations/CM5a.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Homology/Factorizations/CM5a.lean#L669-L693) · Joël Riou. Copyright (c) 2026 Joël Riou. All rights reserved. [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/LICENSE).

- [`InjectiveComplexReplacement.lean`](MathGenome/Internal/AdvancedHomologicalAlgebra/AdvancedHomologicalAlgebra/InjectiveComplexReplacement.lean#L56-L91). Adapts the lower-bound truncation and adds degreewise monomorphisms at the bound.
- [`ProjectiveComplexReplacement.lean`](MathGenome/Internal/AdvancedHomologicalAlgebra/AdvancedHomologicalAlgebra/ProjectiveComplexReplacement.lean#L41-L75). Adapts the same truncation with a degreewise monomorphism before dualizing to projective replacement.
