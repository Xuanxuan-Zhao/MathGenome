# MathGenome

MathGenome v0.25.0 is a Lean library organized around mathematical definitions,
theorems, and their sources. The catalog links results to Lean declarations and
to the corresponding lecture notes. This repository contains the v0.25.0
library and its accompanying notes, including publication errata.

This release adds the ALG-02 group theory supplement.

## Library

| Subject | Public import |
| --- | --- |
| Single-variable analysis | `MathGenome.SingleVariableAnalysis` |
| Multivariable analysis | `MathGenome.MultivariableAnalysis` |
| Linear algebra | `MathGenome.LinearAlgebra` |
| Symmetric powers and Witt theory | `MathGenome.LinearAlgebraSupplement` |
| Abstract algebra | `MathGenome.AbstractAlgebra` |
| Point-set topology | `MathGenome.PointSetTopology` |
| Real analysis and measure theory | `MathGenome.RealAnalysis` |
| Complex analysis | `MathGenome.ComplexAnalysis` |
| Ordinary differential equations and dynamical systems | `MathGenome.ODEDynamics` |
| Functional analysis | `MathGenome.FunctionalAnalysis` |
| Fourier analysis, distributions, and Sobolev spaces | `MathGenome.FourierSobolev` |
| Rings and modules, commutative algebra, finite group representations, and basic homological algebra | `MathGenome.AlgebraCore` |
| Smooth manifolds and differential geometry | `MathGenome.SmoothManifolds` |
| Probability foundations | `MathGenome.ProbabilityFoundations` |
| Variational methods, convex analysis, and basic optimality | `MathGenome.VariationalMethods` |
| Classical and weak linear PDE | `MathGenome.LinearPDE` |
| Algebraic topology and Riemannian geometry | `MathGenome.TopologyRiemannianGeometry` |
| Elementary number theory | `MathGenome.ElementaryNumberTheory` |
| Finite combinatorics | `MathGenome.FiniteCombinatorics` |
| Extremal methods, networks, and matroid optimization | `MathGenome.ExtremalOptimization` |
| Foundations of numerical analysis | `MathGenome.NumericalAnalysis` |
| Discrete Markov chains and martingales | `MathGenome.DiscreteMarkovMartingales` |
| Advanced Commutative Algebra | `MathGenome.AdvancedCommutativeAlgebra` |
| Advanced Homological Algebra | `MathGenome.AdvancedHomologicalAlgebra` |
| Advanced Field Theory | `MathGenome.AdvancedFieldTheory` |
| Advanced Finite Group Representation Theory | `MathGenome.AdvancedFiniteGroupRepresentations` |
| Lie Algebras and Finite-Dimensional Representations | `MathGenome.LieAlgebrasAndRepresentations` |
| Group theory supplement | `MathGenome.GroupTheorySupplement` |

The [lecture notes index](docs/NOTES.md) links the PDF and LaTeX sources for each
subject. The [revised notes edition registry](docs/notes-revisions/v0.13.0/index.json)
records the exact revised files and their hashes.

Search the included catalog by topic, source ID, or linked Lean
declaration from the repository root with Python 3:

```sh
python tools/search.py Brouwer
```

For full declaration search, download `mathgenome-v0.25.0-declarations.zip`
from the [v0.25.0 Release](https://github.com/Xuanxuan-Zhao/MathGenome-Public/releases/tag/v0.25.0)
and save it in `catalog/`. The search tool reads the ZIP directly.

```sh
python tools/search.py --kind declarations ae_lebesguePoint
```

Catalog entries cite the corresponding lecture statements and give keywords,
the recommended Lean import, and the associated declarations. The lecture
source maps provide bibliographic references and links to the distributed notes.

## Build

Install Lean through [Elan](https://github.com/leanprover/elan) and run these
commands from the repository root:

```sh
lake build
lake build +MathGenomeChecks.AllModules:olean
```

The second command builds the release's aggregate module check. The first
build needs access to the dependency repositories and can take time.
[`lean-toolchain`](lean-toolchain) pins Lean **4.35.0**.
[`lake-manifest.json`](lake-manifest.json) pins Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679` and records the other Lake
dependencies.

## Use in a Lean project

Use the same Lean toolchain and pin MathGenome to a release tag in your
`lakefile.lean`. For v0.25.0, add this dependency and run `lake update`.

```lean
require mathGenome from git "https://github.com/Xuanxuan-Zhao/MathGenome-Public.git" @ "v0.25.0"
```

Then import the subject you need.

```lean
import MathGenome.GroupTheorySupplement

#check ALG02GroupTheory.Chief.AmbientCovBy
```

## Licenses

Original MathGenome Lean code is available under the
[Apache License 2.0](LICENSE). The original portions of the MathGenome
lecture notes, in PDF and LaTeX, are available under
[Creative Commons Attribution 4.0 International](LICENSES/CC-BY-4.0.txt).
When reusing the notes, preserve their supplied credits and identify the
lecture-note title, version, license, and any changes.
[Third-party notices](THIRD_PARTY_NOTICES.md) cover dependencies and material
cited in the notes.
