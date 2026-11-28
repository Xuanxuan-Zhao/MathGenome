# MathGenome

MathGenome is a mathematical knowledge base where you can look up and verify definitions, theorems, and proofs formalized in Lean. Our long-term goal is to formalize all theories across mathematics, so that every theorem has its own piece of mathematical DNA here.

From classic textbooks to the research literature, we link theorems to their original sources, proofs, and dependencies. In your own Lean projects, you can import the modules you need and reuse existing definitions and theorems directly. Follow those links to see how a theorem was proved and how it can become the starting point for another proof.

<details>
<summary>中文介绍</summary>

MathGenome 是一座可查阅、可核验的数学知识库，收录用 Lean 形式化的定义、定理与证明。我们的长远目标，是逐步形式化数学各领域的所有理论，让每一条定理都在这里拥有独属于自己的「基因片段」。

从经典教材到研究文献，我们把定理与原文、证明和依赖关系连在一起。在自己的 Lean 项目中，你可以导入所需模块，直接复用库中已有的定义和定理。沿着这些联系，你既能追溯一条定理如何得来，也能看到它如何成为下一段证明的起点。

</details>

[Explore MathGenome](https://mathgenome.org).

The current release, v0.32.0, adds Topics in Lie Theory, extending the ALG-08 collection.

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
| Rings, Modules, and Associative Algebras | `MathGenome.RingModuleAssociativeAlgebra` |
| Linear Algebraic Groups | `MathGenome.LinearAlgebraicGroups` |
| Topics in Commutative Algebra | `MathGenome.CommutativeAlgebraDeepening` |
| Topics in Homological Algebra | `MathGenome.HomologicalAlgebraDeepening` |
| Topics in Field and Galois Theory | `MathGenome.FieldAndGaloisTheoryDeepening` |
| Topics in Representation Theory | `MathGenome.RepresentationTheoryDeepening` |
| Topics in Lie Theory | `MathGenome.LieTheoryDeepening` |

The [lecture notes index](docs/NOTES.md) links the PDF and LaTeX sources for each
subject. The [revised notes edition registry](docs/notes-revisions/v0.13.0/index.json)
records the exact revised files and their hashes.

Search the included catalog by topic, source ID, or linked Lean
declaration from the repository root with Python 3:

```sh
python tools/search.py Brouwer
```

For full declaration search, download `mathgenome-v0.32.0-declarations.zip`
from the [v0.32.0 Release](https://github.com/Xuanxuan-Zhao/MathGenome/releases/tag/v0.32.0)
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
`lakefile.lean`. For v0.32.0, add this dependency and run `lake update`.

```lean
require mathGenome from git "https://github.com/Xuanxuan-Zhao/MathGenome.git" @ "v0.32.0"
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
