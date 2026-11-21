# Functional analysis supplements

These supplements record two mathematical results and their relation to the
published lecture and Lean library.

## Hilbert Moreau envelope

Let `φ` be a proper lower-semicontinuous convex function on a real Hilbert space
and let `λ > 0`. The Moreau envelope is continuously Fréchet differentiable.
Its gradient at `f` is `(f - prox_{λφ}(f)) / λ`.

The [Hilbert proximity chapter](../../notes-revisions/v0.13.0/D16/main.tex#L8431)
defines the proximal point and proves the primal–dual identities. The
[Lean regularity theorem](../../../MathGenome/Internal/FunctionalAnalysis/ExpandedFA/Proximal/EnvelopeGradient.lean#L139)
is available through `MathGenome.FunctionalAnalysis.Topics.ExpandedFA.Proximal`.

## Range of a bounded normal operator and its adjoint

For a bounded normal operator `T` on a real or complex Hilbert space, the
actual ranges of `T` and `T*` agree. The common range need not be closed.

In the [polar decomposition](../../notes-revisions/v0.13.0/D16/main.tex#L12608)
`T = U|T|`, the normal case makes `U` commute with `|T|`. The initial and
final projections of `U` both project onto the orthogonal complement of the
kernel of `T`. Thus `T = |T|U` and `|T| = TU*`, which give equality of
the ranges of `T` and `|T|`. The same argument for `T*` gives the result.

The published Lean library contains the
[spectral theorem](../../../MathGenome/Internal/FunctionalAnalysis/ExpandedFA/SpectralMeasure/NormalSpectral.lean#L99)
and [polar decomposition](../../../MathGenome/Internal/FunctionalAnalysis/ExpandedFA/SpectralMeasure/PolarDecomposition.lean#L456).
The website also provides an independently checked Lean supplement for the
range equality.
