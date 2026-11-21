import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Compact products of scalar disks: independent specification

Source: `paper.tex`, lemma `fa2:p1:c13:scalar-product-compactness`,
lines 2475–2479.

The scalar field is real or complex, represented by `RCLike`. A closed disk
centered at zero with radius `r i` is `{z | ‖z‖ ≤ r i}`. The function space
`I → 𝕜` carries its canonical product topology, so the displayed subset is
the Cartesian product of these disks. `IsCompact` also means that this subset,
with its subspace topology, is a compact space. There is no restriction on the
index type, and the nonnegative real radii may be zero.
-/

namespace ExpandedFA.P1.C13ScalarProductCompactnessSpec

/-- Arbitrary products of closed bounded scalar disks are compact, including
zero-radius disks and the empty product. -/
def CompactScalarDiskProducts : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (I : Type*) (r : I → ℝ),
    (∀ i, 0 ≤ r i) → IsCompact {z : I → 𝕜 | ∀ i, ‖z i‖ ≤ r i}

end ExpandedFA.P1.C13ScalarProductCompactnessSpec
