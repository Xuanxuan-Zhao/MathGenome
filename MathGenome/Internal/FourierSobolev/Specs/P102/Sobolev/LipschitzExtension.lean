import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzGeometry
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.BiLipschitzPullback
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.WholeSpaceDensity

/-! Independent scope of paper.tex:1734–1778 and 2023–2030.
The geometric hypothesis is exactly the shared one-sided Lipschitz graph
condition. An arbitrary linear isometry identifies the graph-coordinate
ambient space with the shared Euclidean coordinate space. Thus m=0 includes
dimension one. Neither connectedness nor C¹ boundary regularity is assumed.
The formula below is fixed before choosing either scalar field or exponent.
All expected theorem types remain unconditional propositions. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology

namespace P102.Sobolev.Extension
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry

/-- The open set in the graph-coordinate model, with no change of geometry. -/
def geometricOpen {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))) : Opens (Ambient m) :=
  ⟨e ⁻¹' (Ω : Set (Space (m + 1))), Ω.isOpen.preimage e.continuous⟩

/-- Purely geometric finite localization. Compact supports inside full charts
supply the collars needed at the artificial chart boundaries. -/
structure Localization {m : ℕ} (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))) where
  count : ℕ
  chart : Fin count → BoundaryChart (geometricOpen e Ω : Set (Ambient m))
  cutoff : Fin (count + 1) → Ambient m → ℝ
  smooth : ∀ i, ContDiff ℝ ∞ (cutoff i)
  compact : ∀ i, HasCompactSupport (cutoff i)
  nonneg : ∀ i z, 0 ≤ cutoff i z
  partition : ∀ z ∈ (geometricOpen e Ω : Set (Ambient m)), ∑ i, cutoff i z = 1
  interior_support : tsupport (cutoff 0) ⊆ (geometricOpen e Ω : Set (Ambient m))
  boundary_support : ∀ i, tsupport (cutoff i.succ) ⊆
    chartImage (chart i).frame (chart i).graphFunction (chart i).center
      (chart i).radius (chart i).height

/-- Conjugate reflection by the Lipschitz flattening and the rigid frame.
No derivative of the boundary graph is assumed in this definition. -/
def reflectedPoint {m : ℕ} {G : Set (Ambient m)} (C : BoundaryChart G)
    (z : Ambient m) : Ambient m :=
  let w := unshear C.graphFunction (C.frame.symm z)
  C.frame (shear C.graphFunction (WithLp.toLp 2 (w.ofLp.1, -w.ofLp.2)))

/-- Localized functions vanish outside the actual open set. -/
def localizedValue {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1)))
    (χ : Ambient m → ℝ) (f : Space (m + 1) → 𝕜) : Ambient m → 𝕜 :=
  (geometricOpen e Ω : Set (Ambient m)).indicator (fun z => χ z • f (e z))

/-- The source's fixed cutoff/reflection formula, with zero values on the
flattened boundary. Its definition has no exponent or Sobolev certificate. -/
def rawExtension {m : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)} {Ω : Opens (Space (m + 1))}
    (D : Localization e Ω) (f : Space (m + 1) → 𝕜) (x : Space (m + 1)) : 𝕜 :=
  localizedValue e Ω (D.cutoff 0) f (e.symm x) +
    ∑ i : Fin D.count,
      (chartImage (D.chart i).frame (D.chart i).graphFunction (D.chart i).center
        (D.chart i).radius (D.chart i).height).indicator
        (fun z => localizedValue e Ω (D.cutoff i.succ) f z +
          localizedValue e Ω (D.cutoff i.succ) f (reflectedPoint (D.chart i) z)) (e.symm x)

/-- Smooth ambient representatives for every coordinate of a domain Sobolev jet. -/
def RepresentsOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Space d → 𝕜) (u : Sobolev 𝕜 Ω k p) : Prop :=
  ∀ α : SobolevIndex d k,
    sobolevDerivative u α =ᵐ[volume.restrict (Ω : Set (Space d))] multiPartial f α.val

namespace Expected

/-- One localization, one bounded support set, and constants independent of the
scalar field. The zero-order constant B r is independent of the Sobolev exponent
p. Representative invariance also gives agreement on intersections of exponents. -/
def Extension : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∃ (D : Localization e Ω) (K : Compacts (Space (m + 1)))
      (C B : ℝ≥0∞ → ℝ≥0),
      (∀ (𝕜 : Type) [RCLike 𝕜] (f g : Space (m + 1) → 𝕜),
        f =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] g →
        rawExtension D f =ᵐ[volume] rawExtension D g) ∧
      ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
        ∃ E : Sobolev 𝕜 Ω 1 p →L[𝕜] Sobolev 𝕜 (⊤ : Opens (Space (m + 1))) 1 p,
          (∀ u, sobolevUnderlying (E u) =ᵐ[volume] rawExtension D (sobolevUnderlying u)) ∧
          (∀ u, sobolevUnderlying (E u) =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))]
            sobolevUnderlying u) ∧
          (∀ u, ∀ᵐ x ∂volume, x ∉ (K : Set (Space (m + 1))) → sobolevUnderlying (E u) x = 0) ∧
          ‖E‖ ≤ C p ∧
          ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)] (u : Sobolev 𝕜 Ω 1 p),
            MemLp (sobolevUnderlying u) r (volume.restrict (Ω : Set (Space (m + 1)))) →
            MemLp (sobolevUnderlying (E u)) r volume ∧
            eLpNorm (sobolevUnderlying (E u)) r volume ≤
              (B r : ℝ≥0∞) * eLpNorm (sobolevUnderlying u) r
                (volume.restrict (Ω : Set (Space (m + 1))))

/-- Restrictions of ambient compactly supported smooth functions are dense in
the full W¹ᵖ norm. No vanishing boundary values are imposed on the restrictions. -/
def Density : Prop :=
  ∀ (m : ℕ) (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Opens (Space (m + 1))),
    IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)) →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
      ∀ u : Sobolev 𝕜 Ω 1 p,
        ∃ (φ : ℕ → WholeTests (m + 1) 𝕜) (v : ℕ → Sobolev 𝕜 Ω 1 p),
          (∀ n, RepresentsOn (φ n) (v n)) ∧ Tendsto v atTop (𝓝 u)

end Expected
end P102.Sobolev.Extension
