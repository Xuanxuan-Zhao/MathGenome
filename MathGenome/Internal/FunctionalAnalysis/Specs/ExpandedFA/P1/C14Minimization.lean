import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14BallCharacterization
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12NormLsc

/-!
Independent statements for fa2:p1:c14:minimization, paper.tex 2994–3005.
`WithTop ℝ` is precisely ℝ ∪ {+∞}; there is no −∞ value. The function
is defined on C itself. Closedness and lower semicontinuity use σ(E,E′)
and its induced topology on C, while boundedness and coercivity use the
original norm. The convex specialization is included below.
-/
namespace ExpandedFA.P1.C14Minimization.Spec
universe u v
noncomputable section

/-- The ambient realization of a real sublevel of a function on C. -/
def sublevel {E : Type v} (C : Set E) (Φ : C → WithTop ℝ) (a : ℝ) : Set E :=
  Subtype.val '' {x : C | Φ x ≤ (a : WithTop ℝ)}

/-- Every real sublevel is bounded in the original norm. -/
def BoundedSublevels {E : Type v} [NormedAddCommGroup E]
    (C : Set E) (Φ : C → WithTop ℝ) : Prop :=
  ∀ a : ℝ, Bornology.IsBounded (sublevel C Φ a)

/-- The explicit threshold form of Φ(x) → +∞ as ‖x‖ → ∞ on C. -/
def Coercive {E : Type v} [NormedAddCommGroup E]
    (C : Set E) (Φ : C → WithTop ℝ) : Prop :=
  ∀ a : ℝ, ∃ R : ℝ, ∀ x : C, R ≤ ‖(x : E)‖ → (a : WithTop ℝ) < Φ x

/-- Lower semicontinuity for the relative weak topology, with the original dual. -/
def WeakLowerSemicontinuous (𝕜 : Type u) {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (C : Set E)
    (Φ : C → WithTop ℝ) : Prop :=
  letI : TopologicalSpace E := C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)
  LowerSemicontinuous Φ

/-- A minimizer with a real value, not just an extended-real infimum. -/
def FiniteMinimum {E : Type v} (C : Set E) (Φ : C → WithTop ℝ) : Prop :=
  ∃ x₀ : C, ∃ m : ℝ, Φ x₀ = (m : WithTop ℝ) ∧ ∀ x : C, Φ x₀ ≤ Φ x

def Attainment : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (C : Set E), C.Nonempty →
    @IsClosed E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) C →
    ∀ Φ : C → WithTop ℝ, (∃ a : C, Φ a ≠ ⊤) →
    WeakLowerSemicontinuous 𝕜 C Φ → BoundedSublevels C Φ → FiniteMinimum C Φ

def BoundedDomainSublevels : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] (C : Set E) (Φ : C → WithTop ℝ),
    Bornology.IsBounded C → BoundedSublevels C Φ

def CoerciveSublevels : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] (C : Set E) (Φ : C → WithTop ℝ),
    Coercive C Φ → BoundedSublevels C Φ

end
end ExpandedFA.P1.C14Minimization.Spec

/-!
Independent statements for the complete direct-method conclusion of
`fa2:p1:c14:minimization`, paper.tex 2994–3005, and its convex specialization.
The shared `WithTop ℝ` representation excludes −∞. Properness means that
the restriction to C has a finite value; no global finite-domain condition
is imposed. Convexity uses real scalars also when the ambient field is complex.
All boundedness and coercivity conditions use the original norm, whereas
weak closedness and weak lower semicontinuity use the original continuous
scalar-linear dual and the relative topology on C.
-/
namespace ExpandedFA.P1.C14Minimization.Spec
universe u v
noncomputable section

/-- The general direct method has no convexity assumption. Each of the three
displayed boundedness hypotheses suffices independently. -/
def GeneralDirectMethod : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    ∀ (C : Set E), C.Nonempty →
    @IsClosed E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) C →
    ∀ Φ : C → WithTop ℝ, (∃ a : C, Φ a ≠ ⊤) →
    WeakLowerSemicontinuous 𝕜 C Φ →
    (BoundedSublevels C Φ ∨ Coercive C Φ ∨ Bornology.IsBounded C) →
    FiniteMinimum C Φ

/-- The hypotheses of the convex specialization imply the required weak
regularity. This bridge needs neither completeness nor reflexivity. -/
def ConvexApplicability : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (C : Set E), Convex ℝ C → IsClosed C →
    ∀ Φ : E → WithTop ℝ,
    Convex ℝ {p : E × ℝ | Φ p.1 ≤ (p.2 : WithTop ℝ)} →
    LowerSemicontinuous Φ →
    @IsClosed E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) C ∧
    @LowerSemicontinuous E (WithTop ℝ)
      (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) inferInstance Φ ∧
    WeakLowerSemicontinuous 𝕜 C (fun x : C => Φ (x : E))

/-- A proper restriction of a norm-l.s.c. convex extended-real function to
a nonempty norm-closed convex set attains a finite minimum. Bounded real
sublevels, coercivity on C, or boundedness of C each suffice. No norm
compactness, separability, or nontriviality assumption is present. -/
def ConvexDirectMethod : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (C : Set E), C.Nonempty → Convex ℝ C → IsClosed C →
    ∀ Φ : E → WithTop ℝ,
    Convex ℝ {p : E × ℝ | Φ p.1 ≤ (p.2 : WithTop ℝ)} →
    LowerSemicontinuous Φ →
    (∃ a : C, Φ (a : E) ≠ ⊤) →
    (BoundedSublevels C (fun x : C => Φ (x : E)) ∨
      Coercive C (fun x : C => Φ (x : E)) ∨ Bornology.IsBounded C) →
    FiniteMinimum C (fun x : C => Φ (x : E))

end
end ExpandedFA.P1.C14Minimization.Spec
