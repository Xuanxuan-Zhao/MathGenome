import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.MaximalIntegralCurves

/-! M06.08, paper.tex:1440–1444. All times in a recorded interval below are
absolute times. Thus restarting preserves that interval; in elapsed-time
coordinates this is exactly translation by the elapsed time. The time–state
set is an arbitrary open subset of `J × M`, not necessarily a product.
Euclidean model structures represent boundaryless manifolds, including dimension
zero and the empty manifold. No completeness assumption is made.
-/
namespace SmoothManifolds.EvolutionData
open ModelData AtlasData MapData TangentData TangentBundleData Set Filter
open scoped Topology
universe u

/-- The intrinsic coefficients of a section along the state projection.
Values outside the chart source are only an evaluation convention. -/
noncomputable def fieldCoefficients {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    {Ω : Set (ℝ × M)} (v : (z : Ω) → TangentSpace S z.val.2)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (z : Ω) : Euclidean n := by
  classical
  exact if h : z.val.2 ∈ e.source then B.fiberCoordinates.equiv e he z.val.2 h (v z) else 0

/-- A smooth time-dependent vector field is a smooth section along the state
projection on its actual domain. Continuity is in the existing tangent-bundle
topology; joint smoothness is the all-charts local ambient-extension test for
its fiber coordinates, with the time coordinate retained. -/
structure SmoothTimeDependentField {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (B : TangentBundleStructure S)
    (Ω : Set (ℝ × M)) where
  val : (z : Ω) → TangentSpace S z.val.2
  continuous : letI := B.topology
    Continuous (fun z : Ω => (⟨z.val.2, val z⟩ : TotalSpace S))
  smooth : ∀ (z : Ω) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val), z.val.2 ∈ e.source →
    ∃ U : Set (ℝ × Euclidean n), IsOpen U ∧ (z.val.1, (e z.val.2).val) ∈ U ∧
      ∃ G : ℝ × Euclidean n → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
        (fun w : Ω => G (w.val.1, (e w.val.2).val)) =ᶠ[𝓝 z]
          fieldCoefficients B val e he

/-- The nonautonomous equation in every smooth state chart. In particular its
graph must stay in Ω; no evaluation of the field outside Ω is allowed. -/
def IsIntegralCurveOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {Ω : Set (ℝ × M)} (X : SmoothTimeDependentField B Ω)
    (I : Set ℝ) (γ : ℝ → M) : Prop :=
  ContinuousOn γ I ∧ ∀ t ∈ I, ∃ h : (t, γ t) ∈ Ω,
    ∀ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
      (ht : γ t ∈ e.source),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun r => (e (γ r)).val) t ∧
      HasDerivAt (fun r => (e (γ r)).val)
        (B.fiberCoordinates.equiv e he (γ t) ht (X.val ⟨(t, γ t), h⟩)) t

/-- Universal maximality compares all solution intervals containing the initial
absolute time, including intervals not containing zero. Representatives are
compared only on their actual domains. -/
def IsMaximalThrough {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {Ω : Set (ℝ × M)} (X : SmoothTimeDependentField B Ω) (z : Ω)
    (I : D13Unified.OpenTimeInterval) (γ : ℝ → M) : Prop :=
  z.val.1 ∈ I.carrier ∧ γ z.val.1 = z.val.2 ∧ IsIntegralCurveOn X I.carrier γ ∧
    ∀ (K : D13Unified.OpenTimeInterval) (η : ℝ → M),
      z.val.1 ∈ K.carrier → η z.val.1 = z.val.2 → IsIntegralCurveOn X K.carrier η →
        K.carrier ⊆ I.carrier ∧ EqOn γ η K.carrier

/-- Raw data only: existence and all correctness clauses are theorem obligations. -/
structure EvolutionFamily {M : Type u} (Ω : Set (ℝ × M)) where
  interval : Ω → D13Unified.OpenTimeInterval
  curve : Ω → ℝ → M

def IsMaximalFamily {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {B : TangentBundleStructure S}
    {Ω : Set (ℝ × M)} (X : SmoothTimeDependentField B Ω)
    (F : EvolutionFamily Ω) : Prop :=
  ∀ z, IsMaximalThrough X z (F.interval z) (F.curve z)

/-- Triples are ordered `(terminal time, (initial time, initial state))`.
Invalid initial data are excluded, even if a representative happens to exist. -/
def evolutionDomain {M : Type u} {Ω : Set (ℝ × M)} (F : EvolutionFamily Ω) :
    Set (ℝ × (ℝ × M)) :=
  {q | ∃ h : q.2 ∈ Ω, q.1 ∈ (F.interval ⟨q.2, h⟩).carrier}

/-- A total representative with assertions only on `evolutionDomain`. Its value
at invalid initial data is irrelevant; using the supplied state avoids requiring
an inhabitant of M, so the empty-manifold case is included. -/
noncomputable def evolution {M : Type u} {Ω : Set (ℝ × M)}
    (F : EvolutionFamily Ω) (q : ℝ × (ℝ × M)) : M := by
  classical
  exact if h : q.2 ∈ Ω then F.curve ⟨q.2, h⟩ q.1 else q.2.2

def timeDomain {M : Type u} {Ω : Set (ℝ × M)}
    (F : EvolutionFamily Ω) (s t : ℝ) : Set M :=
  {p | (t, s, p) ∈ evolutionDomain F}

/-- The true elapsed-time interval at an initial time–state point. -/
def elapsedInterval {M : Type u} {Ω : Set (ℝ × M)}
    (F : EvolutionFamily Ω) (z : Ω) : Set ℝ :=
  {τ | z.val.1 + τ ∈ (F.interval z).carrier}

/-- Joint C-infinity regularity in both times and the state, tested using the
shared local extension convention in every pair of smooth state charts. -/
def EvolutionSmoothAt {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) {Ω : Set (ℝ × M)}
    (F : EvolutionFamily Ω) (q : ℝ × (ℝ × M)) : Prop :=
  ContinuousAt (evolution F) q ∧
  ∀ e ∈ S.smoothStructure.val, ∀ d ∈ S.smoothStructure.val,
    q.2.2 ∈ e.source → evolution F q ∈ d.source →
    ∃ U : Set (ℝ × (ℝ × Euclidean n)), IsOpen U ∧
      (q.1, q.2.1, (e q.2.2).val) ∈ U ∧
      ∃ G : ℝ × (ℝ × Euclidean n) → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) G U ∧
        (fun w : ℝ × (ℝ × M) => G (w.1, w.2.1, (e w.2.2).val)) =ᶠ[𝓝 q]
          (fun w => (d (evolution F w)).val)

/-- Exact restart domains, in absolute and elapsed time, and the evolution law.
Graph membership explicitly justifies forming the new initial point. -/
def HasRestartLaw {M : Type u} {Ω : Set (ℝ × M)} (F : EvolutionFamily Ω) : Prop :=
  ∀ (z : Ω) (u : ℝ), u ∈ (F.interval z).carrier →
    ∃ h : (u, F.curve z u) ∈ Ω,
      let w : Ω := ⟨(u, F.curve z u), h⟩
      (F.interval w).carrier = (F.interval z).carrier ∧
      elapsedInterval F w = {τ | (u - z.val.1) + τ ∈ elapsedInterval F z} ∧
      ∀ t ∈ (F.interval z).carrier, F.curve w t = F.curve z t

/-- Fixed initial/terminal time maps between the two actual open state domains. -/
def HasTimeDiffeomorphs {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) {Ω : Set (ℝ × M)}
    (F : EvolutionFamily Ω) : Prop :=
  ∀ s t : ℝ, ∃ (hU : IsOpen (timeDomain F s t)) (hV : IsOpen (timeDomain F t s)),
    ∃ h : Diffeomorph
      (openSubsetAtlas S.smoothStructure.val (timeDomain F s t) hU)
      (openSubsetAtlas S.smoothStructure.val (timeDomain F t s) hV),
      (∀ p : timeDomain F s t, (h.toEquiv p).val = evolution F (t, s, p.val)) ∧
      (∀ p : timeDomain F t s, (h.toEquiv.symm p).val = evolution F (s, t, p.val))

end SmoothManifolds.EvolutionData

namespace Specs.SmoothManifolds.Ch06.Evolution
open _root_.SmoothManifolds _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.TangentBundleData _root_.SmoothManifolds.EvolutionData Set
universe u

/-- No solution-existence or smooth-dependence certificate is assumed of X. -/
def maximal_family_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (J : Set ℝ), IsOpen J → OrdConnected J →
    ∀ (Ω : Set (ℝ × M)), IsOpen Ω → (∀ z ∈ Ω, z.1 ∈ J) →
    ∀ X : SmoothTimeDependentField B Ω,
      ∃ F : EvolutionFamily Ω, IsMaximalFamily X F

/-- Uniqueness of both maximal absolute intervals and values on those intervals. -/
def maximal_uniqueType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (Ω : Set (ℝ × M)) (X : SmoothTimeDependentField B Ω)
    (F G : EvolutionFamily Ω), IsMaximalFamily X F → IsMaximalFamily X G →
    ∀ z, (F.interval z).carrier = (G.interval z).carrier ∧
      EqOn (F.curve z) (G.curve z) (F.interval z).carrier

def domain_open_smoothType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (Ω : Set (ℝ × M)), IsOpen Ω →
    ∀ (X : SmoothTimeDependentField B Ω) (F : EvolutionFamily Ω), IsMaximalFamily X F →
      IsOpen (evolutionDomain F) ∧
      (∀ z : Ω, (z.val.1, z.val) ∈ evolutionDomain F) ∧
      ∀ q ∈ evolutionDomain F, EvolutionSmoothAt S F q

def restartType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (Ω : Set (ℝ × M)) (X : SmoothTimeDependentField B Ω)
    (F : EvolutionFamily Ω), IsMaximalFamily X F → HasRestartLaw F

def time_diffeomorphType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (Ω : Set (ℝ × M)), IsOpen Ω →
    ∀ (X : SmoothTimeDependentField B Ω) (F : EvolutionFamily Ω), IsMaximalFamily X F →
      HasTimeDiffeomorphs S F

/-- The complete source conclusion. Initial values and the differential equation
are included in `IsMaximalFamily`, not assumed independently of existence. -/
def evolution_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (B : TangentBundleStructure S)
    (J : Set ℝ), IsOpen J → OrdConnected J →
    ∀ (Ω : Set (ℝ × M)), IsOpen Ω → (∀ z ∈ Ω, z.1 ∈ J) →
    ∀ X : SmoothTimeDependentField B Ω,
    ∃ F : EvolutionFamily Ω, IsMaximalFamily X F ∧
      IsOpen (evolutionDomain F) ∧
      (∀ z : Ω, (z.val.1, z.val) ∈ evolutionDomain F) ∧
      (∀ q ∈ evolutionDomain F, EvolutionSmoothAt S F q) ∧
      HasRestartLaw F ∧ HasTimeDiffeomorphs S F ∧
      ∀ G : EvolutionFamily Ω, IsMaximalFamily X G →
        evolutionDomain G = evolutionDomain F ∧ EqOn (evolution G) (evolution F) (evolutionDomain F)

end Specs.SmoothManifolds.Ch06.Evolution
