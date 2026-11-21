import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Degree.SphereNonextension
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.NoRetraction
import Mathlib.Tactic.Linarith

/-!
A topological proof of the manuscript's nonextension conclusions.
MathGenome's no-retraction theorem applies to the L² Euclidean norm. We prove
its exact relation to the shared sum-of-squares coordinates before applying it.
This direct proof excludes even continuous extensions, and thus needs no
approximation that could change boundary values.

The proof is independent of the degree-property interfaces. In particular,
no relative approximation or additional boundary regularity is assumed.
-/
noncomputable section
set_option autoImplicit false

namespace SmoothManifolds.SphereNonextension
open ModelData AtlasData MapData SphereTorusData SphereNonextensionData
open scoped BigOperators

lemma norm_sq_coordinates {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    ‖x‖ ^ 2 = squareSum (WithLp.ofLp x) := by
  simpa only [squareSum] using EuclideanSpace.real_norm_sq_eq x

lemma norm_le_one_of_squareSum_le {m : ℕ} (x : Euclidean m)
    (hx : squareSum x ≤ 1) : ‖WithLp.toLp 2 x‖ ≤ 1 := by
  have h := norm_sq_coordinates (WithLp.toLp 2 x)
  change ‖WithLp.toLp 2 x‖ ^ 2 = squareSum x at h
  nlinarith [norm_nonneg (WithLp.toLp 2 x)]

lemma norm_eq_one_of_squareSum_eq {m : ℕ} (x : Euclidean m)
    (hx : squareSum x = 1) : ‖WithLp.toLp 2 x‖ = 1 := by
  have h := norm_sq_coordinates (WithLp.toLp 2 x)
  change ‖WithLp.toLp 2 x‖ ^ 2 = squareSum x at h
  nlinarith [norm_nonneg (WithLp.toLp 2 x)]

/-- Exact transport of the literal boundary-value problem to MathGenome's
L² ball/sphere statement; includes n=0, where the ambient dimension is one. -/
lemma no_continuous_extension (n : ℕ) :
    ¬ ∃ F : ClosedBall n → Sphere n,
      Continuous F ∧ ∀ x : Sphere n, F (boundaryInclusion x) = x := by
  rintro ⟨F, hF, hfix⟩
  let b : {x : EuclideanSpace ℝ (Fin (n + 1)) // ‖x‖ ≤ 1} → ClosedBall n :=
    fun x => ⟨WithLp.ofLp x.val, by
      have h := norm_sq_coordinates x.val
      have hnonneg := norm_nonneg x.val
      have hle := x.property
      change squareSum (WithLp.ofLp x.val) ≤ 1
      nlinarith⟩
  let s : Sphere n → {x : EuclideanSpace ℝ (Fin (n + 1)) // ‖x‖ = 1} :=
    fun x => ⟨WithLp.toLp 2 x.val, norm_eq_one_of_squareSum_eq x.val x.property⟩
  have hb : Continuous b :=
    ((PiLp.continuous_ofLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
      continuous_subtype_val).subtype_mk _
  have hs : Continuous s :=
    ((PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
      continuous_subtype_val).subtype_mk _
  apply D10Topology.Ch17.no_retraction_ball_sphere (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  refine ⟨s ∘ F ∘ b, hs.comp (hF.comp hb), ?_⟩
  intro y
  let x : Sphere n := ⟨WithLp.ofLp y.val, by
    have h := norm_sq_coordinates y.val
    rw [y.property] at h
    exact h.symm.trans (by norm_num)⟩
  have hbdy : b ⟨y.val, y.property.le⟩ = boundaryInclusion x := rfl
  change s (F (b ⟨y.val, y.property.le⟩)) = y
  rw [hbdy, hfix x]

theorem continuous_nonextension :
    Specs.SmoothManifolds.Degree.SphereNonextension.continuous_nonextensionType := by
  exact no_continuous_extension

theorem smooth_nonextension :
    Specs.SmoothManifolds.Degree.SphereNonextension.smooth_nonextensionType := by
  intro n _ S T ⟨F, hF, hfix⟩
  exact no_continuous_extension n
    ⟨F, continuous_iff_continuousAt.mpr (fun x => (hF x).1), hfix⟩

theorem zero_dimensional_nonextension :
    Specs.SmoothManifolds.Degree.SphereNonextension.zero_dimensional_nonextensionType := by
  exact no_continuous_extension 0

end SmoothManifolds.SphereNonextension
