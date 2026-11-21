import MathGenome.Internal.Specs.D07.Ch15.TrisectAngle
import MathGenome.Internal.D07.Ch15.DegreeObstruction
import MathGenome.Internal.D07.Ch15.GeometricFieldOperations
import MathGenome.Internal.D07.Ch11.LowDegreeIrreducible
import MathGenome.Internal.D07.Ch11.RationalRoot
import Mathlib.Tactic.ComputeDegree

namespace D07.Ch15.TrisectAngle
open Polynomial IntermediateField StraightedgeCompass
open Specs.D07.Ch15.TrisectAngle

lemma cubic_monic : trisectionCubic.Monic := by
  unfold trisectionCubic
  monicity <;> norm_num

lemma cubic_degree : trisectionCubic.degree = 3 := by
  unfold trisectionCubic
  compute_degree <;> norm_num

lemma cubic_natDegree : trisectionCubic.natDegree = 3 :=
  natDegree_eq_of_degree_eq_some cubic_degree

/-- Integral rational roots divide -1, so are ±1. Neither is a root. -/
lemma cubic_no_rational_root (q : ℚ) : trisectionCubic.eval q ≠ 0 := by
  intro hq
  let f : Polynomial ℤ := X ^ 3 - C 3 * X - 1
  have hf : f.Monic := by dsimp [f]; monicity <;> norm_num
  have hroot : aeval q f = 0 := by
    change f.eval₂ (algebraMap ℤ ℚ) q = 0
    norm_num [f, trisectionCubic] at hq ⊢
    exact hq
  obtain ⟨z, hz, hd⟩ := exists_integer_of_is_root_of_monic hf hroot
  have hd' : z ∣ (1 : ℤ) := by
    simpa [f] using hd
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hd') with h | h
  · subst z
    norm_num at hz
    rw [hz] at hq
    norm_num [trisectionCubic] at hq
  · subst z
    norm_num at hz
    rw [hz] at hq
    norm_num [trisectionCubic] at hq

lemma cubic_irreducible : Irreducible trisectionCubic :=
  (Ch11.LowDegreeIrreducible.degree_two_or_three_iff_no_root ℚ trisectionCubic
    (Or.inr cubic_degree)).mpr cubic_no_rational_root

lemma twice_cos_root : aeval (2 * Real.cos (Real.pi / 9)) trisectionCubic = 0 := by
  have h := Real.cos_three_mul (Real.pi / 9)
  rw [show 3 * (Real.pi / 9) = Real.pi / 3 by ring, Real.cos_pi_div_three] at h
  norm_num [trisectionCubic]
  nlinarith

theorem twenty_degree : TwentyDegree := by
  have hi : IsIntegral ℚ (2 * Real.cos (Real.pi / 9)) :=
    ⟨trisectionCubic, cubic_monic, twice_cos_root⟩
  have hm : minpoly ℚ (2 * Real.cos (Real.pi / 9)) = trisectionCubic :=
    (minpoly.eq_of_irreducible_of_monic cubic_irreducible twice_cos_root cubic_monic).symm
  exact ⟨hi, hm, by rw [adjoin.finrank hi, hm, cubic_natDegree]⟩

/-- Geometric normalization uses the radius recovered from the two coordinates. -/
theorem normalize_ray : NormalizeRay := by
  intro P θ
  constructor
  · rintro ⟨r, hr, hp⟩
    have hx : IsConstructibleReal P (r * Real.cos θ) :=
      constructible_project_fst P _ hp
    have hy : IsConstructibleReal P (r * Real.sin θ) := constructible_snd_real hp
    have hx2 := constructible_mul P _ _ hx hx
    have hy2 := constructible_mul P _ _ hy hy
    have he : (r * Real.cos θ) * (r * Real.cos θ) +
        (r * Real.sin θ) * (r * Real.sin θ) = r ^ 2 := by
      calc
        _ = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
        _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    have hr2 : IsConstructibleReal P (r ^ 2) := by
      rw [← he]; exact constructible_add P _ _ hx2 hy2
    have hrad : IsConstructibleReal P r := by
      simpa [Real.sqrt_sq (le_of_lt hr)] using
        constructible_sqrt P _ hr2 (sq_nonneg r)
    have hc := constructible_div P _ _ hx hrad (ne_of_gt hr)
    have hs := constructible_div P _ _ hy hrad (ne_of_gt hr)
    have hcn : (r * Real.cos θ) / r = Real.cos θ :=
      mul_div_cancel_left₀ _ (ne_of_gt hr)
    have hsn : (r * Real.sin θ) / r = Real.sin θ :=
      mul_div_cancel_left₀ _ (ne_of_gt hr)
    rw [hcn] at hc
    rw [hsn] at hs
    exact constructible_combine P _ _ hc hs
  · intro h
    exact ⟨1, zero_lt_one, by simpa using h⟩

theorem constructible_sixty : ConstructibleSixty := by
  intro P
  apply (normalize_ray P _).mpr
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  have h1 := constructible_one P
  have h2 : IsConstructibleReal P 2 := by
    convert constructible_add P 1 1 h1 h1 using 1; norm_num
  have h3 : IsConstructibleReal P 3 := by
    convert constructible_add P 2 1 h2 h1 using 1; norm_num
  exact constructible_combine P _ _
    (constructible_div P _ _ h1 h2 (by norm_num))
    (constructible_div P _ _ (constructible_sqrt P 3 h3 (by norm_num)) h2 (by norm_num))

lemma rational_coordinateField (P : InitialData) (hP : RationalInitialData P) :
    coordinateField P = ⊥ := by
  apply le_antisymm _ bot_le
  apply adjoin_le_iff.mpr
  rintro x (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
  · obtain ⟨a, b, rfl⟩ := hP p hp
    exact IntermediateField.algebraMap_mem _ a
  · obtain ⟨a, b, rfl⟩ := hP p hp
    exact IntermediateField.algebraMap_mem _ b

/-- With rational initial data the geometric coordinate field is the
canonical copy of ℚ. Restriction of scalars identifies the two simple fields. -/
lemma twice_cos_not_constructible (P : InitialData) (hP : RationalInitialData P) :
    ¬ IsConstructibleReal P (2 * Real.cos (Real.pi / 9)) := by
  intro hc
  let b : ℝ := 2 * Real.cos (Real.pi / 9)
  let K : IntermediateField ℚ ℝ := ⊥
  have hi : IsIntegral ℚ b := twenty_degree.1
  have hiK : IsIntegral K b := hi.tower_top
  have hfield : coordinateField P = K := rational_coordinateField P hP
  have hiP : IsIntegral (coordinateField P) b := by rw [hfield]; exact hiK
  obtain ⟨n, hn⟩ := DegreeObstruction.geometric_necessary_degree P b hiP hc
  change Module.finrank (coordinateField P) (coordinateField P)⟮b⟯ = 2 ^ n at hn
  rw [hfield] at hn
  let : FiniteDimensional K K⟮b⟯ := adjoin.finiteDimensional hiK
  have heq : (K⟮b⟯ : IntermediateField K ℝ).restrictScalars ℚ = ℚ⟮b⟯ := by
    rw [restrictScalars_adjoin_eq_sup]
    exact bot_sup_eq _
  have hd : Module.finrank ℚ (K⟮b⟯ : IntermediateField K ℝ) = 3 := by
    change Module.finrank ℚ ((K⟮b⟯ : IntermediateField K ℝ).restrictScalars ℚ) = 3
    rw [heq]
    exact twenty_degree.2.2
  rw [← Module.finrank_mul_finrank ℚ K K⟮b⟯,
    show Module.finrank ℚ K = 1 by simp [K], one_mul, hn] at hd
  have hthree : 3 ∣ 2 ^ n := by rw [hd]
  have hbad := Nat.prime_three.dvd_of_dvd_pow hthree
  norm_num at hbad

theorem no_trisection_sixty : NoTrisectionSixty := by
  intro P hP ha
  have hangle : (Real.pi / 3) / 3 = Real.pi / 9 := by ring
  rw [hangle] at ha
  have hp := (normalize_ray P _).mp ha
  have hc : IsConstructibleReal P (Real.cos (Real.pi / 9)) :=
    constructible_project_fst P _ hp
  have htwo : IsConstructibleReal P 2 := by
    convert constructible_add P 1 1 (constructible_one P) (constructible_one P) using 1
    norm_num
  exact twice_cos_not_constructible P hP (constructible_mul P _ _ htwo hc)

/-- A construction can be replayed after constructing its initial points.
This is a statement about finite histories and permitted intersection steps. -/
lemma constructible_from_constructible_data (P Q : InitialData)
    (hQ : ∀ p ∈ Q.points, IsConstructible P p) {p : Point}
    (hp : IsConstructible Q p) : IsConstructible P p := by
  obtain ⟨S, hS, hpS⟩ := hp
  have hall : ∀ q ∈ S, IsConstructible P q := by
    clear hpS
    induction hS with
    | initial => exact hQ
    | @step S q hS hq ih =>
      obtain ⟨T, hT, hST⟩ := constructible_finite_available hS.finite ih
      have hnew : IsConstructible P q :=
        ⟨insert q T, hT.step (hq.mono hST), Set.mem_insert q T⟩
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · exact hnew
      · exact ih a ha
  exact hall p hpS

theorem no_trisection_from_constructible_data : NoTrisectionFromConstructibleData := by
  intro P Q hP hQ hangle
  obtain ⟨r, hr, hp⟩ := hangle
  exact no_trisection_sixty P hP
    ⟨r, hr, constructible_from_constructible_data P Q hQ hp⟩

theorem straight_angle_trisectable : StraightAngleTrisectable := by
  intro P
  refine ⟨?_, constructible_sixty P⟩
  apply (normalize_ray P _).mpr
  rw [Real.cos_pi, Real.sin_pi]
  exact constructible_neg P 1 (constructible_one P)

theorem no_universal_trisection : NoUniversalTrisection := by
  intro P hP hall
  exact no_trisection_sixty P hP
    (hall (Real.pi / 3) (by positivity) (by linarith [Real.pi_pos])
      (constructible_sixty P))

end D07.Ch15.TrisectAngle
