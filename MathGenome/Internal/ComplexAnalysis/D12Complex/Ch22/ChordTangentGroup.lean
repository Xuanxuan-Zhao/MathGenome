import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.ChordTangentGroup
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.SecantAddition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.TangentAddition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.ExceptionalAddition
import Mathlib.Tactic.FinCases

noncomputable section
open scoped Classical

namespace D12Complex.ChordTangentGroup
open TorusSurface CubicFiniteCharts CubicInfinityChart ExceptionalAddition
open TorusCubicLocalMap (phi)
open ProjectivePlaneTopology (coordinatePatch)
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)

/-- Coordinates of the reflection of the third nonvertical secant intersection. -/
def secantCoordinates (x y u v : ℂ) : ℂ × ℂ :=
  let m := (y-v)/(x-u)
  let a := -x-u+m^2/4
  (a, -y+m*(x-a))

/-- Coordinates of the reflection of the third nonvertical tangent intersection. -/
def tangentCoordinates (G x y : ℂ) : ℂ × ℂ :=
  let m := (12*x^2-G)/(2*y)
  let a := -2*x+m^2/4
  (a, -y+m*(x-a))

/-- The five exhaustive geometric rules, without a transported-group assumption.
The third clause includes a vertical tangent when y=0. The first two clauses
include the infinity tangent O+O=O. The last clause includes flexes. -/
def GeometricSum {ω₁ ω₂ : ℂ} (P Q R : E ω₁ ω₂) : Prop :=
  (P.val = O ∧ R = Q) ∨
  (Q.val = O ∧ R = P) ∨
  (∃ x y : ℂ, P.val = affinePoint x y ∧ Q.val = affinePoint x (-y) ∧ R.val = O) ∨
  (∃ x y u v : ℂ, P.val = affinePoint x y ∧ Q.val = affinePoint u v ∧ x ≠ u ∧
    R.val = affinePoint (secantCoordinates x y u v).1 (secantCoordinates x y u v).2) ∨
  (∃ x y : ℂ, P.val = affinePoint x y ∧ Q = P ∧ y ≠ 0 ∧
    R.val = affinePoint (tangentCoordinates (g₂ ω₁ ω₂) x y).1
      (tangentCoordinates (g₂ ω₁ ω₂) x y).2)

/-- Transport of the actual abelian group ℂ/Λ. No curve group theorem is assumed. -/
@[instance_reducible] def groupStructure {ω₁ ω₂ : ℂ} (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂) :
    AddCommGroup (E ω₁ ω₂) := e.symm.addCommGroup


/-- Compatibility with Φ fixes the equivalence, so transport involves no choice
of a different curve parametrization. Existence uses the actual biholomorphism. -/
theorem equivalence_exists_unique :
    Specs.D12Complex.Ch22.ChordTangentGroup.equivalence_exists_unique_type := by
  intro ω₁ ω₂ h₁ h₂
  obtain ⟨e, he⟩ := ExceptionalAddition.equivalence_exists ω₁ ω₂ h₁ h₂
  refine ⟨e, he, ?_⟩
  intro f hf
  apply Equiv.ext
  intro t
  exact Subtype.ext ((hf t).trans (he t).symm)

theorem group_laws : Specs.D12Complex.Ch22.ChordTangentGroup.group_laws_type := by
  intro ω₁ ω₂ e
  letI := groupStructure e
  refine ⟨(fun _ _ => rfl), rfl, (fun _ => rfl), ?_, ?_, ?_⟩
  · exact fun P Q R => _root_.add_assoc P Q R
  · exact fun P Q => _root_.add_comm P Q
  · intro P
    exact ⟨_root_.zero_add P, _root_.add_zero P, _root_.neg_add_cancel P,
      _root_.add_neg_cancel P⟩

theorem group_isomorphism : Specs.D12Complex.Ch22.ChordTangentGroup.group_isomorphism_type := by
  intro ω₁ ω₂ e
  letI := groupStructure e
  refine ⟨{ toEquiv := e, map_add' := ?_ }, rfl⟩
  intro t s
  change e (t+s) = e (e.symm (e t) + e.symm (e s))
  simp only [e.symm_apply_apply]

lemma cubic_point_cases (G H : ℂ) (P : Cubic G H) :
    P.val = O ∨ ∃ x y : ℂ, P.val = affinePoint x y ∧ y^2 = q G H x := by
  by_cases hf : P.val ∈ coordinatePatch 0
  · right
    exact ⟨finiteX P.val, finiteY P.val, (affinePoint_coordinates hf).symm,
      (affine_equation G H P.val hf).mp P.property⟩
  · exact Or.inl (eq_O_of_not_finite G H P.property hf)

lemma tangent_transport {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂/ω₁).im)
    (e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂))
    (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (P : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) (x y : ℂ)
    (hP : P.val = affinePoint x y) (hy : y ≠ 0) :
    let m := (12*x^2-g₂ ω₁ ω₂)/(2*y)
    let x₂ := -2*x+m^2/4
    let y₂ := -y+m*(x-x₂)
    (transportedAdd e P P).val = affinePoint x₂ y₂ := by
  have hcurve : y^2 = q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) x :=
    (onCubic_affinePoint_iff _ _ x y).mp (hP ▸ P.property)
  obtain ⟨z, hz, hx, hdy⟩ := TorusCubicBiholomorphism.finite_values_surjective h₁ h₂ x y hcurve
  have hPt : e (projection ω₁ ω₂ z) = P := by
    apply Subtype.ext
    calc
      (e (projection ω₁ ω₂ z)).val = phi ω₁ ω₂ (projection ω₁ ω₂ z) := he _
      _ = affinePoint (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z) :=
        TorusCubicLocalMap.phi_finite h₁ h₂ hz
      _ = affinePoint x y := by rw [hx, hdy]
      _ = P.val := hP.symm
  have hd := TangentAddition.tangent_doubling ω₁ ω₂ h₁ h₂ z hz
    (by simpa only [hdy] using hy)
  dsimp only at hd ⊢
  rw [hx, hdy] at hd
  calc
    (transportedAdd e P P).val =
        (e (projection ω₁ ω₂ z + projection ω₁ ω₂ z)).val := by
      rw [← hPt, ExceptionalAddition.Transport.add_apply]
    _ = phi ω₁ ω₂ (projection ω₁ ω₂ z + projection ω₁ ω₂ z) := he _
    _ = _ := hd.2.2.2.2


open ProjectivePlaneTopology

def reflectedRepresentative (v : HomogeneousVector) : HomogeneousVector :=
  ⟨![v.val 0, v.val 1, -v.val 2], by
    intro h
    apply v.property
    ext i
    fin_cases i
    · simpa using congrFun h 0
    · simpa using congrFun h 1
    · simpa using congrFun h 2⟩

lemma reflectedRepresentative_finite {v : HomogeneousVector} (hz : v.val 0 ≠ 0) :
    ProjectivePlaneTopology.projection (reflectedRepresentative v) =
      affinePoint (v.val 1 / v.val 0) (-(v.val 2 / v.val 0)) := by
  have hp : ProjectivePlaneTopology.projection (reflectedRepresentative v) ∈ coordinatePatch 0 := by
    apply (projection_mem_patch_iff _ _).mpr
    exact hz
  symm
  convert affinePoint_coordinates hp using 1 <;>
    simp [finiteX, finiteY, coordinateRatio_projection, reflectedRepresentative, neg_div]

lemma transportedNeg_homogeneous {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂))
    (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (P : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) (v : HomogeneousVector)
    (hv : ProjectivePlaneTopology.projection v = P.val) :
    (transportedNeg e P).val = ProjectivePlaneTopology.projection (reflectedRepresentative v) := by
  by_cases hz : v.val 0 = 0
  · have hfin : P.val ∉ coordinatePatch 0 := by
      rw [← hv, projection_mem_patch_iff]
      exact not_not.mpr hz
    have hP : P.val = O := eq_O_of_not_finite _ _ P.property hfin
    have hzero := Transport.eq_zero_of_val h₁ h₂ e he P hP
    rw [hzero, Transport.neg_zero]
    have hx : v.val 1 = 0 := by
      have hm := (projection_eq_iff_minors v _).mp (hv.trans hP) 1 2
      change v.val 1 * (1 : ℂ) = v.val 2 * (0 : ℂ) at hm
      simpa only [mul_one, mul_zero] using hm
    have href : ProjectivePlaneTopology.projection (reflectedRepresentative v) = O := by
      apply (projection_eq_iff_minors _ _).mpr
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [O, affineParam, ProjectivePlaneTopology.projection, Fin.insertNth, Fin.succAboveCases,
          reflectedRepresentative, hz, hx]
    exact (Transport.zero_val h₁ h₂ e he).trans href.symm
  · have hp : P.val ∈ coordinatePatch 0 := by
      rw [← hv]
      exact (projection_mem_patch_iff _ v).mpr hz
    have hP : P.val = affinePoint (v.val 1 / v.val 0) (v.val 2 / v.val 0) := by
      rw [← hv]
      exact (affinePoint_coordinates ((projection_mem_patch_iff _ v).mpr hz)).symm
    exact (Transport.neg_finite h₁ h₂ e he P _ _ hP).trans
      (reflectedRepresentative_finite hz).symm


lemma finite_secant_transport {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im)
    (e : Torus ω₁ ω₂ ≃ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂))
    (he : ∀ t, (e t).val = phi ω₁ ω₂ t)
    (P Q : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) (x y u v : ℂ)
    (hP : P.val = affinePoint x y) (hQ : Q.val = affinePoint u v)
    (hxu : x ≠ u) :
    let m := (y-v)/(x-u)
    let s := -x-u+m^2/4
    (transportedAdd e P Q).val = affinePoint s (-y+m*(x-s)) := by
  have hPc := P.property
  rw [hP] at hPc
  have hQc := Q.property
  rw [hQ] at hQc
  obtain ⟨z, hz, hzx, hzy⟩ := TorusCubicBiholomorphism.finite_values_surjective
    h₁ h₂ x y ((onCubic_affinePoint_iff _ _ _ _).mp hPc)
  obtain ⟨w, hw, hwx, hwy⟩ := TorusCubicBiholomorphism.finite_values_surjective
    h₁ h₂ u v ((onCubic_affinePoint_iff _ _ _ _).mp hQc)
  have hPz : e (projection ω₁ ω₂ z) = P := by
    apply Subtype.ext
    exact (he _).trans ((TorusCubicLocalMap.phi_finite h₁ h₂ hz).trans
      ((congrArg₂ affinePoint hzx hzy).trans hP.symm))
  have hQw : e (projection ω₁ ω₂ w) = Q := by
    apply Subtype.ext
    exact (he _).trans ((TorusCubicLocalMap.phi_finite h₁ h₂ hw).trans
      ((congrArg₂ affinePoint hwx hwy).trans hQ.symm))
  have hneq : weierstrassP ω₁ ω₂ z ≠ weierstrassP ω₁ ω₂ w := by
    simpa only [hzx, hwx] using hxu
  have hs := SecantAddition.secant_intersections ω₁ ω₂ h₁ h₂ z w hz hw hneq
  have hx := (SecantAddition.addition_formula ω₁ ω₂ h₁ h₂ z w hz hw hneq).2
  have hxsum : weierstrassP ω₁ ω₂ (z+w) = -x-u+((y-v)/(x-u))^2/4 := by
    simpa only [Specs.D12Complex.Ch22.SecantAddition.additionExpression,
      hzx, hzy, hwx, hwy] using hx
  rw [← hPz, ← hQw]
  rw [ExceptionalAddition.addition_agreement ω₁ ω₂ e he]
  simpa only [hzx, hzy, hwx, hwy, hxsum] using hs.2.2.2.2.2


/-- Every geometric rule gives the transported sum. This also proves that
choices of coincident intersections never give different results. -/
lemma geometricSum_eq_transport {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂/ω₁).im) (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂)
    (he : ∀ t, (e t).val = phi ω₁ ω₂ t) (P Q R : E ω₁ ω₂)
    (h : GeometricSum P Q R) : R = transportedAdd e P Q := by
  rcases h with ⟨hP,hR⟩ | ⟨hQ,hR⟩ | ⟨x,y,hP,hQ,hR⟩ |
    ⟨x,y,u,v,hP,hQ,hxu,hR⟩ | ⟨x,y,hP,hQP,hy,hR⟩
  · exact hR.trans (Transport.origin_add h₁ h₂ e he Q P hP).1.symm
  · exact hR.trans (Transport.origin_add h₁ h₂ e he P Q hQ).2.symm
  · exact Subtype.ext (hR.trans (Transport.vertical_add h₁ h₂ e he P Q x y hP hQ).symm)
  · exact Subtype.ext (hR.trans (finite_secant_transport h₁ h₂ e he P Q x y u v hP hQ hxu).symm)
  · rw [hQP]
    exact Subtype.ext (hR.trans (tangent_transport h₁ h₂ e he P x y hP hy).symm)

/-- The five cases exhaust all pairs: each point is finite or O, and two
finite points with equal abscissae have equal or opposite ordinates. -/
lemma geometricSum_transport {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂/ω₁).im) (e : Torus ω₁ ω₂ ≃ E ω₁ ω₂)
    (he : ∀ t, (e t).val = phi ω₁ ω₂ t) (P Q : E ω₁ ω₂) :
    GeometricSum P Q (transportedAdd e P Q) := by
  rcases cubic_point_cases _ _ P with hP | ⟨x,y,hP,hPc⟩
  · exact Or.inl ⟨hP, (Transport.origin_add h₁ h₂ e he Q P hP).1⟩
  rcases cubic_point_cases _ _ Q with hQ | ⟨u,v,hQ,hQc⟩
  · exact Or.inr (Or.inl ⟨hQ, (Transport.origin_add h₁ h₂ e he P Q hQ).2⟩)
  by_cases hxu : x = u
  · subst u
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hQc.trans hPc.symm) with hv | hv
    · subst v
      have hQP : Q = P := Subtype.ext (hQ.trans hP.symm)
      subst Q
      by_cases hy : y = 0
      · apply Or.inr; apply Or.inr; apply Or.inl
        have hPn : P.val = affinePoint x (-y) := by simpa only [hy, neg_zero] using hP
        exact ⟨x,y,hP,hPn,Transport.vertical_add h₁ h₂ e he P P x y hP hPn⟩
      · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact ⟨x,y,hP,rfl,hy,tangent_transport h₁ h₂ e he P x y hP hy⟩
    · apply Or.inr; apply Or.inr; apply Or.inl
      have hQn : Q.val = affinePoint x (-y) := by simpa only [hv] using hQ
      exact ⟨x,y,hP,hQn,Transport.vertical_add h₁ h₂ e he P Q x y hP hQn⟩
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    exact ⟨x,y,u,v,hP,hQ,hxu,finite_secant_transport h₁ h₂ e he P Q x y u v hP hQ hxu⟩

theorem geometric_addition : Specs.D12Complex.Ch22.ChordTangentGroup.geometric_addition_type := by
  intro ω₁ ω₂ h₁ h₂ e he P Q R
  constructor
  · exact geometricSum_eq_transport h₁ h₂ e he P Q R
  · intro hR
    subst R
    exact geometricSum_transport h₁ h₂ e he P Q

theorem geometric_total_unique :
    Specs.D12Complex.Ch22.ChordTangentGroup.geometric_total_unique_type := by
  intro ω₁ ω₂ h₁ h₂ P Q
  obtain ⟨e, he⟩ := ExceptionalAddition.equivalence_exists ω₁ ω₂ h₁ h₂
  refine ⟨transportedAdd e P Q, geometricSum_transport h₁ h₂ e he P Q, ?_⟩
  intro R hR
  exact geometricSum_eq_transport h₁ h₂ e he P Q R hR

theorem exceptional_rules : Specs.D12Complex.Ch22.ChordTangentGroup.exceptional_rules_type :=
  ⟨ExceptionalAddition.identity, ExceptionalAddition.inverse_finite,
    ExceptionalAddition.opposites, ExceptionalAddition.half_period⟩

theorem intersection_geometry : Specs.D12Complex.Ch22.ChordTangentGroup.intersection_geometry_type :=
  ⟨SecantAddition.secant_intersections, TangentAddition.projective_line,
    TangentAddition.tangent_slope, TangentAddition.tangent_intersections,
    TangentAddition.tangent_polynomial, TangentAddition.tangent_doubling,
    TangentAddition.tangent_projective_intersections, ExceptionalAddition.tangent_differential,
    ExceptionalAddition.line_restrictions, ExceptionalAddition.vertical_intersections,
    ExceptionalAddition.vertical_multiplicities, ExceptionalAddition.vertical_tangent,
    ExceptionalAddition.line_through_origin, ExceptionalAddition.infinity_tangent⟩

theorem addition_formula : Specs.D12Complex.Ch22.ChordTangentGroup.addition_formula_type :=
  SecantAddition.addition_formula

theorem meromorphic_identity : Specs.D12Complex.Ch22.ChordTangentGroup.meromorphic_identity_type :=
  SecantAddition.meromorphic_identity

theorem inversion_homogeneous :
    Specs.D12Complex.Ch22.ChordTangentGroup.inversion_homogeneous_type := by
  intro ω₁ ω₂ h₁ h₂ e he P v hv
  exact ⟨(reflectedRepresentative v).property,
    transportedNeg_homogeneous h₁ h₂ e he P v hv⟩

/-- The full group identification, using the actual Φ and the independently
specified geometric operation on the literal projective cubic. -/
theorem chord_tangent_group :
    Specs.D12Complex.Ch22.ChordTangentGroup.chord_tangent_group_type := by
  intro ω₁ ω₂ h₁ h₂
  obtain ⟨e, he⟩ := ExceptionalAddition.equivalence_exists ω₁ ω₂ h₁ h₂
  refine ⟨e, he, ?_⟩
  letI := groupStructure e
  refine ⟨Transport.zero_val h₁ h₂ e he, ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ := group_isomorphism ω₁ ω₂ e
    refine ⟨F,hF,?_⟩
    intro t
    exact (congrArg (fun f : Torus ω₁ ω₂ ≃ E ω₁ ω₂ => (f t).val) hF).trans (he t)
  · intro P Q R
    exact geometric_addition ω₁ ω₂ h₁ h₂ e he P Q R
  · intro P v hv
    exact inversion_homogeneous ω₁ ω₂ h₁ h₂ e he P v hv

end D12Complex.ChordTangentGroup
