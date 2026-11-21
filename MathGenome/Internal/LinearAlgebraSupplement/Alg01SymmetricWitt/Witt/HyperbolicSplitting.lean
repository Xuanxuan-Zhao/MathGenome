import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.Coordinates
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Witt.OrthogonalSplitting

namespace Alg01SymmetricWitt.Witt.HyperbolicSplitting

open Coordinates (hyperbolicPlane hyperbolicNondegenerate)
open OrthogonalSplitting (orthogonalComplement orthogonalSplitting)

universe u v

variable {k : Type u} {V : Type v} [Field k] [Invertible (2 : k)]
  [AddCommGroup V] [Module k V]

/-- Split off a hyperbolic plane with the prescribed first isotropic coordinate vector. -/
theorem hyperbolicSplitting [FiniteDimensional k V]
    (q : QuadraticForm k V) (hq : q.Nondegenerate) (e : V) (he : e ≠ 0) (heq : q e = 0) :
    ∃ f : V, f ≠ 0 ∧ q f = 0 ∧ 2 * q.associated e f = 1 ∧
      let P := Submodule.span k ({e, f} : Set V)
      let W := orthogonalComplement q P
      (∃ i : (hyperbolicPlane k).IsometryEquiv (q.comp P.subtype),
        ∀ z : k × k, (i z : V) = z.1 • e + z.2 • f) ∧
      IsCompl P W ∧
      (∃ a : ((q.comp P.subtype).prod (q.comp W.subtype)).IsometryEquiv q,
        ∀ z : P × W, a z = (z.1 : V) + (z.2 : V)) ∧
      (q.comp W.subtype).Nondegenerate := by
  obtain ⟨g, hg⟩ : ∃ g, QuadraticMap.polar q e g ≠ 0 := by
    by_contra! h
    exact he ((QuadraticMap.nondegenerate_polar_iff.mpr hq).1 e h)
  have hee : QuadraticMap.polar q e e = 0 := by simp [heq]
  let f₀ := (QuadraticMap.polar q e g)⁻¹ • g
  have hef₀ : QuadraticMap.polar q e f₀ = 1 := by
    simp [f₀, inv_mul_cancel₀ hg]
  let f := f₀ + (-q f₀) • e
  have hef : QuadraticMap.polar q e f = 1 := by
    simp [f, hef₀, hee]
  have hfe₀ : QuadraticMap.polar q f₀ e = 1 := (QuadraticMap.polar_comm q f₀ e).trans hef₀
  have hfq : q f = 0 := by
    change q (f₀ + (-q f₀) • e) = 0
    rw [QuadraticMap.map_add q]
    simp [q.map_smul, heq, hfe₀]
  have hf : f ≠ 0 := by
    intro h
    simp [h] at hef
  have hassoc : 2 * q.associated e f = 1 := by
    have h := congrArg (fun B : LinearMap.BilinForm k V => B e f)
      (QuadraticMap.two_nsmul_associated k q)
    change (2 : ℕ) • q.associated e f = QuadraticMap.polar q e f at h
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, hef] using h
  have hfe : QuadraticMap.polar q f e = 1 := (QuadraticMap.polar_comm q f e).trans hef
  have hff : QuadraticMap.polar q f f = 0 := by simp [hfq]
  let P := Submodule.span k ({e, f} : Set V)
  let L := (LinearMap.toSpanSingleton k V e).coprod (LinearMap.toSpanSingleton k V f)
  let coord : k × k →ₗ[k] P :=
    L.codRestrict P (fun z => Submodule.mem_span_pair.mpr ⟨z.1, z.2, rfl⟩)
  have coord_apply (z : k × k) : (coord z : V) = z.1 • e + z.2 • f := rfl
  have hcoord : Function.Bijective coord := by
    constructor
    · intro z z' h
      have hV := congrArg Subtype.val h
      rw [coord_apply, coord_apply] at hV
      apply Prod.ext
      · simpa [hef, hff] using congrArg (fun x => QuadraticMap.polar q x f) hV
      · simpa [hee, hfe] using congrArg (fun x => QuadraticMap.polar q x e) hV
    · intro p
      obtain ⟨s, t, h⟩ := Submodule.mem_span_pair.mp p.property
      exact ⟨(s, t), Subtype.ext h⟩
  let i : (hyperbolicPlane k).IsometryEquiv (q.comp P.subtype) :=
    { LinearEquiv.ofBijective coord hcoord with
      map_app' := by
        intro z
        change q (z.1 • e + z.2 • f) = hyperbolicPlane k z
        rw [QuadraticMap.map_add q]
        simp [q.map_smul, heq, hfq, hef, mul_comm] }
  have hP : (q.comp P.subtype).Nondegenerate := by
    apply QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr
    rw [← i.map_radical, (hyperbolicNondegenerate k).1.radical_eq_bot, Submodule.map_bot]
  exact ⟨f, hf, hfq, hassoc, ⟨i, coord_apply⟩, orthogonalSplitting q P hq hP⟩

end Alg01SymmetricWitt.Witt.HyperbolicSplitting
