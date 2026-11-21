import MathGenome.Internal.Specs.D05.M10.CyclicTest.Commutant
import MathGenome.Internal.D05.M10.CyclicTest
import MathGenome.Internal.D05.M10.Rational
import MathGenome.Internal.D05.M09.CommutantInvariance

noncomputable section
open Polynomial
namespace D05.M10.CyclicTest.Commutant

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem polynomial_of_commutes_of_cyclic :
    Specs.D05.M10.CyclicTest.Commutant.polynomial_of_commutes_of_cyclic := by
  intro K V _ _ _ T v hv S hS
  obtain ⟨p, hp⟩ := (Cyclic.module_bridge T v (S v)).mpr (hv ▸ Submodule.mem_top)
  have hp' : Polynomial.aeval T p v = S v := congrArg (Module.AEval'.of T).symm hp
  refine ⟨p, ?_⟩
  ext w
  obtain ⟨q, hq⟩ := (Cyclic.module_bridge T v w).mpr (hv ▸ Submodule.mem_top)
  have hq' : Polynomial.aeval T q v = w := congrArg (Module.AEval'.of T).symm hq
  rw [← hq']
  calc
    S (Polynomial.aeval T q v) = Polynomial.aeval T q (S v) :=
      congrArg (fun f : Module.End K V => f v)
        (M09.CommutantInvariance.commutes_polynomial S T hS q)
    _ = Polynomial.aeval T q (Polynomial.aeval T p v) := by rw [hp']
    _ = Polynomial.aeval T p (Polynomial.aeval T q v) := by
      change (Polynomial.aeval T q * Polynomial.aeval T p) v =
        (Polynomial.aeval T p * Polynomial.aeval T q) v
      rw [← map_mul, ← map_mul, mul_comm q p]



open Specs.D05.M10.Rational (Residue)

/-- Divisibility induces the actual reduction map between principal quotients. -/
def residueReduction (a b : K[X]) (hab : a ∣ b) : Residue b →ₗ[K[X]] Residue a :=
  Submodule.mapQ (Ideal.span {b}) (Ideal.span {a}) LinearMap.id (by
    intro q hq
    change q ∈ Ideal.span {a}
    exact Ideal.mem_span_singleton.mpr (hab.trans (Ideal.mem_span_singleton.mp hq)))

@[simp] lemma residueReduction_mk (a b : K[X]) (hab : a ∣ b) (q : K[X]) :
    residueReduction a b hab (Submodule.Quotient.mk q) = Submodule.Quotient.mk q := rfl

lemma residue_one_ne_zero (a : K[X]) (ha : 0 < a.natDegree) :
    (Submodule.Quotient.mk (1 : K[X]) : Residue a) ≠ 0 := by
  intro h
  have hd : a ∣ 1 := Ideal.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero _).mp h)
  have hdeg := Polynomial.natDegree_le_of_dvd hd (one_ne_zero : (1 : K[X]) ≠ 0)
  rw [Polynomial.natDegree_one] at hdeg
  exact (Nat.not_lt_of_ge hdeg) ha

/-- An off-diagonal quotient map commutes with X but cannot act as a polynomial
scalar. Transport it across the actual rational-decomposition isomorphism. -/
lemma counterexample_of_two_quotients (T : Module.End K V) {r : ℕ}
    (d : Fin r → K[X])
    (e : Module.AEval' T ≃ₗ[K[X]] (∀ i, Residue (d i)))
    (i j : Fin r) (hij : i ≠ j) (hi : 0 < (d i).natDegree) (hd : d i ∣ d j) :
    ∃ S : Module.End K V, S * T = T * S ∧
      ∀ p : K[X], S ≠ Polynomial.aeval T p := by
  classical
  let P := ∀ k, Residue (d k)
  let F : P →ₗ[K[X]] P :=
    (LinearMap.single K[X] (fun k => Residue (d k)) i).comp
      ((residueReduction (d i) (d j) hd).comp (LinearMap.proj j))
  let E : V ≃ₗ[K] P := (Module.AEval'.of T).trans (e.restrictScalars K)
  have hEp (p : K[X]) (v : V) : E (Polynomial.aeval T p v) = p • E v := by
    change e ((Module.AEval'.of T) ((Polynomial.aeval T p) v)) = _
    change e (p • (Module.AEval'.of T v)) = _
    exact e.map_smul p _
  have hET (v : V) : E (T v) = (X : K[X]) • E v := by
    simpa only [Polynomial.aeval_X] using hEp X v
  let S : Module.End K V :=
    E.symm.toLinearMap.comp ((F.restrictScalars K).comp E.toLinearMap)
  have hES (v : V) : E (S v) = F (E v) := by simp [S]
  refine ⟨S, ?_, ?_⟩
  · ext v
    apply E.injective
    change E (S (T v)) = E (T (S v))
    rw [hES, hET, F.map_smul, hET, hES]
  · intro p hS
    let z : P := Pi.single j (Submodule.Quotient.mk (1 : K[X]))
    have hpoly : F z = p • z := by
      calc
        F z = E (S (E.symm z)) := by rw [hES, E.apply_symm_apply]
        _ = E (Polynomial.aeval T p (E.symm z)) := by rw [hS]
        _ = p • z := by rw [hEp, E.apply_symm_apply]
    have hcoord := congrFun hpoly i
    have hleft : F z i = (Submodule.Quotient.mk (1 : K[X]) : Residue (d i)) := by
      change (Pi.single i (residueReduction (d i) (d j) hd (z j)) : P) i = _
      rw [Pi.single_eq_same]
      change residueReduction (d i) (d j) hd
        ((Pi.single j (Submodule.Quotient.mk (1 : K[X])) : P) j) = _
      rw [Pi.single_eq_same, residueReduction_mk]
    have hright : (p • z) i = 0 := by
      change p • (z i) = 0
      rw [show z i = 0 from Pi.single_eq_of_ne hij _, smul_zero]
    rw [hleft, hright] at hcoord
    exact residue_one_ne_zero (d i) hi hcoord

theorem cyclic_iff_commutant_polynomial :
    Specs.D05.M10.CyclicTest.Commutant.cyclic_iff_commutant_polynomial := by
  intro K V _ _ _ _ T
  constructor
  · rintro ⟨v, hv⟩
    exact polynomial_of_commutes_of_cyclic T v hv
  · intro h
    obtain ⟨r, d, hm, hp, hdiv, ⟨e⟩, b, hb, hdim⟩ := Rational.rational_form T
    cases r with
    | zero =>
      have hV : Module.finrank K V = 0 := by simpa using hdim.symm
      exact ⟨0, (CyclicTest.zero_case T hV).1⟩
    | succ r =>
      cases r with
      | zero => exact CyclicTest.cyclic_of_single_quotient T d e
      | succ r =>
        obtain ⟨S, hS, hnp⟩ := counterexample_of_two_quotients T d e
          0 (Fin.last (r+1)) (by
            intro heq
            have hh := congrArg Fin.val heq
            simp only [Fin.val_zero, Fin.val_last] at hh
            omega) (hp 0)
          (hdiv 0 (Fin.last (r+1)) (Fin.zero_le _))
        obtain ⟨p, hpol⟩ := h S hS
        exact False.elim (hnp p hpol)

theorem noncyclic_counterexample :
    Specs.D05.M10.CyclicTest.Commutant.noncyclic_counterexample := by
  intro K V _ _ _ _ T h
  have hn := mt (cyclic_iff_commutant_polynomial T).mpr h
  push Not at hn
  obtain ⟨S, hS, hp⟩ := hn
  exact ⟨S, hS, hp⟩

end D05.M10.CyclicTest.Commutant
