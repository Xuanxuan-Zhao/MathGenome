import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.CyclicHilbert90
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.CyclicDegreeOne
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Hilbert90
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.TraceContraction

noncomputable section

namespace GaloisFormalization.GH.CyclicHilbert90

open CyclicDegreeOne
open scoped BigOperators

universe u v

private def powersEquiv {C : Type v} [Group C] [Finite C] (s : C)
    (hs : Subgroup.zpowers s = ⊤) : Fin (orderOf s) ≃ C :=
  (finEquivZPowers (isOfFinOrder_of_finite s)).trans
    { toFun := Subtype.val
      invFun := fun g => ⟨g, by rw [hs]; exact Subgroup.mem_top g⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem trace_formula : Specs.GaloisFormalization.GH.CyclicHilbert90.TraceFormula.{u,v} := by
  intro k E _ _ _ _ _ s hs x
  change (∑ i ∈ Finset.range (orderOf s), (s ^ i) x) = _
  rw [trace_eq_sum_automorphisms, ← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (powersEquiv s hs) _ _ (fun _ => rfl)

theorem norm_formula : Specs.GaloisFormalization.GH.CyclicHilbert90.NormFormula.{u,v} := by
  intro k E _ _ _ _ _ s hs x
  change ((∑ i ∈ Finset.range (orderOf s), s ^ i • Additive.ofMul x).toMul : E) = _
  rw [toMul_sum, Units.coe_prod, Algebra.norm_eq_prod_automorphisms,
    ← Fin.prod_univ_eq_prod_range]
  exact Fintype.prod_equiv (powersEquiv s hs) _ _ (fun _ => rfl)

theorem additive_quotient_vanishing :
    Specs.GaloisFormalization.GH.CyclicHilbert90.AdditiveQuotientVanishing.{u,v} := by
  intro k E _ _ _ _ _ s hs
  obtain ⟨e, _⟩ := evaluation_at_generator Gal(E/k) E s hs
  have h := semilinear_cohomology_subsingleton k E E
    (fun g a b => show g (a * b) = g a * g b from map_mul g a b) 1 Nat.zero_lt_one
  exact ⟨fun x y => e.symm.injective (h.elim _ _)⟩

theorem multiplicative_quotient_vanishing :
    Specs.GaloisFormalization.GH.CyclicHilbert90.MultiplicativeQuotientVanishing.{u,v} := by
  intro k E _ _ _ _ _ s hs
  let : TopologicalSpace Eˣ := ⊥
  let : DiscreteTopology Eˣ := discreteTopology_bot _
  let : ContinuousSMul Gal(E/k) Eˣ := ⟨continuous_of_discreteTopology⟩
  have h : Subsingleton (ContinuousH Gal(E/k) (Additive Eˣ) 1) := Hilbert90.unitsVanishing
  let comparison := ordinaryCohomologyEquiv.{v,v,0} Gal(E/k) (Additive Eˣ) 1
  obtain ⟨e, _⟩ := evaluation_at_generator Gal(E/k) (Additive Eˣ) s hs
  let fromQuotient := e.symm.trans comparison.symm
  exact ⟨fun x y => fromQuotient.injective (h.elim _ _)⟩

private theorem norm_eq_zero_iff {C : Type v} {A : Type v} [Group C] [Finite C]
    [AddCommGroup A] [DistribMulAction C A] (s : C)
    (h : Subsingleton (NormQuotient (A := A) s)) (a : A) :
    norm s a = 0 ↔ ∃ b : A, a = s • b - b := by
  constructor
  · intro ha
    let x : LinearMap.ker (norm s) := ⟨a, LinearMap.mem_ker.mpr ha⟩
    have hx : (Submodule.Quotient.mk x : NormQuotient (A := A) s) = 0 := h.elim _ _
    have hr : a ∈ LinearMap.range (generatorDifference s) :=
      (Submodule.Quotient.mk_eq_zero (generatorDifferences s)).mp hx
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hr
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, hb⟩
    apply LinearMap.mem_ker.mp (norm_kills_differences C A s ?_)
    exact LinearMap.mem_range.mpr ⟨b, hb.symm⟩

theorem additive_hilbert90 :
    Specs.GaloisFormalization.GH.CyclicHilbert90.AdditiveHilbert90.{u,v} := by
  intro k E _ _ _ _ _ s hs x
  have htrace : norm s x = 0 ↔ Algebra.trace k E x = 0 := by
    rw [trace_formula k E s hs, ← (algebraMap k E).map_zero, (algebraMap k E).injective.eq_iff]
  exact htrace.symm.trans (norm_eq_zero_iff s (additive_quotient_vanishing k E s hs) x)

theorem multiplicative_hilbert90 :
    Specs.GaloisFormalization.GH.CyclicHilbert90.MultiplicativeHilbert90.{u,v} := by
  intro k E _ _ _ _ _ s hs x
  have hnorm : norm s (Additive.ofMul x) = 0 ↔ Algebra.norm k (x : E) = 1 := by
    constructor
    · intro h
      apply (algebraMap k E).injective
      rw [← norm_formula k E s hs, h, map_one]
      rfl
    · intro h
      apply Units.ext
      change ((norm s (Additive.ofMul x)).toMul : E) = 1
      rw [norm_formula k E s hs, h, map_one]
  rw [← hnorm, norm_eq_zero_iff s (multiplicative_quotient_vanishing k E s hs)]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toMul, congrArg Additive.toMul hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩

end GaloisFormalization.GH.CyclicHilbert90
