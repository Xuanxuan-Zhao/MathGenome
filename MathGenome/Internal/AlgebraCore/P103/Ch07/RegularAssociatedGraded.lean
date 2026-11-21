import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.RegularAssociatedGraded
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertSerreDimension
import MathGenome.Internal.AlgebraCore.P103.Ch07.HilbertSamuelDimension
import MathGenome.Internal.AlgebraCore.P103.Ch07.EmbeddingDimension
import MathGenome.Internal.AlgebraCore.P103.Ch07.ReesGradedConstruction
import MathGenome.Internal.AlgebraCore.P103.Ch06.PolynomialDimension
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace P103.RegularAssociatedGraded
noncomputable section
open IsLocalRing P103.Rees
open P103.Specs.Ch07.EmbeddingDimension
open P103.Specs.Ch06.DimensionConventions

universe u v
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {ι : Type v} (x : ι → maximalIdeal R)

@[simp] theorem canonicalMap_X (i : ι) :
    canonicalMap x (MvPolynomial.X i) = initialForm (x i) :=
  MvPolynomial.aeval_X _ _

@[simp] theorem canonicalMap_C (a : ResidueField R) :
    canonicalMap x (MvPolynomial.C a) =
      algebraMap (ResidueField R) (AssociatedRing (maximalIdeal R)) a :=
  MvPolynomial.aeval_C _ _

theorem initialForm_mem (a : maximalIdeal R) :
    initialForm a ∈ ringPiece (maximalIdeal R) 1 :=
  ⟨_, rfl⟩

/-- The selected initial forms generate the algebra whenever the original
family generates the maximal ideal. This does not use regularity. -/
theorem adjoin_initialForms (hx : GeneratesMaximalIdeal x) :
    Algebra.adjoin (ResidueField R) (Set.range (initialForm ∘ x)) = ⊤ := by
  let I := maximalIdeal R
  let S := Algebra.adjoin (ResidueField R) (Set.range (initialForm ∘ x))
  let T : Subalgebra R (ReesAlgebra I) :=
    (S.restrictScalars R).comap (Ideal.Quotient.mkₐ R (quotientIdeal I))
  have hs : Ideal.span (Set.range (fun i => (x i : R))) = I :=
    (P103.Ch07.EmbeddingDimension.generators_iff_ideal_span R ι x).mp hx
  have ht : ReesAlgebra I ≤ T.map (ReesAlgebra I).val := by
    change reesAlgebra I ≤ _
    have hg : Algebra.adjoin R (Polynomial.monomial 1 '' Set.range (fun i => (x i : R))) =
        reesAlgebra I := by
      rw [← adjoin_monomial_eq_reesAlgebra, ← hs, Submodule.map_span, Algebra.adjoin_span]
    rw [← hg]
    apply Algebra.adjoin_le
    rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
    refine ⟨ringTerm I 1 ⟨(x i : R), by simpa only [pow_one] using (x i).2⟩, ?_, rfl⟩
    change initialForm (x i) ∈ S
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  apply top_unique
  intro a _
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨f', hf', heq⟩ := ht f.2
  have he : f' = f := Subtype.ext heq
  subst f'
  exact hf'

theorem canonicalMap_surjective (hx : GeneratesMaximalIdeal x) :
    Function.Surjective (canonicalMap x) := by
  rw [← AlgHom.range_eq_top]
  calc
    (canonicalMap x).range = Algebra.adjoin (ResidueField R) (Set.range (initialForm ∘ x)) :=
      MvPolynomial.aeval_range (R := ResidueField R) (f := initialForm ∘ x)
    _ = ⊤ := adjoin_initialForms x hx

/-- Constants belong to the actual degree-zero piece. -/
theorem algebraMap_mem_zero (a : ResidueField R) :
    algebraMap (ResidueField R) (AssociatedRing (maximalIdeal R)) a ∈
      ringPiece (maximalIdeal R) 0 := by
  apply (degree_zero (maximalIdeal R)).2.subset
  exact ⟨a, rfl⟩

/-- Evaluation carries homogeneous polynomials to the corresponding piece. -/
theorem canonicalMap_homogeneous (n : ℕ) (p : MvPolynomial ι (ResidueField R))
    (hp : p.IsHomogeneous n) : canonicalMap x p ∈ ringPiece (maximalIdeal R) n := by
  classical
  rw [p.as_sum, map_sum]
  apply AddSubgroup.sum_mem
  intro d hd
  rw [canonicalMap, MvPolynomial.aeval_monomial]
  have hd' : d.degree = n := by
    simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp hd)
  have hprod : d.prod (fun i k => initialForm (x i) ^ k) ∈
      ringPiece (maximalIdeal R) d.degree := by
    simpa only [Finsupp.prod, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul, mul_one] using
      (SetLike.prod_pow_mem_graded (ringPiece (maximalIdeal R)) (fun _ : ι => 1)
        (fun i => initialForm (x i)) d (F := d.support) (fun i _ => initialForm_mem (x i)))
  rw [hd'] at hprod
  simpa only [zero_add, Function.comp_apply] using
    SetLike.mul_mem_graded (algebraMap_mem_zero (R := R) (p.coeff d)) hprod

/-- The concrete Rees projection acts as the degree selector. -/
theorem ringProjection_homogeneous (n m : ℕ)
    (a : AssociatedRing (maximalIdeal R)) (ha : a ∈ ringPiece (maximalIdeal R) m) :
    ringProjection (maximalIdeal R) n a = if n = m then a else 0 := by
  obtain ⟨b, rfl⟩ := ha
  exact ringProjection_class (maximalIdeal R) n m b

/-- Evaluation commutes with degree projection. -/
theorem canonicalMap_component (n : ℕ) (p : MvPolynomial ι (ResidueField R)) :
    ringProjection (maximalIdeal R) n (canonicalMap x p) =
      canonicalMap x (MvPolynomial.homogeneousComponent n p) := by
  classical
  calc
    ringProjection (maximalIdeal R) n (canonicalMap x p) =
        ∑ j ∈ Finset.range (p.totalDegree + 1),
          ringProjection (maximalIdeal R) n
            (canonicalMap x (MvPolynomial.homogeneousComponent j p)) := by
      rw [← map_sum, ← map_sum, MvPolynomial.sum_homogeneousComponent]
    _ = ∑ j ∈ Finset.range (p.totalDegree + 1),
        if n = j then canonicalMap x (MvPolynomial.homogeneousComponent j p) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact ringProjection_homogeneous n j _
        (canonicalMap_homogeneous x j _ (MvPolynomial.homogeneousComponent_isHomogeneous j p))
    _ = canonicalMap x (MvPolynomial.homogeneousComponent n p) := by
      by_cases hn : n < p.totalDegree + 1
      · simp [hn]
      · have hz : MvPolynomial.homogeneousComponent n p = 0 :=
          MvPolynomial.homogeneousComponent_eq_zero n p (by omega)
        simp [hn, hz]

/-- Surjectivity holds in every degree, not just on the underlying ring. -/
theorem canonicalMap_piece_image (hx : GeneratesMaximalIdeal x) (n : ℕ) :
    canonicalMap x '' (MvPolynomial.homogeneousSubmodule ι (ResidueField R) n :
      Set (MvPolynomial ι (ResidueField R))) =
        (ringPiece (maximalIdeal R) n : Set (AssociatedRing (maximalIdeal R))) := by
  ext a
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact canonicalMap_homogeneous x n p hp
  · intro ha
    obtain ⟨p, hp⟩ := canonicalMap_surjective x hx a
    refine ⟨MvPolynomial.homogeneousComponent n p,
      MvPolynomial.homogeneousComponent_mem n p, ?_⟩
    rw [← canonicalMap_component, hp, ringProjection_homogeneous n n a ha]
    simp

/-- Every minimal family has the expected number of variables. -/
theorem regular_generator_card [IsNoetherianRing R] [Fintype ι]
    (hreg : regularLocalValue R) (hx : MinimalGeneratingFamily x) :
    (Fintype.card ι : WithBot ℕ∞) = ringDimensionValue R := by
  obtain ⟨b, _⟩ := P103.Ch07.EmbeddingDimension.minimal_generators_basis R ι x hx
  have hb : Fintype.card ι = embeddingDimensionValue R := by
    exact (Module.finrank_eq_card_basis b).symm
  rw [hb]
  exact hreg

/-- With zero maximal ideal, the associated graded ring is just its base. -/
theorem residueMap_surjective_of_maximalIdeal_eq_bot
    (hm : maximalIdeal R = ⊥) :
    Function.Surjective (algebraMap (ResidueField R) (AssociatedRing (maximalIdeal R))) := by
  let x : Fin 0 → maximalIdeal R := Fin.elim0
  have hx : GeneratesMaximalIdeal x := by
    have : Subsingleton (maximalIdeal R) := by
      rw [hm]
      infer_instance
    exact Subsingleton.elim _ _
  intro a
  obtain ⟨p, hp⟩ := canonicalMap_surjective x hx a
  rw [p.eq_C_of_isEmpty, canonicalMap_C] at hp
  exact ⟨_, hp⟩

theorem ringPiece_positive_eq_bot_of_maximalIdeal_eq_bot
    (hm : maximalIdeal R = ⊥) (n : ℕ) (hn : 0 < n) :
    ringPiece (maximalIdeal R) n = ⊥ := by
  apply le_antisymm _ bot_le
  rintro a ⟨b, rfl⟩
  have hb : b = 0 := by
    apply Subtype.ext
    change (b : R) = 0
    simpa only [hm, Ideal.bot_pow (Nat.ne_of_gt hn), Ideal.mem_bot] using b.2
  simp [hb]

/-- A nonzero relation in a polynomial domain forces a strict dimension drop,
so a matching lower dimension bound proves injectivity. -/
theorem canonicalMap_injective_of_dimension [Fintype ι]
    (hx : GeneratesMaximalIdeal x)
    (hdim : (Fintype.card ι : WithBot ℕ∞) ≤
      ringKrullDim (AssociatedRing (maximalIdeal R))) :
    Function.Injective (canonicalMap x) := by
  classical
  intro p q hpq
  by_contra hpq'
  have hp' : p - q ≠ 0 := sub_ne_zero.mpr hpq'
  have hp0 : canonicalMap x (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  have hdimP : ringKrullDim (MvPolynomial ι (ResidueField R)) =
      (Fintype.card ι : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
    simp
  have hn : p - q ∈ nonZeroDivisors (MvPolynomial ι (ResidueField R)) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hp'
  have hs : Function.Surjective (canonicalMap x).toRingHom := canonicalMap_surjective x hx
  have hz : (canonicalMap x).toRingHom (p - q) = 0 := hp0
  have hsucc : ringKrullDim (AssociatedRing (maximalIdeal R)) + 1 ≤
      ringKrullDim (MvPolynomial ι (ResidueField R)) :=
    @ringKrullDim_succ_le_of_surjective
      (MvPolynomial ι (ResidueField R)) (AssociatedRing (maximalIdeal R))
      inferInstance inferInstance (canonicalMap x).toRingHom hs (p - q) hn hz
  rw [hdimP] at hsucc
  have hstep : (Fintype.card ι : WithBot ℕ∞) + 1 ≤
      ringKrullDim (AssociatedRing (maximalIdeal R)) + 1 := by gcongr
  have hbad := hstep.trans hsucc
  have hbad' : Fintype.card ι + 1 ≤ Fintype.card ι := by exact_mod_cast hbad
  omega

/-- Hilbert--Samuel layer growth gives the lower dimension bound for the
actual associated ring. We use its finite associated module to reuse the
established linear comparison of the successive quotients. -/
theorem dimension_le_associatedRing [IsNoetherianRing R]
    (d : ℕ) (hd : ringDimensionValue R = (d : WithBot ℕ∞)) (hpos : 0 < d) :
    (d : WithBot ℕ∞) ≤ ringKrullDim (AssociatedRing (maximalIdeal R)) := by
  let I := maximalIdeal R
  let A := AssociatedRing I
  let N := AssociatedModule I R
  have hIR : I • (⊤ : Submodule R R) = I := by
    change I * ⊤ = I
    exact Ideal.mul_top (I := I)
  let : Nontrivial A := Function.Injective.nontrivial (degree_zero I).1
  let : Nontrivial N := by
    apply nontrivial_of_ne (moduleClass I R 0 ⟨1, by simp⟩) 0
    intro hz
    have hz' := (moduleClass_eq_zero_iff I R 0 _).mp hz
    have : (1 : R) ∈ I := by simpa only [zero_add, pow_one, hIR] using hz'
    exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem (maximalIdeal R) this isUnit_one)
  let : Module.Finite A N := quotient_finite I R inferInstance
  letI : Module (ResidueField R) N :=
    Module.compHom N (algebraMap (ResidueField R) A)
  let : IsScalarTower (ResidueField R) A N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨G, hG, ⟨U, hU⟩, hstd⟩ := integer_grading I R
  have hzero : P103.Specs.Ch06.LinearGradedNormalization.Connected (ResidueField R) G := by
    intro a
    rw [show G.piece 0 = ringPiece I 0 by simpa using hG 0]
    exact (Set.ext_iff.mp (degree_zero I).2 a).symm
  obtain ⟨hfin, e, b, p, q, he, _, _, hq, hezero, hepos⟩ :=
    P103.HilbertSerreDimension.hilbert_serre (ResidueField R) G U hzero (hstd inferInstance)
  have hcoeff := (P103.HilbertSerreDimension.finite_components
    (ResidueField R) G U hzero (hstd inferInstance)).2
  have hq' : P103.HilbertSamuelPolynomial.EventuallyPolynomial
      (P103.HilbertSamuelPolynomial.layerLength I R) q := by
    obtain ⟨J, hJ⟩ := hq
    refine ⟨J.toNat, fun n hn => ?_⟩
    have hj : J ≤ (n : ℤ) := by omega
    have hh := hJ n hj
    rw [hcoeff] at hh
    simp only [P103.HilbertSerreLength.hilbertFunction, Int.cast_natCast] at hh
    rw [← P103.HilbertSamuelPolynomial.component_length_eq I G hG U hU n] at hh
    exact hh
  have hlen : IsFiniteLength R (R ⧸ (I • (⊤ : Submodule R R))) := by
    rw [hIR]
    change IsFiniteLength R (ResidueField R)
    apply Module.length_ne_top_iff.mp
    rw [Module.length_eq_of_surjective (S := R) (R := ResidueField R)
      (M := ResidueField R) Ideal.Quotient.mk_surjective,
      Module.length_eq_finrank (ResidueField R) (ResidueField R)]
    simp
  have hdim : moduleDimensionValue R R = (d : WithBot ℕ∞) := by
    change ringKrullDim (R ⧸ Module.annihilator R R) = _
    have hann : Module.annihilator R R = ⊥ := (Module.annihilator_eq_bot (R := R) (M := R)).mpr inferInstance
    rw [hann, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)]
    exact hd
  obtain ⟨r, hr, hrne, hrdeg⟩ := P103.HilbertSamuelDimension.positive_layers
    R R I le_rfl hlen d hdim hpos
  have hqr : q = r := P103.HilbertSamuelDimension.eventuallyPolynomial_unique _ _ _ hq' hr
  have hep : 0 < e := by
    by_contra hn
    have hz := (hezero (by omega)).1
    exact hrne (hqr.symm.trans hz)
  have hed : e = d := by
    have := (hepos hep).2
    rw [hqr, hrdeg] at this
    omega
  have hle : moduleDimensionValue A N ≤ ringKrullDim A :=
    @ringKrullDim_quotient_le A inferInstance (Module.annihilator A N)
  calc
    (d : WithBot ℕ∞) = (e : WithBot ℕ∞) := congrArg (fun n : ℕ => (n : WithBot ℕ∞)) hed.symm
    _ = moduleDimensionValue A N := he.symm
    _ ≤ ringKrullDim A := hle

/-- Once injectivity is known, the already established degreewise surjection
supplies the canonical isomorphism, including its inverse grading property. -/
theorem gradedIsomorphism_of_injective [IsNoetherianRing R] [Fintype ι]
    (hreg : regularLocalValue R) (hx : MinimalGeneratingFamily x)
    (hinj : Function.Injective (canonicalMap x)) :
    (Fintype.card ι : WithBot ℕ∞) = ringDimensionValue R ∧
      ∃ e : MvPolynomial ι (ResidueField R) ≃ₐ[ResidueField R]
          AssociatedRing (maximalIdeal R),
        (e : MvPolynomial ι (ResidueField R) → AssociatedRing (maximalIdeal R)) =
          canonicalMap x ∧
        (∀ i, e (MvPolynomial.X i) = initialForm (x i)) ∧
        ∀ n : ℕ,
          e '' (MvPolynomial.homogeneousSubmodule ι (ResidueField R) n :
            Set (MvPolynomial ι (ResidueField R))) =
              (ringPiece (maximalIdeal R) n : Set (AssociatedRing (maximalIdeal R))) := by
  let e := AlgEquiv.ofBijective (canonicalMap x) ⟨hinj, canonicalMap_surjective x hx.1⟩
  exact ⟨regular_generator_card x hreg hx,
    e, rfl, canonicalMap_X x, canonicalMap_piece_image x hx.1⟩

theorem graded_surjection :
    Specs.P103.RegularAssociatedGraded.gradedSurjectionType.{u,v} := by
  intro R _ _ _ ι _ x hx
  exact ⟨canonicalMap_surjective x hx, canonicalMap_piece_image x hx⟩

/-- For every minimal family, regularity and Hilbert growth rule out all
relations in the canonical graded polynomial presentation. -/
theorem graded_isomorphism :
    Specs.P103.RegularAssociatedGraded.gradedIsomorphismType.{u,v} := by
  intro R _ _ _ ι _ x hreg hx
  apply gradedIsomorphism_of_injective x hreg hx
  apply canonicalMap_injective_of_dimension x hx.1
  have hc := regular_generator_card x hreg hx
  by_cases hz : Fintype.card ι = 0
  · rw [hz]
    let : Nontrivial (AssociatedRing (maximalIdeal R)) :=
      Function.Injective.nontrivial (degree_zero (maximalIdeal R)).1
    exact ringKrullDim_nonneg_of_nontrivial
  · exact dimension_le_associatedRing (Fintype.card ι) hc.symm (Nat.pos_of_ne_zero hz)

/-- The complete zero-dimensional boundary, with the canonical base map. -/
theorem dimension_zero :
    Specs.P103.RegularAssociatedGraded.dimensionZeroType.{u} := by
  intro R _ _ _ hreg hd
  have hm : maximalIdeal R = ⊥ :=
    (P103.Ch07.EmbeddingDimension.regular_dimension_zero R hreg hd).1
  have hsurj := residueMap_surjective_of_maximalIdeal_eq_bot hm
  have hinj : Function.Injective
      (algebraMap (ResidueField R) (AssociatedRing (maximalIdeal R))) :=
    (degree_zero (maximalIdeal R)).1
  let e := AlgEquiv.ofBijective
    (Algebra.ofId (ResidueField R) (AssociatedRing (maximalIdeal R))) ⟨hinj, hsurj⟩
  refine ⟨e, rfl, ?_, ringPiece_positive_eq_bot_of_maximalIdeal_eq_bot hm⟩
  apply top_unique
  intro a _
  obtain ⟨r, rfl⟩ := hsurj a
  exact algebraMap_mem_zero r

end
end P103.RegularAssociatedGraded
