import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.AffineDimension
import MathGenome.Internal.AlgebraCore.P103.Ch06.NoetherNormalization
import MathGenome.Internal.AlgebraCore.P103.Ch05.SupportGeometry
import MathGenome.Internal.AlgebraCore.P103.Ch05.NoetherianFiniteness
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Order.ConditionallyCompleteLattice.Finset

namespace P103.Ch06.AffineDimension

open P103.Specs.Ch06.AffineDimension
universe u v

theorem domain_finite_ranks : domain_finite_ranksType.{u,v} := by
  intro k A _ _ _ _ _
  obtain ⟨d, y, hy, hfin, hdim⟩ :=
    P103.Ch06.NoetherNormalization.normalization_elements k A
  let : Module.Finite (Algebra.adjoin k (Set.range y)) A := hfin
  have hb : IsTranscendenceBasis k y :=
    hy.isTranscendenceBasis_iff_isAlgebraic.mpr inferInstance
  let : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  have hbF := hb.algebraMap_comp (A := FractionRing A)
  refine ⟨d, hdim, ?_⟩
  have hc := hbF.lift_cardinalMk_eq_trdeg
  simpa using hc.symm

theorem domain_dimension : domain_dimensionType.{u,v} := by
  intro k A _ _ _ _ _
  obtain ⟨d, hd, ht⟩ := domain_finite_ranks k A
  simpa [ht] using hd

theorem minimalPrimes_finite_nonempty : minimalPrimes_finite_nonemptyType.{u,v} := by
  intro k A _ _ _ _ _
  let : IsNoetherianRing A := P103.Ch05.NoetherianFiniteness.finiteType_noetherian k A
  exact ⟨P103.Ch05.SupportGeometry.minimalPrimes_finite A,
    Set.nonempty_coe_sort.mp (Ideal.nonempty_minimalPrimes (R := A) bot_ne_top)⟩

/-- A bound on the dimensions of minimal-prime quotients bounds every prime
chain: choose a minimal prime below the chain's first prime and descend the
whole chain through the quotient correspondence. -/
theorem dimension_le_of_minimal_components (R : Type*) [CommRing R]
    (b : WithBot ℕ∞)
    (h : ∀ P ∈ minimalPrimes R, ringKrullDim (R ⧸ P) ≤ b) :
    ringKrullDim R ≤ b := by
  change Order.krullDim (PrimeSpectrum R) ≤ b
  apply iSup_le
  intro c
  obtain ⟨P, hP, hPc⟩ :=
    Ideal.exists_minimalPrimes_le (J := c.head.asIdeal) bot_le
  let q : LTSeries (PrimeSpectrum.zeroLocus (R := R) (P : Set R)) :=
    { length := c.length
      toFun := fun i => ⟨c i, hPc.trans (c.head_le i)⟩
      step := fun i => c.step i }
  have hd : ringKrullDim (R ⧸ P) =
      Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (P : Set R)) :=
    Order.krullDim_eq_of_orderIso P.primeSpectrumQuotientOrderIsoZeroLocus
  exact ((Order.LTSeries.length_le_krullDim q).trans_eq hd.symm).trans (h P hP)

theorem dimension_maximal_components : dimension_maximal_componentsType.{u,v} := by
  intro k A _ _ _ _ _
  obtain ⟨hfin, hne⟩ := minimalPrimes_finite_nonempty k A
  let dims := (fun P : Ideal A => ringKrullDim (A ⧸ P)) '' minimalPrimes A
  have hdfin : dims.Finite := hfin.image _
  have hdne : dims.Nonempty := hne.image _
  have hsup : ringKrullDim A = sSup dims := by
    apply le_antisymm
    · exact dimension_le_of_minimal_components A _
        (fun P hP => le_sSup (Set.mem_image_of_mem _ hP))
    · apply sSup_le
      rintro _ ⟨P, _, rfl⟩
      exact ringKrullDim_quotient_le P
  exact ⟨hdfin, hdne, hsup.symm ▸ hdne.isGreatest_csSup hdfin⟩

end P103.Ch06.AffineDimension
