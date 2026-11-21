import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.IntegralDimension
import MathGenome.Internal.AlgebraCore.P103.Ch04.IntegralPrimeProperties
import MathGenome.Internal.AlgebraCore.P103.Ch04.GoingUp
import MathGenome.Internal.AlgebraCore.P103.Ch04.LyingOver
import MathGenome.Internal.AlgebraCore.P103.Ch04.SpectrumFunctorQuotient

namespace P103.Ch04.IntegralDimension

/-- Incomparability makes contraction strictly monotone, even when the
integral ring map has a kernel. -/
theorem strict_contraction : Specs.strict_contraction := by
  intro R A _ _ g hg q q' hlt
  refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) ?_
  intro heq
  have h := IntegralPrimeProperties.incomparability R A g hg q.asIdeal q'.asIdeal
    q.isPrime q'.isPrime hlt.le (congrArg PrimeSpectrum.asIdeal heq)
  exact hlt.ne (PrimeSpectrum.ext h)

/-- Lying over supplies the initial prime, and going up lifts the chain.
Strictness follows from the specified contractions. -/
theorem finite_strict_chain_lift : Specs.finite_strict_chain_lift := by
  intro R A _ _ g hg n p hp hker
  obtain ⟨q₀, hq₀, hcon₀⟩ :=
    LyingOver.exists_prime_over R A g hg (p 0).asIdeal (p 0).isPrime hker
  obtain ⟨q, _, hprime, hmono, hcon⟩ :=
    GoingUp.finite_chain_lift R A g hg n (fun i => (p i).asIdeal)
      (fun i => (p i).isPrime) hp.monotone q₀ hq₀ hcon₀
  refine ⟨fun i => ⟨q i, hprime i⟩, ?_, fun i => PrimeSpectrum.ext (hcon i)⟩
  intro i j hij
  refine lt_of_le_of_ne (hmono hij.le) ?_
  intro heq
  have hq : q i = q j := congrArg PrimeSpectrum.asIdeal heq
  have hpi : (p i).asIdeal = (p j).asIdeal := (hcon i).symm.trans ((congrArg
    (Ideal.comap g) hq).trans (hcon j))
  exact (hp hij).ne (PrimeSpectrum.ext hpi)

/-- Compare the suprema using contraction in one direction and finite-chain
lifting in the other, then use the quotient prime-ideal correspondence. -/
theorem dimension_eq : Specs.dimension_eq := by
  intro R A _ _ g hg
  let Z := PrimeSpectrum.zeroLocus (RingHom.ker g : Set R)
  let f : PrimeSpectrum A → Z := fun q =>
    ⟨PrimeSpectrum.comap g q, LyingOver.contraction_contains_kernel R A g q⟩
  have hf : StrictMono f := fun _ _ h => strict_contraction R A g hg h
  have hdim : Order.krullDim (PrimeSpectrum A) = Order.krullDim Z := by
    apply le_antisymm (Order.krullDim_le_of_strictMono f hf)
    apply iSup_le
    intro p
    obtain ⟨q, hq, _⟩ := finite_strict_chain_lift R A g hg p.length
      (fun i => (p i).val) (fun _ _ h => p.strictMono h) (p 0).property
    exact le_iSup_of_le (LTSeries.mk p.length q hq) le_rfl
  exact hdim.trans (Order.krullDim_eq_of_orderIso
    (RingHom.ker g).primeSpectrumQuotientOrderIsoZeroLocus).symm

/-- The bottom value of the chain supremum detects an empty spectrum. -/
theorem empty_spectrum_iff : Specs.empty_spectrum_iff := by
  intro R A _ _ g hg
  rw [← Order.krullDim_eq_bot_iff, ← Order.krullDim_eq_bot_iff]
  change ringKrullDim A = ⊥ ↔ ringKrullDim (R ⧸ RingHom.ker g) = ⊥
  rw [dimension_eq R A g hg]

end P103.Ch04.IntegralDimension
