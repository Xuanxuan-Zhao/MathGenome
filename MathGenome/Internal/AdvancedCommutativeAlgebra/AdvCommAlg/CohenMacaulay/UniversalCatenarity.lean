import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.PrimeChains
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.PolynomialExtension
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.UniversalCatenarity

/-! Universal catenarity of Noetherian Cohen–Macaulay rings, CM-15. -/
universe u v
open scoped TensorProduct
noncomputable section
namespace AdvCommAlg.CohenMacaulay

/-- The ring and self-module formulations agree, including the zero ring. -/
lemma cohenMacaulayRing_iff_self (R : Type u) [CommRing R] [IsNoetherianRing R] :
    CohenMacaulayRing R ↔ IsCohenMacaulay R R := by
  constructor
  · intro h p _
    exact (localCohenMacaulay_iff_of_linearEquiv (localizedSelfEquiv p)).mpr (h p)
  · intro h p
    exact (localCohenMacaulay_iff_of_linearEquiv (localizedSelfEquiv p)).mp
      (h p (self_mem_support p))

/-- The polynomial module theorem applied to the self-module gives the
ring assertion using the action on the right tensor factor. -/
lemma mvPolynomial_cohenMacaulayRing (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hCM : CohenMacaulayRing R) (n : ℕ) :
    CohenMacaulayRing (MvPolynomial (Fin n) R) := by
  let P := MvPolynomial (Fin n) R
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := P) R P
  letI := Specs.rightTensorFinite R P R P
  have h := (mvPolynomial_cohenMacaulay_iff R R n).mpr
    ((cohenMacaulayRing_iff_self R).mp hCM)
  let e := RegularSequence.rightTensorComm (S := P) R P ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid R P P
  exact (cohenMacaulayRing_iff_self P).mpr
    ((isCohenMacaulay_iff_of_linearEquiv e).mp h)

/-- Finite polynomial extensions are catenary by their Cohen–Macaulayness. -/
theorem mvPolynomial_catenary : Specs.mvPolynomial_catenaryType.{u} := by
  intro R _ _ hCM n
  exact catenary (mvPolynomial_cohenMacaulayRing R hCM n)

/-- An order embedding with order-connected image identifies every interval
between its points, including saturated chains and their lengths. -/
private lemma catenary_of_orderEmbedding {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : PrimeSpectrum S ↪o PrimeSpectrum R)
    (he : (Set.range e).OrdConnected) (hR : Catenary R) : Catenary S := by
  constructor
  · intro p q hpq T hT
    let f : Set.Icc p q → Set.Icc (e p) (e q) :=
      fun x => ⟨e x.1, e.monotone x.2.1, e.monotone x.2.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (e.injective (congrArg Subtype.val hab))
    have hchain : IsChain (· ≤ ·) (f '' T) :=
      IsChain.image_of_map_rel _ _ f (fun _ _ hab => e.monotone hab) hT
    exact (hR.1 (e p) (e q) (e.monotone hpq) (f '' T) hchain).of_finite_image
      hf.injOn
  · intro p q hpq
    obtain ⟨c, hcp, hcq, hlen⟩ := hR.2 (e p) (e q) (e.monotone hpq)
    have hmono : Monotone c :=
      LTSeries.monotone (c.ofLE (fun _ h => h.lt))
    have hmem (i : Fin (c.length + 1)) : c i ∈ Set.range e := by
      apply he.out ⟨p, hcp.symm⟩ ⟨q, hcq.symm⟩
      exact ⟨hmono (Fin.zero_le i), hmono (Fin.le_last i)⟩
    choose g hg using hmem
    let d : Specs.PrimeChain S :=
      ⟨c.length, g, fun i => CovBy.of_image e (by
        rw [hg, hg]
        exact c.step i)⟩
    have hdp : d.head = p := e.injective ((hg 0).trans hcp)
    have hdq : d.last = q := e.injective ((hg (Fin.last c.length)).trans hcq)
    refine ⟨d, hdp, hdq, ?_⟩
    intro d' hd'p hd'q
    let φ : SetRel.Hom {(a, b) : PrimeSpectrum S × PrimeSpectrum S | a ⋖ b}
        {(a, b) : PrimeSpectrum R × PrimeSpectrum R | a ⋖ b} :=
      ⟨e, fun {a b} h => h.image e he⟩
    exact hlen (d'.map φ) (by simp [φ, hd'p]) (by simp [φ, hd'q])

/-- Surjectivity identifies the target spectrum with the primes containing
the kernel, an order-connected subset of the source spectrum. -/
theorem catenary_of_surjective : Specs.catenary_of_surjectiveType.{u,v} := by
  intro R S _ _ f hf hR
  let e : PrimeSpectrum S ↪o PrimeSpectrum R :=
    OrderEmbedding.ofMapLEIff (PrimeSpectrum.comap f) (fun p q =>
      Ideal.comap_le_comap_iff_of_surjective f hf p.asIdeal q.asIdeal)
  apply catenary_of_orderEmbedding e ?_ hR
  change (Set.range (PrimeSpectrum.comap f)).OrdConnected
  rw [range_comap_of_surjective S f hf]
  constructor
  intro p hp q _ r hr
  exact (show RingHom.ker f ≤ p.asIdeal from hp).trans hr.1

/-- No CM hypothesis is imposed on a quotient. -/
theorem quotient_catenary : Specs.quotient_catenaryType.{u} := by
  intro R _ hR I
  exact catenary_of_surjective R (R ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective hR

/-- Every finite type algebra is a surjective image of a finite polynomial
extension. It inherits catenarity even when it is not Cohen–Macaulay. -/
theorem universally_catenary : Specs.universally_catenaryType.{u,v} := by
  intro R _ _ hCM B _ _ _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)
  exact catenary_of_surjective (MvPolynomial (Fin n) R) B f.toRingHom hf
    (mvPolynomial_catenary R hCM n)

end AdvCommAlg.CohenMacaulay
