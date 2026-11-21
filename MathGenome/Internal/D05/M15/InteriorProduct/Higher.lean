import MathGenome.Internal.Specs.D05.M15.InteriorProduct.Higher
import MathGenome.Internal.D05.M15.InteriorProduct
import MathGenome.Internal.D05.M15.ExteriorPairing

/-! Higher interior contraction, paper.tex:3136–3138.
The canonical exterior lift and determinant-pairing bridge are reused from
InteriorProduct. The alternating-map and unique-factorization results below
make explicit why the iterated composite depends only on the exterior covector.
-/
noncomputable section
namespace D05.M15.InteriorProduct.Higher
universe u v

abbrev contraction := @Specs.D05.M15.InteriorProduct.Higher.contraction_value

theorem generator : Specs.D05.M15.InteriorProduct.Higher.generator :=
  D05.M15.InteriorProduct.higher_generator

theorem unit : Specs.D05.M15.InteriorProduct.Higher.unit :=
  D05.M15.InteriorProduct.higher_unit

theorem product : Specs.D05.M15.InteriorProduct.Higher.product :=
  D05.M15.InteriorProduct.higher_product

theorem word_formula : Specs.D05.M15.InteriorProduct.Higher.word_formula :=
  D05.M15.InteriorProduct.higher_word

private theorem elementary_formula {K : Type u} {V : Type v} [Field K]
    [AddCommGroup V] [Module K V] (r : ℕ) (f : Fin r → Module.Dual K V)
    (a : _root_.ExteriorAlgebra K V) :
    contraction K V (_root_.ExteriorAlgebra.ιMulti K r f) a =
      (List.ofFn f).foldl
        (fun a φ => Specs.D05.M15.InteriorProduct.interior φ a) a := by
  simpa only [Specs.D05.M15.InteriorProduct.word,
    _root_.ExteriorAlgebra.ιMulti_apply, List.map_ofFn, Function.comp_def] using
    word_formula (List.ofFn f) a

theorem composite_alternating :
    Specs.D05.M15.InteriorProduct.Higher.composite_alternating := by
  intro K V _ _ _ r
  refine ⟨(contraction K V).compAlternatingMap
    (_root_.ExteriorAlgebra.ιMulti K r), ?_⟩
  intro f a
  exact elementary_formula r f a

theorem repeated_input : Specs.D05.M15.InteriorProduct.Higher.repeated_input := by
  intro K V _ _ _ r f i j hij heq a
  obtain ⟨A, hA⟩ := composite_alternating (K := K) (V := V) r
  rw [← hA f a, A.map_eq_zero_of_eq f heq hij]
  rfl

theorem factor_unique : Specs.D05.M15.InteriorProduct.Higher.factor_unique := by
  intro K V _ _ _ r
  let D := (contraction K V).comp (Submodule.subtype (⋀[K]^r (Module.Dual K V)))
  have hD : ∀ (f : Fin r → Module.Dual K V) (a : _root_.ExteriorAlgebra K V),
      D (exteriorPower.ιMulti K r f) a =
        (List.ofFn f).foldl
          (fun a φ => Specs.D05.M15.InteriorProduct.interior φ a) a :=
    elementary_formula r
  refine ⟨D, hD, ?_⟩
  intro E hE
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  apply LinearMap.ext
  intro a
  exact (hE f a).trans (hD f a).symm

theorem degree : Specs.D05.M15.InteriorProduct.Higher.degree := by
  intro K V _ _ _ r q α a
  exact D05.M15.InteriorProduct.higher_degree (K := K) (V := V) r
    (α : _root_.ExteriorAlgebra K (Module.Dual K V)) α.property q
    (a : _root_.ExteriorAlgebra K V) a.property

theorem pairing : Specs.D05.M15.InteriorProduct.Higher.pairing := by
  intro K V _ _ _ r q α β a
  let b : ⋀[K]^q V := ⟨contraction K V α a, degree r q α a⟩
  refine ⟨b, rfl, ?_⟩
  change exteriorPower.pairingDual K V q β b =
    exteriorPower.pairingDual K V (r+q)
      ⟨(α : _root_.ExteriorAlgebra K (Module.Dual K V)) * β,
        SetLike.GradedMul.mul_mem α.property β.property⟩ a
  rw [← D05.M15.InteriorProduct.scalar_contraction_pairing,
    ← D05.M15.InteriorProduct.scalar_contraction_pairing]
  exact congrArg D05.M15.InteriorProduct.scalarPart
    (LinearMap.congr_fun (product
      (α : _root_.ExteriorAlgebra K (Module.Dual K V))
      (β : _root_.ExteriorAlgebra K (Module.Dual K V))) a).symm

theorem dual_pair_guard : Specs.D05.M15.InteriorProduct.Higher.dual_pair_guard :=
  D05.M15.InteriorProduct.higher_guard

theorem counterexample : Specs.D05.M15.InteriorProduct.Higher.counterexample :=
  D05.M15.InteriorProduct.higher_counterexample

end D05.M15.InteriorProduct.Higher
