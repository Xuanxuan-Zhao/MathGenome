import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.TangentCotangent
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SplitQuotient

namespace AdvCommAlg.Differentials

universe u v w
noncomputable section
open TensorProduct
open Specs.AdvCommAlg.Differentials.Tangent

/-- The coordinate dual numbers are the polynomial quotient in KD-23. -/
theorem point_dual_numbers_model : dualNumbersModel.{w} := by
  intro K _
  let I : Ideal (Polynomial K) := Ideal.span {Polynomial.X ^ 2}
  let z : DualQuotient K := Ideal.Quotient.mk I Polynomial.X
  have hz : z * z = 0 := by
    change Ideal.Quotient.mk I Polynomial.X * Ideal.Quotient.mk I Polynomial.X = 0
    rw [← map_mul, ← pow_two]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let p : Polynomial K →ₐ[K] DualNumber K := Polynomial.aeval DualNumber.eps
  have hp : I ≤ RingHom.ker p.toRingHom := by
    rw [Ideal.span_le]
    rintro a (rfl : a = Polynomial.X ^ 2)
    simp [p]
  let f : DualQuotient K →ₐ[K] DualNumber K :=
    Ideal.Quotient.liftₐ I p (fun a ha => hp ha)
  let g : DualNumber K →ₐ[K] DualQuotient K :=
    DualNumber.lift ⟨(Algebra.ofId K (DualQuotient K), z), hz, fun _ => Commute.all _ _⟩
  have hfX : f z = DualNumber.eps := by
    change Polynomial.aeval (DualNumber.eps : DualNumber K) Polynomial.X = _
    exact Polynomial.aeval_X _
  have hgε : g DualNumber.eps = z := DualNumber.lift_apply_eps _
  have hfg : f.comp g = AlgHom.id K (DualNumber K) := by
    apply DualNumber.algHom_ext
    simpa only [AlgHom.comp_apply, AlgHom.id_apply, hgε] using hfX
  have hgf : g.comp f = AlgHom.id K (DualQuotient K) := by
    apply Ideal.Quotient.algHom_ext
    apply Polynomial.algHom_ext
    change g (f z) = z
    rw [hfX, hgε]
  refine ⟨AlgEquiv.ofAlgHom f g hfg hgf, hfX, ?_⟩
  intro a
  change f (Ideal.Quotient.mk I (Polynomial.C a)) = TrivSqZeroExt.inl a
  change Polynomial.aeval (DualNumber.eps : DualNumber K) (Polynomial.C a) = _
  exact Polynomial.aeval_C _ _

/-- The dual of the fibre of Ω is the vector space of relative derivations
with coefficients restricted along the given point. -/
theorem point_dual_derivations : dualDerivations.{u,v,w} := by
  intro A B K _ _ _ _ _ x
  let := x.toRingHom.toAlgebra
  let e := (LinearMap.liftBaseChangeEquiv K (R := B)
    (M := KaehlerDifferential A B) (N := K)).symm.toEquiv.trans
      (KaehlerDifferential.linearMapEquivDerivation A B).toEquiv
  refine ⟨{ e with map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro L L'; apply Derivation.ext; intro b; rfl
  · intro a L; apply Derivation.ext; intro b; rfl
  · intro L b; rfl

/-- A tangent derivation is exactly the epsilon coordinate of a lift of x. -/
theorem point_tangent_lifts : tangentLifts.{u,v,w} := by
  intro A B K _ _ _ _ _ x
  let := x.toRingHom.toAlgebra
  let F (D : Derivation A B K) : PointLifts A B K x :=
    ⟨{ toFun := fun b => (x b, D b)
       map_one' := by apply TrivSqZeroExt.ext <;> simp
       map_mul' := by
         intro b c
         apply TrivSqZeroExt.ext
         · exact x.map_mul b c
         · change D (b*c) = x b * D c + D b * x c
           rw [mul_comm (D b) (x c)]
           exact D.leibniz b c
       map_zero' := by apply TrivSqZeroExt.ext <;> simp
       map_add' := by
         intro b c
         apply TrivSqZeroExt.ext
         · exact x.map_add b c
         · exact D.map_add b c
       commutes' := by
         intro a
         apply TrivSqZeroExt.ext
         · exact x.commutes a
         · exact D.map_algebraMap a }, by ext; rfl⟩
  let G (f : PointLifts A B K x) : Derivation A B K := by
    have hfst (b : B) : (f.1 b).fst = x b :=
      congrArg (fun g : B →ₐ[A] K => g b) f.2
    refine Derivation.mk'
      { toFun := fun b => (f.1 b).snd
        map_add' := fun b c => by simp
        map_smul' := fun a b => by simp } ?_
    intro b c
    change (f.1 (b*c)).snd = x b • (f.1 c).snd + x c • (f.1 b).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
  refine ⟨⟨F, G, ?_, ?_⟩, fun _ _ => rfl, ?_⟩
  · intro D; apply Derivation.ext; intro b; rfl
  · intro f
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    apply TrivSqZeroExt.ext
    · exact (congrArg (fun g : B →ₐ[A] K => g b) f.2).symm
    · rfl
  · apply AlgHom.ext; intro b; rfl

/-- The dual is identified directly with infinitesimal lifts, sending
zero to the constant lift and L to b ↦ x(b) + ε L(1 ⊗ db). -/
theorem point_dual_lifts : dualLifts.{u,v,w} := by
  intro A B K _ _ _ _ _ x
  let := x.toRingHom.toAlgebra
  obtain ⟨e, he⟩ := point_dual_derivations A B K x
  obtain ⟨f, hf, hf0⟩ := point_tangent_lifts A B K x
  refine ⟨e.toEquiv.trans f, ?_, ?_⟩
  · intro L b
    change (f (e L)).1 b = _
    rw [hf, he]
  · change (f (e 0)).1 = _
    rw [map_zero, hf0]

/-- The rational-point conormal map is invertible because the last term of
the split conormal sequence is Ω[k/k] = 0. -/
theorem point_cotangent : rationalCotangent.{u,v} := by
  intro k B _ _ _ x
  let := x.toRingHom.toAlgebra
  have hs : Function.RightInverse (Algebra.ofId k B) (algebraMap B k) := by
    intro a
    exact x.commutes a
  have h : Function.Surjective (algebraMap B k) := hs.surjective
  obtain ⟨D, hD, r, hr, hleft, hinj, hex, hsurj, t, ht⟩ :=
    split_quotient k B k h (Algebra.ofId k B) hs
  let : Subsingleton (KaehlerDifferential k k) := subsingleton_self k
  have hj : Function.Surjective (conormalMap k B k h) := by
    intro z
    exact (hex z).mp (Subsingleton.elim _ _)
  let e := LinearEquiv.ofBijective (conormalMap k B k h) ⟨hinj, hj⟩
  let P := Specs.AdvCommAlg.Differentials.conormalExtension k B k h
  let q := P.cotangentEquivCotangentKer.restrictScalars k
  refine ⟨q.symm.trans e, ?_⟩
  intro b
  exact conormalMap_apply k B k h b

end
end AdvCommAlg.Differentials
