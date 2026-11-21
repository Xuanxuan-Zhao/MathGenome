import MathGenome.Internal.D07.Ch17.IntertwinersEquivalence
import MathGenome.Internal.Specs.D07.Ch17.Characters

/-! Characters over arbitrary fields, and the modular boundary example.
The group is arbitrary in all the general laws. -/
namespace D07.Ch17.Characters

universe u v w x t z

noncomputable section

/-- The trace character of a finite-dimensional representation. -/
def character (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G) : K :=
  LinearMap.trace K V (ρ g)

theorem trace_matrix : Specs.D07.Ch17.Characters.TraceMatrix.{u,w,t} := by
  intro K V _ _ _ ι _ _ b T
  exact LinearMap.trace_eq_matrix_trace K b T

theorem trace_basis_independence :
    Specs.D07.Ch17.Characters.TraceBasisIndependence.{u,w,t,z} := by
  intro K V _ _ _ ι κ _ _ _ _ b c T
  rw [← trace_matrix K V ι b T, ← trace_matrix K V κ c T]

theorem matrix_trace_cyclic : Specs.D07.Ch17.Characters.MatrixTraceCyclic.{u,t} := by
  intro K _ ι _ _ A B
  refine ⟨rfl, ?_, rfl⟩
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem matrix_trace_conjugate :
    Specs.D07.Ch17.Characters.MatrixTraceConjugate.{u,t} := by
  intro K _ ι _ _ A P
  exact Matrix.trace_units_conj P A

theorem character_conjugate :
    Specs.D07.Ch17.Characters.CharacterConjugate.{u,v,w} := by
  intro K G V _ _ _ _ _ ρ g h
  change LinearMap.trace K V (ρ (h * g * h⁻¹)) = LinearMap.trace K V (ρ g)
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]

theorem character_equivalence :
    Specs.D07.Ch17.Characters.CharacterEquivalence.{u,v,w,x} := by
  intro K G V W _ _ _ _ _ _ _ _ ρ σ ⟨e⟩
  funext g
  change LinearMap.trace K V (ρ g) = LinearMap.trace K W (σ g)
  rw [← e.conj_apply_self g]
  exact (LinearMap.trace_conj' (ρ g) e.toLinearEquiv).symm

theorem character_one : Specs.D07.Ch17.Characters.CharacterOne.{u,v,w} := by
  intro K G V _ _ _ _ _ ρ
  change LinearMap.trace K V (ρ 1) = _
  rw [map_one, LinearMap.trace_one]

theorem modular_counterexample : Specs.D07.Ch17.Characters.ModularCounterexample := by
  intro p hp
  dsimp only
  have hp0 : 0 ≠ p := (Nat.Prime.ne_zero hp.out).symm
  refine ⟨Module.finrank_fin_fun _, Module.finrank_fin_fun _, hp0, ?_, ?_, ?_⟩
  · funext g
    change LinearMap.trace (ZMod p) (Fin 0 → ZMod p) 1 = 0
    simp [LinearMap.trace_one]
  · funext g
    change LinearMap.trace (ZMod p) (Fin p → ZMod p) 1 = 0
    simp [LinearMap.trace_one]
  · rintro ⟨e⟩
    have h := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    exact hp0 h

end

end D07.Ch17.Characters
