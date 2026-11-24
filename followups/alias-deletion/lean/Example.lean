import AliasDeletion

namespace Research.AliasDeletion.Example

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open Research.Boundary Research.AliasDeletion

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [0,2]⟩,
    ⟨GateOp.and, [0,1]⟩,
    ⟨GateOp.or, [0,1]⟩,
    ⟨GateOp.and, [5,2]⟩,
    ⟨GateOp.or, [4,6]⟩,
    ⟨GateOp.and, [1,7]⟩], 8⟩

def target (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)

def bits (m : ℕ) : Fin 3 → Bool := fun v => m.testBit v.val

def positive : List (Fin 3 → Bool) := [bits 3, bits 6]
def negative : List (Fin 3 → Bool) := [bits 2, bits 5]

theorem mono : Monotone2 circuit := by simp [Monotone2, circuit]

theorem clean : CleanL 3 circuit.gates := by
  intro p g hg
  have hp : p < 6 := by
    have h := (List.getElem?_eq_some_iff.mp hg).1
    simpa [circuit] using h
  interval_cases p <;> simp [circuit] at hg <;> subst g <;> simp [CleanGate]

theorem pos_cover : ∀ x : Fin 3 → Bool, target x = true →
    ∃ q ∈ positive, pointLe q x := by
  unfold pointLe
  decide +kernel

theorem neg_cover : ∀ x : Fin 3 → Bool, target x = false →
    ∃ q ∈ negative, pointLe x q := by
  unfold pointLe
  decide +kernel

theorem accepts : ∀ x ∈ positive, circuit.eval (List.ofFn x) = true := by
  decide +kernel

theorem rejects : ∀ x ∈ negative, circuit.eval (List.ofFn x) = false := by
  decide +kernel

theorem boundary_alias : ∀ x ∈ positive ++ negative,
    vl circuit.gates x (3 + 4) = vl circuit.gates x 3 := by
  decide +kernel

theorem not_global_alias :
    vl circuit.gates (bits 1) 7 ≠ vl circuit.gates (bits 1) 3 := by
  decide +kernel

theorem original_correct : ∀ x : Fin 3 → Bool,
    circuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem deleted_correct : Monotone2 (deleteAlias 3 4 3 circuit) ∧
    CleanL 3 (deleteAlias 3 4 3 circuit).gates ∧
    (deleteAlias 3 4 3 circuit).size + 1 = circuit.size ∧
    ∀ x : Fin 3 → Bool, (deleteAlias 3 4 3 circuit).eval (List.ofFn x) = target x := by
  exact deleteAlias_boundary circuit 4 3 target positive negative mono clean
    (by decide) (by decide) pos_cover neg_cover accepts rejects boundary_alias

theorem counts : circuit.size = 6 ∧ (deleteAlias 3 4 3 circuit).size = 5 := by
  exact ⟨rfl, rfl⟩

end Research.AliasDeletion.Example

#print axioms Research.AliasDeletion.Example.deleted_correct
#print axioms Research.AliasDeletion.Example.not_global_alias
