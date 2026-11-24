import Boundary
import PEqualNP.MetaComplexity.Helpers.EdgeFnModel

namespace Research.AliasDeletion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.EdgeFn
open Research.Boundary

def deleteAlias (n p a : ℕ) (C : Circuit) : Circuit :=
  ⟨rdel n p a C.gates, rd n p a C.output⟩

theorem deleteAlias_mono (n p a : ℕ) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (deleteAlias n p a C) := by
  intro g hg
  simp only [deleteAlias, rdel, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g0, hg0, rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · obtain ⟨hop, hlen⟩ := h g0 (List.mem_of_mem_drop hg0)
    exact ⟨hop, by simpa using hlen⟩

theorem deleteAlias_size (n p a : ℕ) (C : Circuit) (hp : p < C.gates.length) :
    (deleteAlias n p a C).size + 1 = C.size :=
  rdel_length n p a C.gates hp

theorem deleteAlias_clean (n p a : ℕ) (C : Circuit) (hc : CleanL n C.gates)
    (hp : p < C.gates.length) (ha : a < n + p) :
    CleanL n (deleteAlias n p a C).gates :=
  rdel_clean n p a C.gates hc hp ha

theorem deleteAlias_eval (n p a : ℕ) (C : Circuit) (hc : CleanL n C.gates)
    (hp : p < C.gates.length) (ha : a < n + p) (x : Fin n → Bool)
    (hx : vl C.gates x (n + p) = vl C.gates x a) :
    (deleteAlias n p a C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  exact rdel_all n p a C.gates hc hp ha x hx C.output

theorem deleteAlias_boundary {n : ℕ} (C : Circuit) (p a : ℕ)
    (f : (Fin n → Bool) → Bool) (positive negative : List (Fin n → Bool))
    (hmono : Monotone2 C) (hc : CleanL n C.gates)
    (hp : p < C.gates.length) (ha : a < n + p)
    (hpos : ∀ x, f x = true → ∃ q ∈ positive, pointLe q x)
    (hneg : ∀ x, f x = false → ∃ q ∈ negative, pointLe x q)
    (haccept : ∀ x ∈ positive, C.eval (List.ofFn x) = true)
    (hreject : ∀ x ∈ negative, C.eval (List.ofFn x) = false)
    (halias : ∀ x ∈ positive ++ negative, vl C.gates x (n + p) = vl C.gates x a) :
    Monotone2 (deleteAlias n p a C) ∧
    CleanL n (deleteAlias n p a C).gates ∧
    (deleteAlias n p a C).size + 1 = C.size ∧
    ∀ x : Fin n → Bool, (deleteAlias n p a C).eval (List.ofFn x) = f x := by
  have hm := deleteAlias_mono n p a C hmono
  refine ⟨hm, deleteAlias_clean n p a C hc hp ha, deleteAlias_size n p a C hp, ?_⟩
  apply boundary_check _ hm f positive negative hpos hneg
  · intro x hx
    rw [deleteAlias_eval n p a C hc hp ha x
      (halias x (List.mem_append.mpr (Or.inl hx))), haccept x hx]
  · intro x hx
    rw [deleteAlias_eval n p a C hc hp ha x
      (halias x (List.mem_append.mpr (Or.inr hx))), hreject x hx]

theorem minimal_no_boundary_alias {n : ℕ} (C : Circuit) (p a : ℕ)
    (f : (Fin n → Bool) → Bool) (positive negative : List (Fin n → Bool))
    (hmono : Monotone2 C) (hc : CleanL n C.gates)
    (hp : p < C.gates.length) (ha : a < n + p)
    (hpos : ∀ x, f x = true → ∃ q ∈ positive, pointLe q x)
    (hneg : ∀ x, f x = false → ∃ q ∈ negative, pointLe x q)
    (haccept : ∀ x ∈ positive, C.eval (List.ofFn x) = true)
    (hreject : ∀ x ∈ negative, C.eval (List.ofFn x) = false)
    (hleast : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) → C.size ≤ D.size) :
    ¬ ∀ x ∈ positive ++ negative, vl C.gates x (n + p) = vl C.gates x a := by
  intro halias
  obtain ⟨hm, _, hs, hf⟩ := deleteAlias_boundary C p a f positive negative
    hmono hc hp ha hpos hneg haccept hreject halias
  have hle := hleast (deleteAlias n p a C) hm hf
  omega

theorem alias_free_representative {n : ℕ} (C : Circuit)
    (f : (Fin n → Bool) → Bool) (positive negative : List (Fin n → Bool))
    (hmono : Monotone2 C) (hc : CleanL n C.gates)
    (hpos : ∀ x, f x = true → ∃ q ∈ positive, pointLe q x)
    (hneg : ∀ x, f x = false → ∃ q ∈ negative, pointLe x q)
    (haccept : ∀ x ∈ positive, C.eval (List.ofFn x) = true)
    (hreject : ∀ x ∈ negative, C.eval (List.ofFn x) = false) :
    ∃ D : Circuit, Monotone2 D ∧ CleanL n D.gates ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) ∧
      ∀ p, p < D.gates.length → ∀ a, a < n + p →
        ¬ ∀ x ∈ positive ++ negative, vl D.gates x (n + p) = vl D.gates x a := by
  classical
  have hcf := boundary_check C hmono f positive negative hpos hneg haccept hreject
  let P : ℕ → Prop := fun k => ∃ D : Circuit, Monotone2 D ∧ CleanL n D.gates ∧
    D.size = k ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x
  have hex : ∃ k, P k := ⟨C.size, C, hmono, hc, rfl, hcf⟩
  obtain ⟨D, hDm, hDc, hDs, hDf⟩ := Nat.find_spec hex
  refine ⟨D, hDm, hDc, ?_, hDf, ?_⟩
  · have hmin : Nat.find hex ≤ C.size :=
      Nat.find_min' hex ⟨C, hmono, hc, rfl, hcf⟩
    omega
  · intro p hp a ha halias
    have hdaccept : ∀ x ∈ positive, D.eval (List.ofFn x) = true := by
      intro x hx
      rw [hDf x, ← hcf x]
      exact haccept x hx
    have hdreject : ∀ x ∈ negative, D.eval (List.ofFn x) = false := by
      intro x hx
      rw [hDf x, ← hcf x]
      exact hreject x hx
    obtain ⟨hEm, hEc, hEs, hEf⟩ := deleteAlias_boundary D p a f positive negative
      hDm hDc hp ha hpos hneg hdaccept hdreject halias
    have hmin : Nat.find hex ≤ (deleteAlias n p a D).size :=
      Nat.find_min' hex ⟨deleteAlias n p a D, hEm, hEc, rfl, hEf⟩
    omega

end Research.AliasDeletion

#print axioms Research.AliasDeletion.deleteAlias_boundary
#print axioms Research.AliasDeletion.minimal_no_boundary_alias
#print axioms Research.AliasDeletion.alias_free_representative
