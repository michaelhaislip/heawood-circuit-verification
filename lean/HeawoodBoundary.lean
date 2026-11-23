import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace Research.Heawood971

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

def pointLe {n : ℕ} (x y : Fin n → Bool) : Prop :=
  ∀ u, x u = true → y u = true

theorem boundary_check {n : ℕ} (C : Circuit)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (f : (Fin n → Bool) → Bool) (positive negative : List (Fin n → Bool))
    (hpositive : ∀ x, f x = true → ∃ p ∈ positive, pointLe p x)
    (hnegative : ∀ x, f x = false → ∃ q ∈ negative, pointLe x q)
    (hp : ∀ p ∈ positive, C.eval (List.ofFn p) = true)
    (hq : ∀ q ∈ negative, C.eval (List.ofFn q) = false) :
    ∀ x, C.eval (List.ofFn x) = f x := by
  intro x
  cases hf : f x with
  | false =>
    apply Bool.eq_false_iff.mpr
    intro hc
    obtain ⟨q, hmem, hle⟩ := hnegative x hf
    have h := wires_mono C hmono x q hle C.output hc
    change C.eval (List.ofFn q) = true at h
    rw [hq q hmem] at h
    contradiction
  | true =>
    obtain ⟨p, hmem, hle⟩ := hpositive x hf
    exact wires_mono C hmono p x hle C.output (hp p hmem)


def heawoodEdges : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def edgePoint (e : Fin 14 × Fin 14) : Fin 14 → Bool :=
  fun u => decide (u = e.1 ∨ u = e.2)

def bitPoint (mask : ℕ) : Fin 14 → Bool :=
  fun u => mask.testBit u.val

def heawoodFun (x : Fin 14 → Bool) : Bool :=
  heawoodEdges.any (fun e => x e.1 && x e.2)

def positives : List (Fin 14 → Bool) := heawoodEdges.map edgePoint

def negatives : List (Fin 14 → Bool) := [bitPoint 127, bitPoint 244, bitPoint 314, bitPoint 432, bitPoint 541, bitPoint 660, bitPoint 792, bitPoint 1102, bitPoint 1220, bitPoint 1290, bitPoint 1548, bitPoint 2087, bitPoint 2212, bitPoint 2338, bitPoint 2565, bitPoint 3078, bitPoint 3716, bitPoint 4179, bitPoint 4304, bitPoint 4370, bitPoint 4625, bitPoint 5008, bitPoint 5186, bitPoint 6147, bitPoint 7426, bitPoint 8297, bitPoint 8416, bitPoint 8488, bitPoint 8713, bitPoint 9288, bitPoint 9992, bitPoint 10273, bitPoint 10656, bitPoint 12353, bitPoint 13504, bitPoint 14849, bitPoint 16256]

theorem positive_cover (x : Fin 14 → Bool) (h : heawoodFun x = true) :
    ∃ p ∈ positives, pointLe p x := by
  obtain ⟨e, he, htrue⟩ := List.any_eq_true.mp h
  have hpair : x e.1 = true ∧ x e.2 = true := by simpa using htrue
  refine ⟨edgePoint e, List.mem_map_of_mem he, ?_⟩
  intro u hu
  have hu' : u = e.1 ∨ u = e.2 := of_decide_eq_true hu
  rcases hu' with rfl | rfl
  · exact hpair.1
  · exact hpair.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem negative_cover_test : ∀ x : Fin 14 → Bool,
    heawoodFun x = false →
      negatives.any (fun q => decide (∀ u, x u = true → q u = true)) = true := by
  decide +kernel

theorem negative_cover (x : Fin 14 → Bool) (h : heawoodFun x = false) :
    ∃ q ∈ negatives, pointLe x q := by
  obtain ⟨q, hq, htrue⟩ := List.any_eq_true.mp (negative_cover_test x h)
  have hle : ∀ u, x u = true → q u = true := of_decide_eq_true htrue
  exact ⟨q, hq, hle⟩

def baseline : Circuit :=
  { gates := [⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [10, 14]⟩, ⟨GateOp.and, [0, 21]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.and, [6, 23]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [3, 25]⟩, ⟨GateOp.or, [12, 19]⟩, ⟨GateOp.and, [5, 27]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.and, [1, 29]⟩, ⟨GateOp.or, [13, 18]⟩, ⟨GateOp.and, [2, 31]⟩, ⟨GateOp.or, [13, 20]⟩, ⟨GateOp.and, [4, 33]⟩, ⟨GateOp.or, [22, 30]⟩, ⟨GateOp.or, [32, 35]⟩, ⟨GateOp.or, [26, 36]⟩, ⟨GateOp.or, [34, 37]⟩, ⟨GateOp.or, [28, 38]⟩, ⟨GateOp.or, [24, 39]⟩], output := 40 }

theorem baseline_mono : PEqualNP.MetaComplexity.Monotone2 baseline := by
  simp [PEqualNP.MetaComplexity.Monotone2, baseline]

theorem baseline_size : baseline.size = 27 := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem baseline_positive_test :
    positives.all (fun p => baseline.eval (List.ofFn p)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem baseline_negative_test :
    negatives.all (fun q => !(baseline.eval (List.ofFn q))) = true := by
  decide +kernel

theorem baseline_correct : ∀ x : Fin 14 → Bool,
    baseline.eval (List.ofFn x) = heawoodFun x := by
  apply boundary_check baseline baseline_mono heawoodFun positives negatives
    positive_cover negative_cover
  · exact List.all_eq_true.mp baseline_positive_test
  · intro q hq
    have h := List.all_eq_true.mp baseline_negative_test q hq
    simpa using h

theorem heawood_fun_iff (x : Fin 14 → Bool) :
    heawoodFun x = true ↔ ∃ u v : Fin 14,
      (u.val, v.val) ∈ heawoodEdges.map (fun e => (e.1.val, e.2.val)) ∧
        x u = true ∧ x v = true := by
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, he, htrue⟩ := List.any_eq_true.mp h
    have hpair : x u = true ∧ x v = true := by simpa using htrue
    exact ⟨u, v, List.mem_map_of_mem he, hpair⟩
  · rintro ⟨u, v, he, hu, hv⟩
    obtain ⟨⟨a, b⟩, hab, heq⟩ := List.mem_map.mp he
    have hau : a = u := Fin.ext (congrArg Prod.fst heq)
    have hbv : b = v := Fin.ext (congrArg Prod.snd heq)
    apply List.any_eq_true.mpr
    exact ⟨(a, b), hab, by simp [hau, hbv, hu, hv]⟩

theorem baseline_target :
    PEqualNP.MetaComplexity.Monotone2 baseline ∧ baseline.size = 27 ∧
    ∀ x : Fin 14 → Bool, baseline.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 14, (u.val, v.val) ∈
        ([(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
          (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
          (6,8),(6,9),(6,11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
  refine ⟨baseline_mono, baseline_size, ?_⟩
  intro x
  rw [baseline_correct x]
  exact heawood_fun_iff x

end Research.Heawood971

#print axioms Research.Heawood971.boundary_check
#print axioms Research.Heawood971.baseline_target
