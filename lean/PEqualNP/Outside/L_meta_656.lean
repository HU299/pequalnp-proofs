import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_656_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

-- Wire support and counting lemmas adapted from the project's L-meta-011 proof.
-- The joint support bound counts a shared subcircuit just once.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem pnpArity {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (sens : ∀ i, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y)
    (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, y, hoff, hne⟩ := sens i
    apply hne
    have hag := (agree_wiresFrom x y C.gates _ _ _ (agree_inputs _ _)).2.2 C.output (by
      intro j hj
      exact hoff j (fun e => hi (e ▸ hj)))
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]
    simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.Outside.L_meta_656_aux

namespace PEqualNP.Outside.L_meta_656_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pnpPassenger (x : Fin 3 → Bool) : Bool := x 2 && (x 0 || x 1)

theorem pnpMonotone : ∀ x y : Fin 3 → Bool,
    (∀ i, x i = true → y i = true) → pnpPassenger x = true → pnpPassenger y = true := by
  intro x y h hx
  simp only [pnpPassenger, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
  exact ⟨h _ hx.1, hx.2.imp (h _) (h _)⟩

theorem pnpZero : pnpPassenger (fun _ => false) = false := rfl

theorem pnpNonempty : ∃ x, pnpPassenger x = true := ⟨fun _ => true, rfl⟩

theorem pnpMiss0 : ∃ x : Fin 3 → Bool, x 0 = true ∧ pnpPassenger x = false :=
  ⟨fun j => decide (j = 0), rfl, rfl⟩

theorem pnpMiss1 : ∃ x : Fin 3 → Bool, x 1 = true ∧ pnpPassenger x = false :=
  ⟨fun j => decide (j = 1), rfl, rfl⟩

def pnpShortFunction (x : Fin 4 → Bool) : Bool :=
  pnpPassenger (fun i => x i.castSucc) || (x 0 && x 3) || (x 3 && x 1)

def pnpSideA (x : Fin 4 → Bool) : Bool :=
  pnpPassenger (fun i => x i.castSucc) || (x 0 && x 3)

def pnpSideB (x : Fin 4 → Bool) : Bool :=
  pnpPassenger (fun i => x i.castSucc) || (x 1 && x 3)

def pnpSplit (x : Fin 5 → Bool) : Bool :=
  pnpPassenger (fun i => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)

def pnpThreeGates : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩], 6⟩

theorem pnpShort : HasCircuitSize 4 pnpShortFunction 3 := by
  refine ⟨pnpThreeGates, ?_, by decide, ?_⟩
  · intro g hg
    simp [pnpThreeGates] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · decide

def pnpAllSensitive {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i, ∃ x y, (∀ j, j ≠ i → x j = y j) ∧ f x ≠ f y

theorem pnpFlipWitness {n : ℕ} (f : (Fin n → Bool) → Bool) (b : Fin n → Fin n)
    (h : ∀ i, f (fun j => decide (j = b i)) ≠
      f (fun j => decide (j = i) || decide (j = b i))) : pnpAllSensitive f := by
  intro i
  refine ⟨fun j => decide (j = b i), fun j => decide (j = i) || decide (j = b i), ?_, h i⟩
  intro j hj
  simp [hj]

theorem pnpSensitiveG : pnpAllSensitive pnpPassenger := by
  apply pnpFlipWitness _ (fun i => if i < 2 then 2 else 0)
  decide

theorem pnpSensitiveA : pnpAllSensitive pnpSideA := by
  apply pnpFlipWitness _ (fun i => if i < 2 then 2 else 0)
  decide

theorem pnpSensitiveB : pnpAllSensitive pnpSideB := by
  apply pnpFlipWitness _ (fun i => if i < 2 then 2 else 1)
  decide

theorem pnpSensitiveSplit : pnpAllSensitive pnpSplit := by
  apply pnpFlipWitness _ (fun i => if i < 2 then 2 else if i = 4 then 1 else 0)
  decide

theorem pnpFirstFails
    (hg : ∀ t, HasCircuitSize 3 pnpPassenger t → 3 ≤ t + 1)
    (ha : ∀ t, HasCircuitSize 4 pnpSideA t → 4 ≤ t + 1)
    (hb : ∀ t, HasCircuitSize 4 pnpSideB t → 4 ≤ t + 1)
    (hs : ∀ t, HasCircuitSize 5 pnpSplit t → 5 ≤ t + 1) :
    ¬ (HasCircuitSize 4 pnpShortFunction 3 ↔
      ((∃ t, 3 + t ≤ 3 ∧ HasCircuitSize 3 pnpPassenger t) ∨
       (∃ t, 2 + t ≤ 3 ∧ (HasCircuitSize 4 pnpSideA t ∨ HasCircuitSize 4 pnpSideB t)) ∨
       HasCircuitSize 5 pnpSplit 3)) := by
  intro h
  rcases h.mp pnpShort with ⟨t, ht, h1⟩ | ⟨t, ht, h1 | h1⟩ | h1
  · have := hg _ h1
    omega
  · have := ha _ h1
    omega
  · have := hb _ h1
    omega
  · have := hs _ h1
    omega

end PEqualNP.Outside.L_meta_656_aux

theorem PEqualNP.Outside.L_meta_656 : ¬ (∀ g : (Fin 3 → Bool) → Bool, (∀ x y : Fin 3 → Bool, (∀ i, x i = true → y i = true) → g x = true → g y = true) → g (fun _ : Fin 3 => false) = false → (∃ x : Fin 3 → Bool, g x = true) → (∃ x : Fin 3 → Bool, x 0 = true ∧ g x = false) → (∃ x : Fin 3 → Bool, x 1 = true ∧ g x = false) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3) || (x 3 && x 1)) s ↔ ((∃ t : ℕ, 3 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨ (∃ t : ℕ, 2 + t ≤ s ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨ PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)) s)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 1)) s ↔ ((∃ t : ℕ, 5 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨ (∃ t : ℕ, 3 + t ≤ s ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨ (∃ t : ℕ, 2 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)) t))) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 3 i)) || (x 0 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 1)) s ↔ ((∃ t : ℕ, 6 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 3 g t) ∨ (∃ t : ℕ, 5 + t ≤ s ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 0 && x 3)) t ∨ PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => g (fun i : Fin 3 => x i.castSucc) || (x 1 && x 3)) t)) ∨ (∃ t : ℕ, 3 + t ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => g (fun i : Fin 3 => x (Fin.castAdd 2 i)) || (x 0 && x 3) || (x 1 && x 4)) t)))) := by
  intro h
  apply PEqualNP.Outside.L_meta_656_aux.pnpFirstFails
    (fun _ hsize => PEqualNP.Outside.L_meta_656_aux.pnpArity PEqualNP.Outside.L_meta_656_aux.pnpSensitiveG hsize)
    (fun _ hsize => PEqualNP.Outside.L_meta_656_aux.pnpArity PEqualNP.Outside.L_meta_656_aux.pnpSensitiveA hsize)
    (fun _ hsize => PEqualNP.Outside.L_meta_656_aux.pnpArity PEqualNP.Outside.L_meta_656_aux.pnpSensitiveB hsize)
    (fun _ hsize => PEqualNP.Outside.L_meta_656_aux.pnpArity PEqualNP.Outside.L_meta_656_aux.pnpSensitiveSplit hsize)
  exact (h PEqualNP.Outside.L_meta_656_aux.pnpPassenger PEqualNP.Outside.L_meta_656_aux.pnpMonotone
    PEqualNP.Outside.L_meta_656_aux.pnpZero PEqualNP.Outside.L_meta_656_aux.pnpNonempty
    PEqualNP.Outside.L_meta_656_aux.pnpMiss0 PEqualNP.Outside.L_meta_656_aux.pnpMiss1 3).1
