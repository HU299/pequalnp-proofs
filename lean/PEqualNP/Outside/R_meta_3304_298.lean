import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3304_298
  (budget : let F : (Fin 8 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
    ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), PEqualNP.MetaComplexity.FanInTwo A → PEqualNP.MetaComplexity.FanInTwo B →
      A.size + B.size ≤ 13 →
      let W := fun x : Fin 8 → Bool => A.wires (List.ofFn x)
      let q := fun x : Fin 8 → Bool => (W x).getD j false
      (∀ x, B.eval (W x ++ [q x]) = F x) →
      (∀ x, B.eval (W x ++ [false]) = (F x || x 0 || x 3)) →
      12 + A.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) + B.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) ≤ A.size + B.size)
  (bareBudget : let F : (Fin 8 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
    ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), PEqualNP.MetaComplexity.FanInTwo A → PEqualNP.MetaComplexity.FanInTwo B →
      A.size + B.size ≤ 13 →
      let W := fun x : Fin 8 → Bool => A.wires (List.ofFn x)
      let q := fun x : Fin 8 → Bool => (W x).getD j false
      (∀ x, B.eval (W x ++ [q x]) = F x) →
      (∀ x, B.eval (W x ++ [false]) = (F x || x 0 || x 3)) →
      (∀ x, q x = false → B.eval (W x ++ [true]) = B.eval (W x ++ [false])) →
      13 + A.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) + B.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) ≤ A.size + B.size)
  (tight : let F : (Fin 8 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
    ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), PEqualNP.MetaComplexity.FanInTwo A → PEqualNP.MetaComplexity.FanInTwo B →
      5 ≤ A.size → A.size + B.size = 13 → 8 ≤ j → j < 8 + A.size →
      A.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) = 0 → B.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op) = 1 →
      let W := fun x : Fin 8 → Bool => A.wires (List.ofFn x)
      let q := fun x : Fin 8 → Bool => (W x).getD j false
      (∀ x, B.eval (W x ++ [q x]) = F x) →
      (∃ x, x 0 = false ∧ x 3 = false ∧ q x = false ∧
        B.eval (W x ++ [true]) ≠ B.eval (W x ++ [false])) →
      ∃ x, B.eval (W x ++ [false]) ≠ (F x || x 0 || x 3)) :
  have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       (5 : ℕ) ≤ x2.size →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.true) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.false]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))) := by
  classical
  intro F A B j hA hB hmin hsize hj hjlt W q hq hcorrect
  by_contra hnone
  push Not at hnone
  let Below (u v : List Bool) : Prop :=
    u.length = v.length ∧ ∀ i, u.getD i false = true → v.getD i false = true

  have snoc_ne (u : List Bool) (a : Bool) {i : ℕ} (hi : i ≠ u.length) :
      (u ++ [a]).getD i false = u.getD i false := by
    by_cases h : i < u.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have snoc {u v : List Bool} {a b : Bool} (h : Below u v)
      (hab : a = true → b = true) : Below (u ++ [a]) (v ++ [b]) := by
    obtain ⟨hlen, hle⟩ := h
    refine ⟨by simp [hlen], ?_⟩
    intro i
    by_cases hi : i = u.length
    · subst i
      have hu : (u ++ [a]).getD u.length false = a := by simp
      have hv : (v ++ [b]).getD u.length false = b := by rw [hlen]; simp
      rw [hu, hv]
      exact hab
    · rw [snoc_ne u _ hi, snoc_ne v _ (by omega)]
      exact hle i

  let pushWire (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have runBelow (gs : List PEqualNP.CircuitLowerBounds.Gate) (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      {u v : List Bool} (h : Below u v) : Below (gs.foldl pushWire u) (gs.foldl pushWire v) := by
    induction gs generalizing u v with
    | nil => exact h
    | cons g gs ih =>
      apply ih (fun k hk => ok k (List.mem_cons_of_mem _ hk))
      apply snoc h
      intro hb
      rcases ok g List.mem_cons_self with hop | hop
      · rw [hop] at hb ⊢
        change (g.inputs.map (fun i => u.getD i false)).all id = true at hb
        change (g.inputs.map (fun i => v.getD i false)).all id = true
        simp only [List.all_map, Function.comp_apply, id, List.all_eq_true] at hb ⊢
        exact fun i hi => h.2 i (hb i hi)
      · rw [hop] at hb ⊢
        change (g.inputs.map (fun i => u.getD i false)).any id = true at hb
        change (g.inputs.map (fun i => v.getD i false)).any id = true
        simp only [List.any_map, Function.comp_apply, id, List.any_eq_true] at hb ⊢
        obtain ⟨i, hi, hb⟩ := hb
        exact ⟨i, hi, h.2 i hb⟩

  have lastBitMono (C : PEqualNP.CircuitLowerBounds.Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
      (hn : ∀ g ∈ C.gates, g.op ≠ .not) (w : List Bool) :
      C.eval (w ++ [false]) = true → C.eval (w ++ [true]) = true := by
    have ok : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := by
      intro g hg
      have hgop := (h g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgop
      exact hgop.elim Or.inl (fun h' => h'.elim Or.inr (fun a => (hn g hg a).elim))
    have hw : Below w w := ⟨rfl, fun _ a => a⟩
    exact (runBelow C.gates ok (snoc hw (a := false) (b := true) (by decide))).2 C.output

  let a : Fin 8 → Bool := fun i => decide (i = 0)
  have ha : F a = false := by decide
  have hb : (a 0 || a 3) = true := by decide
  have hc : (F a || a 0 || a 3) = true := by decide
  have hat := hcorrect a
  rw [hq a ha hb, ha] at hat
  have haf := hnone a
  rw [hc] at haf
  have existsNot : ∃ g ∈ B.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
    by_contra h
    have hn (g) (hg : g ∈ B.gates) (he : g.op = PEqualNP.CircuitLowerBounds.GateOp.not) := h ⟨g, hg, he⟩
    have hfail := lastBitMono B hB hn (W a) haf
    rw [hat] at hfail
    contradiction
  let mark : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g : PEqualNP.CircuitLowerBounds.Gate => PEqualNP.CircuitLowerBounds.GateOp.rec false false true (fun _ => false) false g.op
  have positive : 0 < B.gates.countP mark := by
    obtain ⟨g, hg, he⟩ := existsNot
    exact List.countP_pos_iff.mpr ⟨g, hg, by simp [mark, he]⟩
  have bound : 12 + A.gates.countP mark + B.gates.countP mark ≤ A.size + B.size :=
    budget A B j hA hB hsize hcorrect hnone
  have noPrefixNot : A.gates.countP mark = 0 := by omega
  have prefixOps : ∀ g ∈ A.gates, g.op = .and ∨ g.op = .or := by
    intro g hg
    have hp := (hA g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with ha | hb | hn
    · exact Or.inl ha
    · exact Or.inr hb
    · have pos : 0 < A.gates.countP mark := List.countP_pos_iff.mpr
          ⟨g, hg, by simp [mark, hn]⟩
      omega
  have portMono (x y : Fin 8 → Bool) (le : ∀ i, x i = true → y i = true) :
      q x = true → q y = true := by
    have hxy : Below (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp, ?_⟩
      intro i
      by_cases hi : i < 8
      · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
            List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
        simpa only [List.getElem_ofFn] using le ⟨i,hi⟩
      · simp [List.getD, hi]
    exact (runBelow A.gates prefixOps hxy).2 j
  have endpoint (x : Fin 8 → Bool) (k : Fin 8) (hk : k = 0 ∨ k = 3)
      (hx : x k = true) : q x = true := by
    let unit : Fin 8 → Bool := fun i => decide (i = k)
    have qUnit : q unit = true := by
      apply hq
      · rcases hk with rfl | rfl <;> decide
      · rcases hk with rfl | rfl <;> decide
    apply portMono unit x _ qUnit
    intro i hi
    have he : i = k := of_decide_eq_true hi
    simpa [he] using hx
  have dormant : ∃ x, q x = false ∧
      B.eval (W x ++ [true]) ≠ B.eval (W x ++ [false]) := by
    by_contra h
    push Not at h
    have impossible := bareBudget A B j hA hB hsize hcorrect hnone h
    change 13 + A.gates.countP mark + B.gates.countP mark ≤ A.size + B.size at impossible
    omega
  obtain ⟨x, hqx, difference⟩ := dormant
  have isOff (k : Fin 8) (hk : k = 0 ∨ k = 3) : x k = false := by
    cases hh : x k with
    | false => rfl
    | true => rw [endpoint x k hk hh] at hqx; contradiction
  obtain ⟨w, hw⟩ := tight A B j hA hB hmin (by omega) hj hjlt noPrefixNot
    (show B.gates.countP mark = 1 by omega) hcorrect
    ⟨x, isOff 0 (Or.inl rfl), isOff 3 (Or.inr rfl), hqx, difference⟩
  exact hw (hnone w)
