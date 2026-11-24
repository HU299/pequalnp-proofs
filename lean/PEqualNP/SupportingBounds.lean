import Mathlib.Data.List.GetD
import PEqualNP.Defs.MetaComplexity

-- Supporting constructions for HU299's main-repository PR 7037.
-- The wire reindexing follows the simulation used in the project's L-meta-195.
-- The final adapters take the checked nine-input bound from L-meta-2165 as a hypothesis.

namespace Pnp3304Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_snoc (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (z : Bool)
    (h : Rel n m π W W') : Rel n m π (W ++ [z]) (W' ++ [z]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro w
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  change Rel _ _ _ (_ ++ [_]) (_ ++ [_])
  rw [hv]
  exact rel_snoc _ _ _ _ _ _ ⟨h1, h2, h3⟩

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]; omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

def skipU (i : Fin 8) : Fin 9 :=
  ⟨if i.val < 4 then i.val else i.val + 1, by split <;> omega⟩

def port (i : Fin 8) : Fin 10 := (skipU i).castSucc

def notU : Gate := ⟨.not, [4]⟩

def mask (j : ℕ) : Gate := ⟨.and, [wmap 8 10 port j, 9]⟩

def lift (A B : Circuit) (j : ℕ) : Circuit :=
  ⟨[notU] ++ A.gates.map (relGate 8 10 port) ++ [mask j] ++ B.gates.map (relGate 8 10 port),
    wmap 8 10 port B.output⟩

theorem lift_size (A B : Circuit) (j : ℕ) :
    (lift A B j).size = A.size + B.size + 2 := by simp [lift, Circuit.size]; omega

theorem lift_counts (A B : Circuit) (j : ℕ) (p : GateOp → Bool) :
    (lift A B j).gates.countP (fun g => p g.op) =
    A.gates.countP (fun g => p g.op) + B.gates.countP (fun g => p g.op) +
      (p .not).toNat + (p .and).toNat := by
  simp only [lift, List.countP_append, List.countP_map, List.countP_singleton, Function.comp_def,
    relGate, notU, mask, Bool.toNat]
  cases p .not <;> cases p .and <;> simp <;> omega

theorem lift_ok (A B : Circuit) (j : ℕ) (ha : FanInTwo A) (hb : FanInTwo B) :
    FanInTwo (lift A B j) := by
  intro g hg
  simp only [lift, List.mem_append, List.mem_singleton, List.mem_map] at hg
  rcases hg with ((rfl | ⟨e, he, rfl⟩) | rfl) | ⟨e, he, rfl⟩
  · simp [notU]
  · exact ⟨(ha e he).1, by simpa [relGate] using (ha e he).2⟩
  · simp [mask]
  · exact ⟨(hb e he).1, by simpa [relGate] using (hb e he).2⟩

theorem initial (x : Fin 9 → Bool) :
    Rel 8 10 port (List.ofFn (x ∘ skipU)) (List.ofFn x ++ [! x 4]) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h : i < 8
  · simp only [wmap, dite_eq_left h]
    have hi : (port ⟨i,h⟩).val < (List.ofFn x).length := by
      simp only [List.length_ofFn, port, Fin.val_castSucc]
      exact (skipU ⟨i,h⟩).isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_ofFn]
    rfl
  · simp only [wmap, dite_eq_right h]
    rw [List.getD_eq_default _ _ (by simp),
      List.getD_eq_default _ _ (by simp; omega)]

theorem notU_step (x : Fin 9 → Bool) :
    step (List.ofFn x) notU = List.ofFn x ++ [! x 4] := by
  simp [step, notU, GateOp.eval]

theorem lift_eval (A B : Circuit) (j : ℕ) (x : Fin 9 → Bool) :
    (lift A B j).eval (List.ofFn x) =
      let W := A.wires (List.ofFn (x ∘ skipU))
      B.eval (W ++ [W.getD j false && ! x 4]) := by
  let W := A.wires (List.ofFn (x ∘ skipU))
  let E := (A.gates.map (relGate 8 10 port)).foldl step (List.ofFn x ++ [! x 4])
  have hpre : Rel 8 10 port W E := rel_fold _ _ _ A.gates _ _ (initial x)
  have hn : E.getD 9 false = ! x 4 := by
    unfold E
    rw [run_keep _ _ _ (by simp)]
    simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn x) (! x 4) false
  have hm : step E (mask j) = E ++ [W.getD j false && ! x 4] := by
    change E ++ [E.getD (wmap 8 10 port j) false && (E.getD 9 false && true)] = _
    rw [hpre.2.2 j, hn, Bool.and_true]
  have hr := rel_snoc _ _ _ _ _ (W.getD j false && ! x 4) hpre
  have hs := (rel_fold _ _ _ B.gates _ _ hr).2.2 B.output
  change (([notU] ++ _ ++ [mask j] ++ _).foldl step (List.ofFn x)).getD _ false = _
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, notU_step]
  change ((B.gates.map _).foldl step (step E (mask j))).getD _ false = _
  rw [hm]
  exact hs

theorem lift_function (A B : Circuit) (j : ℕ) (F : (Fin 8 → Bool) → Bool)
    (ha : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      B.eval (W ++ [W.getD j false]) = F z)
    (hb : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      B.eval (W ++ [false]) = (F z || z 0 || z 3)) (x : Fin 9 → Bool) :
    (lift A B j).eval (List.ofFn x) = (F (x ∘ skipU) || (x 4 && (x 0 || x 3))) := by
  rw [lift_eval]
  dsimp only
  cases h : x 4
  · simpa using ha (x ∘ skipU)
  · have h0 : skipU 0 = 0 := rfl
    have h3 : skipU 3 = 3 := rfl
    simpa [Bool.or_assoc, h0, h3] using hb (x ∘ skipU)

theorem costed_lifting (A B : Circuit) (j : ℕ) (F : (Fin 8 → Bool) → Bool)
    (hA : FanInTwo A) (hB : FanInTwo B)
    (hnatural : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      B.eval (W ++ [W.getD j false]) = F z)
    (hforced : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      B.eval (W ++ [false]) = (F z || z 0 || z 3)) :
    ∃ C : Circuit, FanInTwo C ∧ C.size = A.size + B.size + 2 ∧
      (∀ p : GateOp → Bool, C.gates.countP (fun g => p g.op) =
        A.gates.countP (fun g => p g.op) + B.gates.countP (fun g => p g.op) +
        (p .not).toNat + (p .and).toNat) ∧
      ∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x) =
          (F (fun i => x ⟨if i.val < 4 then i.val else i.val + 1, by split <;> omega⟩) ||
          (x 4 && (x 0 || x 3))) :=
  ⟨lift A B j, lift_ok A B j hA hB, lift_size A B j, lift_counts A B j,
    lift_function A B j F hnatural hforced⟩

def bareLift (A B : Circuit) : Circuit :=
  ⟨A.gates.map (relGate 8 9 skipU) ++ [notU] ++ B.gates.map (relGate 8 9 skipU),
    wmap 8 9 skipU B.output⟩

theorem bare_size (A B : Circuit) :
    (bareLift A B).size = A.size + B.size + 1 := by simp [bareLift, Circuit.size]; omega

theorem bare_counts (A B : Circuit) (p : GateOp → Bool) :
    (bareLift A B).gates.countP (fun g => p g.op) =
    A.gates.countP (fun g => p g.op) + B.gates.countP (fun g => p g.op) +
      (p .not).toNat := by
  simp only [bareLift, List.countP_append, List.countP_map, List.countP_singleton,
    Function.comp_def, relGate, notU, Bool.toNat]
  cases p .not <;> simp
  omega

theorem bare_ok (A B : Circuit) (ha : FanInTwo A) (hb : FanInTwo B) :
    FanInTwo (bareLift A B) := by
  intro g hg
  simp only [bareLift, List.mem_append, List.mem_singleton, List.mem_map] at hg
  rcases hg with (⟨e, he, rfl⟩ | rfl) | ⟨e, he, rfl⟩
  · exact ⟨(ha e he).1, by simpa [relGate] using (ha e he).2⟩
  · simp [notU]
  · exact ⟨(hb e he).1, by simpa [relGate] using (hb e he).2⟩

theorem bare_initial (x : Fin 9 → Bool) :
    Rel 8 9 skipU (List.ofFn (x ∘ skipU)) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h : i < 8
  · simp only [wmap, dite_eq_left h]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using (skipU ⟨i,h⟩).isLt),
      List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h)]
    simp only [List.getElem_ofFn]
    rfl
  · simp only [wmap, dite_eq_right h]
    rw [List.getD_eq_default _ _ (by simp),
      List.getD_eq_default _ _ (by simp; omega)]

theorem bare_eval (A B : Circuit) (x : Fin 9 → Bool) :
    (bareLift A B).eval (List.ofFn x) =
      B.eval (A.wires (List.ofFn (x ∘ skipU)) ++ [! x 4]) := by
  let W := A.wires (List.ofFn (x ∘ skipU))
  let E := (A.gates.map (relGate 8 9 skipU)).foldl step (List.ofFn x)
  have hpre : Rel 8 9 skipU W E := rel_fold _ _ _ A.gates _ _ (bare_initial x)
  have hn : E.getD 4 false = x 4 := by
    unfold E
    rw [run_keep _ _ _ (by simp)]
    rfl
  have hm : step E notU = E ++ [! x 4] := by
    change E ++ [! E.getD 4 false] = _
    rw [hn]
  have hs := (rel_fold _ _ _ B.gates _ _ (rel_snoc _ _ _ _ _ (! x 4) hpre)).2.2 B.output
  change ((_ ++ [notU] ++ _).foldl step (List.ofFn x)).getD _ false = _
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  change ((B.gates.map _).foldl step (step E notU)).getD _ false = _
  rw [hm]
  exact hs

theorem bare_lifting (A B : Circuit) (j : ℕ) (F : (Fin 8 → Bool) → Bool)
    (hA : FanInTwo A) (hB : FanInTwo B)
    (hnatural : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      B.eval (W ++ [W.getD j false]) = F z)
    (hforced : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      B.eval (W ++ [false]) = (F z || z 0 || z 3))
    (hdormant : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      W.getD j false = false → B.eval (W ++ [true]) = B.eval (W ++ [false])) :
    ∃ C : Circuit, FanInTwo C ∧ C.size = A.size + B.size + 1 ∧
      (∀ p : GateOp → Bool, C.gates.countP (fun g => p g.op) =
        A.gates.countP (fun g => p g.op) + B.gates.countP (fun g => p g.op) +
        (p .not).toNat) ∧
      ∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x) =
          (F (fun i => x ⟨if i.val < 4 then i.val else i.val + 1, by split <;> omega⟩) ||
          (x 4 && (x 0 || x 3))) := by
  refine ⟨bareLift A B, bare_ok A B hA hB, bare_size A B, bare_counts A B, ?_⟩
  intro x
  rw [bare_eval]
  let z := x ∘ skipU
  let W := A.wires (List.ofFn z)
  change B.eval (W ++ [! x 4]) = (F z || (x 4 && (x 0 || x 3)))
  have hnat : B.eval (W ++ [W.getD j false]) = F z := hnatural z
  cases h : x 4
  · simp only [Bool.not_false, Bool.false_and, Bool.or_false]
    cases hq : W.getD j false
    · rw [hdormant z hq]
      rwa [hq] at hnat
    · rwa [hq] at hnat
  · have h0 : z 0 = x 0 := rfl
    have h3 : z 3 = x 3 := rfl
    have hf : B.eval (W ++ [false]) = (F z || z 0 || z 3) := hforced z
    simpa only [Bool.not_true, Bool.true_and, Bool.or_assoc, h0, h3] using hf

theorem dormant_sensitivity (A B : Circuit) (j : ℕ) (F : (Fin 8 → Bool) → Bool)
    (p : GateOp → Bool) (hp : p .not = false) (k : ℕ)
    (hA : FanInTwo A) (hB : FanInTwo B)
    (hnatural : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      B.eval (W ++ [W.getD j false]) = F z)
    (hforced : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      B.eval (W ++ [false]) = (F z || z 0 || z 3))
    (hsmall : A.gates.countP (fun g => p g.op) + B.gates.countP (fun g => p g.op) < k)
    (hlower : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        (F (fun i => x ⟨if i.val < 4 then i.val else i.val + 1, by split <;> omega⟩) ||
        (x 4 && (x 0 || x 3)))) → k ≤ C.gates.countP (fun g => p g.op)) :
    ∃ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      W.getD j false = false ∧ B.eval (W ++ [true]) ≠ B.eval (W ++ [false]) := by
  by_contra hn
  have hd : ∀ z : Fin 8 → Bool, let W := A.wires (List.ofFn z)
      W.getD j false = false → B.eval (W ++ [true]) = B.eval (W ++ [false]) := by
    intro z
    dsimp only
    intro hq
    by_contra hne
    exact hn ⟨z, hq, hne⟩
  obtain ⟨C, hok, _, hcnt, hev⟩ := bare_lifting A B j F hA hB hnatural hforced hd
  have h := hlower C hok hev
  rw [hcnt p, hp] at h
  exact (Nat.not_le_of_lt hsmall) (by simpa using h)

end Pnp3304Lift


namespace BudgetAdapter

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Vertex := Fin 9
abbrev Edges := List (Vertex × Vertex)

def edges : Edges := [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)]

def edgeFun (es : Edges) (x : Vertex → Bool) : Bool :=
  es.any (fun edge => x edge.1 && x edge.2)

abbrev petersenF := edgeFun edges

def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

def F8 (x : Fin 8 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
  x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4

theorem graph_identity (x : Fin 9 → Bool) :
    (F8 (x ∘ Pnp3304Lift.skipU) || (x 4 && (x 0 || x 3))) = petersenF x := by
  simp only [F8, Function.comp_apply, petersenF, edgeFun, edges,
    List.any_cons, List.any_nil, Bool.or_false, Bool.and_or_distrib_left]
  change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 1 && x 6 ||
    x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5 ||
    (x 4 && x 0 || x 4 && x 3)) = _
  ac_rfl

private noncomputable def mark (g : Gate) : Bool := GateOp.rec false false true (fun _ => false) false g.op

theorem counted (gs : List Gate) : nonNotCount gs + gs.countP mark = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    have em : mark g = isNotGate g.op := by
      cases g with
      | mk op wires => cases op <;> rfl
    rw [em]
    cases h : isNotGate g.op <;> simp <;> omega

theorem postedBudget
    (petersen_binary_lower : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Vertex → Bool, C.eval (List.ofFn x) = petersenF x) → 13 ≤ nonNotCount C.gates) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         have x8 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x8 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x8);         have x9 : (Fin (8 : ℕ) → Bool) → Bool := fun (x9 : Fin (8 : ℕ) → Bool) => (x8 x9).getD x4 Bool.false;         (∀ (x10 : Fin (8 : ℕ) → Bool), x3.eval (x8 x10 ++ [x9 x10]) = x1 x10) → (∀ (x11 : Fin (8 : ℕ) → Bool), x3.eval (x8 x11 ++ [Bool.false]) = (x1 x11 || x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ)))) → (12 : ℕ) + List.countP (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x13 : ℕ) => Bool.false) Bool.false x12.op) x2.gates + List.countP (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x13 : ℕ) => Bool.false) Bool.false x12.op) x3.gates ≤ x2.size + x3.size := by
  intro F A B j hA hB _ W q hn hf
  obtain ⟨C, hok, _, hcount, hev⟩ :=
    Pnp3304Lift.costed_lifting A B j F hA hB hn hf
  have lower := petersen_binary_lower C hok (fun x => (hev x).trans (graph_identity x))
  have hc := hcount (fun op => !(isNotGate op))
  change nonNotCount C.gates = nonNotCount A.gates + nonNotCount B.gates + 0 + 1 at hc
  have h1 := counted A.gates
  have h2 := counted B.gates
  change 12 + A.gates.countP mark + B.gates.countP mark ≤ A.gates.length + B.gates.length
  omega

theorem postedBareBudget
    (petersen_binary_lower : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Vertex → Bool, C.eval (List.ofFn x) = petersenF x) → 13 ≤ nonNotCount C.gates) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         have x8 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x8 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x8);         have x9 : (Fin (8 : ℕ) → Bool) → Bool := fun (x9 : Fin (8 : ℕ) → Bool) => (x8 x9).getD x4 Bool.false;         (∀ (x10 : Fin (8 : ℕ) → Bool), x3.eval (x8 x10 ++ [x9 x10]) = x1 x10) → (∀ (x11 : Fin (8 : ℕ) → Bool), x3.eval (x8 x11 ++ [Bool.false]) = (x1 x11 || x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ)))) → (∀ (x12 : Fin (8 : ℕ) → Bool), x9 x12 = Bool.false → x3.eval (x8 x12 ++ [Bool.true]) = x3.eval (x8 x12 ++ [Bool.false])) → (13 : ℕ) + List.countP (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x14 : ℕ) => Bool.false) Bool.false x13.op) x2.gates + List.countP (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x14 : ℕ) => Bool.false) Bool.false x13.op) x3.gates ≤ x2.size + x3.size := by
  intro F A B j hA hB _ W q hn hf hd
  obtain ⟨C, hok, _, hcount, hev⟩ :=
    Pnp3304Lift.bare_lifting A B j F hA hB hn hf hd
  have lower := petersen_binary_lower C hok (fun x => (hev x).trans (graph_identity x))
  have hc := hcount (fun op => !(isNotGate op))
  change nonNotCount C.gates = nonNotCount A.gates + nonNotCount B.gates + 0 at hc
  have h1 := counted A.gates
  have h2 := counted B.gates
  change 13 + A.gates.countP mark + B.gates.countP mark ≤ A.gates.length + B.gates.length
  omega

end BudgetAdapter

