import BanachDensity1D.Theorems

/-!
# Named witnesses and definition tests

Checks of the definitions against small cases, and witnesses for the generator model.

**Admissible generators exist.** `fresh` outputs, in round `t`, the number
`∑_{i ≤ t} (|w i| + 1)`: it exceeds every input so far and strictly increases with `t`, so every
output is available on every input sequence (`fresh_admissible`). The requirement
`Generator.Admissible` is therefore satisfiable.

**The echo generator is not a generator of the model.** `echo` outputs the latest input. On every
full enumeration of an infinite `K` all its outputs lie in `K` and its output set is `K`, so
`δ_B(O, K) = 1` (`echo_out_mem`, `echo_almostAllIn`, `echo_outputDensity`). But its output is
never available (`echo_not_available`), so it is not admissible (`echo_not_admissible`); this is
the only clause of Theorem 6.1 it fails (`echo_not_witness_fixed_epsilon`). Before the
model required admissibility of every generator, `echo` satisfied the Lean statement of
Theorem 6.1, which has no availability clause; now every theorem quantifies over admissible
generators, and `echo` is excluded.
-/

namespace BanachDensity1D

open Set

/-! ## Small cases of the definitions -/

example (L M : Set ℤ) : layers [L, M] = [L \ M, M] := rfl

example (L : Set ℤ) : layers [L] = [L] := rfl

/-- The single-vertex tree is an admissible obstruction tree (Definition 3.3). -/
example (X : Set (Set ℤ)) (K : Set ℤ) : def_aot X K (LTree.leaf K) := ⟨rfl, trivial⟩

/-- The only root-to-leaf path of the single-vertex tree is `(K)`. -/
example (K : Set ℤ) : (LTree.leaf K).paths = {[K]} := rfl

/-- The partition with no cuts has one board, `ℤ`. -/
example (x : ℤ) : cutBoard ∅ x = univ := by simp [cutBoard]

/-- One layer, three points: `p((K), J) = ⌊3/2⌋/3 = 1/3`. -/
example : def_raw_pairing_score [univ] ({0, 1, 2} : Set ℤ) = 1 / 3 := by
  have h : ({0, 1, 2} : Set ℤ).ncard = 3 := by
    rw [Set.ncard_eq_toFinset_card']; rfl
  simp [def_raw_pairing_score, layers, h]

/-! ## The echo generator -/

/-- The generator that outputs the latest input. -/
def echo : Generator := fun ws => ws.getLastD 0

lemma echo_out (w : ℕ → ℤ) (t : ℕ) : echo.out w t = w t := CaptureAux.inputsUpTo_getLastD w t

/-- On a full enumeration of `K`, every output of `echo` lies in `K`. -/
lemma echo_out_mem {w : ℕ → ℤ} {K : Set ℤ} (hw : IsFullEnumeration w K) (t : ℕ) :
    echo.out w t ∈ K := by
  rw [echo_out, ← hw]; exact mem_range_self t

/-- On a full enumeration of `K`, all but finitely many outputs of `echo` (in fact all of them,
`echo_out_mem`) belong to `K`. -/
lemma echo_almostAllIn {w : ℕ → ℤ} {K : Set ℤ} (hw : IsFullEnumeration w K) :
    echo.AlmostAllIn w K := by
  have : {t | echo.out w t ∉ K} = ∅ := by
    ext t
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
    exact echo_out_mem hw t
  simp [Generator.AlmostAllIn, this]

/-- No output of `echo` is available. -/
lemma echo_not_available (w : ℕ → ℤ) (t : ℕ) : ¬ echo.Available w t := by
  intro h
  exact h.1 t le_rfl (echo_out w t).symm

/-- `echo` is not a generator of the model: its output is never available. -/
lemma echo_not_admissible : ¬ echo.Admissible := fun h => echo_not_available (fun _ => 0) 0 (h _ 0)

/-! ## An admissible generator -/

/-- Output, in round `t`, the sum of `|x| + 1` over all inputs `x` so far. -/
def fresh : Generator := fun ws => (ws.map fun x => |x| + 1).sum

lemma fresh_out (w : ℕ → ℤ) (t : ℕ) :
    fresh.out w t = ∑ i ∈ Finset.range (t + 1), (|w i| + 1) := by
  rw [Generator.out, inputsUpTo, fresh, List.map_ofFn, List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i => |w i| + 1) (t + 1)

lemma fresh_out_succ (w : ℕ → ℤ) (t : ℕ) :
    fresh.out w (t + 1) = fresh.out w t + (|w (t + 1)| + 1) := by
  rw [fresh_out, fresh_out, Finset.sum_range_succ]

lemma fresh_strictMono (w : ℕ → ℤ) : StrictMono (fresh.out w) :=
  strictMono_nat_of_lt_succ fun t => by
    rw [fresh_out_succ]; have := abs_nonneg (w (t + 1)); linarith

lemma fresh_input_lt (w : ℕ → ℤ) {i t : ℕ} (hi : i ≤ t) : w i < fresh.out w t := by
  rw [fresh_out]
  have h1 : |w i| + 1 ≤ ∑ j ∈ Finset.range (t + 1), (|w j| + 1) :=
    Finset.single_le_sum (f := fun j => |w j| + 1) (fun j _ => by positivity)
      (Finset.mem_range.2 (by omega))
  have h2 := le_abs_self (w i)
  linarith

/-- `fresh` is a generator of the model: on every input sequence every output is available. -/
lemma fresh_admissible : fresh.Admissible := fun w t =>
  ⟨fun i hi => (fresh_input_lt w hi).ne, fun s hs => (fresh_strictMono w hs).ne⟩

/-- `δ_B(K, K) = 1` for an infinite `K`: on every interval with at least one point of `K` the
ratio is `1`. -/
lemma def_banach_intro_self {K : Set ℤ} (hK : K.Infinite) : def_banach_intro K K = 1 := by
  have hne : ∀ n : ℕ, Nonempty {R : ℤ × ℤ // n ≤ (K ∩ Icc R.1 R.2).ncard} :=
    BasicAux.banach_inf_nonempty hK
  have hle : ∀ n : ℕ, (⨅ R : {R : ℤ × ℤ // n ≤ (K ∩ Icc R.1 R.2).ncard},
      ((K ∩ Icc R.1.1 R.1.2).ncard : ℝ) / (K ∩ Icc R.1.1 R.1.2).ncard) ≤ 1 := fun n => by
    obtain ⟨R⟩ := hne n
    refine (ciInf_le ⟨0, ?_⟩ R).trans (div_self_le_one _)
    rintro _ ⟨R', rfl⟩
    positivity
  have h1 : (⨅ R : {R : ℤ × ℤ // 1 ≤ (K ∩ Icc R.1 R.2).ncard},
      ((K ∩ Icc R.1.1 R.1.2).ncard : ℝ) / (K ∩ Icc R.1.1 R.1.2).ncard) = 1 := by
    have := hne 1
    refine le_antisymm (hle 1) (le_ciInf fun R => ?_)
    have : (0 : ℝ) < (K ∩ Icc R.1.1 R.1.2).ncard := by exact_mod_cast R.2
    rw [div_self this.ne']
  refine le_antisymm (ciSup_le hle) ?_
  rw [← h1]
  exact le_ciSup (f := fun n : ℕ => ⨅ R : {R : ℤ × ℤ // n ≤ (K ∩ Icc R.1 R.2).ncard},
      ((K ∩ Icc R.1.1 R.1.2).ncard : ℝ) / (K ∩ Icc R.1.1 R.1.2).ncard) ⟨1, by
        rintro _ ⟨n, rfl⟩; exact hle n⟩ 1

/-- On a full enumeration of an infinite `K`, the output set of `echo` is `K`, so
`δ_B(O, K) = 1`. -/
lemma echo_outputDensity {w : ℕ → ℤ} {K : Set ℤ} (hK : K.Infinite)
    (hw : IsFullEnumeration w K) : outputDensity (echo.outputSet w) K = 1 := by
  have hO : echo.outputSet w = K := by
    rw [Generator.outputSet, ← hw]
    congr 1
    funext t
    exact echo_out w t
  rw [outputDensity, hO, inter_self, def_banach_intro_self hK]

/-- `echo` is not a witness for the Lean statement of Theorem 6.1, and admissibility is the only
clause that excludes it: `echo` is not admissible, but for every class `X` and every `ε > 0` it
meets the rest of the statement (on every full enumeration of every `K ∈ X`, all but finitely
many outputs lie in `K` and `δ_B(O, K) = 1 ≥ (b(K) - ε)_+`, since `b(K) ≤ 1/2`). -/
lemma echo_not_witness_fixed_epsilon {X : Set (Set ℤ)} (hX : LangClass X) {ε : ℝ} (hε : 0 < ε) :
    ¬ echo.Admissible ∧ ∀ K ∈ X, ∀ w, IsFullEnumeration w K →
      echo.AlmostAllIn w K ∧ max (bK X K - ε) 0 ≤ outputDensity (echo.outputSet w) K := by
  refine ⟨echo_not_admissible, fun K hK w hw => ⟨echo_almostAllIn hw, ?_⟩⟩
  have hKi : K.Infinite := hX.infinite K hK
  rw [echo_outputDensity hKi hw]
  have hb := (ChainsAux.bK_tendsto (X := X) hKi).2.2
  exact max_le (by linarith) (by norm_num)

end BanachDensity1D
