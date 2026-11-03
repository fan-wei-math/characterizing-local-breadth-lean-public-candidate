import BanachDensityHD.Characterization

namespace BanachDensityHD.ExactStatements
open Set
open scoped Classical

/-- Retain an occurrence path exactly when every vertex passes a hereditary
pointwise test, then map its data. All retained continuations are kept. -/
noncomputable def treeMap {d : ℕ} (T : DTree d) (f : Deco d → Deco d)
    (Good : Deco d → Prop) (hr : Good T.root) : DTree d :=
  .mk (List.map f '' {p | p ∈ T.paths ∧ ∀ v ∈ p, Good v}) (f T.root)
    ⟨[T.root], ⟨TreesAux.dtree_root_mem T, by simpa using hr⟩, rfl⟩
    (by
      rintro p ⟨q, ⟨hq, _⟩, rfl⟩
      obtain ⟨v, l, rfl⟩ := List.exists_cons_of_ne_nil (SuffAux.paths_ne hq)
      have hv : v = T.root := by simpa using TreesAux.dtree_head T _ hq
      simp [hv])
    (by
      rintro p ⟨q, ⟨hq, hg⟩, rfl⟩ n hn
      refine ⟨q.take n, ⟨TreesAux.dtree_prefix T q hq n hn,
        fun v hv => hg v (List.mem_of_mem_take hv)⟩, ?_⟩
      exact List.map_take)
    (((TreesAux.dtree_countable T).mono (fun _ h => h.1)).image _)

lemma treeMap_path {d : ℕ} (T : DTree d) (f : Deco d → Deco d)
    (Good : Deco d → Prop) (hr : Good T.root) {p : List (Deco d)}
    (hp : p ∈ T.paths) (hg : ∀ v ∈ p, Good v) :
    p.map f ∈ (treeMap T f Good hr).paths := ⟨p, ⟨hp, hg⟩, rfl⟩

lemma map_edge {α β : Type} (f : α → β) {q : List α} {p : List β} {v w : β}
    (he : q.map f = p ++ [v, w]) :
    ∃ l a b, q = l ++ [a, b] ∧ l.map f = p ∧ f a = v ∧ f b = w := by
  obtain ⟨l, t, rfl, hl, ht⟩ := List.map_eq_append_iff.1 he
  obtain ⟨a, t', rfl, ha, ht'⟩ := List.map_eq_cons_iff.1 ht
  obtain ⟨b, rfl, hb⟩ := List.map_eq_singleton_iff.1 ht'
  exact ⟨l, a, b, rfl, hl, ha, hb⟩

/-- A schedule-independent broad copy certificate. -/
def BroadCertificate {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ)
    (Q : Deco d → ℝ) (K : Set (Pt d)) (k : ℕ) (T : DTree d) : Prop :=
  T.root.L = K ∧ T.root.k = k ∧
  (∀ p ∈ T.paths, ∀ v ∈ p, v.L ∈ X ∧ ↑v.P ⊆ v.L ∧ 1 ≤ v.s ∧ 0 ≤ v.a ∧ 1 ≤ v.k) ∧
  (∀ p v w, p ++ [v, w] ∈ T.paths → w.L ⊆ v.L ∧ v.a < w.a) ∧
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []), ∀ M ∈ X, ∀ n, 1 ≤ n →
      ↑(p.getLast hp).P ⊆ M → M ⊆ (p.getLast hp).L →
      ∃ w : Deco d, w.L = M ∧ w.k = n ∧ p ++ [w] ∈ T.paths) ∧
  (∀ p ∈ T.paths, ∀ (hp : p ≠ []),
      GeomFeasible h (pathFn Deco.L p hp) (pathFn Q p hp)
        (pathFn Deco.s p hp) (p.getLast hp).a)

lemma geomFeasible_map {d : ℕ} (h : ℕ → ℝ) (f : Deco d → Deco d)
    (Q : Deco d → ℝ) (p : List (Deco d)) (hp : p ≠ [])
    (hm : p.map f ≠ [])
    (hf : GeomFeasible h (pathFn (fun v => (f v).L) p hp)
      (pathFn (fun v => Q (f v)) p hp) (pathFn (fun v => (f v).s) p hp)
      (f (p.getLast hp)).a) :
    GeomFeasible h (pathFn Deco.L (p.map f) hm) (pathFn Q (p.map f) hm)
      (pathFn Deco.s (p.map f) hm) ((p.map f).getLast hm).a := by
  apply CharAux.geom_transport h (by simp : p.length - 1 = (p.map f).length - 1)
    (Ls := pathFn (fun v => (f v).L) p hp)
    (qs := pathFn (fun v => Q (f v)) p hp)
    (ss := pathFn (fun v => (f v).s) p hp)
  · intro i; simp [pathFn, List.get_eq_getElem]
  · intro i; simp [pathFn, List.get_eq_getElem]
  · intro i; simp [pathFn, List.get_eq_getElem]
  · simpa using hf

/-- Map a complete broad certificate; the child lifting condition is universal
in the desired new copy, so no required copy is lost by the path restriction. -/
theorem broadCertificate_map {d : ℕ} {X : Set (Set (Pt d))} {h g : ℕ → ℝ}
    {Q Q' : Deco d → ℝ} {K : Set (Pt d)} {k j : ℕ} {T : DTree d}
    (ht : BroadCertificate X h Q K k T) (f : Deco d → Deco d) (Good : Deco d → Prop)
    (hr : Good T.root) (hroot : (f T.root).k = j)
    (hL : ∀ v, (f v).L = v.L) (hP : ∀ v, (f v).P = v.P)
    (ha : ∀ v, (f v).a = v.a)
    (hv : ∀ v, Good v → 1 ≤ v.s → 1 ≤ v.k → 1 ≤ (f v).s ∧ 1 ≤ (f v).k)
    (hchild : ∀ n, 1 ≤ n → ∃ m, 1 ≤ m ∧ ∀ v, v.k = m → Good v ∧ (f v).k = n)
    (hg : ∀ p (hp : p ≠ []), p ∈ T.paths → (∀ v ∈ p, Good v) →
      GeomFeasible h (pathFn Deco.L p hp) (pathFn Q p hp) (pathFn Deco.s p hp)
        (p.getLast hp).a →
      GeomFeasible g (pathFn (fun v => (f v).L) p hp)
        (pathFn (fun v => Q' (f v)) p hp) (pathFn (fun v => (f v).s) p hp)
        (f (p.getLast hp)).a) :
    BroadCertificate X g Q' K j (treeMap T f Good hr) := by
  obtain ⟨htr, htk, htv, hte, htc, htg⟩ := ht
  refine ⟨(hL _).trans htr, hroot, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨q, ⟨hq, hgood⟩, rfl⟩ v hvp
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hvp
    have h := htv q hq w hw
    exact ⟨by simpa [hL] using h.1, by simpa [hL, hP] using h.2.1,
      (hv w (hgood w hw) h.2.2.1 h.2.2.2.2).1, by simpa [ha] using h.2.2.2.1,
      (hv w (hgood w hw) h.2.2.1 h.2.2.2.2).2⟩
  · rintro p v w ⟨q, ⟨hq, hgq⟩, heq⟩
    obtain ⟨l, a, b, rfl, hl, rfl, rfl⟩ := map_edge f heq
    simpa [hL, ha] using hte l a b hq
  · rintro p ⟨q, ⟨hq, hgood⟩, rfl⟩ hne M hM n hn hPM hML
    have hqne := SuffAux.paths_ne hq
    obtain ⟨m, hm, hmf⟩ := hchild n hn
    have hlast : (q.map f).getLast hne = f (q.getLast hqne) := List.getLast_map hne
    obtain ⟨w, hwL, hwk, hwq⟩ := htc q hq hqne M hM m hm
      (by simpa [hlast, hP] using hPM) (by simpa [hlast, hL] using hML)
    refine ⟨f w, (hL w).trans hwL, (hmf w hwk).2, ?_⟩
    have hgood' : ∀ v ∈ q ++ [w], Good v := by
      intro v hmem
      rcases List.mem_append.1 hmem with hmem | hmem
      · exact hgood v hmem
      · rw [List.mem_singleton.1 hmem]; exact (hmf w hwk).1
    simpa using treeMap_path T f Good hr hwq hgood'
  · rintro p ⟨q, ⟨hq, hgood⟩, rfl⟩ hne
    exact geomFeasible_map g f Q' q (SuffAux.paths_ne hq) hne
      (hg q (SuffAux.paths_ne hq) hq hgood (htg q hq (SuffAux.paths_ne hq)))

end BanachDensityHD.ExactStatements
