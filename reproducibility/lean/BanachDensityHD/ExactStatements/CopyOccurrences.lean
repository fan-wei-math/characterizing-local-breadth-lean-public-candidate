import BanachDensityHD.ExactStatements.TreeMap

namespace BanachDensityHD.ExactStatements
open Set
open scoped Classical

/-- A countable rooted occurrence tree in root-path normal form. An occurrence
is its whole address, not its last symbol or its language. Data depend on the
whole address. Infinite branches are allowed; only finite paths are tested. -/
structure CopyOccurrenceTree (ι : Type*) (d : ℕ) where
  paths : Set (List ι)
  root : ι
  root_mem : [root] ∈ paths
  head : ∀ p ∈ paths, p.head? = some root
  prefix_closed : ∀ p ∈ paths, ∀ n, 1 ≤ n → p.take n ∈ paths
  countable : paths.Countable
  language : List ι → Set (Pt d)
  protectedSet : List ι → Finset (Pt d)
  cutoff : List ι → ℝ
  radius : List ι → ℝ
  accuracy : List ι → ℕ

namespace CopyOccurrenceTree
variable {ι : Type*} {d : ℕ} (T : CopyOccurrenceTree ι d)

/-- Occurrence data, including its own accuracy index. -/
def data (p : List ι) : Deco d :=
  .mk (T.language p) (T.accuracy p) (T.protectedSet p) (T.cutoff p) (T.radius p)

/-- Literal prefix-indexed path data, with no quotient of vertex occurrences. -/
def along {β : Type*} (f : List ι → β) (p : List ι) : Fin (p.length - 1 + 1) → β :=
  fun i => f (p.take (i.val + 1))

/-- Definition 7.14 on occurrences. Every compatible copy must have
an actual child at this occurrence, including when other occurrences have the
same endpoint language. -/
def Protected (X : Set (Set (Pt d))) (h : ℕ → ℝ)
    (Q : Set (Pt d) → ℕ → ℝ) (K : Set (Pt d)) (k : ℕ) : Prop :=
  T.language [T.root] = K ∧ T.accuracy [T.root] = k ∧
  (∀ p ∈ T.paths, T.language p ∈ X ∧ ↑(T.protectedSet p) ⊆ T.language p ∧
      1 ≤ T.cutoff p ∧ 0 ≤ T.radius p ∧ 1 ≤ T.accuracy p) ∧
  (∀ p ∈ T.paths, ∀ i, p ++ [i] ∈ T.paths →
    T.language (p ++ [i]) ⊆ T.language p ∧ T.radius p < T.radius (p ++ [i])) ∧
  (∀ p ∈ T.paths, ∀ M ∈ X, ∀ n, 1 ≤ n →
    ↑(T.protectedSet p) ⊆ M → M ⊆ T.language p →
    ∃ i, p ++ [i] ∈ T.paths ∧ T.language (p ++ [i]) = M ∧ T.accuracy (p ++ [i]) = n) ∧
  (∀ p ∈ T.paths, GeomFeasible h (along T.language p)
    (fun i => Q (along T.language p i) (along T.accuracy p i))
    (along T.cutoff p) (T.radius p))

lemma nonempty {p : List ι} (hp : p ∈ T.paths) : p ≠ [] := by
  intro he
  have := T.head p hp
  simp [he] at this

/-- Map every root path to its sequence of occurrence data. Equal decorated
paths may merge; their continuations are united, never discarded. -/
noncomputable def encode : DTree d :=
  .mk (CharAux.pathG T.data '' T.paths) (T.data [T.root])
    ⟨[T.root], T.root_mem, by simp [CharAux.pathG]⟩
    (by
      rintro p ⟨l, hl, rfl⟩
      obtain ⟨v, t, rfl⟩ := List.exists_cons_of_ne_nil (T.nonempty hl)
      have hv : v = T.root := by simpa using T.head (v :: t) hl
      subst hv
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp [CharAux.pathG_length]),
        CharAux.pathG_getElem]
      simp)
    (by
      rintro p ⟨l, hl, rfl⟩ n hn
      exact ⟨l.take n, T.prefix_closed l hl n hn, (CharAux.pathG_take T.data l n).symm⟩)
    (T.countable.image _)

/-- Each encoded finite path comes from an entire occurrence path and vice versa. -/
theorem encode_paths (p : List (Deco d)) :
    p ∈ T.encode.paths ↔ ∃ l ∈ T.paths, CharAux.pathG T.data l = p := Iff.rfl

/-- The central representation bridge. It preserves every required child,
nonstrict edge, increasing radius, cutoff, and finite-path feasibility condition.
No injectivity of endpoint labels or decorated addresses is assumed. -/
theorem encode_protected {X : Set (Set (Pt d))} {h : ℕ → ℝ}
    {Q : Set (Pt d) → ℕ → ℝ} {K : Set (Pt d)} {k : ℕ} (hT : T.Protected X h Q K k) :
    BroadCertificate X h (fun v => Q v.L v.k) K k T.encode := by
  obtain ⟨hr, hk, hv, he, hc, hf⟩ := hT
  refine ⟨hr, hk, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨l, hl, rfl⟩ v hvp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvp
    rw [CharAux.pathG_getElem]
    have hi' := T.prefix_closed l hl (i + 1) (by omega)
    exact ⟨(hv _ hi').1, (hv _ hi').2.1, (hv _ hi').2.2.1, (hv _ hi').2.2.2.1, (hv _ hi').2.2.2.2⟩
  · rintro p v w ⟨l, hl, hpath⟩
    have hlen : l.length = p.length + 2 := by
      have := congrArg List.length hpath
      simp only [CharAux.pathG_length, List.length_append, List.length_cons, List.length_nil] at this
      omega
    have ev : v = T.data (l.take (p.length + 1)) := by
      have hx : v = (CharAux.pathG T.data l)[p.length]'(by rw [CharAux.pathG_length]; omega) := by
        simp [hpath]
      simpa only [CharAux.pathG_getElem] using hx
    have ew : w = T.data (l.take (p.length + 1 + 1)) := by
      have hx : w = (CharAux.pathG T.data l)[p.length + 1]'(by rw [CharAux.pathG_length]; omega) := by
        simp [hpath]
      simpa only [CharAux.pathG_getElem] using hx
    rw [ev, ew]
    have hpre := T.prefix_closed l hl (p.length + 1) (by omega)
    have hpre' := T.prefix_closed l hl (p.length + 1 + 1) (by omega)
    have hsn : l.take (p.length + 1 + 1) =
        l.take (p.length + 1) ++ [l[p.length + 1]'(by omega)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    simpa only [data, Deco.L, Deco.a, ← hsn] using
      he _ hpre (l[p.length + 1]'(by omega)) (hsn ▸ hpre')
  · rintro p ⟨l, hl, rfl⟩ hp M hM n hn hPM hML
    rw [CharAux.pathG_getLast] at hPM hML
    obtain ⟨i, hi, hLi, hki⟩ := hc l hl M hM n hn hPM hML
    refine ⟨T.data (l ++ [i]), hLi, hki, ?_⟩
    change CharAux.pathG T.data l ++ [T.data (l ++ [i])] ∈ CharAux.pathG T.data '' T.paths
    exact ⟨l ++ [i], hi, CharAux.pathG_snoc T.data l i⟩
  · rintro p ⟨l, hl, rfl⟩ hp
    rw [CharAux.pathG_getLast]
    refine CharAux.geom_transport h (by rw [CharAux.pathG_length]) ?_ ?_ ?_ (hf l hl)
    all_goals
      intro i
      simp only [pathFn, List.get_eq_getElem, CharAux.pathG_getElem, data, Deco.L, Deco.k, Deco.s, along, Fin.val_cast]

/-- View an encoded tree as an occurrence tree: the whole decorated root path is
its occurrence address. In particular, equal final data on different paths are
still different occurrences. -/
noncomputable def ofDTree (S : DTree d) : CopyOccurrenceTree (Deco d) d where
  paths := S.paths
  root := S.root
  root_mem := TreesAux.dtree_root_mem S
  head := TreesAux.dtree_head S
  prefix_closed := TreesAux.dtree_prefix S
  countable := TreesAux.dtree_countable S
  language p := (p.getLastD S.root).L
  protectedSet p := (p.getLastD S.root).P
  cutoff p := (p.getLastD S.root).s
  radius p := (p.getLastD S.root).a
  accuracy p := (p.getLastD S.root).k

/-- The reverse bridge uses paths as occurrences; it does not assert an
isomorphism with a paper tree that had duplicate identical child occurrences. -/
theorem ofDTree_protected {X : Set (Set (Pt d))} {h : ℕ → ℝ}
    {Q : Set (Pt d) → ℕ → ℝ} {K : Set (Pt d)} {k : ℕ} {S : DTree d}
    (hS : BroadCertificate X h (fun v => Q v.L v.k) K k S) : (ofDTree S).Protected X h Q K k := by
  obtain ⟨hr, hk, hv, he, hc, hf⟩ := hS
  have hne : ∀ p ∈ S.paths, p ≠ [] := fun p hp => (ofDTree S).nonempty hp
  have hlast : ∀ p (hp : p ∈ S.paths), p.getLastD S.root = p.getLast (hne p hp) :=
    fun p hp => CharAux.getLastD_eq_getLast _ _ (hne p hp)
  refine ⟨by simpa [ofDTree] using hr, by simpa [ofDTree] using hk, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hx := hv p hp (p.getLast (hne p hp)) (List.getLast_mem _)
    simpa only [ofDTree, hlast p hp] using hx
  · intro p hp i hi
    change p ∈ S.paths at hp
    change p ++ [i] ∈ S.paths at hi
    have hi' : p.dropLast ++ [p.getLast (hne p hp), i] ∈ S.paths := by
      have hi0 := hi
      rw [← List.dropLast_append_getLast (hne p hp)] at hi0
      simpa only [List.append_assoc, List.singleton_append] using hi0
    change ((p ++ [i]).getLastD S.root).L ⊆ (p.getLastD S.root).L ∧
      (p.getLastD S.root).a < ((p ++ [i]).getLastD S.root).a
    have hli : (p ++ [i]).getLastD S.root = i := by simp
    rw [hli, hlast p hp]
    exact he _ _ _ hi'
  · intro p hp M hM n hn hPM hML
    obtain ⟨w, hw, hwk, hwp⟩ := hc p hp (hne p hp) M hM n hn
      (by simpa only [ofDTree, hlast p hp] using hPM)
      (by simpa only [ofDTree, hlast p hp] using hML)
    exact ⟨w, hwp, by simpa [ofDTree] using hw, by simpa [ofDTree] using hwk⟩
  · intro p hp
    have hx := hf p hp (hne p hp)
    change GeomFeasible h _ _ _ (p.getLastD S.root).a
    rw [hlast p hp]
    refine CharAux.geom_transport h rfl ?_ ?_ ?_ hx
    all_goals
      intro i
      simp only [along, ofDTree, pathFn, List.get_eq_getElem, Fin.cast_refl]
      rw [CharAux.getLastD_take p S.root i.val (by
        have := i.isLt; have := List.length_pos_iff.mpr (hne p hp); omega)]
      rfl

end CopyOccurrenceTree

/-- Faithful existence equivalence, rather than a false bijection of vertices. -/
theorem copyOccurrenceTree_iff {d : ℕ} (X : Set (Set (Pt d))) (h : ℕ → ℝ)
    (Q : Set (Pt d) → ℕ → ℝ) (K : Set (Pt d)) (k : ℕ) :
    (∃ (ι : Type) (T : CopyOccurrenceTree ι d), T.Protected X h Q K k) ↔
    ∃ T : DTree d, BroadCertificate X h (fun v => Q v.L v.k) K k T := by
  constructor
  · rintro ⟨ι, T, hT⟩; exact ⟨T.encode, T.encode_protected hT⟩
  · rintro ⟨T, hT⟩; exact ⟨Deco d, CopyOccurrenceTree.ofDTree T, CopyOccurrenceTree.ofDTree_protected hT⟩
end BanachDensityHD.ExactStatements
