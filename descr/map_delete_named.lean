namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! The named keys of `map_update/5` deleting a key: every pair gets the absent field. -/

/-- The final fold of `map_update_project_pair/5` for a deletion: pairs whose old type has values and optional ones
both give the absent field. -/
theorem del_fold (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (a : String)
    (Q' : List Term) (hQ : MQOk E den Q') (kQ : KeepsQ (LitA E a) Q')
    (acc : List Term) (ha : UpdQ E a absF Bool.true acc) :
    ∃ Qf, Erlang.lists.«foldl/3» (D (n + 1))
        (.function "Elixir.Module.Types.Descr" "-map_update_project_pair/5-fun-0-" 2 #[absF])
        (Term.list acc) (Term.list Q') = .ok (Term.list Qf) ∧ UpdQ E a absF Bool.true Qf ∧
      ∀ u, WithF E den absF Qf u ↔
        WithF E den absF acc u ∨ (∃ x, MInPairs E den Q' (some x) u) ∨ MInPairs E den Q' none u := by
  obtain ⟨r, ⟨Qf, rfl, uQ, sA⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr"
    "-map_update_project_pair/5-fun-0-" #[absF]
    (fun pre r => ∃ Qf, r = Term.list Qf ∧ UpdQ E a absF Bool.true Qf ∧
      ∀ u, WithF E den absF Qf u ↔
        WithF E den absF acc u ∨ (∃ x, MInPairs E den pre (some x) u) ∨ MInPairs E den pre none u) Q'
    (fun pre q r mq ⟨Qf, er, uQ, sA⟩ => by
      subst er
      obtain ⟨f, b, rfl, ⟨t, o, rfl, ht⟩, fb, nb⟩ := hQ q mq
      obtain ⟨f', b', e', ob⟩ := kQ _ mq
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'
      obtain ⟨-, rfl⟩ := e'
      obtain ⟨eb, re, se⟩ := ef.empty1 (m := n) hn ht
      let Q₁ := (if o then [Term.tuple #[absF, b]] else []) ++
        ((if eb then [] else [Term.tuple #[absF, b]]) ++ Qf)
      refine ⟨Term.list Q₁, ⟨Q₁, rfl, fun q' mq' => ?_, fun u => ?_⟩, ?_⟩
      · simp only [Q₁, List.mem_append] at mq'
        rcases mq' with mq' | mq' | mq'
        · cases o
          · simp at mq'
          · simp at mq'; subst mq'; exact ⟨absF, b, rfl, Or.inl rfl, fb, ob⟩
        · cases eb
          · simp at mq'; subst mq'; exact ⟨_, b, rfl, Or.inl rfl, fb, ob⟩
          · simp at mq'
        · exact uQ q' mq'
      · have pinS : ∀ x, MInPairs E den [.tuple #[.tuple #[t, boolAtom o], b]] (some x) u ↔
            den t x ∧ denMF E den b u = Bool.true := fun x => by
          simp only [MInPairs, List.mem_singleton, exists_eq_left, mpairIn_iff, fieldSem_mk]; simp
        have pinN : MInPairs E den [.tuple #[.tuple #[t, boolAtom o], b]] none u ↔
            o = Bool.true ∧ denMF E den b u = Bool.true := by
          simp only [MInPairs, List.mem_singleton, exists_eq_left, mpairIn_iff, fieldSem_mk]; simp
        have mid : WithF E den absF (if eb then [] else [Term.tuple #[absF, b]]) u ↔
            ∃ x, den t x ∧ denMF E den b u = Bool.true := by
          cases eb
          · simp only [Bool.false_eq_true, ↓reduceIte, withF_single]
            obtain ⟨x, hx⟩ : ∃ x, den t x := Classical.byContradiction fun h => by
              have := se.mpr fun v hv => h ⟨v, hv⟩
              cases this
            exact ⟨fun ⟨_, h⟩ => ⟨x, hx, h⟩, fun ⟨_, _, h⟩ => ⟨trivial, h⟩⟩
          · simp only [↓reduceIte]
            exact ⟨fun h => absurd h withF_nil, fun ⟨x, hx, _⟩ => absurd hx (se.mp rfl x)⟩
        have first : WithF E den absF (if o then [Term.tuple #[absF, b]] else []) u ↔
            o = Bool.true ∧ denMF E den b u = Bool.true := by
          cases o
          · simp [withF_nil]
          · simp only [↓reduceIte, withF_single, true_and]
        simp only [Q₁, withF_append, sA, mInPairs_append, pinS, pinN, first, mid]
        constructor
        · rintro (h | ⟨x, h⟩ | h | ⟨x, h⟩ | h)
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inr (Or.inl ⟨x, Or.inr h⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨x, Or.inl h⟩)
          · exact Or.inr (Or.inr (Or.inl h))
        · rintro (h | ⟨x, h | h⟩ | h | h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, h⟩)))
          · exact Or.inr (Or.inl ⟨x, h⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
          · exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_project_pair/5-fun-0-/2».pure]
        cases o <;> cases eb <;>
          simp [Elixir.Module.Types.Descr.«-map_update_project_pair/5-fun-0-/3», re, Lynx.Term.isMember, boolAtom, Q₁, absF,
            Term.list])
    (Term.list acc) ⟨acc, rfl, ha, fun u => by simp [MInPairs]⟩
  exact ⟨Qf, run, uQ, sA⟩

/-- `map_update_project_pair/5` for a deletion removes the key from the maps of a pair minus negated pairs whose key
holds a value, and with `keep_absent?`, from those without the key. -/
theorem project_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (P : List Term)
    (hP : ∀ p ∈ P, MPairOk E p ∧ RestOk E den a p) {t : Term} {o : Bool} {rest : Term} (ht : E t)
    (hr : MField E rest) (orest : OField (LitA E a) rest) (nr : ∃ w, denMF E den rest w = Bool.true) (keep : Bool) :
    ∃ Q, Elixir.Module.Types.Descr.«map_update_project_pair/5» (D (n + 2)) (Term.list P) (.tuple #[t, boolAtom o]) rest
        absF (boolAtom keep) = .ok (Term.list Q) ∧ UpdQ E a absF Bool.true Q ∧
      ∀ u, WithF E den absF Q u ↔
        (∃ x, den t x ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p (some x) u) ∨
        (keep = Bool.true ∧ o = Bool.true ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p none u) := by
  have hP' : ∀ p ∈ P, MPairOk E p := fun p mp => (hP p mp).1
  have kP : KeepsQ (LitA E a) P := fun p mp => by
    obtain ⟨⟨f, b, e, -, fb⟩, f', k', ntag, nl, e', -, -, na, -⟩ := hP p mp
    subst e'
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨_, _, rfl, oField_litA fb na⟩
  have hA : FieldValue E absF := ⟨.map [], Bool.true, rfl, ef.none⟩
  obtain ⟨b₀, rb₀, sb₀⟩ := field_empty_val (den := den) ef (m := n + 2) (by omega) hA
  have b₀f : b₀ = Bool.false := by
    cases b₀
    · rfl
    · exact absurd ((delField_sem ef none).mpr rfl) (sb₀.mp rfl none)
  subst b₀f
  obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 2) (by omega) ht
  obtain ⟨s₁, rs₁, ss₁⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' (field := .tuple #[t, .atom "false"])
    ⟨t, Bool.false, rfl, ht⟩
  obtain ⟨s₂, rs₂, ss₂⟩ := mkeeps_snd (den := den) ef (m := n + 1) (by omega) P hP' hA
  -- The shortcuts: the full rest from a present key, and from an absent one.
  let s₁₇ := !e && s₁
  let s₂₇ := keep && o && s₂
  let t₂ := if s₁₇ then Term.map [] else t
  let o₂ := if s₂₇ then Bool.false else (keep && o)
  let pairs₁ := (if s₂₇ then [Term.tuple #[absF, rest]] else []) ++
    (if s₁₇ then [Term.tuple #[absF, rest]] else [])
  have ht₂ : E t₂ := by simp only [t₂]; split; exact ef.none; exact ht
  obtain ⟨fe, rfe, sfe⟩ := field_empty_val (den := den) ef (m := n + 2) (by omega) (⟨t₂, o₂, rfl, ht₂⟩ : FieldValue E _)
  obtain ⟨Q', rQ', qQ', kQ', fQ', sQ'⟩ := mproject_pairs ef hn P hP' ⟨t₂, o₂, rfl, ht₂⟩ hr nr
  have up₁ : UpdQ E a absF Bool.true pairs₁ := by
    intro q mq
    simp only [pairs₁, List.mem_append] at mq
    rcases mq with mq | mq
    · by_cases h : s₂₇
      · rw [if_pos h] at mq; rw [List.mem_singleton] at mq; subst mq
        exact ⟨absF, rest, rfl, Or.inl rfl, hr, orest⟩
      · rw [if_neg h] at mq; simp at mq
    · by_cases h : s₁₇
      · rw [if_pos h] at mq; rw [List.mem_singleton] at mq; subst mq
        exact ⟨_, rest, rfl, Or.inl rfl, hr, orest⟩
      · rw [if_neg h] at mq; simp at mq
  obtain ⟨Qf, rQf, uQf, sAf⟩ := del_fold ef (n := n + 1) (by omega) a Q' qQ' (kQ' _ orest kP) pairs₁ up₁
  have nonx : ∀ x, ¬den (.map []) x := fun x h => (none_field (den := den) ef).2 (some x)
    (by rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk]; exact Or.inr ⟨x, rfl, h⟩)
  have sem₁ : ∀ u, WithF E den absF pairs₁ u ↔ (s₂₇ = Bool.true ∨ s₁₇ = Bool.true) ∧
      denMF E den rest u = Bool.true := fun u => by
    simp only [pairs₁, withF_append]
    by_cases h₂ : s₂₇ <;> by_cases h₁ : s₁₇ <;> simp [h₁, h₂, withF_single, withF_nil]
  have f₂ : ∀ y, FieldSem den (.tuple #[t₂, boolAtom o₂]) y ↔
      (∃ x, y = some x ∧ s₁₇ = Bool.false ∧ den t x) ∨ (y = none ∧ o₂ = Bool.true) := fun y => by
    rw [fieldSem_mk]
    by_cases h : s₁₇
    · simp only [t₂, h, ↓reduceIte]
      constructor
      · rintro (⟨rfl, h'⟩ | ⟨x, rfl, hx⟩)
        · exact Or.inr ⟨rfl, h'⟩
        · exact absurd hx (nonx x)
      · rintro (⟨x, -, e, -⟩ | ⟨rfl, h'⟩)
        · cases e
        · exact Or.inl ⟨rfl, h'⟩
    · simp only [t₂, h, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (⟨rfl, h'⟩ | ⟨x, rfl, hx⟩)
        · exact Or.inr ⟨rfl, h'⟩
        · exact Or.inl ⟨x, rfl, by simpa using h, hx⟩
      · rintro (⟨x, rfl, -, hx⟩ | ⟨rfl, h'⟩)
        · exact Or.inr ⟨x, rfl, hx⟩
        · exact Or.inl ⟨rfl, h'⟩
  have short₁ : s₁₇ = Bool.true → ∃ x, den t x ∧ ∀ u, ∀ p ∈ P, ¬MPairIn E den p (some x) u := fun h => by
    simp only [s₁₇, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨o₀, h₀, out⟩ := ss₁.mp h.2
    obtain ⟨x, rfl, hx⟩ := (putField_sem o₀).mp h₀
    exact ⟨x, hx, fun u p mp ⟨f, nb, e, hf, _⟩ => out p mp f nb e hf⟩
  have short₂ : s₂₇ = Bool.true → keep = Bool.true ∧ o = Bool.true ∧ ∀ u, ∀ p ∈ P, ¬MPairIn E den p none u := by
    intro h
    simp only [s₂₇, Bool.and_eq_true] at h
    obtain ⟨o₀, h₀, out⟩ := ss₂.mp h.2
    rw [absF, delField_sem ef] at h₀
    subst h₀
    exact ⟨h.1.1, h.1.2, fun u p mp ⟨f, nb, e, hf, _⟩ => out p mp f nb e hf⟩
  have o₂e : o₂ = Bool.true ↔ s₂₇ = Bool.false ∧ keep = Bool.true ∧ o = Bool.true := by
    simp only [o₂]
    by_cases h : s₂₇
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, true_and]; try simpa using h
  -- The semantics, from the shortcuts and the pairs of the rest of the fields.
  have toR : ∀ u, ((s₂₇ = Bool.true ∨ s₁₇ = Bool.true) ∧ denMF E den rest u = Bool.true) ∨
      (∃ x, MInPairs E den Q' (some x) u) ∨ MInPairs E den Q' none u →
      (∃ x, den t x ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p (some x) u) ∨
      (keep = Bool.true ∧ o = Bool.true ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p none u) := by
    rintro u (⟨h | h, hr⟩ | ⟨x, hx⟩ | hx)
    · obtain ⟨hk, ho, out⟩ := short₂ h
      exact Or.inr ⟨hk, ho, hr, fun p mp => out u p mp⟩
    · obtain ⟨x, hx, out⟩ := short₁ h
      exact Or.inl ⟨x, hx, hr, fun p mp => out u p mp⟩
    · obtain ⟨hf, hr, out⟩ := (sQ' _ u).mp hx
      obtain ⟨x', e, -, hx'⟩ | ⟨e, -⟩ := (f₂ _).mp hf
      · obtain rfl : x = x' := Option.some.inj e
        exact Or.inl ⟨x, hx', hr, out⟩
      · cases e
    · obtain ⟨hf, hr, out⟩ := (sQ' _ u).mp hx
      obtain ⟨x, e, -⟩ | ⟨-, h⟩ := (f₂ _).mp hf
      · cases e
      · obtain ⟨-, hk, ho⟩ := o₂e.mp h
        exact Or.inr ⟨hk, ho, hr, out⟩
  have ofR : ∀ u, ((∃ x, den t x ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p (some x) u) ∨
      (keep = Bool.true ∧ o = Bool.true ∧ denMF E den rest u = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p none u)) →
      ((s₂₇ = Bool.true ∨ s₁₇ = Bool.true) ∧ denMF E den rest u = Bool.true) ∨
      (fe = Bool.false ∧ ((∃ x, MInPairs E den Q' (some x) u) ∨ MInPairs E den Q' none u)) := by
    rintro u (⟨x, hx, hr, out⟩ | ⟨hk, ho, hr, out⟩)
    · by_cases h : s₁₇
      · exact Or.inl ⟨Or.inr h, hr⟩
      · have hf := (f₂ _).mpr (Or.inl ⟨x, rfl, by simpa using h, hx⟩)
        refine Or.inr ⟨?_, Or.inl ⟨x, (sQ' _ u).mpr ⟨hf, hr, out⟩⟩⟩
        cases fe
        · rfl
        · exact absurd hf (sfe.mp rfl (some x))
    · by_cases h : s₂₇
      · exact Or.inl ⟨Or.inl h, hr⟩
      · have hf := (f₂ _).mpr (Or.inr ⟨rfl, o₂e.mpr ⟨by simpa using h, hk, ho⟩⟩)
        refine Or.inr ⟨?_, Or.inr ((sQ' _ u).mpr ⟨hf, hr, out⟩)⟩
        cases fe
        · rfl
        · exact absurd hf (sfe.mp rfl none)
  refine ⟨if fe then pairs₁ else Qf, ?_, ?_, fun u => ?_⟩
  · unfold Elixir.Module.Types.Descr.«map_update_project_pair/5»
    have rs₁ : Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (n + 2)) (Term.list P)
        (.tuple #[t, .atom "false"]) = .ok (boolAtom s₁) := rs₁
    have rs₂ : Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_snd?/2» (D (n + 2)) (Term.list P)
        absF = .ok (boolAtom s₂) := rs₂
    simp only [s₁₇, s₂₇, t₂, o₂, pairs₁, absF] at rfe rQ' rQf rs₂ rb₀
    clear ss₁ ss₂ sQ' sAf se sfe sb₀ uQf up₁ qQ' kQ' fQ' hP hP' kP sem₁ f₂ short₁ short₂ o₂e toR ofR
    cases fe <;> cases e <;> cases s₁ <;> cases keep <;> cases o <;> cases s₂ <;>
      simp only [Bool.not_false, Bool.not_true, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, boolAtom, s₁₇, s₂₇, t₂, o₂, pairs₁,
        List.cons_append, Term.list] at rfe rQ' rQf rs₁ rs₂ ⊢ <;>
      simp [rb₀, re, rs₁, rs₂, rfe, rQ', rQf, Lynx.Term.isMember, boolAtom, Lynx.Except.andAlso, absF, Term.list] <;>
      (rw [rb₀] at rfe; simp [boolAtom] at rfe)
  · cases fe
    · exact uQf
    · exact up₁
  · cases fe
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sAf, sem₁]
      refine ⟨toR u, fun h => ?_⟩
      rcases ofR u h with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · simp only [↓reduceIte]
      rw [sem₁]
      refine ⟨fun h => toR u (Or.inl h), fun h => ?_⟩
      rcases ofR u h with h | ⟨e, -⟩
      · exact h
      · cases e

/-- The operation deleting a key with `:keep` or `:reject`. -/
abbrev delOpK (keep : Bool) : Term := .tuple #[.tuple #[.atom "constant", absF], modeT keep]

/-- One line of the general clause of `map_update_named_key/5` deleting a key: the pairs of the line's maps whose key
holds a value, as maps with the key removed, and with `:keep`, of those without the key. -/
theorem line_pairs_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (keep : Bool) {tag : Term}
    {l : List (Term × Term)} {negs : List Term} (g : TagV E tag) (sl : FieldsV E l) (lits : ∀ N ∈ negs, MapLitV E N)
    (ne : ∃ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w) {acc : Term} (ha : FieldValue E acc) :
    ∃ (k : Int) (P : List Term) (acc' : Term) (Q : List Term),
      Elixir.Module.Types.Descr.«map_split_key_line/5» (D (n + 2)) tag (fieldsTerm l) (Term.list negs) (.atom a) acc =
        .ok (.tuple #[acc', fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)], Term.list P]) ∧
      Elixir.Module.Types.Descr.«map_update_prepare_pairs/4» (D (n + 2)) (Term.list P) (fieldAt tag l a)
        (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) (delOpK keep) = .ok (Term.list Q) ∧
      FieldValue E acc' ∧
      (∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨ LongM den (.tuple #[tag, fieldsTerm l, Term.list negs]) a o) ∧
      UpdQ E a absF Bool.true Q ∧
      ∀ w, WithF E den absF Q (eraseK a w) ↔
        (∃ x, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a (some x) w)) ∨
        (keep = Bool.true ∧ InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a none w)) := by
  obtain ⟨k, P, acc', run, hacc, sacc, hf, hb, rest, hP, sP⟩ := split_line ef hn a g sl lits ne ha
  obtain ⟨w₀, hw₀⟩ := ne
  have nr : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
    ⟨_, (rest _).mpr ((msem_at ef g l a w₀).mp (inMLine_iff.mp hw₀).1).2⟩
  have orest := oField_litA hb (a := a) (by simp [lookup_eraseKey])
  obtain ⟨t, o, ef', ht⟩ := hf
  obtain ⟨Q, rQ, uQ, sA⟩ := project_del ef hn a P hP ht hb orest nr keep
  have line : ∀ w o', InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) (setK a o' w) ↔
      FieldSem den (.tuple #[t, boolAtom o]) o' ∧
        denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) (eraseK a w) = Bool.true ∧
        ∀ p ∈ P, ¬MPairIn E den p o' (eraseK a w) := by
    intro w o'
    rw [inMLine_iff, msem_at ef g l a, ← ef', rest, eraseK_setK, and_assoc]
    simp only [setK, ite_true]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h p mp hp => ?_, fun h N mN hN => ?_⟩)
    · obtain ⟨N, mN, hN⟩ := (sP (setK a o' w)).mpr ⟨p, mp, by simpa [setK, eraseK_setK] using hp⟩
      exact h N mN (by simpa [setK] using hN)
    · obtain ⟨p, mp, hp⟩ := (sP (setK a o' w)).mp (by simpa [setK] using ⟨N, mN, hN⟩)
      exact h p mp (by simpa [setK, eraseK_setK] using hp)
  refine ⟨k, P, acc', Q, run, ?_, hacc, sacc, uQ, fun w => ?_⟩
  · rw [ef']
    cases keep
    · simpa [Elixir.Module.Types.Descr.«map_update_prepare_pairs/4», modeT, boolAtom, absF] using rQ
    · simpa [Elixir.Module.Types.Descr.«map_update_prepare_pairs/4», modeT, boolAtom, absF] using rQ
  · rw [sA]
    refine or_congr ⟨fun ⟨x, hx, hr, out⟩ => ⟨x, (line w (some x)).mpr ⟨?_, hr, out⟩⟩, fun ⟨x, hx⟩ => ?_⟩ ?_
    · rw [fieldSem_mk]; exact Or.inr ⟨x, rfl, hx⟩
    · obtain ⟨hf', hr, out⟩ := (line w (some x)).mp hx
      rw [fieldSem_mk] at hf'
      rcases hf' with ⟨h, -⟩ | ⟨x', e, hx'⟩
      · cases h
      · cases e; exact ⟨x, hx', hr, out⟩
    · rw [line, fieldSem_mk]
      constructor
      · rintro ⟨hk, ho, hr, out⟩; exact ⟨hk, Or.inl ⟨rfl, ho⟩, hr, out⟩
      · rintro ⟨hk, ⟨-, ho⟩ | ⟨x, e, -⟩, hr, out⟩
        · exact ⟨hk, ho, hr, out⟩
        · cases e

/-- The line fold of the general clause of `map_update_named_key/5` deleting a key. -/
theorem del_fold_lines (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (keep : Bool)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ (pr : List Term) (F : Term), Erlang.lists.«foldl/3» (D (n + 3))
        (.function "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-0-" 2 #[.atom a, delOpK keep])
        (.tuple #[.nil, .tuple #[.map [], .atom "false"]]) (Term.list lines) = .ok (.tuple #[Term.list pr, F]) ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) ∧
      UpdQ E a absF Bool.true pr ∧
      ∀ w, WithF E den absF pr (eraseK a w) ↔
        (∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L (setK a none w)) := by
  obtain ⟨r, ⟨pr, F, rfl, hF, sF, uQ, sA⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr"
    "-map_update_named_key/5-fun-0-" #[.atom a, delOpK keep]
    (fun pre r => ∃ (pr : List Term) (F : Term), r = .tuple #[Term.list pr, F] ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ pre, LongM den L a o) ∧
      UpdQ E a absF Bool.true pr ∧
      ∀ w, WithF E den absF pr (eraseK a w) ↔
        (∃ L ∈ pre, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ ∃ L ∈ pre, InMLine den L (setK a none w))) lines
    (fun pre L r mL ⟨pr, F, er, hF, sF, uQ, sA⟩ => by
      subst er
      obtain ⟨⟨tag, l, negs, rfl, g, sl, lits⟩, ne⟩ := hl L mL
      obtain ⟨k, P, acc', Q, rs, rp, hacc, sacc, uQ', sA'⟩ := line_pairs_del ef hn a keep g sl lits ne hF
      refine ⟨_, ⟨Q.reverse ++ pr, acc', rfl, hacc, fun o => ?_, fun q mq => ?_, fun w => ?_⟩, ?_⟩
      · rw [sacc, sF]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨L', mL', h⟩ | h)
          · exact ⟨L', Or.inl mL', h⟩
          · exact ⟨_, Or.inr rfl, h⟩
        · rintro ⟨L', mL' | rfl, h⟩
          · exact Or.inl ⟨L', mL', h⟩
          · exact Or.inr h
      · rcases List.mem_append.mp mq with mq | mq
        · exact uQ' q (List.mem_reverse.mp mq)
        · exact uQ q mq
      · have : WithF E den absF (Q.reverse ++ pr) (eraseK a w) ↔
            WithF E den absF Q (eraseK a w) ∨ WithF E den absF pr (eraseK a w) := by
          rw [withF_append]; simp [WithF]
        rw [this, sA', sA]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro ((⟨x, h⟩ | ⟨hk, h⟩) | (⟨L', mL', h⟩ | ⟨hk, L', mL', h⟩))
          · exact Or.inl ⟨_, Or.inr rfl, x, h⟩
          · exact Or.inr ⟨hk, _, Or.inr rfl, h⟩
          · exact Or.inl ⟨L', Or.inl mL', h⟩
          · exact Or.inr ⟨hk, L', Or.inl mL', h⟩
        · rintro (⟨L', mL' | rfl, h⟩ | ⟨hk, L', mL' | rfl, h⟩)
          · exact Or.inr (Or.inl ⟨L', mL', h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inr ⟨hk, L', mL', h⟩)
          · exact Or.inl (Or.inr ⟨hk, h⟩)
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_key/5-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-map_update_named_key/5-fun-0-/4», rs, rp, USort.rev2])
    (.tuple #[.nil, .tuple #[.map [], .atom "false"]])
    ⟨[], _, rfl, (none_field ef).1, fun o => by simp [(none_field (den := den) ef).2 o], by simp [UpdQ],
      fun w => by simp [withF_nil]⟩
  exact ⟨pr, F, run, hF, sF, uQ, sA⟩

theorem putAt_none (ef : EF nd E V den tl K) {a : String} {w : MW V} : ¬PutAt den (.map []) a w :=
  fun ⟨x, _, hx⟩ => ef.den_none x hx

/-- The end of the general clause of `map_update_named_key/5` deleting a key: the single group of rests gets the
absent field. -/
theorem del_tail (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (a : String) (keep : Bool)
    (pairs : List Term) (hp : UpdQ E a absF Bool.true pairs) :
    ∃ bdds, (∀ κ : Term → Except Exception Term, (do
        let p ← Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2» (D (m + 1)) (Term.list pairs)
          (delOpK keep)
        let groups ← Erlang.lists.«foldl/3» (D (m + 1))
          (.function "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[]) (.map []) p
        let l ← Erlang.maps.«to_list/1» groups
        let b ← Erlang.lists.«map/2» (D (m + 1)) (.function "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
          #[.atom a]) l
        κ b) = κ (Term.list bdds)) ∧
      (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        w (.atom a) = none ∧ WithF E den absF pairs (eraseK a w) := by
  have hp' : UpdQ E a (.tuple #[.map [], .atom "false"]) Bool.true pairs := fun q mq => by
    obtain ⟨f, b, rfl, hf, fb, ob⟩ := hp q mq
    exact ⟨f, b, rfl, Or.inr ⟨rfl, hf.elim id (·.2)⟩, fb, ob⟩
  have hk : ∀ q ∈ pairs, ∃ f b, q = .tuple #[f, b] ∧ UKey (.map []) f := fun q mq => by
    obtain ⟨f, b, rfl, hf, -⟩ := hp' q mq
    exact ⟨f, b, rfl, hf.elim Or.inl fun h => Or.inr h.2⟩
  obtain ⟨entries, rg, inv⟩ := group_fold (m + 1) pairs hk
  obtain ⟨bdds, rb, fb, sb⟩ := group_bdds ef hm a ef.none pairs hp' entries inv
  refine ⟨bdds, fun κ => ?_, fb, fun w => (sb w).trans ⟨fun h => h.elim (fun h' => absurd h'.1 (putAt_none ef)) id,
    Or.inr⟩⟩
  simp [Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2», rg, Erlang.maps.«to_list/1», rb]

/-- The general clause of `map_update_named_key/5` deleting a key, for `:keep` and `:reject`: the maps of the lines
whose key holds a value, without the key, and with `:keep`, those without the key. -/
theorem del_lines (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (keep : Bool)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (ow : Term) :
    ∃ (bdds : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines)
        (.atom a) (delOpK keep) (.atom "true") ow = .ok (.tuple #[Term.list bdds, F]) ∧ (∀ b ∈ bdds, MField E b) ∧
      FieldValue E F ∧ (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        w (.atom a) = none ∧ ((∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
          (keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L w)) := by
  unfold Elixir.Module.Types.Descr.«map_update_named_key/5»
  split
  · rename_i h; simp at h
  · rename_i h _; cases keep <;> simp [modeT, absF] at h
  rotate_left
  · rename_i h₁ h₂ _; exact absurd rfl h₂
  -- Both paths give the pairs of the lines and their old field.
  have tail : ∀ (pairs : List Term) (F : Term), UpdQ E a absF Bool.true pairs →
      FieldValue E F → (∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o) →
      (∀ w, WithF E den absF pairs (eraseK a w) ↔ (∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
        (keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L (setK a none w))) →
      ∃ bdds, (∀ κ : Term → Except Exception Term, (do
        let p ← Elixir.Module.Types.Descr.«map_update_maybe_apply_callback/2» (D (n + 3)) (Term.list pairs)
          (delOpK keep)
        let groups ← Erlang.lists.«foldl/3» (D (n + 3))
          (.function "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-1-" 2 #[]) (.map []) p
        let l ← Erlang.maps.«to_list/1» groups
        let b ← Erlang.lists.«map/2» (D (n + 3)) (.function "Elixir.Module.Types.Descr" "-map_update_named_key/5-fun-2-" 1
          #[.atom a]) l
        κ b) = κ (Term.list bdds)) ∧ (∀ b ∈ bdds, MField E b) ∧
      ∀ w, (∃ b ∈ bdds, denMF E den b w = Bool.true) ↔
        w (.atom a) = none ∧ ((∃ L ∈ lines, ∃ x, InMLine den L (setK a (some x) w)) ∨
          (keep = Bool.true ∧ ∃ L ∈ lines, InMLine den L w)) := by
    intro pairs F hp hF sF sA
    obtain ⟨bdds, rb, fb, sb⟩ := del_tail ef (m := n + 2) (by omega) a keep pairs hp
    refine ⟨bdds, rb, fb, fun w => (sb w).trans ?_⟩
    rw [sA]
    refine ⟨fun ⟨hn, h⟩ => ⟨hn, ?_⟩, fun ⟨hn, h⟩ => ⟨hn, ?_⟩⟩
    all_goals
      have e : setK a none w = w := by funext κ; by_cases h' : κ = .atom a <;> simp [setK, h', hn]
      first | (rw [e] at h; exact h) | (rw [e]; exact h)
  split
  · rename_i _ _ f heq
    -- One open line without negations: the shortcut.
    obtain ⟨L, rest, rfl⟩ : ∃ L rest, lines = L :: rest := by
      cases lines with
      | nil => simp [Term.list] at heq
      | cons L rest => exact ⟨L, rest, rfl⟩
    simp only [Term.list, Term.cons.injEq] at heq
    obtain ⟨rfl, hr⟩ := heq
    obtain rfl : rest = [] := by cases rest <;> simp_all [Term.list]
    obtain ⟨⟨tag, l, negs, eL, g, sl, lits⟩, ne⟩ := hl _ List.mem_cons_self
    obtain ⟨rfl, rfl, en⟩ := tuple3_inj eL
    obtain rfl : negs = [] := by
      cases negs with
      | nil => rfl
      | cons x xs => simp [Term.list] at en
    have ne : ∃ w, InMLine den (.tuple #[.atom "open", fieldsTerm l, Term.list []]) w := ne
    obtain ⟨k, rpop, -, rest', -⟩ := pop_pair (den := den) ef g sl a
    obtain ⟨k', P, acc', Q, rs, rp, -, -, uQ, sA⟩ := line_pairs_del ef (n := n + 1) (by omega) a keep g sl
      (by simp) ne (none_field ef).1
    have hP : k' = k ∧ P = [] := by
      simp only [Elixir.Module.Types.Descr.«map_split_key_line/5», rpop, Lynx.Except.ok_bind] at rs
      cases hfo : Elixir.Module.Types.Descr.«field_opt_union/3» (D (n + 1 + 2)) (fieldAt (.atom "open") l a)
          (.tuple #[.map [], .atom "false"]) (.map []) with
      | error err => rw [hfo] at rs; cases rs
      | ok c =>
        rw [hfo] at rs
        simp only [Lynx.Except.ok_bind, pure, Except.pure, Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq,
          List.cons.injEq, and_true] at rs
        obtain ⟨-, -, e₁, e₂⟩ := rs
        refine ⟨by simpa using e₁.symm, ?_⟩
        cases P with
        | nil => rfl
        | cons x xs => simp [Term.list] at e₂
    obtain ⟨rfl, rfl⟩ := hP
    obtain ⟨w₀, hw₀⟩ := ne
    have h₀ := (inMLine_iff (negs := []) .. |>.mp hw₀).1
    obtain ⟨bdds, rb, fb, sb⟩ := tail Q (fieldAt (.atom "open") l a) uQ (fieldAt_ok ef g sl a)
      (fun o => by
        rw [lit_values ef g a h₀ o]
        simp only [List.mem_singleton, exists_eq_left, LongM]
        exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (inMLine_iff (negs := [])).mpr ⟨hw, by simp⟩, wa⟩,
          fun ⟨w, hw, wa⟩ => ⟨w, ((inMLine_iff (negs := [])).mp hw).1, wa⟩⟩)
      (fun w => by simpa using sA w)
    refine ⟨bdds, _, ?_, fb, fieldAt_ok ef g sl a, fun o => ?_, sb⟩
    · simp only [rpop, rp, Lynx.Except.ok_bind]
      exact rb fun b => pure (.tuple #[b, fieldAt (.atom "open") l a])
    · rw [lit_values ef g a h₀ o]
      simp only [List.mem_singleton, exists_eq_left, LongM]
      exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, (inMLine_iff (negs := [])).mpr ⟨hw, by simp⟩, wa⟩,
        fun ⟨w, hw, wa⟩ => ⟨w, ((inMLine_iff (negs := [])).mp hw).1, wa⟩⟩
  · -- Otherwise, the fold over the lines.
    obtain ⟨pr, F, runF, hF, sF, uQ, sA⟩ := del_fold_lines ef hn a keep lines hl
    have revW : ∀ f u, WithF E den f pr.reverse u ↔ WithF E den f pr u := fun f u => by
      simp [WithF]
    obtain ⟨bdds, rb, fb, sb⟩ := tail pr.reverse F (fun q mq => uQ q (List.mem_reverse.mp mq)) hF sF
      (fun w => (revW _ _).trans (sA w))
    refine ⟨bdds, F, ?_, fb, hF, sF, sb⟩
    simp only [pure_bind, bind_assoc, runF, reverse1_list, Lynx.Except.ok_bind]
    exact rb fun b => pure (.tuple #[b, F])

/-- The maps of a deletion at a key, from the maps of a type: those whose key held a value, without the key, and
unless rejecting, those without the key. -/
def DelAt (M : MW V → Prop) (md : String) (a : String) (w : MW V) : Prop :=
  w (.atom a) = none ∧ ((∃ x, M (setK a (some x) w)) ∨ (md ≠ "reject" ∧ M w))

theorem setK_none_self {a : String} {w : MW V} (hn : w (.atom a) = none) : setK a none w = w := by
  funext κ; by_cases h' : κ = .atom a <;> simp [setK, h', hn]

/-- `map_update_named_key/5` deleting a key, asking for the old field: the maps `DelAt` gives, when building. -/
theorem del_key_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) {md : String} (hmd : Mode md) (a : String) (bd : Bool) :
    ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines)
        (.atom a) (cOp (.map []) Bool.true md) (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧
      FieldValue E F ∧ (bd = Bool.false → ba = []) ∧
      (bd = Bool.true → (∀ b ∈ ba, MField E b) ∧
        ∀ w, (∃ b ∈ ba, denMF E den b w = Bool.true) ↔ DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w) := by
  obtain ⟨F, rF, hF, -⟩ := mdnf_fetch ef hn a lines hl
  cases bd
  · exact ⟨[], F, by simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember,
      Term.list, rF], hF, fun _ => rfl, fun h => (by cases h)⟩
  rcases hmd with rfl | rfl | rfl
  · obtain ⟨ba, rba, fba, sba⟩ := put_lines ef hn a (leafPut_del ef a) lines hl
    refine ⟨ba, F, by simpa [boolAtom, cOp] using rba Bool.true F fun _ => rF, hF, fun h => (by cases h), fun _ =>
      ⟨fba, fun w => (sba w).trans ⟨fun ⟨hn, L, mL, o, hL⟩ => ⟨hn, ?_⟩, fun ⟨hn, h⟩ => ⟨hn, ?_⟩⟩⟩⟩
    · cases o with
      | none => rw [setK_none_self hn] at hL; exact Or.inr ⟨by simp, L, mL, hL⟩
      | some x => exact Or.inl ⟨x, L, mL, hL⟩
    · rcases h with ⟨x, L, mL, hL⟩ | ⟨-, L, mL, hL⟩
      · exact ⟨L, mL, some x, hL⟩
      · exact ⟨L, mL, none, by rw [setK_none_self hn]; exact hL⟩
  · rw [show cOp (.map []) Bool.true "keep" = delOpK Bool.true from rfl]
    obtain ⟨ba, F', rb, fba, hF', -, sba⟩ := del_lines ef hn a Bool.true lines hl (.atom "true")
    refine ⟨ba, F', by simpa [boolAtom] using rb, hF', fun h => (by cases h), fun _ => ⟨fba, fun w => (sba w).trans ?_⟩⟩
    unfold DelAt
    constructor
    · rintro ⟨hn, ⟨L, mL, x, h⟩ | ⟨hk, L, mL, h⟩⟩
      · exact ⟨hn, Or.inl ⟨x, L, mL, h⟩⟩
      · exact ⟨hn, Or.inr ⟨(by first | (cases hk; done) | simp), L, mL, h⟩⟩
    · rintro ⟨hn, ⟨x, L, mL, h⟩ | ⟨hk, L, mL, h⟩⟩
      · exact ⟨hn, Or.inl ⟨L, mL, x, h⟩⟩
      · exact ⟨hn, Or.inr ⟨(by first | rfl | exact absurd rfl hk), L, mL, h⟩⟩
  · rw [show cOp (.map []) Bool.true "reject" = delOpK Bool.false from rfl]
    obtain ⟨ba, F', rb, fba, hF', -, sba⟩ := del_lines ef hn a Bool.false lines hl (.atom "true")
    refine ⟨ba, F', by simpa [boolAtom] using rb, hF', fun h => (by cases h), fun _ => ⟨fba, fun w => (sba w).trans ?_⟩⟩
    unfold DelAt
    constructor
    · rintro ⟨hn, ⟨L, mL, x, h⟩ | ⟨hk, L, mL, h⟩⟩
      · exact ⟨hn, Or.inl ⟨x, L, mL, h⟩⟩
      · exact ⟨hn, Or.inr ⟨(by first | (cases hk; done) | simp), L, mL, h⟩⟩
    · rintro ⟨hn, ⟨x, L, mL, h⟩ | ⟨hk, L, mL, h⟩⟩
      · exact ⟨hn, Or.inl ⟨L, mL, x, h⟩⟩
      · exact ⟨hn, Or.inr ⟨(by first | rfl | exact absurd rfl hk), L, mL, h⟩⟩

/-- `map_update_named_keys/8` deleting the keys, asking for the old values, on a static type: the maps `DelAt` gives at
the keys, when building. -/
theorem named_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (req bd : Bool) :
    ∀ (ks : List String) (B : List Term) (f : Bool) (T Er : Term), E T →
      ∃ (B' : List Term) (f' : Bool) (T' Er' : Term),
        Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[T, Term.list B, Er, boolAtom f])
          (Term.list lines) (Term.list (ks.map Term.atom)) (cOp (.map []) Bool.true md) (boolAtom req) (.atom "true")
          (.atom "true") (boolAtom bd) = .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ E T' ∧
        (bd = Bool.false → B' = B) ∧
        (bd = Bool.true → (∀ b ∈ B, MField E b) → (∀ b ∈ B', MField E b) ∧
          ∀ w, (∃ b ∈ B', denMF E den b w = Bool.true) ↔ (∃ b ∈ B, denMF E den b w = Bool.true) ∨
            ∃ a ∈ ks, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w) := by
  have loop : ∀ (ks : List String) (B : List Term) (f : Bool) (T Er : Term), E T →
      ∃ (B' : List Term) (f' : Bool) (T' Er' : Term),
        Erlang.lists.«foldl_1/3» (D (n + 4))
          (.function "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, cOp (.map []) Bool.true md, boolAtom req, .atom "true", boolAtom bd, .atom "true",
              boolAtom (decide (md = "force"))])
          (.tuple #[T, Term.list B, Er, boolAtom f]) (Term.list (ks.map Term.atom)) =
          .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ E T' ∧
        (bd = Bool.false → B' = B) ∧
        (bd = Bool.true → (∀ b ∈ B, MField E b) → (∀ b ∈ B', MField E b) ∧
          ∀ w, (∃ b ∈ B', denMF E den b w = Bool.true) ↔ (∃ b ∈ B, denMF E den b w = Bool.true) ∨
            ∃ a ∈ ks, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w) := by
    intro ks
    induction ks with
    | nil =>
      intro B f T Er hT
      exact ⟨B, f, T, Er, by simp [Erlang.lists.«foldl_1/3», Term.list], hT, fun _ => rfl,
        fun _ fB => ⟨fB, fun w => by simp⟩⟩
    | cons a rest ih =>
      intro B f T Er hT
      obtain ⟨ba, F, rb, hF, bF, bT⟩ := del_key_sem ef (n := n) hn lines hl hmd a bd
      obtain ⟨t, o, rfl, ht⟩ := hF
      obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ht hT (m := n + 3) (by omega)
      -- One step of the fold: the maps of the key are added, and the old values stay a type.
      obtain ⟨f₁, T₁, Er₁, step, hT₁⟩ : ∃ (f₁ : Bool) (T₁ Er₁ : Term),
          (D (n + 4)).pure (.function "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, cOp (.map []) Bool.true md, boolAtom req, .atom "true", boolAtom bd, .atom "true",
              boolAtom (decide (md = "force"))]) #[.atom a, .tuple #[T, Term.list B, Er, boolAtom f]] =
            .ok (.tuple #[T₁, Term.list (ba ++ B), Er₁, boolAtom f₁]) ∧ E T₁ := by
        have rb' : Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3)) (Term.list lines) (.atom a)
            (cOp (.map []) Bool.true md) (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, .tuple #[t, boolAtom o]]) := rb
        simp only [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
          Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»]
        rw [rb']
        rcases hmd with rfl | rfl | rfl <;> cases e <;> cases o <;> cases req <;> cases f <;>
          simp [re, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2», ru, boolAtom, Lynx.Except.andAlso,
            Lynx.Except.orElse, Erlang.erlang.«not/1», append_list] <;>
          first
          | exact ⟨_, _, _, ⟨rfl, rfl, rfl, rfl⟩, hu⟩
          | exact ⟨_, _, _, ⟨rfl, rfl, rfl, rfl⟩, hT⟩
          | exact ⟨_, _, _, rfl, hu⟩
          | exact ⟨_, _, _, rfl, hT⟩
          | exact hu
          | exact hT
      obtain ⟨B', f', T', Er', r₁, hT', bF', bT'⟩ := ih (ba ++ B) f₁ T₁ Er₁ hT₁
      refine ⟨B', f', T', Er', ?_, hT', fun hb => ?_, fun hb fB => ?_⟩
      · rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only [Term.list, List.map] at r₁ ⊢
        simp [Term.list] at step
        simp [step, r₁]
      · rw [bF' hb, bF hb]; rfl
      · obtain ⟨fba, sba⟩ := bT hb
        obtain ⟨fB', sB'⟩ := bT' hb fun b mb => by
          rcases List.mem_append.mp mb with mb | mb
          · exact fba b mb
          · exact fB b mb
        refine ⟨fB', fun w => ?_⟩
        rw [sB']
        simp only [List.mem_append, List.mem_cons]
        constructor
        · rintro (⟨b, mb | mb, hb'⟩ | ⟨a', ma, h⟩)
          · exact Or.inr ⟨a, Or.inl rfl, (sba w).mp ⟨b, mb, hb'⟩⟩
          · exact Or.inl ⟨b, mb, hb'⟩
          · exact Or.inr ⟨a', Or.inr ma, h⟩
        · rintro (⟨b, mb, hb'⟩ | ⟨a', rfl | ma, h⟩)
          · exact Or.inl ⟨b, Or.inr mb, hb'⟩
          · obtain ⟨b, mb, hb'⟩ := (sba w).mpr h; exact Or.inl ⟨b, Or.inl mb, hb'⟩
          · exact Or.inr ⟨a', ma, h⟩
  intro ks B f T Er hT
  obtain ⟨B', f', T', Er', r₁, hT', bF', bT'⟩ := loop ks B f T Er hT
  refine ⟨B', f', T', Er', ?_, hT', bF', bT'⟩
  rcases hmd with rfl | rfl | rfl
  all_goals
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse, boolAtom]
    rcases ks with _ | ⟨k, t⟩
    · simp [Term.list, Erlang.lists.«foldl_1/3»] at r₁ ⊢
      simpa [boolAtom] using r₁
    · simp only [Term.list, List.map] at r₁ ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at r₁; simpa [boolAtom] using r₁

end

end Elixir.STTDescrProofsTest.Nest
