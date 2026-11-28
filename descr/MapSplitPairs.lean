module

public import Erlang.program
public import Levels

@[expose] public section

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Pairs of a field and a map type, as maps split at a key. -/
def MPairOk (E : Term → Prop) (p : Term) : Prop := ∃ f b, p = .tuple #[f, b] ∧ FieldValue E f ∧ MField E b

/-- Pairs whose rests have literals of a kind. -/
def KeepsQ (ok : Term → Prop) (Q : List Term) : Prop := ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ OField ok b

/-- Pairs whose fields allow some value at the key. -/
def FilledQ (den : Term → V → Prop) (Q : List Term) : Prop := ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ ∃ o, FieldSem den f o

/-- Differences of map types keep their literals. -/
theorem map_diff_keeps {ok : Term → Prop} {x y w : Term} (fx : MField E x) (fy : MField E y)
    (run : Elixir.Module.Types.Descr.«map_difference/2» x y = .ok w) (ox : OField ok x) (oy : OField ok y) :
    OField ok w := by
  rcases fy with ⟨k, rfl⟩ | wy
  · have e : Elixir.Module.Types.Descr.«map_difference/2» x (.tuple #[.integer k, .atom "open", .nil]) =
        .ok (.atom "bdd_bot") := by unfold Elixir.Module.Types.Descr.«map_difference/2»; rfl
    rw [e] at run; cases run; exact Or.inr Bdd.bot
  have ny := not_top_of_ok wy mlit_not
  have oy : Bdd ok y := oy.resolve_left fun ⟨k, e⟩ => ny _ e
  rcases fx with ⟨kt, rfl⟩ | wx
  · rcases wy.shape with rfl | rfl | ⟨k', a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · have e : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
          (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
        unfold Elixir.Module.Types.Descr.«map_difference/2»; simp [diff_leaf_top]
      rw [e] at run; cases run; exact Or.inr Bdd.bot
    · have e : Elixir.Module.Types.Descr.«map_difference/2» (.tuple #[.integer kt, .atom "open", .nil])
          (.atom "bdd_bot") = .ok (.tuple #[.integer kt, .atom "open", .nil]) := by
        unfold Elixir.Module.Types.Descr.«map_difference/2»; simp [diff_leaf_bot]
      rw [e] at run; cases run; exact ox
    all_goals
      obtain ⟨w', run', keep, -⟩ := neg_ok wy
      rw [map_difference_neg ny _ rfl, run'] at run
      cases run
      exact Or.inr (keep _ oy)
  · have ox : Bdd ok x := ox.resolve_left fun ⟨k, e⟩ => not_top_of_ok wx mlit_not _ e
    obtain ⟨w', run', keep, -⟩ := diff_ok wx wy
    rw [map_difference_bdd (not_top_of_ok wx mlit_not) ny, run'] at run
    cases run
    exact Or.inr (keep _ ox oy)

/-- A value at the key and the rest of a map in a pair. -/
def MPairIn (E : Term → Prop) (den : Term → V → Prop) (p : Term) (o : Option V) (w : MW V) : Prop :=
  ∃ f b, p = .tuple #[f, b] ∧ FieldSem den f o ∧ denMF E den b w = Bool.true

theorem mpairIn_iff {f b : Term} {o : Option V} {w : MW V} :
    MPairIn E den (.tuple #[f, b]) o w ↔ FieldSem den f o ∧ denMF E den b w = Bool.true := by
  constructor
  · rintro ⟨f', b', e, h₁, h₂⟩
    simp only [Term.tuple.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    exact ⟨h₁, h₂⟩
  · intro h; exact ⟨f, b, rfl, h⟩

theorem field_inter_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f g : Term} (hf : FieldValue E f)
    (hg : FieldValue E g) : ∃ h, FieldValue E h ∧ Elixir.Module.Types.Descr.«field_intersection/2» (D m) f g = .ok h ∧
      ∀ o, FieldSem den h o ↔ FieldSem den f o ∧ FieldSem den g o := by
  obtain ⟨t₁, o₁, rfl, h₁⟩ := hf
  obtain ⟨t₂, o₂, rfl, h₂⟩ := hg
  obtain ⟨c, hc, run, sem, -⟩ := ef.inter h₁ h₂
  refine ⟨.tuple #[c, boolAtom (o₁ && o₂)], ⟨c, _, rfl, hc⟩, ?_, fun o => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«field_intersection/2», run m hm]
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso]
  · rw [fieldSem_mk, fieldSem_mk, fieldSem_mk]
    cases o with
    | none => cases o₁ <;> cases o₂ <;> simp
    | some x => simp [sem x]

theorem field_diff_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f g : Term} (hf : FieldValue E f)
    (hg : FieldValue E g) : ∃ h, FieldValue E h ∧ Elixir.Module.Types.Descr.«field_difference/2» (D m) f g = .ok h ∧
      ∀ o, FieldSem den h o ↔ FieldSem den f o ∧ ¬FieldSem den g o := by
  obtain ⟨t₁, o₁, rfl, h₁⟩ := hf
  obtain ⟨t₂, o₂, rfl, h₂⟩ := hg
  obtain ⟨c, hc, run, sem, -⟩ := ef.diff h₁ h₂
  refine ⟨.tuple #[c, boolAtom (o₁ && !o₂)], ⟨c, _, rfl, hc⟩, ?_, fun o => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«field_difference/2», run m hm]
    cases o₁ <;> cases o₂ <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«not/1»]
  · rw [fieldSem_mk, fieldSem_mk, fieldSem_mk]
    cases o with
    | none => cases o₁ <;> cases o₂ <;> simp
    | some x => simp [sem x]

theorem field_empty_val (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f : Term} (hf : FieldValue E f) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«field_empty?/1» (D m) f = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ∀ o, ¬FieldSem den f o) := by
  obtain ⟨t, o, rfl, ht⟩ := hf
  exact field_empty1_val ef hm ht o

/-- The union of the tuple types of pairs. -/
theorem munion_pairs (P : List Term) (hP : ∀ p ∈ P, MPairOk E p) :
    ∃ u, MField E u ∧ (∀ w, denMF E den u w = Bool.true ↔ ∃ p ∈ P, ∃ f b, p = .tuple #[f, b] ∧ denMF E den b w = Bool.true) ∧
      ∀ m, Erlang.lists.«foldl/3» (D m)
        (.function false "Elixir.Module.Types.Descr" "-map_pair_projection_keeps_full_fst?/2-fun-0-" 2 #[])
        (.atom "bdd_bot") (Term.list P) = .ok u := by
  obtain ⟨u, ⟨tu, su⟩, run⟩ := foldl_rel (K := 0) "Elixir.Module.Types.Descr" "-map_pair_projection_keeps_full_fst?/2-fun-0-" #[]
    (fun pre a => MField E a ∧ ∀ w, denMF E den a w = Bool.true ↔
      ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ denMF E den b w = Bool.true) P
    (fun pre x a mx ⟨ta, sa⟩ => by
      obtain ⟨f, b, rfl, -, fb⟩ := hP x mx
      obtain ⟨r, run, tr, sr, -⟩ := map_union_lh (den := den) fb ta
      refine ⟨r, ⟨tr, fun w => ?_⟩, fun m _ => ?_⟩
      · rw [sr, Bool.or_eq_true, sa]
        constructor
        · rintro (h | ⟨p, mp, h⟩)
          · exact ⟨_, by simp, f, b, rfl, h⟩
          · exact ⟨p, by simp [mp], h⟩
        · rintro ⟨p, mp, f', b', e, h⟩
          simp only [List.mem_append, List.mem_singleton] at mp
          rcases mp with mp | rfl
          · exact Or.inr ⟨p, mp, f', b', e, h⟩
          · simp only [Term.tuple.injEq] at e
            obtain ⟨rfl, rfl, -⟩ := e
            exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_pair_projection_keeps_full_fst?/2-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_pair_projection_keeps_full_fst?/2-fun-0-/2»] using run)
    (.atom "bdd_bot") ⟨Or.inr Bdd.bot, fun w => by simp [denMF_bot]⟩
  exact ⟨u, tu, su, fun m => run m (Nat.zero_le _)⟩

/-- `tuple_pair_projection_keeps_full_fst?/2` checks for a remaining tuple outside every negated pair. -/
theorem mkeeps_full (ef : EF nd E V den tl K) {m : Nat} (hm : K + 4 ≤ m) (P : List Term) (hP : ∀ p ∈ P, MPairOk E p)
    {b : Term} (hb : MField E b) : ∃ s : Bool,
      Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_fst?/2» (D m) (Term.list P) b = .ok (boolAtom s) ∧
      (s = Bool.true ↔ ∃ w, denMF E den b w = Bool.true ∧
        ∀ p ∈ P, ∀ f nb, p = .tuple #[f, nb] → denMF E den nb w = Bool.false) := by
  obtain ⟨u, tu, su, run⟩ := munion_pairs (den := den) P hP
  obtain ⟨d, rd, td, sd, -⟩ := map_diff_lh hb tu
  obtain ⟨e, re, se⟩ := map_empty_exact ef td []
  have se := se (lh d + 1) (by omega) (safeN_nil _)
  refine ⟨!e, ?_, ?_⟩
  · cases e <;> simp [Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_fst?/2», run m, rd, re m hm,
      Erlang.erlang.«not/1», boolAtom]
  · cases e
    · simp only [Bool.not_false, true_iff]
      obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt se.mpr (by simp))
      rw [sd] at hw
      simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true'] at hw
      refine ⟨w, hw.1, fun p mp f nb e => ?_⟩
      cases h : denMF E den nb w
      · rfl
      · exact absurd ((su w).mpr ⟨p, mp, f, nb, e, h⟩) (by rw [hw.2]; simp)
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro w hw none
      have := (se.mp rfl) w
      rw [sd, hw] at this
      simp only [Bool.true_and, Bool.not_eq_false'] at this
      obtain ⟨p, mp, f, nb, e, h⟩ := (su w).mp this
      rw [none p mp f nb e] at h
      cases h

/-- Lists of pairs whose tuple types are not empty. -/
def MQOk (E : Term → Prop) (den : Term → V → Prop) (Q : List Term) : Prop :=
  ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ FieldValue E f ∧ MField E b ∧ ∃ w, denMF E den b w = Bool.true

/-- A value and a remaining tuple of values in some pair. -/
def MInPairs (E : Term → Prop) (den : Term → V → Prop) (Q : List Term) (y : Option V) (w : MW V) : Prop :=
  ∃ p ∈ Q, MPairIn E den p y w

/-- `prepend_tuple_pair_unless_empty_diff/4` keeps the pair of the difference, unless it is empty. -/
theorem mprepend_pair (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {f nv b : Term} (hf : FieldValue E f) (hnv : FieldValue E nv)
    (hb : MField E b) (nb : ∃ w, denMF E den b w = Bool.true) :
    ∃ new, (∀ A, Elixir.Module.Types.Descr.«prepend_map_pair_unless_empty_diff/4» (D m) f nv b (Term.list A) =
        .ok (Term.list (new ++ A))) ∧ MQOk E den new ∧ (∀ ok, OField ok b → KeepsQ ok new) ∧ FilledQ den new ∧
      ∀ y w, MInPairs E den new y w ↔ (FieldSem den f y ∧ ¬FieldSem den nv y) ∧ denMF E den b w = Bool.true := by
  obtain ⟨d, hd, rd, sd⟩ := field_diff_val (den := den) ef hm hf hnv
  obtain ⟨e, re, se⟩ := field_empty_val (den := den) ef hm hd
  cases e
  · refine ⟨[.tuple #[d, b]], fun A => ?_, ?_, fun ok ob p mp => ?_, fun p mp => ?_, fun y w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«prepend_map_pair_unless_empty_diff/4»,
        rd, re, Lynx.Term.isMember, Term.list]
    · intro p mp; simp at mp; subst mp; exact ⟨d, b, rfl, hd, hb, nb⟩
    · simp at mp; subst mp; exact ⟨d, b, rfl, ob⟩
    · simp at mp; subst mp
      refine ⟨d, b, rfl, Classical.byContradiction fun none => ?_⟩
      have := se.mpr fun o h => none ⟨o, h⟩
      cases this
    · simp [MInPairs, mpairIn_iff, sd]
  · refine ⟨[], fun A => ?_, by simp [MQOk], fun _ _ => by simp [KeepsQ], by simp [FilledQ], fun y w => ?_⟩
    · simp [Elixir.Module.Types.Descr.«prepend_map_pair_unless_empty_diff/4»,
        rd, re, Lynx.Term.isMember]
    · simp only [MInPairs, List.not_mem_nil, false_and, exists_false, false_iff, not_and]
      intro h₁ _
      exact se.mp rfl y ((sd y).mpr h₁)

/-- One step of `tuple_project_negative_pairs/3`: a pair minus a negated pair, as pairs of non-empty tuple types. -/
theorem mproject_step (ef : EF nd E V den tl K) {m : Nat} (hm : K + 4 ≤ m) {nv nb x : Term} (hnv : FieldValue E nv)
    (hnb : MField E nb) (hx : MQOk E den [x]) :
    ∃ new, (∀ A, Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4» (D m) nb nv x (Term.list A) =
        .ok (Term.list (new ++ A))) ∧ MQOk E den new ∧ (∀ ok, OField ok nb → KeepsQ ok [x] → KeepsQ ok new) ∧
      (FilledQ den [x] → FilledQ den new) ∧
      ∀ y w, MInPairs E den new y w ↔ MPairIn E den x y w ∧ ¬(FieldSem den nv y ∧ denMF E den nb w = Bool.true) := by
  obtain ⟨f, b, rfl, hf, hb, nbw⟩ := hx _ List.mem_cons_self
  have kx : ∀ ok, KeepsQ ok [.tuple #[f, b]] → OField ok b := fun ok k => by
    obtain ⟨f', b', e, ob⟩ := k _ List.mem_cons_self
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨-, rfl⟩ := e
    exact ob
  obtain ⟨ib, rib, tib, sib, -⟩ := map_inter_lh (den := den) hb hnb
  obtain ⟨eib, reib, seib⟩ := map_empty_exact ef tib []
  have seib := seib (lh ib + 1) (by omega) (safeN_nil _)
  obtain ⟨i_f, hif, rif, sif⟩ := field_inter_val (den := den) ef (show K ≤ m by omega) hf hnv
  obtain ⟨e1, re1, se1⟩ := field_empty_val (den := den) ef (show K ≤ m by omega) hif
  obtain ⟨db, rdb, tdb, sdb, -⟩ := map_diff_lh hb hnb
  obtain ⟨e2, re2, se2⟩ := map_empty_exact ef tdb []
  have se2 := se2 (lh db + 1) (by omega) (safeN_nil _)
  obtain ⟨pnew, rp, qp, kp, fp, sp⟩ := mprepend_pair ef (m := m) (by omega) hf hnv hb nbw
  have keepSem : ∀ y w, MInPairs E den [.tuple #[f, b]] y w ↔ MPairIn E den (.tuple #[f, b]) y w := fun y w => by
    simp [MInPairs]
  by_cases keep : (∃ k r, nb = .tuple #[k, .atom "closed", r]) ∧ eib = Bool.true
  · obtain ⟨⟨k, r, rfl⟩, rfl⟩ := keep
    refine ⟨[.tuple #[f, b]], fun A => ?_, hx, fun _ _ k => k, id, fun y w => ?_⟩
    · rw [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4».eq_def]
      simp [rib, reib m hm, Lynx.Term.isMember, Term.list]
    · rw [keepSem, mpairIn_iff]
      refine ⟨fun h => ⟨h, fun ⟨_, h'⟩ => ?_⟩, fun h => h.1⟩
      have := seib.mp rfl w
      rw [sib, h.2, h'] at this
      cases this
  -- The pair meets the negated pair: the intersection of the remaining tuples is not known to be empty.
  cases e1
  · cases e2
    · refine ⟨pnew ++ [.tuple #[i_f, db]], fun A => ?_, ?_, fun ok onb k p mp => ?_, fun _ p mp => ?_, fun y w => ?_⟩
      · rw [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4».eq_def]
        have rp' := rp (.tuple #[i_f, db] :: A)
        simp only [Term.list] at rp'
        by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
        · obtain ⟨k, r, rfl⟩ := hc
          have : eib = Bool.false := by
            cases eib
            · rfl
            · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
          subst this
          simp [rib, reib m hm, Lynx.Term.isMember, rif, re1, rdb,
            re2 m hm, rp']
        · simp only
          split
          · exact absurd ⟨_, _, rfl⟩ hc
          · simp [Lynx.Term.isMember, rif, re1, rdb, re2 m hm, rp']
      · intro p mp
        rcases List.mem_append.mp mp with mp | mp
        · exact qp p mp
        · simp at mp; subst mp
          refine ⟨i_f, db, rfl, hif, tdb, ?_⟩
          exact Classical.byContradiction fun none => by
            have := se2.mpr fun v => by
              cases h : denMF E den db v
              · rfl
              · exact absurd ⟨v, h⟩ none
            cases this
      · rcases List.mem_append.mp mp with mp | mp
        · exact kp ok (kx ok k) p mp
        · simp at mp; subst mp; exact ⟨i_f, db, rfl, map_diff_keeps hb hnb rdb (kx ok k) onb⟩
      · rcases List.mem_append.mp mp with mp | mp
        · exact fp p mp
        · simp at mp; subst mp
          refine ⟨i_f, db, rfl, Classical.byContradiction fun none => ?_⟩
          have := se1.mpr fun o h => none ⟨o, h⟩
          cases this
      · simp only [MInPairs, List.mem_append, List.mem_singleton] at sp ⊢
        rw [mpairIn_iff]
        constructor
        · rintro ⟨p, mp | rfl, hp⟩
          · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := (sp y w).mp ⟨p, mp, hp⟩
            exact ⟨⟨h₁, h₃⟩, fun h => h₂ h.1⟩
          · rw [mpairIn_iff, sif, sdb] at hp
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
            refine ⟨⟨hp.1.1, hp.2.1⟩, fun h => ?_⟩
            rw [h.2] at hp; cases hp.2.2
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩
          by_cases hn : FieldSem den nv y
          · refine ⟨_, Or.inr rfl, ?_⟩
            rw [mpairIn_iff, sif, sdb, h₂]
            cases h : denMF E den nb w
            · exact ⟨⟨h₁, hn⟩, rfl⟩
            · exact absurd ⟨hn, h⟩ h₃
          · obtain ⟨p, mp, hp⟩ := (sp y w).mpr ⟨⟨h₁, hn⟩, h₂⟩
            exact ⟨p, Or.inl mp, hp⟩
    · refine ⟨pnew, fun A => ?_, qp, fun ok _ k => kp ok (kx ok k), fun _ => fp, fun y w => ?_⟩
      · rw [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4».eq_def]
        by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
        · obtain ⟨k, r, rfl⟩ := hc
          have : eib = Bool.false := by
            cases eib
            · rfl
            · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
          subst this
          simp [rib, reib m hm, Lynx.Term.isMember, rif, re1, rdb, re2 m hm, rp A]
        · simp only
          split
          · exact absurd ⟨_, _, rfl⟩ hc
          · simp [Lynx.Term.isMember, rif, re1, rdb, re2 m hm, rp A]
      · rw [sp, mpairIn_iff]
        have cover : ∀ w, denMF E den b w = Bool.true → denMF E den nb w = Bool.true := fun w h => by
          have := se2.mp rfl w
          rw [sdb, h] at this
          simpa using this
        constructor
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨⟨h₁, h₃⟩, fun h => h₂ h.1⟩
        · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨⟨h₁, fun hn => h₃ ⟨hn, cover w h₂⟩⟩, h₂⟩
  · refine ⟨[.tuple #[f, b]], fun A => ?_, hx, fun _ _ k => k, id, fun y w => ?_⟩
    · rw [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4».eq_def]
      by_cases hc : ∃ k r, nb = .tuple #[k, .atom "closed", r]
      · obtain ⟨k, r, rfl⟩ := hc
        have : eib = Bool.false := by
          cases eib
          · rfl
          · exact absurd ⟨⟨k, r, rfl⟩, rfl⟩ keep
        subst this
        simp [rib, reib m hm, Lynx.Term.isMember, rif, re1, Term.list]
      · simp only
        split
        · exact absurd ⟨_, _, rfl⟩ hc
        · simp [Lynx.Term.isMember, rif, re1, Term.list]
    · rw [keepSem, mpairIn_iff]
      refine ⟨fun h => ⟨h, fun h' => (se1.mp rfl) y ((sif y).mpr ⟨h.1, h'.1⟩)⟩, fun h => h.1⟩

/-- `tuple_project_negative_pairs/3` splits a pair minus negated pairs into pairs of non-empty tuple types. -/
theorem mproject_pairs (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (P : List Term) (hP : ∀ p ∈ P, MPairOk E p)
    {value rest : Term} (hv : FieldValue E value) (hr : MField E rest) (nr : ∃ w, denMF E den rest w = Bool.true) :
    ∃ Q, Elixir.Module.Types.Descr.«map_remove_negative/3» (D (n + 2)) (Term.list P) value rest =
        .ok (Term.list Q) ∧ MQOk E den Q ∧ (∀ ok, OField ok rest → KeepsQ ok P → KeepsQ ok Q) ∧
      ((∃ o, FieldSem den value o) → FilledQ den Q) ∧
      ∀ y w, MInPairs E den Q y w ↔ FieldSem den value y ∧ denMF E den rest w = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p y w := by
  obtain ⟨r, ⟨Q, rfl, qQ, kQ, fQ, sQ⟩, run⟩ := foldl_rel_at (m := n + 2) "Elixir.Module.Types.Descr"
    "-map_remove_negative/3-fun-1-" #[]
    (fun pre a => ∃ Q, a = Term.list Q ∧ MQOk E den Q ∧ (∀ ok, OField ok rest → KeepsQ ok pre → KeepsQ ok Q) ∧
      ((∃ o, FieldSem den value o) → FilledQ den Q) ∧
      ∀ y w, MInPairs E den Q y w ↔
        FieldSem den value y ∧ denMF E den rest w = Bool.true ∧ ∀ p ∈ pre, ¬MPairIn E den p y w) P
    (fun pre x a mx ⟨Q, ea, qQ, kQ, fQ, sQ⟩ => by
      subst ea
      obtain ⟨nv, nb, rfl, hnv, hnb⟩ := hP x mx
      have each : ∀ p ∈ Q, ∃ new, (∀ A, Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4» (D n) nb nv
          p (Term.list A) = .ok (Term.list (new ++ A))) ∧ MQOk E den new ∧
          (∀ ok, OField ok nb → KeepsQ ok [p] → KeepsQ ok new) ∧ (FilledQ den [p] → FilledQ den new) ∧
          ∀ y w, MInPairs E den new y w ↔ MPairIn E den p y w ∧ ¬(FieldSem den nv y ∧ denMF E den nb w = Bool.true) :=
        fun p mp => mproject_step ef hn hnv hnb fun p' mp' => by rw [List.mem_singleton] at mp'; rw [mp']; exact qQ p mp
      classical
      let h : Term → List Term := fun p => if hp : p ∈ Q then Classical.choose (each p hp) else []
      have hh : ∀ p ∈ Q, (∀ A, Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-0-/4» (D n) nb nv
          p (Term.list A) = .ok (Term.list (h p ++ A))) ∧ MQOk E den (h p) ∧
          (∀ ok, OField ok nb → KeepsQ ok [p] → KeepsQ ok (h p)) ∧ (FilledQ den [p] → FilledQ den (h p)) ∧
          ∀ y w, MInPairs E den (h p) y w ↔ MPairIn E den p y w ∧ ¬(FieldSem den nv y ∧ denMF E den nb w = Bool.true) := by
        intro p mp
        simp only [h, dite_eq_left mp]
        exact Classical.choose_spec (each p mp)
      have inner := foldl_lists_at (m := n + 1) "Elixir.Module.Types.Descr" "-map_remove_negative/3-fun-0-"
        #[nb, nv] h Q (fun p mp A => by
          rw [Erlang.program.«Elixir.Module.Types.Descr:-map_remove_negative/3-fun-0-/2».pure]
          exact (hh p mp).1 A) []
      refine ⟨Term.list (Q.reverse.flatMap h), ⟨Q.reverse.flatMap h, rfl, fun p mp => ?_, fun ok orest kpre p mp => ?_,
        fun nv p mp => ?_, fun y w => ?_⟩, ?_⟩
      · simp only [List.mem_flatMap, List.mem_reverse] at mp
        obtain ⟨q, mq, mp⟩ := mp
        exact (hh q mq).2.1 p mp
      · simp only [List.mem_flatMap, List.mem_reverse] at mp
        obtain ⟨q, mq, mp⟩ := mp
        have kq := kQ ok orest (fun p' mp' => kpre p' (List.mem_append_left _ mp'))
        obtain ⟨f', b', ex, onb⟩ := kpre _ (List.mem_append_right _ List.mem_cons_self)
        simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at ex
        obtain ⟨rfl, rfl⟩ := ex
        exact (hh q mq).2.2.1 ok onb (fun p' mp' => by rw [List.mem_singleton] at mp'; rw [mp']; exact kq q mq) p mp
      · simp only [List.mem_flatMap, List.mem_reverse] at mp
        obtain ⟨q, mq, mp⟩ := mp
        exact (hh q mq).2.2.2.1 (fun p' mp' => by rw [List.mem_singleton] at mp'; rw [mp']; exact fQ nv q mq) p mp
      · simp only [MInPairs, List.mem_flatMap, List.mem_reverse, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨p, ⟨q, mq, mp⟩, hp⟩
          obtain ⟨hq, hn'⟩ := ((hh q mq).2.2.2.2 y w).mp ⟨p, mp, hp⟩
          obtain ⟨h₁, h₂, h₃⟩ := (sQ y w).mp ⟨q, mq, hq⟩
          refine ⟨h₁, h₂, fun p' mp' hp' => ?_⟩
          rcases mp' with mp' | rfl
          · exact h₃ p' mp' hp'
          · exact hn' (mpairIn_iff.mp hp')
        · rintro ⟨h₁, h₂, h₃⟩
          obtain ⟨q, mq, hq⟩ := (sQ y w).mpr ⟨h₁, h₂, fun p' mp' => h₃ p' (Or.inl mp')⟩
          obtain ⟨p, mp, hp⟩ := ((hh q mq).2.2.2.2 y w).mpr ⟨hq, fun h => h₃ _ (Or.inr rfl) (mpairIn_iff.mpr h)⟩
          exact ⟨p, ⟨q, mq, mp⟩, hp⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_remove_negative/3-fun-1-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_remove_negative/3-fun-1-/2»] using inner)
    (Term.list [.tuple #[value, rest]]) ⟨[.tuple #[value, rest]], rfl, fun p mp => by
      simp at mp; subst mp; exact ⟨value, rest, rfl, hv, hr, nr⟩,
      fun ok orest _ p mp => by simp at mp; subst mp; exact ⟨value, rest, rfl, orest⟩,
      fun nv p mp => by simp at mp; subst mp; exact ⟨value, rest, rfl, nv⟩,
      fun y w => by simp [MInPairs, mpairIn_iff]⟩
  exact ⟨Q, by simp [Elixir.Module.Types.Descr.«map_remove_negative/3», run], qQ, kQ, fQ, sQ⟩

theorem fieldValue_cases {f : Term} (hf : FieldValue E f) : ∃ t o, f = .tuple #[t, boolAtom o] ∧ E t := hf

/-- The final fold of `map_split_key_line/5` unites the fields of the pairs into the accumulated field. -/
theorem munion_fields (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (Q : List Term)
    (hQ : ∀ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ FieldValue E f) {acc : Term} (ha : FieldValue E acc) :
    ∃ u, FieldValue E u ∧ Erlang.lists.«foldl/3» (D (n + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_split_key_line/5-fun-0-" 2 #[]) acc (Term.list Q) = .ok u ∧
      ∀ o, FieldSem den u o ↔ FieldSem den acc o ∨ ∃ p ∈ Q, ∃ f b, p = .tuple #[f, b] ∧ FieldSem den f o := by
  obtain ⟨u, ⟨hu, su⟩, run⟩ := foldl_rel_at (m := n + 1) "Elixir.Module.Types.Descr" "-map_split_key_line/5-fun-0-" #[]
    (fun pre a => FieldValue E a ∧ ∀ o, FieldSem den a o ↔ FieldSem den acc o ∨
      ∃ p ∈ pre, ∃ f b, p = .tuple #[f, b] ∧ FieldSem den f o) Q
    (fun pre x a mx ⟨ha', sa⟩ => by
      obtain ⟨f, b, rfl, hf⟩ := hQ x mx
      obtain ⟨t₁, o₁, rfl, h₁⟩ := hf
      obtain ⟨t₂, o₂, rfl, h₂⟩ := ha'
      obtain ⟨c, hc, rc, sc⟩ := field_opt_union_val (den := den) ef hn rfl rfl h₁ h₂ []
      refine ⟨.tuple #[c, boolAtom (o₁ || o₂)], ⟨⟨c, _, rfl, hc⟩, fun o => ?_⟩, ?_⟩
      · rw [sc, sa]
        constructor
        · rintro (h | h | ⟨p, mp, h⟩)
          · exact Or.inr ⟨_, by simp, _, b, rfl, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨p, by simp [mp], h⟩
        · rintro (h | ⟨p, mp, f', b', e, h⟩)
          · exact Or.inr (Or.inl h)
          · simp only [List.mem_append, List.mem_singleton] at mp
            rcases mp with mp | rfl
            · exact Or.inr (Or.inr ⟨p, mp, f', b', e, h⟩)
            · simp only [Term.tuple.injEq] at e
              obtain ⟨rfl, rfl, -⟩ := e
              exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_split_key_line/5-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_split_key_line/5-fun-0-/2»] using rc)
    acc ⟨ha, fun o => by simp⟩
  exact ⟨u, hu, run, su⟩

/-- The field a line with negations projects to, united with the accumulated one: the values at the key of its pair,
outside the negated pairs. -/
theorem mproj_value (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (P : List Term) (hP : ∀ p ∈ P, MPairOk E p)
    {field rest acc : Term} (hv : FieldValue E field) (hr : MField E rest) (nr : ∃ w, denMF E den rest w = Bool.true)
    (ha : FieldValue E acc) :
    ∃ (s : Bool) (acc' : Term), Elixir.Module.Types.Descr.«map_pair_projection_keeps_full_fst?/2» (D (n + 2))
        (Term.list P) rest = .ok (boolAtom s) ∧
      (s = Bool.true → Elixir.Module.Types.Descr.«field_opt_union/3» (D (n + 2)) field acc (.map []) = .ok acc') ∧
      (s = Bool.false → ∃ Q, Elixir.Module.Types.Descr.«map_remove_negative/3» (D (n + 2)) (Term.list P) field rest =
        .ok (Term.list Q) ∧ Erlang.lists.«foldl/3» (D (n + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_split_key_line/5-fun-0-" 2 #[]) acc (Term.list Q) = .ok acc') ∧
      FieldValue E acc' ∧
      ∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨
        ∃ w, FieldSem den field o ∧ denMF E den rest w = Bool.true ∧ ∀ p ∈ P, ¬MPairIn E den p o w := by
  obtain ⟨s, rs, ss⟩ := mkeeps_full (den := den) ef (m := n + 2) (by omega) P hP hr
  cases s
  · obtain ⟨Q, rQ, qQ, -, -, sQ⟩ := mproject_pairs ef hn P hP hv hr nr
    obtain ⟨u, hu, ru, su⟩ := munion_fields ef (n := n + 1) (by omega) Q (fun p mp => by
      obtain ⟨f, b, e, hf, -⟩ := qQ p mp
      exact ⟨f, b, e, hf⟩) ha
    refine ⟨Bool.false, u, rs, by simp, fun _ => ⟨Q, rQ, ru⟩, hu, fun o => ?_⟩
    rw [su]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨p, mp, f, b, rfl, hy⟩
      obtain ⟨f', b', e, -, -, w, hw⟩ := qQ _ mp
      simp only [Term.tuple.injEq] at e
      obtain ⟨rfl, rfl, -⟩ := e
      exact ⟨w, (sQ o w).mp ⟨_, mp, mpairIn_iff.mpr ⟨hy, hw⟩⟩⟩
    · rintro ⟨w, h⟩
      obtain ⟨p, mp, hp⟩ := (sQ o w).mpr h
      obtain ⟨f, b, rfl, hy, -⟩ := hp
      exact ⟨_, mp, f, b, rfl, hy⟩
  · obtain ⟨w₀, hw₀, out⟩ := ss.mp rfl
    obtain ⟨t₁, o₁, rfl, h₁⟩ := hv
    obtain ⟨t₂, o₂, rfl, h₂⟩ := ha
    obtain ⟨c, hc, rc, sc⟩ := field_opt_union_val (den := den) ef (m := n + 2) (by omega) rfl rfl h₁ h₂ []
    refine ⟨Bool.true, .tuple #[c, boolAtom (o₁ || o₂)], rs, fun _ => rc, by simp, ⟨c, _, rfl, hc⟩, fun o => ?_⟩
    rw [sc, or_comm]
    refine or_congr Iff.rfl ⟨fun hy => ⟨w₀, hy, hw₀, fun p mp hp => ?_⟩, fun ⟨_, hy, _⟩ => hy⟩
    obtain ⟨f, nb, rfl, -, hnb⟩ := hp
    rw [out _ mp f nb rfl] at hnb
    cases hnb

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem fieldAt_ok (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l)
    (a : String) : FieldValue E (fieldAt tag l a) := by
  unfold fieldAt
  cases h : mapLookup l (.atom a) with
  | some f =>
    obtain ⟨e, me, rfl⟩ := lookup_mem h
    exact (sl.1 e me).2
  | none =>
    obtain ⟨f, run, hf⟩ := tag_field_ok ef.term ef.none g.plain
    rw [key_tag_field g] at run
    cases run
    exact hf

theorem mleaf_field {k : Int} {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l)
    (key : KeyOk (.tuple #[.integer k, tag, fieldsTerm l])) : MField E (.tuple #[.integer k, tag, fieldsTerm l]) := by
  by_cases top : tag = .atom "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    exact Or.inl ⟨k, rfl⟩
  · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨k, tag, l, rfl, g, sl⟩, ?_, key⟩)
    rintro ⟨k', e⟩
    obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
    exact top ⟨e₂, fieldsTerm_eq_nil.mp e₃⟩

/-- `map_pop_key_bdd/3` splits a map literal into a pair at a key. -/
theorem pop_pair (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (sl : FieldsV E l)
    (a : String) : ∃ k : Int, Elixir.Module.Types.Descr.«map_pop_key_bdd/3» tag (fieldsTerm l) (.atom a) =
      .ok (.tuple #[fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]]) ∧
      MPairOk E (.tuple #[fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]]) ∧
      (∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true ↔
        MSem den tag (eraseKey a l) w) ∧
      ∀ w, MSem den tag l w ↔ MPairIn E den (.tuple #[fieldAt tag l a, .tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]])
        (w (.atom a)) (eraseK a w) := by
  obtain ⟨k, run, key⟩ := pop_val g sl a
  have sl' := fieldsV_eraseKey (a := a) sl
  have rest : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true ↔
      MSem den tag (eraseKey a l) w := fun w => denMF_leaf ef sl' g w
  refine ⟨k, run, ⟨_, _, rfl, fieldAt_ok ef g sl a, mleaf_field g sl' key⟩, rest, fun w => ?_⟩
  rw [mpairIn_iff, rest, msem_at ef g]

theorem msem_open_nil (w : MW V) : MSem den (.atom "open") [] w :=
  ⟨fun s => by simp [FSem, TagSem, mapLookup], fun k i => by simp [TagSem]⟩

/-- Rests of negated pairs: single literals without the key. -/
def RestOk (E : Term → Prop) (den : Term → V → Prop) (a : String) (p : Term) : Prop :=
  ∃ (f : Term) (k : Int) (ntag : Term) (nl : List (Term × Term)), p = .tuple #[f, .tuple #[.integer k, ntag, fieldsTerm nl]] ∧ TagV E ntag ∧ FieldsV E nl ∧
    mapLookup nl (.atom a) = none ∧
    ∀ w, denMF E den (.tuple #[.integer k, ntag, fieldsTerm nl]) w = Bool.true ↔ MSem den ntag nl w

/-- `map_split_negative_pairs_key/3` splits negated literals at a key, unless one is the top literal. -/
theorem msplit_negs (ef : EF nd E V den tl K) (a : String) : ∀ (negs : List Term), (∀ N ∈ negs, MapLitV E N) →
    ∀ (acc : List Term), ∃ r, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3» (Term.list negs) (.atom a)
        (Term.list acc) = .ok r ∧
      ((r = .atom "empty" ∧ ∃ N ∈ negs, ∀ w, NSem den N w) ∨
        ∃ P, r = Term.list (P ++ acc) ∧ (∀ p ∈ P, MPairOk E p ∧ RestOk E den a p) ∧
          ∀ w, (∃ N ∈ negs, NSem den N w) ↔ ∃ p ∈ P, MPairIn E den p (w (.atom a)) (eraseK a w))
  | [], _, acc => ⟨_, by rw [Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3».eq_def]; rfl,
      Or.inr ⟨[], by simp, by simp, fun w => by simp⟩⟩
  | N :: rest, lits, acc => by
    obtain ⟨k, ntag, nl, rfl, gn, snl⟩ := lits _ List.mem_cons_self
    have lits' := fun N' (m : N' ∈ rest) => lits N' (List.mem_cons_of_mem _ m)
    by_cases top : ntag = .atom "open" ∧ nl = []
    · obtain ⟨rfl, rfl⟩ := top
      refine ⟨_, ?_, Or.inl ⟨rfl, _, List.mem_cons_self, fun w => nsem_lit.mpr (msem_open_nil w)⟩⟩
      rw [Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3».eq_def]
      rfl
    obtain ⟨k', run, ok, rest', sem⟩ := pop_pair (den := den) ef gn snl a
    obtain ⟨r, rr, h⟩ := msplit_negs ef a rest lits'
      (.tuple #[fieldAt ntag nl a, .tuple #[.integer k', ntag, fieldsTerm (eraseKey a nl)]] :: acc)
    have step : Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3»
        (Term.list (.tuple #[.integer k, ntag, fieldsTerm nl] :: rest)) (.atom a) (Term.list acc) =
        Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3» (Term.list rest) (.atom a)
          (Term.list (.tuple #[fieldAt ntag nl a, .tuple #[.integer k', ntag, fieldsTerm (eraseKey a nl)]] :: acc)) := by
      rw [Elixir.Module.Types.Descr.«map_split_negative_pairs_key/3».eq_def]
      simp only [Term.list]
      split
      · rename_i heq
        obtain ⟨h₁, -⟩ := Term.cons.inj heq
        obtain ⟨-, e₂, e₃⟩ := tuple3_inj h₁
        exact absurd ⟨e₂, fieldsTerm_eq_nil.mp e₃⟩ top
      · rename_i heq
        obtain ⟨h₁, rfl⟩ := Term.cons.inj heq
        obtain ⟨-, rfl, rfl⟩ := tuple3_inj h₁
        simp [run]
      · rename_i heq; cases heq
      · rename_i h₁ h₂ h₃; exact absurd rfl (h₂ _ _ _ _)
    refine ⟨r, step.trans rr, ?_⟩
    rcases h with ⟨rfl, N', mN', hN'⟩ | ⟨P, rfl, hP, sP⟩
    · exact Or.inl ⟨rfl, N', List.mem_cons_of_mem _ mN', hN'⟩
    refine Or.inr ⟨P ++ [.tuple #[fieldAt ntag nl a, .tuple #[.integer k', ntag, fieldsTerm (eraseKey a nl)]]], by simp,
      fun p mp => ?_, fun w => ?_⟩
    · rcases List.mem_append.mp mp with mp | mp
      · exact hP p mp
      · rw [List.mem_singleton] at mp; subst mp
        refine ⟨ok, _, k', ntag, eraseKey a nl, rfl, gn, fieldsV_eraseKey snl, by simp [lookup_eraseKey], rest'⟩
    · constructor
      · rintro ⟨N', mN', hN'⟩
        rcases List.mem_cons.mp mN' with rfl | mN'
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), (sem w).mp (nsem_lit.mp hN')⟩
        · obtain ⟨p, mp, hp⟩ := (sP w).mp ⟨N', mN', hN'⟩
          exact ⟨p, List.mem_append_left _ mp, hp⟩
      · rintro ⟨p, mp, hp⟩
        rcases List.mem_append.mp mp with mp | mp
        · obtain ⟨N', mN', hN'⟩ := (sP w).mpr ⟨p, mp, hp⟩
          exact ⟨N', List.mem_cons_of_mem _ mN', hN'⟩
        · rw [List.mem_singleton] at mp; subst mp
          exact ⟨_, List.mem_cons_self, nsem_lit.mpr ((sem w).mpr hp)⟩

theorem eraseK_setK (a : String) (o : Option V) (w : MW V) : eraseK a (setK a o w) = eraseK a w := by
  funext k; by_cases h : k = .atom a <;> simp [eraseK, setK, h]

theorem eraseK_of_none {a : String} {u : MW V} (h : u (.atom a) = none) : eraseK a u = u := by
  funext k; by_cases hk : k = .atom a
  · subst hk; simp [eraseK, h]
  · simp [eraseK, hk]

/-- Values at a key of the maps of a line. -/
def LongM (den : Term → V → Prop) (L : Term) (a : String) (o : Option V) : Prop :=
  ∃ w, InMLine den L w ∧ w (.atom a) = o

/-- The field and rest of a negated pair. -/
def pairField : Term → Term
  | .tuple ⟨[f, _]⟩ => f
  | _ => .nil

def pairRest : Term → Term × List (Term × Term)
  | .tuple ⟨[_, .tuple ⟨[_, tag, fs]⟩]⟩ => (tag, domFields fs)
  | _ => (.atom "open", [])

/-- A value at a key with a rest outside the negated pairs is the value at the key of a map of the line. -/
theorem long_of_rest (ef : EF nd E V den tl K) (a : String) {tag : Term} (g : TagV E tag) {l : List (Term × Term)}
    {negs : List Term} {P : List Term} (hP : ∀ p ∈ P, MPairOk E p ∧ RestOk E den a p)
    (sP : ∀ w, (∃ N ∈ negs, NSem den N w) ↔ ∃ p ∈ P, MPairIn E den p (w (.atom a)) (eraseK a w)) {o : Option V}
    (ho : FieldSem den (fieldAt tag l a) o) {w' : MW V} (hw' : MSem den tag (eraseKey a l) w')
    (out : ∀ p ∈ P, ¬MPairIn E den p o w') :
    LongM den (.tuple #[tag, fieldsTerm l, Term.list negs]) a o := by
  classical
  let Ns := (P.filter fun p => decide (FieldSem den (pairField p) o)).map pairRest
  have hN : ∀ N ∈ Ns, mapLookup N.2 (.atom a) = none ∧ ∃ p ∈ P, FieldSem den (pairField p) o ∧
      ∀ w, MSem den N.1 N.2 w → MPairIn E den p o w := by
    intro N mN
    simp only [Ns, List.mem_map, List.mem_filter, decide_eq_true_eq] at mN
    obtain ⟨p, ⟨mp, hf⟩, rfl⟩ := mN
    obtain ⟨-, f, k, ntag, nl, rfl, -, -, na, rest⟩ := hP p mp
    simp only [pairRest, pairField, domFields_fieldsTerm] at hf ⊢
    exact ⟨na, _, mp, hf, fun w hw => mpairIn_iff.mpr ⟨hf, (rest w).mpr hw⟩⟩
  obtain ⟨u, ua, hu, hn⟩ := aless a (by rw [lookup_eraseKey]; simp) Ns (fun N mN => (hN N mN).1) hw'
    (fun N mN hN' => by
      obtain ⟨-, p, mp, -, inc⟩ := hN N mN
      exact out p mp (inc w' hN'))
  refine ⟨setK a o u, inMLine_iff.mpr ⟨(msem_at ef g l a _).mpr ⟨by simpa [setK] using ho, by
    rw [eraseK_setK, eraseK_of_none ua]; exact hu⟩, fun N mN hN' => ?_⟩, by simp [setK]⟩
  obtain ⟨p, mp, hp⟩ := (sP _).mp ⟨N, mN, hN'⟩
  rw [eraseK_setK, eraseK_of_none ua] at hp
  have hpo : MPairIn E den p o u := by simpa [setK] using hp
  obtain ⟨-, f, k, ntag, nl, rfl, -, -, -, rest⟩ := hP p mp
  obtain ⟨hf, hr⟩ := mpairIn_iff.mp hpo
  refine hn (ntag, nl) ?_ ((rest u).mp hr)
  simp only [Ns, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨_, ⟨mp, by simpa [pairField] using hf⟩, by simp [pairRest, domFields_fieldsTerm]⟩

/-- One step of `map_dnf_fetch_static/2`: the field accumulated so far, united with the values at the key of the maps
of a non-empty line. -/
theorem mline_step (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) {L : Term} (hL : MLine E L)
    (ne : ∃ w, InMLine den L w) {acc : Term} (ha : FieldValue E acc) :
    ∃ acc', (D (n + 3)).pure (.function false "Elixir.Module.Types.Descr" "-map_dnf_fetch_static/2-fun-0-" 2 #[.atom a])
        #[L, acc] = .ok acc' ∧ FieldValue E acc' ∧ ∀ o, FieldSem den acc' o ↔ FieldSem den acc o ∨ LongM den L a o := by
  obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hL
  obtain ⟨w₀, hw₀⟩ := ne
  obtain ⟨hm₀, hn₀⟩ := inMLine_iff.mp hw₀
  obtain ⟨k, run, ⟨f, b, ef', hf, hb⟩, rest, sem⟩ := pop_pair (den := den) ef g sl a
  simp only [Term.tuple.injEq] at ef'
  obtain ⟨rfl, rfl, -⟩ := ef'
  have split₀ := (msem_at ef g l a w₀).mp hm₀
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_dnf_fetch_static/2-fun-0-/2».pure]
  by_cases nn : negs = []
  · subst nn
    obtain ⟨t₁, o₁, e₁, h₁⟩ := hf
    obtain ⟨t₂, o₂, e₂, h₂⟩ := ha
    obtain ⟨c, hc, rc, sc⟩ := field_opt_union_val (den := den) ef (m := n + 2) (by omega) e₁ e₂ h₁ h₂ []
    refine ⟨.tuple #[c, boolAtom (o₁ || o₂)], ?_, ⟨c, _, rfl, hc⟩, fun o => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-map_dnf_fetch_static/2-fun-0-/3»,
        Elixir.Module.Types.Descr.«map_split_key_line/5», run, rc]
    · rw [sc, or_comm]
      refine or_congr Iff.rfl ⟨fun ho => long_of_rest ef a g (P := []) (by simp) (fun w => by simp) ho split₀.2
        (by simp), ?_⟩
      rintro ⟨w, hw, rfl⟩
      exact ((msem_at ef g l a w).mp (inMLine_iff.mp hw).1).1
  · have nnil : Term.list negs ≠ .nil := by cases negs <;> simp_all [Term.list]
    obtain ⟨r, rr, ⟨rfl, N, mN, hN⟩ | ⟨P, rfl, hP, sP⟩⟩ := msplit_negs (den := den) ef a negs lits []
    · refine ⟨acc, ?_, ha, fun o => ⟨fun h => Or.inl h, fun h => h.elim id fun ⟨w, hw, _⟩ =>
        absurd (hN w) ((inMLine_iff.mp hw).2 N mN)⟩⟩
      simp only [Elixir.Module.Types.Descr.«-map_dnf_fetch_static/2-fun-0-/3»]
      rw [Elixir.Module.Types.Descr.«map_split_key_line/5».eq_def]
      split
      · exact absurd ‹_› nnil
      · simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr]
    simp only [List.append_nil] at rr
    have restNe : ∃ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm (eraseKey a l)]) w = Bool.true :=
      ⟨_, (rest _).mpr split₀.2⟩
    obtain ⟨s, acc', rk, hs₁, hs₂, hacc, sacc⟩ := mproj_value ef hn P (fun p mp => (hP p mp).1) hf hb restNe ha
    refine ⟨acc', ?_, hacc, fun o => ?_⟩
    · simp only [Elixir.Module.Types.Descr.«-map_dnf_fetch_static/2-fun-0-/3»]
      rw [Elixir.Module.Types.Descr.«map_split_key_line/5».eq_def]
      split
      · exact absurd ‹_› nnil
      · cases s
        · obtain ⟨Q, rQ, rf⟩ := hs₂ rfl
          cases P with
          | nil => simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr, rk, rQ, rf,
              Lynx.Term.isMember, boolAtom, Term.list]
          | cons p P => simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr, rk, rQ, rf,
              Lynx.Term.isMember, boolAtom, Term.list]
        · cases P with
          | nil => simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr, rk, hs₁ rfl,
              Lynx.Term.isMember, boolAtom, Term.list]
          | cons p P => simp [run, Elixir.Module.Types.Descr.«map_split_negative_pairs_key/2», rr, rk, hs₁ rfl,
              Lynx.Term.isMember, boolAtom, Term.list]
    · rw [sacc]
      refine or_congr Iff.rfl ⟨fun ⟨w', hf', hr', out⟩ => long_of_rest ef a g hP sP hf' ((rest w').mp hr') out, ?_⟩
      rintro ⟨w, hw, rfl⟩
      obtain ⟨hmw, hnw⟩ := inMLine_iff.mp hw
      obtain ⟨hfw, hrw⟩ := (msem_at ef g l a w).mp hmw
      exact ⟨eraseK a w, hfw, (rest _).mpr hrw, fun p mp hp => by
        obtain ⟨N, mN, hN⟩ := (sP w).mpr ⟨p, mp, hp⟩
        exact hnw N mN hN⟩

theorem none_field (ef : EF nd E V den tl K) : FieldValue E (.tuple #[.map [], .atom "false"]) ∧
    ∀ o, ¬FieldSem den (.tuple #[.map [], .atom "false"]) o := by
  refine ⟨⟨_, Bool.false, rfl, ef.none⟩, fun o h => ?_⟩
  rw [show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk] at h
  rcases h with ⟨-, h⟩ | ⟨x, -, hx⟩
  · cases h
  · exact ef.den_none x hx

/-- `map_dnf_fetch_static/2` unites the values at a key of the maps of non-empty lines. -/
theorem mdnf_fetch (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (a : String) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) :
    ∃ F, Elixir.Module.Types.Descr.«map_dnf_fetch_static/2» (D (n + 3)) (Term.list lines) (.atom a) = .ok F ∧
      FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := by
  obtain ⟨F, ⟨hF, sF⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr" "-map_dnf_fetch_static/2-fun-0-"
    #[.atom a] (fun pre acc => FieldValue E acc ∧ ∀ o, FieldSem den acc o ↔ ∃ L ∈ pre, LongM den L a o) lines
    (fun pre L acc mL ⟨ha, sa⟩ => by
      obtain ⟨acc', run, hacc, sacc⟩ := mline_step ef hn a (hl L mL).1 (hl L mL).2 ha
      refine ⟨acc', ⟨hacc, fun o => ?_⟩, run⟩
      rw [sacc, sa]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (⟨L', mL', h⟩ | h)
        · exact ⟨L', Or.inl mL', h⟩
        · exact ⟨L, Or.inr rfl, h⟩
      · rintro ⟨L', mL' | rfl, h⟩
        · exact Or.inl ⟨L', mL', h⟩
        · exact Or.inr h)
    _ ⟨(none_field ef).1, fun o => by simp [(none_field (den := den) ef).2 o]⟩
  exact ⟨F, by simpa [Elixir.Module.Types.Descr.«map_dnf_fetch_static/2»] using run, hF, sF⟩

theorem mfield_three {x a b c : Term} (fx : MField E x) (h : x = .tuple ⟨[a, b, c]⟩) :
    ∃ (k : Int) (tag : Term) (l : List (Term × Term)), x = .tuple #[.integer k, tag, fieldsTerm l] ∧ TagV E tag ∧
      FieldsV E l := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨k, .atom "open", [], rfl, Or.inl rfl, by simp [FieldsV]⟩
  rcases wx.shape with rfl | rfl | ⟨k, y, z, rfl⟩ | ⟨h', lit, c', u, d, rfl⟩
  · cases h
  · cases h
  · obtain ⟨⟨k', tag, l, e, g, sl⟩, -⟩ := Bdd.leaf_iff.mp wx
    exact ⟨k', tag, l, e, g, sl⟩
  · simp at h

/-- A non-empty map literal holds maps with any value of its field at a key. -/
theorem lit_values (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)} (a : String)
    {w₀ : MW V} (h₀ : MSem den tag l w₀) (o : Option V) :
    FieldSem den (fieldAt tag l a) o ↔ ∃ w, MSem den tag l w ∧ w (.atom a) = o := by
  constructor
  · intro ho
    refine ⟨setK a o w₀, (msem_at ef g l a _).mpr ⟨by simpa [setK] using ho, ?_⟩, by simp [setK]⟩
    rw [eraseK_setK]; exact ((msem_at ef g l a w₀).mp h₀).2
  · rintro ⟨w, hw, rfl⟩
    exact ((msem_at ef g l a w).mp hw).1

/-- `map_fetch_key_static/3` on a map field: `:badmap` when it is empty, otherwise the field of the values at a key of
its maps. -/
theorem mstatic_fetch (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) (a : String) :
    ∃ res, Elixir.Module.Types.Descr.«map_fetch_key_static/3» (D (n + 3)) (.map X) (.atom a) (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        (FieldValue E res ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∀ o, FieldSem den res o ↔ ∃ w, denMF E den b w = Bool.true ∧ w (.atom a) = o)) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 3)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 3) (by omega)
    cases e
    · -- Not empty: a map of the literal.
      have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 3) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      refine ⟨fieldAt tag l a, ?_, Or.inr ⟨fieldAt_ok ef g sl a, ⟨w₀, (sem w₀).mpr h₀⟩, fun o => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_fetch_key_static/3»
        have ff := find_val (E := E) a sl
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom,
          Elixir.Module.Types.Descr.«map_fetch_field/3», ff, fieldAt]
        cases h : mapLookup l (.atom a) <;> simp [key_tag_field g]
      · rw [lit_values ef g a h₀]
        exact ⟨fun ⟨w, hw, e⟩ => ⟨w, (sem w).mpr hw, e⟩, fun ⟨w, hw, e⟩ => ⟨w, (sem w).mp hw, e⟩⟩
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_fetch_key_static/3»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 3) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl (m := n + 3) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_fetch_key_static/3»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Lynx.Term.isMember, Term.list]
        · simp [getMapKeys_single, hb, rl, Lynx.Term.isMember, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Lynx.Term.isMember, Term.list]
      · cases h : denMF E den b w
        · rfl
        · simpa using (inB w).mp h
    | cons L rest =>
      obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn a (L :: rest) hl
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨F, ?_, Or.inr ⟨hF, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, fun o => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_fetch_key_static/3»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, rF, Term.list]
        · simp [getMapKeys_single, hb, rl, rF, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, rF, Term.list]
      · rw [sF]
        constructor
        · rintro ⟨L', mL', w, hw, rfl⟩
          exact ⟨w, (inB w).mpr ⟨L', mL', hw⟩, rfl⟩
        · rintro ⟨w, hw, rfl⟩
          obtain ⟨L', mL', hL'⟩ := (inB w).mp hw
          exact ⟨L', mL', w, hL', rfl⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Maps of values in the map field of a type. -/
def MT (t : Term) (n : Nat) (X : List (Term × Term)) (w : MW (level t n).V) : Prop :=
  ∃ b, mapLookup X (.atom "map") = some b ∧ denMF (level t n).E (level t n).den b w = Bool.true

/-- Types of maps only, with some map. -/
def MOnly (t : Term) (n : Nat) (X : List (Term × Term)) : Prop :=
  (∀ v : PN t n, denD (.map X) v → v.1.1 = "map") ∧ ∃ w, MT t n X w

/-- The point of the next level of a map of values. -/
noncomputable def mpt (w : MW (level t n).V) : PN t n :=
  ⟨("map", (0, .nil, valM (level t n).E (level t n).den w)), by simp [names],
    ⟨valM_resp w, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun _ => ⟨w, rfl⟩,
      fun h => by simp at h⟩⟩

theorem denD_mpt {X : List (Term × Term)} (w : MW (level t n).V) : denD (.map X) (mpt (t := t) (n := n) w) ↔ MT t n X w := by
  rw [denD_map]
  simp only [mpt]
  cases h : mapLookup X (.atom "map") with
  | none => simp [MT, h, dn_none]
  | some b => simp [MT, h, dn_mapW (E := (level t n).E) (den := (level t n).den) (p := (0, .nil, valM _ _ w)) rfl]

theorem pt_map (v : PN t n) (h : v.1.1 = "map") :
    ∃ w, ∀ X : List (Term × Term), (denD (.map X) v ↔ MT t n X w) := by
  obtain ⟨⟨name, p⟩, mem, ok⟩ := v
  simp only at h
  subst h
  obtain ⟨w, hw⟩ := ok.2.2.2.2.1 rfl
  refine ⟨w, fun X => ?_⟩
  rw [denD_map]
  simp only
  cases hb : mapLookup X (.atom "map") with
  | none => simp [MT, hb, dn_none]
  | some b => simp [MT, hb, dn_mapW (E := (level t n).E) (den := (level t n).den) hw]

/-- A map without its map field. -/
def rmM (X : List (Term × Term)) : List (Term × Term) :=
  X.filter fun entry => !decide (compareExact (fuel (.atom "map") entry.1) (.atom "map") entry.1 = .eq)

theorem lookup_rmM (X : List (Term × Term)) (name : String) :
    mapLookup (rmM X) (.atom name) = if name = "map" then none else mapLookup X (.atom name) := by
  simp only [rmM, mapLookup_remove]
  by_cases h : name = "map" <;> simp [h]

theorem rest_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) :
    DE (level t n).E (.map (rmM X)) ∧ ∀ v : PN t n, denD (.map (rmM X)) v ↔ denD (.map X) v ∧ v.1.1 ≠ "map" := by
  have sX := de_map hX
  refine ⟨Or.inr ⟨_, rfl, fun q h => ?_, fun name x h => ?_⟩, fun v => ?_⟩
  · have : (mapLookup X q).isSome := by
      simp only [rmM, mapLookup_remove] at h
      split at h
      · simp at h
      · exact h
    exact sX.keys q this
  · rw [lookup_rmM] at h
    split at h
    · cases h
    · exact sX.fields name x h
  · rw [denD_map, denD_map, lookup_rmM]
    by_cases h : v.1.1 = "map"
    · simp [h, dn_none]
    · simp [h]

/-- `map_fetch_key/2` on static types of the next level: types holding only maps, all of them with the key, give the
type of their values there; types holding a map without the key give `:badkey`, and others `:badmap`. -/
theorem fetch_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (a : String) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) : ∃ res, Elixir.Module.Types.Descr.«map_fetch_key/2» (D m) (.map X) (.atom a) = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        (res = .atom "badkey" ∧ MOnly t n X ∧ ∃ w, MT t n X w ∧ w (.atom a) = none) ∨
        ∃ e, res = .tuple #[.atom "false", e] ∧ (level t n).E e ∧ MOnly t n X ∧
          (∀ w, MT t n X w → ∃ x, w (.atom a) = some x ∧ (level t n).den e x) ∧
          (∀ x, (level t n).den e x → ∃ w, MT t n X w ∧ w (.atom a) = some x)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_fetch_key/2».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 3))
      (.function false "Elixir.Module.Types.Descr" "-map_fetch_key/2-fun-0-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_fetch_key/2-fun-0-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_fetch_key/2-fun-0-/1».pure]
  cases hb : mapLookup X (.atom "map") with
  | none =>
    refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso, bad,
      Elixir.Module.Types.Descr.«-map_fetch_key/2-fun-0-/1»]
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
    obtain ⟨dR, sR⟩ := rest_map hX
    have rE := next_empty dR (m := k + 3) (by omega)
    have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have only : MOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmM X)) v) ∧
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), w, (mt w).mp hw⟩
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), w, (mt w).mpr hw⟩
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 3)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨hF, ⟨w₀, hw₀⟩, sF⟩⟩ := mstatic_fetch (level t n).ef (n := k) (by omega) hb fb a
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_fetch_key/2-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      obtain ⟨ty, opt, rfl, hty⟩ := hF
      have ok : MOnly t n X := only.mpr ⟨restE, w₀, hw₀⟩
      obtain ⟨eb, reb, seb⟩ := (level t n).ef.empty_pub hty
      cases opt
      · cases eb
        · refine ⟨_, ?_, Or.inr (Or.inr ⟨ty, rfl, hty, ok, fun w hw => ?_, fun x hx => ?_⟩)⟩
          · simp [key, mo, run, Lynx.Except.andAlso, reb (k + 3) (by omega), Lynx.Except.orElse, Lynx.Term.isMember,
              boolAtom]
          · have := (sF (w (.atom a))).mpr ⟨w, (mt w).mp hw, rfl⟩
            rw [fieldSem_mk] at this
            rcases this with ⟨-, h⟩ | ⟨x, hx, hd⟩
            · cases h
            · exact ⟨x, hx, hd⟩
          · obtain ⟨w, hw, e⟩ := (sF (some x)).mp ((fieldSem_mk (opt := Bool.false)).mpr (Or.inr ⟨x, rfl, hx⟩))
            exact ⟨w, (mt w).mpr hw, e⟩
        · exfalso
          have := (sF (w₀ (.atom a))).mpr ⟨w₀, hw₀, rfl⟩
          rw [fieldSem_mk] at this
          rcases this with ⟨-, h⟩ | ⟨x, -, hd⟩
          · cases h
          · exact seb.mp rfl x hd
      · refine ⟨.atom "badkey", ?_, Or.inr (Or.inl ⟨rfl, ok, ?_⟩)⟩
        · simp [key, mo, run, Lynx.Except.andAlso, Lynx.Except.orElse, Lynx.Term.isMember, boolAtom]
        · obtain ⟨w, hw, e⟩ := (sF none).mp ((fieldSem_mk (opt := Bool.true)).mpr (Or.inl ⟨rfl, rfl⟩))
          exact ⟨w, (mt w).mpr hw, e⟩
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_fetch_key/2-fun-0-/1», boolAtom]

theorem ukeysort_one (x : Term) : Erlang.lists.«ukeysort/2» (.integer 1) (.cons x .nil) = .ok (.cons x .nil) := by
  rw [Erlang.lists.«ukeysort/2».eq_def]
  simp [Erlang.erlang.«>/2», Erlang.erlang.«and/2», Lynx.Except.guard, Lynx.Except.tryWith]
  rfl

/-- `open_map/1` of one required key is the open literal of that field. -/
theorem open_map_run (a : String) {v : Term} (hv : Static v) (m : Nat) : ∃ k : Int,
    Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[.atom a, .tuple #[v, .atom "false"]]]) =
      .ok (.map [(.atom "map", .tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[v, .atom "false"])]])]) ∧
    KeyOk (.tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[v, .atom "false"])]]) := by
  obtain ⟨k, leaf, key⟩ := leaf_new_key "open" (Or.inl rfl) [.tuple #[.atom a, .tuple #[v, .atom "false"]]]
  refine ⟨k, ?_, key⟩
  simp only [Elixir.Module.Types.Descr.«open_map/1», Elixir.Module.Types.Descr.«map_descr/2»,
    Elixir.Module.Types.Descr.«map_descr_pairs/1»]
  simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure,
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_atom/1», Erlang.erlang.«is_boolean/1»,
    Elixir.Module.Types.Descr.«map_descr_pair/4», split_static hv, Lynx.Except.orElse, Lynx.Except.andAlso,
    Erlang.erlang.«==/2», ukeysort_one, Elixir.Module.Types.Descr.«map_descr_static/3», Elixir.Module.Types.Descr.«map_new/2»]
  simp only [Term.list] at leaf
  simp [fieldsTerm, Term.list, leaf]

/-- A map type of a single map field. -/
theorem mfused_de {x : Term} (hx : MField (level t n).E x) : DE (level t n).E (.map [(.atom "map", x)]) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil, equalExact_eq_decide] at h
    by_cases e : compareExact (fuel q (.atom "map")) q (.atom "map") = .eq
    · exact ⟨"map", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · simp [e] at h
  · simp only [mapLookup, List.find?_cons, List.find?_nil, compareExact_eq_atom, Term.atom.injEq, equalExact_eq_decide] at h
    by_cases e : name = "map"
    · subst e
      simp at h
      subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hx⟩))))
    · simp [e] at h

theorem fieldsV_req {a : String} {e : Term} (he : (level t n).E e) :
    FieldsV (level t n).E [(.atom a, .tuple #[e, .atom "false"])] :=
  ⟨fun x mx => by simp at mx; subst mx; exact ⟨⟨a, rfl⟩, ⟨e, Bool.false, rfl, he⟩⟩, by simp⟩

/-- The maps of an open literal of one required key. -/
theorem mt_open_at {e : Term} (he : (level t n).E e) (a : String) (k : Int) (w : MW (level t n).V) :
    MT t n [(.atom "map", .tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[e, .atom "false"])]])] w ↔
      ∃ x, w (.atom a) = some x ∧ (level t n).den e x := by
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left', equalExact_eq_decide]
  rw [denMF_leaf (level t n).ef (fieldsV_req he) (Or.inl rfl), msem_at (level t n).ef (Or.inl rfl) _ a]
  have er : eraseKey a [(.atom a, .tuple #[e, .atom "false"])] = [] := by simp [eraseKey]
  rw [er]
  simp only [fieldAt, lookup_cons_atom, ite_true, Option.getD_some, msem_open_nil, and_true]
  rw [show Term.atom "false" = boolAtom Bool.false from rfl, fieldSem_mk]
  simp

/-- The top map type, as `open_map/0` builds it. -/
theorem mapTop_de : DE (level t n).E (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) :=
  mfused_de (Or.inl ⟨_, rfl⟩)

theorem mapTop_den (v : PN t n) :
    denD (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) v ↔ v.1.1 = "map" := by
  rw [denD_map]
  by_cases h : v.1.1 = "map"
  · simp [mapLookup, h, dn_map, denO_top]
  · simp [mapLookup, h, dn_none]

theorem fetch_map_term (d : Dispatcher) (a : String) :
    Elixir.Module.Types.Descr.«map_fetch_key/2» d (.atom "term") (.atom a) = .ok (.atom "badmap") := by
  rw [Elixir.Module.Types.Descr.«map_fetch_key/2».eq_def]
  rfl

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem fieldValue_den {F : Term} (hF : FieldValue E F) :
    ∃ t, E t ∧ (∃ o, F = .tuple #[t, o]) ∧ ∀ x, den t x ↔ FieldSem den F (some x) := by
  obtain ⟨t, o, rfl, ht⟩ := hF
  exact ⟨t, ht, ⟨_, rfl⟩, fun x => by rw [fieldSem_mk]; simp⟩

/-- `map_get_keys/3` unites the values at atom keys of the maps of non-empty lines. -/
theorem get_keys (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (rs : List Term) (hr : ∀ r ∈ rs, ∃ s, r = .atom s)
    {acc : Term} (ha : E acc) :
    ∃ T, Elixir.Module.Types.Descr.«map_get_keys/3» (D (n + 4)) (Term.list lines) (Term.list rs) acc = .ok T ∧
      E T ∧ ∀ x, den T x ↔ den acc x ∨ ∃ s, .atom s ∈ rs ∧ ∃ L ∈ lines, LongM den L s (some x) := by
  obtain ⟨T, ⟨hT, sT⟩, run⟩ := foldl_rel_at (m := n + 4) "Elixir.Module.Types.Descr" "-map_get_keys/3-fun-0-"
    #[Term.list lines] (fun pre a => E a ∧ ∀ x, den a x ↔ den acc x ∨ ∃ s, .atom s ∈ pre ∧ ∃ L ∈ lines, LongM den L s (some x))
    rs (fun pre r a mr ⟨ha', sa⟩ => by
      obtain ⟨s, rfl⟩ := hr r mr
      obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn s lines hl
      obtain ⟨t, ht, ⟨o, rfl⟩, st⟩ := fieldValue_den (den := den) hF
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] ht ha' (m := n + 3) (by omega)
      refine ⟨c, ⟨hc, fun x => ?_⟩, ?_⟩
      · rw [sc, sa, st, sF]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | h | ⟨s', m', h⟩)
          · exact Or.inr ⟨s, Or.inr rfl, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨s', Or.inl m', h⟩
        · rintro (h | ⟨s', m' | e, h⟩)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨s', m', h⟩)
          · cases e; exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get_keys/3-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-map_get_keys/3-fun-0-/3», rF, Elixir.Module.Types.Descr.«opt_union/2», rc])
    acc ⟨ha, fun x => by simp⟩
  exact ⟨T, by simpa [Elixir.Module.Types.Descr.«map_get_keys/3»] using run, hT, sT⟩

theorem is_list_fieldsTerm (l : List (Term × Term)) : Erlang.erlang.«is_list/1» (fieldsTerm l) = .ok (.atom "true") := by
  cases l <;> simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1»]

/-- The type a tag gives the keys of a kind, as `map_get_domain/3` computes it. -/
theorem tag_type_run {tag : Term} (g : TagV E tag) (s : String) (d : Dispatcher) (f n acc : Term) :
    Elixir.Module.Types.Descr.«-map_get_domain/3-fun-0-/3» d (.atom s) (.tuple #[tag, f, n]) acc =
      Elixir.Module.Types.Descr.«opt_union/2» d (tagType tag s) acc := by
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · simp [Elixir.Module.Types.Descr.«-map_get_domain/3-fun-0-/3», tagType]
  · simp [Elixir.Module.Types.Descr.«-map_get_domain/3-fun-0-/3», tagType]
  · have fd := find_dom s dv
    have ne := fieldsTerm_ne_atom dl
    have il := is_list_fieldsTerm dl
    rw [tagType_dom]
    generalize fieldsTerm dl = T at fd ne il
    rw [Elixir.Module.Types.Descr.«-map_get_domain/3-fun-0-/3».eq_def]
    simp only
    split
    · exact absurd rfl (ne _)
    · exact absurd rfl (ne _)
    · simp [il, Elixir.Module.Types.Descr.«fields_get/3», fd]
      cases mapLookup dl (.atom s) <;> rfl

/-- Values of a kind that the tag of a line allows. -/
def LineTag (den : Term → V → Prop) (L : Term) (s : String) (x : V) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    den (tagType tag s) x

/-- `map_get_domain/3` folded over kinds unites the types the tags of lines give them. -/
theorem get_domains (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (ds : List Term) (hd : ∀ d ∈ ds, ∃ s, d = .atom s) {acc : Term} (ha : E acc) :
    ∃ T, Erlang.lists.«foldl/3» (D (n + 4))
        (.function false "Elixir.Module.Types.Descr" "-map_get_static_dnf/3-fun-0-" 2 #[Term.list lines]) acc (Term.list ds) =
          .ok T ∧ E T ∧ ∀ x, den T x ↔ den acc x ∨ ∃ s, .atom s ∈ ds ∧ ∃ L ∈ lines, LineTag den L s x := by
  obtain ⟨T, ⟨hT, sT⟩, run⟩ := foldl_rel_at (m := n + 4) "Elixir.Module.Types.Descr" "-map_get_static_dnf/3-fun-0-"
    #[Term.list lines] (fun pre a => E a ∧ ∀ x, den a x ↔ den acc x ∨ ∃ s, .atom s ∈ pre ∧ ∃ L ∈ lines, LineTag den L s x)
    ds (fun pre r a mr ⟨ha', sa⟩ => by
      obtain ⟨s, rfl⟩ := hd r mr
      obtain ⟨c, ⟨hc, sc⟩, rc⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr" "-map_get_domain/3-fun-0-"
        #[.atom s] (fun pre' a' => E a' ∧ ∀ x, den a' x ↔ den a x ∨ ∃ L ∈ pre', LineTag den L s x) lines
        (fun pre' L b mL ⟨hb, sb⟩ => by
          obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl L mL
          have hty := tagType_value ef.mopsE g s
          obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hty hb (m := n + 2) (by omega)
          refine ⟨c, ⟨hc, fun x => ?_⟩, ?_⟩
          · rw [sc, sb]
            simp only [List.mem_append, List.mem_singleton]
            constructor
            · rintro (h | h | ⟨L', m', h⟩)
              · exact Or.inr ⟨_, Or.inr rfl, tag, l, negs, rfl, h⟩
              · exact Or.inl h
              · exact Or.inr ⟨L', Or.inl m', h⟩
            · rintro (h | ⟨L', m' | e, h⟩)
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr ⟨L', m', h⟩)
              · subst e
                obtain ⟨tag', l', negs', e', h'⟩ := h
                obtain ⟨rfl, -, -⟩ := tuple3_inj e'
                exact Or.inl h'
          · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get_domain/3-fun-0-/2».pure,
              tag_type_run g s, Elixir.Module.Types.Descr.«opt_union/2», rc])
        a ⟨ha', fun x => by simp⟩
      refine ⟨c, ⟨hc, fun x => ?_⟩, ?_⟩
      · rw [sc, sa]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro ((h | ⟨s', m', h⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨s', Or.inl m', h⟩
          · exact Or.inr ⟨s, Or.inr rfl, h⟩
        · rintro (h | ⟨s', m' | e, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr ⟨s', m', h⟩)
          · cases e; exact Or.inr h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get_static_dnf/3-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_get_static_dnf/3-fun-0-/3», Elixir.Module.Types.Descr.«map_get_domain/3»]
          using rc)
    acc ⟨ha, fun x => by simp⟩
  exact ⟨T, run, hT, sT⟩

/-! Keys of map BDDs outside a negated set of atoms. -/

/-- Literals whose field keys outside a negated set are among some keys. -/
def NegNamed (N new : List (Term × Term)) (t : Term) : Prop :=
  ∀ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] →
    ∀ s ∈ keyStrs l, mapLookup N (.atom s) = none → (.atom s, .atom "true") ∈ new

/-- Keys added outside a negated set of atoms. -/
def NegNew (N new : List (Term × Term)) : Prop :=
  ∀ e ∈ new, ∃ s, e = (.atom s, .atom "true") ∧ mapLookup N (.atom s) = none

theorem negNew_append {N a b : List (Term × Term)} (ha : NegNew N a) (hb : NegNew N b) : NegNew N (a ++ b) :=
  fun e me => (List.mem_append.mp me).elim (ha e) (hb e)

theorem negNamed_mono {N a b : List (Term × Term)} (h : ∀ e ∈ a, e ∈ b) {t : Term} (ht : NegNamed N a t) :
    NegNamed N b t :=
  fun k tag l e s ms ns => h _ (ht k tag l e s ms ns)

/-- `orddict:fold/3` over fields adds their keys outside a negated set. -/
theorem neg_fold (N : List (Term × Term)) (m : Nat) : ∀ (l : List (Term × Term)), FieldsV E l → ∀ es,
    ∃ new, Erlang.orddict.«fold/3» (D m)
        (.function false "Elixir.Module.Types.Descr" "-map_keys_from_negated_set/2-fun-0-" 3 #[.map N]) (.map es)
        (fieldsTerm l) = .ok (.map (new ++ es)) ∧ NegNew N new ∧
      ∀ s ∈ keyStrs l, mapLookup N (.atom s) = none → (.atom s, .atom "true") ∈ new
  | [], _, es => ⟨[], by rw [Erlang.orddict.«fold/3».eq_def]; simp [fieldsTerm, Term.list,
      Erlang.erlang.«is_function/2»], by simp [NegNew], by simp [keyStrs]⟩
  | (k, v) :: t, sl, es => by
    obtain ⟨⟨b, rfl⟩, ty, o, rfl, -⟩ := sl.1 _ List.mem_cons_self
    have step : Elixir.Module.Types.Descr.«-map_keys_from_negated_set/2-fun-0-/4» (.map N) (.atom b)
        (.tuple #[ty, boolAtom o]) (.map es) =
          .ok (.map (if (mapLookup N (.atom b)).isSome then es else (.atom b, .atom "true") :: es)) := by
      cases h : (mapLookup N (.atom b)).isSome <;>
        simp [Elixir.Module.Types.Descr.«-map_keys_from_negated_set/2-fun-0-/4», Erlang.sets.«is_element/2», h,
          Lynx.Term.isMember, Erlang.maps.«put/3», Term.true, Term.false]
    obtain ⟨new, run, hn, hk⟩ := neg_fold N m t (fieldsV_tail sl)
      (if (mapLookup N (.atom b)).isSome then es else (.atom b, .atom "true") :: es)
    cases h : (mapLookup N (.atom b)).isSome
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at run
      refine ⟨new ++ [(.atom b, .atom "true")], ?_, negNew_append hn fun e me => ?_, fun s ms ns => ?_⟩
      · rw [Erlang.orddict.«fold/3».eq_def]
        simp [fieldsTerm_cons, Erlang.program.«Elixir.Module.Types.Descr:-map_keys_from_negated_set/2-fun-0-/3».pure,
          step, h, run]
      · simp at me; subst me; exact ⟨b, rfl, by simpa using h⟩
      · simp only [keyStrs, List.filterMap_cons, List.mem_cons] at ms
        rcases ms with rfl | ms
        · simp
        · exact List.mem_append_left _ (hk s ms ns)
    · simp only [h, ↓reduceIte] at run
      refine ⟨new, ?_, hn, fun s ms ns => ?_⟩
      · rw [Erlang.orddict.«fold/3».eq_def]
        simp [fieldsTerm_cons, Erlang.program.«Elixir.Module.Types.Descr:-map_keys_from_negated_set/2-fun-0-/3».pure,
          step, h, run]
      · simp only [keyStrs, List.filterMap_cons, List.mem_cons] at ms
        rcases ms with rfl | ms
        · rw [ns] at h; cases h
        · exact hk s ms ns

theorem neg_leaf (N : List (Term × Term)) (m : Nat) {t : Term} (ht : MapLitV E t) (es : List (Term × Term)) :
    ∃ new, Lynx.Dispatcher.pure (D (m + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_keys_from_negated_set/2-fun-1-" 2 #[.map N]) #[t, .map es] =
          .ok (.map (new ++ es)) ∧ NegNew N new ∧ NegNamed N new t := by
  obtain ⟨k, tag, l, rfl, -, sl⟩ := ht
  obtain ⟨new, run, hn, hk⟩ := neg_fold N m l sl es
  refine ⟨new, ?_, hn, fun k' tag' l' e s ms ns => ?_⟩
  · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_keys_from_negated_set/2-fun-1-/2».pure]
    simpa [Elixir.Module.Types.Descr.«-map_keys_from_negated_set/2-fun-1-/3»] using run
  · obtain ⟨-, -, e₃⟩ := tuple3_inj e
    rw [← fieldsTerm_inj e₃] at ms
    exact hk s ms ns

/-- `bdd_reduce/3` collects the field keys of a map BDD outside a negated set. -/
theorem neg_reduce (N : List (Term × Term)) (m : Nat) {b : Term} (wb : Bdd (MLit E) b) :
    ∀ es, ∃ new, Elixir.Module.Types.Descr.«bdd_reduce/3» (D (m + 1)) b (.map es)
        (.function false "Elixir.Module.Types.Descr" "-map_keys_from_negated_set/2-fun-1-" 2 #[.map N]) =
          .ok (.map (new ++ es)) ∧ NegNew N new ∧ Bdd (fun t => MLit E t ∧ NegNamed N new t) b := by
  refine Bdd.induction (P := fun ok b => (∀ t, ok t → MLit E t) → ∀ es, ∃ new,
      Elixir.Module.Types.Descr.«bdd_reduce/3» (D (m + 1)) b (.map es)
        (.function false "Elixir.Module.Types.Descr" "-map_keys_from_negated_set/2-fun-1-" 2 #[.map N]) =
          .ok (.map (new ++ es)) ∧ NegNew N new ∧ Bdd (fun t => ok t ∧ NegNamed N new t) b)
    ?_ ?_ ?_ ?_ (MLit E) b wb (fun _ h => h)
  · intro ok _ es
    exact ⟨[], by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simp, by simp [NegNew], by simp [Bdd]⟩
  · intro ok _ es
    exact ⟨[], by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simp, by simp [NegNew], by simp [Bdd]⟩
  · intro ok k x y okl lit es
    obtain ⟨new, run, hn, hk⟩ := neg_leaf N m (lit _ okl).1 es
    exact ⟨new, by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simpa using run, hn,
      Bdd.leaf_iff.mpr ⟨okl, hk⟩⟩
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id lits es
    have lits' : ∀ t, Above ok lit t → MLit E t := fun t ht => lits t ht.1
    obtain ⟨n₀, r₀, h₀, k₀⟩ := neg_leaf N m (lits _ okl).1 es
    obtain ⟨n₁, r₁, h₁, k₁⟩ := ic lits' (n₀ ++ es)
    obtain ⟨n₂, r₂, h₂, k₂⟩ := iu lits' (n₁ ++ (n₀ ++ es))
    obtain ⟨n₃, r₃, h₃, k₃⟩ := id lits' (n₂ ++ (n₁ ++ (n₀ ++ es)))
    refine ⟨n₃ ++ n₂ ++ n₁ ++ n₀, ?_, negNew_append (negNew_append (negNew_append h₃ h₂) h₁) h₀, ?_⟩
    · rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]
      simp [r₀, r₁, r₂, r₃]
    · have lift : ∀ (n' : List (Term × Term)), (∀ e ∈ n', e ∈ n₃ ++ n₂ ++ n₁ ++ n₀) →
          ∀ t, (Above ok lit t ∧ NegNamed N n' t) → Above (fun t => ok t ∧ NegNamed N (n₃ ++ n₂ ++ n₁ ++ n₀) t) lit t :=
        fun n' sub t ⟨⟨o, lt⟩, nt⟩ => ⟨⟨o, negNamed_mono sub nt⟩, lt⟩
      exact Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, negNamed_mono (fun e me => by simp [me]) k₀⟩,
        k₁.mono (lift n₁ (fun e me => by simp [me])), k₂.mono (lift n₂ (fun e me => by simp [me])), k₃.mono (lift n₃ (fun e me => by simp [me]))⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {V : Type} {den : Term → V → Prop}

/-- A map of values with one key set. -/
def setW (κ : MKey) (o : Option V) (w : MW V) : MW V := fun k => if k = κ then o else w k

/-- A literal holding a map with either of two keys set holds the map itself. -/
theorem msem_two {tag : Term} {l : List (Term × Term)} {w : MW V} {κ₁ κ₂ : MKey} (ne : κ₁ ≠ κ₂) {o : Option V}
    (h₁ : MSem den tag l (setW κ₁ o w)) (h₂ : MSem den tag l (setW κ₂ o w)) : MSem den tag l w := by
  rw [msem_keys] at h₁ h₂ ⊢
  intro κ
  by_cases e : κ = κ₁
  · subst e; simpa [setW, ne] using h₂ κ
  · simpa [setW, e] using h₁ κ

theorem nsem_two {N : Term} {w : MW V} {κ₁ κ₂ : MKey} (ne : κ₁ ≠ κ₂) {o : Option V}
    (h₁ : NSem den N (setW κ₁ o w)) (h₂ : NSem den N (setW κ₂ o w)) : NSem den N w := by
  obtain ⟨k, tag, l, rfl, m₁⟩ := h₁
  obtain ⟨k', tag', l', e, m₂⟩ := h₂
  obtain ⟨-, rfl, e₃⟩ := tuple3_inj e
  rw [← fieldsTerm_inj e₃] at m₂
  exact ⟨k, tag, l, rfl, msem_two ne m₁ m₂⟩

/-- Negated literals miss a map with one of many keys set, when they miss the map. -/
theorem survive_set {w : MW V} (o : Option V) : ∀ (Ns : List Term), (∀ N ∈ Ns, ¬NSem den N w) →
    ∀ (C : List MKey), C.Nodup → Ns.length < C.length → ∃ κ ∈ C, ∀ N ∈ Ns, ¬NSem den N (setW κ o w) := by
  intro Ns
  induction Ns with
  | nil =>
    intro _ C _ len
    cases C with
    | nil => simp at len
    | cons κ _ => exact ⟨κ, List.mem_cons_self, by simp⟩
  | cons N rest ih =>
    intro out C nd len
    have out' := fun N' (m : N' ∈ rest) => out N' (List.mem_cons_of_mem _ m)
    by_cases killed : ∃ κ₀ ∈ C, NSem den N (setW κ₀ o w)
    · obtain ⟨κ₀, mκ₀, h₀⟩ := killed
      obtain ⟨κ, mκ, hκ⟩ := ih out' (C.erase κ₀) (nd.erase κ₀) (by rw [List.length_erase_of_mem mκ₀]; simp at len; omega)
      have ne : κ ≠ κ₀ := fun e => by subst e; exact (List.Nodup.not_mem_erase nd) mκ
      refine ⟨κ, List.mem_of_mem_erase mκ, fun N' mN' => ?_⟩
      rcases List.mem_cons.mp mN' with rfl | m
      · exact fun h => out N' List.mem_cons_self (nsem_two ne h h₀)
      · exact hκ N' m
    · obtain ⟨κ, mκ, hκ⟩ := ih out' C nd (by simp at len; omega)
      refine ⟨κ, mκ, fun N' mN' => ?_⟩
      rcases List.mem_cons.mp mN' with rfl | m
      · exact fun h => killed ⟨κ, mκ, h⟩
      · exact hκ N' m

/-- Values a literal allows at one of many keys occur at one of them in a map of a non-empty line. -/
theorem line_witness {tag : Term} {l : List (Term × Term)} {negs : List Term} {w₀ : MW V}
    (h₀ : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w₀) {x : V} (C : List MKey) (nd : C.Nodup)
    (len : negs.length < C.length) (hC : ∀ κ ∈ C, KeyAllow den tag l κ (some x)) :
    ∃ κ ∈ C, ∃ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w ∧ w κ = some x := by
  obtain ⟨hm, hn⟩ := inMLine_iff.mp h₀
  obtain ⟨κ, mκ, out⟩ := survive_set (some x) negs hn C nd len
  refine ⟨κ, mκ, setW κ (some x) w₀, inMLine_iff.mpr ⟨msem_keys.mpr fun κ' => ?_, out⟩, by simp [setW]⟩
  by_cases e : κ' = κ
  · subst e; simpa [setW] using hC κ' mκ
  · simpa [setW, e] using msem_keys.mp hm κ'

/-- A map of values with two atom keys swapped. -/
def swapW (s c : String) (w : MW V) : MW V :=
  fun k => if k = .atom s then w (.atom c) else if k = .atom c then w (.atom s) else w k

theorem swapW_swapW (s c : String) (w : MW V) : swapW s c (swapW s c w) = w := by
  funext k
  by_cases hs : k = .atom s
  · subst hs; by_cases e : s = c
    · subst e; simp [swapW]
    · simp [swapW, Ne.symm e]
  · by_cases hc : k = .atom c
    · subst hc; simp [swapW, hs]
    · simp [swapW, hs, hc]

/-- Literals that mention neither of two atom keys hold maps with the keys swapped. -/
theorem msem_swapW {s c : String} {tag : Term} {l : List (Term × Term)} (hs : mapLookup l (.atom s) = none)
    (hc : mapLookup l (.atom c) = none) {w : MW V} (h : MSem den tag l w) : MSem den tag l (swapW s c w) := by
  refine ⟨fun a => ?_, fun k i => by simpa [swapW] using h.doms k i⟩
  by_cases ha : a = s
  · subst ha
    have := h.atoms c
    unfold FSem at this ⊢
    rw [hc] at this; rw [hs]
    simpa [swapW] using this
  · by_cases hc' : a = c
    · subst hc'
      have := h.atoms s
      unfold FSem at this ⊢
      rw [hs] at this; rw [hc]
      simpa [swapW, ha] using this
    · simpa [swapW, ha, hc'] using h.atoms a

theorem msem_swapW_iff {s c : String} {tag : Term} {l : List (Term × Term)} (hs : mapLookup l (.atom s) = none)
    (hc : mapLookup l (.atom c) = none) {w : MW V} : MSem den tag l (swapW s c w) ↔ MSem den tag l w :=
  ⟨fun h => by simpa [swapW_swapW] using msem_swapW hs hc h, msem_swapW hs hc⟩

theorem fresh_str (L : List String) : ∃ c, c ∉ L := by
  obtain ⟨c, mc⟩ : ∃ c, c ∈ freshStrs ((L.map String.length).foldr max 0) 1 := ⟨_, by simp [freshStrs]; rfl⟩
  exact ⟨c, fun m => by have := le_maxLen L c m; have := freshStrs_len mc; omega⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The keys a split of keys selects: its atoms, the atoms outside its negated set, if any, and the keys of its
domain kinds. -/
def SplitKey (rs : List Term) (neg : Term) (ds : List Term) : MKey → Prop
  | .atom s => .atom s ∈ rs ∨ ∃ N, neg = .map N ∧ mapLookup N (.atom s) = none
  | .dom k _ => .atom (domKind k) ∈ ds

/-- Splits of static keys: atoms, a negated set of atoms or `nil`, and domain kinds, with the atom kind exactly when
atoms are negated. -/
structure SplitOk (rs : List Term) (neg : Term) (ds : List Term) : Prop where
  hrs : ∀ r ∈ rs, ∃ s, r = .atom s
  hneg : neg = .atom "nil" ∨ ∃ N, neg = .map N
  hds : ∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s
  hatom : .atom "atom" ∈ ds ↔ ∃ N, neg = .map N

theorem domKind_of {s : String} (h : s ∈ domainKinds) (ne : s ≠ "atom") : ∃ k, domKind k = s := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl ne
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩

theorem domKind_ne_atom (k : Fin 11) : domKind k ≠ "atom" := by
  revert k; decide

/-- Values a tag allows at the keys of a kind are those of the type it gives them. -/
theorem tagSem_some (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) (kind : String) (x : V) :
    TagSem den tag kind (some x) ↔ den (tagType tag kind) x := by
  rcases g with rfl | rfl | ⟨dl, rfl, -⟩
  · simp [TagSem, tagType, ef.den_term]
  · simp [TagSem, tagType]
    exact fun h => ef.den_none x h
  · rw [tagSem_dom_iff (fun v h => ef.den_none v h), tagType_dom]
    cases mapLookup dl (.atom kind) <;> simp
    exact fun h' => ef.den_none x h'

def atomStrs (R : List Term) : List String := R.filterMap fun r => match r with
  | .atom s => some s
  | _ => none

theorem mem_atomStrs {R : List Term} {s : String} (h : .atom s ∈ R) : s ∈ atomStrs R :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- The keys of the fields of a line. -/
def lineKeys (L : Term) : List String :=
  match L with
  | .tuple ⟨[_, f, _]⟩ => keyStrs (domFields f)
  | _ => []

theorem lineKeys_eq (tag : Term) (l : List (Term × Term)) (negs : List Term) :
    lineKeys (.tuple #[tag, fieldsTerm l, Term.list negs]) = keyStrs l := by
  simp [lineKeys, domFields_fieldsTerm]

theorem lookup_entries_atom {es : List (Term × Term)} {s : String} {v : Term} (h : (Term.atom s, v) ∈ es) :
    .atom s ∈ (mapEntries es).map Prod.fst := by
  have hl : (mapLookup es (.atom s)).isSome := by
    rw [mapLookup]
    simp only [equalExact_eq_decide]
    cases e : es.find? (fun entry => decide (compareExact (fuel (.atom s) entry.1) (.atom s) entry.1 = .eq)) with
    | none => exact absurd h (by simpa using List.find?_eq_none.mp e (.atom s, v))
    | some _ => simp
  rw [← mapLookup_mapEntries, mapLookup] at hl
  simp only [equalExact_eq_decide] at hl
  cases e : (mapEntries es).find? (fun entry => decide (compareExact (fuel (.atom s) entry.1) (.atom s) entry.1 = .eq)) with
  | none => rw [e] at hl; cases hl
  | some r =>
    have mr := List.mem_of_find?_eq_some e
    have := List.find?_some e
    simp only [decide_eq_true_eq] at this
    exact List.mem_map.mpr ⟨r, mr, (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm this)⟩

/-- `map_keys_from_negated_set/2` on a map type: atoms outside the negated set, beyond which the maps of the type
hold the same values at any two atom keys outside the set. -/
theorem neg_keys (ef : EF nd E V den tl K) (N : List (Term × Term)) (m : Nat) {b : Term} (fb : MField E b) :
    ∃ R, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (m + 1)) (.map N) b = .ok (Term.list R) ∧
      (∀ r ∈ R, ∃ s, r = .atom s ∧ mapLookup N (.atom s) = none) ∧
      ∀ s c, mapLookup N (.atom s) = none → mapLookup N (.atom c) = none → .atom s ∉ R → .atom c ∉ R →
        ∀ w, denMF E den b (swapW s c w) = denMF E den b w := by
  rcases fb with ⟨k, rfl⟩ | wb
  · refine ⟨[], ?_, by simp, fun s c _ _ _ _ w => by rw [denMF_top, denMF_top]⟩
    simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», Elixir.Module.Types.Descr.«bdd_reduce/3»,
      Erlang.program.«Elixir.Module.Types.Descr:-map_keys_from_negated_set/2-fun-1-/2».pure,
      Elixir.Module.Types.Descr.«-map_keys_from_negated_set/2-fun-1-/3», Erlang.orddict.«fold/3»,
      Erlang.erlang.«is_function/2», Erlang.maps.«keys/1»]
  obtain ⟨new, run, hn, hk⟩ := neg_reduce N m wb []
  refine ⟨(mapEntries new).map Prod.fst, ?_, fun r mr => ?_, fun s c sN cN ns nc w => ?_⟩
  · simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2», run, Erlang.maps.«keys/1»]
  · obtain ⟨e, me, rfl⟩ := List.mem_map.mp mr
    obtain ⟨s, rfl, hs⟩ := hn e (mem_of_mem_mapEntries me)
    exact ⟨s, rfl, hs⟩
  · rw [denMF_bdd wb, denMF_bdd wb]
    refine eval_ext hk fun t ⟨lt, nt⟩ => ?_
    obtain ⟨k, tag, l, rfl, -, -⟩ := lt.1
    have fresh : ∀ a, mapLookup N (.atom a) = none → .atom a ∉ (mapEntries new).map Prod.fst →
        mapLookup l (.atom a) = none := fun a aN na =>
      lookup_fresh' fun ma => na (lookup_entries_atom (nt k tag l rfl a ma aN))
    have lit : MapLitV E (.tuple #[.integer k, tag, fieldsTerm l]) := lt.1
    rw [Bool.eq_iff_iff, valM_iff ef.mopsE ef.mdopsE ef.semR lit, valM_iff ef.mopsE ef.mdopsE ef.semR lit, nsem_lit,
      nsem_lit, msem_swapW_iff (fresh s sN ns) (fresh c cN nc)]

/-- Values at an atom key outside a negated set and the keys a map type names are values its lines allow at atoms
outside their fields. -/
theorem unnamed_tag (ef : EF nd E V den tl K) {b : Term} {N : List (Term × Term)} {R : List Term} (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w)
    (swap : ∀ s c, mapLookup N (.atom s) = none → mapLookup N (.atom c) = none → .atom s ∉ R → .atom c ∉ R →
      ∀ w, denMF E den b (swapW s c w) = denMF E den b w)
    {s : String} (sN : mapLookup N (.atom s) = none) (sR : .atom s ∉ R) {w : MW V} {x : V}
    (hw : denMF E den b w = Bool.true) (hx : w (.atom s) = some x) : ∃ L ∈ lines, LineTag den L "atom" x := by
  obtain ⟨c, hc⟩ := fresh_str (s :: keyStrs N ++ atomStrs R ++ lines.flatMap lineKeys)
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap, not_or] at hc
  obtain ⟨cs, ⟨cN, cR⟩, cL⟩ := hc
  have cN' : mapLookup N (.atom c) = none := lookup_fresh' cN
  have cR' : .atom c ∉ R := fun m => cR (mem_atomStrs m)
  have hw' : denMF E den b (swapW s c w) = Bool.true := by rw [swap s c sN cN' sR cR']; exact hw
  obtain ⟨L, mL, hL⟩ := (sl _).mp hw'
  obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl L mL
  have hm := (inMLine_iff.mp hL).1.atoms c
  have lc : mapLookup l (.atom c) = none := lookup_fresh' fun m => cL ⟨_, mL, by rw [lineKeys_eq]; exact m⟩
  unfold FSem at hm
  rw [lc] at hm
  have sw : swapW s c w (.atom c) = some x := by
    unfold swapW; simp [show MKey.atom c ≠ MKey.atom s from fun e => cs (MKey.atom.inj e), hx]
  rw [sw] at hm
  exact ⟨_, mL, tag, l, negs, rfl, (tagSem_some ef g "atom" x).mp hm⟩

/-- Values a line allows at the keys of a kind occur at such a key in a map of the line, outside a negated set of
atoms for the atom kind. -/
theorem tag_witness (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) (ne : ∃ w, InMLine den L w) {kind : String}
    (hk : kind ∈ domainKinds) {x : V} (hx : LineTag den L kind x) (N : List (Term × Term)) :
    ∃ w, InMLine den L w ∧ ∃ κ, ((kind = "atom" ∧ ∃ c, κ = .atom c ∧ mapLookup N (.atom c) = none) ∨
      ∃ k i, kind = domKind k ∧ κ = .dom k i) ∧ w κ = some x := by
  obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hL
  obtain ⟨tag', l', negs', e, hx⟩ := hx
  obtain ⟨rfl, -, -⟩ := tuple3_inj e
  obtain ⟨w₀, h₀⟩ := ne
  have hs := (tagSem_some ef g kind x).mpr hx
  by_cases ka : kind = "atom"
  · subst ka
    let M := ((keyStrs l ++ keyStrs N).map String.length).foldr max 0
    have fr : ∀ c ∈ freshStrs M (negs.length + 1), c ∉ keyStrs l ++ keyStrs N := fun c mc m => by
      have := le_maxLen _ c m; have := freshStrs_len mc; omega
    obtain ⟨κ, mκ, w, hw, wκ⟩ := line_witness h₀ ((freshStrs M (negs.length + 1)).map MKey.atom)
      (List.Pairwise.map MKey.atom (fun _ _ ne e => ne (MKey.atom.inj e)) (freshStrs_nodup M _)) (by simp [freshStrs_length]) fun κ mκ => by
        obtain ⟨c, mc, rfl⟩ := List.mem_map.mp mκ
        have lc : mapLookup l (.atom c) = none := lookup_fresh' fun m => fr c mc (List.mem_append_left _ m)
        show FSem den tag l c (some x)
        unfold FSem; rw [lc]; exact hs
    obtain ⟨c, mc, rfl⟩ := List.mem_map.mp mκ
    exact ⟨w, hw, .atom c, Or.inl ⟨rfl, c, rfl, lookup_fresh' fun m => fr c mc (List.mem_append_right _ m)⟩, wκ⟩
  · obtain ⟨k, rfl⟩ := domKind_of hk ka
    obtain ⟨κ, mκ, w, hw, wκ⟩ := line_witness h₀ ((List.range (negs.length + 1)).map (MKey.dom k))
      (List.Pairwise.map (MKey.dom k) (fun _ _ ne e => ne (MKey.dom.inj e).2) List.nodup_range) (by simp) fun κ mκ => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp mκ
        exact hs
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp mκ
    exact ⟨w, hw, .dom k i, Or.inr ⟨k, i, rfl, rfl⟩, wκ⟩

/-- The atoms `map_keys_from_negated_set/2` adds for a split: none without a negated set, otherwise atoms outside it
whose swaps with other such atoms leave the maps of the type unchanged. -/
theorem neg_keys_split (ef : EF nd E V den tl K) {b : Term} (fb : MField E b) (m : Nat) {rs : List Term} {neg : Term}
    {ds : List Term} (hs : SplitOk rs neg ds) :
    ∃ R, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (m + 1)) neg b = .ok (Term.list R) ∧
      (∀ r ∈ R, ∃ s, r = .atom s ∧ ∃ N, neg = .map N ∧ mapLookup N (.atom s) = none) ∧
      ∀ N, neg = .map N → ∀ s c, mapLookup N (.atom s) = none → mapLookup N (.atom c) = none → .atom s ∉ R →
        .atom c ∉ R → ∀ w, denMF E den b (swapW s c w) = denMF E den b w := by
  rcases hs.hneg with rfl | ⟨N, rfl⟩
  · exact ⟨[], by simp [Elixir.Module.Types.Descr.«map_keys_from_negated_set/2»], by simp, fun N e => by cases e⟩
  · obtain ⟨R, rR, hR, swR⟩ := neg_keys ef N m fb
    exact ⟨R, rR, fun r mr => let ⟨s, e, h⟩ := hR r mr; ⟨s, e, N, rfl, h⟩, fun N' e => by cases e; exact swR⟩

/-- The values a split selects in the maps of the non-empty lines of a type: those at its atoms and at the atoms
`map_keys_from_negated_set/2` adds, and those the tags of the lines give its kinds. -/
theorem pieces_sem (ef : EF nd E V den tl K) {b : Term} (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rs : List Term} {neg : Term}
    {ds : List Term} (hs : SplitOk rs neg ds) {R : List Term}
    (hR : ∀ r ∈ R, ∃ s, r = .atom s ∧ ∃ N, neg = .map N ∧ mapLookup N (.atom s) = none)
    (swR : ∀ N, neg = .map N → ∀ s c, mapLookup N (.atom s) = none → mapLookup N (.atom c) = none → .atom s ∉ R →
      .atom c ∉ R → ∀ w, denMF E den b (swapW s c w) = denMF E den b w) (x : V) :
    (((∃ s, .atom s ∈ rs ∧ ∃ L ∈ lines, LongM den L s (some x)) ∨
        ∃ s, .atom s ∈ R ∧ ∃ L ∈ lines, LongM den L s (some x)) ∨
      ∃ kind, .atom kind ∈ ds ∧ ∃ L ∈ lines, LineTag den L kind x) ↔
      ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey rs neg ds κ ∧ w κ = some x := by
  have hl' : ∀ L ∈ lines, MLine E L := fun L m => (hl L m).1
  constructor
  · rintro ((⟨s, ms, L, mL, w, hw, hx⟩ | ⟨s, ms, L, mL, w, hw, hx⟩) | ⟨kind, mk, L, mL, hx⟩)
    · exact ⟨w, (sl w).mpr ⟨L, mL, hw⟩, .atom s, Or.inl ms, hx⟩
    · obtain ⟨s', e, N, eN, hN⟩ := hR _ ms
      obtain rfl : s = s' := Term.atom.inj e
      exact ⟨w, (sl w).mpr ⟨L, mL, hw⟩, .atom s, Or.inr ⟨N, eN, hN⟩, hx⟩
    · obtain ⟨k₀, hk, ek⟩ := hs.hds _ mk
      cases ek
      obtain ⟨N, eN⟩ : ∃ N, (kind = "atom" → neg = .map N) := by
        by_cases ka : kind = "atom"
        · subst ka; obtain ⟨N, eN⟩ := hs.hatom.mp mk; exact ⟨N, fun _ => eN⟩
        · exact ⟨[], fun e => absurd e ka⟩
      obtain ⟨w, hw, κ, hκ, wκ⟩ := tag_witness ef (hl L mL).1 (hl L mL).2 hk hx N
      refine ⟨w, (sl w).mpr ⟨L, mL, hw⟩, κ, ?_, wκ⟩
      rcases hκ with ⟨ka, c, rfl, hc⟩ | ⟨k, i, rfl, rfl⟩
      · exact Or.inr ⟨N, eN ka, hc⟩
      · exact mk
  · rintro ⟨w, hw, κ, sk, hx⟩
    obtain ⟨L, mL, hL⟩ := (sl w).mp hw
    cases κ with
    | atom s =>
      rcases sk with ms | ⟨N, eN, hN⟩
      · exact Or.inl (Or.inl ⟨s, ms, L, mL, w, hL, hx⟩)
      · by_cases sR : .atom s ∈ R
        · exact Or.inl (Or.inr ⟨s, sR, L, mL, w, hL, hx⟩)
        · obtain ⟨L', mL', ht⟩ := unnamed_tag ef lines hl' sl (swR N eN) hN sR hw hx
          exact Or.inr ⟨"atom", hs.hatom.mpr ⟨N, eN⟩, L', mL', ht⟩
    | dom k i =>
      obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl' L mL
      have := (inMLine_iff.mp hL).1.doms k i
      rw [hx] at this
      exact Or.inr ⟨domKind k, sk, _, mL, tag, l, negs, rfl, (tagSem_some ef g _ x).mp this⟩

/-- `map_get_static_dnf/3` on the non-empty lines of a map type and a split of static keys unites the values its maps
hold at the keys the split selects. -/
theorem get_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {b : Term} (fb : MField E b) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rs : List Term} {neg : Term}
    {ds : List Term} (hs : SplitOk rs neg ds) :
    ∃ T, Elixir.Module.Types.Descr.«map_get_static_dnf/3» (D (n + 4)) b (Term.list lines)
        (.tuple #[Term.list rs, .nil, neg, Term.list ds, .nil]) = .ok T ∧ E T ∧
      ∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey rs neg ds κ ∧ w κ = some x := by
  have hl' : ∀ L ∈ lines, MLine E L := fun L m => (hl L m).1
  obtain ⟨T₂, r₂, h₂, s₂⟩ := get_keys ef hn lines hl rs hs.hrs ef.none
  obtain ⟨T₃, r₃, h₃, s₃⟩ := get_keys ef hn lines hl [] (by simp) h₂
  obtain ⟨R, rR, hR, swR⟩ := neg_keys_split ef fb (n + 3) hs
  obtain ⟨T₄, r₄, h₄, s₄⟩ := get_keys ef hn lines hl R (fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩) h₃
  obtain ⟨T₅, r₅, h₅, s₅⟩ := get_domains ef hn lines hl' ds (fun d md => let ⟨s, _, e⟩ := hs.hds d md; ⟨s, e⟩) h₄
  refine ⟨T₅, ?_, h₅, fun x => ?_⟩
  · have nil : Erlang.lists.«foldl/3» (D (n + 4))
        (.function false "Elixir.Module.Types.Descr" "-map_get_static_dnf/3-fun-1-" 2 #[Term.list lines]) T₅ .nil = .ok T₅ := by
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
    simp only [Term.list] at r₃
    simp [Elixir.Module.Types.Descr.«map_get_static_dnf/3», r₂, r₃, rR, r₄, r₅, nil]
  rw [s₅, s₄, s₃, s₂, ← pieces_sem ef lines hl sl hs hR swR x]
  simp only [ef.den_none x, false_or, List.not_mem_nil, false_and, exists_false, or_false]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- A split of keys, as `map_split_keys_and_domains/1` returns it. -/
def splitT (rs : List Term) (neg : Term) (ds : List Term) : Term :=
  .tuple #[Term.list rs, .nil, neg, Term.list ds, .nil]

/-- `map_get_static/2` on a map field and a split of static keys: `:badmap` when it is empty, otherwise the union of
the values its maps hold at the keys the split selects. -/
theorem mstatic_get (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) {rs : List Term} {neg : Term} {ds : List Term}
    (hs : SplitOk rs neg ds) :
    ∃ res, Elixir.Module.Types.Descr.«map_get_static/2» (D (n + 4)) (.map X) (splitT rs neg ds) = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        (∃ T, res = .tuple #[.atom "ok", T] ∧ E T ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey rs neg ds κ ∧ w κ = some x)) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 4)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 4) (by omega)
    cases e
    · -- Not empty: a map of the literal.
      have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have line : ∀ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list []]) w ↔ MSem den tag l w := fun w => by
        rw [inMLine_iff]; simp
      obtain ⟨T, rT, hT, sT⟩ := get_dnf ef hn fb [.tuple #[tag, fieldsTerm l, Term.list []]]
        (fun L mL => by
          simp only [List.mem_singleton] at mL
          subst mL
          exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, (line w₀).mpr h₀⟩)
        (fun w => by simp [sem, line]) hs
      refine ⟨_, ?_, Or.inr ⟨T, rfl, hT, ⟨w₀, (sem w₀).mpr h₀⟩, sT⟩⟩
      unfold Elixir.Module.Types.Descr.«map_get_static/2»
      simp only [Term.list] at rT
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom, rT, splitT]
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_get_static/2»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 4) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl (m := n + 4) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_get_static/2»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      · cases h : denMF E den b w
        · rfl
        · simpa using (inB w).mp h
    | cons L rest =>
      obtain ⟨T, rT, hT, sT⟩ := get_dnf ef hn fb (L :: rest) hl inB hs
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨T, rfl, hT, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, sT⟩⟩
      unfold Elixir.Module.Types.Descr.«map_get_static/2»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simp [getMapKeys_single, hb, rl, rT, Term.list, splitT]
      · simp [getMapKeys_single, hb, rl, rT, Term.list, splitT]
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simp [getMapKeys_single, hb, rl, rT, Term.list, splitT]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- `map_get/2` on static types of the next level, with keys that split into static keys: types holding only maps give
the union of the values their maps hold at the selected keys, or `:error` when there are none, and others `:badmap`. -/
theorem get_map {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {rs : List Term} {neg : Term}
    {ds : List Term} (hs : SplitOk rs neg ds) {key : Term} {m : Nat} (hm : (level t n).K + 25 ≤ m)
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok (splitT rs neg ds)) :
    ∃ res, Elixir.Module.Types.Descr.«map_get/2» (D m) (.map X) key = .ok res ∧
      ((res = .atom "badmap" ∧ ¬MOnly t n X) ∨
        (res = .atom "error" ∧ MOnly t n X ∧ ∀ w, MT t n X w → ∀ κ, SplitKey rs neg ds κ → w κ = none) ∨
        ∃ T, res = .tuple #[.atom "ok", T] ∧ (level t n).E T ∧ MOnly t n X ∧ (∃ x, (level t n).den T x) ∧
          ∀ x, (level t n).den T x ↔ ∃ w, MT t n X w ∧ ∃ κ, SplitKey rs neg ds κ ∧ w κ = some x) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_get/2».eq_def]
  simp only [hk, Lynx.Except.ok_bind, Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 4))
      (.function false "Elixir.Module.Types.Descr" "-map_get/2-fun-0-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get/2-fun-0-/1».pure]
  cases hb : mapLookup X (.atom "map") with
  | none =>
    refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun ⟨_, w, b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso, bad,
      Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1»]
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
    obtain ⟨dR, sR⟩ := rest_map hX
    have rE := next_empty dR (m := k + 4) (by omega)
    have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have only : MOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmM X)) v) ∧
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), w, (mt w).mp hw⟩
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), w, (mt w).mpr hw⟩
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 4)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨T, rfl, hT, ⟨w₀, hw₀⟩, sT⟩⟩ := mstatic_get (level t n).ef (n := k) (by omega) hb fb hs
      · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => ?_⟩⟩
        · simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1»]
        · obtain ⟨-, w, hw⟩ := only.mp h
          rw [emp w] at hw; cases hw
      have ok : MOnly t n X := only.mpr ⟨restE, w₀, hw₀⟩
      obtain ⟨eb, reb, seb⟩ := (level t n).ef.empty_pub hT
      cases eb
      · refine ⟨_, ?_, Or.inr (Or.inr ⟨T, rfl, hT, ok, Classical.byContradiction fun h => ?_, fun x => ?_⟩)⟩
        · simp [key, mo, run, Lynx.Except.andAlso, reb (k + 4) (by omega), Lynx.Term.isMember,
            boolAtom]
        · exact absurd (seb.mpr fun x hx => h ⟨x, hx⟩) (by simp)
        · rw [sT]
          exact ⟨fun ⟨w, hw, h⟩ => ⟨w, (mt w).mpr hw, h⟩, fun ⟨w, hw, h⟩ => ⟨w, (mt w).mp hw, h⟩⟩
      · refine ⟨.atom "error", ?_, Or.inr (Or.inl ⟨rfl, ok, fun w hw κ hκ => ?_⟩)⟩
        · simp [key, mo, run, Lynx.Except.andAlso, reb (k + 4) (by omega), Lynx.Term.isMember,
            boolAtom]
        · cases h : w κ with
          | none => rfl
          | some x => exact absurd ((sT x).mpr ⟨w, (mt w).mp hw, κ, hκ, h⟩) (seb.mp rfl x)
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun h => restE (only.mp h).1⟩⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1», boolAtom]

theorem get_map_term (d : Dispatcher) (key : Term) :
    Elixir.Module.Types.Descr.«map_get/2» d (.atom "term") key = .ok (.atom "badmap") := by
  rw [Elixir.Module.Types.Descr.«map_get/2».eq_def]
  rfl

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- The kinds of keys of the bits of bitmaps. -/
def bitKind : Nat → String
  | 0 => "binary"
  | 1 => "bitstring_no_binary"
  | 2 => "list"
  | 3 => "integer"
  | 4 => "float"
  | 5 => "pid"
  | 6 => "port"
  | _ => "reference"

theorem testBit_and_pow (x i : Nat) : (x &&& 2 ^ i ≠ 0) ↔ x.testBit i = Bool.true := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_and, Nat.testBit_two_pow] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    rw [hj.2]; exact hj.1
  · intro h e
    have := Nat.testBit_and x (2 ^ i) i
    rw [e, Nat.zero_testBit, Nat.testBit_two_pow_self, h] at this
    cases this

theorem ne_bit (x i : Nat) : Erlang.erlang.«/=/2» (.integer (Int.ofNat (x &&& 2 ^ i))) (.integer 0) =
    .ok (boolAtom (x.testBit i)) := by
  have := testBit_and_pow x i
  cases h : x.testBit i <;> simp_all [Erlang.erlang.«/=/2», boolAtom, Term.false, Term.true]

theorem band_nat (x m : Nat) :
    Erlang.erlang.«band/2» (.integer (Int.ofNat x)) (.integer (Int.ofNat m)) = .ok (.integer (Int.ofNat (x &&& m))) :=
  rfl

theorem bit_case (c : Bool) (a y : Term) :
    Elixir.Module.Types.Descr.«atom_intersection/2».match_3 (fun _ => Except Exception Term) (boolAtom c)
      (fun _ => pure y) (fun _ => pure (a.cons y))
      (fun u => Except.error (Exception.error (.tuple #[.atom "case_clause", u]))) =
      .ok (if c then a.cons y else y) := by
  cases c <;> rfl

/-- A list with an element added when a condition holds. -/
def ccons (c : Bool) (a : Term) (l : List Term) : List Term := if c then a :: l else l

theorem ccons_list (c : Bool) (a : Term) (l : List Term) :
    (if c = Bool.true then a.cons (Term.list l) else Term.list l) = Term.list (ccons c a l) := by
  cases c <;> rfl

theorem ccons_append (c : Bool) (a : Term) (l acc : List Term) : ccons c a l ++ acc = ccons c a (l ++ acc) := by
  cases c <;> rfl

theorem mem_ccons {c : Bool} {a d : Term} {l : List Term} : d ∈ ccons c a l ↔ (c = Bool.true ∧ d = a) ∨ d ∈ l := by
  cases c <;> simp [ccons]

theorem exists_lt_eight {P : Nat → Prop} :
    (∃ i < 8, P i) ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 ∨ P 4 ∨ P 5 ∨ P 6 ∨ P 7 := by
  constructor
  · rintro ⟨i, hi, h⟩
    match i, hi with
    | 0, _ => exact Or.inl h
    | 1, _ => exact Or.inr (Or.inl h)
    | 2, _ => exact Or.inr (Or.inr (Or.inl h))
    | 3, _ => exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    | 4, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    | 5, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    | 6, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    | 7, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · rintro (h | h | h | h | h | h | h | h)
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
    · exact ⟨2, by omega, h⟩
    · exact ⟨3, by omega, h⟩
    · exact ⟨4, by omega, h⟩
    · exact ⟨5, by omega, h⟩
    · exact ⟨6, by omega, h⟩
    · exact ⟨7, by omega, h⟩

/-- `bitmap_to_domain_keys/2` adds the kinds of the bits of a bitmap. -/
theorem bitmap_keys (x : Nat) (acc : List Term) :
    ∃ pre, Elixir.Module.Types.Descr.«bitmap_to_domain_keys/2» (.integer (x : Int)) (Term.list acc) =
      .ok (Term.list (pre ++ acc)) ∧ ∀ d, d ∈ pre ↔ ∃ i < 8, x.testBit i = Bool.true ∧ d = .atom (bitKind i) := by
  have a0 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 1) = .ok (.integer (Int.ofNat (x &&& 2 ^ 0))) :=
    band_nat x 1
  have a1 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 2) = .ok (.integer (Int.ofNat (x &&& 2 ^ 1))) :=
    band_nat x 2
  have a2 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 4) = .ok (.integer (Int.ofNat (x &&& 2 ^ 2))) :=
    band_nat x 4
  have a3 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 8) = .ok (.integer (Int.ofNat (x &&& 2 ^ 3))) :=
    band_nat x 8
  have a4 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 16) = .ok (.integer (Int.ofNat (x &&& 2 ^ 4))) :=
    band_nat x 16
  have a5 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 32) = .ok (.integer (Int.ofNat (x &&& 2 ^ 5))) :=
    band_nat x 32
  have a6 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 64) = .ok (.integer (Int.ofNat (x &&& 2 ^ 6))) :=
    band_nat x 64
  have a7 : Erlang.erlang.«band/2» (.integer (x : Int)) (.integer 128) = .ok (.integer (Int.ofNat (x &&& 2 ^ 7))) :=
    band_nat x 128
  refine ⟨(ccons (x.testBit 7) (.atom "reference") (ccons (x.testBit 6) (.atom "port") (ccons (x.testBit 5) (.atom "pid")
    (ccons (x.testBit 4) (.atom "float") (ccons (x.testBit 3) (.atom "integer") (ccons (x.testBit 2) (.atom "list")
    (ccons (x.testBit 1) (.atom "bitstring_no_binary") (ccons (x.testBit 0) (.atom "binary") [])))))))), ?_, fun d => ?_⟩
  · simp only [Elixir.Module.Types.Descr.«bitmap_to_domain_keys/2», a0, a1, a2, a3, a4, a5, a6, a7, Lynx.Except.ok_bind,
      ne_bit, bit_case, ccons_list, ccons_append, List.nil_append]
  · simp only [mem_ccons, List.not_mem_nil, or_false, exists_lt_eight, bitKind]
    simp only [or_comm, or_left_comm, or_assoc]

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- The kind of keys of a point: the kind of its bit for bitmaps, otherwise its field. -/
def ptKind (v : PN t n) : String := if v.1.1 = "bitmap" then bitKind v.1.2.1 else v.1.1

/-- A point of a bitmap, at a bit. -/
def bPt (i : Nat) (h : i < 8) : PN t n := ⟨("bitmap", (i, .nil, fun _ => Bool.false)), by simp [names],
  ⟨resp_const _, fun _ => h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
    fun h => by simp at h⟩⟩

/-- A point of atoms, at a term. -/
def aPt (q : Term) : PN t n := ⟨("atom", (0, q, fun _ => Bool.false)), by simp [names],
  ⟨resp_const _, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h,
    fun h => by simp at h⟩⟩

theorem denD_field {Y : List (Term × Term)} (v : PN t n) :
    denD (.map Y) v ↔ ∃ x, mapLookup Y (.atom v.1.1) = some x ∧ dn v.1.1 (some x) v.1.2 = Bool.true := by
  rw [denD_map]
  cases mapLookup Y (.atom v.1.1) <;> simp [dn_none]

/-- A type restricted to one of its fields. -/
theorem field_de {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {name : String} {x : Term}
    (hx : mapLookup Y (.atom name) = some x) :
    DE (level t n).E (.map [(.atom name, x)]) ∧
      ∀ v : PN t n, denD (.map [(.atom name, x)]) v ↔ v.1.1 = name ∧ denD (.map Y) v := by
  have sY := de_map hY
  refine ⟨Or.inr ⟨_, rfl, fun q h => ?_, fun name' w h => ?_⟩, fun v => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil, equalExact_eq_decide] at h
    by_cases e : compareExact (fuel q (.atom name)) q (.atom name) = .eq
    · rw [(compareExact_eq_atom _ _).mp e]
      exact sY.keys _ (by rw [hx]; rfl)
    · simp [e] at h
  · rw [lookup_cons_atom] at h
    by_cases e : name = name'
    · subst e
      simp at h
      subst h
      exact sY.fields _ _ hx
    · simp [e, mapLookup] at h
  · rw [denD_field, denD_field, lookup_cons_atom]
    by_cases e : name = v.1.1
    · rw [← e, hx]; simp
    · simp [e, mapLookup]
      exact fun h => absurd h.symm e

/-- Bitmaps of key types whose kinds include lists through the empty list. -/
def ListSkip (Y : List (Term × Term)) : Prop :=
  ∃ b : Nat, mapLookup Y (.atom "bitmap") = some (.integer b) ∧ b.testBit 2 = Bool.true

/-- The kinds of keys that a field of a key type contributes to its domain keys. -/
def Contrib (Y : List (Term × Term)) (name : String) (x : Term) (s : String) : Prop :=
  (name = "bitmap" ∧ ∃ b : Nat, x = .integer b ∧ ∃ i < 8, b.testBit i = Bool.true ∧ bitKind i = s) ∨
  (name = "atom" ∧ s = "atom" ∧ ∃ S, x = .tuple #[.atom "negation", .map S]) ∨
  (name ≠ "bitmap" ∧ name ≠ "atom" ∧ s = name ∧ ¬(name = "list" ∧ ListSkip Y) ∧
    ∃ v : PN t n, v.1.1 = name ∧ denD (.map Y) v)

theorem dom_step {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {name : String} {x : Term}
    (hx : mapLookup Y (.atom name) = some x) {m : Nat} (hm : (level t n).K + 23 ≤ m) (acc : List Term) :
    ∃ pre, Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4» (D m) (.map Y) (.atom name) x (Term.list acc) =
        .ok (Term.list (pre ++ acc)) ∧ (∀ d ∈ pre, ∃ s ∈ domainKinds, d = .atom s) ∧
      ∀ s, .atom s ∈ pre ↔ Contrib (t := t) (n := n) Y name x s := by
  have sY := de_map hY
  obtain ⟨name', mn, e⟩ := sY.keys (.atom name) (by rw [hx]; rfl)
  obtain rfl : name = name' := Term.atom.inj e
  have fx := sY.fields name x hx
  obtain ⟨dF, sF⟩ := field_de hY hx
  have emp := next_empty dF hm
  simp only [names, List.mem_cons, List.not_mem_nil, or_false] at mn
  have eb : bp (∀ v : PN t n, ¬denD (.map [(.atom name, x)]) v) =
      !bp (∃ v : PN t n, v.1.1 = name ∧ denD (.map Y) v) := by
    by_cases h : ∃ v : PN t n, v.1.1 = name ∧ denD (.map Y) v
    · obtain ⟨v, hv⟩ := h
      rw [bp_false.mpr fun h' => h' v ((sF v).mpr hv), bp_true.mpr ⟨v, hv⟩]; rfl
    · rw [bp_true.mpr fun v hv => h ⟨v, (sF v).mp hv⟩, bp_false.mpr h]; rfl
  rw [eb] at emp
  rcases mn with rfl | rfl | rfl | rfl | rfl | rfl
  · -- bitmap
    obtain ⟨b, rfl, -, -⟩ := fieldC_bitmap fx
    obtain ⟨pre, run, mem⟩ := bitmap_keys b acc
    refine ⟨pre, ?_, fun d md => ?_, fun s => ?_⟩
    · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, run]
    · obtain ⟨i, hi, -, rfl⟩ := (mem d).mp md
      refine ⟨_, ?_, rfl⟩
      match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bitKind, domainKinds]
    · rw [mem]
      simp only [Contrib, Term.atom.injEq, true_and]
      constructor
      · rintro ⟨i, hi, hb, rfl⟩
        exact Or.inl ⟨b, rfl, i, hi, hb, rfl⟩
      · rintro (⟨b', e, i, hi, hb, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · obtain rfl : b = b' := by have := Term.integer.inj e; omega
          exact ⟨i, hi, hb, rfl⟩
        · simp at h
        · exact absurd rfl h
  · -- atom
    obtain ⟨⟨pos, S, rfl, -⟩, q, hq⟩ := fieldC_atom fx
    cases pos
    · have ne : bp (∃ v : PN t n, v.1.1 = "atom" ∧ denD (.map Y) v) = Bool.true :=
        bp_true.mpr ⟨aPt q, rfl, (denD_field _).mpr ⟨_, hx, by simpa [aPt, dn_atom] using hq⟩⟩
      rw [ne] at emp
      simp only [Bool.false_eq_true, ↓reduceIte] at emp
      refine ⟨[.atom "atom"], ?_, fun d md => ⟨"atom", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom, Term.list]
      · simp [Contrib]
    · refine ⟨[], ?_, by simp, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso]
      · simp [Contrib]
  · -- fun
    by_cases ne : ∃ v : PN t n, v.1.1 = "fun" ∧ denD (.map Y) v
    · rw [bp_true.mpr ne] at emp
      refine ⟨[.atom "fun"], ?_, fun d md => ⟨"fun", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom, Term.list]
      · simp [Contrib, ne]
    · rw [bp_false.mpr ne] at emp
      refine ⟨[], ?_, by simp, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom]
      · simp [Contrib, ne]
  · -- list
    cases hb : mapLookup Y (.atom "bitmap") with
    | none =>
      have nsk : ¬ListSkip Y := fun ⟨b, h, _⟩ => by rw [hb] at h; cases h
      by_cases ne : ∃ v : PN t n, v.1.1 = "list" ∧ denD (.map Y) v
      · rw [bp_true.mpr ne] at emp
        refine ⟨[.atom "list"], ?_, fun d md => ⟨"list", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
            boolAtom, Term.list, getMapKeys_single, hb]
        · simp [Contrib, ne, nsk]
      · rw [bp_false.mpr ne] at emp
        refine ⟨[], ?_, by simp, fun s => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
            boolAtom, getMapKeys_single, hb]
        · simp [Contrib, ne]
    | some x' =>
      obtain ⟨b, rfl, -, -⟩ := fieldC_bitmap (sY.fields _ _ hb)
      have a2 : Erlang.erlang.«band/2» (.integer (b : Int)) (.integer 4) = .ok (.integer (Int.ofNat (b &&& 2 ^ 2))) :=
        band_nat b 4
      have n2 := ne_bit b 2
      have i2 : (if b &&& 4 = 0 then Term.atom "false" else Term.atom "true") = boolAtom (b.testBit 2) := by
        have := testBit_and_pow b 2
        cases h : b.testBit 2 <;> simp_all [boolAtom]
      cases tb : b.testBit 2
      · have nsk : ¬ListSkip Y := fun ⟨b', h, t'⟩ => by
          rw [hb] at h
          obtain rfl : b = b' := by have := Term.integer.inj (Option.some.inj h); omega
          rw [tb] at t'; cases t'
        by_cases ne : ∃ v : PN t n, v.1.1 = "list" ∧ denD (.map Y) v
        · rw [bp_true.mpr ne] at emp
          refine ⟨[.atom "list"], ?_, fun d md => ⟨"list", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
          · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
              boolAtom, Term.list, getMapKeys_single, hb, a2, i2, tb]
          · simp [Contrib, ne, nsk]
        · rw [bp_false.mpr ne] at emp
          refine ⟨[], ?_, by simp, fun s => ?_⟩
          · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
              boolAtom, getMapKeys_single, hb, a2, i2, tb]
          · simp [Contrib, ne]
      · refine ⟨[], ?_, by simp, fun s => ?_⟩
        · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso,
            getMapKeys_single, hb, a2, i2, tb, boolAtom]
        · have sk : ListSkip Y := ⟨b, hb, tb⟩
          simp [Contrib, sk]
  · -- tuple
    by_cases ne : ∃ v : PN t n, v.1.1 = "tuple" ∧ denD (.map Y) v
    · rw [bp_true.mpr ne] at emp
      refine ⟨[.atom "tuple"], ?_, fun d md => ⟨"tuple", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom, Term.list]
      · simp [Contrib, ne]
    · rw [bp_false.mpr ne] at emp
      refine ⟨[], ?_, by simp, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom]
      · simp [Contrib, ne]
  · -- map
    by_cases ne : ∃ v : PN t n, v.1.1 = "map" ∧ denD (.map Y) v
    · rw [bp_true.mpr ne] at emp
      refine ⟨[.atom "map"], ?_, fun d md => ⟨"map", by simp [domainKinds], by simpa using md⟩, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom, Term.list]
      · simp [Contrib, ne]
    · rw [bp_false.mpr ne] at emp
      refine ⟨[], ?_, by simp, fun s => ?_⟩
      · simp [Elixir.Module.Types.Descr.«-to_domain_keys/1-fun-0-/4», Erlang.erlang.«==/2», Lynx.Except.andAlso, emp,
          boolAtom]
      · simp [Contrib, ne]

/-- `maps:fold/3` of the domain keys step over fields of a key type. -/
theorem dom_fold {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∀ (es : List (Term × Term)), (∀ e ∈ es, mapLookup Y e.1 = some e.2) → ∀ acc : List Term,
      ∃ out, es.foldlM (fun acc e => Lynx.Dispatcher.pure (D (m + 1))
          (.function false "Elixir.Module.Types.Descr" "-to_domain_keys/1-fun-0-" 3 #[.map Y]) #[e.1, e.2, acc])
          (Term.list acc) = .ok (Term.list (out ++ acc)) ∧ (∀ d ∈ out, ∃ s ∈ domainKinds, d = .atom s) ∧
        ∀ s, .atom s ∈ out ↔ ∃ e ∈ es, ∃ name, e.1 = .atom name ∧ Contrib (t := t) (n := n) Y name e.2 s
  | [], _, acc => ⟨[], rfl, by simp, by simp⟩
  | (k, x) :: es, hes, acc => by
    have hk := hes _ List.mem_cons_self
    obtain ⟨name, -, rfl⟩ := (de_map hY).keys k (by rw [hk]; rfl)
    obtain ⟨pre, run, hpre, spre⟩ := dom_step hY hk hm acc
    obtain ⟨out, run', hout, sout⟩ := dom_fold hY hm es (fun e me => hes e (List.mem_cons_of_mem _ me)) (pre ++ acc)
    refine ⟨out ++ pre, ?_, fun d md => ?_, fun s => ?_⟩
    · simp only [List.foldlM_cons]
      rw [Erlang.program.«Elixir.Module.Types.Descr:-to_domain_keys/1-fun-0-/3».pure, run]
      simpa using run'
    · rcases List.mem_append.mp md with h | h
      · exact hout d h
      · exact hpre d h
    · rw [List.mem_append, sout, spre]
      constructor
      · rintro (⟨e, me, h⟩ | h)
        · exact ⟨e, List.mem_cons_of_mem _ me, h⟩
        · exact ⟨_, List.mem_cons_self, name, rfl, h⟩
      · rintro ⟨e, me, name', e₁, h⟩
        rcases List.mem_cons.mp me with rfl | me
        · obtain rfl : name = name' := Term.atom.inj e₁
          exact Or.inr h
        · exact Or.inl ⟨e, me, name', e₁, h⟩

theorem entry_of_lookup_entries {es : List (Term × Term)} {q x : Term} (h : mapLookup es q = some x) :
    ∃ e ∈ mapEntries es, compareExact (fuel q e.1) q e.1 = .eq ∧ e.2 = x := by
  rw [← mapLookup_mapEntries, mapLookup] at h
  simp only [equalExact_eq_decide] at h
  cases e : (mapEntries es).find? (fun entry => decide (compareExact (fuel q entry.1) q entry.1 = .eq)) with
  | none => rw [e] at h; cases h
  | some r =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have := List.find?_some e
    simp only [decide_eq_true_eq] at this
    exact ⟨r, List.mem_of_find?_eq_some e, this, h⟩

/-- `to_domain_keys/1` on a static key type: the kinds its fields contribute. -/
theorem dom_keys {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ ds, Elixir.Module.Types.Descr.«to_domain_keys/1» (D (m + 1)) (.map Y) = .ok (Term.list ds) ∧
      (∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) ∧
      ∀ s, .atom s ∈ ds ↔ ∃ name x, mapLookup Y (.atom name) = some x ∧ Contrib (t := t) (n := n) Y name x s := by
  obtain ⟨out, run, hout, sout⟩ := dom_fold hY hm (mapEntries Y)
    (fun e me => mapLookup_of_mem_mapEntries me) []
  refine ⟨out, ?_, hout, fun s => ?_⟩
  · rw [Elixir.Module.Types.Descr.«to_domain_keys/1».eq_def]
    simp only [getMapKeys_single, (de_map hY).static, Option.toList_none]
    simpa [Erlang.maps.«fold/3», Term.list] using run
  · rw [sout]
    constructor
    · rintro ⟨e, me, name, e₁, h⟩
      exact ⟨name, e.2, by rw [← e₁]; exact mapLookup_of_mem_mapEntries me, h⟩
    · rintro ⟨name, x, hx, h⟩
      obtain ⟨e, me, ec, rfl⟩ := entry_of_lookup_entries hx
      exact ⟨e, me, name, ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm ec)), h⟩

/-- Kinds of keys of static key types: the atom kind for negated atoms, and the other kinds of their points. -/
theorem dom_kinds {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ ds, Elixir.Module.Types.Descr.«to_domain_keys/1» (D (m + 1)) (.map Y) = .ok (Term.list ds) ∧
      (∀ d ∈ ds, ∃ s ∈ domainKinds, d = .atom s) ∧
      (.atom "atom" ∈ ds ↔ ∃ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "negation", .map S])) ∧
      ∀ s, s ≠ "atom" → (.atom s ∈ ds ↔ ∃ v : PN t n, denD (.map Y) v ∧ ptKind v = s) := by
  obtain ⟨ds, run, hds, sds⟩ := dom_keys hY hm
  refine ⟨ds, run, hds, ?_, fun s ns => ?_⟩
  · rw [sds]
    constructor
    · rintro ⟨name, x, hx, (⟨rfl, b, -, i, hi, -, e⟩ | ⟨rfl, -, S, rfl⟩ | ⟨-, na, e, -⟩)⟩
      · match i, hi with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bitKind] at e
      · exact ⟨S, hx⟩
      · exact absurd e.symm na
    · rintro ⟨S, hS⟩
      exact ⟨"atom", _, hS, Or.inr (Or.inl ⟨rfl, rfl, S, rfl⟩)⟩
  · rw [sds]
    constructor
    · rintro ⟨name, x, hx, (⟨rfl, b, rfl, i, hi, hb, rfl⟩ | ⟨-, e, -⟩ | ⟨nb, -, rfl, -, v, hv, dv⟩)⟩
      · refine ⟨bPt i hi, (denD_field _).mpr ⟨_, hx, ?_⟩, rfl⟩
        simp [bPt, dn_bitmap, bitOf, hb]
      · exact absurd e ns
      · exact ⟨v, dv, by simp [ptKind, hv, nb]⟩
    · rintro ⟨v, dv, rfl⟩
      obtain ⟨x, hx, dx⟩ := (denD_field v).mp dv
      by_cases hb : v.1.1 = "bitmap"
      · rw [hb] at hx dx
        obtain ⟨b, rfl, -, -⟩ := fieldC_bitmap ((de_map hY).fields _ _ hx)
        have hi : v.1.2.1 < 8 := v.2.2.2.1 hb
        refine ⟨"bitmap", _, hx, Or.inl ⟨rfl, b, rfl, v.1.2.1, hi, ?_, by simp [ptKind, hb]⟩⟩
        simpa [dn_bitmap, bitOf] using dx
      · have pk : ptKind v = v.1.1 := by simp [ptKind, hb]
        rw [pk] at ns ⊢
        by_cases sk : v.1.1 = "list" ∧ ListSkip Y
        · obtain ⟨e, b, hb', tb⟩ := sk
          exact ⟨"bitmap", _, hb', Or.inl ⟨rfl, b, rfl, 2, by omega, tb, by rw [e]; rfl⟩⟩
        · exact ⟨v.1.1, x, hx, Or.inr (Or.inr ⟨hb, ns, rfl, sk, v, rfl, dv⟩)⟩

theorem denD_aPt {Y : List (Term × Term)} (q : Term) :
    denD (.map Y) (aPt (t := t) (n := n) q) ↔ amemV (mapLookup Y (.atom "atom")) q = Bool.true := by
  rw [denD_map]
  simp only [aPt]
  cases h : mapLookup Y (.atom "atom") <;> simp [dn_none, dn_atom, amemV]

/-- `map_split_keys_and_domains/1` on a static key type, whose unions of atoms hold atoms: the atoms of its points,
and the kinds of its other points. -/
theorem split_map {Y : List (Term × Term)} (hY : DE (level t n).E (.map Y))
    (hU : ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.map Y) =
        .ok (splitT rs neg ds) ∧ SplitOk rs neg ds ∧ (∀ N, neg = .map N → rs = []) ∧
      (∀ N, neg = .map N → mapLookup Y (.atom "atom") = some (.tuple #[.atom "negation", .map N])) ∧
      (∀ s, SplitKey rs neg ds (.atom s) ↔ denD (.map Y) (aPt (t := t) (n := n) (.atom s))) ∧
      ∀ k i, SplitKey rs neg ds (.dom k i) ↔ ∃ v : PN t n, denD (.map Y) v ∧ ptKind v = domKind k := by
  obtain ⟨ds, rd, hds, hat, hk⟩ := dom_kinds hY hm
  have dom : ∀ rs neg k i, SplitKey rs neg ds (.dom k i) ↔ ∃ v : PN t n, denD (.map Y) v ∧ ptKind v = domKind k :=
    fun rs neg k i => hk _ (domKind_ne_atom k)
  have st := (de_map hY).static
  cases ha : mapLookup Y (.atom "atom") with
  | none =>
    refine ⟨[], .atom "nil", ds, ?_, ⟨by simp, Or.inl rfl, hds, ?_⟩, fun _ _ => rfl,
      (fun N (e : Term.atom "nil" = .map N) => nomatch e), fun s => ?_, dom _ _⟩
    · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
      simp [getMapKeys_single, st, ha, rd, splitT, Term.list]
    · rw [hat, ha]; simp
    · rw [denD_aPt, ha]; simp [SplitKey, amemV]
  | some x =>
    obtain ⟨⟨pos, S, rfl, -⟩, -⟩ := fieldC_atom ((de_map hY).fields _ _ ha)
    cases pos
    · refine ⟨[], .map S, ds, ?_, ⟨by simp, Or.inr ⟨S, rfl⟩, hds, ?_⟩, fun _ _ => rfl,
        fun N e => by cases e; simp, fun s => ?_, dom _ _⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        simp [getMapKeys_single, st, ha, rd, splitT, Term.list]
      · rw [hat, ha]; simp
      · rw [denD_aPt, ha]; simp [SplitKey, amemV]
    · have hU' := hU S (by simpa using ha)
      refine ⟨(mapEntries S).map Prod.fst, .atom "nil", ds, ?_, ⟨fun r mr => ?_, Or.inl rfl, hds, ?_⟩,
        (fun N (e : Term.atom "nil" = .map N) => nomatch e), (fun N (e : Term.atom "nil" = .map N) => nomatch e),
        fun s => ?_, dom _ _⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        simp [getMapKeys_single, st, ha, rd, splitT, Erlang.sets.«to_list/1», Erlang.maps.«keys/1»]
      · obtain ⟨e, me, rfl⟩ := List.mem_map.mp mr
        exact hU' e.1 (by rw [mapLookup_of_mem_mapEntries me]; rfl)
      · rw [hat, ha]; simp
      · rw [denD_aPt, ha]
        simp only [SplitKey, ↓reduceIte, amemV]
        constructor
        · rintro (m | ⟨N, e, -⟩)
          · obtain ⟨e, me, he⟩ := List.mem_map.mp m
            rw [← he, mapLookup_of_mem_mapEntries me]; rfl
          · cases e
        · intro h
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
          obtain ⟨e, me, ec, -⟩ := entry_of_lookup_entries hv
          exact Or.inl (List.mem_map.mpr ⟨e, me, ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm ec))⟩)

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Unions of static map types of the next level are maps of the points of either. -/
theorem union_map {A B : List (Term × Term)} (hA : DE (level t n).E (.map A)) (hB : DE (level t n).E (.map B)) {m : Nat}
    (hm : (level t n).K + 23 ≤ m) :
    ∃ U, Elixir.Module.Types.Descr.«bare_union/2» (D m) (.map A) (.map B) = .ok (.map U) ∧
      DE (level t n).E (.map U) ∧ ∀ v : PN t n, denD (.map U) v ↔ denD (.map A) v ∨ denD (.map B) v := by
  obtain ⟨c, hc, rc, sc, -⟩ := (ef_next t n).union hA hB
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have sA := de_map hA
  have sB := de_map hB
  obtain ⟨U, rU, -⟩ := union_any k A B sA.static sB.static (fun q h => let ⟨name, _, e⟩ := sB.keys q h; ⟨name, e⟩)
    (fun q x y hx hy => by
      obtain ⟨name, -, rfl⟩ := sA.keys q (by rw [hx]; rfl)
      obtain ⟨u, ru, -⟩ := fieldC_union (tks (level t n)) (tfc (level t n)) (m := k) (by omega)
        (sA.fields _ _ hx) (sB.fields _ _ hy)
      exact ⟨u, ru⟩)
  have e := (rc (k + 1) hm).symm.trans rU
  simp only [Except.ok.injEq] at e
  subst e
  exact ⟨U, rU, hc, sc⟩

theorem denD_single (name : String) (x : Term) (v : PN t n) :
    denD (.map [(.atom name, x)]) v ↔ v.1.1 = name ∧ dn name (some x) v.1.2 = Bool.true := by
  rw [denD_map, lookup_cons_atom]
  by_cases e : name = v.1.1
  · subst e; simp
  · simp [e, mapLookup, dn_none]
    exact fun h => absurd h.symm e

theorem single_de {name : String} {x : Term} (hn : name ∈ names)
    (fx : FieldC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E) (MField (level t n).E) name x) :
    DE (level t n).E (.map [(.atom name, x)]) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name' w h => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil, equalExact_eq_decide] at h
    by_cases e : compareExact (fuel q (.atom name)) q (.atom name) = .eq
    · exact ⟨name, hn, (compareExact_eq_atom _ _).mp e⟩
    · simp [e] at h
  · rw [lookup_cons_atom] at h
    by_cases e : name = name'
    · subst e; simp at h; subst h; exact fx
    · simp [e, mapLookup] at h

/-- Key types of a kind: their points are of that kind, every atom for the atom kind, and some point otherwise. -/
structure KindT (t : Term) (n : Nat) (d : String) (T : List (Term × Term)) : Prop where
  de : DE (level t n).E (.map T)
  pts : ∀ v : PN t n, denD (.map T) v → (d = "atom" ∧ v.1.1 = "atom") ∨ (v.1.1 ≠ "atom" ∧ ptKind v = d)
  wit : d ≠ "atom" → ∃ v : PN t n, denD (.map T) v ∧ ptKind v = d
  atoms : d = "atom" → ∀ q, denD (.map T) (aPt (t := t) (n := n) q)

theorem kind_bit (i : Nat) (hi : i < 8) : KindT t n (bitKind i) [(.atom "bitmap", .integer ((2 ^ i : Nat) : Int))] := by
  have pos : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have le : 2 ^ i ≤ 255 := by
    have : 2 ^ i ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have bk : bitKind i ≠ "atom" := by
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [bitKind]
  refine ⟨single_de (by simp [names]) (Or.inl ⟨rfl, _, rfl, pos, le⟩), fun v hv => ?_, fun _ => ⟨bPt i hi, ?_, rfl⟩,
    fun h => absurd h bk⟩
  · obtain ⟨hb, hd⟩ := (denD_single _ _ v).mp hv
    rw [dn_bitmap, bitOf] at hd
    simp only [Int.toNat_natCast, Nat.testBit_two_pow, decide_eq_true_eq] at hd
    refine Or.inr ⟨by rw [hb]; decide, by simp [ptKind, hb, ← hd]⟩
  · rw [denD_single]
    simp only [bPt, dn_bitmap, bitOf, Int.toNat_natCast, Nat.testBit_two_pow_self, and_self]

theorem kind_atom : KindT t n "atom" [(.atom "atom", .tuple #[.atom "negation", .map []])] := by
  refine ⟨single_de (by simp [names]) (Or.inr (Or.inl ⟨rfl, ⟨Bool.false, [], rfl, by simp [Erlang.sets.elements?]⟩, .nil,
    by simp [amemV, mapLookup]⟩)), fun v hv => Or.inl ⟨rfl, ((denD_single _ _ v).mp hv).1⟩, fun h => absurd rfl h, fun _ q => ?_⟩
  rw [denD_single]
  simp [aPt, dn_atom, amemV, mapLookup]

theorem kind_fun : KindT t n "fun" [(.atom "fun", funTopT)] := by
  obtain ⟨a, ρ, rρ, fv⟩ := fVal_wit (E := (level t n).E) (den := (level t n).den)
  let w : PN t n := ⟨("fun", (0, a, ρ)), by simp [names],
    ⟨rρ, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun h => by simp at h, fun _ => fv⟩⟩
  refine ⟨single_de (by simp [names]) (Or.inr (Or.inr (Or.inl ⟨rfl, funA_top⟩))), fun v hv => ?_,
    fun _ => ⟨w, (denD_single _ _ w).mpr ⟨rfl, dn_funTop _⟩, rfl⟩, fun h => by simp at h⟩
  have hf := ((denD_single _ _ v).mp hv).1
  exact Or.inr ⟨by rw [hf]; decide, by simp [ptKind, hf]⟩

theorem kind_map : KindT t n "map" [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])] := by
  refine ⟨mapTop_de, fun v hv => ?_, fun _ => ⟨mpt (fun _ => none), (mapTop_den _).mpr rfl, rfl⟩,
    fun h => by simp at h⟩
  have hm := (mapTop_den v).mp hv
  exact Or.inr ⟨by rw [hm]; decide, by simp [ptKind, hm]⟩

theorem kind_tuple : KindT t n "tuple" [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])] := by
  refine ⟨tupleTop_de, fun v hv => ?_, fun _ => ⟨tpt [], (tupleTop_den _).mpr rfl, rfl⟩, fun h => by simp at h⟩
  have hm := (tupleTop_den v).mp hv
  exact Or.inr ⟨by rw [hm]; decide, by simp [ptKind, hm]⟩

theorem non_empty_list_top (m : Nat) : Elixir.Module.Types.Descr.«non_empty_list/2» (D m) (.atom "term") (.atom "term") =
    .ok (.map [(.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) := by
  simp [Elixir.Module.Types.Descr.«non_empty_list/2», Elixir.Module.Types.Descr.«list_descr/3»,
    Elixir.Module.Types.Descr.«split_dynamic/1», Elixir.Module.Types.Descr.«list_descr_static/3», Erlang.erlang.«==/2»,
    Lynx.Except.orElse, Term.compare_step, Compare.compareStep]

theorem kind_list {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ T, Elixir.STTDescrProofsTest.«kind_type/1» (D m) (.atom "list") = .ok (.map T) ∧ KindT t n "list" T := by
  have b2 := kind_bit (t := t) (n := n) 2 (by omega)
  simp only [show ((2 ^ 2 : Nat) : Int) = 4 from rfl] at b2
  have dl : DE (level t n).E (.map [(.atom "list", .tuple #[.integer 46675407, .atom "term", .atom "term"])]) :=
    single_de (by simp [names]) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Bdd.leaf_iff.mpr
      ⟨46675407, _, _, rfl, (level t n).ef.term, (level t n).ef.term⟩⟩))))
  obtain ⟨U, rU, dU, sU⟩ := union_map b2.de dl hm
  refine ⟨U, ?_, ⟨dU, fun v hv => ?_, fun _ => ⟨bPt 2 (by omega), (sU _).mpr (Or.inl ?_), rfl⟩, fun h => by simp at h⟩⟩
  · simp [Elixir.STTDescrProofsTest.«kind_type/1», Elixir.Module.Types.Descr.«empty_list/0»,
      Elixir.Module.Types.Descr.«term/0», non_empty_list_top, rU]
  · rcases (sU v).mp hv with h | h
    · rcases b2.pts v h with ⟨e, -⟩ | ⟨ne, pk⟩
      · simp [bitKind] at e
      · exact Or.inr ⟨ne, pk⟩
    · have hl := ((denD_single _ _ v).mp h).1
      exact Or.inr ⟨by rw [hl]; decide, by simp [ptKind, hl]⟩
  · exact (denD_single _ _ _).mpr ⟨rfl, by simp only [bPt, dn_bitmap, bitOf]; decide⟩

/-- The key types of the spec's kinds. -/
theorem kind_run {d : String} (hd : d ∈ domainKinds) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ T, Elixir.STTDescrProofsTest.«kind_type/1» (D m) (.atom d) = .ok (.map T) ∧ KindT t n d T := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, kind_atom⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 0 (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 1 (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 4 (by omega)⟩
  · exact ⟨_, rfl, kind_fun⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 3 (by omega)⟩
  · exact kind_list hm
  · exact ⟨_, rfl, kind_map⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 5 (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 6 (by omega)⟩
  · exact ⟨_, rfl, by simpa [bitKind] using kind_bit (t := t) (n := n) 7 (by omega)⟩
  · exact ⟨_, rfl, kind_tuple⟩

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- Key types of atoms and kinds: the atom points of the atoms `P`, or all of them with the atom kind, and points of
the other kinds `ks`. -/
structure KeyInv (t : Term) (n : Nat) (Y : List (Term × Term)) (P : Term → Prop) (ks : List Term) : Prop where
  de : DE (level t n).E (.map Y)
  atoms : ∀ q, denD (.map Y) (aPt (t := t) (n := n) q) ↔ P q ∨ .atom "atom" ∈ ks
  kinds : ∀ v : PN t n, denD (.map Y) v → v.1.1 ≠ "atom" → .atom (ptKind v) ∈ ks
  wit : ∀ s, .atom s ∈ ks → s ≠ "atom" → ∃ v : PN t n, denD (.map Y) v ∧ ptKind v = s

theorem KeyInv.congr {Y : List (Term × Term)} {P : Term → Prop} {ks ks' : List Term} (h : KeyInv t n Y P ks)
    (e : ∀ x, x ∈ ks ↔ x ∈ ks') : KeyInv t n Y P ks' :=
  ⟨h.de, fun q => by rw [h.atoms, e], fun v hv nv => (e _).mp (h.kinds v hv nv),
    fun s ms ns => h.wit s ((e _).mpr ms) ns⟩

/-- `kinds_type/2` unites the key types of kinds. -/
theorem kinds_type_run {m : Nat} (hm : (level t n).K + 23 ≤ m) : ∀ (kinds : List Term),
    (∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) → ∀ (Y : List (Term × Term)) (P : Term → Prop) (ks : List Term),
    KeyInv t n Y P ks → ∃ Y', Elixir.STTDescrProofsTest.«kinds_type/2» (D m) (Term.list kinds) (.map Y) = .ok (.map Y') ∧
      KeyInv t n Y' P (kinds ++ ks)
  | [], _, Y, P, ks, h => ⟨Y, by simp [Elixir.STTDescrProofsTest.«kinds_type/2»], by simpa using h⟩
  | d :: rest, hd, Y, P, ks, h => by
    obtain ⟨s, ms, rfl⟩ := hd _ List.mem_cons_self
    obtain ⟨T, rT, kT⟩ := kind_run ms hm
    obtain ⟨U, rU, dU, sU⟩ := union_map kT.de h.de hm
    have inT : ∀ q, denD (.map T) (aPt (t := t) (n := n) q) ↔ s = "atom" := fun q => by
      constructor
      · intro hq
        rcases kT.pts _ hq with ⟨e, -⟩ | ⟨ne, -⟩
        · exact e
        · exact absurd rfl ne
      · intro e; exact kT.atoms e q
    have inv : KeyInv t n U P (.atom s :: ks) := by
      refine ⟨dU, fun q => ?_, fun v hv nv => ?_, fun s' ms' ns' => ?_⟩
      · rw [sU, inT, h.atoms]
        simp only [List.mem_cons, Term.atom.injEq]
        constructor
        · rintro (e | h' | h')
          · exact Or.inr (Or.inl e.symm)
          · exact Or.inl h'
          · exact Or.inr (Or.inr h')
        · rintro (h' | e | h')
          · exact Or.inr (Or.inl h')
          · exact Or.inl e.symm
          · exact Or.inr (Or.inr h')
      · rcases (sU v).mp hv with h' | h'
        · rcases kT.pts v h' with ⟨-, e⟩ | ⟨-, pk⟩
          · exact absurd e nv
          · rw [pk]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h.kinds v h' nv)
      · rcases List.mem_cons.mp ms' with e | m'
        · obtain rfl : s' = s := Term.atom.inj e
          obtain ⟨v, hv, pv⟩ := kT.wit ns'
          exact ⟨v, (sU v).mpr (Or.inl hv), pv⟩
        · obtain ⟨v, hv, pv⟩ := h.wit s' m' ns'
          exact ⟨v, (sU v).mpr (Or.inr hv), pv⟩
    obtain ⟨Y', r', h'⟩ := kinds_type_run hm rest (fun d md => hd d (List.mem_cons_of_mem _ md)) U P _ inv
    refine ⟨Y', ?_, h'.congr fun x => ?_⟩
    · simp only [Term.list] at r' ⊢
      simp [Elixir.STTDescrProofsTest.«kinds_type/2», rT, rU, r']
    · simp only [List.mem_append, List.mem_cons, List.cons_append, or_left_comm]

theorem lookup_nil_pairs (atoms : List Term) (ha : ∀ a ∈ atoms, ∃ s, a = .atom s) (q : Term) :
    (mapLookup (atoms.map (·, Term.nil)) q).isSome = Bool.true ↔ q ∈ atoms := by
  induction atoms with
  | nil => simp [mapLookup]
  | cons a rest ih =>
    obtain ⟨s, rfl⟩ := ha a List.mem_cons_self
    have ih := ih fun a m => ha a (List.mem_cons_of_mem _ m)
    rw [List.map_cons]
    by_cases e : compareExact (fuel q (.atom s)) q (.atom s) = .eq
    · obtain rfl := (compareExact_eq_atom _ _).mp e
      simp [mapLookup]
    · have ne : q ≠ .atom s := fun h => e ((compareExact_eq_atom _ _).mpr h)
      have hl : mapLookup ((Term.atom s, Term.nil) :: rest.map (·, Term.nil)) q = mapLookup (rest.map (·, Term.nil)) q := by
        simp [mapLookup, e]
      rw [hl, ih]
      simp [ne]

/-- `key_type/2` on atoms and kinds. -/
theorem key_type_run (atoms kinds : List Term) (ha : ∀ a ∈ atoms, ∃ s, a = .atom s)
    (hk : ∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ Y, Elixir.STTDescrProofsTest.«key_type/2» (D m) (Term.list atoms) (Term.list kinds) = .ok (.map Y) ∧
      KeyInv t n Y (· ∈ atoms) kinds := by
  cases atoms with
  | nil =>
    have base : KeyInv t n [] (· ∈ ([] : List Term)) [] :=
      ⟨Or.inr ⟨[], rfl, fun q h => by simp [mapLookup] at h, fun name w h => by simp [mapLookup] at h⟩,
        fun q => by simp [denD_map, mapLookup, dn_none], fun v hv => by simp [denD_map, mapLookup, dn_none] at hv,
        fun s ms => by simp at ms⟩
    obtain ⟨Y, rY, hY⟩ := kinds_type_run hm kinds hk [] _ [] base
    exact ⟨Y, by simpa [Elixir.STTDescrProofsTest.«key_type/2», Elixir.Module.Types.Descr.«none/0», Term.list] using rY,
      by simpa using hY⟩
  | cons a rest =>
    let S := (a :: rest).map (·, Term.nil)
    have hS : ∀ q, (mapLookup S q).isSome = Bool.true ↔ q ∈ a :: rest := lookup_nil_pairs _ ha
    have set : Erlang.sets.elements? (.map S) = some S := by
      simp only [Erlang.sets.elements?, List.all_eq_true]
      rw [ite_eq_left_iff.mpr fun h => absurd ?_ h]
      intro e me
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp (mem_of_mem_mapEntries me)
      rfl
    have base : KeyInv t n [(.atom "atom", .tuple #[.atom "union", .map S])] (· ∈ a :: rest) [] := by
      refine ⟨single_de (by simp [names]) (Or.inr (Or.inl ⟨rfl, ⟨Bool.true, S, rfl, set⟩, a, ?_⟩)), fun q => ?_,
        fun v hv nv => absurd ((denD_single _ _ v).mp hv).1 nv, fun s ms => by simp at ms⟩
      · simp [amemV, (hS a).mpr List.mem_cons_self]
      · rw [denD_single]
        simp [aPt, dn_atom, amemV, hS q]
    obtain ⟨Y, rY, hY⟩ := kinds_type_run hm kinds hk _ _ [] base
    refine ⟨Y, ?_, by simpa using hY⟩
    have pl : Term.properList? (Term.cons a (Term.list rest)) = some (a :: rest) := Term.properList?_list (a :: rest)
    simp only [Term.list] at pl ⊢
    simp [Elixir.STTDescrProofsTest.«key_type/2», Elixir.Module.Types.Descr.«atom/1»,
      Elixir.Module.Types.Descr.«atom_new/1», Erlang.erlang.«is_list/1», Erlang.sets.«from_list/2»,
      Erlang.sets.«from_list/1», pl]
    exact rY

/-- The keys of the given atoms and kinds. -/
def KeysOf (atoms kinds : List Term) : MKey → Prop
  | .atom s => .atom s ∈ atoms ∨ .atom "atom" ∈ kinds
  | .dom k _ => .atom (domKind k) ∈ kinds

/-- `map_split_keys_and_domains/1` on the key type of atoms and kinds selects their keys. -/
theorem key_split (atoms kinds : List Term) (ha : ∀ a ∈ atoms, ∃ s, a = .atom s)
    (hk : ∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    ∃ Y rs neg ds, Elixir.STTDescrProofsTest.«key_type/2» (D m) (Term.list atoms) (Term.list kinds) = .ok (.map Y) ∧
      Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) (.map Y) = .ok (splitT rs neg ds) ∧
      SplitOk rs neg ds ∧ ∀ κ, SplitKey rs neg ds κ ↔ KeysOf atoms kinds κ := by
  obtain ⟨Y, rY, hY⟩ := key_type_run (t := t) (n := n) atoms kinds ha hk (m := m) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hU : ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s := by
    intro S hS q hq
    have mem : ∀ q, (mapLookup S q).isSome = Bool.true → q ∈ atoms ∨ .atom "atom" ∈ kinds := fun q hq =>
      (hY.atoms q).mp ((denD_aPt q).mpr (by rw [hS]; simpa [amemV] using hq))
    rcases mem q hq with h | h
    · exact ha q h
    · obtain ⟨c, hc⟩ := fresh_str (keyStrs S)
      have := (denD_aPt (t := t) (n := n) (Y := Y) (.atom c)).mp ((hY.atoms _).mpr (Or.inr h))
      rw [hS] at this
      simp [amemV, lookup_fresh' hc] at this
  obtain ⟨rs, neg, ds, rs', ok, -, -, sa, sd⟩ := split_map hY.de hU (m := k) (by omega)
  refine ⟨Y, rs, neg, ds, rY, rs', ok, fun κ => ?_⟩
  cases κ with
  | atom s => rw [sa, hY.atoms]; rfl
  | dom k' i =>
    rw [sd]
    constructor
    · rintro ⟨v, hv, pv⟩
      by_cases va : v.1.1 = "atom"
      · exact absurd (by simpa [ptKind, va] using pv.symm) (domKind_ne_atom k')
      · show .atom (domKind k') ∈ kinds
        rw [← pv]; exact hY.kinds v hv va
    · intro h
      exact hY.wit _ h (domKind_ne_atom k')

end

end Elixir.STTDescrProofsTest.Nest
