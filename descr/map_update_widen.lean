namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-! `map_update_widen/3` for any constant update: the chain of `widen_line`, with the values a kind gets given by a
predicate `P` on kinds instead of a value. -/

/-- A domain update of `map_update_widen/3`: a kind, the tag's type there, and the new type, holding the values `P`
gives the kind. -/
def DomUpdP (E : Term → Prop) (den : Term → V → Prop) (tag : Term) (P : String → V → Prop) (d : String) (u : Term) :
    Prop :=
  ∃ nt, u = .tuple #[.atom d, tagType tag d, nt] ∧ E nt ∧ ∀ x, den nt x ↔ P d x

/-- A step of `map_widen_domains/3`: on negations, `discard` when the tag misses some old values, otherwise the kind
widened by the new type. -/
theorem widen_stepP (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag0 tagL acc : Term} (g0 : TagV E tag0)
    (gL : TagV E tagL) (gA : TagV E acc) {d : String} (hd : d ∈ domainKinds) {P : String → V → Prop} {nt : Term} (hnt : E nt)
    (snt : ∀ x, den nt x ↔ P d x) (neg : Bool) :
    (neg = Bool.true ∧ ¬SubAt den tagL tag0 d ∧
      (D (m + 2)).pure (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg])
        #[.tuple #[.atom d, tagType tagL d, nt], acc] = .error (.throw (.atom "discard"))) ∨
    ((neg = Bool.true → SubAt den tagL tag0 d) ∧ ∃ A, (D (m + 2)).pure
        (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg])
        #[.tuple #[.atom d, tagType tagL d, nt], acc] = .ok A ∧ TagV E A ∧
      ∀ kind ∈ domainKinds, ∀ x, den (tagType A kind) x ↔
        if kind = d then den (tagType tag0 d) x ∨ P d x else den (tagType acc kind) x) := by
  have pureE : ∀ a, (D (m + 2)).pure (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2
      #[tag0, boolAtom neg]) #[.tuple #[.atom d, tagType tagL d, nt], a] =
      Elixir.Module.Types.Descr.«-map_widen_domains/3-fun-0-/4» (D (m + 1)) tag0 (boolAtom neg)
        (Term.tuple #[.atom d, tagType tagL d, nt]) a := fun a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_widen_domains/3-fun-0-/2».pure]
  obtain ⟨sb, rsb, hsb⟩ := ef.sub (tagType_value ef.mopsE gL d) (tagType_value ef.mopsE g0 d)
  have sbI : sb = Bool.true ↔ SubAt den tagL tag0 d := ⟨hsb, fun h => by
    have := ef.subc (tagType_value ef.mopsE gL d) (tagType_value ef.mopsE g0 d) h (m + 1) (by omega)
    rw [rsb (m + 1) (by omega)] at this; cases sb <;> simp_all [boolAtom]⟩
  obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] (tagType_value ef.mopsE g0 d) hnt (m := m + 1) (by omega)
  obtain ⟨A, rA, gA', sA⟩ := replace_domain_any ef gA hd hc m
  by_cases bad : neg = Bool.true ∧ sb = Bool.false
  · obtain ⟨rfl, rfl⟩ := bad
    refine Or.inl ⟨rfl, fun h => absurd (sbI.mpr h) (by simp), ?_⟩
    rw [pureE, widen_dom_eval g0]
    simp [Lynx.Except.andAlso, boolAtom, rsb (m + 1) (by omega), Erlang.erlang.«not/1», Lynx.Term.isMember]
  · refine Or.inr ⟨fun hn => sbI.mp (by cases sb <;> simp_all), A, ?_, gA', fun kind mk x => ?_⟩
    · rw [pureE]
      rw [widen_dom_eval g0]
      cases neg <;> cases sb <;> simp_all [Lynx.Except.andAlso, boolAtom, rsb (m + 1) (by omega), Erlang.erlang.«not/1»,
        Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2»]
    · rw [sA kind mk x]
      by_cases k : kind = d
      · subst k; simp [sc, snt]
      · simp [k]


/-- The fold of `map_widen_domains/3` over the updates of some kinds: `discard` on negations missing old values,
otherwise the tag with the kinds widened by the value. -/
theorem widen_foldP (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag0 tagL : Term} (g0 : TagV E tag0)
    (gL : TagV E tagL) {P : String → V → Prop} (neg : Bool) :
    ∀ (Ds : List String) (U : List Term) (done : List String) (acc : Term), U.length = Ds.length →
      (∀ p ∈ Ds.zip U, DomUpdP E den tagL P p.1 p.2) → (∀ d ∈ Ds, d ∈ domainKinds) → TagV E acc →
      (∀ kind ∈ domainKinds, ∀ x, den (tagType acc kind) x ↔
        if kind ∈ done then den (tagType tag0 kind) x ∨ P kind x else den (tagType tag0 kind) x) →
      ((neg = Bool.true ∧ ∃ d ∈ Ds, ¬SubAt den tagL tag0 d) ∧ Erlang.lists.«foldl_1/3» (D (m + 2))
          (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) acc
          (Term.list U) = .error (.throw (.atom "discard"))) ∨
      ((neg = Bool.true → ∀ d ∈ Ds, SubAt den tagL tag0 d) ∧ ∃ r, Erlang.lists.«foldl_1/3» (D (m + 2))
          (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) acc
          (Term.list U) = .ok r ∧ TagV E r ∧
        ∀ kind ∈ domainKinds, ∀ x, den (tagType r kind) x ↔
          if kind ∈ done ++ Ds then den (tagType tag0 kind) x ∨ P kind x else den (tagType tag0 kind) x)
  | [], U, done, acc, lU, _, _, gA, sA => by
    obtain rfl : U = [] := List.eq_nil_of_length_eq_zero (by simpa using lU)
    exact Or.inr ⟨by simp, acc, by simp [Erlang.lists.«foldl_1/3»], gA, by simpa using sA⟩
  | d :: Ds, [], _, _, lU, _, _, _, _ => by simp at lU
  | d :: Ds, u :: U, done, acc, lU, fU, hD, gA, sA => by
    obtain ⟨nt, eu, hnt, snt⟩ := fU (d, u) (by simp)
    simp only at eu
    subst eu
    have hd := hD d (by simp)
    have fU' : ∀ p ∈ Ds.zip U, DomUpdP E den tagL P p.1 p.2 := fun p mp => fU p (by simp [mp])
    have hD' : ∀ d ∈ Ds, d ∈ domainKinds := fun d' md => hD d' (by simp [md])
    rcases widen_stepP ef hm g0 gL gA hd hnt snt neg with ⟨hn, hs, run⟩ | ⟨hs, A, run, gA', sA'⟩
    · refine Or.inl ⟨⟨hn, d, by simp, hs⟩, ?_⟩
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only at run ⊢
      simp [run]
    · have sA'' : ∀ kind ∈ domainKinds, ∀ x, den (tagType A kind) x ↔
          if kind ∈ done ++ [d] then den (tagType tag0 kind) x ∨ P kind x else den (tagType tag0 kind) x := by
        intro kind mk x
        rw [sA' kind mk x]
        by_cases k : kind = d
        · subst k; simp
        · rw [sA kind mk x]; simp [k]
      rcases widen_foldP ef hm g0 gL neg Ds U (done ++ [d]) A (by simpa using lU) fU' hD' gA' sA'' with
        ⟨⟨hn, d', md', hs'⟩, rr⟩ | ⟨hs', r, rr, gr, sr⟩
      · refine Or.inl ⟨⟨hn, d', by simp [md'], hs'⟩, ?_⟩
        rw [Erlang.lists.«foldl_1/3».eq_def]
        simp only at run rr ⊢
        simp [run, rr]
      · refine Or.inr ⟨fun hn d' md' => ?_, r, ?_, gr, fun kind mk x => by simpa using sr kind mk x⟩
        · rcases List.mem_cons.mp md' with rfl | md'
          · exact hs hn
          · exact hs' hn d' md'
        · rw [Erlang.lists.«foldl_1/3».eq_def]
          simp only at run rr ⊢
          simp [run, rr]


/-- `map_widen_domains/3` on the updates of some kinds. -/
theorem widen_tagP (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {tag0 tagL : Term} (g0 : TagV E tag0)
    (gL : TagV E tagL) {P : String → V → Prop} (neg : Bool) (Ds : List String) (U : List Term) (lU : U.length = Ds.length)
    (fU : ∀ p ∈ Ds.zip U, DomUpdP E den tagL P p.1 p.2) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∃ r, Elixir.Module.Types.Descr.«map_widen_domains/3» (D (m + 2)) tag0 (Term.list U) (boolAtom neg) = .ok r ∧
      ((neg = Bool.true ∧ (∃ d ∈ Ds, ¬SubAt den tagL tag0 d) ∧ r = .atom "discard") ∨
       ((neg = Bool.true → ∀ d ∈ Ds, SubAt den tagL tag0 d) ∧ TagV E r ∧
        ∀ kind ∈ domainKinds, ∀ x, den (tagType r kind) x ↔
          if kind ∈ Ds then den (tagType tag0 kind) x ∨ P kind x else den (tagType tag0 kind) x)) := by
  -- `lists:foldl/3` from `lists:foldl_1/3`.
  have toFoldl : ∀ res, Erlang.lists.«foldl_1/3» (D (m + 2))
      (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) tag0 (Term.list U) =
        res → Erlang.lists.«foldl/3» (D (m + 2))
      (.function "Elixir.Module.Types.Descr" "-map_widen_domains/3-fun-0-" 2 #[tag0, boolAtom neg]) tag0 (Term.list U) =
        res := fun res run => by
    cases U with
    | nil =>
      have e : res = .ok tag0 := by simpa [Term.list, Erlang.lists.«foldl_1/3», pure, Except.pure] using run.symm
      subst e
      simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
    | cons x xs =>
      rw [Erlang.lists.«foldl_1/3».eq_def] at run
      simpa [Erlang.lists.«foldl/3», Lynx.Except.guard, Erlang.erlang.«is_function/2», Term.list] using run
  rcases widen_foldP ef hm g0 gL neg Ds U [] tag0 lU fU hD g0 (fun kind _ x => by simp) with
    ⟨⟨hn, hs⟩, rr⟩ | ⟨hs, r, rr, gr, sr⟩
  · refine ⟨.atom "discard", ?_, Or.inl ⟨hn, hs, rfl⟩⟩
    simp only [Elixir.Module.Types.Descr.«map_widen_domains/3», pure_bind, toFoldl _ rr]
    simp [Lynx.Except.tryWith, Lynx.Exception.classTerm, Lynx.Exception.reason]
  · refine ⟨r, ?_, Or.inr ⟨hs, gr, fun kind mk x => by simpa using sr kind mk x⟩⟩
    simp only [Elixir.Module.Types.Descr.«map_widen_domains/3», pure_bind, toFoldl _ rr]
    simp


/-- What a widened tag allows at the keys of a kind: what the tag allows, or, at the updated kinds, a value of the
type. -/
def WTagP (den : Term → V → Prop) (tag : Term) (Ds : List String) (P : String → V → Prop) (kind : String) (o : Option V) : Prop :=
  o = none ∨ ∃ x, o = some x ∧ (den (tagType tag kind) x ∨ (kind ∈ Ds ∧ P kind x))

/-- Maps of a literal whose tag is widened at some kinds. -/
def WMSemP (den : Term → V → Prop) (tag : Term) (l : List (Term × Term)) (Ds : List String) (P : String → V → Prop) (w : MW V) : Prop :=
  (∀ s, FSem den tag l s (w (.atom s))) ∧ ∀ k i, WTagP den tag Ds P (domKind k) (w (.dom k i))

/-- A tag widened at kinds other than atoms holds the maps of the widened literal. -/
theorem msem_widenP (ef : EF nd E V den tl K) {tag r : Term} (g : TagV E tag) (gr : TagV E r) {Ds : List String}
    (hA : "atom" ∉ Ds) {P : String → V → Prop}
    (sr : ∀ kind ∈ domainKinds, ∀ x, den (tagType r kind) x ↔
      if kind ∈ Ds then den (tagType tag kind) x ∨ P kind x else den (tagType tag kind) x)
    (l : List (Term × Term)) (w : MW V) : MSem den r l w ↔ WMSemP den tag l Ds P w := by
  have atomT : ∀ o, TagSem den r "atom" o ↔ TagSem den tag "atom" o := fun o => by
    rw [tagSem_iff ef gr, tagSem_iff ef g]
    have := sr "atom" (by simp [domainKinds])
    simp only [hA, ↓reduceIte] at this
    simp [this]
  have domT : ∀ k o, TagSem den r (domKind k) o ↔ WTagP den tag Ds P (domKind k) o := fun k o => by
    rw [tagSem_iff ef gr, WTagP]
    have := sr (domKind k) (domKind_mem k)
    by_cases dk : domKind k ∈ Ds
    · simp only [dk, ↓reduceIte, true_and] at this ⊢; simp [this]
    · simp only [dk, ↓reduceIte, false_and, or_false] at this ⊢; simp [this]
  constructor
  · intro h
    refine ⟨fun s => ?_, fun k i => (domT k _).mp (h.doms k i)⟩
    have := h.atoms s
    unfold FSem at this ⊢
    split at this
    · exact this
    · exact (atomT _).mp this
  · rintro ⟨ha, hd⟩
    refine ⟨fun s => ?_, fun k i => (domT k _).mpr (hd k i)⟩
    have := ha s
    unfold FSem at this ⊢
    split at this
    · exact this
    · exact (atomT _).mpr this


/-- The maps a kept negation excludes after widening. -/
def NWideP (den : Term → V → Prop) (Ds : List String) (P : String → V → Prop) (N : Term) (w : MW V) : Prop :=
  ∃ (k : Int) (nt : Term) (nl : List (Term × Term)), N = .tuple #[.integer k, nt, fieldsTerm nl] ∧ WMSemP den nt nl Ds P w

/-- The fold of `map_update_widen/3` over the negations of a line: kept negations, widened, are removed. -/
theorem widen_negsP (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {tagL : Term} (gL : TagV E tagL) {P : String → V → Prop}
    (Ds : List String) (hA : "atom" ∉ Ds) (U : List Term) (lU : U.length = Ds.length)
    (fU : ∀ p ∈ Ds.zip U, DomUpdP E den tagL P p.1 p.2) (hD : ∀ d ∈ Ds, d ∈ domainKinds) :
    ∀ (negs : List Term), (∀ N ∈ negs, MapLitV E N) → ∀ (out : Term), MField E out →
      ∃ out', Erlang.lists.«foldl/3» (D (n + 3))
          (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-1-" 2 #[Term.list U]) out (Term.list negs) =
          .ok out' ∧ MField E out' ∧
        ∀ w, denMF E den out' w = Bool.true ↔ denMF E den out w = Bool.true ∧
          ∀ N ∈ negs, KeptNeg den tagL Ds N → ¬NWideP den Ds P N w := by
  intro negs lits out fo
  obtain ⟨r, ⟨o', eo, fo', so'⟩, run⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr"
    "-map_update_widen/3-fun-1-" #[Term.list U]
    (fun pre a => ∃ o', a = o' ∧ MField E o' ∧ ∀ w, denMF E den o' w = Bool.true ↔ denMF E den out w = Bool.true ∧
      ∀ N ∈ pre, KeptNeg den tagL Ds N → ¬NWideP den Ds P N w) negs
    (fun pre N acc mN ⟨o', ea, fo', so'⟩ => by
      subst ea
      obtain ⟨k, nt, nl, rfl, gn, snl⟩ := lits _ mN
      obtain ⟨r, rr, hr⟩ := widen_tagP ef (m := n) hn gn gL Bool.true Ds U lU fU hD
      replace rr : Elixir.Module.Types.Descr.«map_widen_domains/3» (D (n + 2)) nt (Term.list U) (.atom "true") = .ok r := rr
      have pureE : (D (n + 3)).pure (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-1-" 2
          #[Term.list U]) #[.tuple #[.integer k, nt, fieldsTerm nl], acc] =
          Elixir.Module.Types.Descr.«-map_update_widen/3-fun-1-/3» (D (n + 2)) (Term.list U)
            (.tuple #[.integer k, nt, fieldsTerm nl]) acc := by
        rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-1-/2».pure]
      rcases hr with ⟨-, ⟨d, md, hs⟩, rfl⟩ | ⟨hs, gr, sr⟩
      · -- Discarded: unchanged.
        refine ⟨acc, ⟨acc, rfl, fo', fun w => ?_⟩, ?_⟩
        · rw [so']
          constructor
          · rintro ⟨h, hn'⟩
            refine ⟨h, fun N mN kN => ?_⟩
            rcases List.mem_append.mp mN with mN | mN
            · exact hn' N mN kN
            · simp at mN; subst mN
              obtain ⟨k', nt', nl', e, ks⟩ := kN
              obtain ⟨-, rfl, -⟩ := tuple3_inj e
              exact absurd (ks d md) hs
          · rintro ⟨h, hn'⟩; exact ⟨h, fun N mN => hn' N (List.mem_append_left _ mN)⟩
        · rw [pureE]
          simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-1-/3», rr]
      · obtain ⟨nb, rnb, fnb, snb⟩ := map_new_leaf (den := den) ef gr snl
        obtain ⟨d', rd, fd, sd, -⟩ := map_diff_lh (den := den) fo' fnb
        refine ⟨d', ⟨d', rfl, fd, fun w => ?_⟩, ?_⟩
        · rw [sd, Bool.and_eq_true, so', Bool.not_eq_true']
          have nw : NWideP den Ds P (.tuple #[.integer k, nt, fieldsTerm nl]) w ↔ denMF E den nb w = Bool.true := by
            rw [snb, msem_widenP ef gn gr hA sr]
            constructor
            · rintro ⟨k', nt', nl', e, h⟩
              obtain ⟨-, rfl, e₃⟩ := tuple3_inj e
              rw [fieldsTerm_inj e₃]; exact h
            · intro h; exact ⟨k, nt, nl, rfl, h⟩
          constructor
          · rintro ⟨⟨h, hn'⟩, hb⟩
            refine ⟨h, fun N mN kN hN => ?_⟩
            rcases List.mem_append.mp mN with mN | mN
            · exact hn' N mN kN hN
            · simp at mN; subst mN
              rw [nw, hb] at hN; cases hN
          · rintro ⟨h, hn'⟩
            refine ⟨⟨h, fun N mN => hn' N (List.mem_append_left _ mN)⟩, ?_⟩
            cases hb : denMF E den nb w
            · rfl
            · exact absurd ((nw).mpr hb) (hn' _ (by simp) ⟨k, nt, nl, rfl, hs rfl⟩)
        · rw [pureE]
          have ne : r ≠ .atom "discard" := by
            rcases gr with rfl | rfl | ⟨dl, rfl, -⟩
            · simp
            · simp
            · exact fieldsTerm_ne_atom dl "discard"
          simp only [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-1-/3», rr, Lynx.Except.ok_bind]
          simp [rnb, rd])
    out ⟨out, rfl, fo, fun w => by simp⟩
  subst eo
  exact ⟨r, run, fo', so'⟩


/-- The values an update puts at the keys of a kind of a line: the new type, when forcing or when the line's tag gives
the kind a value. -/
def NewP (den : Term → V → Prop) (nt : Term) (md : String) (tag : Term) (d : String) (x : V) : Prop :=
  den nt x ∧ (md = "force" ∨ ∃ y, den (tagType tag d) y)

/-- Kinds whose update field is not empty, at a line's tag. -/
def UpdNE (den : Term → V → Prop) (nt : Term) (nopt : Bool) (md : String) (tag : Term) (d : String) : Prop :=
  md = "keep" ∨ ((md = "force" ∨ ∃ y, den (tagType tag d) y) ∧ (nopt = Bool.true ∨ ∃ x, den nt x))

/-- The update of one domain by `map_update_widen/3`, for any constant update: nothing when the new field is empty,
otherwise the kind, the tag's type there, and the new type. -/
theorem widen_update_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) {tag : Term} (g : TagV E tag) (d : String) :
    ∃ r, Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3» (D m) (cOp nt nopt md) tag (.atom d) = .ok r ∧
      ((¬UpdNE den nt nopt md tag d ∧ r = .nil) ∨
        (UpdNE den nt nopt md tag d ∧ ∃ u, r = Term.list [u] ∧ DomUpdP E den tag (NewP den nt md tag) d u)) := by
  obtain ⟨F, rF, hF, sF⟩ := update_field_gen ef hm hnt nopt hmd (old := .tuple #[tagType tag d, .atom "true"])
    ⟨_, Bool.true, rfl, tagType_value ef.mopsE g d⟩
  obtain ⟨t, o, rfl, ht⟩ := hF
  obtain ⟨b, rb, sb⟩ := field_empty_val (den := den) ef hm ⟨t, o, rfl, ht⟩
  have o1 : ∀ x, FieldSem den (.tuple #[tagType tag d, .atom "true"]) (some x) ↔ den (tagType tag d) x := fun x => by
    rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; simp
  have o0 : FieldSem den (.tuple #[tagType tag d, .atom "true"]) none := by
    rw [show (Term.atom "true") = boolAtom Bool.true from rfl, fieldSem_mk]; simp
  have st : ∀ x, den t x ↔ NewP den nt md tag d x := fun x => by
    have := sF (some x)
    rw [fieldSem_mk, NewF] at this
    simp only [o1, o0, true_and] at this
    simp only [reduceCtorEq, false_and, Option.some.injEq, exists_eq_left', false_or] at this
    rw [this, NewP]
    grind
  have ne : (∃ o', NewF den nt nopt md (FieldSem den (.tuple #[tagType tag d, .atom "true"])) o') ↔
      UpdNE den nt nopt md tag d := by
    simp only [NewF, o1, o0, true_and, UpdNE]
    constructor
    · rintro ⟨o', h⟩
      grind
    · rintro (rfl | ⟨hf, hn⟩)
      · exact ⟨none, by simp⟩
      · have val : ∃ o', (o' = none ∧ nopt = Bool.true) ∨ ∃ x, o' = some x ∧ den nt x := by
          rcases hn with hn | ⟨x, hx⟩
          · exact ⟨none, Or.inl ⟨rfl, hn⟩⟩
          · exact ⟨some x, Or.inr ⟨x, rfl, hx⟩⟩
        obtain ⟨o', ho'⟩ := val
        exact ⟨o', by grind⟩
  have bI : b = Bool.true ↔ ¬UpdNE den nt nopt md tag d := by
    rw [sb, ← ne]
    simp only [sF, not_exists]
  have ev : Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3» (D m) (cOp nt nopt md) tag (.atom d) =
      .ok (if b = Bool.true then .nil else Term.list [.tuple #[.atom d, tagType tag d, t]]) := by
    rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
    · simp only [tagType, ↓reduceIte] at rF ⊢
      simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3», rF]
      rw [rb]; cases b <;> simp [boolAtom, Term.list]
    · have tc : tagType (.atom "closed") d = .map [] := by simp [tagType]
      rw [tc] at rF ⊢
      simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3», rF]
      rw [rb]; cases b <;> simp [boolAtom, Term.list]
    · have fd := find_dom d dv
      have ne := fieldsTerm_ne_atom dl
      have il := is_list_fieldsTerm dl
      have gt : Elixir.Module.Types.Descr.«fields_get/3» (fieldsTerm dl) (.atom d) (.map []) =
          .ok (tagType (fieldsTerm dl) d) := by
        rw [tagType_dom]
        simp [Elixir.Module.Types.Descr.«fields_get/3», fd]
        cases mapLookup dl (.atom d) <;> rfl
      generalize tagType (fieldsTerm dl) d = TT at gt rF ⊢
      generalize fieldsTerm dl = T at fd ne il gt
      rw [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-0-/3».eq_def]
      simp only
      split
      · exact absurd rfl (ne _)
      · exact absurd rfl (ne _)
      · simp [il, gt, rF]
        rw [rb]; cases b <;> simp [boolAtom, Term.list]
  refine ⟨_, ev, ?_⟩
  by_cases hb : b = Bool.true
  · exact Or.inl ⟨bI.mp hb, by simp [hb]⟩
  · refine Or.inr ⟨Classical.not_not.mp fun h => hb (bI.mpr h), _, by simp [hb], t, rfl, ht, st⟩

/-- The domain updates of a line, by `lists:flatmap/2` over the domains, for any constant update: the kinds whose new
field is not empty. -/
theorem widen_updates_gen (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) {tag : Term} (g : TagV E tag) :
    ∀ Ds : List String, ∃ (Ds' : List String) (U : List Term), Erlang.lists.«flatmap_1/2» (D (m + 1))
        (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[cOp nt nopt md, tag])
        (Term.list (Ds.map Term.atom)) = .ok (Term.list U) ∧ U.length = Ds'.length ∧
      (∀ p ∈ Ds'.zip U, DomUpdP E den tag (NewP den nt md tag) p.1 p.2) ∧
      ∀ d, d ∈ Ds' ↔ d ∈ Ds ∧ UpdNE den nt nopt md tag d
  | [] => ⟨[], [], by simp [Erlang.lists.«flatmap_1/2», Term.list], rfl, by simp, by simp⟩
  | d :: Ds => by
    obtain ⟨r, rr, hr⟩ := widen_update_gen ef hm hnt nopt hmd g d
    obtain ⟨Ds', U, rU, lU, fU, mU⟩ := widen_updates_gen ef hm hnt nopt hmd g Ds
    have step : ∀ r', (r' = [] ∨ ∃ u, r' = [u]) → r = Term.list r' → Erlang.lists.«flatmap_1/2» (D (m + 1))
        (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[cOp nt nopt md, tag])
        (Term.list ((d :: Ds).map Term.atom)) = .ok (Term.list (r' ++ U)) := fun r' hr' e => by
      subst e
      rw [Erlang.lists.«flatmap_1/2».eq_def]
      rcases hr' with rfl | ⟨u, rfl⟩
      · simp only [Term.list, List.map] at rU rr ⊢
        simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-0-/1».pure, rr, rU]
      · simp only [Term.list, List.map] at rU rr ⊢
        simp [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-0-/1».pure, rr, rU]
    rcases hr with ⟨nu, rfl⟩ | ⟨hu, u, rfl, du⟩
    · refine ⟨Ds', U, by simpa using step [] (Or.inl rfl) rfl, lU, fU, fun d' => ?_⟩
      rw [mU d']
      constructor
      · rintro ⟨m', h⟩; exact ⟨List.mem_cons_of_mem _ m', h⟩
      · rintro ⟨m', h⟩
        rcases List.mem_cons.mp m' with rfl | m'
        · exact absurd h nu
        · exact ⟨m', h⟩
    · refine ⟨d :: Ds', u :: U, by simpa using step [u] (Or.inr ⟨u, rfl⟩) rfl, by simp [lU], fun p mp => ?_, fun d' => ?_⟩
      · rcases List.mem_cons.mp mp with rfl | mp
        · exact du
        · exact fU p mp
      · rw [List.mem_cons, mU d', List.mem_cons]
        constructor
        · rintro (rfl | ⟨m', h⟩)
          · exact ⟨Or.inl rfl, hu⟩
          · exact ⟨Or.inr m', h⟩
        · rintro ⟨rfl | m', h⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨m', h⟩

theorem zip_cover {α β : Type} {A : List α} {B : List β} (h : B.length = A.length) :
    (∀ b ∈ B, ∃ a ∈ A, (a, b) ∈ A.zip B) ∧ ∀ a ∈ A, ∃ b ∈ B, (a, b) ∈ A.zip B := by
  constructor
  · intro b mb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mb
    exact ⟨A[i]'(by omega), List.getElem_mem _, List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩⟩
  · intro a ma
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ma
    exact ⟨B[i]'(by omega), List.getElem_mem _, List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩⟩

/-- The maps a line gives when widening some kinds by the values `P` gives them. -/
def WLineP (den : Term → V → Prop) (L : Term) (Ds : List String) (P : String → V → Prop) (w : MW V) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    WMSemP den tag l Ds P w ∧ ∀ N ∈ negs, KeptNeg den tag Ds N → ¬NWideP den Ds P N w

/-- Whether a widened line is among the updated maps: when keeping, no kind loses the values of the line's tag and the
line does not hold the empty map; otherwise, some kind gets a value. -/
def WPres (den : Term → V → Prop) (L tag : Term) (Ds : List String) (P : String → V → Prop) (md : String) : Prop :=
  (md = "keep" → (¬∃ d ∈ Ds, (∃ y, den (tagType tag d) y) ∧ ¬∃ x, P d x) ∧ ¬InMLine den L wNone) ∧
    (md ≠ "keep" → ∃ d ∈ Ds, ∃ x, P d x)

/-- A line of `map_update_widen/3`, for any constant update. -/
theorem widen_line_gen (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) (Ds : List String) (hA : "atom" ∉ Ds) (hD : ∀ d ∈ Ds, d ∈ domainKinds)
    {tag : Term} {l : List (Term × Term)} {negs : List Term} (hL : MLine E (.tuple #[tag, fieldsTerm l, Term.list negs]))
    (Up Un : List Term) :
    ∃ Ds' : List String, (∀ d, d ∈ Ds' ↔ d ∈ Ds ∧ UpdNE den nt nopt md tag d) ∧
      ((Ds' = [] ∧ (D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
          #[Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.tuple #[tag, fieldsTerm l, Term.list negs],
            .tuple #[Term.list Up, Term.list Un]] = .ok (.tuple #[Term.list Up, Term.list Un])) ∨
       (Ds' ≠ [] ∧ ∃ out, MField E out ∧ (∀ w, denMF E den out w = Bool.true ↔
          WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds' (NewP den nt md tag) w) ∧
        (((D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
          #[Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.tuple #[tag, fieldsTerm l, Term.list negs],
            .tuple #[Term.list Up, Term.list Un]] = .ok (.tuple #[Term.list Up, Term.list (out :: Un)]) ∧
          (¬WPres den (.tuple #[tag, fieldsTerm l, Term.list negs]) tag Ds' (NewP den nt md tag) md ∨ HasReq l)) ∨
         ((D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
          #[Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.tuple #[tag, fieldsTerm l, Term.list negs],
            .tuple #[Term.list Up, Term.list Un]] = .ok (.tuple #[Term.list (out :: Up), Term.list Un]) ∧
          WPres den (.tuple #[tag, fieldsTerm l, Term.list negs]) tag Ds' (NewP den nt md tag) md ∧ ¬HasReq l)))) := by
  have hL' := hL
  obtain ⟨tag', l', negs', e, g, sl, lits⟩ := hL'
  obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
  obtain rfl := fieldsTerm_inj e₂
  obtain rfl := list_inj e₃
  obtain ⟨Ds', U, rU, lU, fU, mU⟩ := widen_updates_gen ef (m := n + 3) (by omega) hnt nopt hmd g Ds
  have hD' : ∀ d ∈ Ds', d ∈ domainKinds := fun d m' => hD d ((mU d).mp m').1
  have hA' : "atom" ∉ Ds' := fun m' => hA ((mU _).mp m').1
  have pureE : ∀ a, (D (n + 5)).pure (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-3-" 2
      #[Term.list (Ds.map Term.atom), cOp nt nopt md]) #[.tuple #[tag, fieldsTerm l, Term.list negs], a] =
      Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4» (D (n + 4)) (Term.list (Ds.map Term.atom))
        (cOp nt nopt md) (.tuple #[tag, fieldsTerm l, Term.list negs]) a := fun a => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_widen/3-fun-3-/2».pure]
  have flat : Erlang.lists.«flatmap/2» (D (n + 4))
      (.function "Elixir.Module.Types.Descr" "-map_update_widen/3-fun-0-" 1 #[cOp nt nopt md, tag])
      (Term.list (Ds.map Term.atom)) = .ok (Term.list U) := by
    simpa [Erlang.lists.«flatmap/2», Erlang.erlang.«is_function/2»] using rU
  refine ⟨Ds', mU, ?_⟩
  by_cases e0 : Ds' = []
  · subst e0
    obtain rfl : U = [] := List.eq_nil_of_length_eq_zero lU
    refine Or.inl ⟨rfl, ?_⟩
    rw [pureE]
    simp [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, Term.list, Erlang.erlang.«==/2»]
  refine Or.inr ⟨e0, ?_⟩
  obtain ⟨T, rT, hT⟩ := widen_tagP ef (m := n + 2) (by omega) g g Bool.false Ds' U lU fU hD'
  rcases hT with ⟨h, -⟩ | ⟨-, gT, sT⟩
  · cases h
  replace rT : Elixir.Module.Types.Descr.«map_widen_domains/3» (D (n + 4)) tag (Term.list U) (.atom "false") = .ok T := rT
  obtain ⟨b0, rb0, fb0, sb0⟩ := map_new_leaf (den := den) ef gT sl
  obtain ⟨out, rout, fout, sout⟩ := widen_negsP ef (n := n + 1) (by omega) g Ds' hA' U lU fU hD' negs lits b0 fb0
  have semOut : ∀ w, denMF E den out w = Bool.true ↔
      WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds' (NewP den nt md tag) w := by
    intro w
    rw [sout, sb0, msem_widenP ef g gT hA' sT]
    constructor
    · rintro ⟨h, hn'⟩; exact ⟨tag, l, negs, rfl, h, hn'⟩
    · rintro ⟨tag', l', negs', e, h, hn'⟩
      obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
      obtain rfl := fieldsTerm_inj e₂
      obtain rfl := list_inj e₃
      exact ⟨h, hn'⟩
  -- Whether the line is among the updated maps.
  have rWP := widenPair_eval (n + 4) U fun u mu => by
    obtain ⟨d, -, mp⟩ := (zip_cover lU).1 u mu
    obtain ⟨nt', eu, -, -⟩ := fU _ mp
    exact ⟨_, _, _, eu⟩
  obtain ⟨bp, rbp, sbp⟩ := present_gen (den := den) ef (m := n + 1) (by omega) [.tuple #[tag, fieldsTerm l, Term.list negs]]
    (by simpa using hL) nt nopt hmd (U.map domPair) fun p mp => by
      obtain ⟨u, mu, rfl⟩ := List.mem_map.mp mp
      obtain ⟨d, -, mpz⟩ := (zip_cover lU).1 u mu
      obtain ⟨nt', eu, hnt', -⟩ := fU _ mpz
      simp only at eu
      subst eu
      exact ⟨_, nt', by simp [domPair], tagType_value ef.mopsE g d, hnt'⟩
  -- The pairs are the kinds' old types and new values.
  have pairsI : ∀ (A : Prop → Prop → Prop), (∃ p ∈ U.map domPair, ∃ o n', p = .tuple #[o, n'] ∧
      A (∃ x, den o x) (∃ x, den n' x)) ↔ ∃ d ∈ Ds', A (∃ y, den (tagType tag d) y) (∃ x, NewP den nt md tag d x) := by
    intro A
    constructor
    · rintro ⟨p, mp, o, n', e, h⟩
      obtain ⟨u, mu, rfl⟩ := List.mem_map.mp mp
      obtain ⟨d, md', mpz⟩ := (zip_cover lU).1 u mu
      obtain ⟨nt', eu, -, snt⟩ := fU _ mpz
      simp only at eu
      subst eu
      simp only [domPair, Term.tuple.injEq, List.cons.injEq, and_true, Array.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [propext (exists_congr snt)] at h
      exact ⟨d, md', h⟩
    · rintro ⟨d, md', h⟩
      obtain ⟨u, mu, mpz⟩ := (zip_cover lU).2 d md'
      obtain ⟨nt', eu, -, snt⟩ := fU _ mpz
      simp only at eu
      subst eu
      rw [← propext (exists_congr snt)] at h
      exact ⟨_, List.mem_map_of_mem mu, _, nt', by simp [domPair], h⟩
  have presI : bp = Bool.true ↔
      WPres den (.tuple #[tag, fieldsTerm l, Term.list negs]) tag Ds' (NewP den nt md tag) md := by
    rw [sbp, WPres]
    have k1 := pairsI (fun o n => o ∧ ¬n)
    have k2 := pairsI (fun _ n => n)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun hk => ⟨fun hu => (h1 hk).1 ?_, (h1 hk).2 _ (List.mem_singleton_self _)⟩, fun hk => k2.mp (h2 hk)⟩
      obtain ⟨p, mp, o, n', e, ho, hn⟩ := k1.mpr hu
      exact ⟨p, mp, o, n', e, fun x hx => hn ⟨x, hx⟩, ho⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun hk => ⟨fun ⟨p, mp, o, n', e, hn, ho⟩ => (h1 hk).1 (k1.mp ⟨p, mp, o, n', e, ho, fun ⟨x, hx⟩ => hn x hx⟩),
        fun L' mL' => by simp at mL'; subst mL'; exact (h1 hk).2⟩, fun hk => k2.mpr (h2 hk)⟩
  have neU : Erlang.erlang.«==/2» (Term.list U) .nil = .ok (.atom "false") := by
    cases U with
    | nil => cases Ds' with
      | nil => exact absurd rfl e0
      | cons _ _ => simp at lU
    | cons u U' => simp [Term.list, eqq_val, boolAtom]
  refine ⟨out, fout, semOut, ?_⟩
  cases bp
  · refine Or.inl ⟨?_, Or.inl fun h => by have := presI.mpr h; cases this⟩
    rw [pureE]
    simp only [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, neU, rT, rb0, rout, rWP, rbp,
      Lynx.Except.ok_bind, pure_bind]
    simp [boolAtom, Lynx.Term.isMember]
  · rcases domains_add (n + 3) out sl Up Un with ⟨ra, hr⟩ | ⟨ra, hr⟩
    · refine Or.inl ⟨?_, Or.inr hr⟩
      rw [pureE]
      simp only [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, neU, rT, rb0, rout, rWP, rbp,
        Lynx.Except.ok_bind, pure_bind]
      simp [boolAtom, Lynx.Term.isMember, ra]
    · refine Or.inr ⟨?_, presI.mp rfl, hr⟩
      rw [pureE]
      simp only [Elixir.Module.Types.Descr.«-map_update_widen/3-fun-3-/4», flat, neU, rT, rb0, rout, rWP, rbp,
        Lynx.Except.ok_bind, pure_bind]
      simp [boolAtom, Lynx.Term.isMember, ra]

theorem wlineP_congr {L : Term} {A B : List String} (h : ∀ d, d ∈ A ↔ d ∈ B) {P : String → V → Prop} {w : MW V} :
    WLineP den L A P w ↔ WLineP den L B P w := by
  simp only [WLineP, WMSemP, WTagP, KeptNeg, NWideP, h]

theorem wPres_congr {L tag : Term} {A B : List String} (h : ∀ d, d ∈ A ↔ d ∈ B) {P : String → V → Prop}
    {md : String} : WPres den L tag A P md ↔ WPres den L tag B P md := by
  simp only [WPres, h]

/-- A literal with a required field holds no empty map. -/
theorem wmsemP_ne_none {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l) (hr : HasReq l) {Ds : List String}
    {P : String → V → Prop} {w : MW V} (h : WMSemP den tag l Ds P w) : w ≠ wNone := by
  rintro rfl
  obtain ⟨e, me, t, he⟩ := hr
  obtain ⟨⟨s, es⟩, -⟩ := sl.1 e me
  have := h.1 s
  unfold FSem at this
  rw [lookup_of_mem sl me es] at this
  simp only at this
  rw [he, show (Term.atom "false") = boolAtom Bool.false from rfl, fieldSem_mk] at this
  simp [wNone] at this

/-- The maps `map_update_widen/3` gives from a line, for any constant update: the widened line, at the kinds whose
new field is not empty, without the empty map when the line is updated. -/
def WLG (den : Term → V → Prop) (nt : Term) (nopt : Bool) (md : String) (Ds : List String) (L : Term) (w : MW V) :
    Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    ∃ Ds' : List String, (∀ d, d ∈ Ds' ↔ d ∈ Ds ∧ UpdNE den nt nopt md tag d) ∧ Ds' ≠ [] ∧
      WLineP den L Ds' (NewP den nt md tag) w ∧ (WPres den L tag Ds' (NewP den nt md tag) md → w ≠ wNone)

/-- `map_update_widen/3` for any constant update at kinds other than atoms. -/
theorem widen_run_gen (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {nt : Term} (hnt : E nt) (nopt : Bool)
    {md : String} (hmd : Mode md) (Ds : List String) (hA : "atom" ∉ Ds) (hD : ∀ d ∈ Ds, d ∈ domainKinds)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) :
    ∃ R, Elixir.Module.Types.Descr.«map_update_widen/3» (D (n + 5)) (Term.list lines) (Term.list (Ds.map Term.atom))
        (cOp nt nopt md) = .ok (.map R) ∧ MapsD E den R (fun w => ∃ L ∈ lines, WLG den nt nopt md Ds L w) := by
  obtain ⟨r, ⟨Up, Un, rfl, fUp, fUn, sU⟩, run⟩ := foldl_rel_at (m := n + 5) "Elixir.Module.Types.Descr"
    "-map_update_widen/3-fun-3-" #[Term.list (Ds.map Term.atom), cOp nt nopt md]
    (fun pre a => ∃ Up Un, a = .tuple #[Term.list Up, Term.list Un] ∧ (∀ b ∈ Up, MField E b) ∧ (∀ b ∈ Un, MField E b) ∧
      ∀ w, (((∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone) ∨ ∃ b ∈ Un, denMF E den b w = Bool.true) ↔
        ∃ L ∈ pre, WLG den nt nopt md Ds L w) lines
    (fun pre L a mL ⟨Up, Un, ea, fUp, fUn, sU⟩ => by
      subst ea
      obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hl L mL
      obtain ⟨Ds', mD, h⟩ := widen_line_gen ef hn hnt nopt hmd Ds hA hD (hl _ mL) Up Un
      -- The maps the new line gives.
      have wlg : ∀ w, WLG den nt nopt md Ds (.tuple #[tag, fieldsTerm l, Term.list negs]) w ↔
          Ds' ≠ [] ∧ WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds' (NewP den nt md tag) w ∧
            (WPres den (.tuple #[tag, fieldsTerm l, Term.list negs]) tag Ds' (NewP den nt md tag) md → w ≠ wNone) := by
        intro w
        constructor
        · rintro ⟨tag', l', negs', e, Ds'', mD'', ne'', hw, hp⟩
          obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
          obtain rfl := fieldsTerm_inj e₂
          obtain rfl := list_inj e₃
          have eq : ∀ d, d ∈ Ds'' ↔ d ∈ Ds' := fun d => (mD'' d).trans (mD d).symm
          refine ⟨fun e0 => ne'' ?_, (wlineP_congr eq).mp hw, fun p => hp ((wPres_congr eq).mpr p)⟩
          cases Ds'' with
          | nil => rfl
          | cons d _ => exact absurd ((eq d).mp List.mem_cons_self) (by simp [e0])
        · rintro ⟨ne', hw, hp⟩
          exact ⟨tag, l, negs, rfl, Ds', mD, ne', hw, hp⟩
      have grow : ∀ (X : MW V → Prop), (∀ w, (((∃ b ∈ Up, denMF E den b w = Bool.true) ∧ w ≠ wNone) ∨
          ∃ b ∈ Un, denMF E den b w = Bool.true) ↔ ∃ L ∈ pre, WLG den nt nopt md Ds L w) →
          (∀ w, X w ↔ WLG den nt nopt md Ds (.tuple #[tag, fieldsTerm l, Term.list negs]) w) →
          ∀ w, ((∃ L ∈ pre, WLG den nt nopt md Ds L w) ∨ X w) ↔
            ∃ L ∈ pre ++ [.tuple #[tag, fieldsTerm l, Term.list negs]], WLG den nt nopt md Ds L w := by
        intro X _ hX w
        rw [hX]
        constructor
        · rintro (⟨L', mL', h'⟩ | h')
          · exact ⟨L', List.mem_append_left _ mL', h'⟩
          · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h'⟩
        · rintro ⟨L', mL', h'⟩
          rcases List.mem_append.mp mL' with mL' | mL'
          · exact Or.inl ⟨L', mL', h'⟩
          · simp at mL'; subst mL'; exact Or.inr h'
      rcases h with ⟨rfl, run⟩ | ⟨ne', out, fout, sout, ⟨run, hp⟩ | ⟨run, hp, hr⟩⟩
      · refine ⟨_, ⟨Up, Un, rfl, fUp, fUn, fun w => ?_⟩, run⟩
        rw [sU w, ← grow (fun _ => False) sU (fun w => by rw [wlg]; simp) w]
        simp
      · refine ⟨_, ⟨Up, out :: Un, rfl, fUp, fun b mb => ?_, fun w => ?_⟩, run⟩
        · rcases List.mem_cons.mp mb with rfl | mb
          · exact fout
          · exact fUn b mb
        · rw [← grow (fun w => denMF E den out w = Bool.true) sU (fun w => by
            rw [wlg, sout]
            constructor
            · intro hw
              refine ⟨ne', hw, fun p => ?_⟩
              rcases hp with np | hr
              · exact absurd p np
              · obtain ⟨tag', l', negs', e, hm, -⟩ := hw
                obtain ⟨rfl, e₂, -⟩ := tuple3_inj e
                obtain rfl := fieldsTerm_inj e₂
                exact wmsemP_ne_none sl hr hm
            · rintro ⟨-, hw, -⟩; exact hw) w, ← sU w]
          simp only [List.mem_cons, exists_eq_or_imp]
          constructor
          · rintro (h | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
            · exact Or.inl (Or.inr h)
          · rintro ((h | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl h)
      · refine ⟨_, ⟨out :: Up, Un, rfl, fun b mb => ?_, fUn, fun w => ?_⟩, run⟩
        · rcases List.mem_cons.mp mb with rfl | mb
          · exact fout
          · exact fUp b mb
        · rw [← grow (fun w => denMF E den out w = Bool.true ∧ w ≠ wNone) sU (fun w => by
            rw [wlg, sout]
            constructor
            · rintro ⟨hw, nw⟩; exact ⟨ne', hw, fun _ => nw⟩
            · rintro ⟨-, hw, hn'⟩; exact ⟨hw, hn' hp⟩) w, ← sU w]
          simp only [List.mem_cons, exists_eq_or_imp]
          constructor
          · rintro (⟨h | h, nw⟩ | h)
            · exact Or.inr ⟨h, nw⟩
            · exact Or.inl (Or.inl ⟨h, nw⟩)
            · exact Or.inl (Or.inr h)
          · rintro ((h | h) | h)
            · exact Or.inl ⟨Or.inr h.1, h.2⟩
            · exact Or.inr h
            · exact Or.inl ⟨Or.inl h.1, h.2⟩)
    (.tuple #[.nil, .nil]) ⟨[], [], rfl, by simp, by simp, fun w => by simp⟩
  obtain ⟨R, rR, mR⟩ := domains_result ef (m := n + 3) (by omega) Up Un fUp fUn
  refine ⟨R, ?_, mR.1, mR.2.1, fun w => (mR.2.2 w).trans (sU w)⟩
  simp [Elixir.Module.Types.Descr.«map_update_widen/3», run]
  simpa [Term.list] using rR

/-- `w` agrees with `u` off the kinds `Ds`, and at the keys of `F` of those kinds is absent, kept, or holds a value
`P` gives the kind. -/
def AgreeP (Ds : List String) (P : String → V → Prop) (F : List MKey) (w u : MW V) : Prop :=
  (∀ s, w (.atom s) = u (.atom s)) ∧ (∀ k i, domKind k ∉ Ds → w (.dom k i) = u (.dom k i)) ∧
    ∀ k i, .dom k i ∈ F → domKind k ∈ Ds →
      (w (.dom k i) = none ∨ w (.dom k i) = u (.dom k i) ∨ ∃ x, w (.dom k i) = some x ∧ P (domKind k) x)

theorem AgreeP.mono {Ds : List String} {P : String → V → Prop} {F G : List MKey} {w u : MW V}
    (h : AgreeP Ds P G w u) (sub : ∀ κ ∈ F, κ ∈ G) : AgreeP Ds P F w u :=
  ⟨h.1, h.2.1, fun k i m dk => h.2.2 k i (sub _ m) dk⟩

theorem wline_witnessP (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) {Ds : List String} (hA : "atom" ∉ Ds)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) {P : String → V → Prop} {w : MW V} (hw : WLineP den L Ds P w) (F : List MKey) :
    ∃ u, InMLine den L u ∧ (∀ s, w (.atom s) = u (.atom s)) ∧ (∀ k i, domKind k ∉ Ds → w (.dom k i) = u (.dom k i)) ∧
      ∀ k i, .dom k i ∈ F → domKind k ∈ Ds →
        (w (.dom k i) = none ∨ w (.dom k i) = u (.dom k i) ∨ ∃ x, w (.dom k i) = some x ∧ P (domKind k) x) := by
  classical
  obtain ⟨tag, l, negs, rfl, hwm, hkn⟩ := hw
  obtain ⟨tag', l', negs', e, g, sl, lits⟩ := hL
  obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
  obtain rfl := fieldsTerm_inj e₂
  obtain rfl := list_inj e₃
  -- What escapes a dropped negation.
  let Esc : Term → Fin 11 × V → Prop := fun N p => domKind p.1 ∈ Ds ∧ den (tagType tag (domKind p.1)) p.2 ∧
    ∀ (kN : Int) (nt : Term) (nl : List (Term × Term)), N = .tuple #[.integer kN, nt, fieldsTerm nl] →
      ¬den (tagType nt (domKind p.1)) p.2
  let pick : Term → Option (Fin 11 × V) := fun N => if h : ∃ p, Esc N p then some h.choose else none
  have exDrop : ∀ N ∈ negs, ¬KeptNeg den tag Ds N → ∃ p, Esc N p := by
    intro N mN nk
    obtain ⟨kN, nt, nl, rfl, -, -⟩ := lits N mN
    have : ¬∀ d ∈ Ds, SubAt den tag nt d := fun h => nk ⟨kN, nt, nl, rfl, h⟩
    obtain ⟨d, hd⟩ := Classical.not_forall.mp this
    obtain ⟨md, hd⟩ := Classical.not_imp.mp hd
    obtain ⟨y, hy⟩ := Classical.not_forall.mp hd
    obtain ⟨hy₁, hy₂⟩ := Classical.not_imp.mp hy
    have dA : d ≠ "atom" := fun h => hA (h ▸ md)
    obtain ⟨k, rfl⟩ := domKind_of (hD _ md) dA
    refine ⟨(k, y), md, hy₁, fun kN' nt' nl' e' => ?_⟩
    obtain ⟨-, rfl, -⟩ := tuple3_inj e'
    exact hy₂
  let J := freshIdx F
  let isOld : Fin 11 → Option V → Prop := fun k o => ∃ x, o = some x ∧ den (tagType tag (domKind k)) x
  let u : MW V := fun κ => match κ with
    | .atom s => w (.atom s)
    | .dom k i => if domKind k ∈ Ds then
        (if MKey.dom k i ∈ F then (if isOld k (w (.dom k i)) then w (.dom k i) else none)
         else if J ≤ i then (match negs[i - J]? with
             | some N => (match pick N with | some p => if p.1 = k then some p.2 else none | none => none)
             | none => none)
         else none)
      else w (.dom k i)
  have pickOk : ∀ N p, pick N = some p → Esc N p := by
    intro N p hp
    simp only [pick] at hp
    split at hp
    · rename_i h; cases hp; exact h.choose_spec
    · cases hp
  have uA : ∀ s, u (.atom s) = w (.atom s) := fun s => rfl
  have uN : ∀ k i, domKind k ∉ Ds → u (.dom k i) = w (.dom k i) := fun k i h => by simp [u, h]
  have uF : ∀ k i, MKey.dom k i ∈ F → domKind k ∈ Ds →
      u (.dom k i) = if isOld k (w (.dom k i)) then w (.dom k i) else none := fun k i m h => by simp [u, h, m]
  -- Every value of the witness at a domain key is allowed by the tag.
  have allowed : ∀ k i, TagSem den tag (domKind k) (u (.dom k i)) := by
    intro k i
    rw [tagSem_iff ef g]
    by_cases dk : domKind k ∈ Ds
    · by_cases mF : MKey.dom k i ∈ F
      · rw [uF k i mF dk]
        split
        · rename_i h; obtain ⟨x, e, hx⟩ := h; exact Or.inr ⟨x, e, hx⟩
        · exact Or.inl rfl
      · simp only [u, dk, ↓reduceIte, mF]
        split
        · cases hN : negs[i - J]? with
          | none => exact Or.inl rfl
          | some N =>
            simp only
            cases hp : pick N with
            | none => exact Or.inl rfl
            | some p =>
              simp only
              by_cases e : p.1 = k
              · obtain ⟨-, hy, -⟩ := pickOk N p hp
                rw [e] at hy
                simp only [e, ↓reduceIte]
                exact Or.inr ⟨_, rfl, hy⟩
              · simp [e]
        · exact Or.inl rfl
    · rw [uN k i dk]
      rcases hwm.2 k i with h | ⟨x, e, h | ⟨h, -⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, e, h⟩
      · exact absurd h dk
  refine ⟨u, ⟨tag, l, negs, rfl, ⟨fun s => by rw [uA]; exact hwm.1 s, allowed⟩, fun N mN hN => ?_⟩, fun s => (uA s).symm,
    fun k i h => (uN k i h).symm, fun k i mF dk => ?_⟩
  · obtain ⟨kN, nt, nl, rfl, gN, slN⟩ := lits N mN
    obtain ⟨kN', nt', nl', e', hm⟩ := hN
    obtain ⟨-, rfl, e₃⟩ := tuple3_inj e'
    obtain rfl := fieldsTerm_inj e₃
    by_cases kept : KeptNeg den tag Ds (.tuple #[.integer kN, nt, fieldsTerm nl])
    · -- A kept negation already excludes the line's maps on their non-updated part.
      refine hkn _ mN kept ⟨kN, nt, nl, rfl, fun s => by rw [← uA]; exact hm.atoms s, fun k i => ?_⟩
      obtain ⟨kN'', nt'', nl'', e'', sub⟩ := kept
      obtain ⟨-, rfl, -⟩ := tuple3_inj e''
      by_cases dk : domKind k ∈ Ds
      · rcases hwm.2 k i with h | ⟨x, e, h | ⟨_, h⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, e, Or.inl (sub _ dk x h)⟩
        · exact Or.inr ⟨x, e, Or.inr ⟨dk, h⟩⟩
      · have := hm.doms k i
        rw [uN k i dk, tagSem_iff ef gN] at this
        rcases this with h | ⟨x, e, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, e, Or.inl h⟩
    · -- A dropped negation misses the fresh key holding its escape value.
      obtain ⟨p, hp⟩ := exDrop _ mN kept
      have hpick : ∃ q, pick (.tuple #[.integer kN, nt, fieldsTerm nl]) = some q :=
        ⟨_, by simp only [pick, show ∃ p, Esc (.tuple #[.integer kN, nt, fieldsTerm nl]) p from ⟨p, hp⟩, ↓reduceDIte]; rfl⟩
      obtain ⟨q, hq⟩ := hpick
      obtain ⟨dq, -, nq⟩ := pickOk _ q hq
      obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp mN
      have fresh : MKey.dom q.1 (J + idx) ∉ F := freshIdx_not_mem (by omega)
      have uq : u (.dom q.1 (J + idx)) = some q.2 := by
        simp [u, dq, fresh, hidx, hq]
      have := hm.doms q.1 (J + idx)
      rw [uq, tagSem_iff ef gN] at this
      rcases this with h | ⟨x, e, h⟩
      · cases h
      · cases e; exact nq kN nt nl rfl h
  · rw [uF k i mF dk]
    rcases hwm.2 k i with h | ⟨x, e, h | ⟨_, h⟩⟩
    · exact Or.inl h
    · right; left
      simp only [show isOld k (w (.dom k i)) from ⟨x, e, h⟩, ↓reduceIte]
    · exact Or.inr (Or.inr ⟨x, e, h⟩)


/-- A map agreeing, on every finite set of keys, with some map of a line is a map of the widened line. -/
theorem wline_of_agreeP (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) {Ds : List String} {P : String → V → Prop} {w : MW V}
    (h : ∀ F, ∃ u, InMLine den L u ∧ AgreeP Ds P F w u) : WLineP den L Ds P w := by
  obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hL
  obtain ⟨u₀, hu₀, a₀⟩ := h []
  obtain ⟨m₀, n₀⟩ := inMLine_iff.mp hu₀
  refine ⟨tag, l, negs, rfl, ⟨fun s => by rw [a₀.1 s]; exact m₀.atoms s, fun k i => ?_⟩, fun N mN kept hN => ?_⟩
  · obtain ⟨u, hu, a⟩ := h [.dom k i]
    have t := (inMLine_iff.mp hu).1.doms k i
    rw [tagSem_iff ef g] at t
    by_cases dk : domKind k ∈ Ds
    · rcases a.2.2 k i (List.mem_singleton_self _) dk with e | e | ⟨x, e, hx⟩
      · exact Or.inl e
      · rw [e]
        rcases t with t | ⟨x, t, hx⟩
        · exact Or.inl t
        · exact Or.inr ⟨x, t, Or.inl hx⟩
      · exact Or.inr ⟨x, e, Or.inr ⟨dk, hx⟩⟩
    · rw [a.2.1 k i dk]
      rcases t with t | ⟨x, t, hx⟩
      · exact Or.inl t
      · exact Or.inr ⟨x, t, Or.inl hx⟩
  · -- `u₀` would be a map of the kept negation.
    obtain ⟨kN, nt, nl, rfl, sub⟩ := kept
    obtain ⟨kN', nt', nl', e', hw⟩ := hN
    obtain ⟨-, rfl, e₃⟩ := tuple3_inj e'
    obtain rfl := fieldsTerm_inj e₃
    obtain ⟨kN'', nt'', nl'', e'', gN, -⟩ := lits _ mN
    obtain ⟨-, rfl, -⟩ := tuple3_inj e''
    refine n₀ _ mN ⟨kN, nt, nl, rfl, fun s => by rw [← a₀.1 s]; exact hw.1 s, fun k i => ?_⟩
    rw [tagSem_iff ef gN]
    by_cases dk : domKind k ∈ Ds
    · have t := m₀.doms k i
      rw [tagSem_iff ef g] at t
      rcases t with t | ⟨x, t, hx⟩
      · exact Or.inl t
      · exact Or.inr ⟨x, t, sub _ dk x hx⟩
    · rw [← a₀.2.1 k i dk]
      rcases hw.2 k i with t | ⟨x, t, hx | ⟨hd, _⟩⟩
      · exact Or.inl t
      · exact Or.inr ⟨x, t, hx⟩
      · exact absurd hd dk


/-- A map holds a key of a kind. -/
def HasKind (u : MW V) (d : String) : Prop := ∃ k i, domKind k = d ∧ u (.dom k i) ≠ none

/-- A value of a map of a line at a key of a kind is a value of the line's tag there. -/
theorem inline_tag (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)}
    {negs : List Term} {u : MW V} (hu : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u) {k : Fin 11}
    {i : Nat} {x : V} (e : u (.dom k i) = some x) : den (tagType tag (domKind k)) x := by
  have t := (inMLine_iff.mp hu).1.doms k i
  rw [tagSem_iff ef g, e] at t
  rcases t with t | ⟨y, t, hy⟩
  · cases t
  · cases t; exact hy

theorem inline_hasKind (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)}
    {negs : List Term} {u : MW V} (hu : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u) {d : String}
    (h : HasKind u d) : ∃ y, den (tagType tag d) y := by
  obtain ⟨k, i, rfl, ne⟩ := h
  cases e : u (.dom k i) with
  | none => exact absurd e ne
  | some x => exact ⟨x, inline_tag ef g hu e⟩

/-- A map of a line gives one holding a key of each kind the tag gives a value, agreeing elsewhere and on a finite
set of keys. -/
theorem line_extend (ef : EF nd E V den tl K) {tag : Term} (g : TagV E tag) {l : List (Term × Term)}
    {negs : List Term} {u : MW V} (hu : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u)
    (SK : Fin 11 → Prop) (hS : ∀ k, SK k → ∃ y, den (tagType tag (domKind k)) y) (F : List MKey) :
    ∃ u', InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u' ∧ (∀ s, u' (.atom s) = u (.atom s)) ∧
      (∀ κ ∈ F, u' κ = u κ) ∧ (∀ k i, ¬SK k → u' (.dom k i) = u (.dom k i)) ∧ ∀ k, SK k → ∃ i, u' (.dom k i) ≠ none := by
  classical
  let J := freshIdx F
  let u' : MW V := fun κ => match κ with
    | .atom s => u (.atom s)
    | .dom k i => if h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J then some (hS k h.1).choose else u (.dom k i)
  have uD : ∀ k i, ¬(SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J) → u' (.dom k i) = u (.dom k i) := fun k i h => by
    simp only [u']; rw [dite_eq_right h]
  have uS : ∀ k i (h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J), u' (.dom k i) = some (hS k h.1).choose :=
    fun k i h => by simp only [u']; rw [dite_eq_left h]
  obtain ⟨m, nn⟩ := inMLine_iff.mp hu
  refine ⟨u', inMLine_iff.mpr ⟨⟨fun s => m.atoms s, fun k i => ?_⟩, fun N mN hN => ?_⟩, fun s => rfl,
    fun κ mκ => ?_, fun k i nk => uD k i (fun h => nk h.1), fun k sk => ?_⟩
  · by_cases h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J
    · rw [uS k i h, tagSem_iff ef g]; exact Or.inr ⟨_, rfl, (hS k h.1).choose_spec⟩
    · rw [uD k i h]; exact m.doms k i
  · obtain ⟨kN, tN, lN, rfl, hm⟩ := hN
    refine nn _ mN ⟨kN, tN, lN, rfl, ⟨fun s => hm.atoms s, fun k i => ?_⟩⟩
    by_cases h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ i = J
    · rw [h.2.1 i]; exact tagSem_none _ _
    · rw [← uD k i h]; exact hm.doms k i
  · cases κ with
    | atom s => rfl
    | dom k i => exact uD k i fun h => freshIdx_not_mem (k := k) (Nat.le_of_eq h.2.2.symm) mκ
  · by_cases ex : ∃ i, u (.dom k i) ≠ none
    · obtain ⟨i, hi⟩ := ex
      refine ⟨i, ?_⟩
      rw [uD k i fun h => hi (h.2.1 i)]; exact hi
    · have h : SK k ∧ (∀ i', u (.dom k i') = none) ∧ J = J :=
        ⟨sk, fun i' => Classical.not_not.mp fun hh => ex ⟨i', hh⟩, rfl⟩
      exact ⟨J, by rw [uS k J h]; simp⟩

/-- The maps of a line are maps of the widened line. -/
theorem inline_wline (ef : EF nd E V den tl K) {L : Term} (hL : MLine E L) {Ds : List String}
    {P : String → V → Prop} {u : MW V} (hu : InMLine den L u) : WLineP den L Ds P u :=
  wline_of_agreeP ef hL fun _ => ⟨u, hu, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => Or.inr (Or.inl rfl)⟩

/-- A line whose tag gives no value at the widened kinds, widened by no value, is the line. -/
theorem wline_static (ef : EF nd E V den tl K) {tag : Term} {l : List (Term × Term)} {negs : List Term}
    (hL : MLine E (.tuple #[tag, fieldsTerm l, Term.list negs])) {Ds : List String}
    (hT : ∀ d ∈ Ds, ∀ y, ¬den (tagType tag d) y) {P : String → V → Prop} (hP : ∀ d ∈ Ds, ∀ x, ¬P d x) {w : MW V}
    (hw : WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds P w) :
    InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) w := by
  obtain ⟨tag', l', negs', e, g, sl, lits⟩ := hL
  obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
  obtain rfl := fieldsTerm_inj e₂
  obtain rfl := list_inj e₃
  obtain ⟨tag', l', negs', e, hm, hn⟩ := hw
  obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
  obtain rfl := fieldsTerm_inj e₂
  obtain rfl := list_inj e₃
  refine inMLine_iff.mpr ⟨⟨hm.1, fun k i => ?_⟩, fun N mN hN => ?_⟩
  · rw [tagSem_iff ef g]
    rcases hm.2 k i with h | ⟨x, h, hx | ⟨dk, hx⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, h, hx⟩
    · exact absurd hx (hP _ dk x)
  · obtain ⟨kN, tN, lN, rfl, gN, -⟩ := lits N mN
    obtain ⟨kN', tN', lN', e', hm'⟩ := hN
    obtain ⟨-, rfl, e₃⟩ := tuple3_inj e'
    obtain rfl := fieldsTerm_inj e₃
    refine hn _ mN ⟨kN, tN, lN, rfl, fun d md y hy => absurd hy (hT d md y)⟩
      ⟨kN, tN, lN, rfl, fun s => hm'.atoms s, fun k i => ?_⟩
    have := hm'.doms k i
    rw [tagSem_iff ef gN] at this
    rcases this with h | ⟨x, h, hx⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, h, Or.inl hx⟩

/-- On finitely many lines, a property every finite set of keys meets on some line, antitone in the set, holds for
every finite set on one line. -/
theorem pigeon_lines {lines : List Term} {Q : Term → List MKey → Prop}
    (mono : ∀ L F G, Q L G → (∀ κ ∈ F, κ ∈ G) → Q L F) (h : ∀ F, ∃ L ∈ lines, Q L F) :
    ∃ L ∈ lines, ∀ F, Q L F := by
  classical
  let FL : Term → List MKey := fun L => if hr : ∃ F, ¬Q L F then hr.choose else []
  obtain ⟨L, mL, hq⟩ := h (lines.flatMap FL)
  refine ⟨L, mL, Classical.byContradiction fun nq => ?_⟩
  have hr : ∃ F, ¬Q L F := Classical.not_forall.mp nq
  have hF : FL L = hr.choose := by simp only [FL, hr, ↓reduceDIte]
  exact hr.choose_spec (mono L _ _ hq fun κ m => List.mem_flatMap.mpr ⟨L, mL, hF ▸ m⟩)

/-- The values an update may put at the keys of a kind of a map: the new type, when forcing or when the map holds a
key of the kind. -/
def NewU (den : Term → V → Prop) (nt : Term) (md : String) (u : MW V) (d : String) (x : V) : Prop :=
  den nt x ∧ (md = "force" ∨ HasKind u d)

/-- The maps `map_update_widen/3` gives for a constant update, from the maps of a type: on every finite set of keys,
some map of the type, holding a key of an updated kind when rejecting, agrees as `AgreeP` requires. -/
def WSem (den : Term → V → Prop) (M : MW V → Prop) (nt : Term) (md : String) (Ds : List String) (w : MW V) : Prop :=
  ∀ F, ∃ u, M u ∧ (md = "reject" → ∃ d ∈ Ds, HasKind u d) ∧ AgreeP Ds (NewU den nt md u) F w u

/-- `WSem` without the empty map when keys get values, unless keeping and the type holds it. -/
def WRes (den : Term → V → Prop) (M : MW V → Prop) (nt : Term) (md : String) (Ds : List String) (w : MW V) : Prop :=
  WSem den M nt md Ds w ∧ ((∃ x, den nt x) → (md = "keep" → w = wNone → M wNone) ∧ (md ≠ "keep" → w ≠ wNone))

theorem updNE_iff {nt : Term} {nopt : Bool} (hne : nopt = Bool.true ∨ ∃ x, den nt x) {md : String} (hmd : Mode md)
    {tag : Term} {d : String} : UpdNE den nt nopt md tag d ↔ (md = "reject" → ∃ y, den (tagType tag d) y) := by
  unfold UpdNE
  rcases hmd with rfl | rfl | rfl
  · simp [hne]
  · simp
  · simp [hne]

/-- The widened lines of a type hold the maps `WRes` describes. -/
theorem wlg_sem (ef : EF nd E V den tl K) {lines : List Term} (hl : ∀ L ∈ lines, MLine E L) {nt : Term} (nopt : Bool)
    (hne : nopt = Bool.true ∨ ∃ x, den nt x) {md : String} (hmd : Mode md) {Ds : List String} (hA : "atom" ∉ Ds)
    (hD : ∀ d ∈ Ds, d ∈ domainKinds) (neD : Ds ≠ []) (w : MW V) :
    (∃ L ∈ lines, WLG den nt nopt md Ds L w) ↔ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) nt md Ds w := by
  classical
  constructor
  · rintro ⟨L, mL, tag, l, negs, rfl, Ds', mD, ne', hw, hp⟩
    obtain ⟨tag', l', negs', e, g, sl, lits⟩ := hl _ mL
    obtain ⟨rfl, e₂, e₃⟩ := tuple3_inj e
    obtain rfl := fieldsTerm_inj e₂
    obtain rfl := list_inj e₃
    have hD' : ∀ d ∈ Ds', d ∈ domainKinds := fun d m' => hD d ((mD d).mp m').1
    have hA' : "atom" ∉ Ds' := fun m' => hA ((mD _).mp m').1
    refine ⟨fun F => ?_, fun hnt => ⟨?_, ?_⟩⟩
    · obtain ⟨u, hu, a1, a2, a3⟩ := wline_witnessP ef (hl _ mL) hA' hD' hw F
      obtain ⟨u', hu', b1, bF, bS, bK⟩ := line_extend ef g hu
        (fun k => domKind k ∈ Ds' ∧ ∃ y, den (tagType tag (domKind k)) y) (fun _ h => h.2) F
      refine ⟨u', ⟨_, mL, hu'⟩, fun hr => ?_, fun s => (a1 s).trans (b1 s).symm, fun k i nk => ?_,
        fun k i mF dk => ?_⟩
      · obtain ⟨d, md'⟩ := List.exists_mem_of_ne_nil Ds' ne'
        obtain ⟨dD, up⟩ := (mD d).mp md'
        have tne := (updNE_iff hne hmd).mp up hr
        obtain ⟨k, rfl⟩ := domKind_of (hD _ dD) (fun h => hA (h ▸ dD))
        obtain ⟨i, hi⟩ := bK k ⟨md', tne⟩
        exact ⟨_, dD, k, i, rfl, hi⟩
      · have nk' : domKind k ∉ Ds' := fun m' => nk ((mD _).mp m').1
        rw [a2 k i nk', bS k i (fun h => nk' h.1)]
      · by_cases dk' : domKind k ∈ Ds'
        · rcases a3 k i mF dk' with h | h | ⟨x, h, hx⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl (h.trans (bF _ mF).symm))
          · refine Or.inr (Or.inr ⟨x, h, hx.1, ?_⟩)
            rcases hx.2 with hf | tne
            · exact Or.inl hf
            · obtain ⟨i', hi'⟩ := bK k ⟨dk', tne⟩
              exact Or.inr ⟨k, i', rfl, hi'⟩
        · exact Or.inr (Or.inl ((a2 k i dk').trans (bF _ mF).symm))
    · rintro rfl rfl
      by_cases inL : InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) wNone
      · exact ⟨_, mL, inL⟩
      obtain ⟨x, hx⟩ := hnt
      exact absurd rfl (hp ⟨fun _ => ⟨fun ⟨d, md', ⟨y, hy⟩, hn⟩ => hn ⟨x, hx, Or.inr ⟨y, hy⟩⟩, inL⟩,
        fun hk => absurd rfl hk⟩)
    · intro nk
      obtain ⟨d, md'⟩ := List.exists_mem_of_ne_nil Ds' ne'
      obtain ⟨x, hx⟩ := hnt
      refine hp ⟨fun hk => absurd hk nk, fun _ => ⟨d, md', x, hx, ?_⟩⟩
      rcases hmd with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd rfl nk
      · exact Or.inr ((updNE_iff hne (Or.inr (Or.inr rfl))).mp ((mD d).mp md').2 rfl)
  · rintro ⟨hs, he⟩
    by_cases special : md = "keep" ∧ (∃ x, den nt x) ∧ w = wNone
    · obtain ⟨rfl, hnt, rfl⟩ := special
      obtain ⟨L, mL, hL⟩ := (he hnt).1 rfl rfl
      obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hl L mL
      exact ⟨_, mL, tag, l, negs, rfl, Ds, fun d => ⟨fun m' => ⟨m', Or.inl rfl⟩, fun h => h.1⟩, neD,
        inline_wline ef (hl _ mL) hL, fun p => absurd hL (p.1 rfl).2⟩
    obtain ⟨L, mL, hQ⟩ := pigeon_lines (lines := lines)
      (Q := fun L F => ∃ u, InMLine den L u ∧ (md = "reject" → ∃ d ∈ Ds, HasKind u d) ∧
        AgreeP Ds (NewU den nt md u) F w u)
      (fun L F G ⟨u, hu, hr, a⟩ sub => ⟨u, hu, hr, a.mono sub⟩)
      (fun F => by
        obtain ⟨u, ⟨L, mL, hu⟩, hr, a⟩ := hs F
        exact ⟨L, mL, u, hu, hr, a⟩)
    obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hl L mL
    let Ds' := Ds.filter (fun d => decide (UpdNE den nt nopt md tag d))
    have mD : ∀ d, d ∈ Ds' ↔ d ∈ Ds ∧ UpdNE den nt nopt md tag d := fun d => by simp [Ds']
    have hk : ∀ d, d ∈ Ds → d ∉ Ds' → md = "reject" ∧ ∀ y, ¬den (tagType tag d) y := fun d dD nD => by
      have : ¬UpdNE den nt nopt md tag d := fun h => nD ((mD d).mpr ⟨dD, h⟩)
      rw [updNE_iff hne hmd] at this
      obtain ⟨hr, hy⟩ := Classical.not_imp.mp this
      exact ⟨hr, fun y h => hy ⟨y, h⟩⟩
    have noKey : ∀ k i, domKind k ∈ Ds → domKind k ∉ Ds' → w (.dom k i) = none ∧
        ∀ u, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u → u (.dom k i) = none := by
      intro k i dD nD
      obtain ⟨hr, hy⟩ := hk _ dD nD
      have uN : ∀ u, InMLine den (.tuple #[tag, fieldsTerm l, Term.list negs]) u → u (.dom k i) = none := by
        intro u hu
        cases e : u (.dom k i) with
        | none => rfl
        | some x => exact absurd (inline_tag ef g hu e) (hy x)
      refine ⟨?_, uN⟩
      obtain ⟨u, hu, -, a⟩ := hQ [.dom k i]
      rcases a.2.2 k i (List.mem_singleton_self _) dD with h | h | ⟨x, h, hx⟩
      · exact h
      · exact h.trans (uN u hu)
      · rcases hx.2 with hf | hK
        · rw [hr] at hf; simp at hf
        · obtain ⟨y, hy'⟩ := inline_hasKind ef g hu hK
          exact absurd hy' (hy y)
    have ne' : Ds' ≠ [] := by
      by_cases hr : md = "reject"
      · obtain ⟨u, hu, hk', -⟩ := hQ []
        obtain ⟨d, dD, hK⟩ := hk' hr
        have := inline_hasKind ef g hu hK
        intro e
        have m' := (mD d).mpr ⟨dD, (updNE_iff hne hmd).mpr fun _ => this⟩
        rw [e] at m'; cases m'
      · obtain ⟨d, dD⟩ := List.exists_mem_of_ne_nil Ds neD
        intro e
        have m' := (mD d).mpr ⟨dD, (updNE_iff hne hmd).mpr fun h => absurd h hr⟩
        rw [e] at m'; cases m'
    have hw : WLineP den (.tuple #[tag, fieldsTerm l, Term.list negs]) Ds' (NewP den nt md tag) w :=
      wline_of_agreeP ef (hl _ mL) fun F => by
        obtain ⟨u, hu, -, a⟩ := hQ F
        refine ⟨u, hu, a.1, fun k i nD => ?_, fun k i mF dk => ?_⟩
        · by_cases dD : domKind k ∈ Ds
          · obtain ⟨hw, hu'⟩ := noKey k i dD nD
            rw [hw, hu' u hu]
          · exact a.2.1 k i dD
        · rcases a.2.2 k i mF ((mD _).mp dk).1 with h | h | ⟨x, h, hx⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · refine Or.inr (Or.inr ⟨x, h, hx.1, ?_⟩)
            rcases hx.2 with hf | hK
            · exact Or.inl hf
            · exact Or.inr (inline_hasKind ef g hu hK)
    refine ⟨_, mL, tag, l, negs, rfl, Ds', mD, ne', hw, fun p => ?_⟩
    rintro rfl
    by_cases mk : md = "keep"
    · subst mk
      by_cases hnt : ∃ x, den nt x
      · exact special ⟨rfl, hnt, rfl⟩
      · -- Deleting: no kind gets a value, so every updated kind lacks values and the line is unchanged.
        have tE : ∀ d ∈ Ds', ∀ y, ¬den (tagType tag d) y := fun d md' y hy =>
          (p.1 rfl).1 ⟨d, md', ⟨y, hy⟩, fun ⟨x, hx⟩ => hnt ⟨x, hx.1⟩⟩
        exact (p.1 rfl).2 (wline_static ef (hl _ mL) tE (fun d _ x hx => hnt ⟨x, hx.1⟩) hw)
    · obtain ⟨d, -, x, hx, -⟩ := p.2 mk
      exact (he ⟨x, hx⟩).2 mk rfl

end

end Elixir.STTDescrProofsTest.Nest
