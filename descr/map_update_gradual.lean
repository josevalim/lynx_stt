namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Updates of gradual types: the dynamic part is updated with errors computed as for gradual types, which change
neither the values nor the maps of the update. -/

/-- Accumulators of updates that agree on their value and maps. -/
def Rel4 (a b : Term) : Prop := ∃ v bd e₁ f₁ e₂ f₂, a = .tuple #[v, bd, e₁, f₁] ∧ b = .tuple #[v, bd, e₂, f₂]

/-- One step of `map_update_named_keys/8` gives the same value and maps whether the type is static or not. -/
theorem named_step_rel (d : Dispatcher) (dnf op req bld ov fo key : Term) (s₁ s₂ : Term)
    {v bd e₁ f₁ e₂ f₂ r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req s₁ bld ov fo key
      (.tuple #[v, bd, e₁, f₁]) = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req s₂ bld ov fo key
      (.tuple #[v, bd, e₂, f₂]) = .ok r₂) : Rel4 r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»] at h₁ h₂
  cases hk : Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov with
  | error e => simp [hk] at h₁
  | ok t =>
    simp only [hk, Lynx.Except.ok_bind] at h₁ h₂
    split at h₁
    case h_2 => simp at h₁
    rename_i bds old
    simp only at h₂
    cases hb : Erlang.erlang.«++/2» bds bd with
    | error e => simp [hb] at h₁
    | ok B =>
      simp only [hb, Lynx.Except.ok_bind] at h₁ h₂
      by_cases hn : old = .atom "nil"
      · subst hn
        simp only [pure, Except.pure, Except.ok.injEq] at h₁ h₂
        subst h₁ h₂
        exact ⟨_, _, _, _, _, _, rfl, rfl⟩
      by_cases ht : ∃ value opt, old = .tuple #[value, opt]
      · obtain ⟨value, opt, rfl⟩ := ht
        simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure] at h₁ h₂
        split at h₁
        · simp at h₁
        rename_i b16 h16
        simp only [h16] at h₂
        simp only [Lynx.Except.tryWith] at h₁ h₂
        split at h₁
        · -- The old value has values: the value is updated.
          rename_i hm
          simp only [hm] at h₂
          cases hu : Elixir.Module.Types.Descr.«opt_union/2» d value v with
          | error e => simp [hu] at h₁
          | ok U =>
            simp only [hu] at h₁ h₂
            obtain ⟨e₁', f₁', rfl⟩ : ∃ e f, r₁ = .tuple #[U, B, e, f] := by
              clear h₂
              repeat' split at h₁
              all_goals first
                | (simp at h₁; done)
                | (simp only [Except.ok.injEq] at h₁; subst h₁; exact ⟨_, _, rfl⟩)
            obtain ⟨e₂', f₂', rfl⟩ : ∃ e f, r₂ = .tuple #[U, B, e, f] := by
              clear h₁
              repeat' split at h₂
              all_goals first
                | (simp at h₂; done)
                | (simp only [Except.ok.injEq] at h₂; subst h₂; exact ⟨_, _, rfl⟩)
            exact ⟨_, _, _, _, _, _, rfl, rfl⟩
        · rename_i hx
          cases hm : b16.isMember [Term.atom "false", Term.atom "nil"] with
          | atom a =>
            by_cases ha : a = "true"
            · subst ha; exact (hx hm).elim
            · simp only [hm] at h₂
              obtain ⟨e₁', f₁', rfl⟩ : ∃ e f, r₁ = .tuple #[v, B, e, f] := by
                clear h₂
                repeat' split at h₁
                all_goals first
                  | (simp at h₁; done)
                  | (simp only [Except.ok.injEq] at h₁; subst h₁; exact ⟨_, _, rfl⟩)
              obtain ⟨e₂', f₂', rfl⟩ : ∃ e f, r₂ = .tuple #[v, B, e, f] := by
                clear h₁
                split at h₂
                · simp_all
                repeat' split at h₂
                all_goals first
                  | (simp at h₂; done)
                  | (simp only [Except.ok.injEq] at h₂; subst h₂; exact ⟨_, _, rfl⟩)
              exact ⟨_, _, _, _, _, _, rfl, rfl⟩
          | _ =>
            simp only [hm] at h₂
            obtain ⟨e₁', f₁', rfl⟩ : ∃ e f, r₁ = .tuple #[v, B, e, f] := by
              clear h₂
              repeat' split at h₁
              all_goals first
                | (simp at h₁; done)
                | (simp only [Except.ok.injEq] at h₁; subst h₁; exact ⟨_, _, rfl⟩)
            obtain ⟨e₂', f₂', rfl⟩ : ∃ e f, r₂ = .tuple #[v, B, e, f] := by
              clear h₁
              repeat' split at h₂
              all_goals first
                | (simp at h₂; done)
                | (simp only [Except.ok.injEq] at h₂; subst h₂; exact ⟨_, _, rfl⟩)
            exact ⟨_, _, _, _, _, _, rfl, rfl⟩
      · split at h₁
        · exact absurd rfl hn
        · exact absurd ⟨_, _, rfl⟩ ht
        · simp at h₁

theorem foldl1_rel4 (d : Dispatcher) (f₁ f₂ : Term)
    (hs : ∀ x a b a' b', Rel4 a b → d.pure f₁ #[x, a] = .ok a' → d.pure f₂ #[x, b] = .ok b' → Rel4 a' b') :
    ∀ (l a b : Term) {r₁ r₂ : Term}, Rel4 a b → Erlang.lists.«foldl_1/3» d f₁ a l = .ok r₁ →
      Erlang.lists.«foldl_1/3» d f₂ b l = .ok r₂ → Rel4 r₁ r₂
  | .cons x l, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only at h₁ h₂
    cases e₁ : d.pure f₁ #[x, a] with
    | error e => rw [e₁] at h₁; cases h₁
    | ok a' =>
      cases e₂ : d.pure f₂ #[x, b] with
      | error e => rw [e₂] at h₂; cases h₂
      | ok b' =>
        rw [e₁] at h₁; rw [e₂] at h₂
        exact foldl1_rel4 d f₁ f₂ hs l a' b' (hs x a b a' b' hab e₁ e₂) (by simpa using h₁) (by simpa using h₂)
  | .nil, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only [pure, Except.pure, Except.ok.injEq] at h₁ h₂
    subst h₁ h₂; exact hab
  | .atom _, _, _, _, _, _, h₁, _ | .integer _, _, _, _, _, _, h₁, _ | .float _, _, _, _, _, _, h₁, _
  | .tuple _, _, _, _, _, _, h₁, _ | .map _, _, _, _, _, _, h₁, _ | .bitstring _ _ _, _, _, _, _, _, h₁, _
  | .function _ _ _ _ _, _, _, _, _, _, h₁, _ | .pid _, _, _, _, _, _, h₁, _ | .reference _, _, _, _, _, _, h₁, _ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁; simp at h₁

theorem foldl_rel4 (d : Dispatcher) {mo nm : String} {c₁ c₂ : Array Term}
    (hs : ∀ x a b a' b', Rel4 a b → d.pure (.function false mo nm 2 c₁) #[x, a] = .ok a' →
      d.pure (.function false mo nm 2 c₂) #[x, b] = .ok b' → Rel4 a' b')
    (l a b : Term) {r₁ r₂ : Term} (hab : Rel4 a b)
    (h₁ : Erlang.lists.«foldl/3» d (.function false mo nm 2 c₁) a l = .ok r₁)
    (h₂ : Erlang.lists.«foldl/3» d (.function false mo nm 2 c₂) b l = .ok r₂) : Rel4 r₁ r₂ := by
  have conv : ∀ c acc r, Erlang.lists.«foldl/3» d (.function false mo nm 2 c) acc l = .ok r →
      Erlang.lists.«foldl_1/3» d (.function false mo nm 2 c) acc l = .ok r := by
    intro c acc r h
    simp only [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»] at h
    rw [Erlang.lists.«foldl_1/3».eq_def]
    cases l <;> simp_all
  replace h₁ := conv _ _ _ h₁
  replace h₂ := conv _ _ _ h₂
  exact foldl1_rel4 d _ _ hs l a b hab h₁ h₂

theorem named_keys_rel (m : Nat) (dnf keys op req rt bo s₁ s₂ : Term) {a b r₁ r₂ : Term} (hab : Rel4 a b)
    (h₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) a dnf keys op req s₁ rt bo = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) b dnf keys op req s₂ rt bo = .ok r₂) :
    Rel4 r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», bind, Except.bind, pure, Except.pure] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    refine foldl_rel4 _ (fun x a b a' b' hab e₁ e₂ => ?_) keys a b hab h₁ h₂
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure] at e₁ e₂
    obtain ⟨v, bd, e₁', f₁', e₂', f₂', rfl, rfl⟩ := hab
    exact named_step_rel _ _ _ _ _ _ _ _ _ _ e₁ e₂

/-- `map_update_static_dnf/6` gives the same value and maps whether the type is static or not. -/
theorem dnf_rel (m : Nat) (bdd dnf split op rt s₁ s₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split op rt s₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split op rt s₂ = .ok r₂) :
    Rel4 r₁ r₂ := by
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁
    · simp at h₁
    rename_i v₁ n₁
    split at h₂
    · simp at h₂
    rename_i v₂ n₂
    have r₀ := named_keys_rel _ _ _ _ _ _ _ _ _ ⟨_, _, _, _, _, _, rfl, rfl⟩ n₁ n₂
    split at h₁
    · simp at h₁
    rename_i w₁ n₁'
    split at h₂
    · simp at h₂
    rename_i w₂ n₂'
    obtain ⟨V, BD, e₁, f₁, e₂, f₂, rfl, rfl⟩ := named_keys_rel _ _ _ _ _ _ _ _ _ r₀ n₁' n₂'
    simp only at h₁ h₂
    split at h₁
    · simp at h₁
    rename_i u hu
    simp only [hu] at h₂
    by_cases hbot : u = .atom "bdd_bot"
    · subst hbot
      simp only [Except.ok.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨_, _, _, _, _, _, rfl, rfl⟩
    · split at h₁
      · exact absurd rfl hbot
      split at h₂
      · exact absurd rfl hbot
      simp only [Except.ok.injEq] at h₁ h₂
      subst h₁ h₂
      exact ⟨_, _, _, _, _, _, rfl, rfl⟩

theorem static_rel_ne (m : Nat) (descr split op rt s₁ s₂ : Term) (hd : descr ≠ .atom "term") {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₂ = .ok r₂) :
    r₁ = r₂ ∨ Rel4 r₁ r₂ := by
  rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals first
    | (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂; exact Or.inl rfl)
    | exact Or.inr (dnf_rel _ _ _ _ _ _ _ _ h₁ h₂)
    | exact absurd rfl hd
    | (split at h₁ <;> split at h₂ <;> simp_all)

/-- `map_update_static/5` gives the same value and maps whether the type is static or not. -/
theorem static_rel (m : Nat) (descr split op rt s₁ s₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split op rt s₂ = .ok r₂) :
    r₁ = r₂ ∨ Rel4 r₁ r₂ := by
  by_cases h : descr = .atom "term"
  · subst h
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
    simp only at h₁ h₂
    exact static_rel_ne m _ split op rt s₁ s₂ (by simp) h₁ h₂
  · exact static_rel_ne m descr split op rt s₁ s₂ h h₁ h₂

/-- The gradual branch of `map_update_unchecked/4`: the update of the static part united with the dynamic update of the
dynamic part. -/
theorem grad_upd_inv {X : List (Term × Term)} {Dy : Term} (hD : mapLookup X (.atom "dynamic") = some Dy)
    {split op rt : Term} {m : Nat} {T R er : Term}
    (hdyn : ∀ Td Yd ed fd, Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) Dy split op rt (.atom "false") =
      .ok (.tuple #[Td, Yd, ed, fd]) → ∃ Y', Yd = .map Y' ∧ mapLookup Y' (.atom "dynamic") = none)
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (m + 1)) (.map X) split op rt =
      .ok (.tuple #[T, R, er])) :
    ∃ Yd res sd, (∃ Td ed fd, Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) Dy split op rt (.atom "false") =
        .ok (.tuple #[Td, .map Yd, ed, fd])) ∧ mapLookup Yd (.atom "dynamic") = none ∧
      Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map (rmDyn X)) split op rt (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ sd = .map []) ∨ ∃ a e f, res = .tuple #[a, sd, e, f]) ∧
      Elixir.Module.Types.Descr.«opt_union/2» (D (m + 1)) sd (.map [(.atom "dynamic", .map Yd)]) = .ok R := by
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def] at run
  simp only [Erlang.maps.«take/2», hD] at run
  simp only [filter_dyn, bind, Except.bind, pure, Except.pure] at run
  have fun1 : ∀ x, (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-1-" 1 #[]) #[x] ≠
      .ok (.tuple #[T, R, er]) := fun x => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-1-/1».pure]
    unfold Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»
    split <;> simp
  split at run
  · simp at run
  split at run
  rotate_left
  · exact absurd run (fun1 _)
  cases hd₀ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) Dy split op rt (.atom "false") with
  | error e => rw [hd₀] at run; simp at run
  | ok r =>
    rw [hd₀] at run
    obtain ⟨Td, Yd₀, ed, fd, rfl⟩ : ∃ Td Yd ed fd, r = .tuple #[Td, Yd, ed, fd] := by
      by_cases h4 : ∃ Td Yd ed fd, r = .tuple #[Td, Yd, ed, fd]
      · exact h4
      · exfalso
        simp only at run
        split at run
        · exact h4 ⟨_, _, _, _, rfl⟩
        · exact fun1 _ run
    obtain ⟨Yd, rfl, sYd⟩ := hdyn Td Yd₀ ed fd hd₀
    generalize fd.isMember [Term.atom "false", Term.atom "nil"] = fm at run
    simp only at run
    cases hs₀ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map (rmDyn X)) split op rt (.atom "true") with
    | error e => rw [hs₀] at run; simp at run
    | ok res =>
      rw [hs₀] at run
      have gk : getMapKeys [Term.atom "dynamic"] (.map Yd) = [] := by simp [getMapKeys_single, sYd]
      obtain ⟨sd, hsd⟩ : ∃ sd, (res = .atom "badmap" ∧ sd = .map []) ∨ ∃ a e f, res = .tuple #[a, sd, e, f] := by
        by_cases hb : res = .atom "badmap"
        · exact ⟨_, Or.inl ⟨hb, rfl⟩⟩
        · by_cases h4 : ∃ a sd e f, res = .tuple #[a, sd, e, f]
          · obtain ⟨a, sd, e, f, rfl⟩ := h4
            exact ⟨sd, Or.inr ⟨a, e, f, rfl⟩⟩
          · exfalso
            simp only at run
            repeat' split at run
            all_goals simp_all
      refine ⟨Yd, res, sd, ⟨Td, ed, fd, rfl⟩, sYd, rfl, hsd, ?_⟩
      cases hR : Elixir.Module.Types.Descr.«opt_union/2» (D (m + 1)) sd (.map [(.atom "dynamic", .map Yd)]) with
      | error err =>
        exfalso
        rcases hsd with ⟨rfl, rfl⟩ | ⟨a, e, f, rfl⟩ <;> simp only [gk, hR] at run <;> (repeat' split at run) <;>
          first
          | (simp at run; done)
          | (simp_all; done)
          | (simp only [Lynx.Except.guard, Lynx.Except.tryWith] at run; split at run <;> first | (cases run; done) | simp_all)
      | ok R' =>
        rcases hsd with ⟨rfl, rfl⟩ | ⟨a, e, f, rfl⟩ <;> simp only [gk, hR] at run <;> (repeat' split at run) <;>
          first
          | (simp only at run
             exact congrArg Except.ok run.2.1.symm)
          | (simp at run; done)
          | (simp only [Lynx.Except.guard, Lynx.Except.tryWith] at run; split at run <;> first | (cases run; done) | simp_all)

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The operations of `map_update/5` with a static value, or deleting. -/
def OpK (E : Term → Prop) (den : Term → V → Prop) (op : Term) : Prop :=
  (∃ v, E v ∧ (v = .atom "term" ∨ ∃ Z, v = .map Z) ∧
    (op = forceOp v ∨ ((∃ x, den v x) ∧ ∃ keep, op = keepOp v keep))) ∨
  ∃ md, Mode md ∧ op = cOp (.map []) Bool.true md

/-- Results of `map_update_static/5` with maps of a single field. -/
def UpdRes (E : Term → Prop) (r : Term) : Prop :=
  r = .atom "badmap" ∨ ∃ T Y e f, r = .tuple #[T, Y, e, f] ∧ (Y = .map [] ∨ ∃ r', Y = .map [(.atom "map", r')] ∧ MField E r')

/-- `map_update_static/5` on a map field, for either flag, gives no map or maps of one field. -/
theorem field_wf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b)
    {op : Term} (hop : OpK E den op) (st : Term) {r : Term}
    (h : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") st = .ok r) : UpdRes E r := by
  -- The update as a static type.
  obtain ⟨r', h', s'⟩ : ∃ r', Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") (.atom "true") = .ok r' ∧ UpdRes E r' := by
    rcases hop with ⟨v, hv, sv, rfl | ⟨vne, keep, rfl⟩⟩ | ⟨md, hmd, rfl⟩
    · obtain ⟨res, run, hres⟩ := dput_update_static ef hn hv sv ok (fun N e => by rw [nr N e]; rfl) hNa hb fb
      obtain ⟨res', run', ⟨rfl, bad⟩ | ⟨Y, f, rfl, T, er, run₂, -⟩⟩ := upd_old_static ef hn hv sv ok nr hNa hb fb
      · exact ⟨_, bad, Or.inl rfl⟩
      · rw [run] at run'; cases run'
        refine ⟨_, run₂, Or.inr ⟨T, Y, er, f, rfl, ?_⟩⟩
        rcases hres with ⟨e, -⟩ | ⟨Y', f', e, -, -, hY⟩
        · cases e
        · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e
          obtain ⟨-, rfl, -, rfl, -⟩ := e
          rcases hY with ⟨rfl, -⟩ | ⟨r', rfl, fr, -⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨r', rfl, fr⟩
    · obtain ⟨res, run, ⟨rfl, -⟩ | ⟨T, Y, er, f, rfl, -, Dm, -, hY⟩⟩ :=
        kr_update_static ef hn hv sv vne keep ok nr hNa hb fb
      · exact ⟨_, run, Or.inl rfl⟩
      · refine ⟨_, run, Or.inr ⟨T, Y, er, f, rfl, ?_⟩⟩
        rcases hY with ⟨rfl, -⟩ | ⟨r', rfl, fr, -⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r', rfl, fr⟩
    · obtain ⟨res, run, ⟨rfl, -⟩ | ⟨T, Y, er, f, rfl, -, Dm, -, hY⟩⟩ := del_update_static ef hn hmd ok nr hNa hb fb
      · exact ⟨_, run, Or.inl rfl⟩
      · refine ⟨_, run, Or.inr ⟨T, Y, er, f, rfl, ?_⟩⟩
        rcases hY with ⟨rfl, -⟩ | ⟨r', rfl, fr, -⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨r', rfl, fr⟩
  rcases static_rel (n + 5) _ _ _ _ _ _ h h' with rfl | ⟨v, bd, e₁, f₁, e₂, f₂, rfl, rfl⟩
  · exact s'
  · rcases s' with e | ⟨T, Y, e, f, e', hY⟩
    · cases e
    · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e'
      obtain ⟨rfl, rfl, -⟩ := e'
      exact Or.inr ⟨_, _, _, _, rfl, hY⟩

end

section
variable {t : Term} {n : Nat}

/-- `map_update_static/5` on a static type of the next level, for either flag, gives no map or maps of one field. -/
theorem type_wf {Dy : Term} (hDy : DE (level t n).E Dy) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {op : Term} (hop : OpK (level t n).E (level t n).den op) {m : Nat} (hm : (level t n).K + 10 ≤ m) (st : Term)
    {r : Term} (h : Elixir.Module.Types.Descr.«map_update_static/5» (D m) Dy
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") st = .ok r) :
    UpdRes (level t n).E r := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have ef := (level t n).ef
  rcases hDy with rfl | ⟨DX, rfl, sX⟩
  · rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h
    have gk : getMapKeys [Term.atom "map"] (.atom "term") = [] := by simp [getMapKeys]
    simp only [gk] at h
    exact field_wf ef (n := k) (by omega) ok nr hNa (X := [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])])
      (by simp [mapLookup]) (Or.inl ⟨61102469, rfl⟩) hop st h
  · cases hb : mapLookup DX (.atom "map") with
    | some b => exact field_wf ef (n := k) (by omega) ok nr hNa hb (fieldC_map (sX.fields "map" b hb)) hop st h
    | none =>
      rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h
      simp [getMapKeys_single, hb] at h
      subst h
      exact Or.inr ⟨_, _, _, _, rfl, Or.inl rfl⟩

end

/-- The static branch of `map_update_unchecked/4`. -/
theorem static_upd_inv {S : List (Term × Term)} (hS : mapLookup S (.atom "dynamic") = none)
    {split op rt : Term} {m : Nat} {T Y er : Term}
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (m + 1)) (.map S) split op rt =
      .ok (.tuple #[T, Y, er])) :
    ∃ f, Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map S) split op rt (.atom "true") =
      .ok (.tuple #[T, Y, er, f]) := by
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def] at run
  simp only [Erlang.maps.«take/2», hS] at run
  simp only [bind, Except.bind, pure, Except.pure] at run
  have fun0 : ∀ x, (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[x] ≠
      .ok (.tuple #[T, Y, er]) := fun x => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure]
    unfold Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»
    split <;> simp
  split at run
  · simp at run
  split at run
  rotate_left
  · exact absurd run (fun0 _)
  cases hs : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map S) split op rt (.atom "true") with
  | error e => rw [hs] at run; simp at run
  | ok r =>
    rw [hs] at run
    simp only at run
    split at run
    · rename_i T' Y' er' f'
      simp only [Lynx.Except.guard, Lynx.Except.tryWith] at run
      split at run
      · simp at run
      · simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at run
        obtain ⟨rfl, rfl, rfl, -⟩ := run
        exact ⟨f', rfl⟩
    · exact absurd run (fun0 _)

section
variable {t : Term} {n : Nat}

theorem updRes_de {r : Term} (h : UpdRes (level t n).E r) (nb : r ≠ .atom "badmap") :
    ∃ T Y e f, r = .tuple #[T, .map Y, e, f] ∧ DE (level t n).E (.map Y) ∧ mapLookup Y (.atom "dynamic") = none := by
  rcases h with rfl | ⟨T, Y, e, f, rfl, rfl | ⟨r', rfl, fr⟩⟩
  · exact absurd rfl nb
  · exact ⟨T, [], e, f, rfl, Or.inr ⟨_, rfl, descrC_nil⟩, by simp [mapLookup]⟩
  · exact ⟨T, _, e, f, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, by simp [mapLookup]⟩

/-- Updating a gradual type with a static value at static keys gives, as lower bound, the update of its lower bound. -/
theorem lower_core {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {op : Term} (hop : OpK (level t n).E (level t n).den op) {m : Nat} (hm : (level t n).K + 30 ≤ m)
    {T R er T' Y er' : Term}
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") = .ok (.tuple #[T, R, er]))
    (runL : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map (rmDyn X))
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") = .ok (.tuple #[T', Y, er'])) :
    ∃ R₀, Elixir.Module.Types.Descr.«lower_bound/1» (D m) R = .ok R₀ ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) R₀ Y = .ok (.atom "true") := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have sS : mapLookup (rmDyn X) (.atom "dynamic") = none := by simp [lookup_rmDyn]
  have dS : DE (level t n).E (.map (rmDyn X)) := gX.low_tc
  -- The update of the lower bound.
  obtain ⟨fL, hL⟩ := static_upd_inv sS runL
  obtain ⟨T₀, YY, e₀, f₀, eL, dY, -⟩ := updRes_de (type_wf dS ok nr hNa hop (by omega) _ hL) (by simp)
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eL
  obtain ⟨-, rfl, -⟩ := eL
  have ef := ef_next t n
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    rw [rmDyn_static hD] at runL
    rw [runL] at run
    simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at run
    obtain ⟨-, rfl, -⟩ := run
    refine ⟨.map (rmDyn YY), lower_bound_run (Or.inr ⟨_, rfl⟩), ?_⟩
    have dY' : DE (level t n).E (.map (rmDyn YY)) := (GC.tc dY).low_tc
    exact elem_equal ef dY' dY (fun q => denD_rmDyn YY q) (by omega)
  | some Dy =>
    obtain ⟨dDy, -⟩ : DE (level t n).E Dy ∧ True := by
      rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, -, -⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
      · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, trivial⟩
    have hdyn : ∀ Td Yd ed fd, Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 1)) Dy
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) op (.atom "true") (.atom "false") =
          .ok (.tuple #[Td, Yd, ed, fd]) → ∃ Y', Yd = .map Y' ∧ mapLookup Y' (.atom "dynamic") = none := by
      intro Td Yd ed fd h
      obtain ⟨_, Y', _, _, e, -, sYd⟩ := updRes_de (type_wf dDy ok nr hNa hop (by omega) _ h) (by simp)
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e
      exact ⟨Y', e.2.1, sYd⟩
    obtain ⟨Yd, res, sd, ⟨Td, ed, fd, hdy⟩, -, hres, hsd, hR⟩ := grad_upd_inv hD hdyn run
    rw [hL] at hres
    cases hres
    rcases hsd with ⟨e, -⟩ | ⟨a, e, f, e'⟩
    · cases e
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e'
    obtain ⟨-, rfl, -⟩ := e'
    obtain ⟨T₁, Yd', e₁, f₁, eD, dYd, -⟩ := updRes_de (type_wf dDy ok nr hNa hop (by omega) _ hdy) (by simp)
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eD
    obtain ⟨-, eYd, -⟩ := eD
    cases eYd
    -- The union of the static update and the dynamic one.
    have gA : GC (level t n) (.map [(.atom "dynamic", .map Yd)]) := by
      refine Or.inr ⟨_, .map Yd, rfl, by simp [mapLookup], dYd, ?_, fun v hv => ?_⟩
      · rw [show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]]; exact descrC_nil
      · rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]] at hv
        simp [denD_map, mapLookup, dn_none] at hv
    have noA : ∀ v : PN t n, ¬denD (.map [(.atom "dynamic", .map Yd)]) v := fun v hv => by
      rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]] at hv
      simp [denD_map, mapLookup, dn_none] at hv
    obtain ⟨c, gc, rc, sc, -⟩ := gc_opt_union (GC.tc dY) gA [] (m := k + 1) (by omega)
    rw [show Elixir.Module.Types.Descr.«opt_union/2» (D (k + 1)) (.map YY) (.map [(.atom "dynamic", .map Yd)]) =
      Elixir.Module.Types.Descr.«opt_union/3» (D (k + 1)) (.map YY) (.map [(.atom "dynamic", .map Yd)]) (.map []) from rfl,
      rc] at hR
    cases hR
    refine ⟨lower R, lower_bound_run gc.shape, ?_⟩
    exact elem_equal ef gc.low_tc dY (fun q => (denD_lower R q).trans ((sc q).trans (or_iff_left (noA q)))) (by omega)

end


/-- `map_update/5` with a static value updates with the value at the split of the keys. -/
theorem upd5_val {m : Nat} (X : Term) {key v mode s : Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s)
    (hmode : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject")
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«map_update/5» (D m) X key v mode (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) X s
        (.tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]], mode]) (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rcases sv with rfl | ⟨Z, rfl, sZ⟩
  · rcases hmode with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2»,
      hk, Lynx.Term.getMapKeys]
  · rcases hmode with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2»,
      hk, getMapKeys_single, sZ]

/-- `map_update/5` deleting updates with no value at the split of the keys. -/
theorem upd5_del {m : Nat} (X : Term) {key s : Term} {md : String}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hmd : Mode md) :
    Elixir.Module.Types.Descr.«map_update/5» (D m) X key (.atom "delete") (.atom md) (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) X s (cOp (.map []) Bool.true md) (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«map_update/5»
  rcases hmd with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk] <;> rfl


/-! Splits of gradual keys: required and optional keys and domains update with the same maps as when all are
required, in the order `map_update_static_dnf/6` reads them. -/

/-- Accumulators of updates that agree on their maps. -/
def RelB (a b : Term) : Prop := ∃ v₁ bd e₁ f₁ v₂ e₂ f₂, a = .tuple #[v₁, bd, e₁, f₁] ∧ b = .tuple #[v₂, bd, e₂, f₂]

theorem relB_mk (v₁ bd e₁ f₁ v₂ e₂ f₂ : Term) : RelB (.tuple #[v₁, bd, e₁, f₁]) (.tuple #[v₂, bd, e₂, f₂]) :=
  ⟨_, _, _, _, _, _, _, rfl, rfl⟩

/-- A step of `map_update_named_keys/8` gives the maps of the key prepended to the accumulated ones. -/
theorem named_step_maps (d : Dispatcher) (dnf op req st bld ov fo key : Term) {v bd e f r : Term}
    (h : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req st bld ov fo key
      (.tuple #[v, bd, e, f]) = .ok r) :
    ∃ bds old B, Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov = .ok (.tuple #[bds, old]) ∧
      Erlang.erlang.«++/2» bds bd = .ok B ∧ ∃ a e' f', r = .tuple #[a, B, e', f'] := by
  simp only [Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»] at h
  cases hk : Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov with
  | error e => simp [hk] at h
  | ok t =>
    simp only [hk, Lynx.Except.ok_bind] at h
    split at h
    · rename_i bds old
      cases hb : Erlang.erlang.«++/2» bds bd with
      | error e => simp [hb] at h
      | ok B =>
        refine ⟨bds, old, B, rfl, hb, ?_⟩
        simp only [hb, Lynx.Except.ok_bind] at h
        simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure,
          Lynx.Except.tryWith] at h
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [Except.ok.injEq] at h; subst h; exact ⟨_, _, _, rfl⟩)
    · simp at h

theorem named_step_relB (d : Dispatcher) (dnf op req₁ req₂ s₁ s₂ bld ov fo key : Term) {a b r₁ r₂ : Term}
    (hab : RelB a b)
    (h₁ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req₁ s₁ bld ov fo key a = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req₂ s₂ bld ov fo key b = .ok r₂) :
    RelB r₁ r₂ := by
  obtain ⟨v₁, bd, e₁, f₁, v₂, e₂, f₂, rfl, rfl⟩ := hab
  obtain ⟨bds, old, B, k₁, b₁, a, e, f, rfl⟩ := named_step_maps d dnf op req₁ s₁ bld ov fo key h₁
  obtain ⟨bds', old', B', k₂, b₂, a', e', f', rfl⟩ := named_step_maps d dnf op req₂ s₂ bld ov fo key h₂
  rw [k₁] at k₂
  simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at k₂
  obtain ⟨rfl, rfl⟩ := k₂
  rw [b₁] at b₂; cases b₂
  exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩

theorem foldl1_relP (P : Term → Term → Prop) (d : Dispatcher) (f₁ f₂ : Term)
    (hs : ∀ x a b a' b', P a b → d.pure f₁ #[x, a] = .ok a' → d.pure f₂ #[x, b] = .ok b' → P a' b') :
    ∀ (l a b : Term) {r₁ r₂ : Term}, P a b → Erlang.lists.«foldl_1/3» d f₁ a l = .ok r₁ →
      Erlang.lists.«foldl_1/3» d f₂ b l = .ok r₂ → P r₁ r₂
  | .cons x l, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only at h₁ h₂
    cases e₁ : d.pure f₁ #[x, a] with
    | error e => rw [e₁] at h₁; cases h₁
    | ok a' =>
      cases e₂ : d.pure f₂ #[x, b] with
      | error e => rw [e₂] at h₂; cases h₂
      | ok b' =>
        rw [e₁] at h₁; rw [e₂] at h₂
        exact foldl1_relP P d f₁ f₂ hs l a' b' (hs x a b a' b' hab e₁ e₂) (by simpa using h₁) (by simpa using h₂)
  | .nil, a, b, r₁, r₂, hab, h₁, h₂ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁ h₂
    simp only [pure, Except.pure, Except.ok.injEq] at h₁ h₂
    subst h₁ h₂; exact hab
  | .atom _, _, _, _, _, _, h₁, _ | .integer _, _, _, _, _, _, h₁, _ | .float _, _, _, _, _, _, h₁, _
  | .tuple _, _, _, _, _, _, h₁, _ | .map _, _, _, _, _, _, h₁, _ | .bitstring _ _ _, _, _, _, _, _, h₁, _
  | .function _ _ _ _ _, _, _, _, _, _, h₁, _ | .pid _, _, _, _, _, _, h₁, _ | .reference _, _, _, _, _, _, h₁, _ => by
    rw [Erlang.lists.«foldl_1/3».eq_def] at h₁; simp at h₁

theorem foldl_relP (P : Term → Term → Prop) (d : Dispatcher) {mo nm : String} {c₁ c₂ : Array Term}
    (hs : ∀ x a b a' b', P a b → d.pure (.function false mo nm 2 c₁) #[x, a] = .ok a' →
      d.pure (.function false mo nm 2 c₂) #[x, b] = .ok b' → P a' b')
    (l a b : Term) {r₁ r₂ : Term} (hab : P a b)
    (h₁ : Erlang.lists.«foldl/3» d (.function false mo nm 2 c₁) a l = .ok r₁)
    (h₂ : Erlang.lists.«foldl/3» d (.function false mo nm 2 c₂) b l = .ok r₂) : P r₁ r₂ := by
  have conv : ∀ c acc r, Erlang.lists.«foldl/3» d (.function false mo nm 2 c) acc l = .ok r →
      Erlang.lists.«foldl_1/3» d (.function false mo nm 2 c) acc l = .ok r := by
    intro c acc r h
    simp only [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»] at h
    rw [Erlang.lists.«foldl_1/3».eq_def]
    cases l <;> simp_all
  exact foldl1_relP P d _ _ hs l a b hab (conv _ _ _ h₁) (conv _ _ _ h₂)

/-- `map_update_named_keys/8` gives the same maps whatever the keys' requirement and the static flag. -/
theorem named_keys_relB (m : Nat) (dnf keys op rt bo req₁ req₂ s₁ s₂ : Term) {a b r₁ r₂ : Term} (hab : RelB a b)
    (h₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) a dnf keys op req₁ s₁ rt bo = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) b dnf keys op req₂ s₂ rt bo = .ok r₂) :
    RelB r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», bind, Except.bind, pure, Except.pure] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    refine foldl_relP RelB _ (fun x a b a' b' hab e₁ e₂ => ?_) keys a b hab h₁ h₂
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure] at e₁ e₂
    exact named_step_relB _ _ _ _ _ _ _ _ _ _ _ hab e₁ e₂

/-- `map_update_named_keys/8` over appended keys updates the first keys and then the others. -/
theorem named_keys_append (m : Nat) (acc dnf op req st rt bo : Term) (A B : List Term) :
    Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf (Term.list (A ++ B)) op req st rt bo =
      (Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf (Term.list A) op req st rt bo >>=
        fun r => Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) r dnf (Term.list B) op req st rt bo) := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8»]
  cases h₁ : Erlang.erlang.«element/2» (.integer 2) op with
  | error e => simp
  | ok o =>
    cases h₂ : Erlang.erlang.«==/2» o (.atom "force") with
    | error e => simp [h₂]
    | ok fo =>
      cases h₃ : Lynx.Except.orElse (Except.ok rt) (Erlang.erlang.«not/1» fo) true with
      | error e => simp [h₂, h₃]
      | ok ov =>
        simp only [h₂, h₃, Lynx.Except.ok_bind, pure, Except.pure, foldl_fun]
        rw [foldl1_list_append]

/-- Accumulators of `map_update_get_domains/5`: the fold from a fresh accumulator, and from one with flags and lists,
over the same keys; their accumulated values may differ. -/
def GShift (f : Term) (v mi : List Term) (x y : Term) : Prop :=
  ∃ g V Mi a b, y = .tuple #[g, Term.list V, Term.list Mi, b] ∧
    ((g = .atom "true" ∧ x = .tuple #[.atom "true", Term.list (V ++ v), Term.list (Mi ++ mi), a]) ∨
     (g = .atom "false" ∧ x = .tuple #[f, Term.list (V ++ v), Term.list (Mi ++ mi), a])) ∧ (V ≠ [] → g = .atom "true")

theorem gd_step_shift (d : Dispatcher) (dnf rt cb₁ cb₂ key : Term) (hcb : d.pure cb₁ #[] = d.pure cb₂ #[])
    {f : Term} {v mi : List Term} {x y x' y' : Term} (hxy : GShift f v mi x y)
    (h₁ : Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5» d dnf rt cb₁ key x = .ok x')
    (h₂ : Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5» d dnf rt cb₂ key y = .ok y') :
    GShift f v mi x' y' := by
  obtain ⟨g, V, Mi, a, b, rfl, hx, hV⟩ := hxy
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5»] at h₁ h₂
    simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, pure, Except.pure,
      Lynx.Except.tryWith] at h₁ h₂
    generalize hc₁ : d.pure cb₁ #[] = c at h₁
    generalize hc₂ : d.pure cb₂ #[] = c₂ at h₂
    obtain rfl : c = c₂ := hc₁ ▸ hc₂ ▸ hcb
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
    all_goals (repeat' split at h₁) <;> (try (cases h₁; done))
    all_goals (repeat' split at h₂) <;> (try (simp at h₂; done))
    all_goals (try (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂))
  all_goals first
    | exact ⟨.atom "true", .atom "atom" :: V, Mi, _, _, rfl, Or.inl ⟨rfl, rfl⟩,
        fun _ => rfl⟩
    | exact ⟨.atom "true", key :: V, Mi, _, _, rfl, Or.inl ⟨rfl, rfl⟩, fun _ => rfl⟩
    | exact ⟨.atom "true", V, .atom "atom" :: Mi, _, _, rfl, Or.inl ⟨rfl, rfl⟩,
        fun _ => rfl⟩
    | exact ⟨.atom "false", V, .atom "atom" :: Mi, _, _, rfl, Or.inr ⟨rfl, rfl⟩, hV⟩
    | exact ⟨.atom "true", V, key :: Mi, _, _, rfl, Or.inl ⟨rfl, rfl⟩, hV⟩
    | exact ⟨.atom "false", V, key :: Mi, _, _, rfl, Or.inr ⟨rfl, rfl⟩, hV⟩
    | trace_state

theorem gd_fold_shift (m : Nat) (dnf rt cb₁ cb₂ : Term) (hcb : (D m).pure cb₁ #[] = (D m).pure cb₂ #[])
    {f : Term} {v mi : List Term} (l : Term) {x y x' y' : Term} (hxy : GShift f v mi x y)
    (h₁ : Erlang.lists.«foldl/3» (D (m + 1))
      (.function false "Elixir.Module.Types.Descr" "-map_update_get_domains/5-fun-0-" 2 #[dnf, rt, cb₁]) x l = .ok x')
    (h₂ : Erlang.lists.«foldl/3» (D (m + 1))
      (.function false "Elixir.Module.Types.Descr" "-map_update_get_domains/5-fun-0-" 2 #[dnf, rt, cb₂]) y l = .ok y') :
    GShift f v mi x' y' := by
  refine foldl_relP (GShift f v mi) _ (fun k a b a' b' hab e₁ e₂ => ?_) l x y hxy h₁ h₂
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure] at e₁ e₂
  exact gd_step_shift _ _ _ _ _ _ hcb hab e₁ e₂

/-- Fresh accumulators of `map_update_get_domains/5`, related to themselves. -/
theorem gshift_fresh (a b : Term) :
    GShift (.atom "false") [] [] (.tuple #[.atom "false", .nil, .nil, a]) (.tuple #[.atom "false", .nil, .nil, b]) :=
  ⟨_, [], [], a, b, rfl, Or.inr ⟨rfl, rfl⟩, fun h => absurd rfl h⟩

/-- A fold from a fresh accumulator and one from flags and lists. -/
theorem gshift_start (f : Term) (v mi : List Term) (a b : Term) :
    GShift f v mi (.tuple #[f, Term.list v, Term.list mi, a]) (.tuple #[.atom "false", .nil, .nil, b]) :=
  ⟨_, [], [], a, b, rfl, Or.inr ⟨rfl, rfl⟩, fun h => absurd rfl h⟩

/-- `map_update_get_domains/5` gives a boolean flag, set when some domain is valid, and lists of domains. -/
theorem gd_bool (m : Nat) (dnf ks acc rt cb : Term) {r : Term}
    (h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf ks acc rt cb = .ok r) :
    ∃ g V Mi a, r = .tuple #[g, Term.list V, Term.list Mi, a] ∧ (g = .atom "true" ∨ g = .atom "false") ∧
      (V ≠ [] → g = .atom "true") := by
  simp only [Elixir.Module.Types.Descr.«map_update_get_domains/5», pure, Except.pure, Lynx.Except.ok_bind] at h
  obtain ⟨g, V, Mi, a, b, rfl, hx, hV⟩ := gd_fold_shift m dnf rt cb cb rfl ks (gshift_fresh acc acc) h h
  refine ⟨g, V, Mi, b, rfl, ?_, hV⟩
  rcases hx with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem gd_step_congr (d : Dispatcher) (dnf rt cb₁ cb₂ key x : Term) (hcb : d.pure cb₁ #[] = d.pure cb₂ #[]) :
    Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5» d dnf rt cb₁ key x =
      Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5» d dnf rt cb₂ key x := by
  simp only [Elixir.Module.Types.Descr.«-map_update_get_domains/5-fun-0-/5»]
  generalize hc₁ : d.pure cb₁ #[] = c₁
  generalize hc₂ : d.pure cb₂ #[] = c₂
  rw [hc₁, hc₂] at hcb
  subst hcb
  rfl

/-- `map_update_get_domains/5` over appended domains: the second domains fold on from the first. -/
theorem gd_append_rel (m : Nat) (dnf acc rt cb₁ cb₂ : Term) (hcb : (D m).pure cb₁ #[] = (D m).pure cb₂ #[])
    (A B : List Term) {g a R Y : Term} {V Mi : List Term}
    (hR : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list (A ++ B)) acc rt cb₂ = .ok R)
    (hA : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list A) acc rt cb₁ =
      .ok (.tuple #[g, Term.list V, Term.list Mi, a]))
    (hB : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list B) a rt cb₁ = .ok Y) :
    GShift g V Mi R Y := by
  simp only [Elixir.Module.Types.Descr.«map_update_get_domains/5», pure, Except.pure, Lynx.Except.ok_bind,
    foldl_fun] at hR hA hB
  rw [foldl1_list_append] at hR
  have congr : ∀ (l : Term) (x : Term), Erlang.lists.«foldl_1/3» (D (m + 1))
      (.function false "Elixir.Module.Types.Descr" "-map_update_get_domains/5-fun-0-" 2 #[dnf, rt, cb₂]) x l =
      Erlang.lists.«foldl_1/3» (D (m + 1))
        (.function false "Elixir.Module.Types.Descr" "-map_update_get_domains/5-fun-0-" 2 #[dnf, rt, cb₁]) x l :=
    foldl1_congr _ _ _ fun k x => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure,
        Erlang.program.«Elixir.Module.Types.Descr:-map_update_get_domains/5-fun-0-/2».pure]
      exact (gd_step_congr _ _ _ _ _ _ _ hcb).symm
  rw [congr, hA, Lynx.Except.ok_bind] at hR
  rw [← foldl_fun] at hR hB
  exact gd_fold_shift m dnf rt cb₂ cb₁ hcb.symm (Term.list B) (gshift_start g V Mi a a) hR hB

/-- `map_update_get_domains/5` finds the same domains whatever value it starts from. -/
theorem gd_acc (m : Nat) (dnf ks rt cb a b : Term) {g x Y : Term} {V Mi : List Term}
    (hA : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf ks a rt cb =
      .ok (.tuple #[g, Term.list V, Term.list Mi, x]))
    (hB : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf ks b rt cb = .ok Y) :
    ∃ y, Y = .tuple #[g, Term.list V, Term.list Mi, y] := by
  simp only [Elixir.Module.Types.Descr.«map_update_get_domains/5», pure, Except.pure, Lynx.Except.ok_bind] at hA hB
  obtain ⟨g', V', Mi', a', b', rfl, hx, -⟩ := gd_fold_shift m dnf rt cb cb rfl ks (gshift_fresh a b) hA hB
  rcases hx with ⟨rfl, e⟩ | ⟨rfl, e⟩ <;>
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, List.append_nil, and_true] at e <;>
    obtain ⟨rfl, e₁, e₂, rfl⟩ := e <;> exact ⟨b', by rw [list_inj e₁, list_inj e₂]⟩

/-- `map_update_get_domains/5` over appended domains, against lookups of each part from any values. -/
theorem gd_append_rel2 (m : Nat) (dnf acc accA accB rt cb₁ cb₂ : Term)
    (hcb : (D m).pure cb₁ #[] = (D m).pure cb₂ #[]) (A B : List Term) {g a R Y : Term} {V Mi : List Term}
    (hR : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list (A ++ B)) acc rt cb₂ = .ok R)
    (hA : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list A) accA rt cb₁ =
      .ok (.tuple #[g, Term.list V, Term.list Mi, a]))
    (hB : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 1)) dnf (Term.list B) accB rt cb₁ = .ok Y) :
    GShift g V Mi R Y := by
  simp only [Elixir.Module.Types.Descr.«map_update_get_domains/5», pure, Except.pure, Lynx.Except.ok_bind] at hR hA hB
  rw [foldl_fun, foldl1_list_append] at hR
  obtain ⟨X, hX, hR'⟩ := bind_ok hR
  rw [← foldl_fun] at hX hR'
  obtain ⟨g', V', Mi', a', b', eA, hx, -⟩ := gd_fold_shift m dnf rt cb₂ cb₁ hcb.symm _ (gshift_fresh acc accA) hX hA
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eA
  obtain ⟨e₁, eV, eM, -⟩ := eA
  rw [← e₁, ← list_inj eV, ← list_inj eM] at hx
  rcases hx with ⟨rfl, e⟩ | ⟨rfl, e⟩ <;> rw [e] at hR' <;> simp only [List.append_nil] at hR' <;>
    exact gd_fold_shift m dnf rt cb₂ cb₁ hcb.symm _ (gshift_start _ V Mi a' accB) hR' hB

theorem orElse_boolT {g g' : Term} (hg : g = .atom "true" ∨ g = .atom "false")
    (hg' : g' = .atom "true" ∨ g' = .atom "false") :
    ∃ F, Lynx.Except.orElse (.ok g) (.ok g') true = .ok F ∧ (F = .atom "true" ∨ F = .atom "false") := by
  rcases hg with rfl | rfl
  · exact ⟨_, rfl, Or.inl rfl⟩
  · exact ⟨g', by simp [Lynx.Except.orElse], hg'⟩

@[simp] theorem orElse_true_l (x : Except Exception Term) : Lynx.Except.orElse (.ok (.atom "true")) x true = .ok (.atom "true") := rfl

@[simp] theorem orElse_false_l (x : Except Exception Term) : Lynx.Except.orElse (.ok (.atom "false")) x true = x := by
  simp [Lynx.Except.orElse]

theorem minus_nil (l : List Term) : Erlang.erlang.«--/2» .nil (Term.list l) = .ok .nil := by
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have pn : Term.properList? .nil = some [] := Term.properList?_list []
  simp [Erlang.erlang.«--/2», Term.properList?_list, pn, e00]

theorem minus_nil0 : Erlang.erlang.«--/2» .nil .nil = .ok .nil := minus_nil []

theorem app_nil_l (l : List Term) : Erlang.erlang.«++/2» .nil (Term.list l) = .ok (Term.list l) := append_list [] l

theorem app_nil0 : Erlang.erlang.«++/2» .nil .nil = .ok .nil := append_list [] []

theorem app_nil_r (l : List Term) : Erlang.erlang.«++/2» (Term.list l) .nil = .ok (Term.list l) := by
  simpa using append_list l []

theorem dnf_opt_relB_force (m : Nat) (bdd dnf : Term) (Rs Os Dr Do : List Term) (c : Term) (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Dr, Term.list Do]) (.tuple #[c, .atom "force"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (splitT (Rs ++ Os) (.atom "nil") (Dr ++ Do)) (.tuple #[c, .atom "force"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have hcb : (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[dnf, Term.list Os, Term.list Rs]) #[] = (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[dnf, .nil, Term.list (Rs ++ Os)]) #[] := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list, app_nil_r]
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp only [splitT, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2»] at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Erlang.erlang.«not/1», Lynx.Term.isMember,
    Lynx.Except.andAlso, minus_nil, minus_nil0, app_nil0, app_nil_l, app_nil_r, append_list, gnil] at h₁ h₂
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG, Lynx.Except.ok_bind] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG', Lynx.Except.ok_bind] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE, Lynx.Except.ok_bind] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, .nil, Term.list (Rs ++ Os)]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, .nil, Term.list (Rs ++ Os)]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ := gd_append_rel (m + 1) dnf (.map []) (.atom "true") _ _ hcb Dr Do hH hG hG'
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, -, -, rfl⟩ := eY
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH, Lynx.Except.ok_bind] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE', Lynx.Except.ok_bind] at h₂
  all_goals
    rcases hg₁ with rfl | rfl <;> simp only [orElse_true_l, orElse_false_l, Lynx.Except.ok_bind] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    simp only [bind, Except.bind,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    rename_i xX vX hX x96 v96 h96
    have hb : vX.2 = .atom "true" := by
      clear h₁ h₂
      repeat' split at hX
      all_goals first | (simp at hX; done) | (simp only [Except.ok.injEq] at hX; subst hX; rfl)
    rw [hb] at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    rw [named_keys_append] at N₂
    obtain ⟨p, Np, Np'⟩ := bind_ok N₂
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := Np) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := Np') (hab := R₁)
    have e₂ : n₂' = n₂ := by
      simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
        Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse] at N₂'
      exact N₂'.symm
    subst e₂
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all

theorem dnf_opt_relB_keep (m : Nat) (bdd dnf : Term) (Rs Os Dr Do : List Term) (c : Term) (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Dr, Term.list Do]) (.tuple #[c, .atom "keep"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (splitT (Rs ++ Os) (.atom "nil") (Dr ++ Do)) (.tuple #[c, .atom "keep"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have hcb : (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[dnf, Term.list Os, Term.list Rs]) #[] = (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[dnf, .nil, Term.list (Rs ++ Os)]) #[] := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list, app_nil_r]
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp only [splitT, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2»] at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember,
    Lynx.Except.andAlso, minus_nil, minus_nil0, app_nil0, app_nil_l, app_nil_r, append_list, gnil] at h₁ h₂
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG, Lynx.Except.ok_bind] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG', Lynx.Except.ok_bind] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE, Lynx.Except.ok_bind] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, .nil, Term.list (Rs ++ Os)]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, .nil, Term.list (Rs ++ Os)]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ := gd_append_rel (m + 1) dnf (.map []) (.atom "true") _ _ hcb Dr Do hH hG hG'
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, -, -, rfl⟩ := eY
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH, Lynx.Except.ok_bind] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE', Lynx.Except.ok_bind] at h₂
  all_goals
    rcases hg₁ with rfl | rfl <;> simp only [orElse_true_l, orElse_false_l, Lynx.Except.ok_bind] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    simp only [bind, Except.bind,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    rename_i xX vX hX x96 v96 h96
    have hb : vX.2 = .atom "true" := by
      clear h₁ h₂
      repeat' split at hX
      all_goals first | (simp at hX; done) | (simp only [Except.ok.injEq] at hX; subst hX; rfl)
    rw [hb] at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    rw [named_keys_append] at N₂
    obtain ⟨p, Np, Np'⟩ := bind_ok N₂
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := Np) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := Np') (hab := R₁)
    have e₂ : n₂' = n₂ := by
      simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
        Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse] at N₂'
      exact N₂'.symm
    subst e₂
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all

theorem dnf_opt_relB_reject (m : Nat) (bdd dnf : Term) (Rs Os Dr Do : List Term) (c : Term) (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Dr, Term.list Do]) (.tuple #[c, .atom "reject"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (splitT (Rs ++ Os) (.atom "nil") (Do ++ Dr)) (.tuple #[c, .atom "reject"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have hcb : (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[dnf, Term.list Os, Term.list Rs]) #[] = (D (m + 1)).pure (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[dnf, .nil, Term.list (Rs ++ Os)]) #[] := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure,
      Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list, app_nil_r]
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp only [splitT, Elixir.Module.Types.Descr.«map_keys_from_negated_set/2»] at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember,
    Lynx.Except.andAlso, minus_nil, minus_nil0, app_nil0, app_nil_l, gnil] at h₁ h₂
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG, Lynx.Except.ok_bind] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, Term.list Os, Term.list Rs]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, Term.list Os, Term.list Rs]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG', Lynx.Except.ok_bind] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE, Lynx.Except.ok_bind] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Do ++ Dr))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, .nil, Term.list (Rs ++ Os)]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Do ++ Dr)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, .nil, Term.list (Rs ++ Os)]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ :=
    gd_append_rel2 (m + 1) dnf (.map []) a₁ (.map []) (.atom "true") _ _ hcb Do Dr hH hG' hG
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, eV, eM, rfl⟩ := eY
  rw [← list_inj eV, ← list_inj eM] at hx
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH, Lynx.Except.ok_bind] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (M₁ ++ M₁')) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (M₁ ++ M₁')) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE', Lynx.Except.ok_bind] at h₂
  all_goals
    rcases hg₁' with h | h <;> (try subst h) <;>
      simp only [orElse_true_l, orElse_false_l, Lynx.Except.ok_bind] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    simp only [bind, Except.bind, Lynx.Except.orElse,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    rename_i xX vX hX x96 v96 h96
    have hb : vX.2 = .atom "true" := by
      clear h₁ h₂
      repeat' split at hX
      all_goals first | (simp at hX; done) | (simp only [Except.ok.injEq] at hX; subst hX; rfl)
    rw [hb] at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    rw [named_keys_append] at N₂
    obtain ⟨p, Np, Np'⟩ := bind_ok N₂
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := Np) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := Np') (hab := R₁)
    have e₂ : n₂' = n₂ := by
      simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
        Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse] at N₂'
      exact N₂'.symm
    subst e₂
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all
  all_goals sorry

theorem dnf_opt_relB (m : Nat) (bdd dnf : Term) (Rs Os Dr Do : List Term) (c : Term) (md : String) (hmd : Mode md)
    (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Dr, Term.list Do]) (.tuple #[c, .atom md])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (splitT (Rs ++ Os) (.atom "nil") (if md = "reject" then Do ++ Dr else Dr ++ Do)) (.tuple #[c, .atom md])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  rcases hmd with rfl | rfl | rfl
  · exact dnf_opt_relB_force m bdd dnf Rs Os Dr Do c st₁ st₂ h₁ h₂
  · exact dnf_opt_relB_keep m bdd dnf Rs Os Dr Do c st₁ st₂ h₁ h₂
  · exact dnf_opt_relB_reject m bdd dnf Rs Os Dr Do c st₁ st₂ h₁ h₂

theorem dnf_neg_relB_keep (m : Nat) (bdd dnf : Term) (Rq : Term) (N : List (Term × Term)) (Dr Do : List Term) (c : Term)
    (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list Dr, Term.list Do]) (.tuple #[c, .atom "keep"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list (Dr ++ Do), .nil]) (.tuple #[c, .atom "keep"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember,
    Lynx.Except.andAlso, app_nil_r, append_list, gnil] at h₁ h₂
  simp only [bind, Except.bind] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  rename_i xo opt2 hopt
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG'] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ := gd_append_rel (m + 1) dnf (.map []) (.atom "true") _ _ rfl Dr Do hH hG hG'
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, -, -, rfl⟩ := eY
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE'] at h₂
  all_goals
    rcases hg₁ with rfl | rfl <;> simp only [orElse_true_l, orElse_false_l] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    try simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := N₂) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := N₂') (hab := R₁)
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    try simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all


theorem dnf_neg_relB_force (m : Nat) (bdd dnf : Term) (Rq : Term) (N : List (Term × Term)) (Dr Do : List Term) (c : Term)
    (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list Dr, Term.list Do]) (.tuple #[c, .atom "force"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list (Dr ++ Do), .nil]) (.tuple #[c, .atom "force"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Erlang.erlang.«not/1», Lynx.Term.isMember,
    Lynx.Except.andAlso, app_nil_r, append_list, gnil] at h₁ h₂
  simp only [bind, Except.bind] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  rename_i xo opt2 hopt
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG'] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Dr ++ Do)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ := gd_append_rel (m + 1) dnf (.map []) (.atom "true") _ _ rfl Dr Do hH hG hG'
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, -, -, rfl⟩ := eY
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (MM ++ M₁)) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE'] at h₂
  all_goals
    rcases hg₁ with rfl | rfl <;> simp only [orElse_true_l, orElse_false_l] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r, Lynx.Except.ok_bind] at h₁ h₂
    try simp only [bind, Except.bind, Lynx.Except.guard, Lynx.Except.andAlso, Lynx.Except.orElse, pure, Except.pure,
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := N₂) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := N₂') (hab := R₁)
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    try simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all


theorem dnf_neg_relB_reject (m : Nat) (bdd dnf : Term) (Rq : Term) (N : List (Term × Term)) (Dr Do : List Term) (c : Term)
    (st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list Dr, Term.list Do]) (.tuple #[c, .atom "reject"])
      (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rq, .nil, .map N, Term.list (Do ++ Dr), .nil]) (.tuple #[c, .atom "reject"])
      (.atom "true") st₂ = .ok r₂) : RelB r₁ r₂ := by
  have gnil : ∀ a cb, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf .nil a (.atom "true") cb =
      .ok (.tuple #[.atom "false", .nil, .nil, a]) := fun a cb => by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember,
    Lynx.Except.andAlso, gnil] at h₁ h₂
  simp only [bind, Except.bind] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  rename_i xo opt2 hopt
  -- The first run looks up the required domains and then the optional ones.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr)
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Dr) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list Do) a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG'] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE] at h₁
  -- The second run looks up all domains at once.
  obtain ⟨H, hH⟩ : ∃ H, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Do ++ Dr))
      (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[dnf, opt2, Rq]) = .ok H := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf (Term.list (Do ++ Dr)) (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
          #[dnf, opt2, Rq]) with
    | error e => simp [h] at h₂
    | ok H => exact ⟨H, rfl⟩
  obtain ⟨gg, VV, MM, aa, bb, eY, hx, -⟩ :=
    gd_append_rel2 (m + 1) dnf (.map []) a₁ (.map []) (.atom "true") _ _ rfl Do Dr hH hG' hG
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at eY
  obtain ⟨rfl, eV, eM, rfl⟩ := eY
  rw [← list_inj eV, ← list_inj eM] at hx
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    simp only [hH] at h₂
    obtain ⟨E₂, hE'⟩ : ∃ E₂, Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (M₁ ++ M₁')) =
          .ok E₂ := by
      cases h : Erlang.lists.«map/2» (D (m + 2))
          (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list (M₁ ++ M₁')) with
      | error e => simp [h] at h₂
      | ok E => exact ⟨E, rfl⟩
    simp only [hE'] at h₂
  all_goals
    rcases hg₁' with h | h <;> (try subst h) <;>
      simp only [orElse_true_l, orElse_false_l] at h₁ h₂
  all_goals
    try simp only [append_list, app_nil_r] at h₁ h₂
    try simp only [bind, Except.bind, Lynx.Except.orElse] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    have R₁ := named_keys_relB (m + 1) (h₁ := N₁) (h₂ := N₂) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB (m + 1) (h₁ := N₁') (h₂ := N₂') (hab := R₁)
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    try simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all


/-! Splits of gradual keys with required atoms and a negated set holding them: the updates at the atoms outside
the set and at the required atoms. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The named keys of a split with required atoms inside a negated set: the required atoms updated, and the keys
outside the set read. -/
theorem named_tail_negA (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (vne : ∃ x, den v x) (keep : Bool) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (hne : lines ≠ []) (A ks : List String) (Bl : List Term) (fBl : ∀ b ∈ Bl, MField E b) (fl : Bool) {T₁ : Term}
    (hT₁ : E T₁) (errs : List Term) :
    ∃ (T₂ Er₂ T' Er' : Term) (f₂ f' : Bool) (B₂ : List Term),
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₁, Term.list Bl, Term.list errs, boolAtom fl])
        (Term.list lines) (Term.list (A.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") (.atom "true")
        (.atom "true") = .ok (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂]) ∧
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂])
        (Term.list lines) (Term.list (ks.map Term.atom)) (keepOp v keep) (.atom "false") (.atom "true") (.atom "true")
        (.atom "false") = .ok (.tuple #[T', Term.list B₂, Er', boolAtom f']) ∧ (∀ b ∈ B₂, MField E b) ∧
      ∀ w, (∃ b ∈ B₂, denMF E den b w = Bool.true) ↔ (∃ b ∈ Bl, denMF E den b w = Bool.true) ∨
        ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v keep a w := by
  classical
  let lk : String → Bool := fun a => decide (Lacking den lines a)
  have hlk : ∀ a, lk a = Bool.true ↔ Lacking den lines a := fun a => by simp [lk]
  obtain ⟨B₂, f₂, T₂, Er₂, e0, hT₂, -, -, -, -, bT₂⟩ := named_keep ef (n := n + 2) (by omega) hv vne keep lines hl hne
    Bool.true Bool.true lk hlk A Bl fl T₁ (Term.list errs) hT₁
  obtain ⟨fB₂, sB₂⟩ := bT₂ rfl fBl
  obtain ⟨B', f', T', Er', e1, -, -, -, -, bF', -⟩ := named_keep ef (n := n + 2) (by omega) hv vne keep lines hl hne
    Bool.false Bool.false lk hlk ks B₂ f₂ T₂ Er₂ hT₂
  obtain rfl := bF' rfl
  refine ⟨T₂, Er₂, T', Er', f₂, f', B', by simpa using e0, by simpa using e1, fB₂, fun w => ?_⟩
  rw [sB₂]
  exact or_congr_right (exists_congr fun a => and_congr_right fun _ => keepSem_iff)

end

/-- List difference of atoms keeps the first list when no atom of the second is in it. -/
theorem minus_disj (ks A : List String) (h : ∀ s ∈ ks, s ∉ A) :
    Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) (Term.list (A.map Term.atom)) =
      .ok (Term.list (ks.map Term.atom)) := by
  have keep : ∀ (B : List String), (∀ s ∈ ks, s ∉ B) →
      List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
        (ks.map Term.atom) (B.map Term.atom) = ks.map Term.atom := by
    intro B hB
    induction B with
    | nil => rfl
    | cons b B ih =>
      simp only [List.map_cons, List.foldl_cons]
      have e : List.eraseP (fun x => decide (compareExact (x.fuel (.atom b)) x (.atom b) = .eq)) (ks.map Term.atom) =
          ks.map Term.atom := by
        apply List.eraseP_of_forall_not
        intro x mx
        obtain ⟨s, ms, rfl⟩ := List.mem_map.mp mx
        simp only [decide_eq_true_eq, compareExact_eq_atom, Term.atom.injEq]
        intro e; subst e; exact hB s ms List.mem_cons_self
      rw [e]
      exact ih fun s ms m => hB s ms (List.mem_cons_of_mem _ m)
  simp [Erlang.erlang.«--/2», Term.properList?_list, keep A h]

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem upd_dnf_negreq (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (keep : Bool) (bdd : Term) (fbd : MField E bdd)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (N : List (Term × Term))
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (hks : ∀ s ∈ ks, mapLookup N (.atom s) = none)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks)
    (A : List String) (hA : ∀ s ∈ A, mapLookup N (.atom s) ≠ none)
    (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (A.map Term.atom) (.map N) (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") =
        .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Dm v keep w ∨
          ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v keep a w) := by
  classical
  have keysN := setStrs_keys hNa
  obtain ⟨R', rR', -, mR'⟩ := usort_atoms (ks.map Term.atom ++ (setStrs N).map Term.atom) (fun k mk => by
    rcases List.mem_append.mp mk with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;> exact ⟨s, rfl⟩)
  obtain ⟨AK, rfl⟩ : ∃ AK : List String, R' = AK.map Term.atom := by
    have aR : ∀ r ∈ R', ∃ s, r = .atom s := fun r mr => by
      rcases List.mem_append.mp ((mR' r).mp mr) with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;>
        exact ⟨s, rfl⟩
    clear rR' mR'
    induction R' with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := aR r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => aR x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  have hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ setStrs N := fun s => by
    have := mR' (.atom s); simp at this; exact this
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) .nil = .ok (Term.list (Ds.map Term.atom)) := by
    simpa using append_list (Ds.map Term.atom) []
  have mk0 : Erlang.erlang.«++/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simpa using append_list (ks.map Term.atom) []
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have a0 : Erlang.erlang.«++/2» (Term.list ([] : List Term)) .nil = .ok .nil := by
    simp [Erlang.erlang.«++/2»]
  have minusKA := minus_disj ks A fun s ms ma => hA s ma (hks s ms)
  have minusK0 : Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simpa using minus_disj ks [] (by simp)
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (A ++ ks)
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp only [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3»]
    simpa [append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁, vD₁, vf₁⟩ := upd_domains2 ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  cases keep
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», mv,
      modeT, r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨-, NK, -, -, -, -, -, lnNK, -⟩ := box_named (E := E) (n + 1) lines hl' AK
    have hA1 : ∀ d ∈ val₁, ∃ s ∈ domainKinds, d = .atom s := fun d md => by
      obtain ⟨s, ms, rfl, -⟩ := (vD₁ d).mp md; exact ⟨s, hDs s ms, rfl⟩
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort val₁ hA1
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d := fun d => by
      rw [mKs, vD₁]
      constructor
      · rintro ⟨s, ms, e, h⟩
        cases e
        exact ⟨ms, (kind_held ef hl hne lnNK (hDs d ms)).mpr h⟩
      · rintro ⟨ms, h⟩
        exact ⟨d, ms, rfl, (kind_held ef hl hne lnNK (hDs d ms)).mp h⟩
    have noAtom : "atom" ∉ Ks → ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x := fun na L mL x hx =>
      na ((memKs _).mpr ⟨hat, (kind_held ef hl hne lnNK (hDs _ hat)).mpr ⟨L, mL, x, hx⟩⟩)
    have rmode : keepOp v Bool.false = cOp v Bool.false "reject" := keepOp_cOp v Bool.false
    by_cases v0 : val₁ = []
    · subst v0
      have Ks0 : Ks = [] := by
        cases Ks with
        | nil => rfl
        | cons k _ => exact absurd ((mKs k).mp List.mem_cons_self) (by simp)
      subst Ks0
      have part := partition_atom (n + 5) []
      simp only [List.map_nil, List.filter_nil] at part
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd hv sv Bool.false
        (mode_modeS Bool.false) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' [] (by simp)
        (Or.inr ⟨rfl, noAtom (by simp)⟩)
        ⟨fun h => by simp at h, fun h => by simpa using h "atom" (by simp [domainKinds])⟩
      replace rX : Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
          (Term.list (ks.map Term.atom)) .nil (keepOp v Bool.false) (Term.list (AK.map Term.atom)) = .ok (.map X) := by
        rw [rmode]; exact rX
      simp [Term.list, boolAtom, Lynx.Except.orElse,
        Erlang.erlang.«element/2», Erlang.erlang.«length/1», Lynx.Term.compare_integers, part, rX]
      have semB : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false (modeS Bool.false)
          [] w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] v Bool.false w := by
        intro w
        have nf : ¬FullK ([] : List String) := fun h => by simpa using h "atom" (by simp [domainKinds])
        simp [UpdSemKR, nf]
      rcases mapsD_cases mX with ⟨rfl, emp⟩ | ⟨c, neX, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl hne
          A ks [] (by simp) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] v Bool.false w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semB]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl hne
          A ks [c] (by simpa using fc) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] v Bool.false w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semB]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        have mapE : Term.map X ≠ Term.map [] := fun e => neX (by injection e)
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
    · have f1 : f₁ = Bool.true := vf₁ v0
      subst f1
      have vne' : Term.list val₁ ≠ .nil := by
        cases val₁ with
        | nil => exact absurd rfl v0
        | cons _ _ => simp [Term.list]
      have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
        simpa using length_list (Ks.map Term.atom)
      have fullI : Ks.length = 12 ↔ FullK Ks := by
        rw [lenKs]
        exact ⟨fun h d md => (mKs d).mpr (h d md), fun h d md => (mKs d).mp (h d md)⟩
      have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
          (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false (modeS Bool.false)
            Bx w) →
          (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) v (modeS Bool.false) Ws w) →
          ((FullK Ks ∧ Bx = Ks ∧ Ws = []) ∨ (¬FullK Ks ∧ Bx = Ks.filter (· = "atom") ∧ Ws = Ks.filter (· ≠ "atom"))) →
          ∀ w, (SB w ∨ SW w) ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w := by
        intro Bx Ws SB SW hB hW hc w
        rw [hB, hW]
        rcases hc with ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
        · simp [UpdSemKR, hf]
        · simp [UpdSemKR, hf]
      -- The descr: the box, and the widened kinds.
      have hBox : ∀ Bx : List String, (∀ d ∈ Bx, d ∈ Ks) → (FullK Ks → Bx = Ks) →
          (¬FullK Ks → Bx = Ks.filter (· = "atom")) →
          ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
            (Term.list (ks.map Term.atom)) (Term.list (Bx.map Term.atom)) (keepOp v Bool.false)
            (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
          MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
            (modeS Bool.false) Bx) := by
        intro Bx sub hf hnf
        have hAt : "atom" ∈ Bx ∨ (modeS Bool.false = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x) := by
          by_cases ak : "atom" ∈ Ks
          · left
            by_cases full : FullK Ks
            · rw [hf full]; exact ak
            · rw [hnf full]; simp [ak]
          · exact Or.inr ⟨rfl, noAtom ak⟩
        have hlen : Bx.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Bx := by
          by_cases full : FullK Ks
          · rw [hf full, fullI]; exact Iff.rfl
          · rw [hnf full]
            constructor
            · intro h
              have : (Ks.filter (· = "atom")).length ≤ 1 := by
                have nd := ndKs.filter (fun x => decide (x = "atom"))
                have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
                  simpa using (List.mem_filter.mp m).2
                generalize Ks.filter (· = "atom") = l at nd all
                match l, nd, all with
                | [], _, _ => simp
                | [_], _, _ => simp
                | x :: y :: t, nd, all =>
                  exfalso
                  have ex := all x List.mem_cons_self
                  have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
                  exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
              omega
            · intro h
              have := h "binary" (by simp [domainKinds])
              simp at this
        obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd hv sv Bool.false
          (mode_modeS Bool.false) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' Bx
          (fun d md => subKs d (sub d md)) hAt hlen
        refine ⟨X, ?_, mX⟩
        rw [rmode]; exact rX
      simp [vne', boolAtom, Lynx.Except.orElse, rKs, Erlang.erlang.«element/2», modeT, lenK,
        Lynx.Term.compare_integers]
      by_cases full : FullK Ks
      · have hL' : ((Ks.length : Int) = 12) := by have := fullI.mpr full; omega
        obtain ⟨Z, rZ, MZ⟩ := hBox Ks (fun d m => m) (fun _ => rfl) (fun h => absurd full h)
        have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
            (modeS Bool.false) Ks w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v
            Bool.false w := fun w => by
          have := semAll Ks [] _ (fun _ => False) (fun w => Iff.rfl) (fun w => by simp) (Or.inl ⟨full, rfl, rfl⟩) w
          simpa using this
        simp [hL', rZ, Term.list]
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
            hne A ks [] (by simp) Bool.true hT₁ errs
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
            hne A ks [c] (by simpa using fc) Bool.true hT₁ errs
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]

      · have hL' : ¬((Ks.length : Int) = 12) := by intro h; exact full (fullI.mp (by omega))
        have part := partition_atom (n + 5) Ks
        obtain ⟨X, rX, mX⟩ := hBox (Ks.filter (· = "atom")) (fun d m => (List.mem_filter.mp m).1)
          (fun h => absurd h full) (fun _ => rfl)
        have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
        have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
        simp [hL', part, rX]
        by_cases wn : Ks.filter (· ≠ "atom") = []
        · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
          simp [wn', Term.list]
          have MZ := mX
          have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
              (modeS Bool.false) (Ks.filter (· = "atom")) w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks v Bool.false w := fun w => by
            have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
              (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) (Or.inr ⟨full, rfl, rfl⟩) w
            simpa using this
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
              hne A ks [] (by simp) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                  ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
              hne A ks [c] (by simpa using fc) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                  ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]


        · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) hv Bool.false (Or.inr vne) (mode_modeS Bool.false)
            (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
          rw [← keepOp_cOp] at rW
          obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
          have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
            cases h : Ks.filter (· ≠ "atom") with
            | nil => exact absurd h wn
            | cons d ds => simp [Term.list]
          simp at wsCmp rW
          simp [wsCmp, rW, rZ]
          have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
              (modeS Bool.false) (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) v
              (modeS Bool.false) (Ks.filter (· ≠ "atom")) w) ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks v Bool.false w := fun w =>
            semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
              (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) (Or.inr ⟨full, rfl, rfl⟩) w
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
              hne A ks [] (by simp) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                  ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.false lines hl
              hne A ks [c] (by simpa using fc) Bool.true hT₁ errs
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.false w ∨
                  ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.false a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]


  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
      modeT, r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memK0 : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ (Bool.true = Bool.true ∨
        KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d) := fun d => by simpa using memK0 d
    have aK : "atom" ∈ Ks := (memK0 _).mpr hat
    have full : ¬(Bool.true = Bool.false ∧ FullK Ks) := fun h => by cases h.1
    have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
        (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false (modeS Bool.true)
          Bx w) →
        (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) v (modeS Bool.true) Ws w) →
        Bx = Ks.filter (· = "atom") → Ws = Ks.filter (· ≠ "atom") →
        ∀ w, (SB w ∨ SW w) ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w := by
      intro Bx Ws SB SW hB hW eB eW w
      subst eB eW
      rw [hB, hW]
      simp [UpdSemKR]
    have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
      cases Ds with
      | nil => simp at hat
      | cons _ _ => simp [Term.list]
    have part := partition_atom (n + 5) Ks
    have rmode : keepOp v Bool.true = cOp v Bool.false "keep" := keepOp_cOp v Bool.true
    obtain ⟨X, rX, mX⟩ : ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
        (Term.list (ks.map Term.atom)) (Term.list ((Ks.filter (· = "atom")).map Term.atom)) (keepOp v Bool.true)
        (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
        MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
          (modeS Bool.true) (Ks.filter (· = "atom"))) := by
      have hlen : (Ks.filter (· = "atom")).length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Ks.filter (· = "atom") := by
        constructor
        · intro h
          have : (Ks.filter (· = "atom")).length ≤ 1 := by
            have nd := ndKs.filter (fun x => decide (x = "atom"))
            have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
              simpa using (List.mem_filter.mp m).2
            generalize Ks.filter (· = "atom") = l at nd all
            match l, nd, all with
            | [], _, _ => simp
            | [_], _, _ => simp
            | x :: y :: t, nd, all =>
              exfalso
              have ex := all x List.mem_cons_self
              have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
              exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
          omega
        · intro h
          have := h "binary" (by simp [domainKinds])
          simp at this
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd hv sv Bool.false
        (mode_modeS Bool.true) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' (Ks.filter (· = "atom"))
        (fun d m => subKs d (List.mem_filter.mp m).1) (Or.inl (by simp [aK])) hlen
      refine ⟨X, ?_, mX⟩
      rw [rmode]; exact rX
    have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
    have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
    have o1 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
      cases f₁ <;> rfl
    have o2 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "false")) Bool.true = .ok (boolAtom f₁) := by
      cases f₁ <;> rfl
    simp [dne', rKs, Erlang.erlang.«element/2», modeT, part, rX, o1, o2]
    by_cases wn : Ks.filter (· ≠ "atom") = []
    · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
      simp [wn', Term.list]
      have MZ := mX
      have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
          (modeS Bool.true) (Ks.filter (· = "atom")) w ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks v Bool.true w := fun w => by
        have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
          (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) rfl rfl w
        simpa using this
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.true lines hl
          hne A ks [] (by simp) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.true lines hl
          hne A ks [c] (by simpa using fc) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]


    · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) hv Bool.false (Or.inr vne) (mode_modeS Bool.true)
        (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
      rw [← keepOp_cOp] at rW
      obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
      have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
        cases h : Ks.filter (· ≠ "atom") with
        | nil => exact absurd h wn
        | cons d ds => simp [Term.list]
      simp at wsCmp rW
      simp [wsCmp, rW, rZ]
      have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) v Bool.false
          (modeS Bool.true) (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) v
          (modeS Bool.true) (Ks.filter (· ≠ "atom")) w) ↔ UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks v Bool.true w := fun w =>
        semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
          (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) rfl rfl w
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.true lines hl
          hne A ks [] (by simp) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA ef hn hv vne Bool.true lines hl
          hne A ks [c] (by simpa using fc) f₁ hT₁ errs
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks v Bool.true w ∨
              ∃ a ∈ A, KeepSemM den (fun u => ∃ L ∈ lines, InMLine den L u) v Bool.true a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]




end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem named_tail_negA_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (A ks : List String) (Bl : List Term) (fBl : ∀ b ∈ Bl, MField E b) (fl : Bool) {T₁ : Term}
    (hT₁ : E T₁) (errs : Term) :
    ∃ (T₂ Er₂ T' Er' : Term) (f₂ f' : Bool) (B₂ : List Term),
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₁, Term.list Bl, errs, boolAtom fl])
        (Term.list lines) (Term.list (A.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (.atom "true") (.atom "true")
        (.atom "true") = .ok (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂]) ∧
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 6)) (.tuple #[T₂, Term.list B₂, Er₂, boolAtom f₂])
        (Term.list lines) (Term.list (ks.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "false") (.atom "true")
        (.atom "true") (.atom "false") = .ok (.tuple #[T', Term.list B₂, Er', boolAtom f']) ∧ (∀ b ∈ B₂, MField E b) ∧
      ∀ w, (∃ b ∈ B₂, denMF E den b w = Bool.true) ↔ (∃ b ∈ Bl, denMF E den b w = Bool.true) ∨
        ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w := by
  obtain ⟨B₂, f₂, T₂, Er₂, e0, hT₂, -, bT₂⟩ := named_del ef (n := n + 2) (by omega) hmd lines hl Bool.true Bool.true
    A Bl fl T₁ errs hT₁
  obtain ⟨fB₂, sB₂⟩ := bT₂ rfl fBl
  obtain ⟨B', f', T', Er', e1, -, bF', -⟩ := named_del ef (n := n + 2) (by omega) hmd lines hl Bool.false Bool.false
    ks B₂ f₂ T₂ Er₂ hT₂
  obtain rfl := bF' rfl
  exact ⟨T₂, Er₂, T', Er', f₂, f', B', by simpa using e0, by simpa using e1, fB₂, fun w => by rw [sB₂]⟩


theorem upd_dnf_negreq_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    (bdd : Term) (fbd : MField E bdd)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) (N : List (Term × Term))
    (hNa : ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (ks : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
      .ok (Term.list (ks.map Term.atom)))
    (hks : ∀ s ∈ ks, mapLookup N (.atom s) = none)
    (lnKS : ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks)
    (A : List String) (hA : ∀ s ∈ A, mapLookup N (.atom s) ≠ none)
    (Ds : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (A.map Term.atom) (.map N) (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (.atom "true") =
        .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Dm md w ∨
          ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) md a w) := by
  classical
  have keysN := setStrs_keys hNa
  obtain ⟨R', rR', -, mR'⟩ := usort_atoms (ks.map Term.atom ++ (setStrs N).map Term.atom) (fun k mk => by
    rcases List.mem_append.mp mk with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;> exact ⟨s, rfl⟩)
  obtain ⟨AK, rfl⟩ : ∃ AK : List String, R' = AK.map Term.atom := by
    have aR : ∀ r ∈ R', ∃ s, r = .atom s := fun r mr => by
      rcases List.mem_append.mp ((mR' r).mp mr) with mk | mk <;> obtain ⟨s, -, rfl⟩ := List.mem_map.mp mk <;>
        exact ⟨s, rfl⟩
    clear rR' mR'
    induction R' with
    | nil => exact ⟨[], rfl⟩
    | cons r rs ih =>
      obtain ⟨s, rfl⟩ := aR r List.mem_cons_self
      obtain ⟨B, rfl⟩ := ih fun x mx => aR x (List.mem_cons_of_mem _ mx)
      exact ⟨s :: B, rfl⟩
  have hAK : ∀ s, s ∈ AK ↔ s ∈ ks ∨ s ∈ setStrs N := fun s => by
    have := mR' (.atom s); simp at this; exact this
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) .nil = .ok (Term.list (Ds.map Term.atom)) := by
    simpa using append_list (Ds.map Term.atom) []
  have mk0 : Erlang.erlang.«++/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simpa using append_list (ks.map Term.atom) []
  have e00 : ∀ L : List Term, List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
      ([] : List Term) L = [] := fun L => by induction L <;> simp_all
  have a0 : Erlang.erlang.«++/2» (Term.list ([] : List Term)) .nil = .ok .nil := by
    simp [Erlang.erlang.«++/2»]
  have minusKA := minus_disj ks A fun s ms ma => hA s ma (hks s ms)
  have minusK0 : Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) .nil = .ok (Term.list (ks.map Term.atom)) := by
    simpa using minus_disj ks [] (by simp)
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (A ++ ks)
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simp only [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3»]
    simpa [append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁, vD₁, vf₁⟩ := upd_domains2 ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines) .nil T₁ (.atom "true")
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
        #[Term.list lines, Term.list (ks.map Term.atom), Term.list (A.map Term.atom)]) =
      .ok (.tuple #[.atom "false", .nil, .nil, T₁]) := by
    simp [Elixir.Module.Types.Descr.«map_update_get_domains/5», Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) .nil = .ok (Term.list val₁) := by
    simpa using append_list val₁ []
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  rcases hmd with rfl | rfl | rfl
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
      r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR', Lynx.Except.andAlso]
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memK0 : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have aK : "atom" ∈ Ks := (memK0 _).mpr hat
    have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
      cases Ds with
      | nil => simp at hat
      | cons _ _ => simp [Term.list]
    have o1 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
      cases f₁ <;> rfl
    have o2 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "false")) Bool.true = .ok (boolAtom f₁) := by
      cases f₁ <;> rfl
    have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
      simpa using length_list (Ks.map Term.atom)
    have fullI : Ks.length = 12 ↔ FullK Ks := by
      rw [lenKs]
      exact ⟨fun h d md => (mKs d).mpr (h d md), fun h d md => (mKs d).mp (h d md)⟩
    have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
        (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "force"
          Bx w) →
        (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map []) "force" Ws w) →
        ((FullK Ks ∧ Bx = Ks ∧ Ws = []) ∨ (¬FullK Ks ∧ Bx = Ks.filter (· = "atom") ∧ Ws = Ks.filter (· ≠ "atom"))) →
        ∀ w, (SB w ∨ SW w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w := by
      intro Bx Ws SB SW hB hW hc w
      rw [hB, hW]
      rcases hc with ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · simp [UpdSemD, hf]
      · simp [UpdSemD, hf]
    -- The descr: the box, and the widened kinds.
    have hBox : ∀ Bx : List String, (∀ d ∈ Bx, d ∈ Ks) → (FullK Ks → Bx = Ks) →
        (¬FullK Ks → Bx = Ks.filter (· = "atom")) →
        ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
          (Term.list (ks.map Term.atom)) (Term.list (Bx.map Term.atom)) (cOp (.map []) Bool.true "force")
          (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
        MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "force" Bx) := by
      intro Bx sub hf hnf
      have hAt : "atom" ∈ Bx ∨ ("force" = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x) := by
        by_cases ak : "atom" ∈ Ks
        · left
          by_cases full : FullK Ks
          · rw [hf full]; exact ak
          · rw [hnf full]; simp [ak]
        · exact absurd aK ak
      have hlen : Bx.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Bx := by
        by_cases full : FullK Ks
        · rw [hf full, fullI]; exact Iff.rfl
        · rw [hnf full]
          constructor
          · intro h
            have : (Ks.filter (· = "atom")).length ≤ 1 := by
              have nd := ndKs.filter (fun x => decide (x = "atom"))
              have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
                simpa using (List.mem_filter.mp m).2
              generalize Ks.filter (· = "atom") = l at nd all
              match l, nd, all with
              | [], _, _ => simp
              | [_], _, _ => simp
              | x :: y :: t, nd, all =>
                exfalso
                have ex := all x List.mem_cons_self
                have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
                exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
            omega
          · intro h
            have := h "binary" (by simp [domainKinds])
            simp at this
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
        (Or.inl rfl) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' Bx
        (fun d md => subKs d (sub d md)) hAt hlen
      refine ⟨X, ?_, mX⟩
      exact rX
    simp [dne', o1, o2, rKs, Erlang.erlang.«element/2», lenK,
      Lynx.Term.compare_integers]
    by_cases full : FullK Ks
    · have hL' : ((Ks.length : Int) = 12) := by have := fullI.mpr full; omega
      obtain ⟨Z, rZ, MZ⟩ := hBox Ks (fun d m => m) (fun _ => rfl) (fun h => absurd full h)
      have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "force" Ks w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w := fun w => by
        have := semAll Ks [] _ (fun _ => False) (fun w => Iff.rfl) (fun w => by simp) (Or.inl ⟨full, rfl, rfl⟩) w
        simpa using this
      simp [hL', rZ, Term.list]
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
          A ks [] (by simp) Bool.true hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
          A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
          simp [Term.list] at rN1; simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
          simp [Term.list] at rN1; simp [rN1, rN2, rr]

    · have hL' : ¬((Ks.length : Int) = 12) := by intro h; exact full (fullI.mp (by omega))
      have part := partition_atom (n + 5) Ks
      obtain ⟨X, rX, mX⟩ := hBox (Ks.filter (· = "atom")) (fun d m => (List.mem_filter.mp m).1)
        (fun h => absurd h full) (fun _ => rfl)
      have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
      have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
      simp [hL', part, rX]
      by_cases wn : Ks.filter (· ≠ "atom") = []
      · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
        simp [wn', Term.list]
        have MZ := mX
        have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "force" (Ks.filter (· = "atom")) w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
            (.map N) Ks "force" w := fun w => by
          have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
            (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) (Or.inr ⟨full, rfl, rfl⟩) w
          simpa using this
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
            A ks [] (by simp) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
            A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]


      · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) ef.none Bool.true (Or.inl rfl) (Or.inl rfl)
          (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
        obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
        have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
          cases h : Ks.filter (· ≠ "atom") with
          | nil => exact absurd h wn
          | cons d ds => simp [Term.list]
        simp at wsCmp rW
        simp [wsCmp, rW, rZ]
        have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "force" (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map [])
            "force" (Ks.filter (· ≠ "atom")) w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
            (.map N) Ks "force" w := fun w =>
          semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
            (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) (Or.inr ⟨full, rfl, rfl⟩) w
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
            A ks [] (by simp) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inl rfl) lines hl
            A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "force" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "force" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», m₃,
      r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, -⟩ := kinds_usort (Ds.map Term.atom) fun d md => by
      obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md; exact ⟨s, hDs s ms, rfl⟩
    have memK0 : ∀ d, d ∈ Ks ↔ d ∈ Ds := fun d => by rw [mKs]; simp
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ ("keep" ≠ "reject" ∨
        KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d) := fun d => by simpa using memK0 d
    have aK : "atom" ∈ Ks := (memK0 _).mpr hat
    have full : ¬("keep" ≠ "keep" ∧ FullK Ks) := fun h => h.1 rfl
    have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
        (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "keep"
          Bx w) →
        (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map []) "keep" Ws w) →
        Bx = Ks.filter (· = "atom") → Ws = Ks.filter (· ≠ "atom") →
        ∀ w, (SB w ∨ SW w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w := by
      intro Bx Ws SB SW hB hW eB eW w
      subst eB eW
      rw [hB, hW]
      simp [UpdSemD]
    have dne' : Term.list (Ds.map Term.atom) ≠ .nil := by
      cases Ds with
      | nil => simp at hat
      | cons _ _ => simp [Term.list]
    have part := partition_atom (n + 5) Ks
    obtain ⟨X, rX, mX⟩ : ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
        (Term.list (ks.map Term.atom)) (Term.list ((Ks.filter (· = "atom")).map Term.atom)) (cOp (.map []) Bool.true "keep")
        (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
        MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "keep" (Ks.filter (· = "atom"))) := by
      have hlen : (Ks.filter (· = "atom")).length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Ks.filter (· = "atom") := by
        constructor
        · intro h
          have : (Ks.filter (· = "atom")).length ≤ 1 := by
            have nd := ndKs.filter (fun x => decide (x = "atom"))
            have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
              simpa using (List.mem_filter.mp m).2
            generalize Ks.filter (· = "atom") = l at nd all
            match l, nd, all with
            | [], _, _ => simp
            | [_], _, _ => simp
            | x :: y :: t, nd, all =>
              exfalso
              have ex := all x List.mem_cons_self
              have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
              exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
          omega
        · intro h
          have := h "binary" (by simp [domainKinds])
          simp at this
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
        (Or.inr (Or.inl rfl)) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' (Ks.filter (· = "atom"))
        (fun d m => subKs d (List.mem_filter.mp m).1) (Or.inl (by simp [aK])) hlen
      refine ⟨X, ?_, mX⟩
      exact rX
    have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
    have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
    have o1 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "true")) Bool.true = .ok (.atom "true") := by
      cases f₁ <;> rfl
    have o2 : Lynx.Except.orElse (Except.ok (boolAtom f₁)) (Except.ok (.atom "false")) Bool.true = .ok (boolAtom f₁) := by
      cases f₁ <;> rfl
    simp [dne', rKs, Erlang.erlang.«element/2», part, rX, o1, o2]
    by_cases wn : Ks.filter (· ≠ "atom") = []
    · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
      simp [wn', Term.list]
      have MZ := mX
      have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "keep" (Ks.filter (· = "atom")) w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks "keep" w := fun w => by
        have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
          (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) rfl rfl w
        simpa using this
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inl rfl)) lines hl
          A ks [] (by simp) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inl rfl)) lines hl
          A ks [c] (by simpa using fc) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]


    · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) ef.none Bool.true (Or.inl rfl) (Or.inr (Or.inl rfl))
        (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
      obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
      have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
        cases h : Ks.filter (· ≠ "atom") with
        | nil => exact absurd h wn
        | cons d ds => simp [Term.list]
      simp at wsCmp rW
      simp [wsCmp, rW, rZ]
      have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
          "keep" (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map [])
          "keep" (Ks.filter (· ≠ "atom")) w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
          (.map N) Ks "keep" w := fun w =>
        semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
          (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) rfl rfl w
      rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inl rfl)) lines hl
          A ks [] (by simp) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inl rfl)) lines hl
          A ks [c] (by simpa using fc) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "keep" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "keep" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memK0, Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neZ, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
  · simp [splitT, hR, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», mv,
      r₁', r₂', rE', minusKA, minusK0, mk0, Erlang.sets.«to_list/1»,
      Erlang.maps.«keys/1», keysN, append_list, rR']
    have hks' : ∀ s ∈ ks, s ∉ setStrs N := fun s m h => setStrs_mem.mp h (hks s m)
    have lnKS' : ∀ L ∈ lines, ∀ s, LineNames L s → s ∈ setStrs N ∨ s ∈ ks := fun L mL s h =>
      (lnKS L mL s h).imp setStrs_mem.mpr id
    have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
    obtain ⟨-, NK, -, -, -, -, -, lnNK, -⟩ := box_named (E := E) (n + 1) lines hl' AK
    have hA1 : ∀ d ∈ val₁, ∃ s ∈ domainKinds, d = .atom s := fun d md => by
      obtain ⟨s, ms, rfl, -⟩ := (vD₁ d).mp md; exact ⟨s, hDs s ms, rfl⟩
    obtain ⟨Ks, rKs, mKs, ndKs, subKs, lenKs⟩ := kinds_usort val₁ hA1
    have memKs : ∀ d, d ∈ Ks ↔ d ∈ Ds ∧ KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d := fun d => by
      rw [mKs, vD₁]
      constructor
      · rintro ⟨s, ms, e, h⟩
        cases e
        exact ⟨ms, (kind_held ef hl hne lnNK (hDs d ms)).mpr h⟩
      · rintro ⟨ms, h⟩
        exact ⟨d, ms, rfl, (kind_held ef hl hne lnNK (hDs d ms)).mp h⟩
    have noAtom : "atom" ∉ Ks → ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x := fun na L mL x hx =>
      na ((memKs _).mpr ⟨hat, (kind_held ef hl hne lnNK (hDs _ hat)).mpr ⟨L, mL, x, hx⟩⟩)
    by_cases v0 : val₁ = []
    · subst v0
      have Ks0 : Ks = [] := by
        cases Ks with
        | nil => rfl
        | cons k _ => exact absurd ((mKs k).mp List.mem_cons_self) (by simp)
      subst Ks0
      have part := partition_atom (n + 5) []
      simp only [List.map_nil, List.filter_nil] at part
      obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
        (Or.inr (Or.inr rfl)) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' [] (by simp)
        (Or.inr ⟨rfl, noAtom (by simp)⟩)
        ⟨fun h => by simp at h, fun h => by simpa using h "atom" (by simp [domainKinds])⟩
      replace rX : Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
          (Term.list (ks.map Term.atom)) .nil (cOp (.map []) Bool.true "reject") (Term.list (AK.map Term.atom)) = .ok (.map X) := by
        exact rX
      simp [Term.list, boolAtom, Lynx.Except.orElse,
        Erlang.erlang.«element/2», Erlang.erlang.«length/1», Lynx.Term.compare_integers, part, rX]
      have semB : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "reject"
          [] w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] "reject" w := by
        intro w
        have nf : ¬FullK ([] : List String) := fun h => by simpa using h "atom" (by simp [domainKinds])
        simp [UpdSemD, nf]
      rcases mapsD_cases mX with ⟨rfl, emp⟩ | ⟨c, neX, lc, fc, sc⟩
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
          A ks [] (by simp) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] "reject" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semB]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
        simp only [Term.list] at rN1
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [rN1, rN2, rr]
      · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
          A ks [c] (by simpa using fc) f₁ hT₁ (Term.list errs)
        obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) [] "reject" w ∨
              ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
            rw [sB']; refine or_congr_left ?_; rw [← semB]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
        have mapE : Term.map X ≠ Term.map [] := fun e => neX (by injection e)
        rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
        · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d, Or.inl ⟨rfl, emp'⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
        · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, [], fun d => by simpa using memKs d,
            Or.inr ⟨r, rfl, fr, sr⟩⟩
          cases f₁ <;> simp [boolAtom] at rN1 rN2 ⊢ <;> simp [neX, getMapKeys_single, lc, Option.toList] <;>
            simp [Term.list] at rN1 <;> simp [rN1, rN2, rr]
    · have f1 : f₁ = Bool.true := vf₁ v0
      subst f1
      have vne' : Term.list val₁ ≠ .nil := by
        cases val₁ with
        | nil => exact absurd rfl v0
        | cons _ _ => simp [Term.list]
      have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
        simpa using length_list (Ks.map Term.atom)
      have fullI : Ks.length = 12 ↔ FullK Ks := by
        rw [lenKs]
        exact ⟨fun h d md => (mKs d).mpr (h d md), fun h d md => (mKs d).mp (h d md)⟩
      have semAll : ∀ (Bx Ws : List String) (SB SW : MW V → Prop),
          (∀ w, SB w ↔ BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true "reject"
            Bx w) →
          (∀ w, SW w ↔ Ws ≠ [] ∧ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map []) "reject" Ws w) →
          ((FullK Ks ∧ Bx = Ks ∧ Ws = []) ∨ (¬FullK Ks ∧ Bx = Ks.filter (· = "atom") ∧ Ws = Ks.filter (· ≠ "atom"))) →
          ∀ w, (SB w ∨ SW w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w := by
        intro Bx Ws SB SW hB hW hc w
        rw [hB, hW]
        rcases hc with ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
        · simp [UpdSemD, hf]
        · simp [UpdSemD, hf]
      -- The descr: the box, and the widened kinds.
      have hBox : ∀ Bx : List String, (∀ d ∈ Bx, d ∈ Ks) → (FullK Ks → Bx = Ks) →
          (¬FullK Ks → Bx = Ks.filter (· = "atom")) →
          ∃ X, Elixir.Module.Types.Descr.«map_update_box/6» (D (n + 6)) bdd (Term.list lines)
            (Term.list (ks.map Term.atom)) (Term.list (Bx.map Term.atom)) (cOp (.map []) Bool.true "reject")
            (Term.list (AK.map Term.atom)) = .ok (.map X) ∧
          MapsD E den X (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "reject" Bx) := by
        intro Bx sub hf hnf
        have hAt : "atom" ∈ Bx ∨ ("reject" = "reject" ∧ ∀ L ∈ lines, ∀ x, ¬LineTag den L "atom" x) := by
          by_cases ak : "atom" ∈ Ks
          · left
            by_cases full : FullK Ks
            · rw [hf full]; exact ak
            · rw [hnf full]; simp [ak]
          · exact Or.inr ⟨rfl, noAtom ak⟩
        have hlen : Bx.length = 12 ↔ ∀ d ∈ domainKinds, d ∈ Bx := by
          by_cases full : FullK Ks
          · rw [hf full, fullI]; exact Iff.rfl
          · rw [hnf full]
            constructor
            · intro h
              have : (Ks.filter (· = "atom")).length ≤ 1 := by
                have nd := ndKs.filter (fun x => decide (x = "atom"))
                have all : ∀ x ∈ Ks.filter (· = "atom"), x = "atom" := fun x m => by
                  simpa using (List.mem_filter.mp m).2
                generalize Ks.filter (· = "atom") = l at nd all
                match l, nd, all with
                | [], _, _ => simp
                | [_], _, _ => simp
                | x :: y :: t, nd, all =>
                  exfalso
                  have ex := all x List.mem_cons_self
                  have ey := all y (List.mem_cons_of_mem _ List.mem_cons_self)
                  exact (List.nodup_cons.mp nd).1 (by rw [ex, ← ey]; exact List.mem_cons_self)
              omega
            · intro h
              have := h "binary" (by simp [domainKinds])
              simp at this
        obtain ⟨X, rX, mX⟩ := box_part ef (n := n + 2) (by omega) lines bdd hl hne fbd sbd ef.none (Or.inr ⟨[], rfl⟩) Bool.true
          (Or.inr (Or.inr rfl)) (setStrs N) ks AK hks' (fun s => hAK s) lnKS' Bx
          (fun d md => subKs d (sub d md)) hAt hlen
        refine ⟨X, ?_, mX⟩
        exact rX
      simp [vne', boolAtom, Lynx.Except.orElse, rKs, Erlang.erlang.«element/2», lenK,
        Lynx.Term.compare_integers]
      by_cases full : FullK Ks
      · have hL' : ((Ks.length : Int) = 12) := by have := fullI.mpr full; omega
        obtain ⟨Z, rZ, MZ⟩ := hBox Ks (fun d m => m) (fun _ => rfl) (fun h => absurd full h)
        have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
            "reject" Ks w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w := fun w => by
          have := semAll Ks [] _ (fun _ => False) (fun w => Iff.rfl) (fun w => by simp) (Or.inl ⟨full, rfl, rfl⟩) w
          simpa using this
        simp [hL', rZ, Term.list]
        rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
            A ks [] (by simp) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
          simp only [Term.list] at rN1
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
        · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
            A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
          obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
              rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
          rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
          · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]
          · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
            simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
            simp [Term.list] at rN1; simp [rN1, rN2, rr]

      · have hL' : ¬((Ks.length : Int) = 12) := by intro h; exact full (fullI.mp (by omega))
        have part := partition_atom (n + 5) Ks
        obtain ⟨X, rX, mX⟩ := hBox (Ks.filter (· = "atom")) (fun d m => (List.mem_filter.mp m).1)
          (fun h => absurd h full) (fun _ => rfl)
        have hD' : ∀ d ∈ Ks.filter (· ≠ "atom"), d ∈ domainKinds := fun d m => subKs d (List.mem_filter.mp m).1
        have hA' : "atom" ∉ Ks.filter (· ≠ "atom") := fun m => by simpa using (List.mem_filter.mp m).2
        simp [hL', part, rX]
        by_cases wn : Ks.filter (· ≠ "atom") = []
        · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
          simp [wn', Term.list]
          have MZ := mX
          have semZ : ∀ w, BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
              "reject" (Ks.filter (· = "atom")) w ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks "reject" w := fun w => by
            have := semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ (fun _ => False) (fun w => Iff.rfl)
              (fun w => ⟨False.elim, fun h => absurd wn h.1⟩) (Or.inr ⟨full, rfl, rfl⟩) w
            simpa using this
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
              A ks [] (by simp) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                  ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
              A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                  ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]


        · obtain ⟨R, rW, mR⟩ := widen_part ef (n := n + 1) (by omega) ef.none Bool.true (Or.inl rfl) (Or.inr (Or.inr rfl))
            (Ks.filter (· ≠ "atom")) hA' hD' wn lines hl'
          obtain ⟨Z, rZ, MZ⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mR
          have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
            cases h : Ks.filter (· ≠ "atom") with
            | nil => exact absurd h wn
            | cons d ds => simp [Term.list]
          simp at wsCmp rW
          simp [wsCmp, rW, rZ]
          have semZ : ∀ w, (BoxSem den (fun u => ∃ L ∈ lines, InMLine den L u) (setStrs N) (.map []) Bool.true
              "reject" (Ks.filter (· = "atom")) w ∨ WRes den (fun u => ∃ L ∈ lines, InMLine den L u) (.map [])
              "reject" (Ks.filter (· ≠ "atom")) w) ↔ UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) []
              (.map N) Ks "reject" w := fun w =>
            semAll (Ks.filter (· = "atom")) (Ks.filter (· ≠ "atom")) _ _ (fun w => Iff.rfl)
              (fun w => ⟨fun h => ⟨wn, h⟩, fun h => h.2⟩) (Or.inr ⟨full, rfl, rfl⟩) w
          rcases mapsD_cases MZ with ⟨rfl, emp⟩ | ⟨c, neZ, lc, fc, sc⟩
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
              A ks [] (by simp) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                  ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.not_mem_nil, false_and, exists_false, false_iff]; exact emp w
            simp only [Term.list] at rN1
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [rN1, rN2, rr]
          · obtain ⟨T₂, Er₂, T', Er', f₂, f', B', rN1, rN2, fB', sB'⟩ := named_tail_negA_del ef hn (Or.inr (Or.inr rfl)) lines hl
              A ks [c] (by simpa using fc) Bool.true hT₁ (Term.list errs)
            obtain ⟨r, rr, hr⟩ := union_Y ef (m := n + 6) (by omega) B' fB' (S := fun w => UpdSemD den (fun u => ∃ L ∈ lines, InMLine den L u) [] (.map N) Ks "reject" w ∨
                  ∃ a ∈ A, DelAt (fun u => ∃ L ∈ lines, InMLine den L u) "reject" a w) fun w => by
                rw [sB']; refine or_congr_left ?_; rw [← semZ]; simp only [List.mem_singleton, exists_eq_left]; exact sc w
            rcases hr with ⟨rfl, emp'⟩ | ⟨bot, fr, sr⟩
            · refine ⟨T', .map [], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inl ⟨rfl, emp'⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]
            · refine ⟨T', .map [(.atom "map", r)], ⟨Er', boolAtom f', ?_⟩, Ks, memKs, Or.inr ⟨r, rfl, fr, sr⟩⟩
              simp [boolAtom] at rN1 rN2 ⊢; simp [neZ, getMapKeys_single, lc, Option.toList]
              simp [Term.list] at rN1; simp [rN1, rN2, rr]

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem kr_update_static_req (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (keep : Bool) {A Ds : List String} {neg : Term} {N : List (Term × Term)} (eN : neg = .map N)
    (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) (hA : ∀ s ∈ A, mapLookup N (.atom s) ≠ none)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
        (splitT (A.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ T Y er f, res = .tuple #[T, Y, er, f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨
              KindHeld (fun u => denMF E den b u = Bool.true) d)) ∧
            MapsY E den Y (fun w => UpdSemKR den (fun u => denMF E den b u = Bool.true) [] neg Dm v keep w ∨
              ∃ a ∈ A, KeepSemM den (fun u => denMF E den b u = Bool.true) v keep a w)) := by
  -- For negated sets, the keys outside the set, and the literals of the field naming only those or the set's.
  have negInfo : ∀ N, neg = .map N → ∃ ks : List String,
      Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) b =
        .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
      ∀ wb : Bdd (MLit E) b, Bdd (fun t => MLit E t ∧ LitIn (fun s => mapLookup N (.atom s) ≠ none ∨ s ∈ ks) t) b := by
    intro N _
    obtain ⟨R, rR, hR, -⟩ := neg_keys (den := den) ef N (n + 5) fb
    obtain ⟨ks, rfl⟩ : ∃ ks : List String, R = ks.map Term.atom := by
      clear rR
      induction R with
      | nil => exact ⟨[], rfl⟩
      | cons r rs ih =>
        obtain ⟨s, rfl, -⟩ := hR r List.mem_cons_self
        obtain ⟨B, rfl⟩ := ih fun x mx => hR x (List.mem_cons_of_mem _ mx)
        exact ⟨s :: B, rfl⟩
    refine ⟨ks, rR, fun s ms => ?_, fun wb => ?_⟩
    · obtain ⟨s', e, h⟩ := hR _ (List.mem_map_of_mem ms); cases e; exact h
    · obtain ⟨R', rR', -, lits, -⟩ := neg_keys_lits (den := den) ef N (n + 5) wb
      have e : R' = ks.map Term.atom := list_inj (Except.ok.inj (rR'.symm.trans rR))
      subst e
      exact lits.mono fun t ⟨lt, it⟩ => ⟨lt, fun k tag l et s ms => (it k tag l et s ms).imp id (by simp)⟩
  -- The semantics over the field.
  have conv : ∀ {lines : List Term}, (∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) →
      (fun u => ∃ L ∈ lines, InMLine den L u) = (fun u => denMF E den b u = Bool.true) := fun h =>
    funext fun u => propext (h u).symm
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 6)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 6) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 6) (by omega) rfl g sl
          (negs := []) (by simp) fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      have inB : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔
          ∃ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], InMLine den L w := fun w => by
        rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
      have hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
          Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N)
            (.tuple #[.integer k, tag, fieldsTerm l]) = .ok (Term.list (ks.map Term.atom)) ∧
          (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧ ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], ∀ s,
            LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
        intro N eN
        obtain ⟨ks, hR, hks, litsQ⟩ := negInfo N eN
        have names : ∀ s ∈ keyStrs l, mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
          rcases fb with ⟨k', e'⟩ | wb
          · intro s ms
            obtain ⟨-, -, e₃⟩ := tuple3_inj e'
            have : l = [] := fieldsTerm_inj (l' := []) e₃
            subst this; simp [keyStrs] at ms
          · exact (Bdd.leaf_iff.mp (litsQ wb)).2 k tag l rfl
        refine ⟨hNa N eN, ks, hR, hks, fun L mL s ⟨tag', l', negs', e', h⟩ => ?_⟩
        rw [List.mem_singleton] at mL; subst mL
        obtain ⟨-, e₂, e₃⟩ := tuple3_inj e'
        rw [← fieldsTerm_inj e₂] at h
        rcases h with h | ⟨N', mN', -⟩
        · exact names s h
        · rw [← list_inj e₃] at mN'; simp at mN'
      obtain ⟨hNa', ks, hR, hks, lnKS⟩ := hneg N eN
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ :=
        upd_dnf_negreq ef hn hv sv vne keep (.tuple #[.integer k, tag, fieldsTerm l]) fb _ hl (by simp) inB N hNa' ks hR hks lnKS A hA Ds hDs hat
      rw [← eN] at rY hY
      rw [conv inB] at hY mDm
      refine ⟨_, ?_, Or.inr ⟨T, Y, er, f, rfl, ⟨w₀, (sem w₀).mpr h₀⟩, Dm, mDm, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      simpa [Term.list] using rY
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N', mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 6) (by omega) rfl g sl
            (negs := []) (by simp) run w ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
      (m := n + 6) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    have hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
        Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) b =
          .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
        ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
      intro N eN
      obtain ⟨ks, hR, hks, litsQ⟩ := negInfo N eN
      obtain ⟨lines', rl', nl'⟩ := dnf_neg_names (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
        (m := n + 6) (by omega) _ (litsQ wb)
      have e : lines' = lines := list_inj (Except.ok.inj (rl'.symm.trans rl))
      subst e
      exact ⟨hNa N eN, ks, hR, hks, nl'⟩
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      · cases h : denMF E den b w
        · rfl
        · simpa using (inB w).mp h
    | cons L rest =>
      obtain ⟨hNa', ks, hR, hks, lnKS⟩ := hneg N eN
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ :=
        upd_dnf_negreq ef hn hv sv vne keep b fb (L :: rest) hl (by simp) inB N hNa' ks hR hks lnKS A hA Ds hDs hat
      rw [← eN] at rY hY
      rw [conv inB] at hY mDm
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨T, Y, er, f, rfl, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, Dm, mDm, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY

theorem del_update_static_req (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    {A Ds : List String} {neg : Term} {N : List (Term × Term)} (eN : neg = .map N)
    (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hat : "atom" ∈ Ds) (hA : ∀ s ∈ A, mapLookup N (.atom s) ≠ none)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
        (splitT (A.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ T Y er f, res = .tuple #[T, Y, er, f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨
              KindHeld (fun u => denMF E den b u = Bool.true) d)) ∧
            MapsY E den Y (fun w => UpdSemD den (fun u => denMF E den b u = Bool.true) [] neg Dm md w ∨
              ∃ a ∈ A, DelAt (fun u => denMF E den b u = Bool.true) md a w)) := by
  -- For negated sets, the keys outside the set, and the literals of the field naming only those or the set's.
  have negInfo : ∀ N, neg = .map N → ∃ ks : List String,
      Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) b =
        .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
      ∀ wb : Bdd (MLit E) b, Bdd (fun t => MLit E t ∧ LitIn (fun s => mapLookup N (.atom s) ≠ none ∨ s ∈ ks) t) b := by
    intro N _
    obtain ⟨R, rR, hR, -⟩ := neg_keys (den := den) ef N (n + 5) fb
    obtain ⟨ks, rfl⟩ : ∃ ks : List String, R = ks.map Term.atom := by
      clear rR
      induction R with
      | nil => exact ⟨[], rfl⟩
      | cons r rs ih =>
        obtain ⟨s, rfl, -⟩ := hR r List.mem_cons_self
        obtain ⟨B, rfl⟩ := ih fun x mx => hR x (List.mem_cons_of_mem _ mx)
        exact ⟨s :: B, rfl⟩
    refine ⟨ks, rR, fun s ms => ?_, fun wb => ?_⟩
    · obtain ⟨s', e, h⟩ := hR _ (List.mem_map_of_mem ms); cases e; exact h
    · obtain ⟨R', rR', -, lits, -⟩ := neg_keys_lits (den := den) ef N (n + 5) wb
      have e : R' = ks.map Term.atom := list_inj (Except.ok.inj (rR'.symm.trans rR))
      subst e
      exact lits.mono fun t ⟨lt, it⟩ => ⟨lt, fun k tag l et s ms => (it k tag l et s ms).imp id (by simp)⟩
  -- The semantics over the field.
  have conv : ∀ {lines : List Term}, (∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) →
      (fun u => ∃ L ∈ lines, InMLine den L u) = (fun u => denMF E den b u = Bool.true) := fun h =>
    funext fun u => propext (h u).symm
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 6)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 6) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 6) (by omega) rfl g sl
          (negs := []) (by simp) fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      have inB : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔
          ∃ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], InMLine den L w := fun w => by
        rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
      have hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
          Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N)
            (.tuple #[.integer k, tag, fieldsTerm l]) = .ok (Term.list (ks.map Term.atom)) ∧
          (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧ ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], ∀ s,
            LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
        intro N eN
        obtain ⟨ks, hR, hks, litsQ⟩ := negInfo N eN
        have names : ∀ s ∈ keyStrs l, mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
          rcases fb with ⟨k', e'⟩ | wb
          · intro s ms
            obtain ⟨-, -, e₃⟩ := tuple3_inj e'
            have : l = [] := fieldsTerm_inj (l' := []) e₃
            subst this; simp [keyStrs] at ms
          · exact (Bdd.leaf_iff.mp (litsQ wb)).2 k tag l rfl
        refine ⟨hNa N eN, ks, hR, hks, fun L mL s ⟨tag', l', negs', e', h⟩ => ?_⟩
        rw [List.mem_singleton] at mL; subst mL
        obtain ⟨-, e₂, e₃⟩ := tuple3_inj e'
        rw [← fieldsTerm_inj e₂] at h
        rcases h with h | ⟨N', mN', -⟩
        · exact names s h
        · rw [← list_inj e₃] at mN'; simp at mN'
      obtain ⟨hNa', ks, hR, hks, lnKS⟩ := hneg N eN
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ :=
        upd_dnf_negreq_del ef hn hmd (.tuple #[.integer k, tag, fieldsTerm l]) fb _ hl (by simp) inB N hNa' ks hR hks lnKS A hA Ds hDs hat
      rw [← eN] at rY hY
      rw [conv inB] at hY mDm
      refine ⟨_, ?_, Or.inr ⟨T, Y, er, f, rfl, ⟨w₀, (sem w₀).mpr h₀⟩, Dm, mDm, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      simpa [Term.list] using rY
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N', mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 6) (by omega) rfl g sl
            (negs := []) (by simp) run w ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
      (m := n + 6) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    have hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
        Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) b =
          .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
        ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
      intro N eN
      obtain ⟨ks, hR, hks, litsQ⟩ := negInfo N eN
      obtain ⟨lines', rl', nl'⟩ := dnf_neg_names (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
        (m := n + 6) (by omega) _ (litsQ wb)
      have e : lines' = lines := list_inj (Except.ok.inj (rl'.symm.trans rl))
      subst e
      exact ⟨hNa N eN, ks, hR, hks, nl'⟩
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      · cases h : denMF E den b w
        · rfl
        · simpa using (inB w).mp h
    | cons L rest =>
      obtain ⟨hNa', ks, hR, hks, lnKS⟩ := hneg N eN
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ :=
        upd_dnf_negreq_del ef hn hmd b fb (L :: rest) hl (by simp) inB N hNa' ks hR hks lnKS A hA Ds hDs hat
      rw [← eN] at rY hY
      rw [conv inB] at hY mDm
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨T, Y, er, f, rfl, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, Dm, mDm, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY

end


/-! Forced updates build the same maps whether they return the old values or not. -/

/-- `map_update_named_key/5` builds the same maps whether it reads the old values or not. -/
theorem named_key_ov (d : Dispatcher) (dnf key op bld ov₁ ov₂ : Term) {t₁ t₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov₁ = .ok t₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_named_key/5» d dnf key op bld ov₂ = .ok t₂) :
    ∃ bds o₁ o₂, t₁ = .tuple #[bds, o₁] ∧ t₂ = .tuple #[bds, o₂] := by
  unfold Elixir.Module.Types.Descr.«map_update_named_key/5» at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals (repeat' split at h₁) <;> (try (cases h₁; done))
  all_goals (repeat' split at h₂) <;> (try (simp at h₂; done))
  all_goals (try (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂))
  all_goals first
    | exact ⟨_, _, _, rfl, rfl⟩
    | trace_state

theorem named_step_relB2 (d : Dispatcher) (dnf op req₁ req₂ s₁ s₂ bld ov₁ ov₂ fo key : Term) {a b r₁ r₂ : Term}
    (hab : RelB a b)
    (h₁ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req₁ s₁ bld ov₁ fo key a = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req₂ s₂ bld ov₂ fo key b = .ok r₂) :
    RelB r₁ r₂ := by
  obtain ⟨v₁, bd, e₁, f₁, v₂, e₂, f₂, rfl, rfl⟩ := hab
  obtain ⟨bds, old, B, k₁, b₁, a, e, f, rfl⟩ := named_step_maps d dnf op req₁ s₁ bld ov₁ fo key h₁
  obtain ⟨bds', old', B', k₂, b₂, a', e', f', rfl⟩ := named_step_maps d dnf op req₂ s₂ bld ov₂ fo key h₂
  obtain ⟨c, o₁, o₂, e₁', e₂'⟩ := named_key_ov d dnf key op bld ov₁ ov₂ k₁ k₂
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e₁' e₂'
  obtain ⟨rfl, -⟩ := e₁'
  obtain ⟨rfl, -⟩ := e₂'
  rw [b₁] at b₂; cases b₂
  exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩

/-- `map_update_named_keys/8` gives the same maps whatever the keys' requirement, the static flag, and whether it reads
the old values. -/
theorem named_keys_relB2 (m : Nat) (dnf keys op bo req₁ req₂ s₁ s₂ rt₁ rt₂ : Term) {a b r₁ r₂ : Term}
    (hab : RelB a b)
    (h₁ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) a dnf keys op req₁ s₁ rt₁ bo = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) b dnf keys op req₂ s₂ rt₂ bo = .ok r₂) :
    RelB r₁ r₂ := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», bind, Except.bind, pure, Except.pure] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals (split at h₁ <;> (try (cases h₁; done)))
  all_goals (split at h₂ <;> (try (simp at h₂; done)))
  all_goals
    refine foldl_relP RelB _ (fun x a b a' b' hab e₁ e₂ => ?_) keys a b hab h₁ h₂
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure] at e₁ e₂
    exact named_step_relB2 _ _ _ _ _ _ _ _ _ _ _ _ hab e₁ e₂

theorem dnf_rt_relB_force (m : Nat) (bdd dnf Rk Ok neg Rd Od c st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rk, Ok, neg, Rd, Od]) (.tuple #[c, .atom "force"]) (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf
      (.tuple #[Rk, Ok, neg, Rd, Od]) (.tuple #[c, .atom "force"]) (.atom "false") st₂ = .ok r₂) : RelB r₁ r₂ := by
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h₁ h₂
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Erlang.erlang.«not/1», Lynx.Term.isMember,
    Lynx.Except.andAlso] at h₁ h₂
  simp only [bind, Except.bind] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  rename_i xo opt2 hopt
  -- The first run looks up the domains.
  obtain ⟨G, hG⟩ : ∃ G, Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf Rd (.map [])
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0 #[dnf, opt2, Rk]) =
      .ok G := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf Rd (.map [])
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0 #[dnf, opt2, Rk]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁, V₁, M₁, a₁, rfl, hg₁, -⟩ := gd_bool (m + 1) _ _ _ _ _ hG
  simp only [hG] at h₁
  obtain ⟨G', hG'⟩ : ∃ G', Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf Od a₁
      (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0 #[dnf, opt2, Rk]) =
      .ok G' := by
    cases h : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (m + 2)) dnf Od a₁
        (.atom "true") (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0 #[dnf, opt2, Rk]) with
    | error e => simp [h] at h₁
    | ok G => exact ⟨G, rfl⟩
  obtain ⟨g₁', V₁', M₁', a₁', rfl, hg₁', -⟩ := gd_bool (m + 1) _ _ _ _ _ hG'
  simp only [hG'] at h₁
  obtain ⟨E₁, hE⟩ : ∃ E₁, Erlang.lists.«map/2» (D (m + 2))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) = .ok E₁ := by
    cases h : Erlang.lists.«map/2» (D (m + 2))
        (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list M₁) with
    | error e => simp [h] at h₁
    | ok E => exact ⟨E, rfl⟩
  simp only [hE] at h₁
  obtain ⟨Dm, hDm⟩ : ∃ Dm, Erlang.erlang.«++/2» Rd Od = .ok Dm := by
    cases h : Erlang.erlang.«++/2» Rd Od with
    | error e => simp [h] at h₂
    | ok Dm => exact ⟨Dm, rfl⟩
  simp only [hDm] at h₁ h₂
  obtain ⟨F, hF, bF⟩ := orElse_boolT hg₁ hg₁'
  simp only [hF] at h₁
  have oT : Lynx.Except.orElse (.ok F) (.ok (.atom "true")) true = .ok (.atom "true") := by
    rcases bF with rfl | rfl <;> rfl
  simp only [oT] at h₁ h₂
  all_goals
    try simp only [
      Lynx.Except.tryWith] at h₁ h₂
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
    -- The found flags differ, but only end in the accumulators.
    split at h₁ <;> (try (cases h₁; done))
    split at h₂ <;> (try (simp at h₂; done))
    repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁ N₁
    split at h₁ <;> try (simp at h₁; done)
    rename_i n₁' N₁'
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂ N₂
    split at h₂ <;> try (simp at h₂; done)
    rename_i n₂' N₂'
    have R₁ := named_keys_relB2 (m + 1) (h₁ := N₁) (h₂ := N₂) (hab := relB_mk _ _ _ _ _ _ _)
    have R₂ := named_keys_relB2 (m + 1) (h₁ := N₁') (h₂ := N₂') (hab := R₁)
    obtain ⟨u₁, B, e₁, f₁, u₂, e₂, f₂, rfl, rfl⟩ := R₂
    try simp only at h₁ h₂
    split at h₁ <;> try (simp at h₁; done)
    rename_i U hU
    simp only [hU] at h₂
    split at h₁ <;> split at h₂ <;> simp only [Except.ok.injEq] at h₁ h₂ <;> subst h₁ h₂ <;>
      first | exact ⟨_, _, _, _, _, _, _, rfl, rfl⟩ | simp_all

theorem static_rt_rel_ne (m : Nat) (descr Rk Ok neg Rd Od c st₁ st₂ : Term) (hd : descr ≠ .atom "term") {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr (.tuple #[Rk, Ok, neg, Rd, Od])
      (.tuple #[c, .atom "force"]) (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr (.tuple #[Rk, Ok, neg, Rd, Od])
      (.tuple #[c, .atom "force"]) (.atom "false") st₂ = .ok r₂) :
    r₁ = r₂ ∨ RelB r₁ r₂ := by
  rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals first
    | (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂; exact Or.inl rfl)
    | exact Or.inr (dnf_rt_relB_force _ _ _ _ _ _ _ _ _ _ _ h₁ h₂)
    | exact absurd rfl hd
    | (split at h₁ <;> split at h₂ <;> simp_all)
    | trace_state

/-- Forcing, `map_update_static/5` gives the same maps whether it returns the old values or not. -/
theorem static_rt_rel (m : Nat) (descr Rk Ok neg Rd Od c st₁ st₂ : Term) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr (.tuple #[Rk, Ok, neg, Rd, Od])
      (.tuple #[c, .atom "force"]) (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr (.tuple #[Rk, Ok, neg, Rd, Od])
      (.tuple #[c, .atom "force"]) (.atom "false") st₂ = .ok r₂) :
    r₁ = r₂ ∨ RelB r₁ r₂ := by
  by_cases h : descr = .atom "term"
  · subst h
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
    simp only at h₁ h₂
    exact static_rt_rel_ne m _ _ _ _ _ _ _ _ _ (by simp) h₁ h₂
  · exact static_rt_rel_ne m descr _ _ _ _ _ _ _ _ h h₁ h₂


/-! The shapes of the splits of keys. -/

section
variable {V : Type}

/-- Splits of keys `map_update_static_dnf/6` reads like static ones: without a negated set, the required and optional
atoms and domains; with one and without atoms, the domains; or required atoms inside a negated set; with the keys
`KP`. -/
def GForm (s : Term) (KP : MKey → Prop) : Prop :=
  (∃ Rs Os Ds Ds' : List Term, s = .tuple #[Term.list Rs, Term.list Os, .atom "nil", Term.list Ds, Term.list Ds'] ∧
    SplitOk (Rs ++ Os) (.atom "nil") (Ds ++ Ds') ∧ ∀ κ, SplitKey (Rs ++ Os) (.atom "nil") (Ds ++ Ds') κ ↔ KP κ) ∨
  (∃ (N : List (Term × Term)) (Ds Ds' : List Term), s = .tuple #[.nil, .nil, .map N, Term.list Ds, Term.list Ds'] ∧
    SplitOk [] (.map N) (Ds ++ Ds') ∧ (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧
    ∀ κ, SplitKey [] (.map N) (Ds ++ Ds') κ ↔ KP κ) ∨
  (∃ (A : List String) (N : List (Term × Term)) (Ds Ds' : List Term),
    s = .tuple #[Term.list (A.map Term.atom), .nil, .map N, Term.list Ds, Term.list Ds'] ∧
    SplitOk [] (.map N) (Ds ++ Ds') ∧ (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧
    (∀ a ∈ A, mapLookup N (.atom a) ≠ none) ∧
    ∀ κ, ((∃ a ∈ A, κ = .atom a) ∨ SplitKey [] (.map N) (Ds ++ Ds') κ) ↔ KP κ)

end

section
variable {t : Term} {n : Nat}

theorem gsplit_form {X : List (Term × Term)} {Dy : Term} (gk : GC (level t n) (.map X))
    (hD : mapLookup X (.atom "dynamic") = some Dy)
    (aS : ∀ tag S, mapLookup X (.atom "atom") = some (.tuple #[.atom tag, .map S]) →
      (tag = "union" ∨ tag = "negation") → ASet S)
    (aD : ∀ Y, Dy = .map Y → ∀ tag S, mapLookup Y (.atom "atom") = some (.tuple #[.atom tag, .map S]) →
      (tag = "union" ∨ tag = "negation") → ASet S)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ s, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.map X) = .ok s ∧
      GForm s (KeyPt t n Dy) := by
  obtain ⟨tD, dS, incl⟩ : TC (level t n) Dy ∧ DE (level t n).E (.map (rmDyn X)) ∧
      ∀ q : TP (level t n), denD (.map X) q → denD Dy q := by
    rcases gk with tX | ⟨X', Dy', e, hD', tD, dS, incl⟩
    · rcases tX with h | ⟨X', e, sX'⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e
      rw [hD] at hD'; cases hD'
      exact ⟨tD, Or.inr ⟨_, rfl, dS⟩, incl⟩
  obtain ⟨Yd, dds, unf, dY, semY, rdd, hdds, hdat, hdk, aY⟩ := dyn_info tD aD hm
  obtain ⟨rds, rrd, hrds, hrat, hrk⟩ := dom_kinds dS hm
  have lX : mapLookup (rmDyn X) (.atom "atom") = mapLookup X (.atom "atom") := lookup_rmDyn_name X (by decide)
  obtain ⟨odds, rod, sod, ind⟩ := diff_atoms dds rds fun x mx => let ⟨s, _, e⟩ := hdds x mx; ⟨s, e⟩
  have rem : Erlang.maps.«remove/2» (.atom "dynamic") (.map X) = .ok (.map (rmDyn X)) := rfl
  -- Atoms and kinds of the static part are those of the dynamic part.
  have inclA : ∀ s, amemV (mapLookup X (.atom "atom")) (.atom s) = Bool.true →
      amemV (mapLookup Yd (.atom "atom")) (.atom s) = Bool.true := fun s h =>
    (denD_aPt (t := t) (n := n) (Y := Yd) _).mp ((semY _).mp (incl _ ((denD_aPt (t := t) (n := n) (Y := X) _).mpr h)))
  have keyA : ∀ s, KeyPt t n Dy (.atom s) ↔ amemV (mapLookup Yd (.atom "atom")) (.atom s) = Bool.true := fun s =>
    (semY _).trans (denD_aPt _)
  have inclK : ∀ k, Term.atom (domKind k) ∈ rds → Term.atom (domKind k) ∈ dds := fun k h => by
    obtain ⟨v, hv, pv⟩ := (hrk _ (domKind_ne_atom k)).mp h
    exact (hdk _ (domKind_ne_atom k)).mpr ⟨v, (semY v).mp (incl v ((denD_rmDyn X v).mp hv)), pv⟩
  have dsK : ∀ k i, Term.atom (domKind k) ∈ rds ++ odds ↔ KeyPt t n Dy (.dom k i) := fun k i => by
    have : KeyPt t n Dy (.dom k i) ↔ Term.atom (domKind k) ∈ dds :=
      ⟨fun ⟨v, hv, pv⟩ => (hdk _ (domKind_ne_atom k)).mpr ⟨v, (semY v).mp hv, pv⟩, fun h =>
        let ⟨v, hv, pv⟩ := (hdk _ (domKind_ne_atom k)).mp h; ⟨v, (semY v).mpr hv, pv⟩⟩
    rw [this, List.mem_append]
    constructor
    · rintro (h | h)
      · exact inclK k h
      · exact sod _ h
    · intro h
      by_cases r : Term.atom (domKind k) ∈ rds
      · exact Or.inl r
      · exact Or.inr (ind _ h r)
  have hds : ∀ d ∈ rds ++ odds, ∃ s ∈ domainKinds, d = .atom s := fun d md =>
    (List.mem_append.mp md).elim (hrds d) fun h => hdds d (sod d h)
  have datom : Term.atom "atom" ∈ rds ++ odds ↔ Term.atom "atom" ∈ rds ∨ Term.atom "atom" ∈ dds := by
    rw [List.mem_append]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (sod _ h)
    · rintro (h | h)
      · exact Or.inl h
      · by_cases r : Term.atom "atom" ∈ rds
        · exact Or.inl r
        · exact Or.inr (ind _ h r)
  -- Splits with the domains of the dynamic part.
  have single : ∀ rs neg, (∀ s, SplitKey rs neg (rds ++ odds) (.atom s) ↔
      amemV (mapLookup Yd (.atom "atom")) (.atom s) = Bool.true) →
      ∀ κ, (∃ sp ∈ [(rs, neg, rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
    intro rs neg h κ
    simp only [List.mem_singleton, exists_eq_left]
    cases κ with
    | atom s => exact (h s).trans (keyA s).symm
    | dom k i => exact dsK k i
  -- The shapes of the atoms.
  have shapeX : mapLookup X (.atom "atom") = none ∨ ∃ (pos : Bool) (S : List (Term × Term)), ASet S ∧
      mapLookup X (.atom "atom") = some (.tuple #[.atom (if pos then "union" else "negation"), .map S]) := by
    cases h : mapLookup X (.atom "atom") with
    | none => exact Or.inl rfl
    | some x =>
      obtain ⟨⟨pos, S, rfl, -⟩, -⟩ := fieldC_atom ((de_map dS).fields _ _ (lX.trans h))
      exact Or.inr ⟨pos, S, aS _ S h (by cases pos <;> simp), rfl⟩
  have shapeY : mapLookup Yd (.atom "atom") = none ∨ ∃ (pos : Bool) (S : List (Term × Term)), ASet S ∧
      mapLookup Yd (.atom "atom") = some (.tuple #[.atom (if pos then "union" else "negation"), .map S]) := by
    cases h : mapLookup Yd (.atom "atom") with
    | none => exact Or.inl rfl
    | some x =>
      obtain ⟨⟨pos, S, rfl, -⟩, -⟩ := fieldC_atom ((de_map dY).fields _ _ h)
      exact Or.inr ⟨pos, S, aY _ S h (by cases pos <;> simp), rfl⟩
  have noRat : mapLookup X (.atom "atom") = none ∨ (∃ S, mapLookup X (.atom "atom") =
      some (.tuple #[.atom "union", .map S])) → Term.atom "atom" ∉ rds := by
    rintro (h | ⟨S, h⟩) m
    · obtain ⟨S', h'⟩ := hrat.mp m; rw [lX, h] at h'; simp at h'
    · obtain ⟨S', h'⟩ := hrat.mp m; rw [lX, h] at h'; simp at h'
  have noDat : mapLookup Yd (.atom "atom") = none ∨ (∃ S, mapLookup Yd (.atom "atom") =
      some (.tuple #[.atom "union", .map S])) → Term.atom "atom" ∉ dds := by
    rintro (h | ⟨S, h⟩) m
    · obtain ⟨S', h'⟩ := hdat.mp m; rw [h] at h'; simp at h'
    · obtain ⟨S', h'⟩ := hdat.mp m; rw [h] at h'; simp at h'
  have aDs : ∀ d ∈ rds ++ odds, d = .atom "atom" → mapLookup X (.atom "atom") = none ∨
      (∃ S, mapLookup X (.atom "atom") = some (.tuple #[.atom "union", .map S])) →
      mapLookup Yd (.atom "atom") = none ∨ (∃ S, mapLookup Yd (.atom "atom") =
        some (.tuple #[.atom "union", .map S])) → False := by
    rintro d md rfl hx hy
    rcases datom.mp md with h | h
    · exact noRat hx h
    · exact noDat hy h
  -- Splits without a negated set, or with one, and their domains.
  have okNil : ∀ rs : List Term, (∀ r ∈ rs, ∃ s, r = .atom s) → Term.atom "atom" ∉ rds ++ odds →
      ∀ sp ∈ [(rs, Term.atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
    intro rs hrs na sp msp
    simp only [List.mem_singleton] at msp
    subst msp
    exact ⟨⟨hrs, Or.inl rfl, hds, ⟨fun h => absurd h na, fun ⟨N, e⟩ => nomatch e⟩⟩, fun N e => nomatch e⟩
  have okNeg : ∀ N, Term.atom "atom" ∈ rds ++ odds →
      ∀ sp ∈ [([], Term.map N, rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
    intro N ha sp msp
    simp only [List.mem_singleton] at msp
    subst msp
    exact ⟨⟨by simp, Or.inr ⟨N, rfl⟩, hds, ⟨fun _ => ⟨N, rfl⟩, fun _ => ha⟩⟩, fun _ _ => rfl⟩
  have atomsOf : ∀ A : List String, ∀ r ∈ A.map Term.atom, ∃ s, r = .atom s := fun A r mr => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp mr; exact ⟨s, rfl⟩
  have memA : ∀ (A : List String) (s : String), Term.atom s ∈ A.map Term.atom ↔ s ∈ A := fun A s => by simp
  rcases shapeX with hx | ⟨px, S, aSS, hx⟩ <;> rcases shapeY with hy | ⟨py, Dn, aDD, hy⟩
  · -- No atoms.
    have na : Term.atom "atom" ∉ rds ++ odds := fun m => (datom.mp m).elim (noRat (Or.inl hx)) (noDat (Or.inl hy))
    have hk : ∀ κ, (∃ sp ∈ [([] ++ [], .atom "nil", rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
        refine single _ _ fun s => ?_
        simp [SplitKey, hy, amemV]
    refine ⟨.tuple #[.nil, .nil, .atom "nil", Term.list rds, Term.list odds], ?_, Or.inl ⟨[], [], rds, odds, rfl, ?_, fun κ => by simpa using hk κ⟩⟩
    · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
      rcases unf with ⟨rfl, ut⟩ | rfl
      · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod]
      · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod]
    · have hok : ∀ sp ∈ [([] ++ [], .atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
        exact okNil _ (by simp) na
      simpa using (hok _ List.mem_cons_self).1
  · cases py <;> simp only [Bool.false_eq_true, ↓reduceIte] at hy
    · -- Atoms outside a dynamic negated set.
      have ha : Term.atom "atom" ∈ rds ++ odds := datom.mpr (Or.inr (hdat.mpr ⟨Dn, hy⟩))
      have hk : ∀ κ, (∃ sp ∈ [([], .map Dn, rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          simp [SplitKey, hy, amemV]
      refine ⟨.tuple #[.nil, .nil, .map Dn, Term.list rds, Term.list odds], ?_, Or.inr (Or.inl ⟨Dn, rds, odds, rfl, ?_, ?_, fun κ => by simpa using hk κ⟩)⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod]
      · have hok : ∀ sp ∈ [([], .map Dn, rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNeg Dn ha
        simpa using (hok _ List.mem_cons_self).1
      · have hna : ∀ N', Term.map Dn = .map N' → ∀ e ∈ mapEntries N', ∃ s, e.1 = .atom s := by
          exact fun N e => by cases e; exact aset_hNa aDD
        exact hna _ rfl
    · -- Dynamic atoms, optional.
      obtain ⟨Dl, rDl, mDl⟩ := aset_list aDD (D (m + 1))
      have na : Term.atom "atom" ∉ rds ++ odds := fun m =>
        (datom.mp m).elim (noRat (Or.inl hx)) (noDat (Or.inr ⟨Dn, hy⟩))
      have hk : ∀ κ, (∃ sp ∈ [([] ++ Dl.map Term.atom, .atom "nil", rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          simp [SplitKey, hy, amemV, mDl]
      refine ⟨.tuple #[.nil, Term.list (Dl.map Term.atom), .atom "nil", Term.list rds, Term.list odds], ?_, Or.inl ⟨[], Dl.map Term.atom, rds, odds, rfl, ?_, fun κ => by simpa using hk κ⟩⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rDl]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rDl]
      · have hok : ∀ sp ∈ [([] ++ Dl.map Term.atom, .atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNil _ (by simp) na
        simpa using (hok _ List.mem_cons_self).1
  · cases px <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx
    · -- A static negated set without dynamic atoms: impossible, as some atom outside it would be dynamic.
      obtain ⟨c, hc⟩ := fresh_str (keyStrs S)
      have := inclA c (by simp [hx, amemV, lookup_fresh' hc])
      simp [hy, amemV] at this
    · -- Static atoms without dynamic atoms: none, as they would be dynamic.
      obtain ⟨Sl, rSl, mSl⟩ := aset_list aSS (D (m + 1))
      have na : Term.atom "atom" ∉ rds ++ odds := fun m =>
        (datom.mp m).elim (noRat (Or.inr ⟨S, hx⟩)) (noDat (Or.inl hy))
      have hk : ∀ κ, (∃ sp ∈ [(Sl.map Term.atom ++ [], .atom "nil", rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          simp only [SplitKey, List.append_nil, memA, mSl, hy, amemV]
          constructor
          · rintro (h | ⟨N, e, -⟩)
            · have := inclA s (by simpa [hx, amemV] using h)
              simp [hy, amemV] at this
            · cases e
          · intro h; cases h
      refine ⟨.tuple #[Term.list (Sl.map Term.atom), .nil, .atom "nil", Term.list rds, Term.list odds], ?_, Or.inl ⟨Sl.map Term.atom, [], rds, odds, rfl, ?_, fun κ => by simpa using hk κ⟩⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rSl]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rSl]
      · have hok : ∀ sp ∈ [(Sl.map Term.atom ++ [], .atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNil _ (by simp) na
        simpa using (hok _ List.mem_cons_self).1
  · cases px <;> cases py <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx hy
    · -- Both negated: the atoms outside both sets.
      obtain ⟨R, rR, aR, mR⟩ := aset_inter aDD aSS
      have ha : Term.atom "atom" ∈ rds ++ odds := datom.mpr (Or.inr (hdat.mpr ⟨Dn, hy⟩))
      have hk : ∀ κ, (∃ sp ∈ [([], .map R, rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          have i := inclA s
          simp only [hx, hy, amemV, Bool.not_eq_true'] at i
          simp only [SplitKey, List.not_mem_nil, false_or, hy, amemV, Bool.not_eq_true']
          constructor
          · rintro ⟨N, e, h⟩
            cases e
            have := mR (.atom s)
            rw [h] at this
            cases hd : (mapLookup Dn (.atom s)).isSome
            · rfl
            · cases hs : (mapLookup S (.atom s)).isSome
              · have := i (by simpa using hs); simp [hd] at this
              · simp [hd, hs] at this
          · intro h
            refine ⟨R, rfl, ?_⟩
            have := mR (.atom s)
            cases hR : mapLookup R (.atom s)
            · rfl
            · rw [hR] at this; simp [h] at this
      refine ⟨.tuple #[.nil, .nil, .map R, Term.list rds, Term.list odds], ?_, Or.inr (Or.inl ⟨R, rds, odds, rfl, ?_, ?_, fun κ => by simpa using hk κ⟩)⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rR]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rR]
      · have hok : ∀ sp ∈ [([], .map R, rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNeg R ha
        simpa using (hok _ List.mem_cons_self).1
      · have hna : ∀ N', Term.map R = .map N' → ∀ e ∈ mapEntries N', ∃ s, e.1 = .atom s := by
          exact fun N e => by cases e; exact aset_hNa aR
        exact hna _ rfl
    · -- A static negated set with dynamic atoms: impossible, as some atom outside both would be dynamic.
      obtain ⟨c, hc⟩ := fresh_str (keyStrs S ++ keyStrs Dn)
      have := inclA c (by simp [hx, amemV, lookup_fresh' (fun m => hc (List.mem_append_left _ m))])
      simp [hy, amemV, lookup_fresh' (fun m => hc (List.mem_append_right _ m))] at this
    · -- Static atoms and a dynamic negated set: the static atoms, and the atoms outside both.
      obtain ⟨Sl, rSl, mSl⟩ := aset_list aSS (D (m + 1))
      obtain ⟨R, rR, aR, mR⟩ := aset_union aDD aSS
      have ha : Term.atom "atom" ∈ rds ++ odds := datom.mpr (Or.inr (hdat.mpr ⟨Dn, hy⟩))
      have hA : ∀ a ∈ Sl, mapLookup R (.atom a) ≠ none := fun a ma => by
        have := mR (.atom a)
        rw [(mSl a).mp ma, Bool.or_true] at this
        exact Option.isSome_iff_ne_none.mp this
      have hk : ∀ κ, (∃ sp ∈ [(Sl.map Term.atom, .atom "nil", []), ([], .map R, rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          intro κ
          simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
          cases κ with
          | atom s =>
            rw [keyA]
            have i := inclA s
            simp only [hx, hy, amemV, Bool.not_eq_true'] at i
            simp only [SplitKey, memA, mSl, List.not_mem_nil, false_or, hy, amemV, Bool.not_eq_true']
            constructor
            · rintro ((h | ⟨N, e, -⟩) | ⟨N, e, h⟩)
              · exact i h
              · cases e
              · cases e
                have := mR (.atom s)
                rw [h] at this
                cases hd : (mapLookup Dn (.atom s)).isSome
                · rfl
                · simp [hd] at this
            · intro h
              by_cases hs : (mapLookup S (.atom s)).isSome = Bool.true
              · exact Or.inl (Or.inl hs)
              · refine Or.inr ⟨R, rfl, ?_⟩
                have := mR (.atom s)
                simp only [h, Bool.false_or] at this
                simp only [Bool.not_eq_true] at hs
                rw [hs] at this
                cases hR : mapLookup R (.atom s)
                · rfl
                · rw [hR] at this; cases this
          | dom k i =>
            simp only [SplitKey, List.not_mem_nil, false_or]
            exact dsK k i
      refine ⟨.tuple #[Term.list (Sl.map Term.atom), .nil, .map R, Term.list rds, Term.list odds], ?_, Or.inr (Or.inr ⟨Sl, R, rds, odds, rfl, ?_, ?_, hA, fun κ => ?_⟩)⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rSl, rR]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rSl, rR]
      · have hok : ∀ sp ∈ [(Sl.map Term.atom, .atom "nil", []), ([], .map R, rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          intro sp msp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at msp
          rcases msp with rfl | rfl
          · exact ⟨⟨atomsOf Sl, Or.inl rfl, by simp, ⟨by simp, fun ⟨N, e⟩ => nomatch e⟩⟩, fun N e => nomatch e⟩
          · exact (okNeg R ha _ List.mem_cons_self)
        simpa using (hok _ (List.mem_cons_of_mem _ List.mem_cons_self)).1
      · have hna : ∀ N', Term.map R = .map N' → ∀ e ∈ mapEntries N', ∃ s, e.1 = .atom s := by
          exact fun N e => by cases e; exact aset_hNa aR
        exact hna _ rfl
      · rw [← hk κ]
        cases κ <;> simp [SplitKey]
    · -- Static and dynamic atoms: the static ones, and the dynamic ones they miss.
      obtain ⟨Sl, rSl, mSl⟩ := aset_list aSS (D (m + 1))
      obtain ⟨R, rR, aR, mR⟩ := aset_sub aDD aSS
      obtain ⟨Rl, rRl, mRl⟩ := aset_list aR (D (m + 1))
      have na : Term.atom "atom" ∉ rds ++ odds := fun m =>
        (datom.mp m).elim (noRat (Or.inr ⟨S, hx⟩)) (noDat (Or.inr ⟨Dn, hy⟩))
      have hrs : ∀ r ∈ Sl.map Term.atom ++ Rl.map Term.atom, ∃ s, r = .atom s := fun r mr =>
        (List.mem_append.mp mr).elim (atomsOf Sl r) (atomsOf Rl r)
      have hk : ∀ κ, (∃ sp ∈ [(Sl.map Term.atom ++ Rl.map Term.atom, .atom "nil", rds ++ odds)], SplitKey sp.1 sp.2.1 sp.2.2 κ) ↔ KeyPt t n Dy κ := by
          refine single _ _ fun s => ?_
          have i := inclA s
          simp only [hx, hy, amemV] at i
          simp only [SplitKey, List.mem_append, memA, mSl, mRl, mR, hy, amemV]
          constructor
          · rintro ((h | h) | ⟨N, e, -⟩)
            · exact i h
            · exact (Bool.and_eq_true_iff.mp h).1
            · cases e
          · intro h
            by_cases hs : (mapLookup S (.atom s)).isSome = Bool.true
            · exact Or.inl (Or.inl hs)
            · exact Or.inl (Or.inr (by simp [h, hs]))

      refine ⟨.tuple #[Term.list (Sl.map Term.atom), Term.list (Rl.map Term.atom), .atom "nil", Term.list rds, Term.list odds], ?_, Or.inl ⟨Sl.map Term.atom, Rl.map Term.atom, rds, odds, rfl, ?_, fun κ => by simpa using hk κ⟩⟩
      · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
        rcases unf with ⟨rfl, ut⟩ | rfl
        · simp [getMapKeys_single, hD, ut, hx, hy, rem, rrd, rdd, rod, rSl, rR, rRl]
        · simp [getMapKeys_single, hD, hx, hy, rem, rrd, rdd, rod, rSl, rR, rRl]
      · have hok : ∀ sp ∈ [(Sl.map Term.atom ++ Rl.map Term.atom, .atom "nil", rds ++ odds)], SplitOk sp.1 sp.2.1 sp.2.2 ∧ ∀ N, sp.2.1 = .map N → sp.1 = [] := by
          exact okNil _ hrs na
        simpa using (hok _ List.mem_cons_self).1

end


/-! The maps of updates at keys of the shapes, as those of static splits. -/

section
variable {t : Term} {n : Nat}

/-- Static keys split in one of the shapes. -/
theorem static_gform {k : Term} (hk : DE (level t n).E k)
    (hU : ∀ Y, k = .map Y → ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s)
    (hNeg : ∀ Y, k = .map Y → ∀ S, mapLookup Y (.atom "atom") = some (.tuple #[.atom "negation", .map S]) →
      ∀ e ∈ mapEntries S, ∃ s, e.1 = .atom s)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ s, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) k = .ok s ∧ GForm s (KeyPt t n k) := by
  obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ := key_split_any hk hU hNeg hm
  refine ⟨_, rk, ?_⟩
  rcases ok.hneg with rfl | ⟨N, rfl⟩
  · exact Or.inl ⟨rs, [], ds, [], by simp [splitT, Term.list], by simpa using ok, fun κ => by simpa using sk κ⟩
  · obtain rfl := nr N rfl
    exact Or.inr (Or.inl ⟨N, ds, [], by simp [splitT, Term.list], by simpa using ok, na N rfl,
      fun κ => by simpa using sk κ⟩)

end

/-- Static splits: of atoms, of the atoms outside a negated set, or of required atoms inside one, with keys `KP`. -/
def SForm (s : Term) (KP : MKey → Prop) : Prop :=
  (∃ rs Ds : List Term, s = splitT rs (.atom "nil") Ds ∧ SplitOk rs (.atom "nil") Ds ∧
    ∀ κ, SplitKey rs (.atom "nil") Ds κ ↔ KP κ) ∨
  (∃ (N : List (Term × Term)) (Ds : List Term), s = splitT [] (.map N) Ds ∧ SplitOk [] (.map N) Ds ∧
    (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∀ κ, SplitKey [] (.map N) Ds κ ↔ KP κ) ∨
  (∃ (A : List String) (N : List (Term × Term)) (Ds : List Term), s = splitT (A.map Term.atom) (.map N) Ds ∧
    SplitOk [] (.map N) Ds ∧ (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ (∀ a ∈ A, mapLookup N (.atom a) ≠ none) ∧
    ∀ κ, ((∃ a ∈ A, κ = .atom a) ∨ SplitKey [] (.map N) Ds κ) ↔ KP κ)

theorem splitOk_swap {rs : List Term} {neg : Term} {A B : List Term} (h : SplitOk rs neg (A ++ B)) :
    SplitOk rs neg (B ++ A) :=
  ⟨h.hrs, h.hneg, fun d md => h.hds d (List.mem_append.mpr (List.mem_append.mp md).symm),
    ⟨fun m => h.hatom.mp (List.mem_append.mpr (List.mem_append.mp m).symm),
     fun e => List.mem_append.mpr (List.mem_append.mp (h.hatom.mpr e)).symm⟩⟩

theorem splitKey_swap {rs : List Term} {neg : Term} {A B : List Term} (κ : MKey) :
    SplitKey rs neg (B ++ A) κ ↔ SplitKey rs neg (A ++ B) κ := by
  cases κ <;> simp [SplitKey, or_comm]

/-- Splits of the shapes update with the maps of static splits. -/
theorem dnf_gform_relB {s : Term} {KP : MKey → Prop} (hs : GForm s KP) (md : String) (hmd : Mode md) :
    ∃ s', SForm s' KP ∧ ∀ (m : Nat) (bdd dnf c st₁ st₂ : Term) {r₁ r₂ : Term},
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s (.tuple #[c, .atom md])
        (.atom "true") st₁ = .ok r₁ →
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s' (.tuple #[c, .atom md])
        (.atom "true") st₂ = .ok r₂ → RelB r₁ r₂ := by
  have sel : ∀ (Ds Ds' : List Term), ∃ L : List Term, (L = Ds ++ Ds' ∨ L = Ds' ++ Ds) ∧
      (md = "reject" → L = Ds' ++ Ds) ∧ (md ≠ "reject" → L = Ds ++ Ds') := fun Ds Ds' => by
    by_cases h : md = "reject"
    · exact ⟨Ds' ++ Ds, Or.inr rfl, fun _ => rfl, fun h' => absurd h h'⟩
    · exact ⟨Ds ++ Ds', Or.inl rfl, fun h' => absurd h' h, fun _ => rfl⟩
  have okL : ∀ {rs neg} {Ds Ds' L : List Term}, (L = Ds ++ Ds' ∨ L = Ds' ++ Ds) → SplitOk rs neg (Ds ++ Ds') →
      SplitOk rs neg L := fun hL ok => by rcases hL with rfl | rfl; exact ok; exact splitOk_swap ok
  have keyL : ∀ {rs neg} {Ds Ds' L : List Term}, (L = Ds ++ Ds' ∨ L = Ds' ++ Ds) → ∀ κ,
      SplitKey rs neg L κ ↔ SplitKey rs neg (Ds ++ Ds') κ := fun hL κ => by
    rcases hL with rfl | rfl; exact Iff.rfl; exact splitKey_swap κ
  rcases hs with ⟨Rs, Os, Ds, Ds', rfl, ok, sk⟩ | ⟨N, Ds, Ds', rfl, ok, na, sk⟩ | ⟨A, N, Ds, Ds', rfl, ok, na, hA, sk⟩
  · obtain ⟨L, hL, hr, hn⟩ := sel Ds Ds'
    refine ⟨splitT (Rs ++ Os) (.atom "nil") L, Or.inl ⟨_, L, rfl, okL hL ok, fun κ => (keyL hL κ).trans (sk κ)⟩, ?_⟩
    intro m bdd dnf c st₁ st₂ r₁ r₂ h₁ h₂
    refine dnf_opt_relB m bdd dnf Rs Os Ds Ds' c md hmd st₁ st₂ h₁ ?_
    by_cases h : md = "reject"
    · rw [ite_eq_left h, ← hr h]; exact h₂
    · rw [ite_eq_right h, ← hn h]; exact h₂
  · obtain ⟨L, hL, hr, hn⟩ := sel Ds Ds'
    refine ⟨splitT [] (.map N) L, Or.inr (Or.inl ⟨N, L, rfl, okL hL ok, na, fun κ => (keyL hL κ).trans (sk κ)⟩), ?_⟩
    intro m bdd dnf c st₁ st₂ r₁ r₂ h₁ h₂
    rcases hmd with rfl | rfl | rfl
    · exact dnf_neg_relB_force m bdd dnf .nil N Ds Ds' c st₁ st₂ h₁ (by rw [← hn (by decide)] at *; exact h₂)
    · exact dnf_neg_relB_keep m bdd dnf .nil N Ds Ds' c st₁ st₂ h₁ (by rw [← hn (by decide)] at *; exact h₂)
    · exact dnf_neg_relB_reject m bdd dnf .nil N Ds Ds' c st₁ st₂ h₁ (by rw [← hr rfl] at *; exact h₂)
  · obtain ⟨L, hL, hr, hn⟩ := sel Ds Ds'
    refine ⟨splitT (A.map Term.atom) (.map N) L, Or.inr (Or.inr ⟨A, N, L, rfl, okL hL ok, na, hA,
      fun κ => (or_congr_right (keyL hL κ)).trans (sk κ)⟩), ?_⟩
    intro m bdd dnf c st₁ st₂ r₁ r₂ h₁ h₂
    rcases hmd with rfl | rfl | rfl
    · exact dnf_neg_relB_force m bdd dnf _ N Ds Ds' c st₁ st₂ h₁ (by rw [← hn (by decide)] at *; exact h₂)
    · exact dnf_neg_relB_keep m bdd dnf _ N Ds Ds' c st₁ st₂ h₁ (by rw [← hn (by decide)] at *; exact h₂)
    · exact dnf_neg_relB_reject m bdd dnf _ N Ds Ds' c st₁ st₂ h₁ (by rw [← hr rfl] at *; exact h₂)

theorem static_split_rel_ne (m : Nat) (descr s s' op st₁ st₂ : Term) (hd : descr ≠ .atom "term")
    (HR : ∀ bdd dnf {r₁ r₂ : Term},
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s op (.atom "true") st₁ = .ok r₁ →
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s' op (.atom "true") st₂ = .ok r₂ →
      RelB r₁ r₂) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr s op (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr s' op (.atom "true") st₂ = .ok r₂) :
    r₁ = r₂ ∨ RelB r₁ r₂ := by
  rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
  simp only [bind, Except.bind, Lynx.Except.guard, pure, Except.pure,
    Lynx.Except.tryWith] at h₁ h₂
  repeat' (split at h₁ <;> (try (cases h₁; done)) <;> (revert h₁; simp only [*] at h₂; intro h₁))
  all_goals first
    | (simp only [Except.ok.injEq] at h₁ h₂; subst h₁ h₂; exact Or.inl rfl)
    | exact Or.inr (HR _ _ h₁ h₂)
    | exact absurd rfl hd
    | (split at h₁ <;> split at h₂ <;> simp_all)
    | trace_state

/-- `map_update_static/5` on splits updating with the same maps gives the same maps. -/
theorem static_split_rel (m : Nat) (descr s s' op st₁ st₂ : Term)
    (HR : ∀ bdd dnf {r₁ r₂ : Term},
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s op (.atom "true") st₁ = .ok r₁ →
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 2)) bdd dnf s' op (.atom "true") st₂ = .ok r₂ →
      RelB r₁ r₂) {r₁ r₂ : Term}
    (h₁ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr s op (.atom "true") st₁ = .ok r₁)
    (h₂ : Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 2)) descr s' op (.atom "true") st₂ = .ok r₂) :
    r₁ = r₂ ∨ RelB r₁ r₂ := by
  by_cases h : descr = .atom "term"
  · subst h
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at h₁ h₂
    simp only at h₁ h₂
    exact static_split_rel_ne m _ s s' op st₁ st₂ (by simp) HR h₁ h₂
  · exact static_split_rel_ne m descr s s' op st₁ st₂ h HR h₁ h₂

section
variable {t : Term} {n : Nat}

/-- The maps an update with a key of keys `KP` may give: those of some static split of keys in `KP`. -/
def KRSem (t : Term) (n : Nat) (X : List (Term × Term)) (KP : MKey → Prop) (v : Term) (keep : Bool)
    (w : MW (level t n).V) : Prop :=
  ∃ (rs Ds Dm : List String) (neg : Term), SplitOk (rs.map Term.atom) neg (Ds.map Term.atom) ∧
    (∀ N, neg = .map N → rs = []) ∧ (∀ κ, SplitKey (rs.map Term.atom) neg (Ds.map Term.atom) κ → KP κ) ∧
    (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨ KindHeld (MT t n X) d)) ∧
    UpdSemKR (level t n).den (MT t n X) rs neg Dm v keep w

theorem strs_of {l : List Term} (h : ∀ r ∈ l, ∃ s, r = .atom s) : ∃ A : List String, l = A.map Term.atom :=
  atoms_of h

theorem ds_of {l : List Term} (h : ∀ d ∈ l, ∃ s ∈ domainKinds, d = .atom s) :
    ∃ A : List String, l = A.map Term.atom ∧ ∀ s ∈ A, s ∈ domainKinds := by
  obtain ⟨A, rfl⟩ := atoms_of fun d md => let ⟨s, _, e⟩ := h d md; ⟨s, e⟩
  refine ⟨A, rfl, fun s ms => ?_⟩
  obtain ⟨s', ms', e⟩ := h _ (List.mem_map_of_mem ms)
  cases e; exact ms'

/-- `:keep` and `:reject` of a static value at a key of the shapes, on a static map type, for either flag. -/
theorem kr_gsem {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {s : Term} {KP : MKey → Prop}
    (hs : GForm s KP) {v : Term} (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z)
    (vne : ∃ x, (level t n).den v x) (keep : Bool) (st : Term) {m : Nat} (hm : (level t n).K + 30 ≤ m)
    {T Y er f : Term}
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) s (keepOp v keep) (.atom "true") st =
      .ok (.tuple #[T, Y, er, f])) :
    ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → KRSem t n X KP v keep w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  have hmd : Mode (if keep then "keep" else "reject") := by cases keep <;> simp [Mode]
  have eop : keepOp v keep = .tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]],
      .atom (if keep then "keep" else "reject")] := rfl
  obtain ⟨s', hs', HR⟩ := dnf_gform_relB hs _ hmd
  have conv : ∀ {b : Term}, mapLookup X (.atom "map") = some b →
      (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X := fun hb =>
    funext fun u => propext (by simp [MT, hb])
  -- No map field: no maps.
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  -- The static split.
  have rel := fun {r} (h : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) (.map X) s' (keepOp v keep)
      (.atom "true") (.atom "true") = .ok r) => static_split_rel (k + 6) (.map X) s s' (keepOp v keep) st (.atom "true")
        (fun bdd dnf r₁ r₂ h₁ h₂ => HR (k + 6) bdd dnf _ st (.atom "true") (by rw [eop] at h₁; exact h₁)
          (by rw [eop] at h₂; exact h₂)) run h
  have toY : ∀ {r Yr : Term} {S S' : MW (level t n).V → Prop}, (.tuple #[T, Y, er, f] = r ∨ RelB (.tuple #[T, Y, er, f]) r) →
      (∃ T' er' f', r = .tuple #[T', Yr, er', f']) → MapsY (level t n).E (level t n).den Yr S → (∀ w, S w → S' w) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → S' w := by
    rintro r Yr S S' hr ⟨T', er', f', rfl⟩ hY hS
    have eY : Yr = Y := by
      rcases hr with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e; exact e.2.1.symm
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂; rw [e₂.2.1, ← e₁.2.1]
    subst eY
    rcases hY with ⟨rfl, emp⟩ | ⟨r', rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun w h => ?_⟩
      obtain ⟨b', hb', h'⟩ := h
      simp [mapLookup] at hb'; subst hb'
      exact hS w ((sr w).mp h')
  rcases hs' with ⟨rs, Ds, rfl, ok, sk⟩ | ⟨N, Ds, rfl, ok, na, sk⟩ | ⟨A, N, Ds, rfl, ok, na, hA, sk⟩
  · obtain ⟨rs', rfl⟩ := strs_of ok.hrs
    obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      kr_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv vne keep ok (fun N e => nomatch e)
        (fun N e => nomatch e) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ⟨rs', Ds', Dm, .atom "nil", ok, (fun N e => nomatch e),
        fun κ h' => (sk κ).mp h', mDm, h⟩)
  · obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      kr_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv vne keep (rk := []) ok (fun _ _ => rfl)
        (fun N' e => by cases e; exact na) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ⟨[], Ds', Dm, .map N, ok, fun _ _ => rfl,
        fun κ h' => (sk κ).mp h', mDm, h⟩)
  · obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    have hat : "atom" ∈ Ds' := by
      obtain ⟨s, ms, e⟩ := List.mem_map.mp (ok.hatom.mpr ⟨N, rfl⟩); cases e; exact ms
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      kr_update_static_req ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv vne keep rfl hDs hat hA
        (fun N' e => by cases e; exact na) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      refine toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ?_)
      rcases h with h | ⟨a, ma, h⟩
      · exact ⟨[], Ds', Dm, .map N, ok, fun _ _ => rfl, fun κ h' => (sk κ).mp (Or.inr h'), mDm, h⟩
      · refine ⟨A, [], [], .atom "nil", ⟨fun r mr => by obtain ⟨s, -, rfl⟩ := List.mem_map.mp mr; exact ⟨s, rfl⟩,
          Or.inl rfl, by simp, ⟨by simp, fun ⟨N, e⟩ => nomatch e⟩⟩, (fun N e => nomatch e), fun κ h' => ?_,
          fun d => by simp, Or.inl ⟨rfl, Or.inl ⟨a, ma, h⟩⟩⟩
        cases κ with
        | atom s' => rcases h' with h' | ⟨N, e, -⟩
                     · obtain ⟨a', ma', e⟩ := List.mem_map.mp h'; exact (sk _).mp (Or.inl ⟨a', ma', by injection e with e; rw [e]⟩)
                     · cases e
        | dom k' i => simp [SplitKey] at h'


/-- The maps a delete with a key of keys `KP` may give: those of some static split of keys in `KP`. -/
def DelGSem (t : Term) (n : Nat) (X : List (Term × Term)) (KP : MKey → Prop) (md : String)
    (w : MW (level t n).V) : Prop :=
  ∃ (rs Ds Dm : List String) (neg : Term), SplitOk (rs.map Term.atom) neg (Ds.map Term.atom) ∧
    (∀ N, neg = .map N → rs = []) ∧ (∀ κ, SplitKey (rs.map Term.atom) neg (Ds.map Term.atom) κ → KP κ) ∧
    (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld (MT t n X) d)) ∧
    UpdSemD (level t n).den (MT t n X) rs neg Dm md w

/-- Deleting a key of the shapes, on a static map type, for either flag. -/
theorem del_gsem {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {s : Term} {KP : MKey → Prop}
    (hs : GForm s KP) {md : String} (hmd : Mode md) (st : Term) {m : Nat} (hm : (level t n).K + 30 ≤ m)
    {T Y er f : Term}
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) s (cOp (.map []) Bool.true md) (.atom "true") st =
      .ok (.tuple #[T, Y, er, f])) :
    ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → DelGSem t n X KP md w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  have eop : cOp (.map []) Bool.true md = .tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]],
      .atom md] := rfl
  obtain ⟨s', hs', HR⟩ := dnf_gform_relB hs _ hmd
  have conv : ∀ {b : Term}, mapLookup X (.atom "map") = some b →
      (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X := fun hb =>
    funext fun u => propext (by simp [MT, hb])
  -- No map field: no maps.
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  -- The static split.
  have rel := fun {r} (h : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) (.map X) s' (cOp (.map []) Bool.true md)
      (.atom "true") (.atom "true") = .ok r) => static_split_rel (k + 6) (.map X) s s' (cOp (.map []) Bool.true md) st (.atom "true")
        (fun bdd dnf r₁ r₂ h₁ h₂ => HR (k + 6) bdd dnf _ st (.atom "true") (by rw [eop] at h₁; exact h₁)
          (by rw [eop] at h₂; exact h₂)) run h
  have toY : ∀ {r Yr : Term} {S S' : MW (level t n).V → Prop}, (.tuple #[T, Y, er, f] = r ∨ RelB (.tuple #[T, Y, er, f]) r) →
      (∃ T' er' f', r = .tuple #[T', Yr, er', f']) → MapsY (level t n).E (level t n).den Yr S → (∀ w, S w → S' w) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → S' w := by
    rintro r Yr S S' hr ⟨T', er', f', rfl⟩ hY hS
    have eY : Yr = Y := by
      rcases hr with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e; exact e.2.1.symm
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂; rw [e₂.2.1, ← e₁.2.1]
    subst eY
    rcases hY with ⟨rfl, emp⟩ | ⟨r', rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun w h => ?_⟩
      obtain ⟨b', hb', h'⟩ := h
      simp [mapLookup] at hb'; subst hb'
      exact hS w ((sr w).mp h')
  rcases hs' with ⟨rs, Ds, rfl, ok, sk⟩ | ⟨N, Ds, rfl, ok, na, sk⟩ | ⟨A, N, Ds, rfl, ok, na, hA, sk⟩
  · obtain ⟨rs', rfl⟩ := strs_of ok.hrs
    obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      del_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hmd ok (fun N e => nomatch e)
        (fun N e => nomatch e) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ⟨rs', Ds', Dm, .atom "nil", ok, (fun N e => nomatch e),
        fun κ h' => (sk κ).mp h', mDm, h⟩)
  · obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      del_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hmd (rk := []) ok (fun _ _ => rfl)
        (fun N' e => by cases e; exact na) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ⟨[], Ds', Dm, .map N, ok, fun _ _ => rfl,
        fun κ h' => (sk κ).mp h', mDm, h⟩)
  · obtain ⟨Ds', rfl, hDs⟩ := ds_of ok.hds
    have hat : "atom" ∈ Ds' := by
      obtain ⟨s, ms, e⟩ := List.mem_map.mp (ok.hatom.mpr ⟨N, rfl⟩); cases e; exact ms
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      del_update_static_req ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hmd rfl hDs hat hA
        (fun N' e => by cases e; exact na) hb fb
    · rcases rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      refine toY (rel (by rw [show k + 2 + 6 = k + 8 by omega] at rr; exact rr)) ⟨_, _, _, rfl⟩ hY (fun w h => ?_)
      rcases h with h | ⟨a, ma, h⟩
      · exact ⟨[], Ds', Dm, .map N, ok, fun _ _ => rfl, fun κ h' => (sk κ).mp (Or.inr h'), mDm, h⟩
      · refine ⟨A, [], [], .atom "nil", ⟨fun r mr => by obtain ⟨s, -, rfl⟩ := List.mem_map.mp mr; exact ⟨s, rfl⟩,
          Or.inl rfl, by simp, ⟨by simp, fun ⟨N, e⟩ => nomatch e⟩⟩, (fun N e => nomatch e), fun κ h' => ?_,
          fun d => by simp, Or.inl ⟨rfl, Or.inl ⟨a, ma, h⟩⟩⟩
        cases κ with
        | atom s' => rcases h' with h' | ⟨N, e, -⟩
                     · obtain ⟨a', ma', e⟩ := List.mem_map.mp h'; exact (sk _).mp (Or.inl ⟨a', ma', by injection e with e; rw [e]⟩)
                     · cases e
        | dom k' i => simp [SplitKey] at h'

end


section
variable {t : Term} {n : Nat}

/-- `map_split_keys_and_domains/1` on a gradual key type of the laws: a split of the shapes, with the keys of the upper
bound. -/
theorem key_gform {k : Term} {m : Nat} (hm : (level t n).K + 23 ≤ m)
    (h : «arrows_gradual?/2» (D (m + 1)) k (.tuple #[.integer n, t]) = .ok (.atom "true")) :
    ∃ s, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) k = .ok s ∧
      GForm s (KeyPt t n (upper k)) := by
  have static : «arrows_static?/2» k (.tuple #[.integer n, t]) = .ok (.atom "true") → ∃ s,
      Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) k = .ok s ∧
      GForm s (KeyPt t n (upper k)) := by
    intro hs
    have dk := arrows_static_ok hs
    rw [upper_tc dk]
    exact static_gform dk (fun Y e => by subst e; exact static_union_atoms hs)
      (fun Y e => by subst e; exact static_negation_atoms hs) hm
  have gk := arrows_gradual_gc (t := t) (n := n) (m := m + 1) (by omega) k (by simpa [Term.true] using h)
  unfold «arrows_gradual?/2» at h
  cases k with
  | map X =>
    cases hD : mapLookup X (.atom "dynamic") with
    | none => simp [getMapKeys_single, hD] at h; exact static h
    | some Dy =>
      simp only [getMapKeys_single, hD, Option.toList, Erlang.maps.«remove/2», Lynx.Except.ok_bind,
        Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨hS, hDy⟩, -⟩ := h
      rw [← rmDyn] at hS
      have lX : mapLookup (rmDyn X) (.atom "atom") = mapLookup X (.atom "atom") := lookup_rmDyn_name X (by decide)
      rw [upper_dyn hD]
      exact gsplit_form gk hD (fun tag S e ht => static_atom_set hS tag S (lX.trans e) ht)
        (fun Y e tag S e' ht => by subst e; exact static_atom_set hDy tag S e' ht) hm
  | _ => simp at h; exact static h

/-- Forcing a static value at a split putting with `P`, on a static map type, for either flag, asking for the old
values: the maps the puts give. -/
theorem force_gsem {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {Rk Ok neg' Rd Od neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts (.tuple #[Rk, Ok, neg', Rd, Od]) neg P)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {v : Term} (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (st : Term) {m : Nat}
    (hm : (level t n).K + 30 ≤ m) {T Y er f : Term}
    (run : Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) (.tuple #[Rk, Ok, neg', Rd, Od])
      (forceOp v) (.atom "true") st = .ok (.tuple #[T, Y, er, f])) :
    ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧ ∀ w, MT t n Y' w → P (level t n).den (MT t n X) v w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X :=
    funext fun u => propext (by simp [MT, hb])
  obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨Y', f', rfl, -, -, hY⟩⟩ :=
    dput_update_static_g hP hNa ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv hb fb
  · rcases static_rt_rel (k + 6) (.map X) _ _ _ _ _ _ _ _ run (by rw [show k + 2 + 6 = k + 6 + 2 by omega] at rr; exact rr)
      with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
  rcases static_rt_rel (k + 6) (.map X) _ _ _ _ _ _ _ _ run (by rw [show k + 2 + 6 = k + 6 + 2 by omega] at rr; exact rr)
    with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
  · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e
    obtain ⟨-, rfl, -⟩ := e
    rw [conv] at hY
    rcases hY with ⟨rfl, -⟩ | ⟨r, rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun w h => ?_⟩
      obtain ⟨b', hb', h'⟩ := h
      simp [mapLookup] at hb'; subst hb'
      exact (sr w).mp h'
  · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂
    obtain ⟨-, rfl, -⟩ := e₁
    obtain ⟨-, rfl, -⟩ := e₂
    rw [conv] at hY
    rcases hY with ⟨rfl, -⟩ | ⟨r, rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun w h => ?_⟩
      obtain ⟨b', hb', h'⟩ := h
      simp [mapLookup] at hb'; subst hb'
      exact (sr w).mp h'

end


/-! Upper bounds of updates of gradual map types. -/


section
variable {t : Term} {n : Nat}

theorem single_map_only {Y : List (Term × Term)} (hY : Y = [] ∨ ∃ r, Y = [(.atom "map", r)]) (q : PN t n)
    (hq : denD (.map Y) q) : q.1.1 = "map" := by
  rcases hY with rfl | ⟨r, rfl⟩
  · simp [denD_map, mapLookup, dn_none] at hq
  · rw [denD_map] at hq
    by_cases e : q.1.1 = "map"
    · exact e
    · simp [mapLookup, e, dn_none] at hq

/-- Updates of gradual map types at the upper bound: the maps the update gives from the static part or from the
dynamic part. -/
theorem upd_upper_gen {M : List (Term × Term)} (gM : GC (level t n) (.map M)) {s op : Term} {m : Nat}
    (hm : (level t n).K + 14 ≤ m + 1) {Sm : (MW (level t n).V → Prop) → MW (level t n).V → Prop}
    (hsem : ∀ X : List (Term × Term), DE (level t n).E (.map X) → ∀ st T Y er f,
      Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) (.map X) s op (.atom "true") st =
        .ok (.tuple #[T, Y, er, f]) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧
        ∀ w, MT t n Y' w → Sm (MT t n X) w)
    (hDy : ∀ Dy, mapLookup M (.atom "dynamic") = some Dy → ∃ DX, Dy = .map DX) {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (m + 1)) (.map M) s op (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    GC (level t n) R ∧ (∀ q : PN t n, denD (upper R) q → q.1.1 = "map") ∧
      ∀ w, denD (upper R) (mpt (t := t) (n := n) w) → Sm (MT t n (rmDyn M)) w ∨
        ∃ DX, mapLookup M (.atom "dynamic") = some (.map DX) ∧ Sm (MT t n DX) w := by
  cases hD : mapLookup M (.atom "dynamic") with
  | none =>
    have dM := GC.static gM hD
    obtain ⟨f, hs⟩ := static_upd_inv hD run
    obtain ⟨Y', rfl, dY, shY, sY⟩ := hsem M dM _ _ _ _ _ hs
    refine ⟨GC.tc dY, fun q hq => single_map_only shY q (by rwa [upper_tc dY] at hq), fun w h => Or.inl ?_⟩
    rw [upper_tc dY, denD_mpt] at h
    rw [rmDyn_static hD]
    exact sY w h
  | some Dy =>
    obtain ⟨DX, rfl⟩ := hDy _ hD
    obtain ⟨dDy, -⟩ : DE (level t n).E (.map DX) ∧ True := by
      rcases gM with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, -, -⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
      · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, trivial⟩
    obtain ⟨Yd, res, sd, ⟨Td, ed, fd, hdy⟩, sYd, hres, hsd, hR⟩ := grad_upd_inv hD (fun Td Yd ed fd h => by
      obtain ⟨Y', rfl, -, shY, -⟩ := hsem DX dDy _ _ _ _ _ h
      refine ⟨Y', rfl, ?_⟩
      rcases shY with rfl | ⟨r, rfl⟩ <;> simp [mapLookup]) run
    obtain ⟨Yd', eYd, dYd, shYd, sYd'⟩ := hsem DX dDy _ _ _ _ _ hdy
    cases eYd
    -- The static part.
    obtain ⟨SD, rfl, dSD, shSD, sSD⟩ : ∃ SD, sd = .map SD ∧ DE (level t n).E (.map SD) ∧
        (SD = [] ∨ ∃ r, SD = [(.atom "map", r)]) ∧ ∀ w, MT t n SD w → Sm (MT t n (rmDyn M)) w := by
      rcases hsd with ⟨rfl, rfl⟩ | ⟨a, e, f, rfl⟩
      · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun w h => by simp [MT, mapLookup] at h⟩
      · exact hsem (rmDyn M) gM.low_tc _ _ _ _ _ hres
    have gA : GC (level t n) (.map [(.atom "dynamic", .map Yd)]) := by
      refine Or.inr ⟨_, .map Yd, rfl, by simp [mapLookup], dYd, ?_, fun v hv => ?_⟩
      · rw [show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]]; exact descrC_nil
      · rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map Yd)] = [] by simp [rmDyn]] at hv
        simp [denD_map, mapLookup, dn_none] at hv
    obtain ⟨c, gc, rc, -, uc⟩ := gc_opt_union (GC.tc dSD) gA [] (m := m + 1) hm
    rw [show Elixir.Module.Types.Descr.«opt_union/2» (D (m + 1)) (.map SD) (.map [(.atom "dynamic", .map Yd)]) =
      Elixir.Module.Types.Descr.«opt_union/3» (D (m + 1)) (.map SD) (.map [(.atom "dynamic", .map Yd)]) (.map []) from rfl,
      rc] at hR
    cases hR
    have upA : upper (.map [(.atom "dynamic", .map Yd)]) = .map Yd := by simp [upper, mapLookup]
    refine ⟨gc, fun q hq => ?_, fun w h => ?_⟩
    · rcases (uc q).mp hq with h | h
      · rw [upper_tc dSD] at h; exact single_map_only shSD q h
      · rw [upA] at h; exact single_map_only shYd q h
    · rcases (uc _).mp h with h | h
      · rw [upper_tc dSD, denD_mpt] at h; exact Or.inl (sSD w h)
      · rw [upA, denD_mpt] at h; exact Or.inr ⟨DX, rfl, sYd' w h⟩

end

/-- `map_update/5` with a gradual value updates the dynamic part of the map type with the value's dynamic part. -/
theorem upd5_gval {m : Nat} (X : List (Term × Term)) {key mode s : Term} {Zv : List (Term × Term)} {Dv : Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s)
    (hmode : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject")
    (hZ : mapLookup Zv (.atom "dynamic") = some Dv) :
    Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key (.map Zv) mode (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map (dynG X)) s
        (.tuple #[.tuple #[.atom "constant", .tuple #[Dv, .atom "false"]], mode]) (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«map_update/5»
  cases hX : mapLookup X (.atom "dynamic") <;>
    rcases hmode with rfl | rfl | rfl <;>
    simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk, getMapKeys_single, hZ, hX,
      dynG] <;> rfl


/-- `empty?/1` of a gradual type is that of its dynamic part. -/
theorem empty_gval {Zv : List (Term × Term)} {Dv : Term} (hZ : mapLookup Zv (.atom "dynamic") = some Dv)
    (sD : Dv = .atom "term" ∨ ∃ DX, Dv = .map DX ∧ mapLookup DX (.atom "dynamic") = none) (m : Nat) :
    Elixir.Module.Types.Descr.«empty?/1» (D m) (.map Zv) = Elixir.Module.Types.Descr.«empty?/1» (D m) Dv := by
  rcases sD with rfl | ⟨DX, rfl, sX⟩
  · simp only [Elixir.Module.Types.Descr.«empty?/1»]
    rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    simp [getMapKeys_single, hZ]
  · simp only [Elixir.Module.Types.Descr.«empty?/1»]
    rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def, Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]
    simp [getMapKeys_single, hZ, sX]

end Elixir.STTDescrProofsTest.Nest
