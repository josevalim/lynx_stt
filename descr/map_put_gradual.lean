namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Forced updates do not read whether the type is static, so the dynamic part of a gradual type is put like a
static one. -/

theorem foldl1_congr (d : Dispatcher) (f g : Term) (h : ∀ x a, d.pure f #[x, a] = d.pure g #[x, a]) :
    ∀ (l : List Term) (acc : Term),
      Erlang.lists.«foldl_1/3» d f acc (Term.list l) = Erlang.lists.«foldl_1/3» d g acc (Term.list l)
  | [], acc => by simp [Term.list, Erlang.lists.«foldl_1/3»]
  | x :: l, acc => by
    simp only [Term.list]
    rw [Erlang.lists.«foldl_1/3».eq_def, Erlang.lists.«foldl_1/3».eq_def]
    simp only [h]
    cases d.pure g #[x, acc] with
    | error e => rfl
    | ok a => simpa [Term.list] using foldl1_congr d f g h l a

theorem foldl_congr (d : Dispatcher) {mo nm : String} {c₁ c₂ : Array Term}
    (h : ∀ x a, d.pure (.function mo nm 2 c₁) #[x, a] = d.pure (.function mo nm 2 c₂) #[x, a]) (l : List Term)
    (acc : Term) :
    Erlang.lists.«foldl/3» d (.function mo nm 2 c₁) acc (Term.list l) =
      Erlang.lists.«foldl/3» d (.function mo nm 2 c₂) acc (Term.list l) := by
  cases l with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Term.list]
  | cons x l =>
    simp only [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Term.list]
    simp only [h]
    cases d.pure (.function mo nm 2 c₂) #[x, acc] with
    | error e => simp [Lynx.Except.guard]
    | ok a => simpa [Lynx.Except.guard, Term.list] using foldl1_congr d _ _ h l a

/-- The step of `map_update_named_keys/8` does not read whether the type is static when forcing. -/
theorem named_step_static (d : Dispatcher) (dnf op req build ov key acc : Term) :
    Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req (.atom "false") build ov (.atom "true")
        key acc =
      Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req (.atom "true") build ov (.atom "true")
        key acc := by
  simp [Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»]

end Elixir.STTDescrProofsTest.Nest
