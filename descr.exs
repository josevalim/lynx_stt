# LYNX_DEBUG=lean LYNX_CACHE=0 elixir descr.exs
# Prove the set operations of Elixir's type system, Module.Types.Descr.
#
# Laws:
#
#   * Empty type: a type meets none() in the empty type.
#   * Negation: a type does not meet its negation, and a type united with its negation
#     is the top type. A gradual type meets its negation in its dynamic part, so the
#     intersection is checked on its lower bound and the union on its upper bound.
#   * De Morgan: the negation of a union is the intersection of the negations. For the
#     optimized operations, so is the dual: the negation of an intersection is the
#     union of the negations.
#   * Bounds: intersections are included in their arguments, and unions include them.
#   * Agreement: the plain and optimized unions, intersections, differences, and
#     negations are equal.
#   * Distributivity: plain intersections distribute over plain unions.
#   * Function arity: the top function type of each arity is the arrow from that many
#     arguments of none() to term().
#   * Compatibility: a type is compatible with another when its static part is included
#     in the dynamic part of the other and the two meet.
#   * Order: subtyping is reflexive and transitive, two types are equal when each is a
#     subtype of the other, and two types are disjoint when their intersection is empty.
#   * Lattice: unions and intersections are commutative, associative, and idempotent,
#     absorb each other, and unions distribute over intersections. A type is a subtype
#     of another when their union is the other, and when their intersection is the first.
#   * Difference: for static types, a type is a subtype of another when their difference is
#     empty, a type is the union of its difference with another type and its intersection
#     with it, a difference is disjoint from the type it removes, and negating a type twice
#     gives it back.
#   * Tuples: fetching an index of a static type of tuples gives the least type including
#     the values of its tuples there, and :badindex exactly when one of them is too short.
#     Inserting a non-empty type at an index and fetching that index gives the type back,
#     and deleting that index gives the tuples back. Inserting is monotone in the tuples
#     and the inserted type.
#   * Maps: fetching a key of a static type of maps gives the least type including the
#     values of its maps there, and :badkey exactly when one of them lacks the key.
#     Getting the keys of given atoms and kinds of keys gives the least type including
#     the values of its maps at those keys, :error exactly when none of them holds such
#     a key, and :badmap exactly for types other than non-empty types of maps. Getting
#     a single atom key agrees with fetching it. Converting a static type of maps to lists
#     lists every key and value of its maps, for atom keys and keys of each kind, with
#     values only from its maps; its lists hold the empty list exactly when the type holds
#     the empty map, and are only the empty list exactly when all its maps are empty.
#     Constructing maps from pairs of static types holds, at each atom key, the type and
#     optional flag of the last pair of the key, or else the optional values of the atom
#     domain, and at the keys of each kind the union of the domain pairs naming it, or
#     else any value for open maps and none for closed ones, all of them least. Closed
#     maps are open maps, and the empty map is the closed map of no pairs.
#     Putting a non-empty static type at an atom key gives :badmap exactly for types
#     other than non-empty types of maps; fetching the key afterwards gives the type
#     back, and other keys are unchanged. Putting is monotone in the maps and the type,
#     keeps the maps whose key already holds such a value, and putting twice is putting
#     once. Deleting the key after putting it is deleting it from the maps. Putting keys
#     of any static key type is monotone too, in the maps, the keys, and the type.
#     Forcing a static value at an atom key with map_update/5 puts the key, and returns the
#     values its maps held there, as map_get/2 gets them. Keeping or rejecting missing keys
#     instead gives a badkey error when some map lacks the key, and otherwise does the same.
#     Keeping or rejecting at keys without named atoms gives an error exactly when map_get/2
#     finds no value there, and every mode reports a missing domain exactly for the kinds
#     of the key type no map holds a key of.
#   * Functions: applying a static function type to non-empty static arguments succeeds exactly when the type is
#     a non-empty type of functions in the arrow from the arguments to term(), and then the function type is in the
#     top function type of their arity and in the arrow from the arguments to the result. Function types that are
#     empty, or that hold other values than functions, give :badfun.
#
# The negation, De Morgan, and bounds laws hold for both the plain operations and the
# optimized ones the type checker uses.
#
# Types:
#
#   * The empty type law holds for any map, valid type or not.
#   * The other laws need the invariants Descr maintains, and cover the top type and the
#     types of bitmaps, atoms, functions, lists, tuples, and maps. Lists, tuples, maps,
#     maps with domains, and functions nest types at any depth: each law takes the
#     depth as an input.
#   * Gradual types, whose dynamic part includes their static part, for both parts.
#     Inserting, deleting, and replacing tuple elements of gradual types gives, as upper bound,
#     the operation on the upper bounds, and, for a static value, as lower bound, the operation
#     on the lower bound, whenever both succeed. The values of tuple elements of gradual types have
#     the values of their bounds as bounds.
#   * The recursive type t = nil or {term(), t}, as a Descr node wherever types nest.
#
# Function types are modeled as sets of functions, whose arguments and returns are nested
# types. The plain negation and De Morgan laws also hold for static types whose function
# types hold any literals, modeled as Boolean combinations of arrows.
#
# Checked against Elixir 1.21.0-dev (468a8c51a), Erlang/OTP 29.1.2.
# Source reference: ../elixir/lib/elixir/lib/module/types/descr.ex.
# These proofs depend on implementation details; rerun after Elixir upgrades.
Mix.install([{:lynx, path: Path.expand("../lynx", __DIR__)}])

ExUnit.start()

defmodule STTDescrProofsTest do
  use ExUnit.Case, async: true
  use Lynx.Case

  @moduletag timeout: :infinity
  alias Module.Types.Descr

  # Static types of bitmaps and atoms in normal form: bitmaps are non-empty,
  # and so are unions of atoms.
  def valid?(descr) when is_map(descr), do: valid_fields?(:maps.to_list(descr))
  def valid?(_descr), do: false

  defp valid_fields?([{:bitmap, bits} | fields]),
    do: is_integer(bits) and bits >= 1 and bits <= 255 and valid_fields?(fields)

  defp valid_fields?([{:atom, {:union, set}} | fields]),
    do: atoms?(set) and map_size(set) > 0 and valid_fields?(fields)

  defp valid_fields?([{:atom, {:negation, set}} | fields]),
    do: atoms?(set) and valid_fields?(fields)

  defp valid_fields?([]), do: true
  defp valid_fields?(_fields), do: false

  # Version 2 sets are maps from their elements to [].
  defp atoms?(set) when is_map(set), do: atom_keys?(:maps.to_list(set))
  defp atoms?(_set), do: false

  defp atom_keys?([{atom, []} | rest]), do: is_atom(atom) and atom_keys?(rest)
  defp atom_keys?([]), do: true
  defp atom_keys?(_rest), do: false

  # The top type and types of bitmaps, atoms, functions, lists, tuples, and maps. Function
  # types are unions or negations of maps from arities to BDDs, whose literals are not
  # inspected. List elements and tails, tuple elements, map fields, and the arguments and
  # returns of nested functions nest types of bitmaps, atoms, functions, lists, tuples, and
  # maps, at most `depth` levels deep, and the recursive node `node` below, given as
  # `{depth, node}`. The laws take any depth as an input, so they hold for types of every depth.
  def depth?(depth), do: is_integer(depth) and depth >= 0

  # The recursive node of the laws: a recursive tuple, t = nil or {term(), t}, as
  # Descr.recursive/1 builds it from the generator below.
  def tuple_list(recur),
    do: Descr.bare_union(Descr.atom([nil]), Descr.tuple([Descr.term(), recur.(:t)]))

  def recursive_node?({id, %{t: {id, generator}}, generator}) when is_reference(id),
    do: generator === &__MODULE__.tuple_list/1

  def recursive_node?(_node), do: false

  def negatable?(:term, _depth), do: true
  def negatable?(descr, depth) when is_map(descr), do: negatable_fields?(:maps.to_list(descr), depth)
  def negatable?(_descr, _depth), do: false

  defp negatable_fields?([field | fields], depth),
    do: negatable_field?(field, depth) and negatable_fields?(fields, depth)

  defp negatable_fields?([], _depth), do: true

  defp negatable_field?({:fun, {tag, arities}}, _depth) when tag in [:union, :negation],
    do: is_map(arities) and arity_bdds?(:maps.to_list(arities))

  defp negatable_field?(field, depth), do: nested_field?(field, depth)

  defp arity_bdds?([{_arity, bdd} | arities]), do: any_bdd?(bdd, :bottom) and arity_bdds?(arities)
  defp arity_bdds?([]), do: true

  # BDDs ordered by Erlang's term order, whose literals may hold anything.
  defp any_bdd?(:bdd_top, _lower), do: true
  defp any_bdd?(:bdd_bot, _lower), do: true
  defp any_bdd?({key, _, _} = leaf, lower), do: is_integer(key) and leaf > lower

  defp any_bdd?({hash, {key, _, _} = lit, c, u, d}, lower),
    do:
      is_integer(hash) and is_integer(key) and lit > lower and any_bdd?(c, lit) and any_bdd?(u, lit) and
        any_bdd?(d, lit)

  defp any_bdd?(_bdd, _lower), do: false

  # Nested types: the top type, the recursive node, valid types, or types of bitmaps, atoms,
  # functions, lists, tuples, and maps whose contents nest at most `depth - 1` levels. The
  # depth comes with the recursive node the types may hold, as `{depth, node}`.
  defp nested?(:term, _depth), do: true

  defp nested?({_, _, _} = other, {_depth, node}) when other === node,
    do: recursive_node?(other)

  defp nested?(type, {0, _node}), do: valid?(type)

  defp nested?(type, {depth, node}) when is_map(type),
    do: nested_fields?(:maps.to_list(type), {depth - 1, node})

  defp nested?(_type, _depth), do: false

  defp nested_fields?([field | fields], depth),
    do: nested_field?(field, depth) and nested_fields?(fields, depth)

  defp nested_fields?([], _depth), do: true

  defp nested_field?({:fun, {tag, arities}}, depth) when tag in [:union, :negation],
    do: is_map(arities) and fun_arities?(:maps.to_list(arities), depth)

  defp nested_field?({:list, bdd}, depth), do: list_bdd?(bdd, depth)
  defp nested_field?({:tuple, bdd}, depth), do: tuple_bdd?(bdd, depth)
  defp nested_field?({:map, bdd}, depth), do: map_bdd?(bdd, depth)
  defp nested_field?(field, _depth), do: valid_fields?([field])

  # Function types map arities to BDDs of function literals ordered by Erlang's
  # term order, whose arguments, as many as their arity, and return types are
  # nested types.
  defp fun_arities?([{arity, bdd} | arities], depth),
    do: is_integer(arity) and fun_bdd?(bdd, arity, :bottom, depth) and fun_arities?(arities, depth)

  defp fun_arities?([], _depth), do: true

  defp fun_bdd?(:bdd_top, _arity, _lower, _depth), do: true
  defp fun_bdd?(:bdd_bot, _arity, _lower, _depth), do: true
  defp fun_bdd?({_, _, _} = leaf, arity, lower, depth), do: fun_literal?(leaf, arity, lower, depth)

  defp fun_bdd?({hash, lit, c, u, d}, arity, lower, depth),
    do:
      is_integer(hash) and fun_literal?(lit, arity, lower, depth) and fun_bdd?(c, arity, lit, depth) and
        fun_bdd?(u, arity, lit, depth) and fun_bdd?(d, arity, lit, depth)

  defp fun_bdd?(_bdd, _arity, _lower, _depth), do: false

  defp fun_literal?({key, args, return} = lit, arity, lower, depth),
    do:
      is_integer(key) and lit > lower and elements?(args, depth) and length(args) == arity and
        nested?(return, depth)

  defp fun_literal?(_lit, _arity, _lower, _depth), do: false

  # List types are all non-empty lists, or BDDs of other list literals ordered
  # by Erlang's term order, whose element and tail types are nested types. Atoms
  # precede the tuples of literals.
  defp list_bdd?({key, :term, :term}, _depth), do: is_integer(key)
  defp list_bdd?(bdd, depth), do: ordered_bdd?(bdd, :bottom, depth)

  defp ordered_bdd?(:bdd_top, _lower, _depth), do: true
  defp ordered_bdd?(:bdd_bot, _lower, _depth), do: true
  defp ordered_bdd?({_, _, _} = leaf, lower, depth), do: list_literal?(leaf, lower, depth)

  defp ordered_bdd?({hash, lit, c, u, d}, lower, depth),
    do:
      is_integer(hash) and list_literal?(lit, lower, depth) and ordered_bdd?(c, lit, depth) and
        ordered_bdd?(u, lit, depth) and ordered_bdd?(d, lit, depth)

  defp ordered_bdd?(_bdd, _lower, _depth), do: false

  defp list_literal?({key, list, last} = lit, lower, depth),
    do:
      is_integer(key) and lit > lower and not (list == :term and last == :term) and
        nested?(list, depth) and nested?(last, depth)

  defp list_literal?(_lit, _lower, _depth), do: false

  # Tuple types are all tuples, or BDDs of other tuple literals ordered by
  # Erlang's term order, whose elements are nested types.
  defp tuple_bdd?({key, :open, []}, _depth), do: is_integer(key)
  defp tuple_bdd?(bdd, depth), do: ordered_tuple_bdd?(bdd, :bottom, depth)

  defp ordered_tuple_bdd?(:bdd_top, _lower, _depth), do: true
  defp ordered_tuple_bdd?(:bdd_bot, _lower, _depth), do: true
  defp ordered_tuple_bdd?({_, _, _} = leaf, lower, depth), do: tuple_literal?(leaf, lower, depth)

  defp ordered_tuple_bdd?({hash, lit, c, u, d}, lower, depth),
    do:
      is_integer(hash) and tuple_literal?(lit, lower, depth) and ordered_tuple_bdd?(c, lit, depth) and
        ordered_tuple_bdd?(u, lit, depth) and ordered_tuple_bdd?(d, lit, depth)

  defp ordered_tuple_bdd?(_bdd, _lower, _depth), do: false

  defp tuple_literal?({key, tag, elements} = lit, lower, depth) when tag in [:open, :closed],
    do:
      is_integer(key) and lit > lower and not (tag == :open and elements == []) and
        elements?(elements, depth)

  defp tuple_literal?(_lit, _lower, _depth), do: false

  defp elements?([element | elements], depth), do: nested?(element, depth) and elements?(elements, depth)
  defp elements?([], _depth), do: true
  defp elements?(_elements, _depth), do: false

  # Map types are all maps, or BDDs of other map literals ordered by Erlang's term order.
  # Their literals are open maps, closed maps, or maps with domains, the types of the values
  # of each kind of keys, and their fields and domains hold nested types.
  defp map_bdd?({key, :open, []}, _depth), do: is_integer(key)
  defp map_bdd?(bdd, depth), do: ordered_map_bdd?(bdd, :bottom, depth)

  defp ordered_map_bdd?(:bdd_top, _lower, _depth), do: true
  defp ordered_map_bdd?(:bdd_bot, _lower, _depth), do: true
  defp ordered_map_bdd?({_, _, _} = leaf, lower, depth), do: map_literal?(leaf, lower, depth)

  defp ordered_map_bdd?({hash, lit, c, u, d}, lower, depth),
    do:
      is_integer(hash) and map_literal?(lit, lower, depth) and ordered_map_bdd?(c, lit, depth) and
        ordered_map_bdd?(u, lit, depth) and ordered_map_bdd?(d, lit, depth)

  defp ordered_map_bdd?(_bdd, _lower, _depth), do: false

  defp map_literal?({key, tag, fields} = lit, lower, depth),
    do:
      is_integer(key) and lit > lower and map_tag?(tag, depth) and
        not (tag == :open and fields == []) and map_fields?(fields, depth)

  defp map_literal?(_lit, _lower, _depth), do: false

  defp map_tag?(tag, _depth) when tag in [:open, :closed], do: true
  defp map_tag?(domains, depth), do: map_domains?(domains, depth)

  defp map_domains?([{_kind, type} | domains], depth),
    do: nested?(type, depth) and map_domains?(domains, depth)

  defp map_domains?([], _depth), do: true
  defp map_domains?(_domains, _depth), do: false

  defp map_fields?([{_key, {type, optional?}} | fields], depth),
    do: is_boolean(optional?) and nested?(type, depth) and map_fields?(fields, depth)

  defp map_fields?([], _depth), do: true
  defp map_fields?(_fields, _depth), do: false

  # Any type: the top type or a map of fields, whose dynamic part, if any,
  # is the top type or a map. The fields may hold anything.
  def descr?(:term), do: true
  def descr?(%{dynamic: dynamic}), do: dynamic == :term or is_map(dynamic)
  def descr?(descr), do: is_map(descr)

  defp sorted_keys?([{key, _} | [{next, _} | _] = fields]),
    do: is_atom(key) and key < next and sorted_keys?(fields)

  defp sorted_keys?([{key, _}]), do: is_atom(key)
  defp sorted_keys?(_fields), do: true

  # Types of the laws on optimized operations: the top type, or negatable types whose tuple
  # and map literals are keyed as Descr keys them at every depth, so closed literals sort
  # before open ones: closed literals have negative keys, open ones other than the top
  # literals and those with domains have non-negative keys, and map literals have atom keys
  # in order and domains of the kinds Descr knows in order. Function types inside other
  # types have arities that are natural numbers, at least one when they are unions, and keyed
  # arguments and returns. The depth comes with the recursive node, as `{depth, node}`.
  def opt_negatable?(:term, _depth), do: true

  def opt_negatable?(descr, {depth, _node} = nested),
    do: negatable?(descr, nested) and keyed_fields?(:maps.to_list(descr), depth, false)

  defp arrows?(%{fun: fun}, {depth, _node} = nested),
    do: nested_field?({:fun, fun}, nested) and keyed_fields?([{:fun, fun}], depth, true)

  defp arrows?(_descr, _nested), do: true

  # Static types of the laws: the types above whose function types are arrows between nested types.
  def arrows_static?(descr, nested), do: opt_negatable?(descr, nested) and arrows?(descr, nested)

  # Gradual types of the laws: static types, or a static part and a dynamic part of those types, where the dynamic
  # part includes the static part, as Descr maintains. Inclusion is checked with Descr.
  def arrows_gradual?(%{dynamic: dynamic} = descr, nested) do
    static = Map.delete(descr, :dynamic)

    arrows_static?(static, nested) and arrows_static?(dynamic, nested) and
      Descr.empty?(Descr.bare_difference(static, dynamic))
  end

  def arrows_gradual?(descr, nested), do: arrows_static?(descr, nested)

  # Arguments of the laws on function application: lists of static types.
  def arguments?([arg | args], nested), do: arrows_static?(arg, nested) and arguments?(args, nested)
  def arguments?([], _nested), do: true
  def arguments?(_args, _nested), do: false

  # Arguments none of which is empty.
  def inhabited?([arg | args]), do: not Descr.empty?(arg) and inhabited?(args)
  def inhabited?([]), do: true

  # Arguments of the gradual laws on function application: lists of gradual types.
  def gradual_arguments?([arg | args], nested), do: arrows_gradual?(arg, nested) and gradual_arguments?(args, nested)
  def gradual_arguments?([], _nested), do: true
  def gradual_arguments?(_args, _nested), do: false

  # A gradual type at least as precise as another: the other's lower bound is in its own, and its upper bound in
  # the other's.
  def precise?(left, right),
    do:
      Descr.subtype?(Descr.lower_bound(right), Descr.lower_bound(left)) and
        Descr.subtype?(Descr.upper_bound(left), Descr.upper_bound(right))

  def all_precise?([left | lefts], [right | rights]), do: precise?(left, right) and all_precise?(lefts, rights)
  def all_precise?([], []), do: true
  def all_precise?(_lefts, _rights), do: false

  # A static type between the bounds of a gradual type.
  def materializes?(static, gradual),
    do: Descr.subtype?(Descr.lower_bound(gradual), static) and Descr.subtype?(static, Descr.upper_bound(gradual))

  def all_materialize?([static | statics], [gradual | graduals]),
    do: materializes?(static, gradual) and all_materialize?(statics, graduals)

  def all_materialize?([], []), do: true
  def all_materialize?(_statics, _graduals), do: false

  # Arguments whose upper bounds are in the upper bounds of others.
  def uppers_in?([left | lefts], [right | rights]),
    do: Descr.subtype?(Descr.upper_bound(left), Descr.upper_bound(right)) and uppers_in?(lefts, rights)

  def uppers_in?([], []), do: true
  def uppers_in?(_lefts, _rights), do: false

  defp keyed?(:term, _depth), do: true
  defp keyed?({_, _, _}, _depth), do: true
  defp keyed?(_descr, 0), do: true
  defp keyed?(descr, depth), do: keyed_fields?(:maps.to_list(descr), depth - 1, true)

  defp keyed_fields?([{:fun, {tag, arities}} | fields], depth, true) when is_map(arities),
    do:
      (tag == :negation or map_size(arities) > 0) and keyed_arities?(:maps.to_list(arities), depth) and
        keyed_fields?(fields, depth, true)

  defp keyed_fields?([{:fun, _fun} | _fields], _depth, true), do: false

  defp keyed_fields?([{:tuple, bdd} | fields], depth, element?),
    do: keyed_tuple_bdd?(bdd, depth) and keyed_fields?(fields, depth, element?)

  defp keyed_fields?([{:map, bdd} | fields], depth, element?),
    do: keyed_map_bdd?(bdd, depth) and keyed_fields?(fields, depth, element?)

  defp keyed_fields?([{:list, bdd} | fields], depth, element?),
    do: keyed_list_bdd?(bdd, depth) and keyed_fields?(fields, depth, element?)

  defp keyed_fields?([_field | fields], depth, element?), do: keyed_fields?(fields, depth, element?)
  defp keyed_fields?([], _depth, _element?), do: true
  defp keyed_fields?(_fields, _depth, _element?), do: false

  defp keyed_tuple_bdd?({_, lit, c, u, d}, depth),
    do:
      keyed_tuple_bdd?(lit, depth) and keyed_tuple_bdd?(c, depth) and keyed_tuple_bdd?(u, depth) and
        keyed_tuple_bdd?(d, depth)

  defp keyed_tuple_bdd?({key, :closed, elements}, depth),
    do: key < 0 and keyed_elements?(elements, depth)

  defp keyed_tuple_bdd?({key, _tag, elements}, depth),
    do: (elements == [] or key >= 0) and keyed_elements?(elements, depth)

  defp keyed_tuple_bdd?(_bdd, _depth), do: true

  defp keyed_elements?([element | elements], depth),
    do: keyed?(element, depth) and keyed_elements?(elements, depth)

  defp keyed_elements?([], _depth), do: true
  defp keyed_elements?(_elements, _depth), do: false

  defp keyed_map_bdd?({_, lit, c, u, d}, depth),
    do:
      keyed_map_bdd?(lit, depth) and keyed_map_bdd?(c, depth) and keyed_map_bdd?(u, depth) and
        keyed_map_bdd?(d, depth)

  defp keyed_map_bdd?({key, :closed, fields}, depth),
    do: key < 0 and sorted_keys?(fields) and keyed_values?(fields, depth)

  defp keyed_map_bdd?({key, domains, fields}, depth) when is_list(domains),
    do:
      key >= 0 and domain_kinds?(domains) and keyed_domains?(domains, depth) and sorted_keys?(fields) and
        keyed_values?(fields, depth)

  defp keyed_map_bdd?({key, _tag, fields}, depth),
    do: (fields == [] or key >= 0) and sorted_keys?(fields) and keyed_values?(fields, depth)

  defp keyed_map_bdd?(_bdd, _depth), do: true

  defp keyed_values?([{_key, {type, _optional?}} | fields], depth),
    do: keyed?(type, depth) and keyed_values?(fields, depth)

  defp keyed_values?([], _depth), do: true
  defp keyed_values?(_fields, _depth), do: false

  defp domain_kinds?([{kind, _} | [{next, _} | _] = domains]),
    do: domain_kind?(kind) and kind < next and domain_kinds?(domains)

  defp domain_kinds?([{kind, _}]), do: domain_kind?(kind)
  defp domain_kinds?(_domains), do: true

  defp domain_kind?(kind)
       when kind in [:atom, :binary, :bitstring_no_binary, :float, :fun, :integer] or
              kind in [:list, :map, :pid, :port, :reference, :tuple],
       do: true

  defp domain_kind?(_kind), do: false

  defp keyed_domains?([{_kind, type} | domains], depth),
    do: keyed?(type, depth) and keyed_domains?(domains, depth)

  defp keyed_domains?([], _depth), do: true
  defp keyed_domains?(_domains, _depth), do: false

  # Function types inside other types have arities that are natural numbers, at least one when
  # they are unions, and keyed arguments and returns.
  defp keyed_arities?([{arity, bdd} | arities], depth),
    do: is_integer(arity) and arity >= 0 and keyed_fun_bdd?(bdd, depth) and keyed_arities?(arities, depth)

  defp keyed_arities?([], _depth), do: true
  defp keyed_arities?(_arities, _depth), do: false

  defp keyed_fun_bdd?({_, lit, c, u, d}, depth),
    do:
      keyed_fun_bdd?(lit, depth) and keyed_fun_bdd?(c, depth) and keyed_fun_bdd?(u, depth) and
        keyed_fun_bdd?(d, depth)

  defp keyed_fun_bdd?({_key, args, return}, depth), do: keyed_elements?(args, depth) and keyed?(return, depth)
  defp keyed_fun_bdd?(_bdd, _depth), do: true

  defp keyed_list_bdd?({_, lit, c, u, d}, depth),
    do:
      keyed_list_bdd?(lit, depth) and keyed_list_bdd?(c, depth) and keyed_list_bdd?(u, depth) and
        keyed_list_bdd?(d, depth)

  defp keyed_list_bdd?({_key, list, last}, depth), do: keyed?(list, depth) and keyed?(last, depth)
  defp keyed_list_bdd?(_bdd, _depth), do: true

  # Keys of map types, as lists of atoms and of kinds of keys that map domains name.
  def keys?(atoms, kinds), do: atom_list?(atoms) and kind_list?(kinds)

  defp atom_list?([atom | atoms]), do: is_atom(atom) and atom_list?(atoms)
  defp atom_list?(atoms), do: atoms == []

  defp kind_list?([kind | kinds]), do: domain_kind?(kind) and kind_list?(kinds)
  defp kind_list?(kinds), do: kinds == []

  # The type of the keys of the given atoms and kinds.
  def key_type([], kinds), do: kinds_type(kinds, Descr.none())
  def key_type(atoms, kinds), do: kinds_type(kinds, Descr.atom(atoms))

  # The type map_get/2 found, or none() when no map holds such a key.
  def got({:ok, type}), do: type
  def got(_), do: Descr.none()

  # The kinds of keys other than atoms, whose domains map_update/5 reports in {:baddomain, type} errors.
  def update_kinds,
    do: [:bitstring_no_binary, :binary, :integer, :float, :pid, :port, :reference, :fun, :tuple, :map, :list]

  def has_baddomain?([{:baddomain, other} | errors], type),
    do: (Descr.subtype?(other, type) and Descr.subtype?(type, other)) or has_baddomain?(errors, type)

  def has_baddomain?([_ | errors], type), do: has_baddomain?(errors, type)
  def has_baddomain?(_errors, _type), do: false

  # Each domain of the key type is reported missing exactly when no map holds a key of that domain.
  def baddomains?(map, key, errors, [kind | kinds]),
    do:
      (Descr.disjoint?(kind_type(kind), key) or
         has_baddomain?(errors, kind_type(kind)) == Descr.empty?(got(Descr.map_get(map, kind_type(kind))))) and
        baddomains?(map, key, errors, kinds)

  def baddomains?(_map, _key, _errors, []), do: true

  # Key types without named atoms: no atoms, all atoms, or all atoms but a finite set.
  def unnamed_keys?(key, atoms),
    do:
      keys?(atoms, []) and
        (Descr.disjoint?(key, Descr.atom()) or Descr.subtype?(Descr.atom(), key) or
           (atoms != [] and Descr.subtype?(Descr.opt_difference(Descr.atom(), key), Descr.atom(atoms))))

  # Results of tuple_fetch/2 that agree: the same element type, or the same error.
  def same_fetch?({false, left}, {false, right}), do: Descr.equal?(left, right)
  def same_fetch?(left, right), do: left == right

  # Results of map_get/2 that agree: the same value type, or the same error.
  def same_get?({:ok, left}, {:ok, right}), do: Descr.equal?(left, right)
  def same_get?(left, right), do: left == right

  # Maps holding an atom key.
  def has_key(atom), do: Descr.open_map([{atom, {Descr.term(), false}}])

  # Maps holding every one of the atom keys.
  def holding([atom | atoms]), do: Descr.bare_intersection(has_key(atom), holding(atoms))
  def holding([]), do: Descr.open_map()

  # The errors of the atom keys some map of a type lacks.
  def lacking(map, [atom | atoms]) do
    case Descr.subtype?(map, has_key(atom)) do
      true -> lacking(map, atoms)
      false -> [{:badkey, atom} | lacking(map, atoms)]
    end
  end

  def lacking(_map, []), do: []

  # The union of putting each of the atom keys.
  def puts(map, [atom | atoms], value),
    do: Descr.bare_union(elem(Descr.map_put_key(map, atom, value), 1), puts(map, atoms, value))

  def puts(_map, [], _value), do: Descr.none()

  # The union of putting each of the atom keys into the maps holding it.
  def updates(map, [atom | atoms], value) do
    holder = Descr.opt_intersection(map, has_key(atom))

    case Descr.empty?(holder) do
      true -> updates(map, atoms, value)
      false -> Descr.bare_union(elem(Descr.map_put_key(holder, atom, value), 1), updates(map, atoms, value))
    end
  end

  def updates(_map, [], _value), do: Descr.none()

  # The maps updating the atom keys gives: the updated maps, and with :keep the maps lacking some key.
  def updated(map, atoms, value, :reject), do: updates(map, atoms, value)

  def updated(map, atoms, value, :keep),
    do: Descr.bare_union(updates(map, atoms, value), Descr.opt_difference(map, holding(atoms)))

  # Lists with the same elements, without duplicates.
  def permutation?(left, right), do: length(left) == length(right) and all_in?(left, right) and all_in?(right, left)

  defp all_in?([x | xs], ys), do: :lists.member(x, ys) and all_in?(xs, ys)
  defp all_in?([], _ys), do: true

  # Sizes of tuples, as lists of natural numbers.
  def sizes?([size | sizes]), do: is_integer(size) and size >= 0 and sizes?(sizes)
  def sizes?(sizes), do: sizes == []

  # The closed tuples of the given sizes whose elements are values of a type.
  def closed_tuples([size | sizes], value),
    do: Descr.bare_union(Descr.tuple(:lists.duplicate(size, value)), closed_tuples(sizes, value))

  def closed_tuples([], _value), do: Descr.none()

  defp kinds_type([kind | kinds], acc), do: kinds_type(kinds, Descr.bare_union(kind_type(kind), acc))
  defp kinds_type([], acc), do: acc

  defp kind_type(:atom), do: Descr.atom()
  defp kind_type(:binary), do: Descr.binary()
  defp kind_type(:bitstring_no_binary), do: Descr.bitstring_no_binary()
  defp kind_type(:float), do: Descr.float()
  defp kind_type(:fun), do: Descr.fun()
  defp kind_type(:integer), do: Descr.integer()
  defp kind_type(:list), do: Descr.bare_union(Descr.empty_list(), Descr.non_empty_list(Descr.term(), Descr.term()))
  defp kind_type(:map), do: Descr.open_map()
  defp kind_type(:pid), do: Descr.pid()
  defp kind_type(:port), do: Descr.port()
  defp kind_type(:reference), do: Descr.reference()
  defp kind_type(:tuple), do: Descr.tuple()

  # Maps whose keys of the given atoms and kinds hold values of a type: the open maps
  # holding them at each of those keys.
  def keys_hold(atoms, kinds, value), do: kinds_hold(kinds, value, atoms_hold(atoms, value, Descr.open_map()))

  defp atoms_hold([atom | atoms], value, acc),
    do: atoms_hold(atoms, value, Descr.bare_intersection(acc, Descr.open_map([{atom, {value, true}}])))

  defp atoms_hold([], _value, acc), do: acc

  defp kinds_hold([kind | kinds], value, acc),
    do: kinds_hold(kinds, value, Descr.bare_intersection(acc, Descr.open_map([{[kind], value}])))

  defp kinds_hold([], _value, acc), do: acc

  # Pairs of map constructors: atom keys with types and optional flags, and lists of kinds of keys
  # with types, all of them static types of the given nesting.
  def map_pairs?([{key, {value, optional?}} | pairs], nested) when is_atom(key) and is_boolean(optional?),
    do: arrows_static?(value, nested) and map_pairs?(pairs, nested)

  def map_pairs?([{kinds, value} | pairs], nested) when is_list(kinds),
    do: kind_list?(kinds) and arrows_static?(value, nested) and map_pairs?(pairs, nested)

  def map_pairs?(pairs, _nested), do: pairs == []

  # The map constructors of open and closed maps.
  def construct(:open, pairs), do: Descr.open_map(pairs)
  def construct(:closed, pairs), do: Descr.closed_map(pairs)

  # The field a constructed map holds at an atom key: that of the last pair of the key, or the
  # optional values of the atom domain.
  def atom_field(tag, pairs, key) do
    case :lists.keyfind(key, 1, :lists.reverse(pairs)) do
      {^key, field} -> field
      false -> {domain_value(tag, pairs, :atom), true}
    end
  end

  # The values a constructed map holds at the keys of a kind: the union of the types of the pairs
  # naming the kind, or any value for open maps and none for closed ones.
  def domain_value(tag, pairs, kind), do: domain_value(pairs, kind, tag_value(tag), false)

  defp domain_value([{kinds, value} | pairs], kind, acc, found?) when is_list(kinds) do
    case kind_in?(kinds, kind) do
      true when found? -> domain_value(pairs, kind, Descr.bare_union(acc, value), true)
      true -> domain_value(pairs, kind, value, true)
      false -> domain_value(pairs, kind, acc, found?)
    end
  end

  defp domain_value([_pair | pairs], kind, acc, found?), do: domain_value(pairs, kind, acc, found?)
  defp domain_value([], _kind, acc, _found?), do: acc

  defp kind_in?([kind | kinds], other), do: kind == other or kind_in?(kinds, other)
  defp kind_in?([], _other), do: false

  defp tag_value(:open), do: Descr.term()
  defp tag_value(:closed), do: Descr.none()

  laws "static" do
    # Elixir's default map field access falls back to a remote call on non-maps.
    cutoff &:elixir_erl_pass.no_parens_remote/2

    # Lines with negative tuple or map literals are not modeled, so their
    # emptiness is cut off.

    # Tuples are only padded to longer sizes, which never raises.
    cutoff &ArgumentError.exception/1

    # The laws do not inspect the domains that failed applications report.
    cutoff &Descr.domain_to_flat_args/2

    # Descr only uses version 2 sets, which are maps.
    cutoff &:sets.get_slot/2
    cutoff &:sets.get_bucket/2
    cutoff &:sets.fold_set/3
    cutoff &:sets.filter_set/2
    cutoff &:sets.maybe_expand/1
    cutoff &:sets.maybe_contract/2
    cutoff &:sets.mk_seg/1

    # Recursive types are unfolded on demand, so descr's recursion is partial.
    termination_suffix &Descr.unfold/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.upper_bound/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.lower_bound/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.empty_seen?/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_union/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_difference/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_intersection/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.bdd_difference/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_map_difference_strategy/5, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:orddict.merge/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.fields_merge_with_defaults/5, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.duplicate/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_map_union_strategy/5, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_tuple_fuse_elements/4, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.opt_tuple_union_leaf/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.empty_difference_subtype?/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.iterator_empty_difference_subtype?/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.fun_line_empty?/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.dynamic/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.fun_normalize/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.fun_apply/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.tuple_fetch/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_fetch_key/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_get/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_split_keys_and_domains/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.to_domain_keys/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:sets.fold_1/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_to_list/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.ukeymerge3_1/11, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.rukeymerge3_1/11, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.umergel/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.mergel/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &:lists.ukeymergel/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.fields_put_all_new/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.tuple_elim_sizes/4, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.tuple_delete_at/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.tuple_insert_at/3, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.tuple_values/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_union_all/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_update_static/5, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_update_unchecked/4, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &Descr.map_put/3, ~LEAN"partial_fixpoint", recur: true
    # Nested types are finite, so their specification terminates.
    termination_suffix &__MODULE__.nested?/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &__MODULE__.keyed?/2, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &__MODULE__.sorted_keys?/1, ~LEAN"partial_fixpoint", recur: true
    termination_suffix &__MODULE__.domain_kinds?/1, ~LEAN"partial_fixpoint", recur: true

    # Valid types hold a non-empty bitmap and atom types of version 2 sets.
    postlude "descr/valid_types.lean"

    # Unions merge fields with maps:merge_with/3.
    postlude "descr/union_fields.lean"

    # Intersections intersect fields with maps:intersect_with/3 and drop empty ones.
    postlude "descr/intersection_fields.lean"

    # Differences fold over the fields of the right type and drop empty ones.
    postlude "descr/difference_fields.lean"

    # The empty type is the empty map, and intersecting with it empties a type.
    postlude "descr/empty_type.lean"

    # A function type and its negation hold the same BDDs for each arity, whose
    # differences are bottom, so their intersection drops every arity.
    postlude "descr/function_negation.lean"

    # Lazy BDDs ordered by their literals: unions, removals, intersections,
    # negations, and differences terminate and compute the propositional
    # connectives, so a BDD that no assignment of its literals satisfies has no line.
    postlude "descr/bdd_connectives.lean"

    # Tuple types are the top tuple literal or ordered BDDs of other tuple literals,
    # whose elements are types of bitmaps, atoms, tuples, and lists. Lines of
    # tuples intersect these elements, which stay such types, and what remains
    # of a tuple type and its negation has no line, except for the empty tuple,
    # whose negation holds tuples of other sizes.
    postlude "descr/tuple_negation.lean"

    # Map types are the top map literal or ordered BDDs of other map literals,
    # open or closed maps whose fields hold types of bitmaps and atoms. Lines of
    # maps intersect these fields, whose emptiness is immediate, and what remains
    # of a map type and its negation has no line.
    postlude "descr/map_negation.lean"

    # List types are the top list literal or ordered BDDs of other list literals,
    # so negations hold the same literals and the list intersection shortcuts
    # never apply. What remains of a list type and its negation has no line.
    postlude "descr/list_negation.lean"

    # Negations are differences from the top type, which no type intersects.
    postlude "descr/negation_intersection.lean"

    # The optimized operations compute the same negations of bitmaps, atoms, functions,
    # lists, and tuples, while open maps of one field negate to open maps of one field.
    # Their intersections fall back to BDD intersections, since the negation of a BDD
    # node is never a leaf, or intersect literals whose fields do not meet.
    postlude "descr/opt_negation_intersection.lean"

    # The top type is a subtype of a type united with its negation: each field of the top
    # type, minus what the type and its negation unite into at that field, is empty.
    # Propositional BDD unions are tautologies, while `{}` and its negation `{term, ...}`
    # are checked as concrete tuple lines.
    postlude "descr/union_negation_top.lean"

    # Optimized unions of a type with its optimized negation fuse open maps of a single
    # field into one, except for `:__struct__` keys, which only fuse when one side is a
    # subtype. Basic types, whose fields are non-empty bitmaps, atoms, or the top function,
    # list, tuple, and map types, compute set operations, so the fused fields and the map
    # lines of both single field maps can be checked directly.
    postlude "descr/opt_union_negation.lean"

    # De Morgan's law for the plain operations. Each field denotes a propositional predicate:
    # bitmaps their bits, atoms their members, functions their BDDs per arity, and lists,
    # tuples, and maps their BDDs. Unions, intersections, and negations compute the
    # connectives, under valuations that some tuple realizes for tuple literals, since the
    # negation of `{}` is `{term, ...}`. A type whose fields hold no more than another's is
    # its subtype, since tuple lines that no realizable valuation satisfies are empty.
    postlude "descr/plain_de_morgan.lean"
    postlude "descr/recursive_node.lean"
    postlude "descr/element_values.lean"
    postlude "descr/basic_values.lean"
    postlude "descr/open_map_leaves.lean"
    postlude "descr/basic_subtype_sound.lean"
    postlude "descr/tuple_opt_union_literals.lean"
    postlude "descr/tuple_fuse_flat.lean"
    postlude "descr/tuple_negation_flat.lean"
    postlude "descr/opt_fields_values.lean"
    postlude "descr/compare_lt_trans.lean"
    postlude "descr/opt_union_element_top.lean"
    postlude "descr/tuple3_eq.lean"
    postlude "descr/opt_intersection_basic.lean"
    postlude "descr/map_opt_negation_values.lean"
    postlude "descr/map_opt_intersection_negation.lean"
    postlude "descr/bdd_line_valuations.lean"
    postlude "descr/tuple_opt_intersection_values.lean"
    postlude "descr/bdd_compare_differences.lean"
    postlude "descr/element_disjoint.lean"
    postlude "descr/list_differences_values.lean"
    postlude "descr/flat_field_differences.lean"
    postlude "descr/flat_differences.lean"
    postlude "descr/sorted_keys.lean"
    postlude "descr/literal_heights.lean"
    postlude "descr/flat_elements.lean"
    postlude "descr/tuple_opt_union_elements.lean"
    postlude "descr/tuple_fuse_elements.lean"
    postlude "descr/tuple_opt_intersection_elements.lean"
    postlude "descr/tuple_differences_values.lean"
    postlude "descr/tuple_emptiness_sound.lean"
    postlude "descr/node_tuple_fields.lean"
    postlude "descr/tuple_emptiness_exact.lean"
    postlude "descr/tuple_heights.lean"
    postlude "descr/structural_kinds.lean"
    postlude "descr/list_emptiness_sound.lean"
    postlude "descr/list_emptiness_exact.lean"
    postlude "descr/list_plain_operations.lean"
    postlude "descr/list_opt_union_intersection.lean"
    postlude "descr/list_opt_difference.lean"
    postlude "descr/list_kind.lean"
    postlude "descr/kind_fields.lean"
    postlude "descr/kind_operations.lean"
    postlude "descr/kind_emptiness.lean"
    postlude "descr/kind_congruence.lean"
    postlude "descr/kind_subtype_disjoint.lean"
    postlude "descr/value_maps.lean"
    postlude "descr/map_line_completeness.lean"
    postlude "descr/map_literal_intersections.lean"
    postlude "descr/map_bdd_emptiness.lean"
    postlude "descr/map_opt_union_literals.lean"
    postlude "descr/map_opt_union_types.lean"
    postlude "descr/map_opt_intersection_elements.lean"
    postlude "descr/map_opt_negation_elements.lean"
    postlude "descr/map_opt_difference_strategy.lean"
    postlude "descr/map_differences_values.lean"
    postlude "descr/map_opt_difference_literals.lean"
    postlude "descr/map_emptiness_sound_fields.lean"
    postlude "descr/map_emptiness_sound.lean"
    postlude "descr/map_emptiness_exact.lean"
    postlude "descr/map_heights.lean"
    postlude "descr/map_field_elements.lean"
    postlude "descr/map_kind.lean"
    postlude "descr/bottom_level.lean"
    postlude "descr/function_values.lean"
    postlude "descr/term_list_positions.lean"
    postlude "descr/phi_terms.lean"
    postlude "descr/phi_cache.lean"
    postlude "descr/phi_skip.lean"
    postlude "descr/phi_empty_sets.lean"
    postlude "descr/phi_positive_arrows.lean"
    postlude "descr/phi_run.lean"
    postlude "descr/arrow_application.lean"
    postlude "descr/function_checks.lean"
    postlude "descr/function_type_values.lean"
    postlude "descr/element_top_function.lean"
    postlude "descr/function_element_types.lean"
    postlude "descr/top_type_operands.lean"
    postlude "descr/next_level_elements.lean"
    postlude "descr/next_level_fuse.lean"
    postlude "descr/function_check_elements.lean"
    postlude "descr/level_step.lean"
    postlude "descr/node_elements.lean"
    postlude "descr/levels.lean"
    postlude "descr/empty_no_points.lean"
    postlude "descr/top_level_types.lean"
    postlude "descr/keyed_elements.lean"
    postlude "descr/top_type_levels.lean"
    postlude "descr/keyed_specification.lean"
    postlude "descr/plain_top_laws.lean"
    postlude "descr/merge_fields.lean"
    postlude "descr/gradual_types.lean"
    postlude "descr/gradual_unions.lean"
    postlude "descr/gradual_intersections.lean"
    postlude "descr/gradual_differences.lean"
    postlude "descr/gradual_negations.lean"
    postlude "descr/gradual_subtype_complete.lean"
    postlude "descr/gradual_laws.lean"
    postlude "descr/top_level_emptiness_sound.lean"
    postlude "descr/gradual_negation_bounds.lean"

    # Compatibility only checks emptiness, inclusion, and disjointness of the bounds of gradual types, which are
    # exact on the element types of the next level, whose function types are the top one.
    postlude "descr/gradual_compatibility.lean"
    postlude "descr/arrow_subtype_order.lean"
    postlude "descr/arrow_union_intersection.lean"
    postlude "descr/arrow_difference_negation.lean"
    postlude "descr/tuple_fetch_elements.lean"
    postlude "descr/tuple_fetch_lines.lean"
    postlude "descr/tuple_fetch.lean"
    postlude "descr/map_split_key.lean"
    postlude "descr/map_move_key.lean"
    postlude "descr/map_lines.lean"
    postlude "descr/map_split_pairs.lean"
    postlude "descr/map_pop_key.lean"
    postlude "descr/map_fetch.lean"
    postlude "descr/tuple_insert_elements.lean"
    postlude "descr/tuple_positive_literals.lean"
    postlude "descr/tuple_insert.lean"
    postlude "descr/tuple_insert_at.lean"
    postlude "descr/tuple_delete.lean"
    postlude "descr/tuple_replace.lean"

    # The top function type of an arity is the arrow from that many arguments of none() to term():
    # removing the arrow leaves a line whose only negative literal is the arrow itself, which phi covers.
    postlude "descr/function_arity.lean"
    postlude "descr/map_get_keys.lean"
    postlude "descr/map_set_key.lean"
    postlude "descr/map_split_keys.lean"
    postlude "descr/map_static_get.lean"
    postlude "descr/map_get.lean"
    postlude "descr/bitmap_key_kinds.lean"
    postlude "descr/point_key_kinds.lean"
    postlude "descr/map_union_points.lean"
    postlude "descr/key_types.lean"
    postlude "descr/lists_sort_compare.lean"
    postlude "descr/lists_sort_merges.lean"
    postlude "descr/lists_ukeymerge2.lean"
    postlude "descr/lists_ukeymerge3.lean"
    postlude "descr/lists_rukeymerge.lean"
    postlude "descr/lists_ukeymergel.lean"
    postlude "descr/lists_ukeysort_1.lean"
    postlude "descr/lists_ukeysort_2.lean"
    postlude "descr/lists_ukeysort.lean"
    postlude "descr/lists_umerge.lean"
    postlude "descr/lists_rumerge.lean"
    postlude "descr/lists_umergel.lean"
    postlude "descr/lists_usort_1.lean"
    postlude "descr/lists_usort_2.lean"
    postlude "descr/lists_usort.lean"
    postlude "descr/open_map_domain.lean"
    postlude "descr/maps_of_points.lean"
    postlude "descr/open_map_subtype.lean"
    postlude "descr/tuple_list_constructors.lean"
    postlude "descr/tuple_values.lean"
    postlude "descr/points_above.lean"
    postlude "descr/map_line_pairs.lean"
    postlude "descr/single_atom.lean"
    # Putting a key into map types pops the key from the lines of their maps, unites the remaining maps, and stores
    # the key into every literal of the result, and into the open map that ends the paths without a positive literal.
    postlude "descr/map_put_key.lean"
    postlude "descr/map_swap_keys.lean"
    postlude "descr/optional_fields.lean"
    postlude "descr/map_dnf_nonempty.lean"
    postlude "descr/map_to_list.lean"
    postlude "descr/map_to_list_pairs.lean"
    postlude "descr/key_sorted_lists.lean"
    postlude "descr/map_pairs_fold.lean"
    postlude "descr/map_descr_pairs.lean"
    postlude "descr/map_constructor_values.lean"
    postlude "descr/map_constructor_run.lean"
    postlude "descr/open_map_atom_key.lean"

    # Static function application normalizes the function into the positive arrows of its non-empty lines,
    # checks the arguments against their domains, and applies the arrows to the arguments.
    postlude "descr/function_apply.lean"

    # Gradual function application unites the application of the static arrows to the lower bounds of the arguments
    # with the dynamic application of the dynamic arrows to their upper bounds.
    postlude "descr/function_apply_gradual.lean"

    # Putting at any static key type: the union of the puts at finite atoms, the box of the type at the atoms
    # outside a negated set, and widened domains, all determined by the maps of the type.
    postlude "descr/map_put_domain.lean"
    postlude "descr/map_put_values.lean"
    postlude "descr/map_put_gradual.lean"
    postlude "descr/map_update_values.lean"
    postlude "descr/map_update_keep.lean"
    postlude "descr/map_update_delete.lean"
    postlude "descr/map_put_gradual_keys.lean"
    postlude "descr/map_update_box.lean"
    postlude "descr/map_update_widen.lean"
    postlude "descr/map_update_sem.lean"
    postlude "descr/map_update_dnf.lean"
    postlude "descr/map_update_kr.lean"
    postlude "descr/map_update_mono.lean"
    postlude "descr/map_delete_named.lean"
    postlude "descr/map_delete_dnf.lean"
    postlude "descr/map_delete_mono.lean"
    postlude "descr/map_update_found.lean"
    postlude "descr/tuple_gradual.lean"

    law intersection_none_empty(descr),
      requires: descr?(descr),
      expects: Descr.empty?(Descr.bare_intersection(descr, Descr.none())),
      proof: ~LEAN"""
      -- The proofs run from a depth of 100 on.
      refine ⟨100, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_le' deep
      open Lynx Lynx.Term in
      simp only [«intersection_none_empty:requires/1»] at requires
      simp only [Lynx.apply_eq, «intersection_none_empty:ensures/1», Elixir.Module.Types.Descr.«none/0»]
      cases descr with
      | map X =>
        cases dynamic : mapLookup X (.atom "dynamic") with
        | none => simp [intersection_none_static (δ + 99) X dynamic, empty_none]
        | some Dy =>
          have inner : Dy = .atom "term" ∨ ∃ Y, Dy = .map Y := by
            simp [«descr?/1», getMapKeys_single, dynamic, Erlang.erlang.«==/2», Erlang.erlang.«is_map/1»] at requires
            cases Dy <;> simp_all
          simp [intersection_none_dynamic (δ + 99) X Dy dynamic inner, empty_none]
      | atom name =>
        by_cases top : name = "term"
        · subst top
          unfold Elixir.Module.Types.Descr.«bare_intersection/2»
          simp [empty_none]
        · simp [«descr?/1», top, Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      | _ => simp [«descr?/1», Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      """

    law intersection_negation_empty(descr, depth, node),
      requires: (negatable?(descr, {depth, node}) or arrows_gradual?(descr, {depth, node})) and depth?(depth),
      expects: Descr.empty?(Descr.lower_bound(Descr.bare_intersection(descr, Descr.bare_negation(descr)))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_negation_empty:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_negation_empty:requires/3», Term.true, Lynx.Except.orElse_eq_true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      simp only [Lynx.apply_eq, «intersection_negation_empty:ensures/3»]
      rcases requires with static | ⟨-, gradual⟩
      · rcases Nest.negatable_cases node d descr (by simpa [Term.true] using static) with rfl | ⟨X, rfl, valid⟩
        · simp [negation_term_none, inter_term_left, Nest.lower_bound_run, Nest.lower, Nest.rmDyn, empty_none]
        obtain ⟨ops, -, -, -, -⟩ := closed_ok node d
        replace valid := valid.mono (nest_closed node d)
        by_cases empty : X = []
        · subst empty
          have negation : Elixir.Module.Types.Descr.«bare_negation/1»
              (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map []) = .ok (.atom "term") := by
            simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
            unfold Elixir.Module.Types.Descr.«bare_difference/2»
            simp [Erlang.erlang.«==/2»]
          have intersection : Elixir.Module.Types.Descr.«bare_intersection/2»
              (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map []) (.atom "term") = .ok (.map []) := by
            unfold Elixir.Module.Types.Descr.«bare_intersection/2»
            rfl
          simp [negation, intersection, Nest.lower_bound_run, Nest.lower, Nest.rmDyn, empty_none]
        · obtain ⟨N, negation, static, bitmaps, atoms, funs, lists, tuples, maps, -⟩ :=
            negation_fields ops (δ + 98) X valid empty
          obtain ⟨I, run, only⟩ := intersection_disjoint (δ + 99) X N valid static bitmaps atoms
            (fun x y hx hy => funs x y hx hy (δ + 99)) lists tuples maps
          have staticI : mapLookup I (.atom "dynamic") = Option.none := by
            cases h : mapLookup I (.atom "dynamic") with
            | none => rfl
            | some w => rcases only _ _ h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> simp at e
          simp [negation, run, Nest.lower_bound_run, Nest.lower, Nest.rmDyn_static staticI,
            empty_gone (m := δ + 100) (by omega) I only]
      · have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr gradual
        obtain ⟨n, i, r₁, r₂, r₃, eq⟩ := Nest.gd_inter_neg_lower t (m := δ + 100) (by rw [Nest.level_K]; omega)
        simp [r₁, r₂, r₃, eq]
      """

    law opt_intersection_negation_empty(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.empty?(Descr.lower_bound(Descr.opt_intersection(descr, Descr.opt_negation(descr)))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_intersection_negation_empty:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_intersection_negation_empty:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr requires
      obtain ⟨n, i, r₁, r₂, r₃, eq⟩ := Nest.gd_opt_inter_neg_lower t (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_intersection_negation_empty:ensures/3»]
      simp [r₁, r₂, r₃, eq]
      """

    law union_negation_term(descr, depth, node),
      requires: (negatable?(descr, {depth, node}) or arrows_gradual?(descr, {depth, node})) and depth?(depth),
      expects: Descr.subtype?(Descr.term(), Descr.upper_bound(Descr.bare_union(descr, Descr.bare_negation(descr)))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_negation_term:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_negation_term:requires/3», Term.true, Lynx.Except.orElse_eq_true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      simp only [Lynx.apply_eq, «union_negation_term:ensures/3»]
      rcases requires with static | ⟨-, gradual⟩
      · rcases Nest.negatable_cases node d descr (by simpa [Term.true] using static) with rfl | ⟨X, rfl, valid⟩
        · simp [Elixir.Module.Types.Descr.«term/0», negation_term_none, union_term_l, Nest.upper_bound_term,
            Nest.sub_term_term]
        obtain ⟨ops, -, -, -, -⟩ := closed_ok node d
        replace valid := valid.mono (nest_closed node d)
        by_cases empty : X = []
        · subst empty
          have negation : Elixir.Module.Types.Descr.«bare_negation/1»
              (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map []) = .ok (.atom "term") := by
            simp only [Elixir.Module.Types.Descr.«bare_negation/1»]
            unfold Elixir.Module.Types.Descr.«bare_difference/2»
            simp [Erlang.erlang.«==/2»]
          have union : Elixir.Module.Types.Descr.«bare_union/2»
              (Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map []) (.atom "term") = .ok (.atom "term") := by
            unfold Elixir.Module.Types.Descr.«bare_union/2»
            rfl
          simp [Elixir.Module.Types.Descr.«term/0», negation, union, Nest.upper_bound_term, Nest.sub_term_term]
        · obtain ⟨N, U, negation, union, staticU, sub⟩ := union_negation_covers δ ops (by omega) X valid empty
          simp [Elixir.Module.Types.Descr.«term/0», negation, union, Nest.upper_bound_static staticU, sub]
      · have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr gradual
        obtain ⟨n, u, r₁, r₂, r₃, sub⟩ := Nest.gd_union_neg_upper t (m := δ + 100) (by rw [Nest.level_K]; omega)
        simp [Elixir.Module.Types.Descr.«term/0», r₁, r₂, r₃, sub]
      """

    law opt_union_negation_term(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(Descr.term(), Descr.upper_bound(Descr.opt_union(descr, Descr.opt_negation(descr)))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_union_negation_term:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_union_negation_term:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr requires
      obtain ⟨n, u, r₁, r₂, r₃, sub⟩ := Nest.gd_opt_union_neg_upper t (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_union_negation_term:ensures/3»]
      simp [Elixir.Module.Types.Descr.«term/0», r₁, r₂, r₃, sub]
      """

    law de_morgan_union(left, right, depth, node),
      requires:
        ((negatable?(left, {depth, node}) and negatable?(right, {depth, node})) or
           (arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}))) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_negation(Descr.bare_union(left, right)),
          Descr.bare_intersection(Descr.bare_negation(left), Descr.bare_negation(right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «de_morgan_union:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «de_morgan_union:requires/4», Term.true, Lynx.Except.orElse_eq_true,
        Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      simp only [Lynx.apply_eq, «de_morgan_union:ensures/4»]
      rcases requires with ⟨sl, sr⟩ | ⟨-, gl, gr⟩
      · exact de_morgan_union_any δ (by omega) (Nest.negatable_cases node d left (by simpa [Term.true] using sl))
          (Nest.negatable_cases node d right (by simpa [Term.true] using sr))
      · have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left gl
        have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right gr
        obtain ⟨u, x, nl, nr, y, r₁, r₂, r₃, r₄, r₅, eq⟩ :=
          Nest.gd_de_morgan_union tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
        simp [r₁, r₂, r₃, r₄, r₅, eq]
      """

    law opt_de_morgan_union(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.opt_negation(Descr.opt_union(left, right)),
          Descr.opt_intersection(Descr.opt_negation(left), Descr.opt_negation(right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_de_morgan_union:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_de_morgan_union:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, x, nl, nr, y, r₁, r₂, r₃, r₄, r₅, eq⟩ :=
        Nest.gd_opt_de_morgan_union tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_de_morgan_union:ensures/4»]
      simp [r₁, r₂, r₃, r₄, r₅, eq]
      """

    law opt_de_morgan_intersection(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.opt_negation(Descr.opt_intersection(left, right)),
          Descr.opt_union(Descr.opt_negation(left), Descr.opt_negation(right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_de_morgan_intersection:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_de_morgan_intersection:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨i, x, nl, nr, y, r₁, r₂, r₃, r₄, r₅, eq⟩ :=
        Nest.gd_opt_de_morgan_inter tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_de_morgan_intersection:ensures/4»]
      simp [r₁, r₂, r₃, r₄, r₅, eq]
      """

    law opt_intersection_subtype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.subtype?(Descr.opt_intersection(left, right), left) and
          Descr.subtype?(Descr.opt_intersection(left, right), right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_intersection_subtype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_intersection_subtype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨i, r₁, s₁, s₂⟩ := Nest.gd_opt_inter_sub tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_intersection_subtype:ensures/4»]
      simp [r₁, s₁, s₂]
      """

    law opt_union_supertype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.subtype?(left, Descr.opt_union(left, right)) and
          Descr.subtype?(right, Descr.opt_union(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_union_supertype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_union_supertype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, r₁, s₁, s₂⟩ := Nest.gd_opt_union_sup tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_union_supertype:ensures/4»]
      simp [r₁, s₁, s₂]
      """

    law intersection_subtype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.subtype?(Descr.bare_intersection(left, right), left) and
          Descr.subtype?(Descr.bare_intersection(left, right), right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_subtype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_subtype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨i, r₁, s₁, s₂⟩ := Nest.gd_inter_sub tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «intersection_subtype:ensures/4»]
      simp [r₁, s₁, s₂]
      """

    law union_supertype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.subtype?(left, Descr.bare_union(left, right)) and
          Descr.subtype?(right, Descr.bare_union(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_supertype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_supertype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, r₁, s₁, s₂⟩ := Nest.gd_union_sup tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «union_supertype:ensures/4»]
      simp [r₁, s₁, s₂]
      """

    law opt_union_equal(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(Descr.bare_union(left, right), Descr.opt_union(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_union_equal:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_union_equal:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, w, r₁, r₂, eq⟩ := Nest.gd_union_equal tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_union_equal:ensures/4»]
      simp [r₁, r₂, eq]
      """

    law opt_intersection_equal(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(Descr.bare_intersection(left, right), Descr.opt_intersection(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_intersection_equal:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_intersection_equal:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨i, j, r₁, r₂, eq⟩ := Nest.gd_inter_equal tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_intersection_equal:ensures/4»]
      simp [r₁, r₂, eq]
      """

    law intersection_union_distributive(descr, left, right, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_intersection(descr, Descr.bare_union(left, right)),
          Descr.bare_union(Descr.bare_intersection(descr, left), Descr.bare_intersection(descr, right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_union_distributive:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_union_distributive:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tT := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr (by simpa [Term.true] using requires.1.1)
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1.2)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨u, x, y, z, w, r₁, r₂, r₃, r₄, r₅, eq⟩ :=
        Nest.gd_distrib tT tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «intersection_union_distributive:ensures/5»]
      simp [r₁, r₂, r₃, r₄, r₅, eq]
      """

    law opt_negation_equal(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_negation(descr), Descr.opt_negation(descr)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_negation_equal:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_negation_equal:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have t := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) descr requires
      obtain ⟨x, y, r₁, r₂, eq⟩ := Nest.gd_neg_equal t (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_negation_equal:ensures/3»]
      simp [r₁, r₂, eq]
      """

    law opt_difference_equal(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_difference(left, right), Descr.opt_difference(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «opt_difference_equal:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «opt_difference_equal:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have tL := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) left (by simpa [Term.true] using requires.1)
      have tR := Nest.arrows_gradual_gc (t := node) (m := δ + 100) (n := d) (by rw [Nest.level_K]; omega) right (by simpa [Term.true] using requires.2)
      obtain ⟨x, y, r₁, r₂, eq⟩ := Nest.gd_diff_equal tL tR (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «opt_difference_equal:ensures/4»]
      simp [r₁, r₂, eq]
      """

    law fun_arity_equal(arity),
      requires: is_integer(arity) and arity >= 0,
      expects: Descr.equal?(Descr.fun(arity), Descr.fun(:lists.duplicate(arity, Descr.none()), Descr.term())),
      proof: ~LEAN"""
      open Lynx Lynx.Term in
      obtain ⟨n, rfl⟩ : ∃ n : Nat, arity = .integer n := by
        simp only [«fun_arity_equal:requires/1»] at requires
        cases arity <;> simp [Erlang.erlang.«is_integer/1», Lynx.Except.andAlso, Term.true, Erlang.erlang.«>=/2»,
          Int.isGE_compare] at requires
        rename_i z
        exact ⟨z.toNat, by simp only [Term.integer.injEq]; omega⟩
      -- The proofs run from a depth of 100 on.
      refine ⟨100, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_le' deep
      obtain ⟨right, run, eq⟩ := fun_arity_equal_run n (δ + 100) (by omega)
      simp only [Lynx.apply_eq, «fun_arity_equal:ensures/1»]
      simp [fun_arity_run, Elixir.Module.Types.Descr.«none/0», dup_nat, Elixir.Module.Types.Descr.«term/0», run, eq,
        Term.true]
      """

    law compatible_bounds(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.compatible?(left, right) ==
          (Descr.subtype?(Descr.lower_bound(left), Descr.upper_bound(right)) and not Descr.disjoint?(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «compatible_bounds:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «compatible_bounds:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      obtain ⟨gl, ll, ul⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (by rw [Nest.level_K]; omega) requires.1
      obtain ⟨gr, -, ur⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (by rw [Nest.level_K]; omega) requires.2
      obtain ⟨b, r₁, r₂⟩ := Nest.gd_compatible gl gr ll ul ur (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «compatible_bounds:ensures/4»]
      simp [r₁, Nest.lower_bound_run gl.shape, Nest.upper_bound_run gr.ub, r₂, Erlang.erlang.«==/2», Term.true]
      """

    law subtype_reflexive(descr),
      requires: descr?(descr),
      expects: Descr.subtype?(descr, descr),
      proof: ~LEAN"""
      -- The proofs run from a depth of 1 on.
      refine ⟨1, fun depth _ => ?_⟩
      open Lynx Lynx.Term in
      simp only [«subtype_reflexive:requires/1»] at requires
      simp only [Lynx.apply_eq, «subtype_reflexive:ensures/1»]
      cases descr with
      | map X => simp [Nest.subtype_refl _ (Or.inr ⟨X, rfl⟩), Term.true]
      | atom name =>
        by_cases top : name = "term"
        · subst top; simp [Nest.subtype_refl _ (Or.inl rfl), Term.true]
        · simp [«descr?/1», top, Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      | _ => simp [«descr?/1», Lynx.Term.getMapKeys, Erlang.erlang.«is_map/1»] at requires
      """

    law subtype_transitive(left, middle, right, depth, node),
      requires:
        arrows_gradual?(left, {depth, node}) and arrows_gradual?(middle, {depth, node}) and
          arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        not (Descr.subtype?(left, middle) and Descr.subtype?(middle, right)) or Descr.subtype?(left, right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «subtype_transitive:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «subtype_transitive:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨ga, la, ua⟩ := Nest.arrows_gradual_ok hK requires.1.1
      obtain ⟨gb, lb, ub⟩ := Nest.arrows_gradual_ok hK requires.1.2
      obtain ⟨gc, lc, uc⟩ := Nest.arrows_gradual_ok hK requires.2
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      rw [Lynx.apply_eq, «subtype_transitive:ensures/5», Nest.gd_sub ga gb la ua lb ub hm, Nest.gd_sub gb gc lb ub lc uc hm,
        Nest.gd_sub ga gc la ua lc uc hm]
      by_cases h₁ : Nest.SubN node d (Nest.lower left) (Nest.lower middle) ∧
          Nest.SubN node d (Nest.upper left) (Nest.upper middle)
      · by_cases h₂ : Nest.SubN node d (Nest.lower middle) (Nest.lower right) ∧
            Nest.SubN node d (Nest.upper middle) (Nest.upper right)
        · have h₃ : Nest.SubN node d (Nest.lower left) (Nest.lower right) ∧
              Nest.SubN node d (Nest.upper left) (Nest.upper right) :=
            ⟨fun v h => h₂.1 v (h₁.1 v h), fun v h => h₂.2 v (h₁.2 v h)⟩
          simp [Nest.bp_true.mpr h₁, Nest.bp_true.mpr h₂, Nest.bp_true.mpr h₃, boolAtom, Lynx.Except.andAlso]
        · simp [Nest.bp_true.mpr h₁, Nest.bp_false.mpr h₂, boolAtom, Lynx.Except.andAlso]
      · simp [Nest.bp_false.mpr h₁, boolAtom, Lynx.Except.andAlso]
      """

    law equal_subtype(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(left, right) == (Descr.subtype?(left, right) and Descr.subtype?(right, left)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «equal_subtype:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «equal_subtype:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨gl, ll, ul⟩ := Nest.arrows_gradual_ok hK requires.1
      obtain ⟨gr, lr, ur⟩ := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨s₁, s₂, r₁, r₂, r₃⟩ := Nest.gd_equal gl gr ll ul lr ur (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «equal_subtype:ensures/4»]
      cases s₁ <;> cases s₂ <;> simp [r₁, r₂, r₃, boolAtom, Lynx.Except.andAlso, Erlang.erlang.«==/2», Term.true]
      """

    law disjoint_empty(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.disjoint?(left, right) == Descr.empty?(Descr.bare_intersection(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «disjoint_empty:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «disjoint_empty:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨gl, -, ul⟩ := Nest.arrows_gradual_ok hK requires.1
      obtain ⟨gr, -, ur⟩ := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c, s, run, r₁, r₂⟩ := Nest.gd_disj_empty gl gr ul ur (m := δ + 100) (by rw [Nest.level_K]; omega)
      simp only [Lynx.apply_eq, «disjoint_empty:ensures/4»]
      cases s <;> simp [run, r₁, r₂, boolAtom, Erlang.erlang.«==/2», Term.true]
      """

    law union_commutative(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_union(left, right), Descr.bare_union(right, left)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_commutative:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_commutative:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_union gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_union gr gl hm
      have eq := Nest.gd_eq_true g₁ g₂ (m := δ + 100) (by omega) (fun v => by rw [l₁, l₂]; exact or_comm)
        (fun v => by rw [u₁, u₂]; exact or_comm)
      simp only [Lynx.apply_eq, «union_commutative:ensures/4»]
      simp [r₁, r₂, eq, Term.true]
      """

    law intersection_commutative(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_intersection(left, right), Descr.bare_intersection(right, left)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_commutative:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_commutative:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_inter gr gl hm
      have eq := Nest.gd_eq_true g₁ g₂ (m := δ + 100) (by omega) (fun v => by rw [l₁, l₂]; exact and_comm)
        (fun v => by rw [u₁, u₂]; exact and_comm)
      simp only [Lynx.apply_eq, «intersection_commutative:ensures/4»]
      simp [r₁, r₂, eq, Term.true]
      """

    law union_associative(left, middle, right, depth, node),
      requires:
        arrows_gradual?(left, {depth, node}) and arrows_gradual?(middle, {depth, node}) and
          arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_union(Descr.bare_union(left, middle), right),
          Descr.bare_union(left, Descr.bare_union(middle, right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_associative:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_associative:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1.1
      have gm : Nest.GD node d middle := Nest.arrows_gradual_ok hK requires.1.2
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_union gl gm hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_union g₁ gr hm
      obtain ⟨c₃, r₃, g₃, l₃, u₃⟩ := Nest.gd_union gm gr hm
      obtain ⟨c₄, r₄, g₄, l₄, u₄⟩ := Nest.gd_union gl g₃ hm
      have eq := Nest.gd_eq_true g₂ g₄ (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁, l₄, l₃]; exact or_assoc)
        (fun v => by rw [u₂, u₁, u₄, u₃]; exact or_assoc)
      simp only [Lynx.apply_eq, «union_associative:ensures/5»]
      simp [r₁, r₂, r₃, r₄, eq, Term.true]
      """

    law intersection_associative(left, middle, right, depth, node),
      requires:
        arrows_gradual?(left, {depth, node}) and arrows_gradual?(middle, {depth, node}) and
          arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_intersection(Descr.bare_intersection(left, middle), right),
          Descr.bare_intersection(left, Descr.bare_intersection(middle, right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_associative:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_associative:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1.1
      have gm : Nest.GD node d middle := Nest.arrows_gradual_ok hK requires.1.2
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gl gm hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_inter g₁ gr hm
      obtain ⟨c₃, r₃, g₃, l₃, u₃⟩ := Nest.gd_inter gm gr hm
      obtain ⟨c₄, r₄, g₄, l₄, u₄⟩ := Nest.gd_inter gl g₃ hm
      have eq := Nest.gd_eq_true g₂ g₄ (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁, l₄, l₃]; exact and_assoc)
        (fun v => by rw [u₂, u₁, u₄, u₃]; exact and_assoc)
      simp only [Lynx.apply_eq, «intersection_associative:ensures/5»]
      simp [r₁, r₂, r₃, r₄, eq, Term.true]
      """

    law union_idempotent(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_union(descr, descr), descr),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_idempotent:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_idempotent:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gd : Nest.GD node d descr := Nest.arrows_gradual_ok hK requires
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_union gd gd hm
      have eq := Nest.gd_eq_true g₁ gd (m := δ + 100) (by omega) (fun v => by rw [l₁]; exact or_self_iff)
        (fun v => by rw [u₁]; exact or_self_iff)
      simp only [Lynx.apply_eq, «union_idempotent:ensures/3»]
      simp [r₁, eq, Term.true]
      """

    law intersection_idempotent(descr, depth, node),
      requires: arrows_gradual?(descr, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_intersection(descr, descr), descr),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_idempotent:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_idempotent:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gd : Nest.GD node d descr := Nest.arrows_gradual_ok hK requires
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gd gd hm
      have eq := Nest.gd_eq_true g₁ gd (m := δ + 100) (by omega) (fun v => by rw [l₁]; exact and_self_iff)
        (fun v => by rw [u₁]; exact and_self_iff)
      simp only [Lynx.apply_eq, «intersection_idempotent:ensures/3»]
      simp [r₁, eq, Term.true]
      """

    law union_absorption(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_union(left, Descr.bare_intersection(left, right)), left),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_absorption:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_absorption:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_union gl g₁ hm
      have eq := Nest.gd_eq_true g₂ gl (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁]; exact ⟨fun h => h.elim id And.left, Or.inl⟩)
        (fun v => by rw [u₂, u₁]; exact ⟨fun h => h.elim id And.left, Or.inl⟩)
      simp only [Lynx.apply_eq, «union_absorption:ensures/4»]
      simp [r₁, r₂, eq, Term.true]
      """

    law intersection_absorption(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_intersection(left, Descr.bare_union(left, right)), left),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «intersection_absorption:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «intersection_absorption:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_union gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_inter gl g₁ hm
      have eq := Nest.gd_eq_true g₂ gl (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁]; exact ⟨And.left, fun h => ⟨h, Or.inl h⟩⟩)
        (fun v => by rw [u₂, u₁]; exact ⟨And.left, fun h => ⟨h, Or.inl h⟩⟩)
      simp only [Lynx.apply_eq, «intersection_absorption:ensures/4»]
      simp [r₁, r₂, eq, Term.true]
      """

    law union_intersection_distributive(descr, left, right, depth, node),
      requires:
        arrows_gradual?(descr, {depth, node}) and arrows_gradual?(left, {depth, node}) and
          arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_union(descr, Descr.bare_intersection(left, right)),
          Descr.bare_intersection(Descr.bare_union(descr, left), Descr.bare_union(descr, right))
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «union_intersection_distributive:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «union_intersection_distributive:requires/5», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gd : Nest.GD node d descr := Nest.arrows_gradual_ok hK requires.1.1
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1.2
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c₁, r₁, g₁, l₁, u₁⟩ := Nest.gd_inter gl gr hm
      obtain ⟨c₂, r₂, g₂, l₂, u₂⟩ := Nest.gd_union gd g₁ hm
      obtain ⟨c₃, r₃, g₃, l₃, u₃⟩ := Nest.gd_union gd gl hm
      obtain ⟨c₄, r₄, g₄, l₄, u₄⟩ := Nest.gd_union gd gr hm
      obtain ⟨c₅, r₅, g₅, l₅, u₅⟩ := Nest.gd_inter g₃ g₄ hm
      have eq := Nest.gd_eq_true g₂ g₅ (m := δ + 100) (by omega) (fun v => by rw [l₂, l₁, l₅, l₃, l₄]; exact or_and_left)
        (fun v => by rw [u₂, u₁, u₅, u₃, u₄]; exact or_and_left)
      simp only [Lynx.apply_eq, «union_intersection_distributive:ensures/5»]
      simp [r₁, r₂, r₃, r₄, r₅, eq, Term.true]
      """

    law subtype_union(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(left, right) == Descr.equal?(Descr.bare_union(left, right), right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «subtype_union:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «subtype_union:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c, s, r₁, r₂, r₃⟩ := Nest.gd_sub_union gl gr hm
      simp only [Lynx.apply_eq, «subtype_union:ensures/4»]
      cases s <;> simp [r₁, r₂, r₃, boolAtom, Erlang.erlang.«==/2», Term.true]
      """

    law subtype_intersection(left, right, depth, node),
      requires: arrows_gradual?(left, {depth, node}) and arrows_gradual?(right, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(left, right) == Descr.equal?(Descr.bare_intersection(left, right), left),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «subtype_intersection:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      open Lynx Lynx.Term in
      simp only [Lynx.apply_eq, «subtype_intersection:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      replace requires := requires.1
      have hK : (Nest.level node d).K + 15 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have gl : Nest.GD node d left := Nest.arrows_gradual_ok hK requires.1
      have gr : Nest.GD node d right := Nest.arrows_gradual_ok hK requires.2
      obtain ⟨c, s, r₁, r₂, r₃⟩ := Nest.gd_sub_inter gl gr hm
      simp only [Lynx.apply_eq, «subtype_intersection:ensures/4»]
      cases s <;> simp [r₁, r₂, r₃, boolAtom, Erlang.erlang.«==/2», Term.true]
      """

    law subtype_difference(left, right, depth, node),
      requires: arrows_static?(left, {depth, node}) and arrows_static?(right, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(left, right) == Descr.empty?(Descr.bare_difference(left, right)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      open Lynx Lynx.Term in
      simp only [«subtype_difference:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat requires.2
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      replace requires := requires.1
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dl := Nest.arrows_static_ok requires.1
      have dr := Nest.arrows_static_ok requires.2
      obtain ⟨c, s, r₁, r₂, r₃⟩ := Nest.next_sub_diff dl dr hm
      simp only [Lynx.apply_eq, «subtype_difference:ensures/4»]
      cases s <;> simp [r₁, r₂, r₃, boolAtom, Erlang.erlang.«==/2», Term.true]
      """

    law difference_partition(left, right, depth, node),
      requires: arrows_static?(left, {depth, node}) and arrows_static?(right, {depth, node}) and depth?(depth),
      expects:
        Descr.equal?(
          Descr.bare_union(Descr.bare_difference(left, right), Descr.bare_intersection(left, right)),
          left
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      open Lynx Lynx.Term in
      simp only [«difference_partition:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat requires.2
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      replace requires := requires.1
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dl := Nest.arrows_static_ok requires.1
      have dr := Nest.arrows_static_ok requires.2
      have ef := Nest.ef_next node d
      obtain ⟨c₁, d₁, r₁, s₁, -⟩ := ef.diff dl dr
      obtain ⟨c₂, d₂, r₂, s₂, -⟩ := ef.inter dl dr
      obtain ⟨c₃, d₃, r₃, s₃, -⟩ := ef.union d₁ d₂
      have eq := Nest.next_eq_true d₃ dl hm fun v => by
        rw [s₃, s₁, s₂]
        exact ⟨fun h => h.elim And.left And.left, fun h => (Classical.em _).elim (fun h' => Or.inr ⟨h, h'⟩)
          fun h' => Or.inl ⟨h, h'⟩⟩
      simp only [Lynx.apply_eq, «difference_partition:ensures/4»]
      simp [r₁ _ hm, r₂ _ (by omega), r₃ _ hm, eq, Term.true]
      """

    law difference_disjoint(left, right, depth, node),
      requires: arrows_static?(left, {depth, node}) and arrows_static?(right, {depth, node}) and depth?(depth),
      expects: Descr.disjoint?(Descr.bare_difference(left, right), right),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      open Lynx Lynx.Term in
      simp only [«difference_disjoint:requires/4», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat requires.2
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      replace requires := requires.1
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dl := Nest.arrows_static_ok requires.1
      have dr := Nest.arrows_static_ok requires.2
      obtain ⟨c, dc, run, sem, -⟩ := (Nest.ef_next node d).diff dl dr
      have disj := Nest.next_disj dc dr hm
      rw [Nest.bp_true.mpr fun v h₁ h₂ => ((sem v).mp h₁).2 h₂] at disj
      simp only [Lynx.apply_eq, «difference_disjoint:ensures/4»]
      simp [run _ hm, disj, Term.true]
      """

    law negation_involutive(descr, depth, node),
      requires: arrows_static?(descr, {depth, node}) and depth?(depth),
      expects: Descr.equal?(Descr.bare_negation(Descr.bare_negation(descr)), descr),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      open Lynx Lynx.Term in
      simp only [«negation_involutive:requires/3», Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat requires.2
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      replace requires := requires.1
      have hm : (Nest.level node d).K + 23 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dd := Nest.arrows_static_ok requires
      obtain ⟨c₁, r₁, d₁, s₁⟩ := Nest.next_neg dd hm
      obtain ⟨c₂, r₂, d₂, s₂⟩ := Nest.next_neg d₁ hm
      have eq := Nest.next_eq_true d₂ dd hm fun v => by rw [s₂, s₁]; exact Classical.not_not
      simp only [Lynx.apply_eq, «negation_involutive:ensures/3»]
      simp [r₁, r₂, eq, Term.true]
      """

    law tuple_fetch_sound(tuple, index, depth, node),
      requires:
        arrows_static?(tuple, {depth, node}) and depth?(depth) and is_integer(index) and
          match?({false, _}, Descr.tuple_fetch(tuple, index)),
      expects:
        Descr.subtype?(
          tuple,
          Descr.open_tuple(:lists.duplicate(index, Descr.term()) ++ [elem(Descr.tuple_fetch(tuple, index), 1)])
        ),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_fetch_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_fetch_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨hs, -⟩, hi⟩, hf⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      by_cases neg : z < 0
      · rw [Nest.fetch_neg _ _ neg] at hf; simp at hf
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.fetch_term] at hf; simp at hf
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨e, rfl, he, only, long, s₁, -⟩⟩ :=
        Nest.fetch_tuple (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · rw [run] at hf; simp at hf
      · rw [run] at hf; simp at hf
      have hl : ∀ x ∈ List.replicate i (.atom "term") ++ [e], (Nest.level node d).E x := by
        intro x mx
        rcases List.mem_append.mp mx with mx | mx
        · rw [List.eq_of_mem_replicate mx]; exact (Nest.level node d).ef.term
        · simp at mx; subst mx; exact he
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate i (.atom "term") ++ [e])
        fun x mx => (Nest.level node d).ef.static (hl x mx)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.fused_de (Or.inl rfl) hl key) (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node d (.map X) _ from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_tuple v (only.1 v hv)
        rw [hw X] at hv
        rw [hw, Nest.tt_open_at he i k]
        have lw := long w hv
        have split : w = w.take i ++ w[i] :: w.drop (i + 1) := by simp
        refine ⟨w.take i, w[i], w.drop (i + 1), split, List.length_take_of_le (Nat.le_of_lt lw),
          s₁ (w.take i) w[i] (w.drop (i + 1)) (List.length_take_of_le (Nat.le_of_lt lw)) ?_⟩
        rw [← split]; exact hv)] at sub
      simp only [Lynx.apply_eq, «tuple_fetch_sound:ensures/4»]
      simp only [Elixir.Module.Types.Descr.«term/0», dup_nat, run, Lynx.Except.ok_bind]
      simp [Erlang.erlang.«element/2»]
      rw [append_list, Lynx.Except.ok_bind, rot, Lynx.Except.ok_bind, sub]
      rfl
      """

    law tuple_fetch_least(tuple, index, element, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(element, {depth, node}) and depth?(depth) and
          is_integer(index) and match?({false, _}, Descr.tuple_fetch(tuple, index)) and
          Descr.subtype?(tuple, Descr.open_tuple(:lists.duplicate(index, Descr.term()) ++ [element])),
      expects: Descr.subtype?(elem(Descr.tuple_fetch(tuple, index), 1), element),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the element `d`, so the proofs run from the bound of level `d + 1`
      -- on, and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_fetch_least:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_fetch_least:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hf⟩, hsub⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have del : (Nest.level node (d + 1)).E element := Or.inl (Nest.arrows_static_ok hel)
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      by_cases neg : z < 0
      · rw [Nest.fetch_neg _ _ neg] at hf; simp at hf
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.fetch_term] at hf; simp at hf
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨e, rfl, he, -, -, -, s₂⟩⟩ :=
        Nest.fetch_tuple (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · rw [run] at hf; simp at hf
      · rw [run] at hf; simp at hf
      have hl : ∀ x ∈ List.replicate i (.atom "term") ++ [element], (Nest.level node (d + 1)).E x := by
        intro x mx
        rcases List.mem_append.mp mx with mx | mx
        · rw [List.eq_of_mem_replicate mx]; exact (Nest.level node (d + 1)).ef.term
        · simp at mx; subst mx; exact del
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate i (.atom "term") ++ [element])
        fun x mx => (Nest.level node (d + 1)).ef.static (hl x mx)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.fused_de (Or.inl rfl) hl key) (m := δ + 100) (by omega)
      simp only [Elixir.Module.Types.Descr.«term/0», pure, Except.pure, dup_nat, Lynx.Except.ok_bind] at hsub
      rw [append_list, Lynx.Except.ok_bind, rot, Lynx.Except.ok_bind, sub, Except.ok.injEq] at hsub
      have incl := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have sem : ∀ y, (Nest.level node (d + 1)).den e y → (Nest.level node (d + 1)).den element y := by
        intro y hy
        obtain ⟨v₁, v₂, len, hw⟩ := s₂ y hy
        have := incl _ ((Nest.denD_tpt _).mpr hw)
        rw [Nest.denD_tpt, Nest.tt_open_at del i k] at this
        obtain ⟨w₁, y', w₂, ew, lw, hy'⟩ := this
        obtain ⟨-, e₂⟩ := List.append_inj ew (by omega)
        simp only [List.cons.injEq] at e₂
        rw [e₂.1]; exact hy'
      simp only [Lynx.apply_eq, «tuple_fetch_least:ensures/5»]
      simp [run, Erlang.erlang.«element/2», (Nest.level node (d + 1)).ef.subc he del sem (δ + 100) (by rw [Nest.level_K]; omega),
        Lynx.Term.true]
      """

    law tuple_fetch_badindex(tuple, index, depth, node),
      requires:
        arrows_static?(tuple, {depth, node}) and depth?(depth) and is_integer(index) and index >= 0 and
          Descr.subtype?(tuple, Descr.tuple()) and not Descr.empty?(tuple),
      expects:
        (Descr.tuple_fetch(tuple, index) == :badindex) ==
          not Descr.subtype?(tuple, Descr.open_tuple(:lists.duplicate(index + 1, Descr.term()))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_fetch_badindex:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_fetch_badindex:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨⟨hs, -⟩, hi⟩, hnn⟩, htup⟩, hne⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := by
        refine ⟨z.toNat, ?_⟩
        by_cases neg : z < 0
        · simp [Erlang.erlang.«>=/2», Int.isGE_compare, neg] at hnn
        · omega
      have dt := Nest.arrows_static_ok hs
      have sT := Nest.next_sub dt Nest.tupleTop_de (m := δ + 100) (by omega)
      rw [show Elixir.Module.Types.Descr.«tuple/0» =
        .ok (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) from rfl, Lynx.Except.ok_bind, sT] at htup
      rw [Except.ok.injEq] at htup
      have onlyT := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) htup)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · have := (Nest.tupleTop_den Nest.bitPt).mp (onlyT Nest.bitPt (Nest.denD_term _))
        simp [Nest.bitPt] at this
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      rw [ne] at hne
      have ex : ∃ v : Nest.PN node d, Nest.denD (.map X) v := by
        cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD (.map X) v)
        · exact Classical.byContradiction fun none => by
            have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
            rw [h] at this; cases this
        · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
      have only : Nest.TOnly node d X := by
        refine ⟨fun v hv => (Nest.tupleTop_den v).mp (onlyT v hv), ?_⟩
        obtain ⟨v, hv⟩ := ex
        obtain ⟨w, hw⟩ := Nest.pt_tuple v ((Nest.tupleTop_den v).mp (onlyT v hv))
        exact ⟨w, (hw X).mp hv⟩
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate (i + 1) (.atom "term"))
        fun x mx => by rw [List.eq_of_mem_replicate mx]; exact Or.inl rfl
      have hl : ∀ x ∈ List.replicate (i + 1) (.atom "term"), (Nest.level node d).E x := by
        intro x mx; rw [List.eq_of_mem_replicate mx]; exact (Nest.level node d).ef.term
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.fused_de (Or.inl rfl) hl key) (m := δ + 100) (by omega)
      have subIff : Nest.SubN node d (.map X)
          (.map [(.atom "tuple", .tuple #[.integer k, .atom "open", Lynx.Term.list (List.replicate (i + 1) (.atom "term"))])]) ↔ ∀ w, Nest.TT node d X w → i + 1 ≤ w.length := by
        constructor
        · intro h w hw
          have := h _ ((Nest.denD_tpt w).mpr hw)
          rwa [Nest.denD_tpt, Nest.tt_open] at this
        · intro h v hv
          obtain ⟨w, hw⟩ := Nest.pt_tuple v (only.1 v hv)
          rw [hw X] at hv
          rw [hw, Nest.tt_open]
          exact h w hv
      have dup' : Erlang.lists.«duplicate/2» (.integer ((i : Int) + 1)) (.atom "term") =
          .ok (Lynx.Term.list (List.replicate (i + 1) (.atom "term"))) := by simpa using dup_nat (.atom "term") (i + 1)
      obtain ⟨res, run, ⟨-, nonly⟩ | ⟨rfl, -, w, hw, len⟩ | ⟨e, rfl, -, -, long, -, -⟩⟩ :=
        Nest.fetch_tuple (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · exact absurd only nonly
      · rw [Nest.bp_false.mpr fun h => by have := (subIff.mp h) w hw; omega] at sub
        simp only [Lynx.apply_eq, «tuple_fetch_badindex:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», dup', rot, sub,
          Erlang.erlang.«not/1», Lynx.Term.true]
      · rw [Nest.bp_true.mpr (subIff.mpr fun w hw => long w hw)] at sub
        simp only [Lynx.apply_eq, «tuple_fetch_badindex:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», dup', rot, sub,
          Erlang.erlang.«not/1», Lynx.Term.true]
      """

    law map_fetch_key_sound(map, key, depth, node),
      requires:
        arrows_static?(map, {depth, node}) and depth?(depth) and is_atom(key) and
          match?({false, _}, Descr.map_fetch_key(map, key)),
      expects: Descr.subtype?(map, Descr.open_map([{key, {elem(Descr.map_fetch_key(map, key), 1), false}}])),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_fetch_key_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_fetch_key_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨hs, -⟩, hi⟩, hf⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.fetch_map_term] at hf; simp at hf
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨e, rfl, he, only, s₁, -⟩⟩ :=
        Nest.fetch_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) a (m := δ + 100) hm
      · rw [run] at hf; simp at hf
      · rw [run] at hf; simp at hf
      obtain ⟨k, rom, key⟩ := Nest.open_map_run a ((Nest.level node d).ef.static he) (δ + 99)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.mfused_de (Nest.mleaf_field (Or.inl rfl) (Nest.fieldsV_req he) key))
        (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node d (.map X) _ from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_map v (only.1 v hv)
        rw [hw X] at hv
        rw [hw, Nest.mt_open_at he a k]
        exact s₁ w hv)] at sub
      simp only [Lynx.apply_eq, «map_fetch_key_sound:ensures/4»]
      simp [run, Erlang.erlang.«element/2», rom, sub, Lynx.Term.true]
      """

    law map_fetch_key_least(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key) and match?({false, _}, Descr.map_fetch_key(map, key)) and
          Descr.subtype?(map, Descr.open_map([{key, {value, false}}])),
      expects: Descr.subtype?(elem(Descr.map_fetch_key(map, key), 1), value),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_fetch_key_least:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_fetch_key_least:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hf⟩, hsub⟩ := requires
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have del : (Nest.level node (d + 1)).E value := Or.inl (Nest.arrows_static_ok hel)
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.fetch_map_term] at hf; simp at hf
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨e, rfl, he, -, -, s₂⟩⟩ :=
        Nest.fetch_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a (m := δ + 100) hm
      · rw [run] at hf; simp at hf
      · rw [run] at hf; simp at hf
      obtain ⟨k, rom, key⟩ := Nest.open_map_run a ((Nest.level node (d + 1)).ef.static del) (δ + 99)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.mfused_de (Nest.mleaf_field (Or.inl rfl) (Nest.fieldsV_req del) key))
        (m := δ + 100) (by omega)
      rw [rom, Lynx.Except.ok_bind, sub, Except.ok.injEq] at hsub
      have incl := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have sem : ∀ x, (Nest.level node (d + 1)).den e x → (Nest.level node (d + 1)).den value x := by
        intro x hx
        obtain ⟨w, hw, wa⟩ := s₂ x hx
        have := incl _ ((Nest.denD_mpt w).mpr hw)
        rw [Nest.denD_mpt, Nest.mt_open_at del a k] at this
        obtain ⟨x', wa', hx'⟩ := this
        rw [wa] at wa'
        cases wa'
        exact hx'
      simp only [Lynx.apply_eq, «map_fetch_key_least:ensures/5»]
      simp [run, Erlang.erlang.«element/2», (Nest.level node (d + 1)).ef.subc he del sem (δ + 100) (by rw [Nest.level_K]; omega),
        Lynx.Term.true]
      """

    law map_fetch_key_badkey(map, key, depth, node),
      requires:
        arrows_static?(map, {depth, node}) and depth?(depth) and is_atom(key) and
          Descr.subtype?(map, Descr.open_map()) and not Descr.empty?(map),
      expects:
        (Descr.map_fetch_key(map, key) == :badkey) ==
          not Descr.subtype?(map, Descr.open_map([{key, {Descr.term(), false}}])),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_fetch_key_badkey:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_fetch_key_badkey:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨hs, -⟩, hi⟩, hmap⟩, hne⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      have dt := Nest.arrows_static_ok hs
      have sT := Nest.next_sub dt Nest.mapTop_de (m := δ + 100) (by omega)
      rw [show Elixir.Module.Types.Descr.«open_map/0» =
        .ok (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) from rfl, Lynx.Except.ok_bind, sT,
        Except.ok.injEq] at hmap
      have onlyM := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hmap)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · have := (Nest.mapTop_den Nest.bitPt).mp (onlyM Nest.bitPt (Nest.denD_term _))
        simp [Nest.bitPt] at this
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      rw [ne] at hne
      have ex : ∃ v : Nest.PN node d, Nest.denD (.map X) v := by
        cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD (.map X) v)
        · exact Classical.byContradiction fun none => by
            have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
            rw [h] at this; cases this
        · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
      have only : Nest.MOnly node d X := by
        refine ⟨fun v hv => (Nest.mapTop_den v).mp (onlyM v hv), ?_⟩
        obtain ⟨v, hv⟩ := ex
        obtain ⟨w, hw⟩ := Nest.pt_map v ((Nest.mapTop_den v).mp (onlyM v hv))
        exact ⟨w, (hw X).mp hv⟩
      have hterm : (Nest.level node d).E (.atom "term") := (Nest.level node d).ef.term
      obtain ⟨k, rom, key⟩ := Nest.open_map_run a ((Nest.level node d).ef.static hterm) (δ + 99)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.mfused_de (Nest.mleaf_field (Or.inl rfl) (Nest.fieldsV_req hterm) key))
        (m := δ + 100) (by omega)
      have subIff : Nest.SubN node d (.map X)
          (.map [(.atom "map", .tuple #[.integer k, .atom "open",
            fieldsTerm [(.atom a, .tuple #[.atom "term", .atom "false"])]])]) ↔
          ∀ w, Nest.MT node d X w → w (.atom a) ≠ none := by
        constructor
        · intro h w hw
          have := h _ ((Nest.denD_mpt w).mpr hw)
          rw [Nest.denD_mpt, Nest.mt_open_at hterm a k] at this
          obtain ⟨x, wa, -⟩ := this
          rw [wa]; simp
        · intro h v hv
          obtain ⟨w, hw⟩ := Nest.pt_map v (only.1 v hv)
          rw [hw X] at hv
          rw [hw, Nest.mt_open_at hterm a k]
          cases wa : w (.atom a) with
          | none => exact absurd wa (h w hv)
          | some x => exact ⟨x, rfl, (Nest.level node d).ef.den_term x⟩
      obtain ⟨res, run, ⟨-, nonly⟩ | ⟨rfl, -, w, hw, wa⟩ | ⟨e, rfl, -, -, s₁, -⟩⟩ :=
        Nest.fetch_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) a (m := δ + 100) hm
      · exact absurd only nonly
      · rw [Nest.bp_false.mpr fun h => (subIff.mp h) w hw wa] at sub
        simp only [Lynx.apply_eq, «map_fetch_key_badkey:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», rom, sub, Erlang.erlang.«not/1», Lynx.Term.true]
      · rw [Nest.bp_true.mpr (subIff.mpr fun w hw => by obtain ⟨x, wa, -⟩ := s₁ w hw; rw [wa]; simp)] at sub
        simp only [Lynx.apply_eq, «map_fetch_key_badkey:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», rom, sub, Erlang.erlang.«not/1», Lynx.Term.true]
      """

    law map_put_fetch(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key) and not Descr.empty?(value) and match?({:ok, _}, Descr.map_put_key(map, key, value)),
      expects:
        match?({false, _}, Descr.map_fetch_key(elem(Descr.map_put_key(map, key, value), 1), key)) and
          Descr.equal?(elem(Descr.map_fetch_key(elem(Descr.map_put_key(map, key, value), 1), key), 1), value),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_fetch:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_fetch:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hput⟩ := requires
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del sx (m := δ + 100) hm
      · rw [run] at hput; simp at hput
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The put type holds the maps of the type with the key set to a value of the value type.
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have inY : ∀ y, (Nest.level node (d + 1)).den value y → Nest.MT node (d + 1) Y (Nest.setK a (some y) w₀) := by
        intro y hy
        refine (semY _).mpr ⟨⟨y, by simp [Nest.setK], hy⟩, w₀ (.atom a), ?_⟩
        have e : Nest.setK a (w₀ (.atom a)) (Nest.setK a (some y) w₀) = w₀ := by
          funext k; by_cases h : k = .atom a <;> simp [Nest.setK, h]
        rw [e]; exact hw₀
      obtain ⟨res', fetch, ⟨rfl, nonly⟩ | ⟨rfl, -, w, hw, wa⟩ | ⟨e, rfl, he, -, s₁, s₂⟩⟩ :=
        Nest.fetch_map (t := node) (n := d + 1) dY a hm
      · exact absurd ⟨onlyY, _, inY y₀ hy₀⟩ nonly
      · obtain ⟨⟨x, wx, -⟩, -⟩ := (semY w).mp hw
        rw [wa] at wx; cases wx
      have sem : ∀ y, (Nest.level node (d + 1)).den e y ↔ (Nest.level node (d + 1)).den value y := by
        intro y
        constructor
        · intro hy
          obtain ⟨w, hw, wa⟩ := s₂ y hy
          obtain ⟨⟨x, wx, hx⟩, -⟩ := (semY w).mp hw
          rw [wa] at wx; cases wx; exact hx
        · intro hy
          obtain ⟨x, wx, hx⟩ := s₁ _ (inY y hy)
          simp [Nest.setK] at wx; subst wx; exact hx
      simp only [Lynx.apply_eq, «map_put_fetch:ensures/5», run, Lynx.Except.ok_bind]
      simp [Erlang.erlang.«element/2», fetch, Nest.elem_equal (Nest.level node (d + 1)).ef he del sem (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega), Lynx.Term.true]
      """

    law map_put_other(map, key, other, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key) and is_atom(other) and key != other and not Descr.empty?(value) and
          match?({:ok, _}, Descr.map_put_key(map, key, value)),
      expects:
        (Descr.map_fetch_key(elem(Descr.map_put_key(map, key, value), 1), other) == :badkey) ==
          (Descr.map_fetch_key(map, other) == :badkey) and
          (Descr.map_fetch_key(map, other) == :badkey or
             Descr.equal?(
               elem(Descr.map_fetch_key(elem(Descr.map_put_key(map, key, value), 1), other), 1),
               elem(Descr.map_fetch_key(map, other), 1)
             )),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_other:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_other:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hi₂⟩, hne'⟩, hne⟩, hput⟩ := requires
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨c, rfl⟩ : ∃ c : String, other = .atom c := by
        cases other <;> simp [Erlang.erlang.«is_atom/1»] at hi₂
        exact ⟨_, rfl⟩
      have ac : a ≠ c := by
        rintro rfl
        simp [Erlang.erlang.«/=/2»] at hne'
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del sx (m := δ + 100) hm
      · rw [run] at hput; simp at hput
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      have ka : (Nest.MKey.atom c) ≠ .atom a := fun h => ac (Nest.MKey.atom.inj h).symm
      -- Maps of either type have a map of the other with the same value at the other key.
      have toX : ∀ w, Nest.MT node (d + 1) Y w → ∃ w₀, Nest.MT node (d + 1) X w₀ ∧ w₀ (.atom c) = w (.atom c) := by
        intro w hw
        obtain ⟨-, o, ho⟩ := (semY w).mp hw
        exact ⟨_, ho, by simp [Nest.setK, ka]⟩
      have toY : ∀ w₀, Nest.MT node (d + 1) X w₀ → ∃ w, Nest.MT node (d + 1) Y w ∧ w (.atom c) = w₀ (.atom c) := by
        intro w₀ hw₀
        refine ⟨Nest.setK a (some y₀) w₀, (semY _).mpr ⟨⟨y₀, by simp [Nest.setK], hy₀⟩, w₀ (.atom a), ?_⟩, by
          simp [Nest.setK, ka]⟩
        have e : Nest.setK a (w₀ (.atom a)) (Nest.setK a (some y₀) w₀) = w₀ := by
          funext k; by_cases h : k = .atom a <;> simp [Nest.setK, h]
        rw [e]; exact hw₀
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      obtain ⟨wY, hwY, -⟩ := toY w₀ hw₀
      obtain ⟨rX, fX, ⟨rfl, nX⟩ | ⟨rfl, -, u, hu, ua⟩ | ⟨eX, rfl, heX, -, sX₁, sX₂⟩⟩ :=
        Nest.fetch_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) c hm
      · exact absurd onlyX nX
      · obtain ⟨rY, fY, ⟨rfl, nY⟩ | ⟨rfl, -, -, -, -⟩ | ⟨eY, rfl, -, -, sY₁, -⟩⟩ :=
          Nest.fetch_map (t := node) (n := d + 1) dY c hm
        · exact absurd ⟨onlyY, wY, hwY⟩ nY
        · simp only [Lynx.apply_eq, «map_put_other:ensures/6», run, fX, Lynx.Except.ok_bind]
          simp [Erlang.erlang.«element/2», Erlang.erlang.«==/2», fY, Lynx.Term.true]
        · obtain ⟨w, hw, wc⟩ := toY u hu
          obtain ⟨x, wx, -⟩ := sY₁ w hw
          rw [wc, ua] at wx; cases wx
      · obtain ⟨rY, fY, ⟨rfl, nY⟩ | ⟨rfl, -, u, hu, ua⟩ | ⟨eY, rfl, heY, -, sY₁, sY₂⟩⟩ :=
          Nest.fetch_map (t := node) (n := d + 1) dY c hm
        · exact absurd ⟨onlyY, wY, hwY⟩ nY
        · obtain ⟨w, hw, wc⟩ := toX u hu
          obtain ⟨x, wx, -⟩ := sX₁ w hw
          rw [wc, ua] at wx; cases wx
        have sem : ∀ y, (Nest.level node (d + 1)).den eY y ↔ (Nest.level node (d + 1)).den eX y := by
          intro y
          constructor
          · intro hy
            obtain ⟨w, hw, wc⟩ := sY₂ y hy
            obtain ⟨w', hw', wc'⟩ := toX w hw
            obtain ⟨x, wx, hx⟩ := sX₁ w' hw'
            rw [wc', wc] at wx; cases wx; exact hx
          · intro hy
            obtain ⟨w, hw, wc⟩ := sX₂ y hy
            obtain ⟨w', hw', wc'⟩ := toY w hw
            obtain ⟨x, wx, hx⟩ := sY₁ w' hw'
            rw [wc', wc] at wx; cases wx; exact hx
        simp only [Lynx.apply_eq, «map_put_other:ensures/6», run, fX, Lynx.Except.ok_bind]
        simp [Erlang.erlang.«element/2», Erlang.erlang.«==/2», fY, Nest.elem_equal (Nest.level node (d + 1)).ef heY heX sem
          (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega), Lynx.Term.true]
      """

    law map_put_subtype(left, right, key, small, large, depth, node),
      requires:
        arrows_static?(left, {depth + 1, node}) and arrows_static?(right, {depth + 1, node}) and
          arrows_static?(small, {depth, node}) and arrows_static?(large, {depth, node}) and depth?(depth) and
          is_atom(key) and Descr.subtype?(left, right) and Descr.subtype?(small, large) and
          match?({:ok, _}, Descr.map_put_key(left, key, small)) and
          match?({:ok, _}, Descr.map_put_key(right, key, large)),
      expects:
        Descr.subtype?(
          elem(Descr.map_put_key(left, key, small), 1),
          elem(Descr.map_put_key(right, key, large), 1)
        ),
      proof: ~LEAN"""
      -- The maps nest at most `d + 1` levels and the values `d`, so the proofs run from the bound of level `d + 1` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_subtype:requires/7», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_subtype:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hr⟩, hs⟩, hg⟩, -⟩, hi⟩, hsub⟩, hsubv⟩, hputL⟩, hputR⟩ := requires
      have hl : «arrows_static?/2» left (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hl
      have hr : «arrows_static?/2» right (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hr
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have ds := Nest.arrows_static_ok hs
      have dg := Nest.arrows_static_ok hg
      have es : (Nest.level node (d + 1)).E small := Or.inl ds
      have eg : (Nest.level node (d + 1)).E large := Or.inl dg
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      have static : ∀ {x : Lynx.Term}, Nest.DE (Nest.level node d).E x →
          x = .atom "term" ∨ ∃ Z, x = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := fun h => by
        rcases h with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      -- Values of the small type are values of the large one.
      have subV := Nest.next_sub ds dg (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [subV, Except.ok.injEq] at hsubv
      have subV := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsubv)
      have vals : ∀ y, (Nest.level node (d + 1)).den small y → (Nest.level node (d + 1)).den large y := fun y hy =>
        (Nest.denN_of dg.notT).mpr (subV y ((Nest.denN_of ds.notT).mp hy))
      have dl := Nest.arrows_static_ok hl
      have dr := Nest.arrows_static_ok hr
      -- Maps of the left type are maps of the right one.
      have subM := Nest.next_sub dl dr (m := δ + 100) (by omega)
      rw [subM, Except.ok.injEq] at hsub
      have subM := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      rcases dl with rfl | ⟨XL, rfl, sXL⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hputL
      rcases dr with rfl | ⟨XR, rfl, sXR⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hputR
      have maps : ∀ w, Nest.MT node (d + 1) XL w → Nest.MT node (d + 1) XR w := fun w hw =>
        (Nest.denD_mpt w).mp (subM _ ((Nest.denD_mpt w).mpr hw))
      obtain ⟨resL, runL, ⟨rfl, -⟩ | ⟨YL, rfl, -, dYL, onlyL, semL⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨XL, rfl, sXL⟩) a es (static ds) (m := δ + 100) hm
      · rw [runL] at hputL; simp at hputL
      obtain ⟨resR, runR, ⟨rfl, -⟩ | ⟨YR, rfl, -, dYR, -, semR⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨XR, rfl, sXR⟩) a eg (static dg) (m := δ + 100) hm
      · rw [runR] at hputR; simp at hputR
      have sub := Nest.next_sub dYL dYR (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node (d + 1) (.map YL) (.map YR) from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_map v (onlyL v hv)
        rw [hw] at hv ⊢
        obtain ⟨⟨x, wx, hx⟩, o, ho⟩ := (semL w).mp hv
        exact (semR w).mpr ⟨⟨x, wx, vals x hx⟩, o, maps _ ho⟩)] at sub
      simp only [Lynx.apply_eq, «map_put_subtype:ensures/7»]
      simp [runL, runR, Erlang.erlang.«element/2», sub, Lynx.Term.true]
      """

    law map_put_hold(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key) and not Descr.empty?(value) and match?({:ok, _}, Descr.map_put_key(map, key, value)),
      expects:
        Descr.subtype?(
          Descr.opt_intersection(map, Descr.open_map([{key, {value, false}}])),
          elem(Descr.map_put_key(map, key, value), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_hold:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_hold:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hput⟩ := requires
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del sx (m := δ + 100) hm
      · rw [run] at hput; simp at hput
      -- The maps of the type whose key already holds a value of the type are maps of the put.
      obtain ⟨k, rom, key⟩ := Nest.open_map_run a ((Nest.level node (d + 1)).ef.static del) (δ + 99)
      have dO := Nest.mfused_de (Nest.mleaf_field (Or.inl rfl) (Nest.fieldsV_req (t := node) (n := d + 1) del) key)
      obtain ⟨i, gi, ri, si⟩ := Nest.gc_opt_inter2 (Nest.GC.tc (Or.inr ⟨X, rfl, sX⟩)) (Nest.GC.tc dO) (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      have incl : ∀ v : Nest.PN node (d + 1), Nest.denD (.map X) v → Nest.denD
          (.map [(.atom "map", .tuple #[.integer k, .atom "open", fieldsTerm [(.atom a, .tuple #[value, .atom "false"])]])])
          v → Nest.denD (.map Y) v := by
        intro v hX hO
        have h : v.1.1 = "map" := by
          rw [Nest.denD_map] at hO
          by_cases e : v.1.1 = "map"
          · exact e
          · simp [Lynx.Term.mapLookup, e, Elixir.STTDescrProofsTest.dn_none] at hO
        obtain ⟨w, hw⟩ := Nest.pt_map v h
        rw [hw] at hX hO ⊢
        have e : Nest.setK a (w (.atom a)) w = w := by funext k; by_cases h : k = .atom a <;> simp [Nest.setK, h]
        exact (semY w).mpr ⟨(Nest.mt_open_at del a k w).mp hO, w (.atom a), by rw [e]; exact hX⟩
      have sub := Nest.gc_sub gi (Nest.GC.tc dY) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        (fun v h => incl v ((si.1 v).mp h).1 ((si.1 v).mp h).2) (fun v h => by
          rw [Nest.upper_tc dY]
          have := (si.2 v).mp h
          rw [Nest.upper_tc (Or.inr ⟨X, rfl, sX⟩), Nest.upper_tc dO] at this
          exact incl v this.1 this.2)
      simp only [Lynx.apply_eq, «map_put_hold:ensures/5»]
      simp [run, rom, ri, sub, Erlang.erlang.«element/2», Lynx.Term.true]
      """

    law map_put_idempotent(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key) and not Descr.empty?(value) and match?({:ok, _}, Descr.map_put_key(map, key, value)),
      expects:
        Descr.equal?(
          elem(Descr.map_put_key(elem(Descr.map_put_key(map, key, value), 1), key, value), 1),
          elem(Descr.map_put_key(map, key, value), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_idempotent:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_idempotent:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hput⟩ := requires
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del sx (m := δ + 100) hm
      · rw [run] at hput; simp at hput
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The put type holds the maps of the type with the key set to a value of the value type.
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have inY : ∀ y, (Nest.level node (d + 1)).den value y → Nest.MT node (d + 1) Y (Nest.setK a (some y) w₀) := by
        intro y hy
        refine (semY _).mpr ⟨⟨y, by simp [Nest.setK], hy⟩, w₀ (.atom a), ?_⟩
        have e : Nest.setK a (w₀ (.atom a)) (Nest.setK a (some y) w₀) = w₀ := by
          funext k; by_cases h : k = .atom a <;> simp [Nest.setK, h]
        rw [e]; exact hw₀
      -- Putting the key again sets it to a value of the type in maps whose key already holds one.
      have onlyY' : Nest.MOnly node (d + 1) Y := ⟨onlyY, _, inY y₀ hy₀⟩
      obtain ⟨res₂, run₂, ⟨rfl, nY⟩ | ⟨Y₂, rfl, -, dY₂, onlyY₂, semY₂⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) dY a del sx (m := δ + 100) hm
      · exact absurd onlyY' nY
      have twice : ∀ (o o' : Option (Nest.level node (d + 1)).V) (w : Nest.MW (Nest.level node (d + 1)).V),
          Nest.setK a o' (Nest.setK a o w) = Nest.setK a o' w := fun o o' w => by
        funext k; by_cases h : k = .atom a <;> simp [Nest.setK, h]
      have same : ∀ v : Nest.PN node (d + 1), Nest.denD (.map Y₂) v ↔ Nest.denD (.map Y) v := by
        intro v
        by_cases h : v.1.1 = "map"
        · obtain ⟨w, hw⟩ := Nest.pt_map v h
          rw [hw, hw, semY₂, semY]
          refine and_congr_right fun hp => ⟨fun ⟨o, ho⟩ => ?_, fun ⟨o', ho'⟩ => ?_⟩
          · obtain ⟨-, o', ho'⟩ := (semY _).mp ho
            exact ⟨o', by rwa [twice] at ho'⟩
          · refine ⟨w (.atom a), ?_⟩
            have e : Nest.setK a (w (.atom a)) w = w := by funext k; by_cases h : k = .atom a <;> simp [Nest.setK, h]
            rw [e]
            exact (semY w).mpr ⟨hp, o', ho'⟩
        · exact ⟨fun h' => absurd (onlyY₂ v h') h, fun h' => absurd (onlyY v h') h⟩
      simp only [Lynx.apply_eq, «map_put_idempotent:ensures/5», run, Lynx.Except.ok_bind]
      simp [Erlang.erlang.«element/2», run₂, Nest.next_eq_true dY₂ dY (m := δ + 100) (by omega) same, Lynx.Term.true]
      """

    law map_put_delete(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key) and not Descr.empty?(value) and match?({:ok, _}, Descr.map_put_key(map, key, value)),
      expects:
        Descr.equal?(
          elem(Descr.map_update(elem(Descr.map_put_key(map, key, value), 1), Descr.atom([key]), :delete, :force, false), 1),
          elem(Descr.map_update(map, Descr.atom([key]), :delete, :force, false), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_delete:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_delete:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hput⟩ := requires
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del sx (m := δ + 100) hm
      · rw [run] at hput; simp at hput
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The put type holds the maps of the type with the key set to a value of the value type.
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have inY : ∀ y, (Nest.level node (d + 1)).den value y → Nest.MT node (d + 1) Y (Nest.setK a (some y) w₀) := by
        intro y hy
        refine (semY _).mpr ⟨⟨y, by simp [Nest.setK], hy⟩, w₀ (.atom a), ?_⟩
        have e : Nest.setK a (w₀ (.atom a)) (Nest.setK a (some y) w₀) = w₀ := by
          funext k; by_cases h : k = .atom a <;> simp [Nest.setK, h]
        rw [e]; exact hw₀
      -- Deleting the key from the put type gives the maps of the type without the key, as deleting it from the type.
      have onlyY' : Nest.MOnly node (d + 1) Y := ⟨onlyY, _, inY y₀ hy₀⟩
      obtain ⟨r₁, run₁, ⟨rfl, n₁⟩ | ⟨Y₁, rfl, -, dY₁, only₁, sem₁⟩⟩ := Nest.del_map (t := node) (n := d + 1) dY a hm
      · exact absurd onlyY' n₁
      obtain ⟨r₂, run₂, ⟨rfl, n₂⟩ | ⟨Y₂, rfl, -, dY₂, only₂, sem₂⟩⟩ :=
        Nest.del_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a hm
      · exact absurd onlyX n₂
      have twice : ∀ (o o' : Option (Nest.level node (d + 1)).V) (w : Nest.MW (Nest.level node (d + 1)).V),
          Nest.setK a o' (Nest.setK a o w) = Nest.setK a o' w := fun o o' w => by
        funext k; by_cases h : k = .atom a <;> simp [Nest.setK, h]
      have same : ∀ v : Nest.PN node (d + 1), Nest.denD (.map Y₁) v ↔ Nest.denD (.map Y₂) v := by
        intro v
        by_cases h : v.1.1 = "map"
        · obtain ⟨w, hw⟩ := Nest.pt_map v h
          rw [hw, hw, sem₁, sem₂]
          refine and_congr Iff.rfl ⟨fun ⟨o, ho⟩ => ?_, fun ⟨o', ho'⟩ => ?_⟩
          · obtain ⟨-, o', ho'⟩ := (semY _).mp ho
            exact ⟨o', by rwa [twice] at ho'⟩
          · exact ⟨some y₀, (semY _).mpr ⟨⟨y₀, by simp [Nest.setK], hy₀⟩, o', by rwa [twice]⟩⟩
        · exact ⟨fun h' => absurd (only₁ v h') h, fun h' => absurd (only₂ v h') h⟩
      simp only [Lynx.apply_eq, «map_put_delete:ensures/5», run, Lynx.Except.ok_bind]
      rw [Nest.atom_one a]
      simp [Erlang.erlang.«element/2», run₁, run₂,
        Nest.next_eq_true dY₁ dY₂ (m := δ + 100) (by omega) same, Lynx.Term.true]
      """

    law map_put_domain_subtype(left, right, small_key, large_key, small, large, depth, node),
      requires:
        arrows_static?(left, {depth + 1, node}) and arrows_static?(right, {depth + 1, node}) and
          arrows_static?(small_key, {depth, node}) and arrows_static?(large_key, {depth, node}) and
          arrows_static?(small, {depth, node}) and arrows_static?(large, {depth, node}) and depth?(depth) and
          Descr.subtype?(left, right) and Descr.subtype?(small_key, large_key) and Descr.subtype?(small, large) and
          match?({:ok, _}, Descr.map_put(left, small_key, small)) and
          match?({:ok, _}, Descr.map_put(right, large_key, large)),
      expects:
        Descr.subtype?(
          elem(Descr.map_put(left, small_key, small), 1),
          elem(Descr.map_put(right, large_key, large), 1)
        ),
      proof: ~LEAN"""
      -- The maps nest at most `d + 1` levels, and the keys and values `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_domain_subtype:requires/8», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_domain_subtype:requires/8», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hr⟩, hsk⟩, hlk⟩, hs⟩, hg⟩, -⟩, hsub⟩, hsubk⟩, hsubv⟩, hputL⟩, hputR⟩ := requires
      have hl : «arrows_static?/2» left (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hl
      have hr : «arrows_static?/2» right (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hr
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have ds := Nest.arrows_static_ok hs
      have dg := Nest.arrows_static_ok hg
      have es : (Nest.level node (d + 1)).E small := Or.inl ds
      have eg : (Nest.level node (d + 1)).E large := Or.inl dg
      have static : ∀ {x : Lynx.Term}, Nest.DE (Nest.level node d).E x →
          x = .atom "term" ∨ ∃ Z, x = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := fun h => by
        rcases h with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      -- Values of the small type are values of the large one.
      have subV := Nest.next_sub ds dg (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [subV, Except.ok.injEq] at hsubv
      have subV := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsubv)
      have vals : ∀ y, (Nest.level node (d + 1)).den small y → (Nest.level node (d + 1)).den large y := fun y hy =>
        (Nest.denN_of dg.notT).mpr (subV y ((Nest.denN_of ds.notT).mp hy))
      -- Keys of the small key type are keys of the large one.
      have dsk := Nest.arrows_static_ok hsk
      have dlk := Nest.arrows_static_ok hlk
      have subK := Nest.next_sub dsk dlk (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [subK, Except.ok.injEq] at hsubk
      have subK := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsubk)
      have splitOf : ∀ {k : Lynx.Term}, «arrows_static?/2» k (.tuple #[.integer (d : Int), node]) = .ok (.atom "true") →
          ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) k =
            .ok (Nest.splitT rs neg ds) ∧ Nest.SplitOk rs neg ds ∧ (∀ N, neg = .map N → rs = []) ∧
            (∀ N, neg = .map N → ∀ e ∈ Lynx.Term.mapEntries N, ∃ s, e.1 = .atom s) ∧
            ∀ κ, Nest.SplitKey rs neg ds κ ↔ Nest.KeyPt node d k κ := fun h =>
        Nest.key_split_any (Nest.arrows_static_ok h) (fun Y e => by subst e; exact static_union_atoms h)
          (fun Y e => by subst e; exact static_negation_atoms h) hmk
      obtain ⟨rs₁, neg₁, ds₁, rk₁, ok₁, nr₁, na₁, sk₁⟩ := splitOf hsk
      obtain ⟨rs₂, neg₂, ds₂, rk₂, ok₂, nr₂, na₂, sk₂⟩ := splitOf hlk
      have keys : ∀ κ, Nest.SplitKey rs₁ neg₁ ds₁ κ → Nest.SplitKey rs₂ neg₂ ds₂ κ := fun κ h =>
        (sk₂ κ).mpr (Nest.keyPt_mono subK ((sk₁ κ).mp h))
      -- Maps of the left type are maps of the right one.
      have dl := Nest.arrows_static_ok hl
      have dr := Nest.arrows_static_ok hr
      have subM := Nest.next_sub dl dr (m := δ + 100) (by omega)
      rw [subM, Except.ok.injEq] at hsub
      have subM := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      rcases dl with rfl | ⟨XL, rfl, sXL⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hputL
      rcases dr with rfl | ⟨XR, rfl, sXR⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hputR
      have maps : ∀ w, Nest.MT node (d + 1) XL w → Nest.MT node (d + 1) XR w := fun w hw =>
        (Nest.denD_mpt w).mp (subM _ ((Nest.denD_mpt w).mpr hw))
      obtain ⟨resL, runL, ⟨rfl, -⟩ | ⟨YL, rfl, -, dYL, onlyL, semL⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) (Or.inr ⟨XL, rfl, sXL⟩) rk₁ ok₁ nr₁ na₁ es (static ds) hm
      · rw [runL] at hputL; simp at hputL
      obtain ⟨resR, runR, ⟨rfl, -⟩ | ⟨YR, rfl, -, dYR, -, semR⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) (Or.inr ⟨XR, rfl, sXR⟩) rk₂ ok₂ nr₂ na₂ eg (static dg) hm
      · rw [runR] at hputR; simp at hputR
      have sub := Nest.next_sub dYL dYR (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node (d + 1) (.map YL) (.map YR) from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_map v (onlyL v hv)
        rw [hw] at hv ⊢
        exact (semR w).mpr (Nest.put_mono maps vals ok₁ ok₂ nr₂ keys ((semL w).mp hv)))] at sub
      simp only [Lynx.apply_eq, «map_put_domain_subtype:ensures/8»]
      simp [runL, runR, Erlang.erlang.«element/2», sub, Lynx.Term.true]
      """

    law map_put_within(map, atom, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and is_atom(atom) and
          Descr.subtype?(Descr.atom([atom]), key) and match?({:ok, _}, Descr.map_put_key(map, atom, value)) and
          match?({:ok, _}, Descr.map_put(map, key, value)),
      expects: Descr.subtype?(elem(Descr.map_put_key(map, atom, value), 1), elem(Descr.map_put(map, key, value), 1)),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_within:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_within:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hmp, hk⟩, hv⟩, -⟩, ha⟩, hsub⟩, hputK⟩, hput⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      obtain ⟨s, rfl⟩ : ∃ s, atom = .atom s := by
        cases atom <;> simp [Erlang.erlang.«is_atom/1»] at ha
        exact ⟨_, rfl⟩
      -- The atom is a key of the key type.
      have dk := Nest.arrows_static_ok hk
      have subA := Nest.next_sub (Nest.atomT_de s) dk (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [Nest.atom_one, Lynx.Except.ok_bind, subA, Except.ok.injEq] at hsub
      have subA := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have keyA : Nest.KeyPt node d key (.atom s) :=
        subA _ ((Nest.atomT_den s _).mpr ⟨rfl, rfl⟩)
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hputK
      obtain ⟨res₁, run₁, ⟨rfl, -⟩ | ⟨Y₁, rfl, -, dY₁, only₁, sem₁⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) s ev sv (m := δ + 100) (by omega)
      · rw [run₁] at hputK; simp at hputK
      obtain ⟨res₂, run₂, ⟨rfl, -⟩ | ⟨Y₂, rfl, -, dY₂, -, sem₂⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rk ok nr na ev sv hm
      · rw [run₂] at hput; simp at hput
      -- The single atom is a split whose keys are keys of the split of the key type.
      have ok₁ : Nest.SplitOk [.atom s] (.atom "nil") [] :=
        ⟨by simp, Or.inl rfl, by simp, by simp⟩
      have keys : ∀ κ, Nest.SplitKey [.atom s] (.atom "nil") [] κ → Nest.SplitKey rs neg ds κ := by
        intro κ h
        cases κ with
        | atom s' =>
          rcases h with h | ⟨N, e, -⟩
          · simp at h; subst h; exact (sk _).mpr keyA
          · cases e
        | dom k i => simp [Nest.SplitKey] at h
      have sub := Nest.next_sub dY₁ dY₂ (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node (d + 1) (.map Y₁) (.map Y₂) from fun q hq => by
        obtain ⟨w, hw⟩ := Nest.pt_map q (only₁ q hq)
        rw [hw] at hq ⊢
        obtain ⟨pa, o, hX⟩ := (sem₁ w).mp hq
        exact (sem₂ w).mpr (Nest.put_mono (fun u h => h) (fun x h => h) ok₁ ok nr keys
          (Or.inl ⟨rfl, Or.inl ⟨s, by simp, pa, o, hX⟩⟩)))] at sub
      simp only [Lynx.apply_eq, «map_put_within:ensures/6»]
      simp [run₁, run₂, Erlang.erlang.«element/2», sub, Lynx.Term.true]
      """

    law map_put_get(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and not Descr.empty?(key) and
          not Descr.empty?(value) and match?({:ok, _}, Descr.map_put(map, key, value)) and
          not Descr.empty?(elem(Descr.map_put(map, key, value), 1)),
      expects:
        Descr.subtype?(value, got(Descr.map_get(elem(Descr.map_put(map, key, value), 1), key))) and
          Descr.subtype?(
            got(Descr.map_get(elem(Descr.map_put(map, key, value), 1), key)),
            Descr.bare_union(value, got(Descr.map_get(map, key)))
          ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_get:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_get:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hmp, hk⟩, hv⟩, -⟩, -⟩, hnv⟩, hput⟩, hne⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rk ok nr na ev sv hm
      · rw [run] at hput; simp at hput
      have ef := (Nest.level node (d + 1)).ef
      -- The value has values.
      obtain ⟨x₀, hx₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hnv
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hnv; simp [Erlang.erlang.«not/1»] at hnv
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The put holds a map, which selects a key.
      obtain ⟨w₀, hw₀⟩ : ∃ w, Nest.MT node (d + 1) Y w := by
        refine Nest.nonempty_map dY onlyY (m := δ + 100) (by omega) ?_
        have e := Nest.next_empty dY (m := δ + 100) (by omega)
        rw [e]
        cases hb : Nest.bp (∀ v : Nest.PN node (d + 1), ¬Nest.denD (.map Y) v)
        · rfl
        · rw [hb] at e
          simp [run, Erlang.erlang.«element/2», e, boolAtom, Erlang.erlang.«not/1»] at hne
      obtain ⟨κ₀, hκ₀⟩ := Nest.put_selects ((semY w₀).mp hw₀)
      obtain ⟨u₀, hu₀⟩ := onlyX.2
      have wit : ∀ x, (Nest.level node (d + 1)).den value x → Nest.MT node (d + 1) Y (Nest.updK κ₀ x u₀) := fun x hx =>
        (semY _).mpr (Nest.put_witness ok nr hu₀ hκ₀ hx)
      -- The values at the keys after the put.
      obtain ⟨resY, runY, ⟨-, nY⟩ | ⟨-, -, eY⟩ | ⟨T, rfl, hT, -, -, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) dY ok (m := δ + 100) (by omega) rk
      · exact absurd ⟨onlyY, w₀, hw₀⟩ nY
      · have := eY _ (wit x₀ hx₀) κ₀ hκ₀
        rw [Nest.updK_same] at this; cases this
      -- The values at the keys before the put.
      obtain ⟨resX, T₀, hT₀, runX, gX, sT₀⟩ : ∃ resX T₀, (Nest.level node (d + 1)).E T₀ ∧
          Elixir.Module.Types.Descr.«map_get/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) key = .ok resX ∧ «got/1» resX = .ok T₀ ∧
          ∀ y, (Nest.level node (d + 1)).den T₀ y ↔
            ∃ u κ, Nest.MT node (d + 1) X u ∧ Nest.SplitKey rs neg ds κ ∧ u κ = some y := by
        obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨T₀, rfl, hT₀, -, -, sT₀⟩⟩ :=
          Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok (m := δ + 100) (by omega) rk
        · exact absurd onlyX nX
        · refine ⟨_, .map [], ef.none, runX, by simp [«got/1», Elixir.Module.Types.Descr.«none/0»], fun y => ?_⟩
          simp only [ef.den_none y, false_iff]
          rintro ⟨u, κ, hu, hκ, e⟩
          rw [eX u hu κ hκ] at e; cases e
        · exact ⟨_, T₀, hT₀, runX, by simp [«got/1», pure, Except.pure], fun y => by
            rw [sT₀ y]
            constructor
            · rintro ⟨u, hu, κ, hκ, e⟩; exact ⟨u, κ, hu, hκ, e⟩
            · rintro ⟨u, κ, hu, hκ, e⟩; exact ⟨u, hu, κ, hκ, e⟩⟩
      obtain ⟨c, hc, rc, sc, -⟩ := ef.union ev hT₀
      have sub₁ := ef.subc ev hT (fun y hy => (sT y).mpr ⟨_, wit y hy, κ₀, hκ₀, Nest.updK_same _ _ _⟩) (δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      have sub₂ := ef.subc hT hc (fun y hy => by
        obtain ⟨w, hw, κ, hκ, e⟩ := (sT y).mp hy
        rw [sc]
        rcases Nest.put_upper ((semY w).mp hw) hκ e with h | ⟨u, κ', hu, hκ', e'⟩
        · exact Or.inl h
        · exact Or.inr ((sT₀ y).mpr ⟨u, κ', hu, hκ', e'⟩)) (δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      have rY : Elixir.Module.Types.Descr.«map_get/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map Y) key =
          .ok (.tuple #[.atom "ok", T]) := runY
      have gY : «got/1» (.tuple #[.atom "ok", T]) = .ok T := rfl
      simp only [Lynx.apply_eq, «map_put_get:ensures/5»]
      simp [run, Erlang.erlang.«element/2», rY, gY, runX, gX, rc (δ + 100) (by rw [Nest.level_K] at hm ⊢; omega), sub₁, sub₂,
        Lynx.Term.true]
      """

    law map_put_other_atom(map, key, other, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and is_atom(other) and
          Descr.disjoint?(Descr.atom([other]), key) and match?({:ok, _}, Descr.map_put(map, key, value)) and
          not Descr.empty?(elem(Descr.map_put(map, key, value), 1)),
      expects:
        same_fetch?(Descr.map_fetch_key(elem(Descr.map_put(map, key, value), 1), other), Descr.map_fetch_key(map, other)),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_other_atom:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_other_atom:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hmp, hk⟩, hv⟩, -⟩, ha⟩, hdis⟩, hput⟩, hne⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rk ok nr na ev sv hm
      · rw [run] at hput; simp at hput
      have ef := (Nest.level node (d + 1)).ef
      -- The put holds a map, which selects a key.
      obtain ⟨w₀, hw₀⟩ : ∃ w, Nest.MT node (d + 1) Y w := by
        refine Nest.nonempty_map dY onlyY (m := δ + 100) (by omega) ?_
        have e := Nest.next_empty dY (m := δ + 100) (by omega)
        rw [e]
        cases hb : Nest.bp (∀ v : Nest.PN node (d + 1), ¬Nest.denD (.map Y) v)
        · rfl
        · rw [hb] at e
          simp [run, Erlang.erlang.«element/2», e, boolAtom, Erlang.erlang.«not/1»] at hne
      obtain ⟨κ₀, hκ₀⟩ := Nest.put_selects ((semY w₀).mp hw₀)
      obtain ⟨s, rfl⟩ : ∃ s, other = .atom s := by
        cases other <;> simp [Erlang.erlang.«is_atom/1»] at ha
        exact ⟨_, rfl⟩
      -- The atom is not a selected key.
      have disA := Nest.next_disj (Nest.atomT_de s) dk (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [Nest.atom_one, Lynx.Except.ok_bind, disA, Except.ok.injEq] at hdis
      have disA := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hdis)
      have notA : ¬Nest.SplitKey rs neg ds (.atom s) := fun h =>
        disA _ ((Nest.atomT_den s _).mpr ⟨rfl, rfl⟩) ((sk _).mp h)
      obtain ⟨x₀, hx₀⟩ := Nest.put_value ((semY w₀).mp hw₀)
      have neA : κ₀ ≠ .atom s := fun e => notA (e ▸ hκ₀)
      have wit : ∀ u, Nest.MT node (d + 1) X u → Nest.MT node (d + 1) Y (Nest.updK κ₀ x₀ u) ∧
          Nest.updK κ₀ x₀ u (.atom s) = u (.atom s) := fun u hu =>
        ⟨(semY _).mpr (Nest.put_witness ok nr hu hκ₀ hx₀), Nest.updK_other (Ne.symm neA) _ _⟩
      have back : ∀ w, Nest.MT node (d + 1) Y w → ∃ u, Nest.MT node (d + 1) X u ∧ u (.atom s) = w (.atom s) :=
        fun w hw => Nest.put_other_atom ((semY w).mp hw) notA
      obtain ⟨resY, runY, ⟨-, nY⟩ | ⟨rfl, -, wY, hwY, eY⟩ | ⟨eY, rfl, heY, -, aY, bY⟩⟩ :=
        Nest.fetch_map (t := node) (n := d + 1) dY s (m := δ + 100) (by omega)
      · exact absurd ⟨onlyY, w₀, hw₀⟩ nY
      · obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, -⟩ | ⟨eX, rfl, -, -, aX, -⟩⟩ :=
          Nest.fetch_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) s (m := δ + 100) (by omega)
        · exact absurd onlyX nX
        · simp only [Lynx.apply_eq, «map_put_other_atom:ensures/6»]
          simp [run, Erlang.erlang.«element/2», runY, runX, «same_fetch?/2», Erlang.erlang.«==/2», Lynx.Term.true]
        · obtain ⟨u, hu, e⟩ := back wY hwY
          obtain ⟨x, ux, -⟩ := aX u hu
          rw [e, eY] at ux; cases ux
      · obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, u, hu, eu⟩ | ⟨eX, rfl, heX, -, aX, bX⟩⟩ :=
          Nest.fetch_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) s (m := δ + 100) (by omega)
        · exact absurd onlyX nX
        · obtain ⟨hw, e⟩ := wit u hu
          obtain ⟨x, wx, -⟩ := aY _ hw
          rw [e, eu] at wx; cases wx
        · have sem : ∀ y, (Nest.level node (d + 1)).den eY y ↔ (Nest.level node (d + 1)).den eX y := by
            intro y
            constructor
            · intro hy
              obtain ⟨w, hw, wy⟩ := bY y hy
              obtain ⟨u, hu, e⟩ := back w hw
              obtain ⟨x, ux, hx⟩ := aX u hu
              rw [e, wy] at ux; cases ux; exact hx
            · intro hy
              obtain ⟨u, hu, uy⟩ := bX y hy
              obtain ⟨hw, e⟩ := wit u hu
              obtain ⟨x, wx, hx⟩ := aY _ hw
              rw [e, uy] at wx; cases wx; exact hx
          simp only [Lynx.apply_eq, «map_put_other_atom:ensures/6»]
          simp [run, Erlang.erlang.«element/2», runY, runX, «same_fetch?/2»,
            Nest.elem_equal (Nest.level node (d + 1)).ef heY heX sem (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega),
            Lynx.Term.true]
      """

    law map_put_other_kind(map, key, kind, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and keys?([], [kind]) and
          Descr.disjoint?(key_type([], [kind]), key) and match?({:ok, _}, Descr.map_put(map, key, value)) and
          not Descr.empty?(elem(Descr.map_put(map, key, value), 1)),
      expects:
        same_get?(
          Descr.map_get(elem(Descr.map_put(map, key, value), 1), key_type([], [kind])),
          Descr.map_get(map, key_type([], [kind]))
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_other_kind:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_other_kind:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hmp, hk⟩, hv⟩, -⟩, hks⟩, hdis⟩, hput⟩, hne⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rk ok nr na ev sv hm
      · rw [run] at hput; simp at hput
      have ef := (Nest.level node (d + 1)).ef
      -- The put holds a map, which selects a key.
      obtain ⟨w₀, hw₀⟩ : ∃ w, Nest.MT node (d + 1) Y w := by
        refine Nest.nonempty_map dY onlyY (m := δ + 100) (by omega) ?_
        have e := Nest.next_empty dY (m := δ + 100) (by omega)
        rw [e]
        cases hb : Nest.bp (∀ v : Nest.PN node (d + 1), ¬Nest.denD (.map Y) v)
        · rfl
        · rw [hb] at e
          simp [run, Erlang.erlang.«element/2», e, boolAtom, Erlang.erlang.«not/1»] at hne
      obtain ⟨κ₀, hκ₀⟩ := Nest.put_selects ((semY w₀).mp hw₀)
      -- The kind's key type.
      obtain ⟨as, ks, -, eks, -, hks'⟩ := Nest.keys_ok hks
      have eks' := Elixir.STTDescrProofsTest.list_inj eks
      subst eks'
      obtain ⟨s, ms, rfl⟩ := hks' kind (by simp)
      obtain ⟨KY, rsK, negK, dsK, rKY, rSK, okK, skK⟩ :=
        Nest.key_split (t := node) (n := d) [] [.atom s] (by simp) hks' (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      obtain ⟨KY', rKY', inv⟩ := Nest.key_type_run (t := node) (n := d) [] [.atom s] (by simp) hks' (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      rw [rKY] at rKY'
      simp only [Except.ok.injEq, Lynx.Term.map.injEq] at rKY'
      subst rKY'
      -- No key of the kind is selected by the key type.
      have disK := Nest.next_disj inv.de dk (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [show Elixir.STTDescrProofsTest.«key_type/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
        Lynx.Term.nil (Lynx.Term.list [.atom s]) = .ok (.map KY) from rKY, Lynx.Except.ok_bind, disK, Except.ok.injEq] at hdis
      have disK := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hdis)
      have notSel : ∀ κ, Nest.SplitKey rsK negK dsK κ → ¬Nest.SplitKey rs neg ds κ := by
        intro κ hκ hk'
        rw [skK] at hκ
        rw [sk] at hk'
        cases κ with
        | atom a =>
          simp only [Nest.KeysOf, List.not_mem_nil, false_or, List.mem_singleton, Lynx.Term.atom.injEq] at hκ
          subst hκ
          exact disK _ ((inv.atoms _).mpr (Or.inr (by simp))) hk'
        | dom k i =>
          simp only [Nest.KeysOf, List.mem_singleton, Lynx.Term.atom.injEq] at hκ
          subst hκ
          obtain ⟨q, hq, pq⟩ := hk'
          have na : Nest.domKind k ≠ "atom" := by
            match k with
            | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => decide
          obtain ⟨T, rT, fT⟩ := Nest.kind_full (t := node) (n := d) ms na (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
          have eKY : KY = T := by
            have : Elixir.STTDescrProofsTest.«key_type/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
                Lynx.Term.nil (Lynx.Term.list [.atom (Nest.domKind k)]) = .ok (.map T) := by
              simp [Elixir.STTDescrProofsTest.«key_type/2», Elixir.STTDescrProofsTest.«kinds_type/2»,
                Elixir.Module.Types.Descr.«none/0», rT, Nest.union_nil_r, pure, Except.pure, Lynx.Term.list]
            rw [rKY] at this
            simpa using this
          subst eKY
          exact disK q (fT q pq) hq
      -- The values of the kind before and after the put agree.
      obtain ⟨x₀, hx₀⟩ := Nest.put_value ((semY w₀).mp hw₀)
      have fwd : ∀ w, Nest.MT node (d + 1) Y w → ∀ κ x, Nest.SplitKey rsK negK dsK κ → w κ = some x →
          ∃ u κ', Nest.MT node (d + 1) X u ∧ Nest.SplitKey rsK negK dsK κ' ∧ u κ' = some x := by
        intro w hw κ x hκ e
        cases κ with
        | atom a =>
          obtain ⟨u, hu, eu⟩ := Nest.put_other_atom ((semY w).mp hw) (notSel _ hκ)
          exact ⟨u, _, hu, hκ, eu.trans e⟩
        | dom k i =>
          obtain ⟨u, j, hu, eu⟩ := Nest.put_other_dom ((semY w).mp hw) (notSel _ hκ) e
          exact ⟨u, _, hu, Nest.splitKey_dom.mp hκ, eu⟩
      have bwd : ∀ u, Nest.MT node (d + 1) X u → ∀ κ x, Nest.SplitKey rsK negK dsK κ → u κ = some x →
          ∃ w κ', Nest.MT node (d + 1) Y w ∧ Nest.SplitKey rsK negK dsK κ' ∧ w κ' = some x := by
        intro u hu κ x hκ e
        have ne : κ ≠ κ₀ := fun h => notSel _ hκ (h ▸ hκ₀)
        exact ⟨_, κ, (semY _).mpr (Nest.put_witness ok nr hu hκ₀ hx₀), hκ, by rw [Nest.updK_other ne]; exact e⟩
      obtain ⟨resY, runY, ⟨-, nY⟩ | ⟨rfl, -, eY⟩ | ⟨TY, rfl, hTY, -, neY, sTY⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) dY okK (m := δ + 100) (by omega) rSK
      · exact absurd ⟨onlyY, w₀, hw₀⟩ nY
      · obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, -⟩ | ⟨TX, rfl, -, -, ⟨x, hx⟩, sTX⟩⟩ :=
          Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) okK (m := δ + 100) (by omega) rSK
        · exact absurd onlyX nX
        · simp only [Lynx.apply_eq, «map_put_other_kind:ensures/6»]
          simp [run, Erlang.erlang.«element/2», rKY, runY, runX, «same_get?/2», Erlang.erlang.«==/2», Lynx.Term.true]
        · obtain ⟨u, hu, κ, hκ, e⟩ := (sTX x).mp hx
          obtain ⟨w, κ', hw, hκ', e'⟩ := bwd u hu κ x hκ e
          rw [eY w hw κ' hκ'] at e'; cases e'
      · obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨TX, rfl, hTX, -, -, sTX⟩⟩ :=
          Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) okK (m := δ + 100) (by omega) rSK
        · exact absurd onlyX nX
        · obtain ⟨x, hx⟩ := neY
          obtain ⟨w, hw, κ, hκ, e⟩ := (sTY x).mp hx
          obtain ⟨u, κ', hu, hκ', e'⟩ := fwd w hw κ x hκ e
          rw [eX u hu κ' hκ'] at e'; cases e'
        · have sem : ∀ y, (Nest.level node (d + 1)).den TY y ↔ (Nest.level node (d + 1)).den TX y := by
            intro y
            rw [sTY, sTX]
            constructor
            · rintro ⟨w, hw, κ, hκ, e⟩
              obtain ⟨u, κ', hu, hκ', e'⟩ := fwd w hw κ y hκ e
              exact ⟨u, hu, κ', hκ', e'⟩
            · rintro ⟨u, hu, κ, hκ, e⟩
              obtain ⟨w, κ', hw, hκ', e'⟩ := bwd u hu κ y hκ e
              exact ⟨w, hw, κ', hκ', e'⟩
          simp only [Lynx.apply_eq, «map_put_other_kind:ensures/6»]
          simp [run, Erlang.erlang.«element/2», rKY, runY, runX, «same_get?/2»,
            Nest.elem_equal (Nest.level node (d + 1)).ef hTY hTX sem (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega),
            Lynx.Term.true]
      """

    law map_update_force_atoms(map, atoms, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          keys?(atoms, []) and atoms != [] and :lists.usort(atoms) == atoms and not Descr.empty?(value) and
          match?({:ok, _}, Descr.map_put(map, Descr.atom(atoms), value)),
      expects:
        match?({_, _, []}, Descr.map_update(map, Descr.atom(atoms), value, :force, true)) and
          Descr.equal?(elem(Descr.map_update(map, Descr.atom(atoms), value, :force, true), 1), puts(map, atoms, value)) and
          Descr.equal?(
            elem(Descr.map_update(map, Descr.atom(atoms), value, :force, true), 0),
            got(Descr.map_get(map, Descr.atom(atoms)))
          ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_force_atoms:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_force_atoms:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hmp, hv⟩, -⟩, hks⟩, hne⟩, -⟩, -⟩, hput⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have ef := (Nest.level node (d + 1)).ef
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      -- The atoms: a non-empty list, whose type is split into exactly those required atoms.
      obtain ⟨as, ks, rfl, eks, ha, -⟩ := Nest.keys_ok hks
      obtain ⟨A, rfl⟩ := Nest.atoms_of ha
      have hA : A ≠ [] := by
        rintro rfl
        simp [Erlang.erlang.«/=/2», Lynx.Term.list] at hne
      obtain ⟨K, rk', rA, -, rS, okS, mem⟩ := Nest.atoms_split (t := node) (n := d + 1) A hA (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      rw [rA, Lynx.Except.ok_bind] at hput
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      obtain ⟨r₁, r₂, run₁, run₂, ⟨rfl, rfl⟩ | ⟨rfl, -, rk0⟩ | ⟨Y, T, er, rfl, rfl, hT, sT, hE⟩⟩ :=
        Nest.update_put_old (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rS okS (fun N e => by cases e)
          (fun N e => by cases e) ev sv hm
      · rw [run₁] at hput; simp at hput
      · subst rk0
        obtain ⟨a, ma⟩ := List.exists_mem_of_ne_nil _ hA
        exact absurd ((mem a).mpr ma) (by simp)
      obtain rfl := hE rfl
      -- The maps of the put, by `map_put/3`.
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y', rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rS okS (fun N e => by cases e)
          (fun N e => by cases e) ev sv hm
      · rw [run] at run₁; cases run₁
      rw [run] at run₁; cases run₁
      -- The puts at each atom.
      obtain ⟨Z, rZ, dZ, onlyZ, semZ⟩ := Nest.puts_run (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) onlyX ev sv
        (m := δ + 100) (by omega) A
      have eq₁ := Nest.next_eq_true (t := node) (n := d + 1) dY dZ (m := δ + 100) (by omega) fun q => by
        by_cases kq : q.1.1 = "map"
        · obtain ⟨w, hw⟩ := Nest.pt_map q kq
          rw [hw, hw, semY, semZ]
          simp only [Nest.PutSem, Nest.UnionS, List.mem_map, Lynx.Term.atom.injEq, exists_eq_right, true_and]
          simp [mem]
        · exact ⟨fun h => absurd (onlyY q h) kq, fun h => absurd (onlyZ q h) kq⟩
      -- The values at the atoms, by `map_get/2`.
      obtain ⟨resX, T₀, hT₀, runX, gX, sT₀⟩ : ∃ resX T₀, (Nest.level node (d + 1)).E T₀ ∧
          Elixir.Module.Types.Descr.«map_get/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (.map K) = .ok resX ∧ «got/1» resX = .ok T₀ ∧
          ∀ y, (Nest.level node (d + 1)).den T₀ y ↔ (Nest.level node (d + 1)).den T y := by
        obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨T₀, rfl, hT₀, -, -, sT₀⟩⟩ :=
          Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) okS (m := δ + 100) (by omega) rS
        · exact absurd onlyX nX
        · refine ⟨_, .map [], ef.none, runX, by simp [«got/1», Elixir.Module.Types.Descr.«none/0»], fun y => ?_⟩
          rw [sT]
          simp only [ef.den_none y, false_iff]
          rintro ⟨u, hu, κ, hκ, e⟩
          rw [eX u hu κ hκ] at e; cases e
        · exact ⟨_, T₀, hT₀, runX, by simp [«got/1», pure, Except.pure], fun y => by rw [sT₀ y, sT y]⟩
      have eq₂ := Nest.elem_equal ef hT hT₀ (fun y => (sT₀ y).symm) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      simp only [Lynx.apply_eq, «map_update_force_atoms:ensures/5»]
      simp [rA, run₂, Erlang.erlang.«element/2», rZ, eq₁, runX, gX, eq₂, Lynx.Term.true]
      """

    law map_update_missing_atoms(map, atoms, value, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          keys?(atoms, []) and atoms != [] and :lists.usort(atoms) == atoms and not Descr.empty?(value) and
          mode in [:keep, :reject] and match?({:ok, _}, Descr.map_put(map, Descr.atom(atoms), value)),
      expects:
        (case Descr.map_update(map, Descr.atom(atoms), value, mode, true) do
          {:error, errors} ->
            length(lacking(map, atoms)) == length(atoms) and permutation?(errors, lacking(map, atoms))

          {old, descr, errors} ->
            length(lacking(map, atoms)) < length(atoms) and permutation?(errors, lacking(map, atoms)) and
              Descr.equal?(old, got(Descr.map_get(map, Descr.atom(atoms)))) and
              Descr.equal?(descr, updated(map, atoms, value, mode))

          _ ->
            false
        end),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the value `d`.
      classical
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_missing_atoms:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_missing_atoms:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hmp, hv⟩, -⟩, hks⟩, hne⟩, hus⟩, hnv⟩, hmode⟩, hput⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have ef := (Nest.level node (d + 1)).ef
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hnv
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hnv; simp [Erlang.erlang.«not/1»] at hnv
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      obtain ⟨keep, rfl⟩ : ∃ keep, mode = Nest.modeT keep := by
        by_cases h : mode = .atom "keep"
        · exact ⟨true, by simp [h, Nest.modeT]⟩
        · by_cases h' : mode = .atom "reject"
          · exact ⟨false, by simp [h', Nest.modeT]⟩
          · simp [Lynx.Term.isMember, h, h'] at hmode
      -- The atoms: a non-empty list without duplicates.
      obtain ⟨as, ks, rfl, eks, ha, -⟩ := Nest.keys_ok hks
      obtain ⟨A, rfl⟩ := Nest.atoms_of ha
      have hA : A ≠ [] := by
        rintro rfl
        simp [Erlang.erlang.«/=/2», Lynx.Term.list] at hne
      have ndA : A.Nodup := by
        obtain ⟨R, rR, sR, mR⟩ := Nest.usort_atoms (A.map Lynx.Term.atom) ha
        rw [rR, Lynx.Except.ok_bind, Nest.eqq_val] at hus
        obtain ⟨R', rfl⟩ := Nest.atoms_of fun r mr => ha r ((mR r).mp mr)
        have ce : Lynx.Term.compare (Lynx.Term.fuel (Lynx.Term.list (R'.map Lynx.Term.atom))
            (Lynx.Term.list (A.map Lynx.Term.atom))) (Lynx.Term.list (R'.map Lynx.Term.atom))
            (Lynx.Term.list (A.map Lynx.Term.atom)) = .eq := by
          cases h : Lynx.Term.compare (Lynx.Term.fuel (Lynx.Term.list (R'.map Lynx.Term.atom))
              (Lynx.Term.list (A.map Lynx.Term.atom))) (Lynx.Term.list (R'.map Lynx.Term.atom))
              (Lynx.Term.list (A.map Lynx.Term.atom)) <;> simp_all [boolAtom]
        obtain rfl := Nest.atoms_compare_eq R' A ce
        have := List.pairwise_map.mp sR
        exact this.imp fun {a b} h e => by subst e; simp at h
      -- The split of the atoms: distinct atoms, the same as the list.
      obtain ⟨K, rk', rA, dK, rS, okS, mem⟩ := Nest.atoms_split (t := node) (n := d + 1) A hA (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      have ndR : rk'.Nodup := by
        have := Nest.split_nodup (t := node) (n := d + 1) dK (m := δ + 99) rS
        exact (List.pairwise_map.mp this).imp fun h e => h (by rw [e])
      have perm : rk'.Perm A := (List.perm_ext_iff_of_nodup ndR ndA).mpr fun a => mem a
      rw [rA, Lynx.Except.ok_bind] at hput
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y', rfl, onlyX, -⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rS okS (fun N e => by cases e)
          (fun N e => by cases e) ev sv hm
      · rw [run] at hput; simp at hput
      let lk : String → Bool := fun a => decide (∃ w, Nest.MT node (d + 1) X w ∧ w (.atom a) = none)
      have hlk : ∀ a, lk a = Bool.true ↔ ∃ w, Nest.MT node (d + 1) X w ∧ w (.atom a) = none := fun a => by simp [lk]
      obtain ⟨r, runU, ⟨-, no⟩ | ⟨-, T, Y, f, hr, dY, oY, sY, hT, sT, sf⟩⟩ :=
        Nest.update_keep_atoms (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rS ev ⟨y₀, hy₀⟩ sv keep hm lk hlk
      · exact absurd onlyX no
      have rL := Nest.lacking_run (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) onlyX (m := δ + 99)
        (by rw [Nest.level_K] at hm ⊢; omega) lk hlk A
      have pE : «permutation?/2» (Lynx.Term.list ((rk'.filter lk).reverse.map
          fun a => Lynx.Term.tuple #[.atom "badkey", .atom a]))
          (Lynx.Term.list ((A.filter lk).map fun a => Lynx.Term.tuple #[.atom "badkey", .atom a])) = .ok (.atom "true") :=
        Nest.permutation_true (((List.reverse_perm _).trans (perm.filter lk)).map _)
      rw [List.map_reverse] at pE
      have rL' : «lacking/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
          (Lynx.Term.list (A.map Lynx.Term.atom)) =
          .ok (Lynx.Term.list ((A.filter lk).map fun a => Lynx.Term.tuple #[.atom "badkey", .atom a])) := rL
      have found : f = Bool.true ↔ ∃ a ∈ A, lk a = Bool.false := by
        rw [sf]
        constructor
        · rintro ⟨a, ma, h⟩
          exact ⟨a, (mem a).mp ma, by simp only [lk, decide_eq_false_iff_not]; exact h⟩
        · rintro ⟨a, ma, h⟩; exact ⟨a, (mem a).mpr ma, fun h' => by rw [(hlk a).mpr h'] at h; cases h⟩
      have lenE : (A.filter lk).length = A.length ↔ ∀ a ∈ A, lk a = Bool.true := List.length_filter_eq_length_iff
      have lenL : (A.filter lk).length < A.length ↔ ∃ a ∈ A, lk a = Bool.false := by
        constructor
        · intro h
          exact Classical.byContradiction fun hn => by
            have := lenE.mpr fun a ma => by cases e : lk a; exact absurd ⟨a, ma, e⟩ hn; rfl
            omega
        · rintro ⟨a, ma, h⟩
          have := List.length_filter_le lk A
          have ne : (A.filter lk).length ≠ A.length := fun e => by rw [lenE.mp e a ma] at h; cases h
          omega
      rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- Some atom no map lacks: the old values and the updated maps.
        obtain ⟨a₀, ma₀, la₀⟩ := found.mp rfl
        have lt : (A.filter lk).length < A.length := lenL.mpr ⟨a₀, ma₀, la₀⟩
        obtain ⟨resX, T₀, hT₀, runX, gX, sT₀⟩ : ∃ resX T₀, (Nest.level node (d + 1)).E T₀ ∧
            Elixir.Module.Types.Descr.«map_get/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
              (.map X) (.map K) = .ok resX ∧ «got/1» resX = .ok T₀ ∧
            ∀ y, (Nest.level node (d + 1)).den T₀ y ↔ (Nest.level node (d + 1)).den T y := by
          obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨T₀, rfl, hT₀, -, -, sT₀⟩⟩ :=
            Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) okS (m := δ + 100) (by omega) rS
          · exact absurd onlyX nX
          · refine ⟨_, .map [], ef.none, runX, by simp [«got/1», Elixir.Module.Types.Descr.«none/0»], fun y => ?_⟩
            rw [sT]
            simp only [ef.den_none y, false_iff]
            intro h
            obtain ⟨a, ma, u, hu, e⟩ := h
            rw [eX u hu (.atom a) (Or.inl (List.mem_map_of_mem ma))] at e; cases e
          · refine ⟨_, T₀, hT₀, runX, by simp [«got/1», pure, Except.pure], fun y => ?_⟩
            rw [sT₀ y, sT y]
            constructor
            · rintro ⟨w, hw, κ, hκ, e⟩
              cases κ with
              | atom s =>
                rcases hκ with mk | ⟨N, eN, -⟩
                · obtain ⟨a, ma, ea⟩ := List.mem_map.mp mk
                  obtain rfl := Lynx.Term.atom.inj ea
                  exact ⟨a, ma, w, hw, e⟩
                · cases eN
              | dom k i => simp [Nest.SplitKey] at hκ
            · rintro ⟨a, ma, w, hw, e⟩
              exact ⟨w, hw, .atom a, Or.inl (List.mem_map_of_mem ma), e⟩
        have eq₂ := Nest.elem_equal ef hT hT₀ (fun y => (sT₀ y).symm) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        obtain ⟨U, rU, dU, oU, sU⟩ := Nest.updated_run (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) onlyX ev sv
          (m := δ + 99) (by omega) A keep
        have eq₁ := Nest.next_eq_true (t := node) (n := d + 1) dY dU (m := δ + 100) (by omega) fun q => by
          by_cases kq : q.1.1 = "map"
          · obtain ⟨w, hw⟩ := Nest.pt_map q kq
            rw [hw, hw, sY, sU]
            exact ⟨fun ⟨a, ma, h⟩ => ⟨a, (mem a).mp ma, h⟩, fun ⟨a, ma, h⟩ => ⟨a, (mem a).mpr ma, h⟩⟩
          · exact ⟨fun h => absurd (oY q h) kq, fun h => absurd (oU q h) kq⟩
        have rU' : «updated/4» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
            (Lynx.Term.list (A.map Lynx.Term.atom)) value (Nest.modeT keep) = .ok (.map U) := rU
        simp only [Lynx.apply_eq, «map_update_missing_atoms:ensures/6»]
        have ltc : compare ((A.filter lk).length : Int) (A.length : Int) = .lt :=
          Int.compare_eq_lt.mpr (by exact_mod_cast lt)
        simp [rA, runU, rL', length_list, Erlang.erlang.«</2», ltc, pE, runX, gX, eq₂, rU', eq₁, Lynx.Term.true,
          Lynx.Except.andAlso]
      · -- Every atom some map lacks: an error.
        have all : ∀ a ∈ A, lk a = Bool.true := fun a ma => by
          cases e : lk a
          · have := found.mpr ⟨a, ma, e⟩; cases this
          · rfl
        simp only [Lynx.apply_eq, «map_update_missing_atoms:ensures/6»]
        simp [rA, runU, rL', length_list, Erlang.erlang.«==/2», lenE.mpr all, pE, Lynx.Term.true, Lynx.Except.andAlso]
      """

    law map_update_force_put(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and not Descr.empty?(value) and
          match?({:ok, _}, Descr.map_put(map, key, value)),
      expects:
        (case Descr.map_update(map, key, value, :force, true) do
          {_, descr, _} -> Descr.equal?(descr, elem(Descr.map_put(map, key, value), 1))
          {:error, _} -> Descr.empty?(elem(Descr.map_put(map, key, value), 1))
          _ -> false
        end),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_force_put:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_force_put:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hmp, hk⟩, hv⟩, -⟩, -⟩, hput⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      obtain ⟨rs', rfl⟩ := Nest.atoms_of ok.hrs
      obtain ⟨ds', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok.hds d md; ⟨s, e⟩
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      obtain ⟨r₁, r₂, run₁, run₂, ⟨rfl, rfl⟩ | ⟨rfl, ⟨er, rfl⟩, -⟩ | ⟨Y, T, er, rfl, rfl, -⟩⟩ :=
        Nest.update_put_old (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rk ok
          (fun N e => by have := nr N e; cases rs' <;> simp_all) na ev sv hm
      · rw [run₁] at hput; simp at hput
      · simp only [Lynx.apply_eq, «map_update_force_put:ensures/5»]
        simp [run₁, run₂, Erlang.erlang.«element/2», empty_none, Lynx.Term.true]
      · simp only [Lynx.apply_eq, «map_update_force_put:ensures/5»]
        simp [run₁, run₂, Erlang.erlang.«element/2», Elixir.Module.Types.Descr.«equal?/2», Erlang.erlang.«==/2»,
          Lynx.Term.true, Lynx.Except.orElse]
      """

    law map_update_old(map, key, value, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and mode in [:force, :keep, :reject] and
          not Descr.empty?(value) and match?({_, _, _}, Descr.map_update(map, key, value, mode, true)),
      expects:
        Descr.equal?(elem(Descr.map_update(map, key, value, mode, true), 0), got(Descr.map_get(map, key))),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_old:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_old:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨hmp, hk⟩, hv⟩, -⟩, hmode⟩, hne⟩, hupd⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have ef := (Nest.level node (d + 1)).ef
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      obtain ⟨rs', rfl⟩ := Nest.atoms_of ok.hrs
      obtain ⟨ds', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok.hds d md; ⟨s, e⟩
      have nr' : ∀ N, neg = .map N → rs' = [] := fun N e => by have := nr N e; cases rs' <;> simp_all
      have rk' : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) key =
          .ok (Nest.splitT (rs'.map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom)) := rk
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · have mt : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject" := by
          by_cases h : mode = .atom "force"
          · exact Or.inl h
          by_cases h' : mode = .atom "keep"
          · exact Or.inr (Or.inl h')
          by_cases h'' : mode = .atom "reject"
          · exact Or.inr (Or.inr h'')
          simp [Lynx.Term.isMember, h, h', h''] at hmode
        rcases sv with rfl | ⟨Z, rfl, sZ⟩
        · rcases mt with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk', Lynx.Term.getMapKeys,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupd
        · rcases mt with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk', Lynx.Term.getMapKeys_single, sZ,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupd
      -- The update gives the old values the split selects.
      obtain ⟨T, Y, er, runU, onlyX, hT, sT⟩ : ∃ T Y er, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) key value mode (.atom "true") =
            .ok (.tuple #[T, Y, er]) ∧ Nest.MOnly node (d + 1) X ∧ (Nest.level node (d + 1)).E T ∧
          ∀ x, (Nest.level node (d + 1)).den T x ↔ ∃ w, Nest.MT node (d + 1) X w ∧
            ∃ κ, Nest.SplitKey (rs'.map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom) κ ∧ w κ = some x := by
        by_cases hf : mode = .atom "force"
        · subst hf
          obtain ⟨r₁, r₂, run₁, run₂, ⟨-, rfl⟩ | ⟨-, ⟨er, rfl⟩, -⟩ | ⟨Y, T, er, rfl, rfl, hT, sT, -⟩⟩ :=
            Nest.update_put_old (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rk' ok nr' na ev sv hm
          · rw [run₂] at hupd; simp at hupd
          · rw [run₂] at hupd; simp at hupd
          · obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y', rfl, onlyX, -⟩⟩ :=
              Nest.dput (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rk' ok nr na ev sv hm
            · rw [run] at run₁; cases run₁
            · exact ⟨T, Y, er, run₂, onlyX, hT, sT⟩
        · obtain ⟨keep, rfl⟩ : ∃ keep, mode = Nest.modeT keep := by
            by_cases h : mode = .atom "keep"
            · exact ⟨true, by simp [h, Nest.modeT]⟩
            · by_cases h' : mode = .atom "reject"
              · exact ⟨false, by simp [h', Nest.modeT]⟩
              · simp [Lynx.Term.isMember, h, h', hf] at hmode
          cases hr : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
              (.map X) key value (Nest.modeT keep) (.atom "true") with
          | error e => rw [hr] at hupd; simp at hupd
          | ok r =>
            rcases Nest.update_keep_old (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rk' ok nr' ev ⟨y₀, hy₀⟩ sv keep hm hr
              with rfl | ⟨er, rfl⟩ | ⟨T, Y, er, rfl, onlyX, hT, sT⟩
            · rw [hr] at hupd; simp at hupd
            · rw [hr] at hupd; simp at hupd
            · exact ⟨T, Y, er, rfl, onlyX, hT, sT⟩
      -- The values `map_get/2` selects.
      obtain ⟨resX, T₀, hT₀, runX, gX, sT₀⟩ : ∃ resX T₀, (Nest.level node (d + 1)).E T₀ ∧
          Elixir.Module.Types.Descr.«map_get/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) key = .ok resX ∧ «got/1» resX = .ok T₀ ∧
          ∀ y, (Nest.level node (d + 1)).den T₀ y ↔ (Nest.level node (d + 1)).den T y := by
        obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨T₀, rfl, hT₀, -, -, sT₀⟩⟩ :=
          Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok (m := δ + 100) (by omega) rk'
        · exact absurd onlyX nX
        · refine ⟨_, .map [], ef.none, runX, by simp [«got/1», Elixir.Module.Types.Descr.«none/0»], fun y => ?_⟩
          rw [sT]
          simp only [ef.den_none y, false_iff]
          rintro ⟨u, hu, κ, hκ, e⟩
          rw [eX u hu κ hκ] at e; cases e
        · exact ⟨_, T₀, hT₀, runX, by simp [«got/1», pure, Except.pure], fun y => by rw [sT₀ y, sT y]⟩
      have eq₂ := Nest.elem_equal ef hT hT₀ (fun y => (sT₀ y).symm) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      simp only [Lynx.apply_eq, «map_update_old:ensures/6»]
      simp [runU, Erlang.erlang.«element/2», runX, gX, eq₂, Lynx.Term.true]
      """

    law map_update_within(map, atom, key, value, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and mode in [:force, :keep, :reject] and
          is_atom(atom) and Descr.subtype?(Descr.atom([atom]), key) and not Descr.empty?(value) and
          match?({_, _, _}, Descr.map_update(map, Descr.atom([atom]), value, mode, true)) and
          match?({_, _, _}, Descr.map_update(map, key, value, mode, true)),
      expects:
        Descr.subtype?(
          elem(Descr.map_update(map, Descr.atom([atom]), value, mode, true), 1),
          elem(Descr.map_update(map, key, value, mode, true), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_within:requires/7», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_within:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hmp, hk⟩, hv⟩, -⟩, hmode⟩, ha⟩, hsub⟩, hne⟩, hupdL⟩, hupdR⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      obtain ⟨s, rfl⟩ : ∃ s, atom = .atom s := by
        cases atom <;> simp [Erlang.erlang.«is_atom/1»] at ha
        exact ⟨_, rfl⟩
      -- The atom is a key of the key type.
      have dk := Nest.arrows_static_ok hk
      have subA := Nest.next_sub (Nest.atomT_de s) dk (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [Nest.atom_one, Lynx.Except.ok_bind, subA, Except.ok.injEq] at hsub
      have subA := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have keyA : Nest.KeyPt node d key (.atom s) :=
        subA _ ((Nest.atomT_den s _).mpr ⟨rfl, rfl⟩)
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      obtain ⟨rs', rfl⟩ := Nest.atoms_of ok.hrs
      obtain ⟨ds', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok.hds d md; ⟨s, e⟩
      have nr' : ∀ N, neg = .map N → rs' = [] := fun N e => by have := nr N e; cases rs' <;> simp_all
      -- The single atom is a split whose keys are keys of the split of the key type.
      obtain ⟨Y, ra, aY, dY, rS, okS, mS⟩ := Nest.atoms_split (t := node) (n := d) [s] (by simp) (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      simp only [List.map] at aY
      rw [Nest.atom_one] at aY
      cases aY
      have keys : ∀ κ, Nest.SplitKey (ra.map Lynx.Term.atom) (.atom "nil") (([] : List String).map Lynx.Term.atom) κ →
          Nest.SplitKey (rs'.map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom) κ := by
        intro κ h
        cases κ with
        | atom s' =>
          rcases h with h | ⟨N, e, -⟩
          · obtain ⟨s'', ms'', e⟩ := List.mem_map.mp h
            have e' : s'' = s' := by injection e
            subst e'
            have := (mS s'').mp ms''
            simp at this; subst this
            exact (sk _).mpr keyA
          · cases e
        | dom k i => simp [Nest.SplitKey] at h
      have mt : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject" := by
        by_cases h : mode = .atom "force"
        · exact Or.inl h
        by_cases h' : mode = .atom "keep"
        · exact Or.inr (Or.inl h')
        by_cases h'' : mode = .atom "reject"
        · exact Or.inr (Or.inr h'')
        simp [Lynx.Term.isMember, h, h', h''] at hmode
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · rcases sv with rfl | ⟨Z, rfl, sZ⟩
        · rcases mt with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk, Lynx.Term.getMapKeys,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupdR
        · rcases mt with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk, Lynx.Term.getMapKeys_single, sZ,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupdR
      -- Both updates succeed.
      obtain ⟨T₁, Y₁, e₁, run₁⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (Nest.atomT s) value mode (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        rw [Nest.atom_one, Lynx.Except.ok_bind] at hupdL
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (Nest.atomT s) value mode (.atom "true") with
        | error e => rw [h] at hupdL; simp at hupdL
        | ok r =>
          rw [h] at hupdL
          simp only [Lynx.Except.ok_bind] at hupdL
          split at hupdL
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupdL
      obtain ⟨T₂, Y₂, e₂, run₂⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) key value mode (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) key value mode (.atom "true") with
        | error e => rw [h] at hupdR; simp at hupdR
        | ok r =>
          rw [h] at hupdR
          simp only [Lynx.Except.ok_bind] at hupdR
          split at hupdR
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupdR
      obtain ⟨YL, YR, rfl, rfl, dYL, dYR, sub⟩ := Nest.upd_sub (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩)
        (Or.inr ⟨X, rfl, sX⟩) (fun w h => h) rS okS (fun N e => by cases e) (fun N e => by cases e) rk ok nr' na keys ev ev
        sv sv (fun y h => h) ⟨y₀, hy₀⟩ mt hm run₁ run₂
      have subE := Nest.next_sub dYL dYR (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr sub] at subE
      simp only [Lynx.apply_eq, «map_update_within:ensures/7»]
      rw [Nest.atom_one, Lynx.Except.ok_bind, run₁]
      simp [run₂, Erlang.erlang.«element/2», subE, Lynx.Term.true]
      """

    law map_update_subtype(left, right, small_key, large_key, small, large, mode, depth, node),
      requires:
        arrows_static?(left, {depth + 1, node}) and arrows_static?(right, {depth + 1, node}) and
          arrows_static?(small_key, {depth, node}) and arrows_static?(large_key, {depth, node}) and
          arrows_static?(small, {depth, node}) and arrows_static?(large, {depth, node}) and depth?(depth) and
          mode in [:force, :keep, :reject] and Descr.subtype?(left, right) and
          Descr.subtype?(small_key, large_key) and Descr.subtype?(small, large) and not Descr.empty?(small) and
          match?({_, _, _}, Descr.map_update(left, small_key, small, mode, true)) and
          match?({_, _, _}, Descr.map_update(right, large_key, large, mode, true)),
      expects:
        Descr.subtype?(
          elem(Descr.map_update(left, small_key, small, mode, true), 1),
          elem(Descr.map_update(right, large_key, large, mode, true), 1)
        ),
      proof: ~LEAN"""
      -- The maps nest at most `d + 1` levels, and the keys and values `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_subtype:requires/9», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_subtype:requires/9», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hr⟩, hsk⟩, hlk⟩, hs⟩, hg⟩, -⟩, hmode⟩, hsub⟩, hsubk⟩, hsubv⟩, hne⟩, hupdL⟩, hupdR⟩ :=
        requires
      have hl : «arrows_static?/2» left (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hl
      have hr : «arrows_static?/2» right (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hr
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have ds := Nest.arrows_static_ok hs
      have dg := Nest.arrows_static_ok hg
      have es : (Nest.level node (d + 1)).E small := Or.inl ds
      have eg : (Nest.level node (d + 1)).E large := Or.inl dg
      have static : ∀ {x : Lynx.Term}, Nest.DE (Nest.level node d).E x →
          x = .atom "term" ∨ ∃ Z, x = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := fun h => by
        rcases h with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      -- The small value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den small y := by
        have ne := Nest.next_empty ds (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD small v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD small v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of ds.notT).mpr hy⟩
      -- Values of the small type are values of the large one.
      have subV := Nest.next_sub ds dg (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [subV, Except.ok.injEq] at hsubv
      have subV := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsubv)
      have vals : ∀ y, (Nest.level node (d + 1)).den small y → (Nest.level node (d + 1)).den large y := fun y hy =>
        (Nest.denN_of dg.notT).mpr (subV y ((Nest.denN_of ds.notT).mp hy))
      -- Keys of the small key type are keys of the large one.
      have dsk := Nest.arrows_static_ok hsk
      have dlk := Nest.arrows_static_ok hlk
      have subK := Nest.next_sub dsk dlk (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [subK, Except.ok.injEq] at hsubk
      have subK := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsubk)
      have splitOf : ∀ {k : Lynx.Term}, «arrows_static?/2» k (.tuple #[.integer (d : Int), node]) = .ok (.atom "true") →
          ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) k =
            .ok (Nest.splitT rs neg ds) ∧ Nest.SplitOk rs neg ds ∧ (∀ N, neg = .map N → rs = []) ∧
            (∀ N, neg = .map N → ∀ e ∈ Lynx.Term.mapEntries N, ∃ s, e.1 = .atom s) ∧
            ∀ κ, Nest.SplitKey rs neg ds κ ↔ Nest.KeyPt node d k κ := fun h =>
        Nest.key_split_any (Nest.arrows_static_ok h) (fun Y e => by subst e; exact static_union_atoms h)
          (fun Y e => by subst e; exact static_negation_atoms h) hmk
      obtain ⟨rs₁, neg₁, ds₁, rk₁, ok₁, nr₁, na₁, sk₁⟩ := splitOf hsk
      obtain ⟨rs₂, neg₂, ds₂, rk₂, ok₂, nr₂, na₂, sk₂⟩ := splitOf hlk
      have keys : ∀ κ, Nest.SplitKey rs₁ neg₁ ds₁ κ → Nest.SplitKey rs₂ neg₂ ds₂ κ := fun κ h =>
        (sk₂ κ).mpr (Nest.keyPt_mono subK ((sk₁ κ).mp h))
      obtain ⟨rs₁', rfl⟩ := Nest.atoms_of ok₁.hrs
      obtain ⟨ds₁', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok₁.hds d md; ⟨s, e⟩
      obtain ⟨rs₂', rfl⟩ := Nest.atoms_of ok₂.hrs
      obtain ⟨ds₂', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok₂.hds d md; ⟨s, e⟩
      have nr₁' : ∀ N, neg₁ = .map N → rs₁' = [] := fun N e => by have := nr₁ N e; cases rs₁' <;> simp_all
      have nr₂' : ∀ N, neg₂ = .map N → rs₂' = [] := fun N e => by have := nr₂ N e; cases rs₂' <;> simp_all
      -- Maps of the left type are maps of the right one.
      have dl := Nest.arrows_static_ok hl
      have dr := Nest.arrows_static_ok hr
      have subM := Nest.next_sub dl dr (m := δ + 100) (by omega)
      rw [subM, Except.ok.injEq] at hsub
      have subM := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have mt : mode = .atom "force" ∨ mode = .atom "keep" ∨ mode = .atom "reject" := by
        by_cases h : mode = .atom "force"
        · exact Or.inl h
        by_cases h' : mode = .atom "keep"
        · exact Or.inr (Or.inl h')
        by_cases h'' : mode = .atom "reject"
        · exact Or.inr (Or.inr h'')
        simp [Lynx.Term.isMember, h, h', h''] at hmode
      rcases dl with rfl | ⟨XL, rfl, sXL⟩
      · rcases static ds with rfl | ⟨Z, rfl, sZ⟩
        · rcases mt with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk₁, Lynx.Term.getMapKeys,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupdL
        · rcases mt with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk₁, Lynx.Term.getMapKeys_single, sZ,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupdL
      rcases dr with rfl | ⟨XR, rfl, sXR⟩
      · rcases static dg with rfl | ⟨Z, rfl, sZ⟩
        · rcases mt with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk₂, Lynx.Term.getMapKeys,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupdR
        · rcases mt with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk₂, Lynx.Term.getMapKeys_single, sZ,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupdR
      have maps : ∀ w, Nest.MT node (d + 1) XL w → Nest.MT node (d + 1) XR w := fun w hw =>
        (Nest.denD_mpt w).mp (subM _ ((Nest.denD_mpt w).mpr hw))
      -- Both updates succeed.
      obtain ⟨T₁, Y₁, e₁, run₁⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XL) small_key small mode (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map XL) small_key small mode (.atom "true") with
        | error e => rw [h] at hupdL; simp at hupdL
        | ok r =>
          rw [h] at hupdL
          simp only [Lynx.Except.ok_bind] at hupdL
          split at hupdL
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupdL
      obtain ⟨T₂, Y₂, e₂, run₂⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XR) large_key large mode (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map XR) large_key large mode (.atom "true") with
        | error e => rw [h] at hupdR; simp at hupdR
        | ok r =>
          rw [h] at hupdR
          simp only [Lynx.Except.ok_bind] at hupdR
          split at hupdR
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupdR
      obtain ⟨YL, YR, rfl, rfl, dYL, dYR, sub⟩ := Nest.upd_sub (t := node) (n := d + 1) (Or.inr ⟨XL, rfl, sXL⟩)
        (Or.inr ⟨XR, rfl, sXR⟩) maps rk₁ ok₁ nr₁' na₁ rk₂ ok₂ nr₂' na₂ keys es eg (static ds) (static dg) vals ⟨y₀, hy₀⟩ mt
        hm run₁ run₂
      have subE := Nest.next_sub dYL dYR (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr sub] at subE
      simp only [Lynx.apply_eq, «map_update_subtype:ensures/9»]
      simp [run₁, run₂, Erlang.erlang.«element/2», subE, Lynx.Term.true]
      """

    law map_delete_within(map, atom, key, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and depth?(depth) and
          mode in [:force, :keep, :reject] and is_atom(atom) and Descr.subtype?(Descr.atom([atom]), key) and
          match?({_, _, _}, Descr.map_update(map, Descr.atom([atom]), :delete, mode, true)) and
          match?({_, _, _}, Descr.map_update(map, key, :delete, mode, true)),
      expects:
        Descr.subtype?(
          elem(Descr.map_update(map, Descr.atom([atom]), :delete, mode, true), 1),
          elem(Descr.map_update(map, key, :delete, mode, true), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_delete_within:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_delete_within:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hmp, hk⟩, -⟩, hmode⟩, ha⟩, hsub⟩, hupdL⟩, hupdR⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      obtain ⟨s, rfl⟩ : ∃ s, atom = .atom s := by
        cases atom <;> simp [Erlang.erlang.«is_atom/1»] at ha
        exact ⟨_, rfl⟩
      -- The atom is a key of the key type.
      have dk := Nest.arrows_static_ok hk
      have subA := Nest.next_sub (Nest.atomT_de s) dk (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [Nest.atom_one, Lynx.Except.ok_bind, subA, Except.ok.injEq] at hsub
      have subA := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have keyA : Nest.KeyPt node d key (.atom s) :=
        subA _ ((Nest.atomT_den s _).mpr ⟨rfl, rfl⟩)
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      obtain ⟨rs', rfl⟩ := Nest.atoms_of ok.hrs
      obtain ⟨ds', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok.hds d md; ⟨s, e⟩
      have nr' : ∀ N, neg = .map N → rs' = [] := fun N e => by have := nr N e; cases rs' <;> simp_all
      -- The single atom is a split whose keys are keys of the split of the key type.
      obtain ⟨Y, ra, aY, dY, rS, okS, mS⟩ := Nest.atoms_split (t := node) (n := d) [s] (by simp) (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      simp only [List.map] at aY
      rw [Nest.atom_one] at aY
      cases aY
      have keys : ∀ κ, Nest.SplitKey (ra.map Lynx.Term.atom) (.atom "nil") (([] : List String).map Lynx.Term.atom) κ →
          Nest.SplitKey (rs'.map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom) κ := by
        intro κ h
        cases κ with
        | atom s' =>
          rcases h with h | ⟨N, e, -⟩
          · obtain ⟨s'', ms'', e⟩ := List.mem_map.mp h
            have e' : s'' = s' := by injection e
            subst e'
            have := (mS s'').mp ms''
            simp at this; subst this
            exact (sk _).mpr keyA
          · cases e
        | dom k i => simp [Nest.SplitKey] at h
      obtain ⟨md, rfl, hmd⟩ : ∃ md, mode = .atom md ∧ Nest.Mode md := by
        by_cases h : mode = .atom "force"
        · exact ⟨_, h, Or.inl rfl⟩
        by_cases h' : mode = .atom "keep"
        · exact ⟨_, h', Or.inr (Or.inl rfl)⟩
        by_cases h'' : mode = .atom "reject"
        · exact ⟨_, h'', Or.inr (Or.inr rfl)⟩
        simp [Lynx.Term.isMember, h, h', h''] at hmode
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · rcases hmd with rfl | rfl | rfl <;>
          simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
            Erlang.erlang.«=:=/2», rk, Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupdR
      -- Both updates succeed.
      obtain ⟨T₁, Y₁, e₁, run₁⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (Nest.atomT s) (.atom "delete") (.atom md) (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        rw [Nest.atom_one, Lynx.Except.ok_bind] at hupdL
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (Nest.atomT s) (.atom "delete") (.atom md) (.atom "true") with
        | error e => rw [h] at hupdL; simp at hupdL
        | ok r =>
          rw [h] at hupdL
          simp only [Lynx.Except.ok_bind] at hupdL
          split at hupdL
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupdL
      obtain ⟨T₂, Y₂, e₂, run₂⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) key (.atom "delete") (.atom md) (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) key (.atom "delete") (.atom md) (.atom "true") with
        | error e => rw [h] at hupdR; simp at hupdR
        | ok r =>
          rw [h] at hupdR
          simp only [Lynx.Except.ok_bind] at hupdR
          split at hupdR
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupdR
      obtain ⟨YL, YR, rfl, rfl, dYL, dYR, sub⟩ := Nest.del_sub (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩)
        (Or.inr ⟨X, rfl, sX⟩) (fun w h => h) rS okS (fun N e => by cases e) (fun N e => by cases e) rk ok nr' na keys hmd
        hm run₁ run₂
      have subE := Nest.next_sub dYL dYR (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr sub] at subE
      simp only [Lynx.apply_eq, «map_delete_within:ensures/6»]
      rw [Nest.atom_one, Lynx.Except.ok_bind, run₁]
      simp [run₂, Erlang.erlang.«element/2», subE, Lynx.Term.true]
      """

    law map_delete_subtype(left, right, small_key, large_key, mode, depth, node),
      requires:
        arrows_static?(left, {depth + 1, node}) and arrows_static?(right, {depth + 1, node}) and
          arrows_static?(small_key, {depth, node}) and arrows_static?(large_key, {depth, node}) and depth?(depth) and
          mode in [:force, :keep, :reject] and Descr.subtype?(left, right) and Descr.subtype?(small_key, large_key) and
          match?({_, _, _}, Descr.map_update(left, small_key, :delete, mode, true)) and
          match?({_, _, _}, Descr.map_update(right, large_key, :delete, mode, true)),
      expects:
        Descr.subtype?(
          elem(Descr.map_update(left, small_key, :delete, mode, true), 1),
          elem(Descr.map_update(right, large_key, :delete, mode, true), 1)
        ),
      proof: ~LEAN"""
      -- The maps nest at most `d + 1` levels, and the keys `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_delete_subtype:requires/7», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_delete_subtype:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hr⟩, hsk⟩, hlk⟩, -⟩, hmode⟩, hsub⟩, hsubk⟩, hupdL⟩, hupdR⟩ := requires
      have hl : «arrows_static?/2» left (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hl
      have hr : «arrows_static?/2» right (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hr
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      -- Keys of the small key type are keys of the large one.
      have dsk := Nest.arrows_static_ok hsk
      have dlk := Nest.arrows_static_ok hlk
      have subK := Nest.next_sub dsk dlk (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [subK, Except.ok.injEq] at hsubk
      have subK := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsubk)
      have splitOf : ∀ {k : Lynx.Term}, «arrows_static?/2» k (.tuple #[.integer (d : Int), node]) = .ok (.atom "true") →
          ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) k =
            .ok (Nest.splitT rs neg ds) ∧ Nest.SplitOk rs neg ds ∧ (∀ N, neg = .map N → rs = []) ∧
            (∀ N, neg = .map N → ∀ e ∈ Lynx.Term.mapEntries N, ∃ s, e.1 = .atom s) ∧
            ∀ κ, Nest.SplitKey rs neg ds κ ↔ Nest.KeyPt node d k κ := fun h =>
        Nest.key_split_any (Nest.arrows_static_ok h) (fun Y e => by subst e; exact static_union_atoms h)
          (fun Y e => by subst e; exact static_negation_atoms h) hmk
      obtain ⟨rs₁, neg₁, ds₁, rk₁, ok₁, nr₁, na₁, sk₁⟩ := splitOf hsk
      obtain ⟨rs₂, neg₂, ds₂, rk₂, ok₂, nr₂, na₂, sk₂⟩ := splitOf hlk
      have keys : ∀ κ, Nest.SplitKey rs₁ neg₁ ds₁ κ → Nest.SplitKey rs₂ neg₂ ds₂ κ := fun κ h =>
        (sk₂ κ).mpr (Nest.keyPt_mono subK ((sk₁ κ).mp h))
      obtain ⟨rs₁', rfl⟩ := Nest.atoms_of ok₁.hrs
      obtain ⟨ds₁', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok₁.hds d md; ⟨s, e⟩
      obtain ⟨rs₂', rfl⟩ := Nest.atoms_of ok₂.hrs
      obtain ⟨ds₂', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok₂.hds d md; ⟨s, e⟩
      have nr₁' : ∀ N, neg₁ = .map N → rs₁' = [] := fun N e => by have := nr₁ N e; cases rs₁' <;> simp_all
      have nr₂' : ∀ N, neg₂ = .map N → rs₂' = [] := fun N e => by have := nr₂ N e; cases rs₂' <;> simp_all
      -- Maps of the left type are maps of the right one.
      have dl := Nest.arrows_static_ok hl
      have dr := Nest.arrows_static_ok hr
      have subM := Nest.next_sub dl dr (m := δ + 100) (by omega)
      rw [subM, Except.ok.injEq] at hsub
      have subM := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      obtain ⟨md, rfl, hmd⟩ : ∃ md, mode = .atom md ∧ Nest.Mode md := by
        by_cases h : mode = .atom "force"
        · exact ⟨_, h, Or.inl rfl⟩
        by_cases h' : mode = .atom "keep"
        · exact ⟨_, h', Or.inr (Or.inl rfl)⟩
        by_cases h'' : mode = .atom "reject"
        · exact ⟨_, h'', Or.inr (Or.inr rfl)⟩
        simp [Lynx.Term.isMember, h, h', h''] at hmode
      rcases dl with rfl | ⟨XL, rfl, sXL⟩
      · rcases hmd with rfl | rfl | rfl <;>
          simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
            Erlang.erlang.«=:=/2», rk₁, Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupdL
      rcases dr with rfl | ⟨XR, rfl, sXR⟩
      · rcases hmd with rfl | rfl | rfl <;>
          simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
            Erlang.erlang.«=:=/2», rk₂, Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupdR
      have maps : ∀ w, Nest.MT node (d + 1) XL w → Nest.MT node (d + 1) XR w := fun w hw =>
        (Nest.denD_mpt w).mp (subM _ ((Nest.denD_mpt w).mpr hw))
      -- Both updates succeed.
      obtain ⟨T₁, Y₁, e₁, run₁⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XL) small_key (.atom "delete") (.atom md) (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map XL) small_key (.atom "delete") (.atom md) (.atom "true") with
        | error e => rw [h] at hupdL; simp at hupdL
        | ok r =>
          rw [h] at hupdL
          simp only [Lynx.Except.ok_bind] at hupdL
          split at hupdL
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupdL
      obtain ⟨T₂, Y₂, e₂, run₂⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XR) large_key (.atom "delete") (.atom md) (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map XR) large_key (.atom "delete") (.atom md) (.atom "true") with
        | error e => rw [h] at hupdR; simp at hupdR
        | ok r =>
          rw [h] at hupdR
          simp only [Lynx.Except.ok_bind] at hupdR
          split at hupdR
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupdR
      obtain ⟨YL, YR, rfl, rfl, dYL, dYR, sub⟩ := Nest.del_sub (t := node) (n := d + 1) (Or.inr ⟨XL, rfl, sXL⟩)
        (Or.inr ⟨XR, rfl, sXR⟩) maps rk₁ ok₁ nr₁' na₁ rk₂ ok₂ nr₂' na₂ keys hmd hm run₁ run₂
      have subE := Nest.next_sub dYL dYR (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr sub] at subE
      simp only [Lynx.apply_eq, «map_delete_subtype:ensures/7»]
      simp [run₁, run₂, Erlang.erlang.«element/2», subE, Lynx.Term.true]
      """

    law map_delete_old(map, key, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and depth?(depth) and
          mode in [:force, :keep, :reject] and match?({_, _, _}, Descr.map_update(map, key, :delete, mode, true)),
      expects: Descr.equal?(elem(Descr.map_update(map, key, :delete, mode, true), 0), got(Descr.map_get(map, key))),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_delete_old:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_delete_old:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨hmp, hk⟩, -⟩, hmode⟩, hupd⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have ef := (Nest.level node (d + 1)).ef
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      obtain ⟨rs', rfl⟩ := Nest.atoms_of ok.hrs
      obtain ⟨ds', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok.hds d md; ⟨s, e⟩
      have nr' : ∀ N, neg = .map N → rs' = [] := fun N e => by have := nr N e; cases rs' <;> simp_all
      have rk' : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) key =
          .ok (Nest.splitT (rs'.map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom)) := rk
      obtain ⟨md, rfl, hmd⟩ : ∃ md, mode = .atom md ∧ (md = "force" ∨ md = "keep" ∨ md = "reject") := by
        by_cases h : mode = .atom "force"
        · exact ⟨_, h, Or.inl rfl⟩
        by_cases h' : mode = .atom "keep"
        · exact ⟨_, h', Or.inr (Or.inl rfl)⟩
        by_cases h'' : mode = .atom "reject"
        · exact ⟨_, h'', Or.inr (Or.inr rfl)⟩
        simp [Lynx.Term.isMember, h, h', h''] at hmode
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · rcases hmd with rfl | rfl | rfl <;>
          simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
            Erlang.erlang.«=:=/2», rk', Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupd
      -- The update gives the old values the split selects.
      obtain ⟨T, Y, er, runU, onlyX, hT, sT⟩ : ∃ T Y er, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) key (.atom "delete") (.atom md)
            (.atom "true") = .ok (.tuple #[T, Y, er]) ∧ Nest.MOnly node (d + 1) X ∧ (Nest.level node (d + 1)).E T ∧
          ∀ x, (Nest.level node (d + 1)).den T x ↔ ∃ w, Nest.MT node (d + 1) X w ∧
            ∃ κ, Nest.SplitKey (rs'.map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom) κ ∧ w κ = some x := by
        cases hr : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) key (.atom "delete") (.atom md) (.atom "true") with
        | error e => rw [hr] at hupd; simp at hupd
        | ok r =>
          rcases Nest.update_delete_old (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) rk' ok nr' md hmd hm hr
            with rfl | ⟨er, rfl⟩ | ⟨T, Y, er, rfl, onlyX, hT, sT⟩
          · rw [hr] at hupd; simp at hupd
          · rw [hr] at hupd; simp at hupd
          · exact ⟨T, Y, er, rfl, onlyX, hT, sT⟩
      -- The values `map_get/2` selects.
      obtain ⟨resX, T₀, hT₀, runX, gX, sT₀⟩ : ∃ resX T₀, (Nest.level node (d + 1)).E T₀ ∧
          Elixir.Module.Types.Descr.«map_get/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) key = .ok resX ∧ «got/1» resX = .ok T₀ ∧
          ∀ y, (Nest.level node (d + 1)).den T₀ y ↔ (Nest.level node (d + 1)).den T y := by
        obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨T₀, rfl, hT₀, -, -, sT₀⟩⟩ :=
          Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok (m := δ + 100) (by omega) rk'
        · exact absurd onlyX nX
        · refine ⟨_, .map [], ef.none, runX, by simp [«got/1», Elixir.Module.Types.Descr.«none/0»], fun y => ?_⟩
          rw [sT]
          simp only [ef.den_none y, false_iff]
          rintro ⟨u, hu, κ, hκ, e⟩
          rw [eX u hu κ hκ] at e; cases e
        · exact ⟨_, T₀, hT₀, runX, by simp [«got/1», pure, Except.pure], fun y => by rw [sT₀ y, sT y]⟩
      have eq₂ := Nest.elem_equal ef hT hT₀ (fun y => (sT₀ y).symm) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      simp only [Lynx.apply_eq, «map_delete_old:ensures/5»]
      simp [runU, Erlang.erlang.«element/2», runX, gX, eq₂, Lynx.Term.true]
      """

    law map_put_gradual_atom(map, atom, key, value, depth, node),
      requires:
        arrows_gradual?(map, {depth + 1, node}) and arrows_gradual?(key, {depth, node}) and
          arrows_gradual?(value, {depth, node}) and depth?(depth) and is_atom(atom) and
          Descr.subtype?(Descr.atom([atom]), Descr.upper_bound(key)) and
          match?({:ok, _}, Descr.map_put_key(Descr.upper_bound(map), atom, Descr.upper_bound(value))) and
          match?({:ok, _}, Descr.map_put(map, key, value)),
      expects:
        Descr.subtype?(
          elem(Descr.map_put_key(Descr.upper_bound(map), atom, Descr.upper_bound(value)), 1),
          Descr.upper_bound(elem(Descr.map_put(map, key, value), 1))
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_gradual_atom:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_gradual_atom:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hg, hk⟩, hgv⟩, -⟩, ha⟩, hsub⟩, hputK⟩, hput⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨a, rfl⟩ : ∃ a, atom = .atom a := by
        cases atom <;> simp [Erlang.erlang.«is_atom/1»] at ha
        exact ⟨_, rfl⟩
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) map
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gM, -, -⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      have hgv : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) value
          (.tuple #[.integer (d : Int), node]) = .ok (.atom "true") := by simpa using hgv
      obtain ⟨gV, -, dVu⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) hgv
      have evu : (Nest.level node (d + 1)).E (Nest.upper value) := Or.inl dVu
      have svu : Nest.upper value = .atom "term" ∨
          ∃ Z, Nest.upper value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dVu with h | ⟨Z, h, sZ⟩
        · exact Or.inl h
        · exact Or.inr ⟨Z, h, sZ.static⟩
      have svu' : Nest.upper value = .atom "term" ∨ ∃ Z, Nest.upper value = .map Z := svu.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
      have hk : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) key
          (.tuple #[.integer (d : Int), node]) = .ok (.atom "true") := by simpa using hk
      obtain ⟨gK, -, -⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) hk
      obtain ⟨s, neg, Ss, rk, na, hP, oks, rs₂, neg₂, ds₂, rk₂, ok₂, nr₂, na₂, sk, skK⟩ :=
        Nest.key_gsplit (t := node) (n := d) (m := δ + 99) hmk hk
      have hmono : ∀ v (M₁ M₂ : Nest.MW (Nest.level node (d + 1)).V → Prop), (∀ u, M₁ u → M₂ u) → ∀ w,
          Nest.PutAny Ss (Nest.level node (d + 1)).den M₁ v w → Nest.PutAny Ss (Nest.level node (d + 1)).den M₂ v w :=
        fun v M₁ M₂ sub w ⟨sp, msp, h⟩ => ⟨sp, msp, Nest.put_mono sub (fun _ h => h) (oks sp msp).1 (oks sp msp).1
          (oks sp msp).2 (fun _ h => h) h⟩
      rcases gM.shape with rfl | ⟨X, rfl⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      -- The upper bound of the map type is a static map type.
      have uX : Nest.upper (.map X) = (Lynx.Term.mapLookup X (.atom "dynamic")).getD (.map X) := rfl
      obtain ⟨U, eU, dU⟩ : ∃ U, Nest.upper (.map X) = .map U ∧ Nest.DE (Nest.level node (d + 1)).E (.map U) := by
        rcases gM.up_tc with h | ⟨U, h, sU⟩
        · rw [Nest.upper_bound_run gM.ub, h] at hputK
          simp [Elixir.Module.Types.Descr.«map_put_key/3», Nest.upper_bound_run gV.ub] at hputK
        · exact ⟨U, h, Or.inr ⟨U, rfl, sU⟩⟩
      -- The put holds in its upper bound the puts at the upper bounds.
      obtain ⟨R, run, gR, oR, sR⟩ : ∃ R, Elixir.Module.Types.Descr.«map_put/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) key value = .ok (.tuple #[.atom "ok", R]) ∧
          Nest.GC (Nest.level node (d + 1)) R ∧ (∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper R) q → q.1.1 = "map") ∧
          ∀ w, Nest.denD (Nest.upper R) (Nest.mpt (t := node) (n := d + 1) w) ↔
            Nest.PutOfP (Nest.PutAny Ss) node (d + 1) U (Nest.upper value) w := by
        -- A static value is its own upper bound.
        have staticV : (value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none) →
            ∃ R, Elixir.Module.Types.Descr.«map_put/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
              key value = .ok (.tuple #[.atom "ok", R]) ∧ Nest.GC (Nest.level node (d + 1)) R ∧
            (∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper R) q → q.1.1 = "map") ∧
            ∀ w, Nest.denD (Nest.upper R) (Nest.mpt (t := node) (n := d + 1) w) ↔
              Nest.PutOfP (Nest.PutAny Ss) node (d + 1) U (Nest.upper value) w := by
          intro sv
          have uv : Nest.upper value = value := by
            rcases sv with rfl | ⟨Z, rfl, sZ⟩
            · rfl
            · simp [Nest.upper, sZ]
          have ev : (Nest.level node (d + 1)).E value := uv ▸ evu
          have sv' : value = .atom "term" ∨ ∃ Z, value = .map Z := sv.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
          rw [uv]
          cases hD : Lynx.Term.mapLookup X (.atom "dynamic") with
          | none =>
            have dX : Nest.DE (Nest.level node (d + 1)).E (.map X) := Nest.GC.static gM hD
            have eUX : U = X := by
              have : Nest.upper (.map X) = .map X := by simp [Nest.upper, hD]
              rw [this] at eU; simp only [Lynx.Term.map.injEq] at eU; exact eU.symm
            subst eUX
            obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
              Nest.dput_g (t := node) (n := d + 1) dX rk hP na ev sv (by omega)
            · rw [run] at hput; simp at hput
            refine ⟨_, run, Nest.GC.tc dY, fun q h => onlyY q (by rwa [Nest.upper_tc dY] at h), fun w => ?_⟩
            rw [Nest.upper_tc dY, Nest.denD_mpt, semY]
            exact ⟨fun h => ⟨onlyX.2, h⟩, fun h => h.2⟩
          | some Dy =>
            have eUD : Nest.dynL Dy = U := by
              rw [Nest.upper_dyn hD] at eU; subst eU; rfl
            obtain ⟨res, run, rfl | ⟨R, rfl, gR, oR, -, -, sR⟩⟩ := Nest.gres_g gM hD ev sv' hP (hmono _) na (m := δ + 100) hm
            · rw [Nest.put_static_value_g rk sv, run] at hput; simp at hput
            exact ⟨R, by rw [Nest.put_static_value_g rk sv, run], gR, oR, fun w => by rw [sR, eUD]⟩
        rcases gV.shape with rfl | ⟨Zv, rfl⟩
        · exact staticV (Or.inl rfl)
        cases hZ : Lynx.Term.mapLookup Zv (.atom "dynamic") with
        | none => exact staticV (Or.inr ⟨Zv, rfl, hZ⟩)
        | some Dv =>
          -- A gradual value puts its dynamic part into the dynamic part of the map type.
          have uV : Nest.upper (.map Zv) = Dv := Nest.upper_dyn hZ
          rw [uV] at evu svu' ⊢
          have gG : Nest.GC (Nest.level node (d + 1)) (.map (Nest.dynG X)) :=
            Or.inr ⟨_, _, rfl, by simp [Nest.dynG, Lynx.Term.mapLookup], uX ▸ gM.up_tc,
              by simp only [Nest.dynG, Nest.rmDyn_cons_dyn]; exact Nest.descrC_nil, fun q h => by
                have := (Nest.denD_rmDyn _ q).mpr h
                simp [Nest.dynG, Nest.rmDyn, Nest.denD_map, Lynx.Term.mapLookup, Elixir.STTDescrProofsTest.dn_none] at this⟩
          have hD : Lynx.Term.mapLookup (Nest.dynG X) (.atom "dynamic") =
              some ((Lynx.Term.mapLookup X (.atom "dynamic")).getD (.map X)) := by simp [Nest.dynG, Lynx.Term.mapLookup]
          obtain ⟨res, run, rfl | ⟨R, rfl, gR, oR, -, -, sR⟩⟩ := Nest.gres_g gG hD evu svu' hP (hmono _) na (m := δ + 100) hm
          · rw [Nest.put_gradual_value_g rk hZ, run] at hput; simp at hput
          refine ⟨R, by rw [Nest.put_gradual_value_g rk hZ, run], gR, oR, fun w => ?_⟩
          rw [sR, ← uX, eU]
          rfl
      -- The atom is a key of the upper bound of the key type.
      have subA := Nest.next_sub (Nest.atomT_de a) gK.up_tc (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [Nest.atom_one, Lynx.Except.ok_bind, Nest.upper_bound_run gK.ub, Lynx.Except.ok_bind, subA,
        Except.ok.injEq] at hsub
      have subA := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have keyA : Nest.KeyPt node d (Nest.upper key) (.atom a) := subA _ ((Nest.atomT_den a _).mpr ⟨rfl, rfl⟩)
      obtain ⟨sp₀, msp₀, ksp₀⟩ := (sk _).mpr ((skK _).mpr keyA)
      -- The put at the atom of the upper bounds.
      obtain ⟨res₁, run₁, ⟨rfl, -⟩ | ⟨Y₁, rfl, -, dY₁, only₁, sem₁⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) dU a evu svu (m := δ + 100) (by omega)
      · rw [Nest.upper_bound_run gM.ub, eU, Lynx.Except.ok_bind, Nest.upper_bound_run gV.ub, Lynx.Except.ok_bind,
          run₁] at hputK
        simp at hputK
      have ok₁ : Nest.SplitOk [.atom a] (.atom "nil") [] := ⟨by simp, Or.inl rfl, by simp, by simp⟩
      have keys : ∀ κ, Nest.SplitKey [.atom a] (.atom "nil") [] κ → Nest.SplitKey sp₀.1 sp₀.2.1 sp₀.2.2 κ := by
        intro κ h
        cases κ with
        | atom s' =>
          rcases h with h | ⟨N, e, -⟩
          · simp at h; subst h; exact ksp₀
          · cases e
        | dom k i => simp [Nest.SplitKey] at h
      obtain ⟨R', eR'⟩ : ∃ R', Nest.upper R = .map R' := by
        rcases gR.up_tc with h | ⟨R', h, -⟩
        · have := oR Nest.bitPt (by rw [h]; exact Nest.denD_term _)
          simp [Nest.bitPt] at this
        · exact ⟨R', h⟩
      have sub := Nest.next_sub dY₁ (gR.up_tc : Nest.DE (Nest.level node (d + 1)).E (Nest.upper R)) (m := δ + 100)
        (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node (d + 1) (.map Y₁) (Nest.upper R) from fun q hq => by
        obtain ⟨w, hw⟩ := Nest.pt_map q (only₁ q hq)
        rw [hw] at hq
        obtain ⟨pa, o, hX⟩ := (sem₁ w).mp hq
        rw [eR', hw]
        exact (Nest.denD_mpt w).mp (eR' ▸ (sR w).mpr ⟨⟨_, hX⟩, sp₀, msp₀, Nest.put_mono (fun u h => h) (fun x h => h) ok₁
          (oks sp₀ msp₀).1 (oks sp₀ msp₀).2 keys (Or.inl ⟨rfl, Or.inl ⟨a, by simp, pa, o, hX⟩⟩)⟩))] at sub
      simp only [Lynx.apply_eq, «map_put_gradual_atom:ensures/6», run]
      simp [Erlang.erlang.«element/2», Nest.upper_bound_run gR.ub, Nest.upper_bound_run gM.ub, eU,
        Nest.upper_bound_run gV.ub, run₁, sub, Lynx.Term.true]
      """

    law map_put_gradual_upper(map, key, value, depth, node),
      requires:
        arrows_gradual?(map, {depth + 1, node}) and arrows_gradual?(key, {depth, node}) and
          arrows_gradual?(value, {depth, node}) and depth?(depth) and match?({:ok, _}, Descr.map_put(map, key, value)) and
          match?(
            {:ok, _},
            Descr.map_put(Descr.upper_bound(map), Descr.upper_bound(key), Descr.upper_bound(value))
          ),
      expects:
        Descr.subtype?(
          Descr.upper_bound(elem(Descr.map_put(map, key, value), 1)),
          elem(Descr.map_put(Descr.upper_bound(map), Descr.upper_bound(key), Descr.upper_bound(value)), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_gradual_upper:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_gradual_upper:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hg, hk⟩, hgv⟩, -⟩, hput⟩, hputU⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) map
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gM, -, -⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      have hgv : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) value
          (.tuple #[.integer (d : Int), node]) = .ok (.atom "true") := by simpa using hgv
      obtain ⟨gV, -, dVu⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) hgv
      have evu : (Nest.level node (d + 1)).E (Nest.upper value) := Or.inl dVu
      have svu : Nest.upper value = .atom "term" ∨
          ∃ Z, Nest.upper value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dVu with h | ⟨Z, h, sZ⟩
        · exact Or.inl h
        · exact Or.inr ⟨Z, h, sZ.static⟩
      have svu' : Nest.upper value = .atom "term" ∨ ∃ Z, Nest.upper value = .map Z := svu.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
      have hk : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) key
          (.tuple #[.integer (d : Int), node]) = .ok (.atom "true") := by simpa using hk
      obtain ⟨gK, -, -⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) hk
      obtain ⟨s, neg, Ss, rk, na, hP, oks, rs₂, neg₂, ds₂, rk₂, ok₂, nr₂, na₂, sk, -⟩ :=
        Nest.key_gsplit (t := node) (n := d) (m := δ + 99) hmk hk
      have hmono : ∀ v (M₁ M₂ : Nest.MW (Nest.level node (d + 1)).V → Prop), (∀ u, M₁ u → M₂ u) → ∀ w,
          Nest.PutAny Ss (Nest.level node (d + 1)).den M₁ v w → Nest.PutAny Ss (Nest.level node (d + 1)).den M₂ v w :=
        fun v M₁ M₂ sub w ⟨sp, msp, h⟩ => ⟨sp, msp, Nest.put_mono sub (fun _ h => h) (oks sp msp).1 (oks sp msp).1
          (oks sp msp).2 (fun _ h => h) h⟩
      rcases gM.shape with rfl | ⟨X, rfl⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      -- The upper bound of the map type is a static map type.
      have uX : Nest.upper (.map X) = (Lynx.Term.mapLookup X (.atom "dynamic")).getD (.map X) := rfl
      obtain ⟨U, eU, dU⟩ : ∃ U, Nest.upper (.map X) = .map U ∧ Nest.DE (Nest.level node (d + 1)).E (.map U) := by
        rcases gM.up_tc with h | ⟨U, h, sU⟩
        · rw [Nest.upper_bound_run gM.ub, h] at hputU
          simp [Elixir.Module.Types.Descr.«map_put/3», Nest.upper_bound_run gK.ub, Nest.upper_bound_run gV.ub] at hputU
        · exact ⟨U, h, Or.inr ⟨U, rfl, sU⟩⟩
      -- The put holds in its upper bound the puts at the upper bounds.
      obtain ⟨R, run, gR, oR, sR⟩ : ∃ R, Elixir.Module.Types.Descr.«map_put/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) key value = .ok (.tuple #[.atom "ok", R]) ∧
          Nest.GC (Nest.level node (d + 1)) R ∧ (∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper R) q → q.1.1 = "map") ∧
          ∀ w, Nest.denD (Nest.upper R) (Nest.mpt (t := node) (n := d + 1) w) ↔
            Nest.PutOfP (Nest.PutAny Ss) node (d + 1) U (Nest.upper value) w := by
        -- A static value is its own upper bound.
        have staticV : (value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none) →
            ∃ R, Elixir.Module.Types.Descr.«map_put/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
              key value = .ok (.tuple #[.atom "ok", R]) ∧ Nest.GC (Nest.level node (d + 1)) R ∧
            (∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper R) q → q.1.1 = "map") ∧
            ∀ w, Nest.denD (Nest.upper R) (Nest.mpt (t := node) (n := d + 1) w) ↔
              Nest.PutOfP (Nest.PutAny Ss) node (d + 1) U (Nest.upper value) w := by
          intro sv
          have uv : Nest.upper value = value := by
            rcases sv with rfl | ⟨Z, rfl, sZ⟩
            · rfl
            · simp [Nest.upper, sZ]
          have ev : (Nest.level node (d + 1)).E value := uv ▸ evu
          have sv' : value = .atom "term" ∨ ∃ Z, value = .map Z := sv.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
          rw [uv]
          cases hD : Lynx.Term.mapLookup X (.atom "dynamic") with
          | none =>
            have dX : Nest.DE (Nest.level node (d + 1)).E (.map X) := Nest.GC.static gM hD
            have eUX : U = X := by
              have : Nest.upper (.map X) = .map X := by simp [Nest.upper, hD]
              rw [this] at eU; simp only [Lynx.Term.map.injEq] at eU; exact eU.symm
            subst eUX
            obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
              Nest.dput_g (t := node) (n := d + 1) dX rk hP na ev sv (by omega)
            · rw [run] at hput; simp at hput
            refine ⟨_, run, Nest.GC.tc dY, fun q h => onlyY q (by rwa [Nest.upper_tc dY] at h), fun w => ?_⟩
            rw [Nest.upper_tc dY, Nest.denD_mpt, semY]
            exact ⟨fun h => ⟨onlyX.2, h⟩, fun h => h.2⟩
          | some Dy =>
            have eUD : Nest.dynL Dy = U := by
              rw [Nest.upper_dyn hD] at eU; subst eU; rfl
            obtain ⟨res, run, rfl | ⟨R, rfl, gR, oR, -, -, sR⟩⟩ := Nest.gres_g gM hD ev sv' hP (hmono _) na (m := δ + 100) hm
            · rw [Nest.put_static_value_g rk sv, run] at hput; simp at hput
            exact ⟨R, by rw [Nest.put_static_value_g rk sv, run], gR, oR, fun w => by rw [sR, eUD]⟩
        rcases gV.shape with rfl | ⟨Zv, rfl⟩
        · exact staticV (Or.inl rfl)
        cases hZ : Lynx.Term.mapLookup Zv (.atom "dynamic") with
        | none => exact staticV (Or.inr ⟨Zv, rfl, hZ⟩)
        | some Dv =>
          -- A gradual value puts its dynamic part into the dynamic part of the map type.
          have uV : Nest.upper (.map Zv) = Dv := Nest.upper_dyn hZ
          rw [uV] at evu svu' ⊢
          have gG : Nest.GC (Nest.level node (d + 1)) (.map (Nest.dynG X)) :=
            Or.inr ⟨_, _, rfl, by simp [Nest.dynG, Lynx.Term.mapLookup], uX ▸ gM.up_tc,
              by simp only [Nest.dynG, Nest.rmDyn_cons_dyn]; exact Nest.descrC_nil, fun q h => by
                have := (Nest.denD_rmDyn _ q).mpr h
                simp [Nest.dynG, Nest.rmDyn, Nest.denD_map, Lynx.Term.mapLookup, Elixir.STTDescrProofsTest.dn_none] at this⟩
          have hD : Lynx.Term.mapLookup (Nest.dynG X) (.atom "dynamic") =
              some ((Lynx.Term.mapLookup X (.atom "dynamic")).getD (.map X)) := by simp [Nest.dynG, Lynx.Term.mapLookup]
          obtain ⟨res, run, rfl | ⟨R, rfl, gR, oR, -, -, sR⟩⟩ := Nest.gres_g gG hD evu svu' hP (hmono _) na (m := δ + 100) hm
          · rw [Nest.put_gradual_value_g rk hZ, run] at hput; simp at hput
          refine ⟨R, by rw [Nest.put_gradual_value_g rk hZ, run], gR, oR, fun w => ?_⟩
          rw [sR, ← uX, eU]
          rfl
      obtain ⟨resU, runU, ⟨rfl, -⟩ | ⟨Y, rfl, onlyU, dY, onlyY, semY⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) dU rk₂ ok₂ nr₂ na₂ evu svu (by omega)
      · simp [Nest.upper_bound_run gM.ub, eU, Nest.upper_bound_run gK.ub, Nest.upper_bound_run gV.ub, runU] at hputU
      obtain ⟨R', eR'⟩ : ∃ R', Nest.upper R = .map R' := by
        rcases gR.up_tc with h | ⟨R', h, -⟩
        · have := oR Nest.bitPt (by rw [h]; exact Nest.denD_term _)
          simp [Nest.bitPt] at this
        · exact ⟨R', h⟩
      have sub := Nest.next_sub (gR.up_tc : Nest.DE (Nest.level node (d + 1)).E (Nest.upper R)) dY (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node (d + 1) (Nest.upper R) (.map Y) from fun q hq => by
        obtain ⟨w, hw⟩ := Nest.pt_map q (oR q hq)
        rw [eR', hw] at hq
        rw [hw]
        obtain ⟨-, sp, msp, h⟩ := (sR w).mp (by rw [eR']; exact (Nest.denD_mpt w).mpr hq)
        exact ((semY w).mpr (Nest.put_mono (fun u h => h) (fun x h => h) (oks sp msp).1 ok₂ nr₂
          (fun κ h => (sk κ).mp ⟨sp, msp, h⟩) h)))] at sub
      simp only [Lynx.apply_eq, «map_put_gradual_upper:ensures/5», run]
      simp [Erlang.erlang.«element/2», Nest.upper_bound_run gR.ub, Nest.upper_bound_run gM.ub, eU,
        Nest.upper_bound_run gK.ub, Nest.upper_bound_run gV.ub, runU, sub, Lynx.Term.true]
      """

    law map_put_upper_static_key(map, key, value, depth, node),
      requires:
        arrows_gradual?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_gradual?(value, {depth, node}) and depth?(depth) and match?({:ok, _}, Descr.map_put(map, key, value)) and
          match?({:ok, _}, Descr.map_put(Descr.upper_bound(map), key, Descr.upper_bound(value))),
      expects:
        Descr.equal?(
          Descr.upper_bound(elem(Descr.map_put(map, key, value), 1)),
          elem(Descr.map_put(Descr.upper_bound(map), key, Descr.upper_bound(value)), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_upper_static_key:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_upper_static_key:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hg, hk⟩, hgv⟩, -⟩, hput⟩, hputU⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) map
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gM, -, -⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      have hgv : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) value
          (.tuple #[.integer (d : Int), node]) = .ok (.atom "true") := by simpa using hgv
      obtain ⟨gV, -, dVu⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) hgv
      have evu : (Nest.level node (d + 1)).E (Nest.upper value) := Or.inl dVu
      have svu : Nest.upper value = .atom "term" ∨
          ∃ Z, Nest.upper value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dVu with h | ⟨Z, h, sZ⟩
        · exact Or.inl h
        · exact Or.inr ⟨Z, h, sZ.static⟩
      have svu' : Nest.upper value = .atom "term" ∨ ∃ Z, Nest.upper value = .map Z := svu.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      rcases gM.shape with rfl | ⟨X, rfl⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      -- The upper bound of the map type is a static map type.
      have uX : Nest.upper (.map X) = (Lynx.Term.mapLookup X (.atom "dynamic")).getD (.map X) := rfl
      obtain ⟨U, eU, dU⟩ : ∃ U, Nest.upper (.map X) = .map U ∧ Nest.DE (Nest.level node (d + 1)).E (.map U) := by
        rcases gM.up_tc with h | ⟨U, h, sU⟩
        · rw [Nest.upper_bound_run gM.ub, h] at hputU
          simp [Elixir.Module.Types.Descr.«map_put/3», Nest.upper_bound_run gV.ub] at hputU
        · exact ⟨U, h, Or.inr ⟨U, rfl, sU⟩⟩
      -- The put holds in its upper bound the puts at the upper bounds.
      obtain ⟨R, run, gR, oR, sR⟩ : ∃ R, Elixir.Module.Types.Descr.«map_put/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) key value = .ok (.tuple #[.atom "ok", R]) ∧
          Nest.GC (Nest.level node (d + 1)) R ∧ (∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper R) q → q.1.1 = "map") ∧
          ∀ w, Nest.denD (Nest.upper R) (Nest.mpt (t := node) (n := d + 1) w) ↔
            Nest.PutOf node (d + 1) U rs neg ds (Nest.upper value) w := by
        -- A static value is its own upper bound.
        have staticV : (value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none) →
            ∃ R, Elixir.Module.Types.Descr.«map_put/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
              key value = .ok (.tuple #[.atom "ok", R]) ∧ Nest.GC (Nest.level node (d + 1)) R ∧
            (∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper R) q → q.1.1 = "map") ∧
            ∀ w, Nest.denD (Nest.upper R) (Nest.mpt (t := node) (n := d + 1) w) ↔
              Nest.PutOf node (d + 1) U rs neg ds (Nest.upper value) w := by
          intro sv
          have uv : Nest.upper value = value := by
            rcases sv with rfl | ⟨Z, rfl, sZ⟩
            · rfl
            · simp [Nest.upper, sZ]
          have ev : (Nest.level node (d + 1)).E value := uv ▸ evu
          have sv' : value = .atom "term" ∨ ∃ Z, value = .map Z := sv.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
          rw [uv]
          cases hD : Lynx.Term.mapLookup X (.atom "dynamic") with
          | none =>
            have dX : Nest.DE (Nest.level node (d + 1)).E (.map X) := Nest.GC.static gM hD
            have eUX : U = X := by
              have : Nest.upper (.map X) = .map X := by simp [Nest.upper, hD]
              rw [this] at eU; simp only [Lynx.Term.map.injEq] at eU; exact eU.symm
            subst eUX
            obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
              Nest.dput (t := node) (n := d + 1) dX rk ok nr na ev sv (by omega)
            · rw [run] at hput; simp at hput
            refine ⟨_, run, Nest.GC.tc dY, fun q h => onlyY q (by rwa [Nest.upper_tc dY] at h), fun w => ?_⟩
            rw [Nest.upper_tc dY, Nest.denD_mpt, semY]
            exact ⟨fun h => ⟨onlyX.2, h⟩, fun h => h.2⟩
          | some Dy =>
            have eUD : Nest.dynL Dy = U := by
              rw [Nest.upper_dyn hD] at eU; subst eU; rfl
            obtain ⟨res, run, rfl | ⟨R, rfl, gR, oR, -, -, sR⟩⟩ := Nest.gres gM hD ev sv' ok nr na (m := δ + 100) hm
            · rw [Nest.put_static_value rk sv, run] at hput; simp at hput
            exact ⟨R, by rw [Nest.put_static_value rk sv, run], gR, oR, fun w => by rw [sR, eUD]⟩
        rcases gV.shape with rfl | ⟨Zv, rfl⟩
        · exact staticV (Or.inl rfl)
        cases hZ : Lynx.Term.mapLookup Zv (.atom "dynamic") with
        | none => exact staticV (Or.inr ⟨Zv, rfl, hZ⟩)
        | some Dv =>
          -- A gradual value puts its dynamic part into the dynamic part of the map type.
          have uV : Nest.upper (.map Zv) = Dv := Nest.upper_dyn hZ
          rw [uV] at evu svu' ⊢
          have gG : Nest.GC (Nest.level node (d + 1)) (.map (Nest.dynG X)) :=
            Or.inr ⟨_, _, rfl, by simp [Nest.dynG, Lynx.Term.mapLookup], uX ▸ gM.up_tc,
              by simp only [Nest.dynG, Nest.rmDyn_cons_dyn]; exact Nest.descrC_nil, fun q h => by
                have := (Nest.denD_rmDyn _ q).mpr h
                simp [Nest.dynG, Nest.rmDyn, Nest.denD_map, Lynx.Term.mapLookup, Elixir.STTDescrProofsTest.dn_none] at this⟩
          have hD : Lynx.Term.mapLookup (Nest.dynG X) (.atom "dynamic") =
              some ((Lynx.Term.mapLookup X (.atom "dynamic")).getD (.map X)) := by simp [Nest.dynG, Lynx.Term.mapLookup]
          obtain ⟨res, run, rfl | ⟨R, rfl, gR, oR, -, -, sR⟩⟩ := Nest.gres gG hD evu svu' ok nr na (m := δ + 100) hm
          · rw [Nest.put_gradual_value rk hZ, run] at hput; simp at hput
          refine ⟨R, by rw [Nest.put_gradual_value rk hZ, run], gR, oR, fun w => ?_⟩
          rw [sR, ← uX, eU]
          rfl
      obtain ⟨resU, runU, ⟨rfl, -⟩ | ⟨Y, rfl, onlyU, dY, onlyY, semY⟩⟩ :=
        Nest.dput (t := node) (n := d + 1) dU rk ok nr na evu svu (by omega)
      · simp [Nest.upper_bound_run gM.ub, eU, Nest.upper_bound_run gV.ub, runU] at hputU
      obtain ⟨R', eR'⟩ : ∃ R', Nest.upper R = .map R' := by
        rcases gR.up_tc with h | ⟨R', h, -⟩
        · have := oR Nest.bitPt (by rw [h]; exact Nest.denD_term _)
          simp [Nest.bitPt] at this
        · exact ⟨R', h⟩
      have same : ∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper R) q ↔ Nest.denD (.map Y) q := by
        intro q
        by_cases h : q.1.1 = "map"
        · obtain ⟨w, hw⟩ := Nest.pt_map q h
          rw [eR', hw, hw, ← Nest.denD_mpt, ← eR', sR, semY]
          exact ⟨fun h => h.2, fun h => ⟨onlyU.2, h⟩⟩
        · exact ⟨fun hq => absurd (oR q hq) h, fun hq => absurd (onlyY q hq) h⟩
      simp only [Lynx.apply_eq, «map_put_upper_static_key:ensures/5», run]
      simp [Erlang.erlang.«element/2», Nest.upper_bound_run gR.ub, Nest.upper_bound_run gM.ub, eU,
        Nest.upper_bound_run gV.ub, runU, Nest.next_eq_true gR.up_tc dY (m := δ + 100) (by omega) same, Lynx.Term.true]
      """

    law map_put_lower_static(map, key, value, depth, node),
      requires:
        arrows_gradual?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and match?({:ok, _}, Descr.map_put(map, key, value)),
      expects:
        Descr.equal?(
          Descr.lower_bound(elem(Descr.map_put(map, key, value), 1)),
          got(Descr.map_put(Descr.lower_bound(map), key, value))
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_put_lower_static:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_put_lower_static:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨hg, hk⟩, hv⟩, -⟩, hput⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) map
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gM, -, -⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      have sv' : value = .atom "term" ∨ ∃ Z, value = .map Z := sv.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      rcases gM.shape with rfl | ⟨X, rfl⟩
      · simp [Elixir.Module.Types.Descr.«map_put/3»] at hput
      cases hD : Lynx.Term.mapLookup X (.atom "dynamic") with
      | none =>
        -- Static maps are their own lower bound.
        have dX : Nest.DE (Nest.level node (d + 1)).E (.map X) := Nest.GC.static gM hD
        have lX : Nest.lower (.map X) = .map X := by simp [Nest.lower, Nest.rmDyn_static hD]
        obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, -, dY, -, -⟩⟩ :=
          Nest.dput (t := node) (n := d + 1) dX rk ok nr na ev sv (by omega)
        · rw [run] at hput; simp at hput
        have lY : Nest.lower (.map Y) = .map Y := by simp [Nest.lower, Nest.rmDyn_static (Nest.de_map dY).static]
        simp only [Lynx.apply_eq, «map_put_lower_static:ensures/5»]
        simp [run, Erlang.erlang.«element/2», Nest.lower_bound_run (Or.inr ⟨_, rfl⟩), lX, lY, «got/1», pure, Except.pure,
          Nest.next_eq_true dY dY (m := δ + 100) (by omega) (fun _ => Iff.rfl), Lynx.Term.true]
      | some Dy =>
        obtain ⟨res, run, rfl | ⟨R, rfl, gR, oR, oS, s₁, -⟩⟩ := Nest.gres gM hD ev sv' ok nr na (m := δ + 100) hm
        · rw [Nest.put_static_value rk sv, run] at hput; simp at hput
        obtain ⟨R', rfl⟩ : ∃ R', R = .map R' := by
          rcases gR.shape with rfl | ⟨R', rfl⟩
          · have := oR Nest.bitPt (by simp [Nest.upper, Nest.denD_term])
            simp [Nest.bitPt] at this
          · exact ⟨R', rfl⟩
        -- The lower bound of the map type.
        have dL : Nest.DE (Nest.level node (d + 1)).E (.map (Nest.rmDyn X)) := gM.low_tc
        -- The put at the lower bound, or none() when it gives `:badmap`.
        obtain ⟨G, rG, dG, sG⟩ : ∃ G, (do
            let r ← Elixir.Module.Types.Descr.«map_put/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
              (.map (Nest.rmDyn X)) key value
            «got/1» r) = .ok G ∧ Nest.DE (Nest.level node (d + 1)).E G ∧
            ∀ q : Nest.PN node (d + 1), Nest.denD (Nest.lower (.map R')) q ↔ Nest.denD G q := by
          obtain ⟨resL, runL, ⟨rfl, nL⟩ | ⟨Y, rfl, onlyL, dY, onlyY, semY⟩⟩ :=
            Nest.dput (t := node) (n := d + 1) dL rk ok nr na ev sv (by omega)
          · -- The lower bound holds no maps, so the put holds none at its lower bound.
            have noP : ∀ w, ¬Nest.PutOf node (d + 1) (Nest.rmDyn X) rs neg ds value w := by
              rcases oS with oS | h
              · intro w ⟨⟨u, hu⟩, _⟩
                exact nL ⟨oS, u, hu⟩
              · exact h
            refine ⟨.map [], by simp [runL, «got/1», Elixir.Module.Types.Descr.«none/0»], Or.inr ⟨[], rfl, Nest.descrC_nil⟩,
              fun q => ?_⟩
            rw [Nest.denD_lower]
            constructor
            · intro hq
              by_cases h : q.1.1 = "map"
              · obtain ⟨w, hw⟩ := Nest.pt_map q h
                rw [hw, ← Nest.denD_mpt, s₁] at hq
                exact absurd hq (noP w)
              · exact absurd (oR q (Nest.GC.inv gR q hq)) h
            · intro hq; simp [Nest.denD_map, Lynx.Term.mapLookup, Elixir.STTDescrProofsTest.dn_none] at hq
          · refine ⟨.map Y, by simp [runL, «got/1», pure, Except.pure], dY, fun q => ?_⟩
            rw [Nest.denD_lower]
            by_cases h : q.1.1 = "map"
            · obtain ⟨w, hw⟩ := Nest.pt_map q h
              rw [hw, hw, ← Nest.denD_mpt, s₁, semY]
              exact ⟨fun h => h.2, fun h => ⟨onlyL.2, h⟩⟩
            · exact ⟨fun hq => absurd (oR q (Nest.GC.inv gR q hq)) h, fun hq => absurd (onlyY q hq) h⟩
        have eq := Nest.next_eq_true gR.low_tc dG (m := δ + 100) (by omega) sG
        simp only [Nest.lower] at eq
        simp only [Lynx.apply_eq, «map_put_lower_static:ensures/5», Nest.put_static_value rk sv, run]
        simp [Erlang.erlang.«element/2», Nest.lower_bound_run gR.shape, Nest.lower_bound_run (Or.inr ⟨_, rfl⟩), Nest.lower]
        cases h : Elixir.Module.Types.Descr.«map_put/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map (Nest.rmDyn X)) key value with
        | error e => rw [h] at rG; cases rG
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at rG
          simp [rG, eq, Lynx.Term.true]
      """

    law map_update_force(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key) and not Descr.empty?(value) and match?({:ok, _}, Descr.map_put_key(map, key, value)),
      expects:
        Descr.equal?(
          elem(Descr.map_update(map, Descr.atom([key]), value, :force, true), 1),
          elem(Descr.map_put_key(map, key, value), 1)
        ) and elem(Descr.map_update(map, Descr.atom([key]), value, :force, true), 2) == [] and
          Descr.equal?(
            elem(Descr.map_update(map, Descr.atom([key]), value, :force, true), 0),
            got(Descr.map_get(map, Descr.atom([key])))
          ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_force:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_force:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hput⟩ := requires
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del sx (m := δ + 100) hm
      · rw [run] at hput; simp at hput
      -- Forcing the key gives the maps of the put, and the values the maps of the type hold at the key.
      obtain ⟨ru, runU, ⟨rfl, nU⟩ | ⟨T, Y', rfl, -, hT, sT, dY', onlyY', semY'⟩⟩ :=
        Nest.update_force (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del sx (m := δ + 100) hm
      · exact absurd onlyX nU
      have same : ∀ v : Nest.PN node (d + 1), Nest.denD (.map Y') v ↔ Nest.denD (.map Y) v := by
        intro v
        by_cases h : v.1.1 = "map"
        · obtain ⟨w, hw⟩ := Nest.pt_map v h
          rw [hw, hw, semY', semY]
        · exact ⟨fun h' => absurd (onlyY' v h') h, fun h' => absurd (onlyY v h') h⟩
      have hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (Nest.atomT a) =
          .ok (Nest.splitT [.atom a] (.atom "nil") []) := by
        rw [show δ + 100 = (δ + 99) + 1 from rfl, Nest.split_one]; rfl
      have hs : Nest.SplitOk [.atom a] (.atom "nil") [] := ⟨by simp, Or.inl rfl, by simp, by simp⟩
      have key : ∀ κ, Nest.SplitKey [.atom a] (.atom "nil") [] κ ↔ κ = .atom a := fun κ => by
        cases κ with
        | atom s => simp [Nest.SplitKey]
        | dom k i => simp [Nest.SplitKey]
      have none : ∀ y, ¬(Nest.level node (d + 1)).den (.map []) y := fun y h => (Nest.none_field (Nest.level node (d + 1)).ef).2
        (some y) (by rw [show (Lynx.Term.atom "false") = boolAtom Bool.false from rfl, Nest.fieldSem_mk]; exact Or.inr ⟨y, rfl, h⟩)
      obtain ⟨rg, runG, ⟨rfl, nG⟩ | ⟨rfl, -, noKey⟩ | ⟨G, rfl, hG, -, -, sG⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) hs hm hk
      · exact absurd onlyX nG
      · have sem : ∀ y, (Nest.level node (d + 1)).den T y ↔ (Nest.level node (d + 1)).den (.map []) y := by
          intro y
          refine ⟨fun h => ?_, fun h => absurd h (none y)⟩
          obtain ⟨w, hw, wa⟩ := (sT y).mp h
          rw [noKey w hw _ ((key _).mpr rfl)] at wa
          cases wa
        simp only [Lynx.apply_eq, «map_update_force:ensures/5», run, Lynx.Except.ok_bind]
        rw [Nest.atom_one a]
        simp [Erlang.erlang.«element/2», Erlang.erlang.«==/2», runU, runG, «got/1», Elixir.Module.Types.Descr.«none/0»,
          Nest.next_eq_true dY' dY (m := δ + 100) (by omega) same,
          Nest.elem_equal (Nest.level node (d + 1)).ef hT (Nest.level node (d + 1)).ef.none sem (m := δ + 100)
            (by rw [Nest.level_K] at hm ⊢; omega), Lynx.Term.true]
      · have sem : ∀ y, (Nest.level node (d + 1)).den T y ↔ (Nest.level node (d + 1)).den G y := fun y => by
          rw [sT, sG]
          exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, hw, _, (key _).mpr rfl, wa⟩,
            fun ⟨w, hw, κ, hκ, wκ⟩ => by rw [(key κ).mp hκ] at wκ; exact ⟨w, hw, wκ⟩⟩
        simp only [Lynx.apply_eq, «map_update_force:ensures/5», run, Lynx.Except.ok_bind]
        rw [Nest.atom_one a]
        simp [Erlang.erlang.«element/2», Erlang.erlang.«==/2», runU, runG, «got/1»,
          Nest.next_eq_true dY' dY (m := δ + 100) (by omega) same,
          Nest.elem_equal (Nest.level node (d + 1)).ef hT hG sem (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega),
          Lynx.Term.true]
      """

    law map_update_missing(map, key, value, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key) and mode in [:keep, :reject] and not Descr.empty?(value) and
          match?({:ok, _}, Descr.map_put_key(map, key, value)),
      expects:
        (if Descr.map_fetch_key(map, key) == :badkey do
          Descr.map_update(map, Descr.atom([key]), value, mode, true) == {:error, [badkey: key]}
        else
          Descr.equal?(
            elem(Descr.map_update(map, Descr.atom([key]), value, mode, true), 1),
            elem(Descr.map_put_key(map, key, value), 1)
          ) and elem(Descr.map_update(map, Descr.atom([key]), value, mode, true), 2) == [] and
            Descr.equal?(
              elem(Descr.map_update(map, Descr.atom([key]), value, mode, true), 0),
              got(Descr.map_get(map, Descr.atom([key])))
            )
        end),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_missing:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_missing:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hmode⟩, hne⟩, hput⟩ := requires
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨keep, rfl⟩ : ∃ keep, mode = Nest.modeT keep := by
        by_cases h : mode = .atom "keep"
        · exact ⟨true, by simp [h, Nest.modeT]⟩
        · by_cases h' : mode = .atom "reject"
          · exact ⟨false, by simp [h', Nest.modeT]⟩
          · simp [Lynx.Term.isMember, h, h'] at hmode
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«map_put_key/3»] at hput
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del sx (m := δ + 100) hm
      · rw [run] at hput; simp at hput
      obtain ⟨ru, runU, ⟨rfl, nU⟩ | ⟨-, hbad, hgood⟩⟩ :=
        Nest.update_keep (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del ⟨y₀, hy₀⟩ sx keep (m := δ + 100) hm
      · exact absurd onlyX nU
      obtain ⟨rf, runF, ⟨rfl, nF⟩ | ⟨rfl, -, lack⟩ | ⟨e, rfl, -, -, all, -⟩⟩ :=
        Nest.fetch_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a (m := δ + 100) hm
      · exact absurd onlyX nF
      · -- Some map lacks the key: `badkey`.
        simp only [Lynx.apply_eq, «map_update_missing:ensures/6», runF, Lynx.Except.ok_bind]
        rw [Nest.atom_one a]
        simp [Erlang.erlang.«==/2», runU, hbad lack, Lynx.Term.true]
      -- Every map holds the key: the put, and the old values.
      have nlack : ¬∃ w, Nest.MT node (d + 1) X w ∧ w (.atom a) = none := fun ⟨w, hw, wa⟩ => by
        obtain ⟨x, hx, -⟩ := all w hw
        rw [wa] at hx; cases hx
      obtain ⟨T, Y', rfl, hT, sT, dY', onlyY', semY'⟩ := hgood nlack
      have same : ∀ v : Nest.PN node (d + 1), Nest.denD (.map Y') v ↔ Nest.denD (.map Y) v := by
        intro v
        by_cases h : v.1.1 = "map"
        · obtain ⟨w, hw⟩ := Nest.pt_map v h
          rw [hw, hw, semY', semY]
        · exact ⟨fun h' => absurd (onlyY' v h') h, fun h' => absurd (onlyY v h') h⟩
      have hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (Nest.atomT a) =
          .ok (Nest.splitT [.atom a] (.atom "nil") []) := by
        rw [show δ + 100 = (δ + 99) + 1 from rfl, Nest.split_one]; rfl
      have hs : Nest.SplitOk [.atom a] (.atom "nil") [] := ⟨by simp, Or.inl rfl, by simp, by simp⟩
      have key : ∀ κ, Nest.SplitKey [.atom a] (.atom "nil") [] κ ↔ κ = .atom a := fun κ => by
        cases κ with
        | atom s => simp [Nest.SplitKey]
        | dom k i => simp [Nest.SplitKey]
      have none : ∀ y, ¬(Nest.level node (d + 1)).den (.map []) y := fun y h => (Nest.none_field (Nest.level node (d + 1)).ef).2
        (some y) (by rw [show (Lynx.Term.atom "false") = boolAtom Bool.false from rfl, Nest.fieldSem_mk]; exact Or.inr ⟨y, rfl, h⟩)
      have fetchE : Erlang.erlang.«==/2» (.tuple #[.atom "false", e]) (.atom "badkey") = .ok (.atom "false") := by
        simp [Erlang.erlang.«==/2»]
      obtain ⟨rg, runG, ⟨rfl, nG⟩ | ⟨rfl, -, noKey⟩ | ⟨G, rfl, hG, -, -, sG⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) hs hm hk
      · exact absurd onlyX nG
      · have sem : ∀ y, (Nest.level node (d + 1)).den T y ↔ (Nest.level node (d + 1)).den (.map []) y := by
          intro y
          refine ⟨fun h => ?_, fun h => absurd h (none y)⟩
          obtain ⟨w, hw, wa⟩ := (sT y).mp h
          rw [noKey w hw _ ((key _).mpr rfl)] at wa
          cases wa
        simp only [Lynx.apply_eq, «map_update_missing:ensures/6», runF, fetchE, run, Lynx.Except.ok_bind]
        rw [Nest.atom_one a]
        simp [Erlang.erlang.«element/2», Erlang.erlang.«==/2», runU, runG, «got/1», Elixir.Module.Types.Descr.«none/0»,
          Nest.next_eq_true dY' dY (m := δ + 100) (by omega) same,
          Nest.elem_equal (Nest.level node (d + 1)).ef hT (Nest.level node (d + 1)).ef.none sem (m := δ + 100)
            (by rw [Nest.level_K] at hm ⊢; omega), Lynx.Term.true]
      · have sem : ∀ y, (Nest.level node (d + 1)).den T y ↔ (Nest.level node (d + 1)).den G y := fun y => by
          rw [sT, sG]
          exact ⟨fun ⟨w, hw, wa⟩ => ⟨w, hw, _, (key _).mpr rfl, wa⟩,
            fun ⟨w, hw, κ, hκ, wκ⟩ => by rw [(key κ).mp hκ] at wκ; exact ⟨w, hw, wκ⟩⟩
        simp only [Lynx.apply_eq, «map_update_missing:ensures/6», runF, fetchE, run, Lynx.Except.ok_bind]
        rw [Nest.atom_one a]
        simp [Erlang.erlang.«element/2», Erlang.erlang.«==/2», runU, runG, «got/1»,
          Nest.next_eq_true dY' dY (m := δ + 100) (by omega) same,
          Nest.elem_equal (Nest.level node (d + 1)).ef hT hG sem (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega),
          Lynx.Term.true]
      """

    law map_update_found(map, key, atoms, value, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and mode in [:keep, :reject] and
          unnamed_keys?(key, atoms) and not Descr.empty?(value) and
          Descr.map_update(map, key, value, mode, true) != :badmap,
      expects:
        match?({:error, _}, Descr.map_update(map, key, value, mode, true)) ==
          Descr.empty?(got(Descr.map_get(map, key))),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_found:requires/7», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_found:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hmp, hk⟩, hv⟩, -⟩, hmode⟩, hun⟩, hne⟩, hbad⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have ef := (Nest.level node (d + 1)).ef
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The key splits into no named atoms.
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      obtain ⟨rs', rfl⟩ := Nest.atoms_of ok.hrs
      obtain ⟨ds', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok.hds d md; ⟨s, e⟩
      have nr' : ∀ N, neg = .map N → rs' = [] := fun N e => by have := nr N e; cases rs' <;> simp_all
      obtain ⟨A, -, hA⟩ := Nest.unnamed_ok (t := node) (n := d) dk (m := δ + 100) (by omega) hun
      have rs0 := Nest.unnamed_rs ok nr sk A hA
      obtain rfl : rs' = [] := by cases rs' <;> simp_all
      -- The mode.
      obtain ⟨keep, rfl⟩ : ∃ keep, mode = Nest.modeT keep := by
        by_cases h : mode = .atom "keep"
        · exact ⟨Bool.true, h⟩
        by_cases h' : mode = .atom "reject"
        · exact ⟨Bool.false, h'⟩
        simp [Lynx.Term.isMember, h, h'] at hmode
      have hmd : Nest.Mode (if keep then "keep" else "reject") := by
        cases keep
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · rcases sv with rfl | ⟨Z, rfl, sZ⟩
        · cases keep <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk, Lynx.Term.getMapKeys, Nest.modeT,
              Elixir.Module.Types.Descr.«map_update_unchecked/4», Erlang.erlang.«/=/2»] at hbad
        · cases keep <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk, Lynx.Term.getMapKeys_single, sZ, Nest.modeT,
              Elixir.Module.Types.Descr.«map_update_unchecked/4», Erlang.erlang.«/=/2»] at hbad
      have hX : Nest.DE (Nest.level node (d + 1)).E (.map X) := Or.inr ⟨X, rfl, sX⟩
      have upd : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) key value (.atom (if keep then "keep" else "reject")) (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_unchecked/4» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (Nest.splitT (([] : List String).map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom))
            (.tuple #[.tuple #[.atom "constant", .tuple #[value, .atom "false"]], .atom (if keep then "keep" else "reject")])
            (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update/5»
        rcases sv with rfl | ⟨Z, rfl, sZ⟩
        · cases keep <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», rk,
            Lynx.Term.getMapKeys]
        · cases keep <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», rk,
            Lynx.Term.getMapKeys_single, sZ]
      have hkL : ∀ k, k + 6 = δ + 100 → ∀ lines : List Lynx.Term,
          (∀ L ∈ lines, Nest.MLine (Nest.level node (d + 1)).E L ∧ ∃ w, Nest.InMLine (Nest.level node (d + 1)).den L w) →
          ∀ (bd : Bool) a, ∃ (ba : List Lynx.Term) (F : Lynx.Term), Elixir.Module.Types.Descr.«map_update_named_key/5»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (k + 5)) (Lynx.Term.list lines) (.atom a)
            (.tuple #[.tuple #[.atom "constant", .tuple #[value, .atom "false"]], .atom (if keep then "keep" else "reject")])
            (boolAtom bd) (.atom "true") = .ok (.tuple #[Lynx.Term.list ba, F]) ∧
            FieldValue (Nest.level node (d + 1)).E F ∧
            ∀ o, Nest.FieldSem (Nest.level node (d + 1)).den F o ↔ ∃ L ∈ lines, Nest.LongM (Nest.level node (d + 1)).den L a o :=
        fun k ek lines hl bd a => by
          have := Nest.hk_val ef (n := k + 2) (by omega) ev ⟨y₀, hy₀⟩ keep lines hl bd a
          cases keep <;> exact this
      -- The update and `map_get/2`.
      rw [show Nest.modeT keep = .atom (if keep then "keep" else "reject") from rfl] at hbad ⊢
      cases hr : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) key value (.atom (if keep then "keep" else "reject")) (.atom "true") with
      | error e => rw [hr] at hbad; simp at hbad
      | ok r =>
      rcases Nest.flag_update hX ok (fun _ _ => rfl) _ hmd hm upd hkL hr with rfl | ⟨er, extra, mis, f, only, rfl, hres, -, -, -, hf⟩
      · rw [hr] at hbad; simp [Erlang.erlang.«/=/2»] at hbad
      have hf := hf (by cases keep <;> simp) rfl
      obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨T₀, rfl, hT₀, -, ⟨x₀, hx₀⟩, sT₀⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) hX ok (m := δ + 100) (by omega) rk
      · exact absurd only nX
      · -- Nothing is found.
        have f0 : f = Bool.false := by
          cases f
          · rfl
          · obtain ⟨x, w, hw, κ, hκ, e⟩ := (hf.mp rfl)
            rw [eX w hw κ hκ] at e; cases e
        subst f0
        rcases hres with ⟨-, rfl⟩ | ⟨e, -⟩
        · obtain ⟨b, rb, sb⟩ := ef.empty1 (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) ef.none
          have b1 : b = Bool.true := sb.mpr fun x hx => ef.den_none x hx
          subst b1
          simp only [Lynx.apply_eq, «map_update_found:ensures/7»]
          rw [hr]
          simp [runX, «got/1», Elixir.Module.Types.Descr.«none/0», Erlang.erlang.«==/2», rb, boolAtom]
        · cases e
      · -- Something is found.
        have f1 : f = Bool.true := hf.mpr (let ⟨w, hw, κ, hκ, e⟩ := (sT₀ x₀).mp hx₀; ⟨x₀, w, hw, κ, hκ, e⟩)
        subst f1
        rcases hres with ⟨e, -⟩ | ⟨-, T, Y, rfl⟩
        · cases e
        obtain ⟨b, rb, sb⟩ := ef.empty1 (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) hT₀
        have b0 : b = Bool.false := by
          cases b
          · rfl
          · exact absurd hx₀ (sb.mp rfl x₀)
        subst b0
        simp only [Lynx.apply_eq, «map_update_found:ensures/7»]
        rw [hr]
        simp [runX, «got/1», rb, Erlang.erlang.«==/2», boolAtom]
      """

    law map_delete_found(map, key, atoms, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and depth?(depth) and
          mode in [:keep, :reject] and unnamed_keys?(key, atoms) and
          Descr.map_update(map, key, :delete, mode, true) != :badmap,
      expects:
        match?({:error, _}, Descr.map_update(map, key, :delete, mode, true)) ==
          Descr.empty?(got(Descr.map_get(map, key))),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_delete_found:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_delete_found:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hmp, hk⟩, -⟩, hmode⟩, hun⟩, hbad⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have ef := (Nest.level node (d + 1)).ef
      -- The key splits into no named atoms.
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      obtain ⟨rs', rfl⟩ := Nest.atoms_of ok.hrs
      obtain ⟨ds', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok.hds d md; ⟨s, e⟩
      have nr' : ∀ N, neg = .map N → rs' = [] := fun N e => by have := nr N e; cases rs' <;> simp_all
      obtain ⟨A, -, hA⟩ := Nest.unnamed_ok (t := node) (n := d) dk (m := δ + 100) (by omega) hun
      have rs0 := Nest.unnamed_rs ok nr sk A hA
      obtain rfl : rs' = [] := by cases rs' <;> simp_all
      -- The mode.
      obtain ⟨keep, rfl⟩ : ∃ keep, mode = Nest.modeT keep := by
        by_cases h : mode = .atom "keep"
        · exact ⟨Bool.true, h⟩
        by_cases h' : mode = .atom "reject"
        · exact ⟨Bool.false, h'⟩
        simp [Lynx.Term.isMember, h, h'] at hmode
      have hmd : Nest.Mode (if keep then "keep" else "reject") := by
        cases keep
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · cases keep <;>
          simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
            Erlang.erlang.«=:=/2», rk, Nest.modeT,
            Elixir.Module.Types.Descr.«map_update_unchecked/4», Erlang.erlang.«/=/2»] at hbad
      have hX : Nest.DE (Nest.level node (d + 1)).E (.map X) := Or.inr ⟨X, rfl, sX⟩
      have upd : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) key (.atom "delete") (.atom (if keep then "keep" else "reject")) (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_unchecked/4» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (Nest.splitT (([] : List String).map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom))
            (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom (if keep then "keep" else "reject")])
            (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update/5»
        cases keep <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», rk,
          Elixir.Module.Types.Descr.«none/0»]
      have hkL : ∀ k, k + 6 = δ + 100 → ∀ lines : List Lynx.Term,
          (∀ L ∈ lines, Nest.MLine (Nest.level node (d + 1)).E L ∧ ∃ w, Nest.InMLine (Nest.level node (d + 1)).den L w) →
          ∀ (bd : Bool) a, ∃ (ba : List Lynx.Term) (F : Lynx.Term), Elixir.Module.Types.Descr.«map_update_named_key/5»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (k + 5)) (Lynx.Term.list lines) (.atom a)
            (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom (if keep then "keep" else "reject")])
            (boolAtom bd) (.atom "true") = .ok (.tuple #[Lynx.Term.list ba, F]) ∧
            FieldValue (Nest.level node (d + 1)).E F ∧
            ∀ o, Nest.FieldSem (Nest.level node (d + 1)).den F o ↔ ∃ L ∈ lines, Nest.LongM (Nest.level node (d + 1)).den L a o :=
        fun k ek lines hl bd a => by
          exact Nest.hk_del ef (n := k + 2) (by omega) hmd lines hl bd a
      -- The update and `map_get/2`.
      rw [show Nest.modeT keep = .atom (if keep then "keep" else "reject") from rfl] at hbad ⊢
      cases hr : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) key (.atom "delete") (.atom (if keep then "keep" else "reject")) (.atom "true") with
      | error e => rw [hr] at hbad; simp at hbad
      | ok r =>
      rcases Nest.flag_update hX ok (fun _ _ => rfl) _ hmd hm upd hkL hr with rfl | ⟨er, extra, mis, f, only, rfl, hres, -, -, -, hf⟩
      · rw [hr] at hbad; simp [Erlang.erlang.«/=/2»] at hbad
      have hf := hf (by cases keep <;> simp) rfl
      obtain ⟨resX, runX, ⟨-, nX⟩ | ⟨rfl, -, eX⟩ | ⟨T₀, rfl, hT₀, -, ⟨x₀, hx₀⟩, sT₀⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) hX ok (m := δ + 100) (by omega) rk
      · exact absurd only nX
      · -- Nothing is found.
        have f0 : f = Bool.false := by
          cases f
          · rfl
          · obtain ⟨x, w, hw, κ, hκ, e⟩ := (hf.mp rfl)
            rw [eX w hw κ hκ] at e; cases e
        subst f0
        rcases hres with ⟨-, rfl⟩ | ⟨e, -⟩
        · obtain ⟨b, rb, sb⟩ := ef.empty1 (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) ef.none
          have b1 : b = Bool.true := sb.mpr fun x hx => ef.den_none x hx
          subst b1
          simp only [Lynx.apply_eq, «map_delete_found:ensures/6»]
          rw [hr]
          simp [runX, «got/1», Elixir.Module.Types.Descr.«none/0», Erlang.erlang.«==/2», rb, boolAtom]
        · cases e
      · -- Something is found.
        have f1 : f = Bool.true := hf.mpr (let ⟨w, hw, κ, hκ, e⟩ := (sT₀ x₀).mp hx₀; ⟨x₀, w, hw, κ, hκ, e⟩)
        subst f1
        rcases hres with ⟨e, -⟩ | ⟨-, T, Y, rfl⟩
        · cases e
        obtain ⟨b, rb, sb⟩ := ef.empty1 (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) hT₀
        have b0 : b = Bool.false := by
          cases b
          · rfl
          · exact absurd hx₀ (sb.mp rfl x₀)
        subst b0
        simp only [Lynx.apply_eq, «map_delete_found:ensures/6»]
        rw [hr]
        simp [runX, «got/1», rb, Erlang.erlang.«==/2», boolAtom]
      """

    law map_update_baddomain(map, key, value, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and
          arrows_static?(value, {depth, node}) and depth?(depth) and mode in [:force, :keep, :reject] and
          not Descr.empty?(value) and match?({_, _, _}, Descr.map_update(map, key, value, mode, true)),
      expects: baddomains?(map, key, elem(Descr.map_update(map, key, value, mode, true), 2), update_kinds()),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key and value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_update_baddomain:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_update_baddomain:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨hmp, hk⟩, hv⟩, -⟩, hmode⟩, hne⟩, hupd⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have ef := (Nest.level node (d + 1)).ef
      have dv := Nest.arrows_static_ok hv
      have ev : (Nest.level node (d + 1)).E value := Or.inl dv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The split of the key.
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      obtain ⟨rs', rfl⟩ := Nest.atoms_of ok.hrs
      obtain ⟨ds', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok.hds d md; ⟨s, e⟩
      have nr' : ∀ N, neg = .map N → rs' = [] := fun N e => by have := nr N e; cases rs' <;> simp_all
      have hDs : ∀ s ∈ ds', s ∈ Nest.domainKinds := fun s ms => by
        obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
      obtain ⟨md, rfl, hmd⟩ : ∃ md, mode = .atom md ∧ Nest.Mode md := by
        by_cases h : mode = .atom "force"
        · exact ⟨_, h, Or.inl rfl⟩
        by_cases h' : mode = .atom "keep"
        · exact ⟨_, h', Or.inr (Or.inl rfl)⟩
        by_cases h'' : mode = .atom "reject"
        · exact ⟨_, h'', Or.inr (Or.inr rfl)⟩
        simp [Lynx.Term.isMember, h, h', h''] at hmode
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · rcases sv with rfl | ⟨Z, rfl, sZ⟩
        · rcases hmd with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk, Lynx.Term.getMapKeys,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupd
        · rcases hmd with rfl | rfl | rfl <;>
            simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
              Erlang.erlang.«=:=/2», rk, Lynx.Term.getMapKeys_single, sZ,
              Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupd
      have hX : Nest.DE (Nest.level node (d + 1)).E (.map X) := Or.inr ⟨X, rfl, sX⟩
      have upd : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) key value (.atom md) (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_unchecked/4» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (Nest.splitT (rs'.map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom))
            (.tuple #[.tuple #[.atom "constant", .tuple #[value, .atom "false"]], .atom md]) (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update/5»
        rcases sv with rfl | ⟨Z, rfl, sZ⟩
        · rcases hmd with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
            Erlang.erlang.«=:=/2», rk, Lynx.Term.getMapKeys]
        · rcases hmd with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
            Erlang.erlang.«=:=/2», rk, Lynx.Term.getMapKeys_single, sZ]
      have hkL : ∀ k, k + 6 = δ + 100 → ∀ lines : List Lynx.Term,
          (∀ L ∈ lines, Nest.MLine (Nest.level node (d + 1)).E L ∧ ∃ w, Nest.InMLine (Nest.level node (d + 1)).den L w) →
          ∀ (bd : Bool) a, ∃ (ba : List Lynx.Term) (F : Lynx.Term), Elixir.Module.Types.Descr.«map_update_named_key/5»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (k + 5)) (Lynx.Term.list lines) (.atom a)
            (.tuple #[.tuple #[.atom "constant", .tuple #[value, .atom "false"]], .atom md])
            (boolAtom bd) (.atom "true") = .ok (.tuple #[Lynx.Term.list ba, F]) ∧
            FieldValue (Nest.level node (d + 1)).E F ∧
            ∀ o, Nest.FieldSem (Nest.level node (d + 1)).den F o ↔ ∃ L ∈ lines, Nest.LongM (Nest.level node (d + 1)).den L a o :=
        fun k ek lines hl bd a => by
          rcases hmd with rfl | rfl | rfl
          · exact Nest.hk_force ef (n := k + 2) (by omega) ev lines hl bd a
          · exact Nest.hk_val ef (n := k + 2) (by omega) ev ⟨y₀, hy₀⟩ Bool.true lines hl bd a
          · exact Nest.hk_val ef (n := k + 2) (by omega) ev ⟨y₀, hy₀⟩ Bool.false lines hl bd a
      -- The update succeeds, with the errors `flag_update` gives.
      obtain ⟨T, Y, e, run⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) key value (.atom md) (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) key value (.atom md) (.atom "true") with
        | error e => rw [h] at hupd; simp at hupd
        | ok r =>
          rw [h] at hupd
          simp only [Lynx.Except.ok_bind] at hupd
          split at hupd
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupd
      rcases Nest.flag_update hX ok nr' _ hmd hm upd hkL run with e₀ | ⟨er, extra, mis, f, only, rfl, hres, hx, hmisD, hmk, -⟩
      · cases e₀
      obtain rfl : e = Lynx.Term.list (extra ++ mis.map Nest.bdErr) := by
        rcases hres with ⟨-, e'⟩ | ⟨-, T', Y', e'⟩
        · cases e'
        · simp only [Lynx.Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'; exact e'.2.2
      have bd := Nest.bd_ok hX only dk sk hDs hx hmisD hmk hm
        ["bitstring_no_binary", "binary", "integer", "float", "pid", "port", "reference", "fun", "tuple", "map", "list"]
        (by simp [Nest.domainKinds])
      simp only [Lynx.apply_eq, «map_update_baddomain:ensures/6»]
      simp [run, Erlang.erlang.«element/2», «update_kinds/0»]
      simpa [Lynx.Term.list] using bd
      """

    law map_delete_baddomain(map, key, mode, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(key, {depth, node}) and depth?(depth) and
          mode in [:force, :keep, :reject] and match?({_, _, _}, Descr.map_update(map, key, :delete, mode, true)),
      expects: baddomains?(map, key, elem(Descr.map_update(map, key, :delete, mode, true), 2), update_kinds()),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, and the key `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_delete_baddomain:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_delete_baddomain:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨hmp, hk⟩, -⟩, hmode⟩, hupd⟩ := requires
      have hmp : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hmp
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hmk : (Nest.level node d).K + 23 ≤ δ + 99 := by rw [Nest.level_K] at hm ⊢; omega
      have ef := (Nest.level node (d + 1)).ef
      -- The split of the key.
      have dk := Nest.arrows_static_ok hk
      obtain ⟨rs, neg, ds, rk, ok, nr, na, sk⟩ :=
        Nest.key_split_any dk (fun Y e => by subst e; exact static_union_atoms hk)
          (fun Y e => by subst e; exact static_negation_atoms hk) hmk
      obtain ⟨rs', rfl⟩ := Nest.atoms_of ok.hrs
      obtain ⟨ds', rfl⟩ := Nest.atoms_of fun d md => let ⟨s, _, e⟩ := ok.hds d md; ⟨s, e⟩
      have nr' : ∀ N, neg = .map N → rs' = [] := fun N e => by have := nr N e; cases rs' <;> simp_all
      have hDs : ∀ s ∈ ds', s ∈ Nest.domainKinds := fun s ms => by
        obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
      obtain ⟨md, rfl, hmd⟩ : ∃ md, mode = .atom md ∧ Nest.Mode md := by
        by_cases h : mode = .atom "force"
        · exact ⟨_, h, Or.inl rfl⟩
        by_cases h' : mode = .atom "keep"
        · exact ⟨_, h', Or.inr (Or.inl rfl)⟩
        by_cases h'' : mode = .atom "reject"
        · exact ⟨_, h'', Or.inr (Or.inr rfl)⟩
        simp [Lynx.Term.isMember, h, h', h''] at hmode
      rcases Nest.arrows_static_ok hmp with rfl | ⟨X, rfl, sX⟩
      · rcases hmd with rfl | rfl | rfl <;>
          simp [Elixir.Module.Types.Descr.«map_update/5», Lynx.Term.isMember, Erlang.erlang.«is_boolean/1»,
            Erlang.erlang.«=:=/2», rk, Elixir.Module.Types.Descr.«map_update_unchecked/4»] at hupd
      have hX : Nest.DE (Nest.level node (d + 1)).E (.map X) := Or.inr ⟨X, rfl, sX⟩
      have upd : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) key (.atom "delete") (.atom md) (.atom "true") =
          Elixir.Module.Types.Descr.«map_update_unchecked/4» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (Nest.splitT (rs'.map Lynx.Term.atom) neg (ds'.map Lynx.Term.atom))
            (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom md]) (.atom "true") := by
        unfold Elixir.Module.Types.Descr.«map_update/5»
        rcases hmd with rfl | rfl | rfl <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», rk,
          Elixir.Module.Types.Descr.«none/0»]
      have hkL : ∀ k, k + 6 = δ + 100 → ∀ lines : List Lynx.Term,
          (∀ L ∈ lines, Nest.MLine (Nest.level node (d + 1)).E L ∧ ∃ w, Nest.InMLine (Nest.level node (d + 1)).den L w) →
          ∀ (bd : Bool) a, ∃ (ba : List Lynx.Term) (F : Lynx.Term), Elixir.Module.Types.Descr.«map_update_named_key/5»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (k + 5)) (Lynx.Term.list lines) (.atom a)
            (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom md])
            (boolAtom bd) (.atom "true") = .ok (.tuple #[Lynx.Term.list ba, F]) ∧
            FieldValue (Nest.level node (d + 1)).E F ∧
            ∀ o, Nest.FieldSem (Nest.level node (d + 1)).den F o ↔ ∃ L ∈ lines, Nest.LongM (Nest.level node (d + 1)).den L a o :=
        fun k ek lines hl bd a => Nest.hk_del ef (n := k + 2) (by omega) hmd lines hl bd a
      -- The update succeeds, with the errors `flag_update` gives.
      obtain ⟨T, Y, e, run⟩ : ∃ T Y e, Elixir.Module.Types.Descr.«map_update/5»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) key (.atom "delete") (.atom md) (.atom "true") =
          .ok (.tuple #[T, Y, e]) := by
        cases h : Elixir.Module.Types.Descr.«map_update/5» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) key (.atom "delete") (.atom md) (.atom "true") with
        | error e => rw [h] at hupd; simp at hupd
        | ok r =>
          rw [h] at hupd
          simp only [Lynx.Except.ok_bind] at hupd
          split at hupd
          · rename_i a b c; exact ⟨a, b, c, rfl⟩
          · simp at hupd
      rcases Nest.flag_update hX ok nr' _ hmd hm upd hkL run with e₀ | ⟨er, extra, mis, f, only, rfl, hres, hx, hmisD, hmk, -⟩
      · cases e₀
      obtain rfl : e = Lynx.Term.list (extra ++ mis.map Nest.bdErr) := by
        rcases hres with ⟨-, e'⟩ | ⟨-, T', Y', e'⟩
        · cases e'
        · simp only [Lynx.Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e'; exact e'.2.2
      have bd := Nest.bd_ok hX only dk sk hDs hx hmisD hmk hm
        ["bitstring_no_binary", "binary", "integer", "float", "pid", "port", "reference", "fun", "tuple", "map", "list"]
        (by simp [Nest.domainKinds])
      simp only [Lynx.apply_eq, «map_delete_baddomain:ensures/5»]
      simp [run, Erlang.erlang.«element/2», «update_kinds/0»]
      simpa [Lynx.Term.list] using bd
      """

    law map_put_badmap(map, key, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_atom(key),
      expects:
        (Descr.map_put_key(map, key, value) == :badmap) ==
          not (Descr.subtype?(map, Descr.open_map()) and not Descr.empty?(map)),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on.
      simp only [«map_put_badmap:requires/5», Lynx.Term.true] at requires
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at requires; cases requires
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at requires
      simp only [Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨ht, hel⟩, hd⟩, hi⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      simp only [Erlang.erlang.«+/2_integers», Except.ok.injEq] at hp
      subst hp
      have ht : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      refine ⟨100 + 24 * (d + 1), fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      have dt := Nest.arrows_static_ok ht
      have top : Elixir.Module.Types.Descr.«open_map/0» =
          .ok (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) := rfl
      have sT := Nest.next_sub dt Nest.mapTop_de (m := δ + 100) (by omega)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.bp_false.mpr fun h => by
          have := (Nest.mapTop_den Nest.bitPt).mp (h Nest.bitPt (Nest.denD_term _))
          simp [Nest.bitPt] at this] at sT
        simp only [Lynx.apply_eq, «map_put_badmap:ensures/5»]
        simp [Elixir.Module.Types.Descr.«map_put_key/3», Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      obtain ⟨res, run, ⟨rfl, nonly⟩ | ⟨Y, rfl, only, -⟩⟩ :=
        Nest.put_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) a del sx (m := δ + 100) hm
      · rw [Nest.monly_iff] at nonly
        simp only [Lynx.apply_eq, «map_put_badmap:ensures/5»]
        by_cases h : Nest.SubN node (d + 1) (.map X) (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])])
        · rw [Nest.bp_true.mpr h] at sT
          rw [Nest.bp_true.mpr (Classical.not_not.mp fun h' => nonly ⟨h, h'⟩)] at ne
          simp [run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
        · rw [Nest.bp_false.mpr h] at sT
          simp [run, Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      · obtain ⟨h₁, h₂⟩ := Nest.monly_iff.mp only
        rw [Nest.bp_true.mpr h₁] at sT
        rw [Nest.bp_false.mpr h₂] at ne
        simp only [Lynx.apply_eq, «map_put_badmap:ensures/5»]
        simp [run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
      """

    law tuple_insert_fetch(tuple, index, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and not Descr.empty?(value) and is_map(Descr.tuple_insert_at(tuple, index, value)),
      expects:
        match?({false, _}, Descr.tuple_fetch(Descr.tuple_insert_at(tuple, index, value), index)) and
          Descr.equal?(elem(Descr.tuple_fetch(Descr.tuple_insert_at(tuple, index, value), index), 1), value),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_insert_fetch:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_insert_fetch:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hmap⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.insert_at_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      by_cases neg : z < 0
      · rw [Nest.insert_at_neg _ _ _ neg] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rw [Nest.insert_at_static _ _ _ sx] at hmap
      obtain ⟨Y, run⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
          (.integer i) value = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨onlyX, longX, dY, onlyY, ttY⟩ := Nest.insert_tuple (Or.inr ⟨X, rfl, sX⟩) del i hm run
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The inserted type holds a tuple.
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have lw := longX w₀ hw₀
      have hY : Nest.TT node (d + 1) Y (w₀.take i ++ y₀ :: w₀.drop i) :=
        (ttY _).mpr ⟨w₀.take i, y₀, w₀.drop i, rfl, by simp; omega, hy₀, by simpa using hw₀⟩
      obtain ⟨res, fetch, ⟨rfl, nonly⟩ | ⟨rfl, -, w, hw, len⟩ | ⟨e, rfl, he, -, -, s₁, s₂⟩⟩ :=
        Nest.fetch_tuple (t := node) (n := d + 1) dY i hm
      · exact absurd ⟨onlyY, _, hY⟩ nonly
      · obtain ⟨w₁, y, w₂, rfl, l₁, -, -⟩ := (ttY w).mp hw
        simp at len; omega
      have sem : ∀ y, (Nest.level node (d + 1)).den e y ↔ (Nest.level node (d + 1)).den value y := by
        intro y
        constructor
        · intro hy
          obtain ⟨v₁, v₂, len, h⟩ := s₂ y hy
          obtain ⟨w₁, y', w₂, ew, l₁, hy', -⟩ := (ttY _).mp h
          obtain ⟨-, e₂⟩ := List.append_inj ew (by omega)
          simp only [List.cons.injEq] at e₂
          rw [e₂.1]; exact hy'
        · intro hy
          exact s₁ (w₀.take i) y (w₀.drop i) (by simp; omega)
            ((ttY _).mpr ⟨w₀.take i, y, w₀.drop i, rfl, by simp; omega, hy, by simpa using hw₀⟩)
      simp only [Lynx.apply_eq, «tuple_insert_fetch:ensures/5», Nest.insert_at_static _ _ _ sx, run, Lynx.Except.ok_bind,
        fetch]
      simp [Erlang.erlang.«element/2», Nest.elem_equal (Nest.level node (d + 1)).ef he del sem (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega), Lynx.Term.true]
      """

    law tuple_insert_subtype(left, right, index, small, large, depth, node),
      requires:
        arrows_static?(left, {depth + 1, node}) and arrows_static?(right, {depth + 1, node}) and
          arrows_static?(small, {depth, node}) and arrows_static?(large, {depth, node}) and depth?(depth) and
          is_integer(index) and Descr.subtype?(left, right) and Descr.subtype?(small, large) and
          is_map(Descr.tuple_insert_at(left, index, small)) and is_map(Descr.tuple_insert_at(right, index, large)),
      expects:
        Descr.subtype?(Descr.tuple_insert_at(left, index, small), Descr.tuple_insert_at(right, index, large)),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels and the values `d`, so the proofs run from the bound of level `d + 1` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_insert_subtype:requires/7», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_insert_subtype:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hr⟩, hs⟩, hg⟩, -⟩, hi⟩, hsub⟩, hsubv⟩, hmapL⟩, hmapR⟩ := requires
      have hl : «arrows_static?/2» left (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hl
      have hr : «arrows_static?/2» right (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hr
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have ds := Nest.arrows_static_ok hs
      have dg := Nest.arrows_static_ok hg
      have es : (Nest.level node (d + 1)).E small := Or.inl ds
      have eg : (Nest.level node (d + 1)).E large := Or.inl dg
      have static : ∀ {x : Lynx.Term}, Nest.DE (Nest.level node d).E x →
          x = .atom "term" ∨ ∃ Z, x = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := fun h => by
        rcases h with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      -- Values of the small type are values of the large one.
      have subV := Nest.next_sub ds dg (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [subV, Except.ok.injEq] at hsubv
      have subV := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsubv)
      have vals : ∀ y, (Nest.level node (d + 1)).den small y → (Nest.level node (d + 1)).den large y := fun y hy =>
        (Nest.denN_of dg.notT).mpr (subV y ((Nest.denN_of ds.notT).mp hy))
      have dl := Nest.arrows_static_ok hl
      have dr := Nest.arrows_static_ok hr
      -- Tuples of the left type are tuples of the right one.
      have subT := Nest.next_sub dl dr (m := δ + 100) (by omega)
      rw [subT, Except.ok.injEq] at hsub
      have subT := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      rcases dl with rfl | ⟨XL, rfl, sXL⟩
      · rw [Nest.insert_at_term] at hmapL; simp [Erlang.erlang.«is_map/1»] at hmapL
      rcases dr with rfl | ⟨XR, rfl, sXR⟩
      · rw [Nest.insert_at_term] at hmapR; simp [Erlang.erlang.«is_map/1»] at hmapR
      by_cases neg : z < 0
      · rw [Nest.insert_at_neg _ _ _ neg] at hmapL; simp [Erlang.erlang.«is_map/1»] at hmapL
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      have tuples : ∀ w, Nest.TT node (d + 1) XL w → Nest.TT node (d + 1) XR w := fun w hw =>
        (Nest.denD_tpt w).mp (subT _ ((Nest.denD_tpt w).mpr hw))
      rw [Nest.insert_at_static _ _ _ (static ds)] at hmapL
      rw [Nest.insert_at_static _ _ _ (static dg)] at hmapR
      obtain ⟨YL, runL⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XL) (.integer i) small = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XL) (.integer i) small with
        | error _ => rw [h] at hmapL; cases hmapL
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapL
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapL
          exact ⟨_, rfl⟩
      obtain ⟨YR, runR⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XR) (.integer i) large = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XR) (.integer i) large with
        | error _ => rw [h] at hmapR; cases hmapR
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapR
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapR
          exact ⟨_, rfl⟩
      obtain ⟨-, -, dYL, onlyL, ttL⟩ := Nest.insert_tuple (Or.inr ⟨XL, rfl, sXL⟩) es i hm runL
      obtain ⟨-, -, dYR, -, ttR⟩ := Nest.insert_tuple (Or.inr ⟨XR, rfl, sXR⟩) eg i hm runR
      have sub := Nest.next_sub dYL dYR (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node (d + 1) (.map YL) (.map YR) from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_tuple v (onlyL v hv)
        rw [hw] at hv ⊢
        obtain ⟨w₁, y, w₂, e, len, hy, hw'⟩ := (ttL w).mp hv
        exact (ttR w).mpr ⟨w₁, y, w₂, e, len, vals y hy, tuples _ hw'⟩)] at sub
      simp only [Lynx.apply_eq, «tuple_insert_subtype:ensures/7»]
      simp [Nest.insert_at_static _ _ _ (static ds), Nest.insert_at_static _ _ _ (static dg), runL, runR, sub,
        Lynx.Term.true]
      """

    law tuple_insert_delete(tuple, index, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and not Descr.empty?(value) and is_map(Descr.tuple_insert_at(tuple, index, value)),
      expects: Descr.equal?(Descr.tuple_delete_at(Descr.tuple_insert_at(tuple, index, value), index), tuple),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_insert_delete:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_insert_delete:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hmap⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.insert_at_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      by_cases neg : z < 0
      · rw [Nest.insert_at_neg _ _ _ neg] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rw [Nest.insert_at_static _ _ _ sx] at hmap
      obtain ⟨Y, run⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
          (.integer i) value = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨onlyX, longX, dY, onlyY, ttY⟩ := Nest.insert_tuple (Or.inr ⟨X, rfl, sX⟩) del i hm run
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      -- The inserted type holds only tuples, longer than the index.
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have lw := longX w₀ hw₀
      have hY : Nest.TT node (d + 1) Y (w₀.take i ++ y₀ :: w₀.drop i) :=
        (ttY _).mpr ⟨w₀.take i, y₀, w₀.drop i, rfl, by simp; omega, hy₀, by simpa using hw₀⟩
      have longY : ∀ w, Nest.TT node (d + 1) Y w → i < w.length := fun w hw => by
        obtain ⟨w₁, y, w₂, rfl, l₁, -, -⟩ := (ttY w).mp hw
        simp; omega
      obtain ⟨r, del, tr, sr⟩ := Nest.delete_tuple dY ⟨onlyY, _, hY⟩ i longY hm
      have dZ : Nest.DE (Nest.level node (d + 1)).E (.map [(.atom "tuple", r)]) :=
        Or.inr ⟨_, rfl, Nest.descrC_put Nest.descrC_nil tr⟩
      have same : ∀ v : Nest.PN node (d + 1), Nest.denD (.map [(.atom "tuple", r)]) v ↔ Nest.denD (.map X) v := by
        intro v
        by_cases h : v.1.1 = "tuple"
        · obtain ⟨w, hw⟩ := Nest.pt_tuple v h
          rw [hw, hw]
          have ttZ : Nest.TT node (d + 1) [(.atom "tuple", r)] w ↔
              Nest.denTF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den r w = Bool.true := by
            simp [Nest.TT, Lynx.Term.mapLookup]
          rw [ttZ, sr]
          constructor
          · rintro ⟨v₁, y, v₂, rfl, l₁, h⟩
            obtain ⟨w₁, y', w₂, e, l₁', -, hx⟩ := (ttY _).mp h
            obtain ⟨e₁, e₂⟩ := List.append_inj e (by omega)
            simp only [List.cons.injEq] at e₂
            rw [e₁, e₂.2]; exact hx
          · intro h
            have lw := longX w h
            refine ⟨w.take i, y₀, w.drop i, by simp, by simp; omega, (ttY _).mpr ⟨w.take i, y₀, w.drop i, rfl, by simp; omega,
              hy₀, by simpa using h⟩⟩
        · constructor
          · intro hv
            rw [Nest.denD_map] at hv
            simp [Lynx.Term.mapLookup, h, Elixir.STTDescrProofsTest.dn_none] at hv
          · intro hv
            exact absurd (onlyX.1 v hv) h
      simp only [Lynx.apply_eq, «tuple_insert_delete:ensures/5», Nest.insert_at_static _ _ _ sx, run, Lynx.Except.ok_bind, del]
      rw [Nest.next_eq_true dZ (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega) same]
      rfl
      """
    law tuple_insert_other(tuple, index, other, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and is_integer(other) and other != index and not Descr.empty?(value) and
          is_map(Descr.tuple_insert_at(tuple, index, value)),
      expects:
        same_fetch?(
          Descr.tuple_fetch(Descr.tuple_insert_at(tuple, index, value), other),
          Descr.tuple_fetch(tuple, if(other < index, do: other, else: other - 1))
        ),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_insert_other:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_insert_other:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, ho⟩, hoi⟩, hne⟩, hmap⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨q, rfl⟩ : ∃ q : Int, other = .integer q := by
        cases other <;> simp [Erlang.erlang.«is_integer/1»] at ho
        exact ⟨_, rfl⟩
      have qz : q ≠ z := by
        intro e; subst e; simp [Erlang.erlang.«/=/2»] at hoi
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.insert_at_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      by_cases neg : z < 0
      · rw [Nest.insert_at_neg _ _ _ neg] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      rw [Nest.insert_at_static _ _ _ sx] at hmap
      obtain ⟨Y, run⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X)
          (.integer i) value = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨onlyX, longX, dY, onlyY, ttY⟩ := Nest.insert_tuple (Or.inr ⟨X, rfl, sX⟩) del i hm run
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      simp only [Lynx.apply_eq, «tuple_insert_other:ensures/6», Nest.insert_at_static _ _ _ sx, run, Lynx.Except.ok_bind]
      by_cases qneg : q < 0
      · have lt : q < (i : Int) := by omega
        simp [Nest.fetch_neg _ _ qneg, Erlang.erlang.«</2», Int.compare_eq_lt, lt, pure, Except.pure,
          «same_fetch?/2», Erlang.erlang.«==/2», Lynx.Term.true]
      obtain ⟨o, rfl⟩ : ∃ o : Nat, q = o := ⟨q.toNat, by omega⟩
      obtain ⟨a, b, ra, rb, same⟩ := Nest.insert_same_fetch (Or.inr ⟨X, rfl, sX⟩) dY onlyX longX onlyY ttY hy₀ o
        (by omega) hm
      by_cases hlt : o < i
      · have lt : (o : Int) < (i : Int) := by omega
        simp only [hlt, ite_true] at rb
        simp [ra, rb, Erlang.erlang.«</2», Int.compare_eq_lt, lt, pure, Except.pure, same, Lynx.Term.true]
      · have nlt : ¬(o : Int) < (i : Int) := by omega
        simp only [hlt, ite_false] at rb
        have rb' : Elixir.Module.Types.Descr.«tuple_fetch/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (.integer ((o : Int) - 1)) = .ok b := by
          have : ((o - 1 : Nat) : Int) = (o : Int) - 1 := by omega
          rw [← this]; exact rb
        simp [ra, rb', Erlang.erlang.«</2», Int.compare_eq_lt, nlt, Erlang.erlang.«-/2_integers», same, Lynx.Term.true]
      """

    law tuple_replace_fetch(tuple, index, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and not Descr.empty?(value) and is_map(Descr.tuple_replace_at(tuple, index, value)),
      expects:
        match?({false, _}, Descr.tuple_fetch(Descr.tuple_replace_at(tuple, index, value), index)) and
          Descr.equal?(elem(Descr.tuple_fetch(Descr.tuple_replace_at(tuple, index, value), index), 1), value),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_replace_fetch:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_replace_fetch:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hmap⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      by_cases neg : z < 0
      · rw [Nest.replace_neg _ _ _ neg] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.replace_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      obtain ⟨Y, run⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_replace_at/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) (.integer i) value = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨onlyX, shortX, dY, onlyY, ttY⟩ := Nest.replace_tuple (Or.inr ⟨X, rfl, sX⟩) i del sx hm run
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      have long : ∀ x, Nest.TT node (d + 1) X x → i < x.length := fun x hx =>
        Classical.byContradiction fun h => shortX ⟨x, hx, by omega⟩
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have hY : Nest.TT node (d + 1) Y (w₀.set i y₀) := (ttY _).mpr ⟨w₀, y₀, hw₀, long w₀ hw₀, hy₀, rfl⟩
      obtain ⟨res, fetch, ⟨rfl, nonly⟩ | ⟨rfl, -, w, hw, len⟩ | ⟨e, rfl, he, -, -, s₁, s₂⟩⟩ :=
        Nest.fetch_tuple (t := node) (n := d + 1) dY i hm
      · exact absurd ⟨onlyY, _, hY⟩ nonly
      · obtain ⟨x', y, hx', lx', -, rfl⟩ := (ttY w).mp hw
        simp at len; omega
      have sem : ∀ y, (Nest.level node (d + 1)).den e y ↔ (Nest.level node (d + 1)).den value y := by
        intro y
        constructor
        · intro hy
          obtain ⟨w, hw, hwy⟩ := Nest.split_getElem.mp (s₂ y hy)
          obtain ⟨x', y', -, lx', hy', rfl⟩ := (ttY w).mp hw
          rw [List.getElem?_set_self lx'] at hwy
          cases hwy; exact hy'
        · intro hy
          obtain ⟨v₁, v₂, len, h⟩ := Nest.split_getElem.mpr
            ⟨_, (ttY _).mpr ⟨w₀, y, hw₀, long w₀ hw₀, hy, rfl⟩, List.getElem?_set_self (long w₀ hw₀)⟩
          exact s₁ v₁ y v₂ len h
      simp only [Lynx.apply_eq, «tuple_replace_fetch:ensures/5», run, Lynx.Except.ok_bind, fetch]
      simp [Erlang.erlang.«element/2», Nest.elem_equal (Nest.level node (d + 1)).ef he del sem (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega), Lynx.Term.true]
      """

    law tuple_replace_other(tuple, index, other, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and is_integer(other) and other != index and not Descr.empty?(value) and
          is_map(Descr.tuple_replace_at(tuple, index, value)),
      expects: same_fetch?(Descr.tuple_fetch(Descr.tuple_replace_at(tuple, index, value), other), Descr.tuple_fetch(tuple, other)),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_replace_other:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_replace_other:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, ho⟩, hoi⟩, hne⟩, hmap⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨q, rfl⟩ : ∃ q : Int, other = .integer q := by
        cases other <;> simp [Erlang.erlang.«is_integer/1»] at ho
        exact ⟨_, rfl⟩
      have qz : q ≠ z := by
        intro e; subst e; simp [Erlang.erlang.«/=/2»] at hoi
      by_cases neg : z < 0
      · rw [Nest.replace_neg _ _ _ neg] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.replace_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      obtain ⟨Y, run⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_replace_at/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) (.integer i) value = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨onlyX, shortX, dY, onlyY, ttY⟩ := Nest.replace_tuple (Or.inr ⟨X, rfl, sX⟩) i del sx hm run
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      have long : ∀ x, Nest.TT node (d + 1) X x → i < x.length := fun x hx =>
        Classical.byContradiction fun h => shortX ⟨x, hx, by omega⟩
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have tY : ∀ w, Nest.TT node (d + 1) Y w ↔ ∃ x' y, Nest.TT node (d + 1) X x' ∧ i < x'.length ∧
          (Nest.level node (d + 1)).den value y ∧ w = x'.set i y := ttY
      simp only [Lynx.apply_eq, «tuple_replace_other:ensures/6», run, Lynx.Except.ok_bind]
      by_cases qneg : q < 0
      · simp [Nest.fetch_neg _ _ qneg, «same_fetch?/2», Erlang.erlang.«==/2», Lynx.Term.true]
      obtain ⟨o, rfl⟩ : ∃ o : Nat, q = o := ⟨q.toNat, by omega⟩
      have ne : o ≠ i := by omega
      obtain ⟨a, b, ra, rb, same⟩ := Nest.same_fetch (t := node) (n := d + 1) dY (Or.inr ⟨X, rfl, sX⟩) o o hm
        ⟨fun _ => onlyX, fun _ => ⟨onlyY, _, (tY _).mpr ⟨w₀, y₀, hw₀, long w₀ hw₀, hy₀, rfl⟩⟩⟩
        (fun _ => ⟨fun ⟨w, hw, lw⟩ => by
            obtain ⟨x', y, hx', -, -, rfl⟩ := (tY w).mp hw
            exact ⟨x', hx', by simpa using lw⟩,
          fun ⟨x', hx', lx'⟩ => ⟨_, (tY _).mpr ⟨x', y₀, hx', long x' hx', hy₀, rfl⟩, by simpa using lx'⟩⟩)
        (fun _ _ y => by
          simp only [Nest.El, Nest.split_getElem]
          constructor
          · rintro ⟨w, hw, hy⟩
            obtain ⟨x', y', hx', -, -, rfl⟩ := (tY w).mp hw
            exact ⟨x', hx', by rwa [List.getElem?_set_ne (Ne.symm ne)] at hy⟩
          · rintro ⟨x', hx', hy⟩
            exact ⟨_, (tY _).mpr ⟨x', y₀, hx', long x' hx', hy₀, rfl⟩, by rwa [List.getElem?_set_ne (Ne.symm ne)]⟩)
      simp [ra, rb, same, Lynx.Term.true]
      """

    law tuple_replace_subtype(left, right, index, small, large, depth, node),
      requires:
        arrows_static?(left, {depth + 1, node}) and arrows_static?(right, {depth + 1, node}) and
          arrows_static?(small, {depth, node}) and arrows_static?(large, {depth, node}) and depth?(depth) and
          is_integer(index) and Descr.subtype?(left, right) and Descr.subtype?(small, large) and
          is_map(Descr.tuple_replace_at(left, index, small)) and is_map(Descr.tuple_replace_at(right, index, large)),
      expects:
        Descr.subtype?(Descr.tuple_replace_at(left, index, small), Descr.tuple_replace_at(right, index, large)),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels and the values `d`, so the proofs run from the bound of level `d + 1` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_replace_subtype:requires/7», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_replace_subtype:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hr⟩, hs⟩, hg⟩, -⟩, hi⟩, hsub⟩, hsubv⟩, hmapL⟩, hmapR⟩ := requires
      have hl : «arrows_static?/2» left (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hl
      have hr : «arrows_static?/2» right (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hr
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have ds := Nest.arrows_static_ok hs
      have dg := Nest.arrows_static_ok hg
      have es : (Nest.level node (d + 1)).E small := Or.inl ds
      have eg : (Nest.level node (d + 1)).E large := Or.inl dg
      have static : ∀ {x : Lynx.Term}, Nest.DE (Nest.level node d).E x →
          x = .atom "term" ∨ ∃ Z, x = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := fun h => by
        rcases h with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      -- Values of the small type are values of the large one.
      have subV := Nest.next_sub ds dg (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
      rw [subV, Except.ok.injEq] at hsubv
      have subV := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsubv)
      have vals : ∀ y, (Nest.level node (d + 1)).den small y → (Nest.level node (d + 1)).den large y := fun y hy =>
        (Nest.denN_of dg.notT).mpr (subV y ((Nest.denN_of ds.notT).mp hy))
      have dl := Nest.arrows_static_ok hl
      have dr := Nest.arrows_static_ok hr
      -- Tuples of the left type are tuples of the right one.
      have subT := Nest.next_sub dl dr (m := δ + 100) (by omega)
      rw [subT, Except.ok.injEq] at hsub
      have subT := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      by_cases neg : z < 0
      · rw [Nest.replace_neg _ _ _ neg] at hmapL; simp [Erlang.erlang.«is_map/1»] at hmapL
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      rcases dl with rfl | ⟨XL, rfl, sXL⟩
      · rw [Nest.replace_term] at hmapL; simp [Erlang.erlang.«is_map/1»] at hmapL
      rcases dr with rfl | ⟨XR, rfl, sXR⟩
      · rw [Nest.replace_term] at hmapR; simp [Erlang.erlang.«is_map/1»] at hmapR
      have tuples : ∀ w, Nest.TT node (d + 1) XL w → Nest.TT node (d + 1) XR w := fun w hw =>
        (Nest.denD_tpt w).mp (subT _ ((Nest.denD_tpt w).mpr hw))
      obtain ⟨YL, runL⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_replace_at/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XL) (.integer i) small = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XL) (.integer i) small with
        | error _ => rw [h] at hmapL; cases hmapL
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapL
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapL
          exact ⟨_, rfl⟩
      obtain ⟨YR, runR⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_replace_at/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XR) (.integer i) large = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map XR) (.integer i) large with
        | error _ => rw [h] at hmapR; cases hmapR
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapR
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapR
          exact ⟨_, rfl⟩
      obtain ⟨-, -, dYL, onlyL, ttL⟩ := Nest.replace_tuple (Or.inr ⟨XL, rfl, sXL⟩) i es (static ds) hm runL
      obtain ⟨-, -, dYR, -, ttR⟩ := Nest.replace_tuple (Or.inr ⟨XR, rfl, sXR⟩) i eg (static dg) hm runR
      have sub := Nest.next_sub dYL dYR (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node (d + 1) (.map YL) (.map YR) from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_tuple v (onlyL v hv)
        rw [hw] at hv ⊢
        obtain ⟨x', y, hx', lx', hy, e⟩ := (ttL w).mp hv
        exact (ttR w).mpr ⟨x', y, tuples _ hx', lx', vals y hy, e⟩)] at sub
      simp only [Lynx.apply_eq, «tuple_replace_subtype:ensures/7»]
      simp [runL, runR, sub, Lynx.Term.true]
      """

    law tuple_replace_badindex(tuple, index, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and index >= 0 and Descr.subtype?(tuple, Descr.tuple()) and not Descr.empty?(tuple),
      expects:
        (case Descr.tuple_replace_at(tuple, index, value) do
          :badindex -> not Descr.subtype?(tuple, Descr.open_tuple(:lists.duplicate(index + 1, Descr.term())))
          result when is_map(result) -> Descr.subtype?(tuple, Descr.open_tuple(:lists.duplicate(index + 1, Descr.term())))
          _ -> false
        end),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_replace_badindex:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_replace_badindex:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨hs, hel⟩, -⟩, hi⟩, hnn⟩, htup⟩, hne⟩ := requires
      have hs : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := by
        refine ⟨z.toNat, ?_⟩
        by_cases neg : z < 0
        · simp [Erlang.erlang.«>=/2», Int.isGE_compare, neg] at hnn
        · omega
      have dt := Nest.arrows_static_ok hs
      have sT := Nest.next_sub dt Nest.tupleTop_de (m := δ + 100) (by omega)
      rw [show Elixir.Module.Types.Descr.«tuple/0» =
        .ok (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) from rfl, Lynx.Except.ok_bind, sT] at htup
      rw [Except.ok.injEq] at htup
      have onlyT := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) htup)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · have := (Nest.tupleTop_den Nest.bitPt).mp (onlyT Nest.bitPt (Nest.denD_term _))
        simp [Nest.bitPt] at this
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      rw [ne] at hne
      have ex : ∃ v : Nest.PN node (d + 1), Nest.denD (.map X) v := by
        cases h : Nest.bp (∀ v : Nest.PN node (d + 1), ¬Nest.denD (.map X) v)
        · exact Classical.byContradiction fun none => by
            have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
            rw [h] at this; cases this
        · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
      have only : Nest.TOnly node (d + 1) X := by
        refine ⟨fun v hv => (Nest.tupleTop_den v).mp (onlyT v hv), ?_⟩
        obtain ⟨v, hv⟩ := ex
        obtain ⟨w, hw⟩ := Nest.pt_tuple v ((Nest.tupleTop_den v).mp (onlyT v hv))
        exact ⟨w, (hw X).mp hv⟩
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate (i + 1) (.atom "term"))
        fun x mx => by rw [List.eq_of_mem_replicate mx]; exact Or.inl rfl
      have hl : ∀ x ∈ List.replicate (i + 1) (.atom "term"), (Nest.level node (d + 1)).E x := by
        intro x mx; rw [List.eq_of_mem_replicate mx]; exact (Nest.level node (d + 1)).ef.term
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.fused_de (Or.inl rfl) hl key) (m := δ + 100) (by omega)
      have subIff : Nest.SubN node (d + 1) (.map X)
          (.map [(.atom "tuple", .tuple #[.integer k, .atom "open", Lynx.Term.list (List.replicate (i + 1) (.atom "term"))])]) ↔ ∀ w, Nest.TT node (d + 1) X w → i + 1 ≤ w.length := by
        constructor
        · intro h w hw
          have := h _ ((Nest.denD_tpt w).mpr hw)
          rwa [Nest.denD_tpt, Nest.tt_open] at this
        · intro h v hv
          obtain ⟨w, hw⟩ := Nest.pt_tuple v (only.1 v hv)
          rw [hw X] at hv
          rw [hw, Nest.tt_open]
          exact h w hv
      have dup' : Erlang.lists.«duplicate/2» (.integer ((i : Int) + 1)) (.atom "term") =
          .ok (Lynx.Term.list (List.replicate (i + 1) (.atom "term"))) := by simpa using dup_nat (.atom "term") (i + 1)
      rcases Nest.replace_cases (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) i sx (m := δ + 100) hm with
        ⟨-, nonly⟩ | ⟨run, -, w, hw, len⟩ | ⟨-, short, -⟩
      · exact absurd only nonly
      · rw [Nest.bp_false.mpr fun h => by have := (subIff.mp h) w hw; omega] at sub
        simp only [Lynx.apply_eq, «tuple_replace_badindex:ensures/5»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», dup', rot, sub,
          Erlang.erlang.«not/1», Lynx.Term.true]
      · obtain ⟨Y, run⟩ := Nest.replace_ok (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) i del sx hm only short
        rw [Nest.bp_true.mpr (subIff.mpr fun w hw => Classical.byContradiction fun h => short ⟨w, hw, by omega⟩)] at sub
        simp only [Lynx.apply_eq, «tuple_replace_badindex:ensures/5»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», dup', rot, sub,
          Erlang.erlang.«not/1», Lynx.Term.true]
      """

    law tuple_replace_idempotent(tuple, index, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and not Descr.empty?(value) and is_map(Descr.tuple_replace_at(tuple, index, value)),
      expects:
        Descr.equal?(
          Descr.tuple_replace_at(Descr.tuple_replace_at(tuple, index, value), index, value),
          Descr.tuple_replace_at(tuple, index, value)
        ),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_replace_idempotent:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_replace_idempotent:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hne⟩, hmap⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      by_cases neg : z < 0
      · rw [Nest.replace_neg _ _ _ neg] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.replace_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      obtain ⟨Y, run⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_replace_at/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) (.integer i) value = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨onlyX, shortX, dY, onlyY, ttY⟩ := Nest.replace_tuple (Or.inr ⟨X, rfl, sX⟩) i del sx hm run
      -- The value has values.
      obtain ⟨y₀, hy₀⟩ : ∃ y, (Nest.level node (d + 1)).den value y := by
        have ne := Nest.next_empty dv (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        rw [ne] at hne
        obtain ⟨y, hy⟩ : ∃ v : Nest.PN node d, Nest.denD value v := by
          cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD value v)
          · exact Classical.byContradiction fun none => by
              have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
              rw [h] at this; cases this
          · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
        exact ⟨y, (Nest.denN_of dv.notT).mpr hy⟩
      have long : ∀ x, Nest.TT node (d + 1) X x → i < x.length := fun x hx =>
        Classical.byContradiction fun h => shortX ⟨x, hx, by omega⟩
      obtain ⟨w₀, hw₀⟩ := onlyX.2
      have tY : ∀ w, Nest.TT node (d + 1) Y w ↔ ∃ x' y, Nest.TT node (d + 1) X x' ∧ i < x'.length ∧
          (Nest.level node (d + 1)).den value y ∧ w = x'.set i y := ttY
      have onlyY' : Nest.TOnly node (d + 1) Y := ⟨onlyY, _, (tY _).mpr ⟨w₀, y₀, hw₀, long w₀ hw₀, hy₀, rfl⟩⟩
      have shortY : ¬Nest.Short node (d + 1) Y i := fun ⟨w, hw, lw⟩ => by
        obtain ⟨x', y, hx', lx', -, rfl⟩ := (tY w).mp hw
        simp at lw; omega
      obtain ⟨Y₂, run₂⟩ := Nest.replace_ok (t := node) (n := d + 1) dY i del sx hm onlyY' shortY
      obtain ⟨-, -, dY₂, onlyY₂, ttY₂⟩ := Nest.replace_tuple dY i del sx hm run₂
      have same : ∀ v : Nest.PN node (d + 1), Nest.denD (.map Y₂) v ↔ Nest.denD (.map Y) v := by
        intro v
        by_cases h : v.1.1 = "tuple"
        · obtain ⟨w, hw⟩ := Nest.pt_tuple v h
          rw [hw, hw, ttY₂, tY]
          constructor
          · rintro ⟨x'', y, hx'', lx'', hy, rfl⟩
            obtain ⟨x', y', hx', lx', -, rfl⟩ := (tY _).mp hx''
            exact ⟨x', y, hx', lx', hy, by simp⟩
          · rintro ⟨x', y, hx', lx', hy, rfl⟩
            exact ⟨x'.set i y, y, (tY _).mpr ⟨x', y, hx', lx', hy, rfl⟩, by simpa using lx', hy, by simp⟩
        · exact ⟨fun hv => absurd (onlyY₂ v hv) h, fun hv => absurd (onlyY v hv) h⟩
      simp only [Lynx.apply_eq, «tuple_replace_idempotent:ensures/5», run, run₂, Lynx.Except.ok_bind]
      rw [Nest.next_eq_true dY₂ dY (m := δ + 100) (by omega) same]
      rfl
      """

    law tuple_replace_hold(tuple, index, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          is_integer(index) and is_map(Descr.tuple_replace_at(tuple, index, value)),
      expects:
        Descr.subtype?(
          Descr.opt_intersection(tuple, Descr.open_tuple(:lists.duplicate(index, Descr.term()) ++ [value])),
          Descr.tuple_replace_at(tuple, index, value)
        ),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_replace_hold:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_replace_hold:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨ht, hel⟩, -⟩, hi⟩, hmap⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      by_cases neg : z < 0
      · rw [Nest.replace_neg _ _ _ neg] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.replace_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      have sx : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with rfl | ⟨Z, rfl, sZ⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Z, rfl, sZ.static⟩
      obtain ⟨Y, run⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_replace_at/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
          (.map X) (.integer i) value = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨onlyX, shortX, dY, onlyY, ttY⟩ := Nest.replace_tuple (Or.inr ⟨X, rfl, sX⟩) i del sx hm run
      -- The tuples of the type holding a value of the type at the index are tuples of the replacement.
      have hl : ∀ x ∈ List.replicate i (.atom "term") ++ [value], (Nest.level node (d + 1)).E x := by
        intro x mx
        rcases List.mem_append.mp mx with mx | mx
        · rw [List.eq_of_mem_replicate mx]; exact (Nest.level node (d + 1)).ef.term
        · simp at mx; subst mx; exact del
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate i (.atom "term") ++ [value])
        fun x mx => (Nest.level node (d + 1)).ef.static (hl x mx)
      have dO := Nest.fused_de (Or.inl rfl) hl key
      obtain ⟨c, gc, rc, sc⟩ := Nest.gc_opt_inter2 (Nest.GC.tc (Or.inr ⟨X, rfl, sX⟩)) (Nest.GC.tc dO) (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      have incl : ∀ v : Nest.PN node (d + 1), Nest.denD (.map X) v →
          Nest.denD (.map [(.atom "tuple", .tuple #[.integer k, .atom "open",
            Lynx.Term.list (List.replicate i (.atom "term") ++ [value])])]) v → Nest.denD (.map Y) v := by
        intro v hX hO
        obtain ⟨w, hw⟩ := Nest.pt_tuple v (onlyX.1 v hX)
        rw [hw] at hX hO ⊢
        obtain ⟨v₁, y, v₂, rfl, len, hy⟩ := (Nest.tt_open_at del i k _).mp hO
        refine (ttY _).mpr ⟨_, y, hX, by simp; omega, hy, ?_⟩
        subst len
        simp
      have sub := Nest.gc_sub gc (Nest.GC.tc dY) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        (fun v h => incl v ((sc.1 v).mp h).1 ((sc.1 v).mp h).2) (fun v h => by
          rw [Nest.upper_tc dY]
          have := (sc.2 v).mp h
          rw [Nest.upper_tc (Or.inr ⟨X, rfl, sX⟩), Nest.upper_tc dO] at this
          exact incl v this.1 this.2)
      simp only [Lynx.apply_eq, «tuple_replace_hold:ensures/5»]
      simp only [Elixir.Module.Types.Descr.«term/0», pure, Except.pure, Lynx.Except.ok_bind, dup_nat]
      rw [append_list, Lynx.Except.ok_bind, rot, Lynx.Except.ok_bind]
      simp [rc, run, sub, Lynx.Term.true]
      """

    law tuple_delete_subtype(left, right, index, depth, node),
      requires:
        arrows_static?(left, {depth, node}) and arrows_static?(right, {depth, node}) and depth?(depth) and
          is_integer(index) and Descr.subtype?(left, right) and is_map(Descr.tuple_delete_at(left, index)) and
          is_map(Descr.tuple_delete_at(right, index)),
      expects: Descr.subtype?(Descr.tuple_delete_at(left, index), Descr.tuple_delete_at(right, index)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the precondition from its
      -- own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_delete_subtype:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_delete_subtype:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨⟨⟨hl, hr⟩, -⟩, hi⟩, hsub⟩, hmapL⟩, hmapR⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      have dl := Nest.arrows_static_ok hl
      have dr := Nest.arrows_static_ok hr
      -- Tuples of the left type are tuples of the right one.
      have subT := Nest.next_sub dl dr (m := δ + 100) (by omega)
      rw [subT, Except.ok.injEq] at hsub
      have subT := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      rcases dl with rfl | ⟨XL, rfl, sXL⟩
      · rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmapL
        simp [Erlang.erlang.«is_map/1»] at hmapL
      rcases dr with rfl | ⟨XR, rfl, sXR⟩
      · rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmapR
        simp [Erlang.erlang.«is_map/1»] at hmapR
      by_cases neg : z < 0
      · have : ¬0 ≤ z := by omega
        rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmapL
        simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare, this,
          Erlang.erlang.«is_map/1»] at hmapL
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      have tuples : ∀ w, Nest.TT node d XL w → Nest.TT node d XR w := fun w hw =>
        (Nest.denD_tpt w).mp (subT _ ((Nest.denD_tpt w).mpr hw))
      obtain ⟨resL, runL, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, rL, rfl, tL, sL⟩⟩ :=
        Nest.delete_cases (t := node) (n := d) (Or.inr ⟨XL, rfl, sXL⟩) i (m := δ + 100) hm
      · simp [runL, Erlang.erlang.«is_map/1»] at hmapL
      · simp [runL, Erlang.erlang.«is_map/1»] at hmapL
      obtain ⟨resR, runR, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, rR, rfl, tR, sR⟩⟩ :=
        Nest.delete_cases (t := node) (n := d) (Or.inr ⟨XR, rfl, sXR⟩) i (m := δ + 100) hm
      · simp [runR, Erlang.erlang.«is_map/1»] at hmapR
      · simp [runR, Erlang.erlang.«is_map/1»] at hmapR
      have dZL : Nest.DE (Nest.level node d).E (.map [(.atom "tuple", rL)]) := Or.inr ⟨_, rfl, Nest.descrC_put Nest.descrC_nil tL⟩
      have dZR : Nest.DE (Nest.level node d).E (.map [(.atom "tuple", rR)]) := Or.inr ⟨_, rfl, Nest.descrC_put Nest.descrC_nil tR⟩
      have sub := Nest.next_sub dZL dZR (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node d (.map [(.atom "tuple", rL)]) (.map [(.atom "tuple", rR)]) from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_tuple v (Nest.single_tuples rL v hv)
        rw [hw] at hv ⊢
        rw [Nest.tt_single, sL] at hv
        rw [Nest.tt_single, sR]
        obtain ⟨v₁, y, v₂, e, len, h⟩ := hv
        exact ⟨v₁, y, v₂, e, len, tuples _ h⟩)] at sub
      simp only [Lynx.apply_eq, «tuple_delete_subtype:ensures/5»]
      simp [runL, runR, sub, Lynx.Term.true]
      """

    law tuple_delete_fetch(tuple, index, other, depth, node),
      requires:
        arrows_static?(tuple, {depth, node}) and depth?(depth) and is_integer(index) and is_integer(other) and
          is_map(Descr.tuple_delete_at(tuple, index)),
      expects:
        same_fetch?(
          Descr.tuple_fetch(Descr.tuple_delete_at(tuple, index), other),
          Descr.tuple_fetch(tuple, if(other < index, do: other, else: other + 1))
        ),
      proof: ~LEAN"""
      -- The type nests at most `d` levels, so the proofs run from the bound of level `d` on, and the precondition from its
      -- own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_delete_fetch:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_delete_fetch:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨hs, -⟩, hi⟩, ho⟩, hmap⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨q, rfl⟩ : ∃ q : Int, other = .integer q := by
        cases other <;> simp [Erlang.erlang.«is_integer/1»] at ho
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmap
        simp [Erlang.erlang.«is_map/1»] at hmap
      by_cases neg : z < 0
      · have : ¬0 ≤ z := by omega
        rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmap
        simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare, this,
          Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨onlyX, shortX, r, rfl, tr, sr⟩⟩ :=
        Nest.delete_cases (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · simp [run, Erlang.erlang.«is_map/1»] at hmap
      · simp [run, Erlang.erlang.«is_map/1»] at hmap
      simp only [Lynx.apply_eq, «tuple_delete_fetch:ensures/5», run, Lynx.Except.ok_bind]
      by_cases qneg : q < 0
      · have lt : q < (i : Int) := by omega
        simp [Nest.fetch_neg _ _ qneg, Erlang.erlang.«</2», Int.compare_eq_lt, lt, pure, Except.pure,
          «same_fetch?/2», Erlang.erlang.«==/2», Lynx.Term.true]
      obtain ⟨o, rfl⟩ : ∃ o : Nat, q = o := ⟨q.toNat, by omega⟩
      obtain ⟨a, b, ra, rb, same⟩ := Nest.delete_same_fetch (Or.inr ⟨X, rfl, sX⟩) onlyX shortX tr sr o hm
      by_cases hoi : o < i
      · have lt : (o : Int) < (i : Int) := by omega
        simp only [hoi, ite_true] at rb
        simp [ra, rb, Erlang.erlang.«</2», Int.compare_eq_lt, lt, pure, Except.pure, same, Lynx.Term.true]
      · have nlt : ¬(o : Int) < (i : Int) := by omega
        simp only [hoi, ite_false] at rb
        have rb' : Elixir.Module.Types.Descr.«tuple_fetch/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100))
            (.map X) (.integer ((o : Int) + 1)) = .ok b := by simpa using rb
        simp [ra, rb', Erlang.erlang.«</2», Int.compare_eq_lt, nlt, Erlang.erlang.«+/2_integers», same, Lynx.Term.true]
      """

    law tuple_delete_sound(tuple, index, depth, node),
      requires:
        arrows_static?(tuple, {depth, node}) and depth?(depth) and is_integer(index) and
          is_map(Descr.tuple_delete_at(tuple, index)),
      expects:
        Descr.subtype?(
          Descr.opt_intersection(tuple, Descr.open_tuple(:lists.duplicate(index + 1, Descr.term()))),
          Descr.tuple_insert_at(Descr.tuple_delete_at(tuple, index), index, Descr.term())
        ),
      proof: ~LEAN"""
      -- The type nests at most `d` levels, so the proofs run from the bound of level `d` on, and the precondition from its
      -- own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_delete_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_delete_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨hs, -⟩, hi⟩, hmap⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmap
        simp [Erlang.erlang.«is_map/1»] at hmap
      by_cases neg : z < 0
      · have : ¬0 ≤ z := by omega
        rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmap
        simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare, this,
          Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨onlyX, shortX, r, rfl, tr, sr⟩⟩ :=
        Nest.delete_cases (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · simp [run, Erlang.erlang.«is_map/1»] at hmap
      · simp [run, Erlang.erlang.«is_map/1»] at hmap
      have ef := (Nest.level node d).ef
      have long : ∀ x, Nest.TT node d X x → i < x.length := fun x hx =>
        Classical.byContradiction fun h => shortX ⟨x, hx, by omega⟩
      have tz : ∀ w, Nest.TT node d [(.atom "tuple", r)] w ↔ ∃ x, Nest.TT node d X x ∧ i < x.length ∧ w = x.eraseIdx i :=
        fun w => by rw [Nest.tt_single, sr, Nest.split_erase]
      have dZ : Nest.DE (Nest.level node d).E (.map [(.atom "tuple", r)]) := Or.inr ⟨_, rfl, Nest.descrC_put Nest.descrC_nil tr⟩
      -- Inserting any value back.
      obtain ⟨x₀, hx₀⟩ := onlyX.2
      obtain ⟨Y, runI⟩ := Nest.insert_checked_ok dZ ⟨Nest.single_tuples r, _, (tz _).mpr ⟨x₀, hx₀, long x₀ hx₀, rfl⟩⟩
        ef.term i (fun w hw => by
          obtain ⟨y, hy, ly, rfl⟩ := (tz w).mp hw
          rw [List.length_eraseIdx]; split <;> omega) (m := δ + 100) hm
      obtain ⟨-, -, dY, -, ttY⟩ := Nest.insert_tuple dZ ef.term i hm runI
      -- The open tuple of the tuples long enough.
      have hl : ∀ x ∈ List.replicate (i + 1) (.atom "term"), (Nest.level node d).E x := by
        intro x mx; rw [List.eq_of_mem_replicate mx]; exact ef.term
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate (i + 1) (.atom "term")) fun x mx => ef.static (hl x mx)
      have dO := Nest.fused_de (Or.inl rfl) hl key
      obtain ⟨c, gc, rc, sc⟩ := Nest.gc_opt_inter2 (Nest.GC.tc (Or.inr ⟨X, rfl, sX⟩)) (Nest.GC.tc dO) (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      have incl : ∀ v : Nest.PN node d, Nest.denD (.map X) v → Nest.denD (.map Y) v := by
        intro v hv
        obtain ⟨w, hw⟩ := Nest.pt_tuple v (onlyX.1 v hv)
        rw [hw] at hv ⊢
        have lw := long w hv
        refine (ttY _).mpr ⟨w.take i, w[i], w.drop (i + 1), by simp, by simp; omega, ef.den_term _, ?_⟩
        refine (tz _).mpr ⟨w, hv, lw, ?_⟩
        rw [List.eraseIdx_eq_take_drop_succ]
      have sub := Nest.gc_sub gc (Nest.GC.tc dY) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        (fun v h => incl v ((sc.1 v).mp h).1) (fun v h => by
          rw [Nest.upper_tc dY]
          have := (sc.2 v).mp h
          rw [Nest.upper_tc (Or.inr ⟨X, rfl, sX⟩)] at this
          exact incl v this.1)
      have dup₁ : Erlang.lists.«duplicate/2» (.integer ((i : Int) + 1)) (.atom "term") =
          .ok (Lynx.Term.list (List.replicate (i + 1) (.atom "term"))) := by simpa using dup_nat (.atom "term") (i + 1)
      simp only [Lynx.apply_eq, «tuple_delete_sound:ensures/4»]
      simp only [Elixir.Module.Types.Descr.«term/0», pure, Except.pure, Lynx.Except.ok_bind, Erlang.erlang.«+/2_integers», dup₁,
        rot, rc, run, Nest.insert_at_static _ _ _ (Or.inl rfl), runI]
      simp [sub, Lynx.Term.true]
      """

    law tuple_delete_least(tuple, index, other, depth, node),
      requires:
        arrows_static?(tuple, {depth, node}) and arrows_static?(other, {depth, node}) and depth?(depth) and
          is_integer(index) and is_map(Descr.tuple_delete_at(tuple, index)) and
          is_map(Descr.tuple_insert_at(other, index, Descr.term())) and
          Descr.subtype?(tuple, Descr.tuple_insert_at(other, index, Descr.term())),
      expects: Descr.subtype?(Descr.tuple_delete_at(tuple, index), other),
      proof: ~LEAN"""
      -- The type nests at most `d` levels, so the proofs run from the bound of level `d` on, and the precondition from its
      -- own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_delete_least:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_delete_least:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨⟨⟨hs, ho⟩, -⟩, hi⟩, hmap⟩, hins⟩, hsub⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmap
        simp [Erlang.erlang.«is_map/1»] at hmap
      by_cases neg : z < 0
      · have : ¬0 ≤ z := by omega
        rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmap
        simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare, this,
          Erlang.erlang.«is_map/1»] at hmap
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by omega⟩
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨onlyX, shortX, r, rfl, tr, sr⟩⟩ :=
        Nest.delete_cases (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · simp [run, Erlang.erlang.«is_map/1»] at hmap
      · simp [run, Erlang.erlang.«is_map/1»] at hmap
      have ef := (Nest.level node d).ef
      have tz : ∀ w, Nest.TT node d [(.atom "tuple", r)] w ↔ ∃ x, Nest.TT node d X x ∧ i < x.length ∧ w = x.eraseIdx i :=
        fun w => by rw [Nest.tt_single, sr, Nest.split_erase]
      have dZ : Nest.DE (Nest.level node d).E (.map [(.atom "tuple", r)]) := Or.inr ⟨_, rfl, Nest.descrC_put Nest.descrC_nil tr⟩
      -- The other type, with any value inserted.
      have dS := Nest.arrows_static_ok ho
      rcases dS with rfl | ⟨S, rfl, sS⟩
      · simp [Elixir.Module.Types.Descr.«term/0», Nest.insert_at_term, Erlang.erlang.«is_map/1»] at hins
      obtain ⟨YS, runS⟩ : ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map S) (.integer i) (.atom "term") = .ok (.map Y) := by
        simp only [Elixir.Module.Types.Descr.«term/0», pure, Except.pure, Lynx.Except.ok_bind,
          Nest.insert_at_static _ _ _ (Or.inl rfl)] at hins
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map S) (.integer i) (.atom "term") with
        | error _ => rw [h] at hins; cases hins
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hins
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hins
          exact ⟨_, rfl⟩
      obtain ⟨-, -, dYS, -, ttYS⟩ := Nest.insert_tuple (Or.inr ⟨S, rfl, sS⟩) ef.term i hm runS
      have subXS := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) dYS (m := δ + 100) (by omega)
      simp only [Elixir.Module.Types.Descr.«term/0», pure, Except.pure, Lynx.Except.ok_bind,
        Nest.insert_at_static _ _ _ (Or.inl rfl), runS, subXS, Except.ok.injEq] at hsub
      have subXS := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      -- The tuples without the element at the index are tuples of the other type.
      have sub := Nest.next_sub dZ (Or.inr ⟨S, rfl, sS⟩) (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node d (.map [(.atom "tuple", r)]) (.map S) from fun v hv => by
        obtain ⟨w, hw⟩ := Nest.pt_tuple v (Nest.single_tuples r v hv)
        rw [hw] at hv ⊢
        obtain ⟨x, hx, lx, rfl⟩ := (tz w).mp hv
        have hY : Nest.TT node d YS x := (Nest.denD_tpt x).mp (subXS _ ((Nest.denD_tpt x).mpr hx))
        obtain ⟨w₁, y, w₂, rfl, l₁, -, hS⟩ := (ttYS x).mp hY
        rw [List.eraseIdx_append_of_length_le (by omega)]
        simpa [l₁] using hS)] at sub
      simp only [Lynx.apply_eq, «tuple_delete_least:ensures/5», run, Lynx.Except.ok_bind]
      simp [sub, Lynx.Term.true]
      """

    law tuple_delete_badindex(tuple, index, depth, node),
      requires:
        arrows_static?(tuple, {depth, node}) and depth?(depth) and is_integer(index) and index >= 0 and
          Descr.subtype?(tuple, Descr.tuple()) and not Descr.empty?(tuple),
      expects:
        (case Descr.tuple_delete_at(tuple, index) do
          :badindex -> not Descr.subtype?(tuple, Descr.open_tuple(:lists.duplicate(index + 1, Descr.term())))
          result when is_map(result) -> Descr.subtype?(tuple, Descr.open_tuple(:lists.duplicate(index + 1, Descr.term())))
          _ -> false
        end),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the
      -- precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_delete_badindex:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_delete_badindex:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨⟨hs, -⟩, hi⟩, hnn⟩, htup⟩, hne⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := by
        refine ⟨z.toNat, ?_⟩
        by_cases neg : z < 0
        · simp [Erlang.erlang.«>=/2», Int.isGE_compare, neg] at hnn
        · omega
      have dt := Nest.arrows_static_ok hs
      have sT := Nest.next_sub dt Nest.tupleTop_de (m := δ + 100) (by omega)
      rw [show Elixir.Module.Types.Descr.«tuple/0» =
        .ok (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) from rfl, Lynx.Except.ok_bind, sT] at htup
      rw [Except.ok.injEq] at htup
      have onlyT := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) htup)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · have := (Nest.tupleTop_den Nest.bitPt).mp (onlyT Nest.bitPt (Nest.denD_term _))
        simp [Nest.bitPt] at this
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      rw [ne] at hne
      have ex : ∃ v : Nest.PN node d, Nest.denD (.map X) v := by
        cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD (.map X) v)
        · exact Classical.byContradiction fun none => by
            have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
            rw [h] at this; cases this
        · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
      have only : Nest.TOnly node d X := by
        refine ⟨fun v hv => (Nest.tupleTop_den v).mp (onlyT v hv), ?_⟩
        obtain ⟨v, hv⟩ := ex
        obtain ⟨w, hw⟩ := Nest.pt_tuple v ((Nest.tupleTop_den v).mp (onlyT v hv))
        exact ⟨w, (hw X).mp hv⟩
      obtain ⟨k, rot, key⟩ := Nest.open_tuple_run (List.replicate (i + 1) (.atom "term"))
        fun x mx => by rw [List.eq_of_mem_replicate mx]; exact Or.inl rfl
      have hl : ∀ x ∈ List.replicate (i + 1) (.atom "term"), (Nest.level node d).E x := by
        intro x mx; rw [List.eq_of_mem_replicate mx]; exact (Nest.level node d).ef.term
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) (Nest.fused_de (Or.inl rfl) hl key) (m := δ + 100) (by omega)
      have subIff : Nest.SubN node d (.map X)
          (.map [(.atom "tuple", .tuple #[.integer k, .atom "open", Lynx.Term.list (List.replicate (i + 1) (.atom "term"))])]) ↔ ∀ w, Nest.TT node d X w → i + 1 ≤ w.length := by
        constructor
        · intro h w hw
          have := h _ ((Nest.denD_tpt w).mpr hw)
          rwa [Nest.denD_tpt, Nest.tt_open] at this
        · intro h v hv
          obtain ⟨w, hw⟩ := Nest.pt_tuple v (only.1 v hv)
          rw [hw X] at hv
          rw [hw, Nest.tt_open]
          exact h w hv
      have dup' : Erlang.lists.«duplicate/2» (.integer ((i : Int) + 1)) (.atom "term") =
          .ok (Lynx.Term.list (List.replicate (i + 1) (.atom "term"))) := by simpa using dup_nat (.atom "term") (i + 1)
      obtain ⟨res, run, ⟨-, nonly⟩ | ⟨rfl, -, w, hw, len⟩ | ⟨-, short, r, rfl, -⟩⟩ :=
        Nest.delete_cases (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) i (m := δ + 100) hm
      · exact absurd only nonly
      · rw [Nest.bp_false.mpr fun h => by have := (subIff.mp h) w hw; omega] at sub
        simp only [Lynx.apply_eq, «tuple_delete_badindex:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», dup', rot, sub,
          Erlang.erlang.«not/1», Lynx.Term.true]
      · rw [Nest.bp_true.mpr (subIff.mpr fun w hw => Classical.byContradiction fun h => short ⟨w, hw, by omega⟩)] at sub
        simp only [Lynx.apply_eq, «tuple_delete_badindex:ensures/4»]
        simp [run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«term/0», dup', rot, sub,
          Erlang.erlang.«not/1», Lynx.Term.true]
      """

    law tuple_values_sound(tuple, index, depth, node),
      requires:
        arrows_static?(tuple, {depth, node}) and depth?(depth) and is_integer(index) and index >= 0 and
          Descr.tuple_values(tuple) != :badtuple,
      expects:
        Descr.subtype?(
          Descr.opt_intersection(tuple, Descr.open_tuple(:lists.duplicate(index + 1, Descr.term()))),
          Descr.open_tuple(:lists.duplicate(index, Descr.term()) ++ [Descr.tuple_values(tuple)])
        ),
      proof: ~LEAN"""
      -- The type nests at most `d` levels, so the proofs run from the bound of level `d` on, and the precondition from its
      -- own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_values_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_values_sound:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨hs, -⟩, hi⟩, hnn⟩, hv⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := by
        refine ⟨z.toNat, ?_⟩
        by_cases neg : z < 0
        · simp [Erlang.erlang.«>=/2», Int.isGE_compare, neg] at hnn
        · omega
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«tuple_values/1», Erlang.erlang.«/=/2», pure, Except.pure] at hv
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨onlyX, hres, P, tP, sP, sr⟩⟩ :=
        Nest.values_cases (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm
      · simp [run, Erlang.erlang.«/=/2»] at hv
      have ef := (Nest.level node d).ef
      -- The open tuples of the tuples long enough, and of those with a value at the index.
      have hl₁ : ∀ x ∈ List.replicate (i + 1) (.atom "term"), (Nest.level node d).E x := by
        intro x mx; rw [List.eq_of_mem_replicate mx]; exact ef.term
      obtain ⟨k₁, rot₁, key₁⟩ := Nest.open_tuple_run (List.replicate (i + 1) (.atom "term"))
        fun x mx => ef.static (hl₁ x mx)
      have dO₁ := Nest.fused_de (Or.inl rfl) hl₁ key₁
      have hl₂ : ∀ x ∈ List.replicate i (.atom "term") ++ [res], (Nest.level node d).E x := by
        intro x mx
        rcases List.mem_append.mp mx with mx | mx
        · rw [List.eq_of_mem_replicate mx]; exact ef.term
        · simp at mx; subst mx; exact hres
      obtain ⟨k₂, rot₂, key₂⟩ := Nest.open_tuple_run (List.replicate i (.atom "term") ++ [res])
        fun x mx => ef.static (hl₂ x mx)
      have dO₂ := Nest.fused_de (Or.inl rfl) hl₂ key₂
      obtain ⟨c, gc, rc, sc⟩ := Nest.gc_opt_inter2 (Nest.GC.tc (Or.inr ⟨X, rfl, sX⟩)) (Nest.GC.tc dO₁) (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega)
      have incl : ∀ v : Nest.PN node d, Nest.denD (.map X) v →
          Nest.denD (.map [(.atom "tuple", .tuple #[.integer k₁, .atom "open",
            Lynx.Term.list (List.replicate (i + 1) (.atom "term"))])]) v →
          Nest.denD (.map [(.atom "tuple", .tuple #[.integer k₂, .atom "open",
            Lynx.Term.list (List.replicate i (.atom "term") ++ [res])])]) v := by
        intro v hX hO
        obtain ⟨w, hw⟩ := Nest.pt_tuple v (onlyX.1 v hX)
        rw [hw] at hX hO ⊢
        rw [Nest.tt_open] at hO
        rw [Nest.tt_open_at hres i k₂]
        obtain ⟨p, mp, hp⟩ := (sP w).mpr hX
        have lw : i < w.length := by omega
        refine ⟨w.take i, w[i], w.drop (i + 1), by simp, by simp; omega, ?_⟩
        exact (sr _).mpr ⟨p, mp, Nest.pieceIn_val (tP p mp) hp (j := i) (by simp [lw])⟩
      have sub := Nest.gc_sub gc (Nest.GC.tc dO₂) (m := δ + 100) (by rw [Nest.level_K] at hm ⊢; omega)
        (fun v h => incl v ((sc.1 v).mp h).1 ((sc.1 v).mp h).2) (fun v h => by
          rw [Nest.upper_tc dO₂]
          have := (sc.2 v).mp h
          rw [Nest.upper_tc (Or.inr ⟨X, rfl, sX⟩), Nest.upper_tc dO₁] at this
          exact incl v this.1 this.2)
      have dup₁ : Erlang.lists.«duplicate/2» (.integer ((i : Int) + 1)) (.atom "term") =
          .ok (Lynx.Term.list (List.replicate (i + 1) (.atom "term"))) := by simpa using dup_nat (.atom "term") (i + 1)
      simp only [Lynx.apply_eq, «tuple_values_sound:ensures/4»]
      simp only [Elixir.Module.Types.Descr.«term/0», pure, Except.pure, Lynx.Except.ok_bind, Erlang.erlang.«+/2_integers», dup₁,
        rot₁, rc, dup_nat, run]
      rw [append_list, Lynx.Except.ok_bind, rot₂, Lynx.Except.ok_bind]
      simp [sub, Lynx.Term.true]
      """

    law tuple_values_least(tuple, sizes, value, depth, node),
      requires:
        arrows_static?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          sizes?(sizes) and Descr.tuple_values(tuple) != :badtuple and
          Descr.subtype?(tuple, closed_tuples(sizes, value)),
      expects: Descr.subtype?(Descr.tuple_values(tuple), value),
      proof: ~LEAN"""
      -- The tuple nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_values_least:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_values_least:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨ht, hel⟩, -⟩, hs⟩, hnb⟩, hsub⟩ := requires
      have ht : «arrows_static?/2» tuple (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using ht
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨ns, rfl⟩ := Nest.sizes_nat hs
      rcases Nest.arrows_static_ok ht with rfl | ⟨X, rfl, sX⟩
      · simp [Elixir.Module.Types.Descr.«tuple_values/1», Erlang.erlang.«/=/2», pure, Except.pure] at hnb
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨onlyX, hres, P, tP, sP, sr⟩⟩ :=
        Nest.values_cases (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) hm
      · simp [run, Erlang.erlang.«/=/2»] at hnb
      -- The tuples of the type are closed tuples of the sizes, of values of the value type.
      obtain ⟨C, rC, dC, sC⟩ := Nest.closed_tuples_sem del hm ns
      have subC := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) dC (m := δ + 100) (by omega)
      rw [rC, Lynx.Except.ok_bind, subC, Except.ok.injEq] at hsub
      have subC := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have tuples : ∀ w, Nest.TT node (d + 1) X w → w.length ∈ ns ∧ ∀ y ∈ w, (Nest.level node (d + 1)).den value y :=
        fun w hw => sC w (subC _ ((Nest.denD_tpt w).mpr hw))
      have le_sum : ∀ (l : List Nat) (a : Nat), a ∈ l → a ≤ l.sum := by
        intro l
        induction l with
        | nil => intro a h; simp at h
        | cons b l ih =>
          intro a h
          rcases List.mem_cons.mp h with rfl | h
          · simp
          · have := ih a h; simp; omega
      have vals : ∀ y, (Nest.level node (d + 1)).den res y → (Nest.level node (d + 1)).den value y := by
        intro y hy
        obtain ⟨q, mq, tag, l, rfl, ne, h⟩ := (sr y).mp hy
        obtain ⟨tag', l', e, g, -⟩ := tP _ mq
        simp only [Lynx.Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, Lynx.Term.atom.injEq, and_true] at e
        obtain ⟨rfl, -⟩ := e
        by_cases op : tag = "open"
        · -- Open literals with values hold tuples longer than any size.
          exfalso
          subst op
          obtain ⟨w, hw, lw⟩ := Nest.inT_witness_open (Classical.choice (Nest.level node (d + 1)).ef.inhabited) ne
            (ns.sum + 1)
          have hX := (sP w).mp ⟨_, mq, Nest.pieceIn_iff.mpr (by simpa using hw)⟩
          have := le_sum _ _ (tuples w hX).1
          omega
        · have cl : tag = "closed" := g.resolve_left op
          subst cl
          obtain ⟨e, me, he⟩ := h.resolve_left (by simp)
          obtain ⟨w, hw, j, hj⟩ := Nest.inT_witness_closed ne me he
          have hX := (sP w).mp ⟨_, mq, Nest.pieceIn_iff.mpr (by simpa using hw)⟩
          exact (tuples w hX).2 y (List.mem_of_getElem? hj)
      simp only [Lynx.apply_eq, «tuple_values_least:ensures/5», run, Lynx.Except.ok_bind]
      rw [(Nest.level node (d + 1)).ef.subc hres del vals (δ + 100) (by omega)]
      rfl
      """

    law tuple_values_badtuple(tuple, depth, node),
      requires: arrows_static?(tuple, {depth, node}) and depth?(depth),
      expects:
        (Descr.tuple_values(tuple) == :badtuple) ==
          (Descr.empty?(tuple) or not Descr.subtype?(tuple, Descr.tuple())),
      proof: ~LEAN"""
      -- The type nests at most `d` levels, so the proofs run from the bound of level `d` on.
      simp only [«tuple_values_badtuple:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨hs, hdep⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hdep
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dt := Nest.arrows_static_ok hs
      have sT := Nest.next_sub dt Nest.tupleTop_de (m := δ + 100) (by omega)
      have tup : Elixir.Module.Types.Descr.«tuple/0» =
          .ok (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) := rfl
      simp only [Lynx.apply_eq, «tuple_values_badtuple:ensures/3»]
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · -- The top type holds values other than tuples.
        have nt : ¬Nest.SubN node d (.atom "term")
            (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) := fun h => by
          have := (Nest.tupleTop_den Nest.bitPt).mp (h Nest.bitPt (Nest.denD_term _))
          simp [Nest.bitPt] at this
        rw [Nest.bp_false.mpr nt] at sT
        have ne : Elixir.Module.Types.Descr.«empty?/1» (D (δ + 100)) (.atom "term") = .ok (.atom "false") := by
          rw [Nest.next_empty (t := node) (n := d) Nest.tc_term (m := δ + 100) (by omega),
            Nest.bp_false.mpr (fun h => h Nest.bitPt (Nest.denD_term _))]
          rfl
        simp [ne, Elixir.Module.Types.Descr.«tuple_values/1», Nest.next_empty (t := node) (n := d) Nest.tc_term (m := δ + 100) (by omega), tup, sT,
          Erlang.erlang.«==/2», Erlang.erlang.«not/1», Lynx.Except.orElse, boolAtom, Lynx.Term.true, pure, Except.pure]
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      -- The type holds only tuples, and some, exactly when it holds some value and only tuples.
      have only : Nest.TOnly node d X ↔ (¬∀ v : Nest.PN node d, ¬Nest.denD (.map X) v) ∧
          Nest.SubN node d (.map X) (.map [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]) := by
        constructor
        · rintro ⟨h₁, w, hw⟩
          exact ⟨fun h => h _ ((Nest.denD_tpt w).mpr hw), fun v hv => (Nest.tupleTop_den v).mpr (h₁ v hv)⟩
        · rintro ⟨h, onlyT⟩
          obtain ⟨v, hv⟩ := Classical.not_forall_not.mp h
          refine ⟨fun v hv => (Nest.tupleTop_den v).mp (onlyT v hv), ?_⟩
          obtain ⟨w, hw⟩ := Nest.pt_tuple v ((Nest.tupleTop_den v).mp (onlyT v hv))
          exact ⟨w, (hw X).mp hv⟩
      obtain ⟨res, run, ⟨rfl, nonly⟩ | ⟨onlyX, hres, -⟩⟩ := Nest.values_cases (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm
      · by_cases h₁ : ∀ v : Nest.PN node d, ¬Nest.denD (.map X) v
        · rw [Nest.bp_true.mpr h₁] at ne
          simp [run, ne, Erlang.erlang.«==/2», Lynx.Except.orElse, boolAtom, Lynx.Term.true]
        · have h₂ := fun h₂ => nonly (only.mpr ⟨h₁, h₂⟩)
          rw [Nest.bp_false.mpr h₁] at ne
          rw [Nest.bp_false.mpr h₂] at sT
          simp [run, ne, tup, sT, Erlang.erlang.«==/2», Erlang.erlang.«not/1», Lynx.Except.orElse, boolAtom,
            Lynx.Term.true]
      · have nb : res ≠ .atom "badtuple" := by
          rcases (Nest.level node d).ef.static hres with rfl | ⟨Y, rfl, -⟩ | ⟨a, b, c, rfl⟩ <;> simp
        obtain ⟨h₁, h₂⟩ := only.mp onlyX
        rw [Nest.bp_false.mpr h₁] at ne
        rw [Nest.bp_true.mpr h₂] at sT
        simp [run, ne, nb, tup, sT, Erlang.erlang.«==/2», Erlang.erlang.«not/1», Lynx.Except.orElse, boolAtom,
          Lynx.Term.true]
      """

    law tuple_insert_upper(tuple, index, value, depth, node),
      requires:
        arrows_gradual?(tuple, {depth + 1, node}) and arrows_gradual?(value, {depth, node}) and not Descr.empty?(value) and
          depth?(depth) and is_integer(index) and
          index >= 0 and is_map(Descr.tuple_insert_at(tuple, index, value)) and
          is_map(Descr.tuple_insert_at(Descr.upper_bound(tuple), index, Descr.upper_bound(value))),
      expects:
        Descr.equal?(
          Descr.upper_bound(Descr.tuple_insert_at(tuple, index, value)),
          Descr.tuple_insert_at(Descr.upper_bound(tuple), index, Descr.upper_bound(value))
        ),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels and the value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_insert_upper:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_insert_upper:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hg, hgv⟩, -⟩, -⟩, hi⟩, hi0⟩, hmap⟩, hmapU⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) tuple
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gT, -, dTu⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      obtain ⟨gV, dVl, dVu⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega) hgv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by simp [Erlang.erlang.«>=/2», Int.isGE_compare] at hi0; omega⟩
      rcases gT.shape with rfl | ⟨X, rfl⟩
      · rw [Nest.insert_at_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      -- The insert into the gradual type.
      obtain ⟨R, run⟩ : ∃ R, Elixir.Module.Types.Descr.«tuple_insert_at/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value = .ok (.map R) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨gR, uR, -⟩ := Nest.ins_at gT gV dVl dVu i hm run
      -- The insert into the upper bound.
      rw [Nest.upper_bound_run gT.ub, Nest.upper_bound_run gV.ub] at hmapU
      simp only [Lynx.Except.ok_bind] at hmapU
      have sv : Nest.upper value = .atom "term" ∨
          ∃ Z, Nest.upper value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dVu with h | ⟨Z, h, sZ⟩
        · exact Or.inl h
        · exact Or.inr ⟨Z, h, sZ.static⟩
      obtain ⟨U, eU, dU⟩ : ∃ U, Nest.upper (.map X) = .map U ∧ Nest.DE (Nest.level node (d + 1)).E (.map U) := by
        rcases dTu with h | ⟨U, h, sU⟩
        · rw [h, Nest.insert_at_term] at hmapU; simp [Erlang.erlang.«is_map/1»] at hmapU
        · exact ⟨U, h, Or.inr ⟨U, rfl, sU⟩⟩
      rw [eU, Nest.insert_at_static _ _ _ sv] at hmapU
      obtain ⟨R₂, run₂⟩ : ∃ R₂, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map U) (.integer i) (Nest.upper value) =
          .ok (.map R₂) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map U) (.integer i) (Nest.upper value) with
        | error _ => rw [h] at hmapU; cases hmapU
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapU
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapU
          exact ⟨_, rfl⟩
      obtain ⟨-, long, dR₂, oR₂, tR₂⟩ := Nest.insert_tuple dU (Or.inl dVu) i (by omega) run₂
      -- The same tuples.
      have same : ∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper (.map R)) q ↔ Nest.denD (.map R₂) q := fun q => by
        rw [uR, Nest.inSat oR₂ tR₂, eU]
        refine Nest.insAt_congr fun u => ?_
        rw [Nest.denD_tpt]
        constructor
        · rintro (⟨h, -⟩ | h)
          · exact h
          · have := gT.inv _ ((Nest.denD_rmDyn X _).mp ((Nest.denD_tpt u).mpr h))
            rw [eU, Nest.denD_tpt] at this
            exact this
        · intro h; exact Or.inl ⟨h, long u h⟩
      have eq := Nest.elem_equal (Nest.ef_next node (d + 1)) gR.up_tc dR₂ same (m := δ + 100) (by omega)
      simp only [Lynx.apply_eq, «tuple_insert_upper:ensures/5»]
      rw [Nest.upper_bound_run gT.ub, Nest.upper_bound_run gV.ub, eU]
      simp only [Lynx.Except.ok_bind]
      rw [Nest.insert_at_static _ _ _ sv]
      simp [run, run₂, Nest.upper_bound_run gR.ub, eq, Lynx.Term.true]
      """

    law tuple_insert_lower(tuple, index, value, depth, node),
      requires:
        arrows_gradual?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and not Descr.empty?(value) and
          depth?(depth) and is_integer(index) and
          index >= 0 and is_map(Descr.tuple_insert_at(tuple, index, value)) and
          is_map(Descr.tuple_insert_at(Descr.lower_bound(tuple), index, value)),
      expects:
        Descr.equal?(
          Descr.lower_bound(Descr.tuple_insert_at(tuple, index, value)),
          Descr.tuple_insert_at(Descr.lower_bound(tuple), index, value)
        ),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels and the value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_insert_lower:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_insert_lower:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hg, hgv⟩, -⟩, -⟩, hi⟩, hi0⟩, hmap⟩, hmapL⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) tuple
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gT, dTl, -⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      have dv := Nest.arrows_static_ok hgv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with h | ⟨Z, h, sZ⟩
        · exact Or.inl h
        · exact Or.inr ⟨Z, h, sZ.static⟩
      have uv : Nest.upper value = value := Nest.upper_tc dv
      have lv : Nest.lower value = value := by
        rcases sv with rfl | ⟨Z, rfl, sZ⟩
        · rfl
        · simp [Nest.lower, Nest.rmDyn_static sZ]
      have gV : Nest.GC (Nest.level node d) value := Nest.GC.tc dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by simp [Erlang.erlang.«>=/2», Int.isGE_compare] at hi0; omega⟩
      rcases gT.shape with rfl | ⟨X, rfl⟩
      · rw [Nest.insert_at_term] at hmap; simp [Erlang.erlang.«is_map/1»] at hmap
      -- The insert into the gradual type.
      obtain ⟨R, run⟩ : ∃ R, Elixir.Module.Types.Descr.«tuple_insert_at/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value = .ok (.map R) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨gR, -, sR⟩ := Nest.ins_at gT gV (by rw [lv]; exact dv) (by rw [uv]; exact dv) i hm run
      have sR := sR uv
      -- The insert into the lower bound.
      rw [Nest.lower_bound_run (Or.inr ⟨X, rfl⟩)] at hmapL
      simp only [Lynx.Except.ok_bind, Nest.lower] at hmapL
      rw [Nest.insert_at_static _ _ _ sv] at hmapL
      obtain ⟨R₂, run₂⟩ : ∃ R₂, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map (Nest.rmDyn X)) (.integer i) value =
          .ok (.map R₂) := by
        cases h : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map (Nest.rmDyn X)) (.integer i) value with
        | error _ => rw [h] at hmapL; cases hmapL
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapL
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapL
          exact ⟨_, rfl⟩
      obtain ⟨-, -, dR₂, oR₂, tR₂⟩ := Nest.insert_tuple dTl (Or.inl dv) i (by omega) run₂
      have same : ∀ q : Nest.PN node (d + 1), Nest.denD (Nest.lower (.map R)) q ↔ Nest.denD (.map R₂) q := fun q => by
        rw [Nest.lower, Nest.denD_rmDyn, sR, Nest.inSat oR₂ tR₂]
      have eq := Nest.elem_equal (Nest.ef_next node (d + 1)) gR.low_tc dR₂ same (m := δ + 100) (by omega)
      simp only [Lynx.apply_eq, «tuple_insert_lower:ensures/5»]
      rw [Nest.lower_bound_run (Or.inr ⟨X, rfl⟩)]
      simp only [Lynx.Except.ok_bind, Nest.lower]
      rw [Nest.insert_at_static _ (Nest.rmDyn X) i sv]
      simp [run, run₂, Nest.lower_bound_run (Or.inr ⟨R, rfl⟩), eq, Lynx.Term.true]
      """

    law tuple_replace_upper(tuple, index, value, depth, node),
      requires:
        arrows_gradual?(tuple, {depth + 1, node}) and arrows_gradual?(value, {depth, node}) and not Descr.empty?(value) and
          depth?(depth) and is_integer(index) and
          index >= 0 and is_map(Descr.tuple_replace_at(tuple, index, value)) and
          is_map(Descr.tuple_replace_at(Descr.upper_bound(tuple), index, Descr.upper_bound(value))),
      expects:
        Descr.equal?(
          Descr.upper_bound(Descr.tuple_replace_at(tuple, index, value)),
          Descr.tuple_replace_at(Descr.upper_bound(tuple), index, Descr.upper_bound(value))
        ),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels and the value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_replace_upper:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_replace_upper:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hg, hgv⟩, -⟩, -⟩, hi⟩, hi0⟩, hmap⟩, hmapU⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) tuple
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gT, -, dTu⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      obtain ⟨gV, dVl, dVu⟩ := Nest.arrows_gradual_ok (t := node) (n := d) (m := δ + 100)
        (by rw [Nest.level_K] at hm ⊢; omega) hgv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by simp [Erlang.erlang.«>=/2», Int.isGE_compare] at hi0; omega⟩
      rcases gT.shape with rfl | ⟨X, rfl⟩
      · simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Elixir.Module.Types.Descr.«tuple_delete_at/2»,
          Erlang.erlang.«is_map/1», Erlang.erlang.«==/2», Lynx.Except.tryWith, Lynx.Except.orElse, Erlang.erlang.«is_integer/1», Lynx.Except.andAlso] at hmap
      -- The insert into the gradual type.
      obtain ⟨R, run⟩ : ∃ R, Elixir.Module.Types.Descr.«tuple_replace_at/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value = .ok (.map R) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨R₁, hd, hi'⟩ := Nest.rep_split gT i value hm run
      obtain ⟨gR₁, -, -, sR₁, uR₁⟩ := Nest.del_pts gT i hm hd
      obtain ⟨gR, uR, -⟩ := Nest.ins_at gR₁ gV dVl dVu i hm hi'
      -- The replace in the upper bound.
      rw [Nest.upper_bound_run gT.ub, Nest.upper_bound_run gV.ub] at hmapU
      simp only [Lynx.Except.ok_bind] at hmapU
      have sv : Nest.upper value = .atom "term" ∨
          ∃ Z, Nest.upper value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dVu with h | ⟨Z, h, sZ⟩
        · exact Or.inl h
        · exact Or.inr ⟨Z, h, sZ.static⟩
      obtain ⟨U, eU, dU⟩ : ∃ U, Nest.upper (.map X) = .map U ∧ Nest.DE (Nest.level node (d + 1)).E (.map U) := by
        rcases dTu with h | ⟨U, h, sU⟩
        · rw [h] at hmapU
          simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Elixir.Module.Types.Descr.«tuple_delete_at/2»,
            Erlang.erlang.«is_map/1», Erlang.erlang.«==/2», Lynx.Except.tryWith, Lynx.Except.orElse, Erlang.erlang.«is_integer/1», Lynx.Except.andAlso] at hmapU
        · exact ⟨U, h, Or.inr ⟨U, rfl, sU⟩⟩
      rw [eU] at hmapU
      obtain ⟨R₂, run₂⟩ : ∃ R₂, Elixir.Module.Types.Descr.«tuple_replace_at/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map U) (.integer i) (Nest.upper value) =
          .ok (.map R₂) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map U) (.integer i) (Nest.upper value) with
        | error _ => rw [h] at hmapU; cases hmapU
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapU
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapU
          exact ⟨_, rfl⟩
      obtain ⟨long, dR₂, oR₂, tR₂⟩ := Nest.rep_static dU i (Or.inl dVu) sv (by omega) run₂
      -- Tuples of the static part are tuples of the upper bound.
      have inU : ∀ u, Nest.TT node (d + 1) (Nest.rmDyn X) u → Nest.TT node (d + 1) U u := fun u h => by
        have := gT.inv _ ((Nest.denD_rmDyn X _).mp ((Nest.denD_tpt u).mpr h))
        rw [eU, Nest.denD_tpt] at this
        exact this
      have pu : ∀ u, ((Nest.denD (Nest.upper (.map X)) (Nest.tpt (t := node) (n := d + 1) u) ∧ i < u.length) ∨
          Nest.TT node (d + 1) (Nest.rmDyn X) u) ↔ Nest.TT node (d + 1) U u := fun u => by
        rw [eU, Nest.denD_tpt]
        exact ⟨fun h => h.elim (·.1) (inU u), fun h => Or.inl ⟨h, long u h⟩⟩
      have same : ∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper (.map R)) q ↔ Nest.denD (.map R₂) q := fun q => by
        rw [uR, Nest.inSat oR₂ tR₂]
        refine Nest.insAt_congr fun u => ?_
        rw [uR₁, ← Nest.denD_tpt, Nest.denD_rmDyn, sR₁, Nest.del_congr pu]
        constructor
        · rintro (⟨h, -⟩ | ⟨v₁, y, v₂, e, len, h⟩)
          · exact h
          · exact ⟨v₁, y, v₂, e, len, inU _ h⟩
        · intro h
          refine Or.inl ⟨h, ?_⟩
          obtain ⟨v₁, y, v₂, rfl, len, -⟩ := h
          simp; omega
      have eq := Nest.elem_equal (Nest.ef_next node (d + 1)) gR.up_tc dR₂ same (m := δ + 100) (by omega)
      simp only [Lynx.apply_eq, «tuple_replace_upper:ensures/5»]
      rw [Nest.upper_bound_run gT.ub, Nest.upper_bound_run gV.ub, eU]
      simp [run, run₂, Nest.upper_bound_run gR.ub, eq, Lynx.Term.true]
      """

    law tuple_replace_lower(tuple, index, value, depth, node),
      requires:
        arrows_gradual?(tuple, {depth + 1, node}) and arrows_static?(value, {depth, node}) and not Descr.empty?(value) and
          depth?(depth) and is_integer(index) and
          index >= 0 and is_map(Descr.tuple_replace_at(tuple, index, value)) and
          is_map(Descr.tuple_replace_at(Descr.lower_bound(tuple), index, value)),
      expects:
        Descr.equal?(
          Descr.lower_bound(Descr.tuple_replace_at(tuple, index, value)),
          Descr.tuple_replace_at(Descr.lower_bound(tuple), index, value)
        ),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels and the value `d`.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_replace_lower:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_replace_lower:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hg, hgv⟩, -⟩, -⟩, hi⟩, hi0⟩, hmap⟩, hmapL⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) tuple
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gT, dTl, -⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      have dv := Nest.arrows_static_ok hgv
      have sv : value = .atom "term" ∨ ∃ Z, value = .map Z ∧ Lynx.Term.mapLookup Z (.atom "dynamic") = none := by
        rcases dv with h | ⟨Z, h, sZ⟩
        · exact Or.inl h
        · exact Or.inr ⟨Z, h, sZ.static⟩
      have uv : Nest.upper value = value := Nest.upper_tc dv
      have lv : Nest.lower value = value := by
        rcases sv with rfl | ⟨Z, rfl, sZ⟩
        · rfl
        · simp [Nest.lower, Nest.rmDyn_static sZ]
      have gV : Nest.GC (Nest.level node d) value := Nest.GC.tc dv
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by simp [Erlang.erlang.«>=/2», Int.isGE_compare] at hi0; omega⟩
      rcases gT.shape with rfl | ⟨X, rfl⟩
      · simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Elixir.Module.Types.Descr.«tuple_delete_at/2»,
          Erlang.erlang.«is_map/1», Erlang.erlang.«==/2», Lynx.Except.tryWith, Lynx.Except.orElse,
          Erlang.erlang.«is_integer/1», Lynx.Except.andAlso] at hmap
      -- The insert into the gradual type.
      obtain ⟨R, run⟩ : ∃ R, Elixir.Module.Types.Descr.«tuple_replace_at/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value = .ok (.map R) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) value with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨R₁, hd, hi'⟩ := Nest.rep_split gT i value hm run
      obtain ⟨gR₁, -, -, sR₁, -⟩ := Nest.del_pts gT i hm hd
      obtain ⟨gR, -, sR⟩ := Nest.ins_at gR₁ gV (by rw [lv]; exact dv) (by rw [uv]; exact dv) i hm hi'
      have sR := sR uv
      -- The replace in the lower bound.
      rw [Nest.lower_bound_run (Or.inr ⟨X, rfl⟩)] at hmapL
      simp only [Lynx.Except.ok_bind, Nest.lower] at hmapL
      obtain ⟨R₂, run₂⟩ : ∃ R₂, Elixir.Module.Types.Descr.«tuple_replace_at/3»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map (Nest.rmDyn X)) (.integer i) value =
          .ok (.map R₂) := by
        cases h : Elixir.Module.Types.Descr.«tuple_replace_at/3»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map (Nest.rmDyn X)) (.integer i) value with
        | error _ => rw [h] at hmapL; cases hmapL
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapL
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapL
          exact ⟨_, rfl⟩
      obtain ⟨-, dR₂, oR₂, tR₂⟩ := Nest.rep_static dTl i (Or.inl dv) sv (by omega) run₂
      have same : ∀ q : Nest.PN node (d + 1), Nest.denD (Nest.lower (.map R)) q ↔ Nest.denD (.map R₂) q := fun q => by
        rw [Nest.lower, Nest.denD_rmDyn, sR, Nest.inSat oR₂ tR₂]
        refine Nest.insAt_congr fun u => ?_
        rw [← Nest.denD_tpt, Nest.denD_rmDyn, sR₁]
      have eq := Nest.elem_equal (Nest.ef_next node (d + 1)) gR.low_tc dR₂ same (m := δ + 100) (by omega)
      simp only [Lynx.apply_eq, «tuple_replace_lower:ensures/5»]
      rw [Nest.lower_bound_run (Or.inr ⟨X, rfl⟩)]
      simp [Nest.lower, run, run₂, Nest.lower_bound_run (Or.inr ⟨R, rfl⟩), Lynx.Term.true]
      exact eq
      """

    law tuple_delete_upper(tuple, index, depth, node),
      requires:
        arrows_gradual?(tuple, {depth + 1, node}) and depth?(depth) and is_integer(index) and
          index >= 0 and is_map(Descr.tuple_delete_at(tuple, index)) and
          is_map(Descr.tuple_delete_at(Descr.upper_bound(tuple), index)),
      expects:
        Descr.equal?(
          Descr.upper_bound(Descr.tuple_delete_at(tuple, index)),
          Descr.tuple_delete_at(Descr.upper_bound(tuple), index)
        ),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_delete_upper:requires/4», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_delete_upper:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hg, -⟩, hi⟩, hi0⟩, hmap⟩, hmapU⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) tuple
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gT, -, dTu⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by simp [Erlang.erlang.«>=/2», Int.isGE_compare] at hi0; omega⟩
      rcases gT.shape with rfl | ⟨X, rfl⟩
      · rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmap
        simp [Erlang.erlang.«is_map/1»] at hmap
      -- The delete from the gradual type.
      obtain ⟨R, run⟩ : ∃ R, Elixir.Module.Types.Descr.«tuple_delete_at/2»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) = .ok (.map R) := by
        cases h : Elixir.Module.Types.Descr.«tuple_delete_at/2»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨gR, -, uR, -, -⟩ := Nest.del_pts gT i hm run
      -- The delete from the upper bound.
      rw [Nest.upper_bound_run gT.ub] at hmapU
      simp only [Lynx.Except.ok_bind] at hmapU
      obtain ⟨U, eU, dU⟩ : ∃ U, Nest.upper (.map X) = .map U ∧ Nest.DE (Nest.level node (d + 1)).E (.map U) := by
        rcases dTu with h | ⟨U, h, sU⟩
        · rw [h, Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmapU
          simp [Erlang.erlang.«is_map/1»] at hmapU
        · exact ⟨U, h, Or.inr ⟨U, rfl, sU⟩⟩
      rw [eU] at hmapU
      obtain ⟨R₂, run₂⟩ : ∃ R₂, Elixir.Module.Types.Descr.«tuple_delete_at/2»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map U) (.integer i) = .ok (.map R₂) := by
        cases h : Elixir.Module.Types.Descr.«tuple_delete_at/2»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map U) (.integer i) with
        | error _ => rw [h] at hmapU; cases hmapU
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapU
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapU
          exact ⟨_, rfl⟩
      obtain ⟨-, long, dR₂, oR₂, tR₂⟩ := Nest.del_static_pts dU i (by omega) run₂
      have same : ∀ q : Nest.PN node (d + 1), Nest.denD (Nest.upper (.map R)) q ↔ Nest.denD (.map R₂) q := fun q => by
        rw [uR, Nest.tdelSat oR₂ tR₂, eU]
        refine Nest.tdelAt_congr fun u => ?_
        rw [Nest.denD_tpt]
        constructor
        · rintro (⟨h, -⟩ | h)
          · exact h
          · have := gT.inv _ ((Nest.denD_rmDyn X _).mp ((Nest.denD_tpt u).mpr h))
            rw [eU, Nest.denD_tpt] at this
            exact this
        · intro h; exact Or.inl ⟨h, long u h⟩
      have eq := Nest.elem_equal (Nest.ef_next node (d + 1)) gR.up_tc dR₂ same (m := δ + 100) (by omega)
      simp only [Lynx.apply_eq, «tuple_delete_upper:ensures/4»]
      rw [Nest.upper_bound_run gT.ub, eU]
      simp [run, run₂, Nest.upper_bound_run gR.ub, eq, Lynx.Term.true]
      """

    law tuple_delete_lower(tuple, index, depth, node),
      requires:
        arrows_gradual?(tuple, {depth + 1, node}) and depth?(depth) and is_integer(index) and
          index >= 0 and is_map(Descr.tuple_delete_at(tuple, index)) and
          is_map(Descr.tuple_delete_at(Descr.lower_bound(tuple), index)),
      expects:
        Descr.equal?(
          Descr.lower_bound(Descr.tuple_delete_at(tuple, index)),
          Descr.tuple_delete_at(Descr.lower_bound(tuple), index)
        ),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_delete_lower:requires/4», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_delete_lower:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hg, -⟩, hi⟩, hi0⟩, hmap⟩, hmapL⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) tuple
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gT, dTl, -⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      obtain ⟨z, rfl⟩ : ∃ z : Int, index = .integer z := by
        cases index <;> simp [Erlang.erlang.«is_integer/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨i, rfl⟩ : ∃ i : Nat, z = i := ⟨z.toNat, by simp [Erlang.erlang.«>=/2», Int.isGE_compare] at hi0; omega⟩
      rcases gT.shape with rfl | ⟨X, rfl⟩
      · rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at hmap
        simp [Erlang.erlang.«is_map/1»] at hmap
      -- The delete from the gradual type.
      obtain ⟨R, run⟩ : ∃ R, Elixir.Module.Types.Descr.«tuple_delete_at/2»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) = .ok (.map R) := by
        cases h : Elixir.Module.Types.Descr.«tuple_delete_at/2»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) (.integer i) with
        | error _ => rw [h] at hmap; cases hmap
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmap
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmap
          exact ⟨_, rfl⟩
      obtain ⟨gR, sR, -, -, -⟩ := Nest.del_pts gT i hm run
      -- The delete from the lower bound.
      rw [Nest.lower_bound_run (Or.inr ⟨X, rfl⟩)] at hmapL
      simp only [Lynx.Except.ok_bind, Nest.lower] at hmapL
      obtain ⟨R₂, run₂⟩ : ∃ R₂, Elixir.Module.Types.Descr.«tuple_delete_at/2»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map (Nest.rmDyn X)) (.integer i) = .ok (.map R₂) := by
        cases h : Elixir.Module.Types.Descr.«tuple_delete_at/2»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map (Nest.rmDyn X)) (.integer i) with
        | error _ => rw [h] at hmapL; cases hmapL
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hmapL
          cases r <;> simp [Erlang.erlang.«is_map/1»] at hmapL
          exact ⟨_, rfl⟩
      obtain ⟨-, -, dR₂, oR₂, tR₂⟩ := Nest.del_static_pts dTl i (by omega) run₂
      have same : ∀ q : Nest.PN node (d + 1), Nest.denD (Nest.lower (.map R)) q ↔ Nest.denD (.map R₂) q := fun q => by
        rw [Nest.lower, Nest.denD_rmDyn, sR, Nest.tdelSat oR₂ tR₂]
      have eq := Nest.elem_equal (Nest.ef_next node (d + 1)) gR.low_tc dR₂ same (m := δ + 100) (by omega)
      simp only [Lynx.apply_eq, «tuple_delete_lower:ensures/4»]
      rw [Nest.lower_bound_run (Or.inr ⟨X, rfl⟩)]
      simp [Nest.lower, run, run₂, Nest.lower_bound_run (Or.inr ⟨R, rfl⟩), Lynx.Term.true]
      exact eq
      """

    law tuple_values_upper(tuple, depth, node),
      requires:
        arrows_gradual?(tuple, {depth + 1, node}) and depth?(depth) and Descr.tuple_values(tuple) != :badtuple and
          Descr.tuple_values(Descr.upper_bound(tuple)) != :badtuple,
      expects: Descr.equal?(Descr.upper_bound(Descr.tuple_values(tuple)), Descr.tuple_values(Descr.upper_bound(tuple))),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_values_upper:requires/3», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_values_upper:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨hg, -⟩, hv⟩, hvU⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) tuple
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gT, -, dTu⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      rcases gT.shape with rfl | ⟨X, rfl⟩
      · simp [Elixir.Module.Types.Descr.«tuple_values/1», Erlang.erlang.«/=/2»] at hv
      -- The values of the gradual type.
      obtain ⟨r, run, nb⟩ : ∃ r, Elixir.Module.Types.Descr.«tuple_values/1»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) = .ok r ∧ r ≠ .atom "badtuple" := by
        cases h : Elixir.Module.Types.Descr.«tuple_values/1»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) with
        | error _ => rw [h] at hv; cases hv
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hv
          refine ⟨r, rfl, fun e => ?_⟩
          subst e; simp [Erlang.erlang.«/=/2»] at hv
      -- The values of the upper bound.
      rw [Nest.upper_bound_run gT.ub] at hvU
      simp only [Lynx.Except.ok_bind] at hvU
      obtain ⟨U, eU, dU⟩ : ∃ U, Nest.upper (.map X) = .map U ∧ Nest.DE (Nest.level node (d + 1)).E (.map U) := by
        rcases dTu with h | ⟨U, h, sU⟩
        · rw [h] at hvU
          simp [Elixir.Module.Types.Descr.«tuple_values/1», Erlang.erlang.«/=/2»] at hvU
        · exact ⟨U, h, Or.inr ⟨U, rfl, sU⟩⟩
      rw [eU] at hvU
      obtain ⟨r₂, run₂, nb₂⟩ : ∃ r₂, Elixir.Module.Types.Descr.«tuple_values/1»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map U) = .ok r₂ ∧ r₂ ≠ .atom "badtuple" := by
        cases h : Elixir.Module.Types.Descr.«tuple_values/1»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map U) with
        | error _ => rw [h] at hvU; cases hvU
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hvU
          refine ⟨r, rfl, fun e => ?_⟩
          subst e; simp [Erlang.erlang.«/=/2»] at hvU
      obtain ⟨e₂, s₂⟩ := Nest.vals_static dU (by omega) run₂ nb₂
      have ef := (Nest.level node (d + 1)).ef
      cases hD : Lynx.Term.mapLookup X (.atom "dynamic") with
      | none =>
        -- A static type: its values are their own upper bound.
        have eX : U = X := by
          have : Nest.upper (.map X) = .map X := by simp [Nest.upper, hD]
          rw [this] at eU; cases eU; rfl
        subst eX
        rw [run] at run₂; cases run₂
        obtain ⟨c, hc, sc, ub, -, -, -⟩ := Nest.el_ops e₂ (δ + 99)
        have eq := Nest.elem_equal ef (Nest.e_succ hc) e₂ (fun v => (Nest.den_succ hc v).trans (sc v).symm)
          (m := δ + 100) (by omega)
        simp only [Lynx.apply_eq, «tuple_values_upper:ensures/3»]
        rw [Nest.upper_bound_run gT.ub, eU]
        simp [run, ub, eq, Lynx.Term.true]
      | some Dy =>
        obtain ⟨gR, -, uR⟩ := Nest.vals_grad gT hD (by omega) run nb
        have eD : Dy = .map U := by
          have : Nest.upper (.map X) = Dy := by simp [Nest.upper, hD]
          rw [this] at eU; exact eU
        subst eD
        obtain ⟨eu, -, su, -⟩ := Nest.gc_el gR
        have eq := Nest.elem_equal ef eu e₂ (fun v => (su v).trans ((uR v).trans
          (by simp only [Nest.denD_tpt]; exact (s₂ v).symm))) (m := δ + 100) (by omega)
        simp only [Lynx.apply_eq, «tuple_values_upper:ensures/3»]
        rw [Nest.upper_bound_run gT.ub, eU]
        simp [run, run₂, Nest.upper_bound_run gR.ub, eq, Lynx.Term.true]
      """

    law tuple_values_lower(tuple, depth, node),
      requires:
        arrows_gradual?(tuple, {depth + 1, node}) and depth?(depth) and Descr.tuple_values(tuple) != :badtuple and
          Descr.tuple_values(Descr.lower_bound(tuple)) != :badtuple,
      expects: Descr.equal?(Descr.lower_bound(Descr.tuple_values(tuple)), Descr.tuple_values(Descr.lower_bound(tuple))),
      proof: ~LEAN"""
      -- The tuples nest at most `d + 1` levels.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «tuple_values_lower:requires/3», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «tuple_values_lower:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨hg, -⟩, hv⟩, hvU⟩ := requires
      have hm : (Nest.level node (d + 1)).K + 26 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hg : «arrows_gradual?/2» (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) tuple
          (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by simpa using hg
      obtain ⟨gT, -, dTu⟩ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := δ + 100) (by omega) hg
      rcases gT.shape with rfl | ⟨X, rfl⟩
      · simp [Elixir.Module.Types.Descr.«tuple_values/1», Erlang.erlang.«/=/2»] at hv
      -- The values of the gradual type.
      obtain ⟨r, run, nb⟩ : ∃ r, Elixir.Module.Types.Descr.«tuple_values/1»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) = .ok r ∧ r ≠ .atom "badtuple" := by
        cases h : Elixir.Module.Types.Descr.«tuple_values/1»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map X) with
        | error _ => rw [h] at hv; cases hv
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hv
          refine ⟨r, rfl, fun e => ?_⟩
          subst e; simp [Erlang.erlang.«/=/2»] at hv
      -- The values of the lower bound.
      rw [Nest.lower_bound_run (Or.inr ⟨X, rfl⟩)] at hvU
      simp only [Lynx.Except.ok_bind, Nest.lower] at hvU
      have dS : Nest.DE (Nest.level node (d + 1)).E (.map (Nest.rmDyn X)) := Nest.GC.low_tc gT
      obtain ⟨r₂, run₂, nb₂⟩ : ∃ r₂, Elixir.Module.Types.Descr.«tuple_values/1»
          (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map (Nest.rmDyn X)) = .ok r₂ ∧
            r₂ ≠ .atom "badtuple" := by
        cases h : Elixir.Module.Types.Descr.«tuple_values/1»
            (Lynx.Dispatcher.ofTable Erlang.program.fun_table (δ + 100)) (.map (Nest.rmDyn X)) with
        | error _ => rw [h] at hvU; cases hvU
        | ok r =>
          rw [h, Lynx.Except.ok_bind] at hvU
          refine ⟨r, rfl, fun e => ?_⟩
          subst e; simp [Erlang.erlang.«/=/2»] at hvU
      obtain ⟨e₂, s₂⟩ := Nest.vals_static dS (by omega) run₂ nb₂
      have ef := (Nest.level node (d + 1)).ef
      cases hD : Lynx.Term.mapLookup X (.atom "dynamic") with
      | none =>
        -- A static type: its values are their own lower bound.
        have eX : Nest.rmDyn X = X := Nest.rmDyn_static hD
        rw [eX] at run₂
        rw [run] at run₂; cases run₂
        obtain ⟨c, hc, sc, -, lb, -, -⟩ := Nest.el_ops e₂ (δ + 99)
        have eq := Nest.elem_equal ef (Nest.e_succ hc) e₂ (fun v => (Nest.den_succ hc v).trans (sc v).symm)
          (m := δ + 100) (by omega)
        simp only [Lynx.apply_eq, «tuple_values_lower:ensures/3»]
        rw [Nest.lower_bound_run (Or.inr ⟨X, rfl⟩)]
        simp [Nest.lower, eX, run, lb, eq, Lynx.Term.true]
      | some Dy =>
        obtain ⟨gR, sR, -⟩ := Nest.vals_grad gT hD (by omega) run nb
        obtain ⟨-, el, -, sl⟩ := Nest.gc_el gR
        have eq := Nest.elem_equal ef el e₂ (fun v => (sl v).trans ((sR v).trans (s₂ v).symm)) (m := δ + 100) (by omega)
        simp only [Lynx.apply_eq, «tuple_values_lower:ensures/3»]
        rw [Nest.lower_bound_run (Or.inr ⟨X, rfl⟩)]
        simp only [Nest.lower, run, run₂, Lynx.Except.ok_bind, Nest.lower_bound_run gR.shape]
        simpa [Nest.lower, Lynx.Term.true] using eq
      """

    law map_get_fetch_key(map, key, depth, node),
      requires: arrows_static?(map, {depth, node}) and depth?(depth) and is_atom(key),
      expects:
        (case {Descr.map_get(map, Descr.atom([key])), Descr.map_fetch_key(map, key)} do
           {{:ok, got}, {_, fetched}} -> Descr.equal?(got, fetched)
           {{:ok, _}, :badkey} -> not Descr.subtype?(map, Descr.open_map([{key, {Descr.term(), false}}]))
           {:error, :badkey} -> true
           {:badmap, :badmap} -> true
           _ -> false
         end),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      simp only [«map_get_fetch_key:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨hs, hd⟩, hi⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d) [.atom a] [] (by simp) (by simp)
        (m := δ + 100) (by omega)
      have rA : Elixir.Module.Types.Descr.«atom/1» (Lynx.Term.list [.atom a]) = .ok (.map Y) := by
        cases h : Elixir.Module.Types.Descr.«atom/1» (Lynx.Term.list [.atom a]) with
        | error e => simp [«key_type/2», Lynx.Term.list, h] at rY
        | ok r =>
          simp only [Lynx.Term.list] at h
          simp [«key_type/2», «kinds_type/2», Lynx.Term.list, h] at rY
          rw [rY]
      have keyA : ∀ κ, Nest.SplitKey rs neg ds κ ↔ κ = .atom a := fun κ => by
        rw [sk]
        cases κ with
        | atom s => simp [Nest.KeysOf]
        | dom k i => simp [Nest.KeysOf]
      have hterm : (Nest.level node d).E (.atom "term") := (Nest.level node d).ef.term
      obtain ⟨k, rom, key⟩ := Nest.open_map_run a ((Nest.level node d).ef.static hterm) (δ + 99)
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · simp only [Lynx.apply_eq, «map_get_fetch_key:ensures/4»]
        simp [rA, Nest.get_map_term, Nest.fetch_map_term, Lynx.Term.true]
      obtain ⟨gres, grun, ⟨rfl, gnon⟩ | ⟨rfl, gonly, gnone⟩ | ⟨T, rfl, hT, gonly, -, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      all_goals obtain ⟨fres, frun, ⟨rfl, fnon⟩ | ⟨rfl, fonly, w₀, hw₀, wa⟩ | ⟨e, rfl, he, fonly, s₁, s₂⟩⟩ :=
        Nest.fetch_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) a (m := δ + 100) hm
      all_goals simp only [Lynx.apply_eq, «map_get_fetch_key:ensures/4»]
      · simp [rA, grun, frun, Lynx.Term.true]
      · exact absurd fonly gnon
      · exact absurd fonly gnon
      · exact absurd gonly fnon
      · simp [rA, grun, frun, Lynx.Term.true]
      · obtain ⟨w, hw⟩ := gonly.2
        obtain ⟨x, hx, -⟩ := s₁ w hw
        rw [gnone w hw _ ((keyA _).mpr rfl)] at hx; cases hx
      · exact absurd gonly fnon
      · -- An optional key: some map lacks it.
        have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩)
          (Nest.mfused_de (Nest.mleaf_field (Or.inl rfl) (Nest.fieldsV_req hterm) key)) (m := δ + 100) (by omega)
        rw [Nest.bp_false.mpr fun h => by
          have := h _ ((Nest.denD_mpt w₀).mpr hw₀)
          rw [Nest.denD_mpt, Nest.mt_open_at hterm a k] at this
          obtain ⟨x, wa', -⟩ := this
          rw [wa] at wa'; cases wa'] at sub
        simp [rA, grun, frun, Elixir.Module.Types.Descr.«term/0», rom, sub, Erlang.erlang.«not/1», Lynx.Term.true]
      · have sem : ∀ x, (Nest.level node d).den T x ↔ (Nest.level node d).den e x := fun x => by
          rw [sT]
          constructor
          · rintro ⟨w, hw, κ, hκ, wκ⟩
            obtain rfl := (keyA κ).mp hκ
            obtain ⟨x', wa, hx'⟩ := s₁ w hw
            rw [wκ] at wa; cases wa; exact hx'
          · intro hx
            obtain ⟨w, hw, wa⟩ := s₂ x hx
            exact ⟨w, hw, .atom a, (keyA _).mpr rfl, wa⟩
        simp [rA, grun, frun, Nest.elem_equal (Nest.level node d).ef hT he sem (m := δ + 100)
          (by rw [Nest.level_K] at hm ⊢; omega), Lynx.Term.true]
      """

    law map_get_sound(map, atoms, kinds, depth, node),
      requires:
        arrows_static?(map, {depth, node}) and depth?(depth) and keys?(atoms, kinds) and
          match?({:ok, _}, Descr.map_get(map, key_type(atoms, kinds))),
      expects: Descr.subtype?(map, keys_hold(atoms, kinds, elem(Descr.map_get(map, key_type(atoms, kinds)), 1))),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the precondition from its
      -- own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_get_sound:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_get_sound:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨hs, -⟩, hk⟩, hg⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨as, ks, rfl, rfl, ha, hks⟩ := Nest.keys_ok hk
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d) as ks ha hks (m := δ + 100) (by omega)
      rw [rY, Lynx.Except.ok_bind] at hg
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.get_map_term] at hg; simp at hg
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨T, rfl, hT, only, -, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      obtain ⟨H, rH, dH, -, sH⟩ := Nest.keys_hold_run (t := node) (n := d) as ks ha hks
        ((Nest.level node d).ef.static hT) hT (m := δ + 100) (by omega)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) dH (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (show Nest.SubN node d (.map X) H from fun p hp => by
        obtain ⟨w, hw⟩ := Nest.pt_map p (only.1 p hp)
        rw [sH p w hw]
        intro κ hκ
        cases e : w κ with
        | none => exact Or.inl rfl
        | some x => exact Or.inr ⟨x, rfl, (sT x).mpr ⟨w, (hw X).mp hp, κ, (sk κ).mpr hκ, e⟩⟩)] at sub
      simp only [Lynx.apply_eq, «map_get_sound:ensures/5»]
      simp [rY, run, Erlang.erlang.«element/2», rH, sub, Lynx.Term.true]
      """

    law map_get_least(map, atoms, kinds, value, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and arrows_static?(value, {depth, node}) and depth?(depth) and
          keys?(atoms, kinds) and match?({:ok, _}, Descr.map_get(map, key_type(atoms, kinds))) and
          Descr.subtype?(map, keys_hold(atoms, kinds, value)),
      expects: Descr.subtype?(elem(Descr.map_get(map, key_type(atoms, kinds)), 1), value),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and the value `d`, so the proofs run from the bound of level `d + 1` on, and
      -- the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_get_least:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_get_least:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hs, hel⟩, -⟩, hk⟩, hg⟩, hsub⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 1)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dv := Nest.arrows_static_ok hel
      have del : (Nest.level node (d + 1)).E value := Or.inl dv
      obtain ⟨as, ks, rfl, rfl, ha, hks⟩ := Nest.keys_ok hk
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d + 1) as ks ha hks (m := δ + 100)
        (by omega)
      rw [rY, Lynx.Except.ok_bind] at hg
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.get_map_term] at hg; simp at hg
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨T, rfl, hT, only, -, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      obtain ⟨H, rH, dH, -, sH⟩ := Nest.keys_hold_run (t := node) (n := d + 1) as ks ha hks
        ((Nest.level node (d + 1)).ef.static del) del (m := δ + 100) (by omega)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) dH (m := δ + 100) (by omega)
      rw [rH, Lynx.Except.ok_bind, sub, Except.ok.injEq] at hsub
      have incl := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hsub)
      have sem : ∀ x, (Nest.level node (d + 1)).den T x → (Nest.level node (d + 1)).den value x := by
        intro x hx
        obtain ⟨w, hw, κ, hκ, wκ⟩ := (sT x).mp hx
        have := (sH _ w (Nest.mapOf_mpt w)).mp (incl _ ((Nest.denD_mpt w).mpr hw)) κ ((sk κ).mp hκ)
        rw [wκ] at this
        rcases this with h | ⟨x', e, h⟩
        · cases h
        · cases e; exact h
      simp only [Lynx.apply_eq, «map_get_least:ensures/6»]
      simp [rY, run, Erlang.erlang.«element/2»,
        (Nest.level node (d + 1)).ef.subc hT del sem (δ + 100) (by rw [Nest.level_K]; omega), Lynx.Term.true]
      """

    law map_get_error(map, atoms, kinds, depth, node),
      requires:
        arrows_static?(map, {depth, node}) and depth?(depth) and keys?(atoms, kinds) and
          Descr.subtype?(map, Descr.open_map()) and not Descr.empty?(map),
      expects:
        (Descr.map_get(map, key_type(atoms, kinds)) == :error) ==
          Descr.subtype?(map, keys_hold(atoms, kinds, Descr.none())),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on, and the precondition from its
      -- own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_get_error:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * d), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_get_error:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨⟨⟨hs, -⟩, hk⟩, hmap⟩, hne⟩ := requires
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dt := Nest.arrows_static_ok hs
      have sT := Nest.next_sub dt Nest.mapTop_de (m := δ + 100) (by omega)
      rw [show Elixir.Module.Types.Descr.«open_map/0» =
        .ok (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) from rfl, Lynx.Except.ok_bind, sT,
        Except.ok.injEq] at hmap
      have onlyM := Nest.bp_true.mp (Nest.boolAtom_inj (q := Bool.true) hmap)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · have := (Nest.mapTop_den Nest.bitPt).mp (onlyM Nest.bitPt (Nest.denD_term _))
        simp [Nest.bitPt] at this
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      rw [ne] at hne
      have ex : ∃ v : Nest.PN node d, Nest.denD (.map X) v := by
        cases h : Nest.bp (∀ v : Nest.PN node d, ¬Nest.denD (.map X) v)
        · exact Classical.byContradiction fun none => by
            have := Nest.bp_true.mpr fun v hv => none ⟨v, hv⟩
            rw [h] at this; cases this
        · rw [h] at hne; simp [Erlang.erlang.«not/1»] at hne
      have only : Nest.MOnly node d X := by
        refine ⟨fun v hv => (Nest.mapTop_den v).mp (onlyM v hv), ?_⟩
        obtain ⟨v, hv⟩ := ex
        obtain ⟨w, hw⟩ := Nest.pt_map v ((Nest.mapTop_den v).mp (onlyM v hv))
        exact ⟨w, (hw X).mp hv⟩
      obtain ⟨as, ks, rfl, rfl, ha, hks⟩ := Nest.keys_ok hk
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d) as ks ha hks (m := δ + 100) (by omega)
      have hn := (Nest.level node d).ef.none
      obtain ⟨H, rH, dH, -, sH⟩ := Nest.keys_hold_run (t := node) (n := d) as ks ha hks
        ((Nest.level node d).ef.static hn) hn (m := δ + 100) (by omega)
      have sub := Nest.next_sub (Or.inr ⟨X, rfl, sX⟩) dH (m := δ + 100) (by omega)
      obtain ⟨res, run, ⟨rfl, nonly⟩ | ⟨rfl, -, none⟩ | ⟨T, rfl, -, -, ⟨x, hx⟩, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      · exact absurd only nonly
      · rw [Nest.bp_true.mpr (show Nest.SubN node d (.map X) H from fun p hp => by
          obtain ⟨w, hw⟩ := Nest.pt_map p (only.1 p hp)
          rw [sH p w hw]
          exact fun κ hκ => Or.inl (none w ((hw X).mp hp) κ ((sk κ).mpr hκ)))] at sub
        simp only [Lynx.apply_eq, «map_get_error:ensures/5»]
        simp [rY, run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«none/0», rH, sub, Lynx.Term.true]
      · obtain ⟨w, hw, κ, hκ, wκ⟩ := (sT x).mp hx
        rw [Nest.bp_false.mpr fun h => by
          have := (sH _ w (Nest.mapOf_mpt w)).mp (h _ ((Nest.denD_mpt w).mpr hw)) κ ((sk κ).mp hκ)
          rw [wκ] at this
          rcases this with h' | ⟨x', e, h'⟩
          · cases h'
          · exact (Nest.level node d).ef.den_none x' h'] at sub
        simp only [Lynx.apply_eq, «map_get_error:ensures/5»]
        simp [rY, run, Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«none/0», rH, sub, Lynx.Term.true]
      """

    law map_get_badmap(map, atoms, kinds, depth, node),
      requires: arrows_static?(map, {depth, node}) and depth?(depth) and keys?(atoms, kinds),
      expects:
        (Descr.map_get(map, key_type(atoms, kinds)) == :badmap) ==
          not (Descr.subtype?(map, Descr.open_map()) and not Descr.empty?(map)),
      proof: ~LEAN"""
      -- The types nest at most `d` levels, so the proofs run from the bound of level `d` on.
      simp only [«map_get_badmap:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨⟨hs, hd⟩, hk⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      refine ⟨100 + 24 * d, fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have hm : (Nest.level node d).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨as, ks, rfl, rfl, ha, hks⟩ := Nest.keys_ok hk
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, -⟩ := Nest.key_split (t := node) (n := d) as ks ha hks (m := δ + 100) (by omega)
      have dt := Nest.arrows_static_ok hs
      have top : Elixir.Module.Types.Descr.«open_map/0» =
          .ok (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) := rfl
      have sT := Nest.next_sub dt Nest.mapTop_de (m := δ + 100) (by omega)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.bp_false.mpr fun h => by
          have := (Nest.mapTop_den Nest.bitPt).mp (h Nest.bitPt (Nest.denD_term _))
          simp [Nest.bitPt] at this] at sT
        simp only [Lynx.apply_eq, «map_get_badmap:ensures/5»]
        simp [rY, Nest.get_map_term, Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      obtain ⟨res, run, ⟨rfl, nonly⟩ | ⟨rfl, only, -⟩ | ⟨T, rfl, -, only, -⟩⟩ :=
        Nest.get_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) ok hm rS
      · rw [Nest.monly_iff] at nonly
        simp only [Lynx.apply_eq, «map_get_badmap:ensures/5»]
        by_cases h : Nest.SubN node d (.map X) (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])])
        · rw [Nest.bp_true.mpr h] at sT
          rw [Nest.bp_true.mpr (Classical.not_not.mp fun h' => nonly ⟨h, h'⟩)] at ne
          simp [rY, run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
        · rw [Nest.bp_false.mpr h] at sT
          simp [rY, run, Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      all_goals
        obtain ⟨h₁, h₂⟩ := Nest.monly_iff.mp only
        rw [Nest.bp_true.mpr h₁] at sT
        rw [Nest.bp_false.mpr h₂] at ne
        simp only [Lynx.apply_eq, «map_get_badmap:ensures/5»]
        simp [rY, run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
      """
    law map_to_list_atom(map, key, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and is_atom(key) and
          match?({:ok, _}, Descr.map_to_list(map)) and match?({:ok, _}, Descr.map_get(map, Descr.atom([key]))),
      expects:
        Descr.subtype?(
          Descr.non_empty_list(Descr.tuple([Descr.atom([key]), elem(Descr.map_get(map, Descr.atom([key])), 1)])),
          elem(Descr.map_to_list(map), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_atom:requires/4», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_atom:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨hs, -⟩, hi⟩, hl⟩, hg⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨a, rfl⟩ : ∃ a : String, key = .atom a := by
        cases key <;> simp [Erlang.erlang.«is_atom/1»] at hi
        exact ⟨_, rfl⟩
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d + 1) [.atom a] [] (by simp) (by simp)
        (m := δ + 100) (by rw [Nest.level_K]; omega)
      have eY : Nest.atomT a = .map Y := by
        have := Nest.atom_one a
        simp only [Lynx.Term.list] at this
        simpa [«key_type/2», «kinds_type/2», Lynx.Term.list, this] using rY
      rw [Nest.atom_one, eY, Lynx.Except.ok_bind] at hg
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -, -⟩ | ⟨T, rfl, hT, -, ⟨x₀, hx₀⟩, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok (by omega) rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      have keyA : ∀ κ, Nest.SplitKey rs neg ds κ ↔ κ = .atom a := fun κ => by
        rw [sk]
        cases κ with
        | atom s => simp [Nest.KeysOf]
        | dom k i => simp [Nest.KeysOf]
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨-, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      obtain ⟨P, rP, dP, sP⟩ := Nest.pair_run (t := node) (n := d + 1) (Or.inl (Nest.atomT_de a)) hT (Nest.atomT_static a)
        ((Nest.level node (d + 1)).ef.static hT)
      have incl : ∀ y : Nest.PN node (d + 1), Nest.denD P y → Nest.denD inner y := by
        intro y hy
        obtain ⟨w', hw', k, x, rfl, hk, hx⟩ := (sP y).mp hy
        obtain ⟨w, hw, κ, hκ, wκ⟩ := (sT x).mp hx
        obtain rfl := (keyA κ).mp hκ
        exact (Nest.same_tuple dI hw').mpr (sI.1 w ((mt w).mp hw) a x wκ k hk)
      obtain ⟨k', rlist, rnel⟩ := Nest.list_run ((Nest.ef_next node (d + 1)).static dP) (δ + 100)
      have one := Nest.atom_one a
      simp only [Lynx.Term.list] at one
      rcases hL with ⟨rfl, emp⟩ | ⟨nil, k, rfl, -⟩
      · exfalso
        have k₀ : (Nest.level node (d + 1)).den (Nest.atomT a) (Nest.aPt (t := node) (n := d) (.atom a)) :=
          (Nest.den_succ (Nest.atomT_de a) _).mpr ((Nest.atomT_den a _).mpr ⟨rfl, rfl⟩)
        exact emp _ (incl _ ((sP _).mpr (Nest.pairPt_tpt k₀ hx₀)))
      have sub := Nest.next_sub (t := node) (n := d + 2) (Nest.lTy_de Bool.false k' dP) (Nest.lTy_de nil k dI)
        (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (Nest.nel_sub dP dI incl nil k k')] at sub
      simp only [Lynx.apply_eq, «map_to_list_atom:ensures/4»]
      rw [eY] at rP
      have e : Nest.lTy Bool.false k' P = .map [(.atom "list", .tuple #[.integer k', P, Nest.nilT])] := rfl
      rw [e] at sub
      simp [one, eY, run, Erlang.erlang.«element/2», rP, rnel, Nest.tolist_one, runL, sub, Lynx.Term.true]
      """

    law map_to_list_kind(map, kind, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and keys?([], [kind]) and kind != :atom and
          match?({:ok, _}, Descr.map_to_list(map)) and match?({:ok, _}, Descr.map_get(map, key_type([], [kind]))),
      expects:
        Descr.subtype?(
          Descr.non_empty_list(Descr.tuple([key_type([], [kind]), elem(Descr.map_get(map, key_type([], [kind])), 1)])),
          elem(Descr.map_to_list(map), 1)
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_kind:requires/4», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_kind:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hs, -⟩, hk⟩, hne⟩, hl⟩, hg⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      obtain ⟨as, ks, eas, eks, -, hks⟩ := Nest.keys_ok hk
      have eas := list_inj (l := []) eas
      subst eas
      have eks := list_inj eks
      subst eks
      obtain ⟨kd, mkd, rfl⟩ := hks _ List.mem_cons_self
      have nkd : kd ≠ "atom" := fun e => by subst e; simp [Erlang.erlang.«/=/2»] at hne
      obtain ⟨Y, rs, neg, ds, rY, rS, ok, sk⟩ := Nest.key_split (t := node) (n := d + 1) [] [.atom kd] (by simp)
        (by simpa using mkd) (m := δ + 100) (by rw [Nest.level_K]; omega)
      obtain ⟨Y₁, rY₁, hY⟩ := Nest.key_type_run (t := node) (n := d) [] [.atom kd] (by simp) (by simpa using mkd)
        (m := δ + 100) (by rw [Nest.level_K]; omega)
      rw [rY] at rY₁
      cases rY₁
      have nil : Lynx.Term.nil = Lynx.Term.list [] := rfl
      rw [← nil] at rY
      rw [rY, Lynx.Except.ok_bind] at hg
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -, -⟩ | ⟨T, rfl, hT, -, ⟨x₀, hx₀⟩, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok (by omega) rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      have keyK : ∀ κ, Nest.SplitKey rs neg ds κ ↔ ∃ kk i, κ = .dom kk i ∧ Nest.domKind kk = kd := fun κ => by
        rw [sk]
        cases κ with
        | atom s => simp [Nest.KeysOf, Ne.symm nkd]
        | dom kk i => simp [Nest.KeysOf]
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨-, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      have kY : ∀ k : Nest.PN node d, Nest.denD (.map Y) k → Nest.ptKind k = kd := by
        intro k hk
        by_cases ka : k.1.1 = "atom"
        · have := (hY.atoms k.1.2.2.1).mp ((Nest.denD_atom_pt ka).mp hk)
          simp at this
          exact absurd this.symm nkd
        · simpa using hY.kinds k hk ka
      obtain ⟨P, rP, dP, sP⟩ := Nest.pair_run (t := node) (n := d + 1) (Or.inl hY.de) hT
        (Or.inr (Or.inl ⟨_, rfl, (Nest.de_map hY.de).static⟩)) ((Nest.level node (d + 1)).ef.static hT)
      have incl : ∀ y : Nest.PN node (d + 1), Nest.denD P y → Nest.denD inner y := by
        intro y hy
        obtain ⟨w', hw', k, x, rfl, hk, hx⟩ := (sP y).mp hy
        obtain ⟨w, hw, κ, hκ, wκ⟩ := (sT x).mp hx
        obtain ⟨kk, i, rfl, hkk⟩ := (keyK κ).mp hκ
        exact (Nest.same_tuple dI hw').mpr (sI.2.1 w ((mt w).mp hw) kk i x wκ k
          (by rw [hkk]; exact kY _ ((Nest.den_succ hY.de _).mp hk)))
      obtain ⟨k', rlist, rnel⟩ := Nest.list_run ((Nest.ef_next node (d + 1)).static dP) (δ + 100)
      rcases hL with ⟨rfl, emp⟩ | ⟨nil, k, rfl, -⟩
      · exfalso
        obtain ⟨v, hv, pv⟩ := hY.wit kd (by simp) nkd
        exact emp _ (incl _ ((sP _).mpr (Nest.pairPt_tpt ((Nest.den_succ hY.de v).mpr hv) hx₀)))
      have sub := Nest.next_sub (t := node) (n := d + 2) (Nest.lTy_de Bool.false k' dP) (Nest.lTy_de nil k dI)
        (m := δ + 100) (by omega)
      rw [Nest.bp_true.mpr (Nest.nel_sub dP dI incl nil k k')] at sub
      have e : Nest.lTy Bool.false k' P = .map [(.atom "list", .tuple #[.integer k', P, Nest.nilT])] := rfl
      rw [e] at sub
      simp only [Lynx.apply_eq, «map_to_list_kind:ensures/4»]
      simp [rY, run, Erlang.erlang.«element/2», rP, rnel, Nest.tolist_one, runL, sub, Lynx.Term.true]
      """

    law map_to_list_values(map, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and match?({:ok, _}, Descr.map_to_list(map)) and
          match?({:ok, _}, Descr.map_get(map, Descr.term())),
      expects:
        Descr.subtype?(
          elem(Descr.map_to_list(map), 1),
          Descr.list(Descr.tuple([Descr.term(), elem(Descr.map_get(map, Descr.term()), 1)]))
        ),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_values:requires/3», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_values:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨hs, -⟩, hl⟩, hg⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨only, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      -- The values of the pairs are values of the maps.
      have tm : Elixir.Module.Types.Descr.«term/0» = .ok (.atom "term") := rfl
      rw [tm, Lynx.Except.ok_bind] at hg
      obtain ⟨rs, neg, ds, rS, ok, allK⟩ := Nest.term_split (t := node) (n := d + 1) (m := δ + 99)
        (by rw [Nest.level_K]; omega)
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨rfl, -, -⟩ | ⟨T, rfl, hT, -, -, sT⟩⟩ :=
        Nest.get_map (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) ok (by omega) rS
      · rw [run] at hg; simp at hg
      · rw [run] at hg; simp at hg
      obtain ⟨P, rP, dP, sP⟩ := Nest.pair_run (t := node) (n := d + 1) (Nest.level node (d + 1)).ef.term hT (Or.inl rfl)
        ((Nest.level node (d + 1)).ef.static hT)
      have incl : ∀ y : Nest.PN node (d + 1), Nest.denD inner y → Nest.denD P y := by
        intro y hy
        obtain ⟨w', hw', k, x, rfl, w, hw, κ, wκ⟩ := sI.2.2 y hy
        exact (sP y).mpr ⟨[k, x], hw', k, x, rfl, (Nest.level node (d + 1)).ef.den_term k,
          (sT x).mpr ⟨w, (mt w).mpr hw, κ, allK κ, wκ⟩⟩
      obtain ⟨k', rlist, -⟩ := Nest.list_run ((Nest.ef_next node (d + 1)).static dP) (δ + 100)
      have e : Elixir.Module.Types.Descr.«list/1» (D (δ + 100)) P = .ok (Nest.lTy Bool.true k' P) := rlist
      have dQ := Nest.lTy_de Bool.true k' dP
      rcases hL with ⟨rfl, -⟩ | ⟨nil, k, rfl, -⟩
      · have sub := Nest.next_sub (t := node) (n := d + 2) Nest.nilT_de dQ (m := δ + 100) (by omega)
        rw [Nest.bp_true.mpr (Nest.nilT_sub_true dP k')] at sub
        simp only [Lynx.apply_eq, «map_to_list_values:ensures/3»]
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», tm, run, rP, e, sub, Lynx.Term.true]
      · have sub := Nest.next_sub (t := node) (n := d + 2) (Nest.lTy_de nil k dI) dQ (m := δ + 100) (by omega)
        rw [Nest.bp_true.mpr (Nest.lTy_mono dI dP incl (fun _ => rfl) k k')] at sub
        simp only [Lynx.apply_eq, «map_to_list_values:ensures/3»]
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», tm, run, rP, e, sub, Lynx.Term.true]
      """

    law map_to_list_empty(map, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and match?({:ok, _}, Descr.map_to_list(map)),
      expects:
        Descr.subtype?(elem(Descr.map_to_list(map), 1), Descr.empty_list()) ==
          Descr.subtype?(map, Descr.empty_map()),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_empty:requires/3», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_empty:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨hs, -⟩, hl⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨only, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      -- Maps of the type are all empty exactly when it lists no pairs.
      have subE := Nest.next_sub (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) Nest.emptyMap_de (m := δ + 100) (by omega)
      have allE : Nest.SubN node (d + 1) (.map X) Nest.emptyMapT ↔ ∀ p : Nest.PN node (d + 1), ¬Nest.denD inner p := by
        rw [Nest.inner_empty_iff sI]
        constructor
        · intro h w hw
          have := h _ ((Nest.denD_mpt w).mpr ((mt w).mpr hw))
          rwa [Nest.emptyMapT, Nest.denD_mpt, Nest.mt_emptyMap] at this
        · intro h q hq
          obtain ⟨w, hw⟩ := Nest.pt_map q (only.1 q hq)
          rw [Nest.emptyMapT, hw, Nest.mt_emptyMap]
          exact h w ((mt w).mp ((hw X).mp hq))
      rcases hL with ⟨rfl, emp⟩ | ⟨nil, k, rfl, -⟩
      · have subL := Nest.next_sub (t := node) (n := d + 2) Nest.nilT_de Nest.nilT_de (m := δ + 100) (by omega)
        rw [Nest.bp_true.mpr (show Nest.SubN node (d + 2) Nest.nilT Nest.nilT from fun q hq => hq)] at subL
        rw [Nest.bp_true.mpr (allE.mpr emp)] at subE
        simp only [Lynx.apply_eq, «map_to_list_empty:ensures/3»]
        have el : Elixir.Module.Types.Descr.«empty_list/0» = .ok Nest.nilT := rfl
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, subE, Erlang.erlang.«==/2»,
          Lynx.Term.true]
      · have subL := Nest.next_sub (t := node) (n := d + 2) (Nest.lTy_de nil k dI) Nest.nilT_de (m := δ + 100) (by omega)
        have el : Elixir.Module.Types.Descr.«empty_list/0» = .ok Nest.nilT := rfl
        rw [Nest.bp_congr ((Nest.lTy_nil_sub dI nil k).trans allE.symm)] at subL
        simp only [Lynx.apply_eq, «map_to_list_empty:ensures/3»]
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, subE, Erlang.erlang.«==/2»,
          Lynx.Term.true]
      """

    law map_to_list_nil(map, depth, node),
      requires:
        arrows_static?(map, {depth + 1, node}) and depth?(depth) and match?({:ok, _}, Descr.map_to_list(map)),
      expects:
        Descr.subtype?(Descr.empty_list(), elem(Descr.map_to_list(map), 1)) ==
          not Descr.disjoint?(map, Descr.empty_map()),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels and its lists `d + 2`, so the proofs run from the bound of level `d + 2` on,
      -- and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_to_list_nil:requires/3», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.2
      refine ⟨max bound (100 + 24 * (d + 2)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have requires := requires (δ + 100) hb
      simp only [Lynx.apply_eq, «map_to_list_nil:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨hs, -⟩, hl⟩ := requires
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      have hm : (Nest.level node (d + 2)).K + 25 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have hm₁ : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      rcases Nest.arrows_static_ok hs with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.tolist_one, Nest.tolist_term] at hl; simp at hl
      obtain ⟨res', runL, ⟨rfl, -⟩ | ⟨only, b, inner, L, hb, rfl, dI, sI, hL⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm₁
      · rw [Nest.tolist_one, runL] at hl; simp at hl
      have mt : ∀ w, Nest.MT node (d + 1) X w ↔
          Nest.denMF (Nest.level node (d + 1)).E (Nest.level node (d + 1)).den b w = Bool.true := fun w => by
        simp [Nest.MT, hb]
      -- Lists of the type hold the empty list exactly when the type holds the empty map.
      have dis := Nest.next_disj (t := node) (n := d + 1) (Or.inr ⟨X, rfl, sX⟩) Nest.emptyMap_de (m := δ + 100) (by omega)
      have holds : (¬∀ v : Nest.PN node (d + 1), Nest.denD (.map X) v → Nest.denD Nest.emptyMapT v → False) ↔
          Nest.MT node (d + 1) X Nest.wNone := by
        constructor
        · intro h
          obtain ⟨v, hv⟩ := Classical.not_forall.mp h
          obtain ⟨hx, he⟩ := Classical.not_imp.mp hv
          have he := Classical.not_imp.mp he |>.1
          obtain ⟨w, hw⟩ := Nest.pt_map v (only.1 v hx)
          rw [Nest.emptyMapT, hw, Nest.mt_emptyMap] at he
          subst he
          exact (hw X).mp hx
        · intro h h'
          exact h' _ ((Nest.denD_mpt _).mpr h) ((Nest.denD_mpt _).mpr ((Nest.mt_emptyMap _).mpr rfl))
      have el : Elixir.Module.Types.Descr.«empty_list/0» = .ok Nest.nilT := rfl
      rcases hL with ⟨rfl, emp⟩ | ⟨nil, k, rfl, hnil⟩
      · have subL := Nest.next_sub (t := node) (n := d + 2) Nest.nilT_de Nest.nilT_de (m := δ + 100) (by omega)
        rw [Nest.bp_true.mpr (show Nest.SubN node (d + 2) Nest.nilT Nest.nilT from fun q hq => hq)] at subL
        have e := (Nest.inner_empty_iff sI).mp emp
        obtain ⟨w, hw⟩ := only.2
        have hn : Nest.MT node (d + 1) X Nest.wNone := by rw [← e w ((mt w).mp hw)]; exact hw
        rw [Nest.bp_false.mpr (fun h => holds.mpr hn h)] at dis
        simp only [Lynx.apply_eq, «map_to_list_nil:ensures/3»]
        simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, dis, Erlang.erlang.«not/1»,
          Erlang.erlang.«==/2», Lynx.Term.true]
      · have subL := Nest.next_sub (t := node) (n := d + 2) Nest.nilT_de (Nest.lTy_de nil k dI) (m := δ + 100) (by omega)
        rw [Nest.bp_congr ((Nest.nilT_sub_lTy dI nil k).trans hnil)] at subL
        simp only [Lynx.apply_eq, «map_to_list_nil:ensures/3»]
        by_cases hn : Nest.MT node (d + 1) X Nest.wNone
        · rw [Nest.bp_true.mpr hn] at subL
          rw [Nest.bp_false.mpr (fun h => holds.mpr hn h)] at dis
          simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, dis, Erlang.erlang.«not/1»,
            Erlang.erlang.«==/2», Lynx.Term.true]
        · rw [Nest.bp_false.mpr hn] at subL
          rw [Nest.bp_true.mpr (Classical.not_not.mp fun h => hn (holds.mp h))] at dis
          simp [Nest.tolist_one, runL, Erlang.erlang.«element/2», el, subL, Nest.emptyMap_run, dis, Erlang.erlang.«not/1»,
            Erlang.erlang.«==/2», Lynx.Term.true]
      """

    law map_to_list_badmap(map, depth, node),
      requires: arrows_static?(map, {depth + 1, node}) and depth?(depth),
      expects:
        (Descr.map_to_list(map) == :badmap) ==
          not (Descr.subtype?(map, Descr.open_map()) and not Descr.empty?(map)),
      proof: ~LEAN"""
      -- The map nests at most `d + 1` levels, so the proofs run from the bound of level `d + 1` on.
      simp only [«map_to_list_badmap:requires/3», Lynx.Term.true] at requires
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at requires; cases requires
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨hs, hd⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      simp only [Erlang.erlang.«+/2_integers», Except.ok.injEq] at hp
      subst hp
      have hs : «arrows_static?/2» map (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hs
      refine ⟨100 + 24 * (d + 1), fun depth deep => ?_⟩
      obtain ⟨δ, rfl⟩ : ∃ δ, depth = δ + 100 := ⟨depth - 100, by omega⟩
      have hm : (Nest.level node (d + 1)).K + 30 ≤ δ + 100 := by rw [Nest.level_K]; omega
      have dt := Nest.arrows_static_ok hs
      have top : Elixir.Module.Types.Descr.«open_map/0» =
          .ok (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]) := rfl
      have sT := Nest.next_sub dt Nest.mapTop_de (m := δ + 100) (by omega)
      rcases dt with rfl | ⟨X, rfl, sX⟩
      · rw [Nest.bp_false.mpr fun h => by
          have := (Nest.mapTop_den Nest.bitPt).mp (h Nest.bitPt (Nest.denD_term _))
          simp [Nest.bitPt] at this] at sT
        simp only [Lynx.apply_eq, «map_to_list_badmap:ensures/3»]
        simp [Nest.tolist_one, Nest.tolist_term, Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      have ne := Nest.next_empty (Or.inr ⟨X, rfl, sX⟩) (m := δ + 100) (by omega)
      obtain ⟨res, run, ⟨rfl, nonly⟩ | ⟨only, b, inner, L, -, rfl, -⟩⟩ :=
        Nest.tolist_map (t := node) (n := d) (Or.inr ⟨X, rfl, sX⟩) hm
      · rw [Nest.monly_iff] at nonly
        simp only [Lynx.apply_eq, «map_to_list_badmap:ensures/3»]
        by_cases h : Nest.SubN node (d + 1) (.map X) (.map [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])])
        · rw [Nest.bp_true.mpr h] at sT
          rw [Nest.bp_true.mpr (Classical.not_not.mp fun h' => nonly ⟨h, h'⟩)] at ne
          simp [Nest.tolist_one, run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
        · rw [Nest.bp_false.mpr h] at sT
          simp [Nest.tolist_one, run, Erlang.erlang.«==/2», top, sT, Lynx.Term.true]
      · obtain ⟨h₁, h₂⟩ := Nest.monly_iff.mp only
        rw [Nest.bp_true.mpr h₁] at sT
        rw [Nest.bp_false.mpr h₂] at ne
        simp only [Lynx.apply_eq, «map_to_list_badmap:ensures/3»]
        simp [Nest.tolist_one, run, Erlang.erlang.«==/2», top, sT, ne, Erlang.erlang.«not/1», Lynx.Term.true]
      """

    law map_constructor_closed_open(pairs, depth, node),
      requires: map_pairs?(pairs, {depth, node}) and depth?(depth),
      expects: Descr.subtype?(Descr.closed_map(pairs), Descr.open_map(pairs)),
      proof: ~LEAN"""
      simp only [«map_constructor_closed_open:requires/3», Lynx.Term.true, Lynx.Except.andAlso_eq_true] at requires
      obtain ⟨hp, hd⟩ := requires
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      refine ⟨(Nest.level node (d + 1)).K + 26, fun depth' deep => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      simp only [Lynx.apply_eq]
      exact Nest.ctor_closed_open_core hfs (by omega) _ _
      """

    law map_constructor_empty(),
      expects: Descr.equal?(Descr.empty_map(), Descr.closed_map([])),
      proof: ~LEAN"""
      refine ⟨(Nest.level (.atom "term") 0).K + 26, fun depth deep => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, depth = m + 1 := ⟨depth - 1, by omega⟩
      simp only [Lynx.apply_eq]
      exact Nest.ctor_empty_core (t := .atom "term") (n := 0) (by omega)
      """

    law map_constructor_atom(tag, pairs, key, depth, node),
      requires: tag in [:open, :closed] and map_pairs?(pairs, {depth, node}) and depth?(depth) and is_atom(key),
      expects: Descr.subtype?(construct(tag, pairs), Descr.open_map([{key, atom_field(tag, pairs, key)}])),
      proof: ~LEAN"""
      simp only [«map_constructor_atom:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true, Except.ok.injEq]
        at requires
      obtain ⟨⟨⟨ht, hp⟩, hd⟩, hk⟩ := requires
      obtain ⟨s, rfl, hs⟩ := Nest.tag_ok ht
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      obtain ⟨k, rfl⟩ := Nest.is_atom_true hk
      refine ⟨(Nest.level node (d + 1)).K + 26, fun depth' deep => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      simp only [Lynx.apply_eq]
      exact Nest.ctor_atom_core hs hfs k (by omega) _ _
      """

    law map_constructor_atom_least(tag, pairs, key, value, optional, depth, node),
      requires:
        tag in [:open, :closed] and map_pairs?(pairs, {depth, node}) and arrows_static?(value, {depth, node}) and
          depth?(depth) and is_atom(key) and is_boolean(optional) and not Descr.empty?(construct(tag, pairs)) and
          Descr.subtype?(construct(tag, pairs), Descr.open_map([{key, {value, optional}}])),
      expects:
        Descr.subtype?(elem(atom_field(tag, pairs, key), 0), value) and
          (optional or not elem(atom_field(tag, pairs, key), 1)),
      proof: ~LEAN"""
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_constructor_atom_least:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Except.ok.injEq] at checked
      obtain ⟨⟨⟨⟨⟨⟨⟨ht, hp⟩, hv⟩, hd⟩, hk⟩, ho⟩, -⟩, -⟩ := checked
      obtain ⟨s, rfl, hs⟩ := Nest.tag_ok ht
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      obtain ⟨k, rfl⟩ := Nest.is_atom_true hk
      obtain ⟨o, rfl⟩ := Nest.is_boolean_true ho
      have ev : (Nest.level node (d + 1)).E value := Or.inl (Nest.arrows_static_ok hv)
      refine ⟨max bound ((Nest.level node (d + 1)).K + 26), fun depth' deep => ?_⟩
      obtain ⟨hb, hm⟩ := Nat.max_le.mp deep
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      have r := requires (m + 1) hb
      simp only [Lynx.apply_eq, «map_constructor_atom_least:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true]
        at r
      obtain ⟨⟨-, r1⟩, r2⟩ := r
      simp only [Lynx.apply_eq]
      exact Nest.ctor_atom_least_core hs hfs k ev o (by omega) r1 r2 _ _
      """

    law map_constructor_kind(tag, pairs, kind, depth, node),
      requires:
        tag in [:open, :closed] and map_pairs?(pairs, {depth, node}) and depth?(depth) and keys?([], [kind]) and
          kind != :atom,
      expects: Descr.subtype?(construct(tag, pairs), Descr.open_map([{[kind], domain_value(tag, pairs, kind)}])),
      proof: ~LEAN"""
      simp only [«map_constructor_kind:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true, Except.ok.injEq]
        at requires
      obtain ⟨⟨⟨⟨ht, hp⟩, hd⟩, hk⟩, hn⟩ := requires
      obtain ⟨s, rfl, hs⟩ := Nest.tag_ok ht
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      obtain ⟨-, ks, -, e, -, hks⟩ := Nest.keys_ok hk
      obtain rfl := list_inj e
      obtain ⟨k, mk, rfl⟩ := hks kind (by simp)
      refine ⟨(Nest.level node (d + 1)).K + 26, fun depth' deep => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      simp only [Lynx.apply_eq]
      exact Nest.ctor_kind_core hs hfs mk (Nest.ne_atom_ok hn) (by omega) _ _
      """

    law map_constructor_kind_least(tag, pairs, kind, value, depth, node),
      requires:
        tag in [:open, :closed] and map_pairs?(pairs, {depth, node}) and arrows_static?(value, {depth, node}) and
          depth?(depth) and keys?([], [kind]) and kind != :atom and not Descr.empty?(construct(tag, pairs)) and
          Descr.subtype?(construct(tag, pairs), Descr.open_map([{[kind], value}])),
      expects: Descr.subtype?(domain_value(tag, pairs, kind), value),
      proof: ~LEAN"""
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «map_constructor_kind_least:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Except.ok.injEq] at checked
      obtain ⟨⟨⟨⟨⟨⟨⟨ht, hp⟩, hv⟩, hd⟩, hk⟩, hn⟩, -⟩, -⟩ := checked
      obtain ⟨s, rfl, hs⟩ := Nest.tag_ok ht
      obtain ⟨d, rfl⟩ := Nest.depth_nat hd
      obtain ⟨fs, rfl, hfs⟩ := Nest.map_pairs_ok (t := node) (d := d) _ hp
      obtain ⟨-, ks, -, e, -, hks⟩ := Nest.keys_ok hk
      obtain rfl := list_inj e
      obtain ⟨k, mk, rfl⟩ := hks kind (by simp)
      have ev : (Nest.level node (d + 1)).E value := Or.inl (Nest.arrows_static_ok hv)
      refine ⟨max bound ((Nest.level node (d + 1)).K + 26), fun depth' deep => ?_⟩
      obtain ⟨hb, hm⟩ := Nat.max_le.mp deep
      obtain ⟨m, rfl⟩ : ∃ m, depth' = m + 1 := ⟨depth' - 1, by omega⟩
      have r := requires (m + 1) hb
      simp only [Lynx.apply_eq, «map_constructor_kind_least:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true]
        at r
      obtain ⟨⟨-, r1⟩, r2⟩ := r
      simp only [Lynx.apply_eq]
      exact Nest.ctor_kind_least_core hs hfs mk (Nest.ne_atom_ok hn) ev (by omega) r1 r2 _ _
      """

    law fun_apply_subtype(fun, args, static?, depth, node),
      requires:
        arrows_static?(fun, {depth + 1, node}) and arguments?(args, {depth, node}) and depth?(depth) and
          match?({:ok, _}, Descr.fun_apply(fun, args, static?)),
      expects: Descr.subtype?(fun, Descr.fun(args, elem(Descr.fun_apply(fun, args, static?), 1))),
      proof: ~LEAN"""
      -- The function nests at most `d + 1` levels and the arguments `d`, so the proofs run from the bound of level
      -- `d + 1` on, and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «fun_apply_subtype:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      have requires := requires depth hb
      simp only [Lynx.apply_eq, «fun_apply_subtype:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨hf, ha⟩, -⟩, hok⟩ := requires
      have hf : «arrows_static?/2» «fun» (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hf
      obtain ⟨l, rfl, hl⟩ := Nest.arguments_ok ha
      obtain ⟨r, run⟩ : ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) «static?» =
          .ok (.tuple #[.atom "ok", r]) := by
        cases h : Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) «static?» with
        | error err => rw [h] at hok; cases hok
        | ok v =>
          rw [h, Lynx.Except.ok_bind] at hok
          split at hok
          · exact ⟨_, rfl⟩
          · simp at hok
      obtain ⟨⟨F, rF, sub⟩, top⟩ := Nest.apply_ok_sub (Nest.arrows_static_ok hf)
        (fun a ma => Nest.arrows_static_ok (hl a ma)) (m := depth) (by rw [Nest.level_K]; omega) run
      simp only [Lynx.apply_eq, «fun_apply_subtype:ensures/5»]
      simp [run, Erlang.erlang.«element/2», rF, sub, Lynx.Term.true]
      """

    law fun_apply_arity(fun, args, static?, depth, node),
      requires:
        arrows_static?(fun, {depth + 1, node}) and arguments?(args, {depth, node}) and depth?(depth) and
          match?({:ok, _}, Descr.fun_apply(fun, args, static?)),
      expects: Descr.subtype?(fun, Descr.fun(length(args))),
      proof: ~LEAN"""
      -- The function nests at most `d + 1` levels and the arguments `d`, so the proofs run from the bound of level
      -- `d + 1` on, and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «fun_apply_arity:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      have requires := requires depth hb
      simp only [Lynx.apply_eq, «fun_apply_arity:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨hf, ha⟩, -⟩, hok⟩ := requires
      have hf : «arrows_static?/2» «fun» (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hf
      obtain ⟨l, rfl, hl⟩ := Nest.arguments_ok ha
      obtain ⟨r, run⟩ : ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) «static?» =
          .ok (.tuple #[.atom "ok", r]) := by
        cases h : Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) «static?» with
        | error err => rw [h] at hok; cases hok
        | ok v =>
          rw [h, Lynx.Except.ok_bind] at hok
          split at hok
          · exact ⟨_, rfl⟩
          · simp at hok
      obtain ⟨⟨F, rF, sub⟩, top⟩ := Nest.apply_ok_sub (Nest.arrows_static_ok hf)
        (fun a ma => Nest.arrows_static_ok (hl a ma)) (m := depth) (by rw [Nest.level_K]; omega) run
      simp only [Lynx.apply_eq, «fun_apply_arity:ensures/5»]
      simp [length_list, fun_arity_run, top, Lynx.Term.true]
      """

    law fun_apply_domain(fun, args, static?, depth, node),
      requires:
        arrows_static?(fun, {depth + 1, node}) and arguments?(args, {depth, node}) and depth?(depth) and
          inhabited?(args) and not Descr.empty?(fun) and Descr.subtype?(fun, Descr.fun(args, Descr.term())),
      expects: match?({:ok, _}, Descr.fun_apply(fun, args, static?)),
      proof: ~LEAN"""
      -- The function nests at most `d + 1` levels and the arguments `d`, so the proofs run from the bound of level
      -- `d + 1` on, and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «fun_apply_domain:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      have requires := requires depth hb
      simp only [Lynx.apply_eq, «fun_apply_domain:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨hf, ha⟩, -⟩, inh⟩, ne⟩, sub⟩ := requires
      have hf : «arrows_static?/2» «fun» (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hf
      obtain ⟨l, rfl, hl⟩ := Nest.arguments_ok ha
      obtain ⟨r, run⟩ := Nest.apply_domain_law (s := «static?») (Nest.arrows_static_ok hf)
        (fun a ma => Nest.arrows_static_ok (hl a ma)) (m := depth) (by rw [Nest.level_K]; omega) inh ne sub
      simp only [Lynx.apply_eq, «fun_apply_domain:ensures/5»]
      simp [run, Lynx.Term.true]
      """

    law fun_apply_badfun(fun, args, static?, depth, node),
      requires:
        arrows_static?(fun, {depth + 1, node}) and arguments?(args, {depth, node}) and depth?(depth) and
          inhabited?(args) and (Descr.empty?(fun) or not Descr.subtype?(fun, Descr.fun())),
      expects: Descr.fun_apply(fun, args, static?) == :badfun,
      proof: ~LEAN"""
      -- The function nests at most `d + 1` levels and the arguments `d`, so the proofs run from the bound of level
      -- `d + 1` on, and the precondition from its own bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «fun_apply_badfun:requires/5», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      have requires := requires depth hb
      simp only [Lynx.apply_eq, «fun_apply_badfun:requires/5», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨hf, ha⟩, -⟩, inh⟩, bad⟩ := requires
      have hf : «arrows_static?/2» «fun» (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hf
      obtain ⟨l, rfl, hl⟩ := Nest.arguments_ok ha
      have run := Nest.apply_badfun_law (s := «static?») (Nest.arrows_static_ok hf)
        (fun a ma => Nest.arrows_static_ok (hl a ma)) (m := depth) (by rw [Nest.level_K]; omega) inh bad
      simp only [Lynx.apply_eq, «fun_apply_badfun:ensures/5»]
      simp [run, Erlang.erlang.«==/2», Lynx.Term.true]
      """

    law fun_apply_sound(fun, args, static?, g, ss, depth, node),
      requires:
        arrows_gradual?(fun, {depth + 1, node}) and gradual_arguments?(args, {depth, node}) and is_boolean(static?) and
          arrows_static?(g, {depth + 1, node}) and arguments?(ss, {depth, node}) and depth?(depth) and
          materializes?(g, fun) and all_materialize?(ss, args) and
          match?({:ok, _}, Descr.fun_apply(fun, args, static?)) and match?({:ok, _}, Descr.fun_apply(g, ss, static?)),
      expects:
        Descr.subtype?(
          elem(Descr.fun_apply(g, ss, static?), 1),
          Descr.upper_bound(elem(Descr.fun_apply(fun, args, static?), 1))
        ),
      proof: ~LEAN"""
      -- Both bounds of the result for the materializations are in the image of the upper bounds of the arguments by
      -- the upper bound of the function, which is the upper bound of the result.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «fun_apply_sound:requires/7», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      have requires := requires depth hb
      simp only [Lynx.apply_eq, «fun_apply_sound:requires/7», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, ha⟩, hs⟩, hg⟩, hss⟩, -⟩, mg⟩, mss⟩, ok₁⟩, ok₂⟩ := requires
      have hs := Nest.boolean_mode hs
      have hf := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := depth) (by rw [Nest.level_K]; omega)
        (by simpa using hf)
      have hg : «arrows_static?/2» g (.tuple #[.integer ((d + 1 : Nat) : Int), node]) = .ok (.atom "true") := by
        simpa using hg
      have hg := Nest.arrows_static_ok hg
      obtain ⟨l, rfl, hl⟩ := Nest.gradual_arguments_ok (t := node) (n := d) (m := depth)
        (by rw [Nest.level_K]; omega) ha
      obtain ⟨sl, rfl, hsl⟩ := Nest.arguments_ok hss
      have hsl : ∀ a ∈ sl, Nest.DE (Nest.level node d).E a := fun a ma => Nest.arrows_static_ok (hsl a ma)
      obtain ⟨gg, -, ug⟩ := Nest.de_gd hg
      have gsl : ∀ a ∈ sl, Nest.GD node d a := fun a ma => (Nest.de_gd (hsl a ma)).1
      have mg := Nest.materializes_ok (m := depth) (by rw [Nest.level_K]; omega) hg hf mg
      have mss := Nest.all_materialize_ok (m := depth) (by rw [Nest.level_K]; omega) hsl hl mss
      have hm : (Nest.level node (d + 1)).K + 41 ≤ depth := by rw [Nest.level_K]; omega
      obtain ⟨T₁, F₁⟩ := Nest.apply_law hf hl hs hm
      obtain ⟨T₂, F₂⟩ := Nest.apply_law gg gsl hs hm
      obtain ⟨r₁, run₁⟩ : ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) «static?» =
          .ok (.tuple #[.atom "ok", r]) := by
        cases h : Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) «static?» with
        | error err => rw [h] at ok₁; cases ok₁
        | ok v =>
          rw [h, Lynx.Except.ok_bind] at ok₁
          split at ok₁
          · exact ⟨_, rfl⟩
          · simp at ok₁
      obtain ⟨r₂, run₂⟩ : ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D depth) g (Lynx.Term.list sl) «static?» =
          .ok (.tuple #[.atom "ok", r]) := by
        cases h : Elixir.Module.Types.Descr.«fun_apply/3» (D depth) g (Lynx.Term.list sl) «static?» with
        | error err => rw [h] at ok₂; cases ok₂
        | ok v =>
          rw [h, Lynx.Except.ok_bind] at ok₂
          split at ok₂
          · exact ⟨_, rfl⟩
          · simp at ok₂
      have C₁ : Nest.AppC node d «fun» l := Classical.byContradiction fun nC => F₁ nC r₁ run₁
      have C₂ : Nest.AppC node d g sl := Classical.byContradiction fun nC => F₂ nC r₂ run₂
      obtain ⟨r₁', e₁, -, u₁, -, ub₁, -, d₁, U₁, -⟩ := T₁ C₁
      obtain ⟨r₂', e₂, l₂, u₂, -, -, -, -, U₂, -, S₂, LU₂⟩ := T₂ C₂
      rw [run₁] at e₁
      rw [run₂] at e₂
      obtain rfl : r₁ = r₁' := by simpa using e₁
      obtain rfl : r₂ = r₂' := by simpa using e₂
      have len := Nest.pairwise2_length mss
      have up : Nest.SubN node d u₂ u₁ := fun v h => by
        refine (U₁ v).mpr ?_
        have h := (U₂ v).mp h
        simp only [Nest.UpI] at h ⊢
        rw [← len]
        refine Nest.imgP_mono (fun g' vg h => ?_) (fun w hw => Nest.inDomR_sub (fun a ma => (gsl a ma).2.2)
          (fun b mb => (hl b mb).2.2) (Nest.pairwise2_imp_mem (fun a ma b h => ?_) mss) hw) h
        · rw [ug] at h
          exact Nest.funT_mono hg hf.2.2 mg.2 vg h
        · rw [(Nest.de_gd (hsl a ma)).2.2]; exact h.2
      obtain ⟨gu, lu, uu⟩ := Nest.de_gd d₁
      simp only [Lynx.apply_eq, «fun_apply_sound:ensures/7»]
      simp [run₁, run₂, Erlang.erlang.«element/2», ub₁, S₂ u₁ gu, lu, uu,
        Nest.bp_true.mpr (⟨fun v h => up v (LU₂ v h), up⟩ : Nest.SubN node d l₂ u₁ ∧ Nest.SubN node d u₂ u₁),
        Lynx.Term.true]
      """

    law fun_apply_upper(fun, args, others, static?, depth, node),
      requires:
        arrows_gradual?(fun, {depth + 1, node}) and gradual_arguments?(args, {depth, node}) and
          gradual_arguments?(others, {depth, node}) and is_boolean(static?) and depth?(depth) and
          uppers_in?(args, others) and match?({:ok, _}, Descr.fun_apply(fun, args, static?)) and
          match?({:ok, _}, Descr.fun_apply(fun, others, static?)),
      expects:
        Descr.subtype?(
          Descr.upper_bound(elem(Descr.fun_apply(fun, args, static?), 1)),
          Descr.upper_bound(elem(Descr.fun_apply(fun, others, static?), 1))
        ),
      proof: ~LEAN"""
      -- The upper bound of the result is the image of the upper bounds of the arguments by the upper bound of the
      -- function, which grows with them.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «fun_apply_upper:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      have requires := requires depth hb
      simp only [Lynx.apply_eq, «fun_apply_upper:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hf, ha⟩, ho⟩, hs⟩, -⟩, hu⟩, ok₁⟩, ok₂⟩ := requires
      have hs := Nest.boolean_mode hs
      have hf := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := depth) (by rw [Nest.level_K]; omega)
        (by simpa using hf)
      obtain ⟨l, rfl, hl⟩ := Nest.gradual_arguments_ok (t := node) (n := d) (m := depth)
        (by rw [Nest.level_K]; omega) ha
      obtain ⟨l', rfl, hl'⟩ := Nest.gradual_arguments_ok (t := node) (n := d) (m := depth)
        (by rw [Nest.level_K]; omega) ho
      have pw := Nest.uppers_in_ok (m := depth) (by rw [Nest.level_K]; omega) hl hl' hu
      have hm : (Nest.level node (d + 1)).K + 41 ≤ depth := by rw [Nest.level_K]; omega
      obtain ⟨T₁, F₁⟩ := Nest.apply_law hf hl hs hm
      obtain ⟨T₂, F₂⟩ := Nest.apply_law hf hl' hs hm
      obtain ⟨r₁, run₁⟩ : ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) «static?» =
          .ok (.tuple #[.atom "ok", r]) := by
        cases h : Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) «static?» with
        | error err => rw [h] at ok₁; cases ok₁
        | ok v =>
          rw [h, Lynx.Except.ok_bind] at ok₁
          split at ok₁
          · exact ⟨_, rfl⟩
          · simp at ok₁
      obtain ⟨r₂, run₂⟩ : ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l') «static?» =
          .ok (.tuple #[.atom "ok", r]) := by
        cases h : Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l') «static?» with
        | error err => rw [h] at ok₂; cases ok₂
        | ok v =>
          rw [h, Lynx.Except.ok_bind] at ok₂
          split at ok₂
          · exact ⟨_, rfl⟩
          · simp at ok₂
      have C₁ : Nest.AppC node d «fun» l := Classical.byContradiction fun nC => F₁ nC r₁ run₁
      have C₂ : Nest.AppC node d «fun» l' := Classical.byContradiction fun nC => F₂ nC r₂ run₂
      obtain ⟨r₁', e₁, -, u₁, -, ub₁, -, d₁, U₁, -⟩ := T₁ C₁
      obtain ⟨r₂', e₂, -, u₂, -, ub₂, -, d₂, U₂, -⟩ := T₂ C₂
      rw [run₁] at e₁
      rw [run₂] at e₂
      obtain rfl : r₁ = r₁' := by simpa using e₁
      obtain rfl : r₂ = r₂' := by simpa using e₂
      have len := Nest.pairwise2_length pw
      have sub : Nest.SubN node d u₁ u₂ := fun v h => by
        refine (U₂ v).mpr ?_
        have h := (U₁ v).mp h
        simp only [Nest.UpI] at h ⊢
        rw [← len]
        exact Nest.imgP_mono (fun g _ h => h)
          (fun w hw => Nest.inDomR_sub (fun a ma => (hl a ma).2.2) (fun b mb => (hl' b mb).2.2) pw hw) h
      simp only [Lynx.apply_eq, «fun_apply_upper:ensures/6»]
      simp [run₁, run₂, Erlang.erlang.«element/2», ub₁, ub₂,
        Nest.next_sub d₁ d₂ (m := depth) (by rw [Nest.level_K]; omega), Nest.bp_true.mpr sub, Lynx.Term.true]
      """

    law fun_apply_precise(fun, args, fun2, args2, depth, node),
      requires:
        arrows_gradual?(fun, {depth + 1, node}) and gradual_arguments?(args, {depth, node}) and
          arrows_gradual?(fun2, {depth + 1, node}) and gradual_arguments?(args2, {depth, node}) and depth?(depth) and
          precise?(fun, fun2) and all_precise?(args, args2) and match?({:ok, _}, Descr.fun_apply(fun, args, false)),
      expects:
        (case Descr.fun_apply(fun2, args2, false) do
           {:ok, result2} -> precise?(elem(Descr.fun_apply(fun, args, false), 1), result2)
           _ -> false
         end),
      proof: ~LEAN"""
      -- Less precise functions and arguments succeed too, and the bounds of their results are the images of their
      -- bounds, which grow with them.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «fun_apply_precise:requires/6», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.1.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      have requires := requires depth hb
      simp only [Lynx.apply_eq, «fun_apply_precise:requires/6», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨⟨⟨⟨⟨hf, ha⟩, hf₂⟩, ha₂⟩, -⟩, pf⟩, pa⟩, ok₁⟩ := requires
      have hf := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := depth) (by rw [Nest.level_K]; omega)
        (by simpa using hf)
      have hf₂ := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := depth) (by rw [Nest.level_K]; omega)
        (by simpa using hf₂)
      obtain ⟨l, rfl, hl⟩ := Nest.gradual_arguments_ok (t := node) (n := d) (m := depth)
        (by rw [Nest.level_K]; omega) ha
      obtain ⟨l₂, rfl, hl₂⟩ := Nest.gradual_arguments_ok (t := node) (n := d) (m := depth)
        (by rw [Nest.level_K]; omega) ha₂
      have pf := Nest.precise_ok (m := depth) (by rw [Nest.level_K]; omega) hf hf₂ pf
      have pa := Nest.all_precise_ok (m := depth) (by rw [Nest.level_K]; omega) hl hl₂ pa
      have hm : (Nest.level node (d + 1)).K + 41 ≤ depth := by rw [Nest.level_K]; omega
      obtain ⟨T₁, F₁⟩ := Nest.apply_law hf hl (s := .atom "false") (Or.inr rfl) hm
      obtain ⟨T₂, -⟩ := Nest.apply_law hf₂ hl₂ (s := .atom "false") (Or.inr rfl) hm
      obtain ⟨r₁, run₁⟩ : ∃ r, Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l)
          (.atom "false") = .ok (.tuple #[.atom "ok", r]) := by
        cases h : Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) (.atom "false") with
        | error err => rw [h] at ok₁; cases ok₁
        | ok v =>
          rw [h, Lynx.Except.ok_bind] at ok₁
          split at ok₁
          · exact ⟨_, rfl⟩
          · simp at ok₁
      have C₁ : Nest.AppC node d «fun» l := Classical.byContradiction fun nC => F₁ nC r₁ run₁
      have C₂ := Nest.appC_mono hf hf₂ pf hl hl₂ pa C₁
      obtain ⟨r₁', e₁, lr₁, ur₁, lb₁, ub₁, dl₁, du₁, U₁, L₁, -⟩ := T₁ C₁
      obtain ⟨r₂, e₂, lr₂, ur₂, lb₂, ub₂, dl₂, du₂, U₂, L₂, -⟩ := T₂ C₂
      rw [run₁] at e₁
      obtain rfl : r₁ = r₁' := by simpa using e₁
      have len := Nest.pairwise2_length pa
      have lo : Nest.SubN node d lr₂ lr₁ := fun v h => by
        refine (L₁ rfl v).mpr ?_
        have h := (L₂ rfl v).mp h
        simp only [Nest.LoI] at h ⊢
        rw [len]
        exact Nest.imgP_mono (fun g vg h => Nest.funT_mono hf₂.2.1 hf.2.1 pf.1 vg h)
          (fun w hw => Nest.inDomR_sub (fun a ma => (hl₂ a ma).2.1) (fun b mb => (hl b mb).2.1)
            (Nest.pairwise2_swap (Nest.pairwise2_imp (fun _ _ h => h.1) pa)) hw) h
      have up : Nest.SubN node d ur₁ ur₂ := fun v h => by
        refine (U₂ v).mpr ?_
        have h := (U₁ v).mp h
        simp only [Nest.UpI] at h ⊢
        rw [← len]
        exact Nest.imgP_mono (fun g vg h => Nest.funT_mono hf.2.2 hf₂.2.2 pf.2 vg h)
          (fun w hw => Nest.inDomR_sub (fun a ma => (hl a ma).2.2) (fun b mb => (hl₂ b mb).2.2)
            (Nest.pairwise2_imp (fun _ _ h => h.2) pa) hw) h
      have hmd : (Nest.level node d).K + 23 ≤ depth := by rw [Nest.level_K]; omega
      simp only [Lynx.apply_eq, «fun_apply_precise:ensures/6»]
      simp [run₁, e₂, Erlang.erlang.«element/2», «precise?/2», lb₁, lb₂, ub₁, ub₂, Nest.next_sub dl₂ dl₁ hmd,
        Nest.next_sub du₁ du₂ hmd, Nest.bp_true.mpr lo, Nest.bp_true.mpr up, Lynx.Term.true]
      """

    law fun_apply_modes(fun, args, depth, node),
      requires:
        arrows_gradual?(fun, {depth + 1, node}) and gradual_arguments?(args, {depth, node}) and depth?(depth) and
          (match?({:ok, _}, Descr.fun_apply(fun, args, true)) or match?({:ok, _}, Descr.fun_apply(fun, args, false))),
      expects:
        (case {Descr.fun_apply(fun, args, true), Descr.fun_apply(fun, args, false)} do
           {{:ok, strict}, {:ok, gradual}} -> Descr.equal?(Descr.upper_bound(strict), Descr.upper_bound(gradual))
           _ -> false
         end),
      proof: ~LEAN"""
      -- Both modes succeed on the same condition, with the same upper bound.
      obtain ⟨bound, requires⟩ := requires
      have checked := requires bound (Nat.le_refl _)
      simp only [Lynx.apply_eq, «fun_apply_modes:requires/4», Lynx.Term.true] at checked
      obtain ⟨p, hp⟩ : ∃ p, Erlang.erlang.«+/2» depth (.integer 1) = .ok p := by
        cases h : Erlang.erlang.«+/2» depth (.integer 1) with
        | error err => rw [h] at checked; cases checked
        | ok p => exact ⟨p, rfl⟩
      rw [hp, Lynx.Except.ok_bind] at checked
      simp only [Lynx.Except.andAlso_eq_true] at checked
      obtain ⟨d, rfl⟩ := Nest.depth_nat checked.1.2
      refine ⟨max bound (100 + 24 * (d + 1)), fun depth deep => ?_⟩
      obtain ⟨hb, hd⟩ := Nat.max_le.mp deep
      have requires := requires depth hb
      simp only [Lynx.apply_eq, «fun_apply_modes:requires/4», Lynx.Term.true, Lynx.Except.andAlso_eq_true,
        Erlang.erlang.«+/2_integers», Lynx.Except.ok_bind] at requires
      obtain ⟨⟨⟨hf, ha⟩, -⟩, hok⟩ := requires
      have hf := Nest.arrows_gradual_ok (t := node) (n := d + 1) (m := depth) (by rw [Nest.level_K]; omega)
        (by simpa using hf)
      obtain ⟨l, rfl, hl⟩ := Nest.gradual_arguments_ok (t := node) (n := d) (m := depth)
        (by rw [Nest.level_K]; omega) ha
      have hm : (Nest.level node (d + 1)).K + 41 ≤ depth := by rw [Nest.level_K]; omega
      obtain ⟨T₁, F₁⟩ := Nest.apply_law hf hl (s := .atom "true") (Or.inl rfl) hm
      obtain ⟨T₂, F₂⟩ := Nest.apply_law hf hl (s := .atom "false") (Or.inr rfl) hm
      by_cases C : Nest.AppC node d «fun» l
      · obtain ⟨r₁, e₁, -, u₁, -, ub₁, -, d₁, U₁, -⟩ := T₁ C
        obtain ⟨r₂, e₂, -, u₂, -, ub₂, -, d₂, U₂, -⟩ := T₂ C
        obtain ⟨g₁, lo₁, up₁⟩ := Nest.de_gd d₁
        obtain ⟨g₂, lo₂, up₂⟩ := Nest.de_gd d₂
        have eq := Nest.gd_eq_true g₁ g₂ (m := depth) (by rw [Nest.level_K]; omega)
          (fun v => by rw [lo₁, lo₂]; exact (U₁ v).trans (U₂ v).symm)
          (fun v => by rw [up₁, up₂]; exact (U₁ v).trans (U₂ v).symm)
        simp only [Lynx.apply_eq, «fun_apply_modes:ensures/4»]
        simp [e₁, e₂, ub₁, ub₂, eq, Lynx.Term.true]
      · exfalso
        have F₁ := F₁ C
        have F₂ := F₂ C
        generalize Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) (.atom "true") = x₁
          at F₁ hok
        generalize Elixir.Module.Types.Descr.«fun_apply/3» (D depth) «fun» (Lynx.Term.list l) (.atom "false") = x₂
          at F₂ hok
        cases x₁ with
        | error err => simp at hok
        | ok v₁ =>
          simp only [Lynx.Except.ok_bind] at hok
          split at hok
          · exact F₁ _ rfl
          · simp only [pure, Except.pure, Lynx.Except.ok_bind] at hok
            cases x₂ with
            | error err => simp at hok
            | ok v₂ =>
              simp only [Lynx.Except.ok_bind] at hok
              split at hok
              · exact F₂ _ rfl
              · simp at hok
      """
  end
end
