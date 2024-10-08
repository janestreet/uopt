open Base
module Obj = Stdlib.Obj
module Obj_local = Base.Exported_for_specific_uses.Obj_local

type +'a t

(* Note: Clients rely on the fact that various functions in this file will not have an
   OCaml safepoint inserted in their prelude. In particular, [is_some], [some], [none] and
   [unsafe_value] must be safepoint free due to uses in clients like [thread_safe_queue]
   and [nano_mutex].
*)

(* Having [%loc_LOC] (statically allocated string) as [none : 'a t] is OK because we never
   allow user code access to [none] as ['a] except via [unsafe_value].  We disallow [_
   Uopt.t Uopt.t], so there is no chance of confusing [none] with [some none].  And [float
   Uopt.t array] is similarly disallowed. *)

external __LOC__ : _ t = "%loc_LOC"

let none : _ t = __LOC__

let[@inline] [@zero_alloc] some (x : 'a) =
  let r : 'a t = Obj.magic x in
  if phys_equal r none then failwith "Uopt.some Uopt.none";
  r
;;

let[@inline] some_local (type a) (x : a) : a t =
  let r : a t = Obj_local.magic x in
  if phys_equal r none then failwith "Uopt.Local.some Uopt.none";
  r
;;

let[@inline] [@zero_alloc] unsafe_value (t : 'a t) : 'a = Obj.magic t
let unsafe_value_local : 'a t -> 'a = Obj_local.magic
let[@inline] [@zero_alloc] is_none t = phys_equal t none
let[@inline] [@zero_alloc] is_some t = not (is_none t)
let[@inline] invariant invariant_a t = if is_some t then invariant_a (unsafe_value t)

let[@inline] [@zero_alloc] value_exn t =
  if is_none t then failwith "Uopt.value_exn" else unsafe_value t
;;

let[@inline] [@zero_alloc] value t ~default =
  Bool.select (is_none t) default (unsafe_value t)
;;

let[@inline] value_local t ~default =
  Bool.select (is_none t) default (unsafe_value_local t)
;;

let[@inline] [@zero_alloc] some_if cond x = Bool.select cond (some x) none
let[@inline] some_if_local cond x = Bool.select cond (some_local x) none

(* [to_option] prioritizes not allocating in the [None] case. Allocation is far cheaper
   for [to_option_local], so it instead prioritizes minimizing unpredictable branches. *)

let[@inline] to_option t = if is_none t then None else Some (unsafe_value t)

let[@inline] to_option_local t =
  Bool.select (is_none t) None (Some (unsafe_value_local t))
;;

let[@inline] of_option_local opt =
  match opt with
  | None -> none
  | Some x -> some_local x
;;

let[@inline] [@zero_alloc] of_option opt =
  match opt with
  | None -> none
  | Some a -> some a
;;

(* Note [sexp_of_t] and [t_of_sexp] must remain stable; see [Uopt_core.Stable]. *)
include
  Sexpable.Of_sexpable1
    (Option)
    (struct
      type nonrec 'a t = 'a t

      let to_sexpable = to_option
      let of_sexpable = of_option
    end)

module Optional_syntax = struct
  module Optional_syntax = struct
    let[@zero_alloc] is_none t = is_none t
    let[@zero_alloc] unsafe_value t = unsafe_value t
  end
end

module Local = struct
  let[@zero_alloc] some t = some_local t
  let[@zero_alloc] unsafe_value t = unsafe_value_local t
  let[@zero_alloc] value t ~default = value_local t ~default
  let[@zero_alloc] some_if cond x = some_if_local cond x
  let to_option = to_option_local
  let[@zero_alloc] of_option t = of_option_local t

  module Optional_syntax = struct
    module Optional_syntax = struct
      let[@zero_alloc] is_none t = is_none t
      let[@zero_alloc] unsafe_value t = unsafe_value_local t
    end
  end
end

let globalize globalize_a t =
  match%optional.Local t with
  | None -> none
  | Some x -> some (globalize_a x)
;;

module%test _ = struct
  let%test_unit ("using the same sentinel value" [@tags "no-js"]) =
    match some "File \"uopt.ml\", line 20, characters 17-24" with
    | (_ : string t) -> failwith "should not have gotten to this point"
    | exception _ -> ()
  ;;
end
