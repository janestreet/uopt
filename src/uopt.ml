open Base
module Obj = Stdlib.Obj
module Obj_local = Base.Exported_for_specific_uses.Obj_local

type +'a t

(* This [Obj.magic] is OK because we never allow user code access to [none] (except via
   [unsafe_value]).  We disallow [_ Uopt.t Uopt.t], so there is no chance of confusing
   [none] with [some none].  And [float Uopt.t array] is similarly disallowed. *)
let none : _ t = Obj.magic "Uopt.none"

let[@inline] some (x : 'a) =
  let r : 'a t = Obj.magic x in
  if phys_equal r none then failwith "Uopt.some Uopt.none";
  r
;;

let[@inline] some_local (type a) (x : a) : a t =
  let r : a t = Obj_local.magic x in
  if phys_equal r none then failwith "Uopt.Local.some Uopt.none";
  r
;;

let unsafe_value : 'a t -> 'a = Obj.magic
let unsafe_value_local : 'a t -> 'a = Obj_local.magic
let[@inline] is_none t = phys_equal t none
let[@inline] is_some t = not (is_none t)
let[@inline] invariant invariant_a t = if is_some t then invariant_a (unsafe_value t)
let[@inline] value_exn t = if is_none t then failwith "Uopt.value_exn" else unsafe_value t
let[@inline] value t ~default = Bool.select (is_none t) default (unsafe_value t)

let[@inline] value_local t ~default =
  Bool.select (is_none t) default (unsafe_value_local t)
;;

let[@inline] some_if cond x = Bool.select cond (some x) none
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

let[@inline] of_option opt =
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
    let is_none = is_none
    let unsafe_value = unsafe_value
  end
end

module Local = struct
  let some = some_local
  let unsafe_value = unsafe_value_local
  let value = value_local
  let some_if = some_if_local
  let to_option = to_option_local
  let of_option = of_option_local

  module Optional_syntax = struct
    module Optional_syntax = struct
      let is_none = is_none
      let unsafe_value = unsafe_value_local
    end
  end
end

let globalize globalize_a t =
  match%optional.Local t with
  | None -> none
  | Some x -> some (globalize_a x)
;;

let%test_module _ =
  (module struct
    let%test_unit ("using the same sentinel value" [@tags "no-js"]) =
      match some "Uopt.none" with
      | (_ : string t) -> failwith "should not have gotten to this point"
      | exception _ -> ()
    ;;
  end)
;;
