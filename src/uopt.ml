open Base

type +'a t : immutable_data with 'a

(* Note: Clients rely on the fact that various functions in this file will not have an
   OCaml safepoint inserted in their prelude. In particular, [is_some], [some], [none] and
   [unsafe_value] must be safepoint free due to uses in clients like [thread_safe_queue]
   and [nano_mutex].
*)

(* Having [%loc_LOC] (statically allocated string) as [none : 'a t] is OK because we never
   allow user code access to [none] as ['a] except via [unsafe_value]. We disallow
   [_ Uopt.t Uopt.t], so there is no chance of confusing [none] with [some none]. And
   [float Uopt.t array] is similarly disallowed. *)

external __LOC__ : _ t @@ portable = "%loc_LOC"

let none = __LOC__

let[@inline] get_none : (unit -> 'a t) @ portable =
  fun () -> none |> Portability_hacks.magic_uncontended__promise_deeply_immutable
;;

external%template magic_some
  :  ('a[@local_opt]) @ c p
  -> ('a t[@local_opt]) @ c p
  @@ portable
  = "%obj_magic"
[@@mode p = (portable, nonportable), c = (contended, uncontended)]

let%template[@zero_alloc] some (x @ c p) =
  let r @ c p = (magic_some [@mode p c]) x in
  if phys_equal r (get_none ()) then failwith "Uopt.some Uopt.none";
  r
[@@mode p = (portable, nonportable), c = (contended, uncontended)]
;;

let%template[@inline] some_local (x @ c local p) = exclave_
  let r @ c p = (magic_some [@mode p c]) x in
  if phys_equal r (get_none ()) then failwith "Uopt.Local.some Uopt.none";
  r
[@@mode p = (portable, nonportable), c = (contended, uncontended)]
;;

let[@inline] [@zero_alloc] unsafe_value (t : 'a t) : 'a = Obj.magic t
let unsafe_value_local : local_ 'a t -> local_ 'a = Obj.magic
let[@inline] [@zero_alloc] is_none t = phys_equal t (get_none ())
let[@inline] [@zero_alloc] is_some t = not (is_none t)
let[@inline] invariant invariant_a t = if is_some t then invariant_a (unsafe_value t)

let[@inline] [@zero_alloc] value_exn t =
  if is_none t then failwith "Uopt.value_exn" else unsafe_value t
;;

let[@inline] [@zero_alloc] value t ~default =
  Bool.select (is_none t) default (unsafe_value t)
;;

let[@inline] value_local t ~default = exclave_
  Bool.select (is_none t) default (unsafe_value_local t)
;;

let[@inline] [@zero_alloc] some_if cond x = Bool.select cond (some x) (get_none ())
let[@inline] some_if_local cond x = exclave_ Bool.select cond (some_local x) (get_none ())

(* [to_option] prioritizes not allocating in the [None] case. Allocation is far cheaper
   for [to_option_local], so it instead prioritizes minimizing unpredictable branches. *)

let[@inline] to_option t = if is_none t then None else Some (unsafe_value t)

let[@inline] to_option_local t = exclave_
  Bool.select (is_none t) None (Some (unsafe_value_local t))
;;

let[@inline] of_option_local opt = exclave_
  match opt with
  | None -> get_none ()
  | Some x -> some_local x
;;

let[@inline] [@zero_alloc] of_option opt =
  match opt with
  | None -> get_none ()
  | Some a -> some a
;;

(* Note [sexp_of_t] and [t_of_sexp] must remain stable; see [Uopt_core.Stable]. *)
  include%template
    Sexpable.Of_sexpable1 [@modality portable]
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
  let%template[@zero_alloc] some t = exclave_ (some_local [@mode p c]) t
  [@@mode p = (nonportable, portable), c = (contended, uncontended)]
  ;;

  let[@zero_alloc] unsafe_value t = exclave_ unsafe_value_local t
  let[@zero_alloc] value t ~default = exclave_ value_local t ~default

  let[@inline] [@zero_alloc] value_exn t = exclave_
    if is_none t then failwith "Uopt.Local.value_exn" else unsafe_value t
  ;;

  let[@zero_alloc] some_if cond x = exclave_ some_if_local cond x
  let[@zero_alloc] to_option t = exclave_ to_option_local t
  let[@zero_alloc] of_option t = exclave_ of_option_local t

  module Optional_syntax = struct
    module Optional_syntax = struct
      let[@zero_alloc] is_none t = is_none t
      let[@zero_alloc] unsafe_value t = exclave_ unsafe_value_local t
    end
  end
end

let globalize globalize_a t =
  match%optional.Local t with
  | None -> get_none ()
  | Some x -> some (globalize_a x)
;;

module%test _ = struct
  let%test_unit ("using the same sentinel value" [@tags "no-js"]) =
    match some "File \"uopt.ml\", line 18, characters 11-18" with
    | (_ : string t) -> failwith "should not have gotten to this point"
    | exception _ -> ()
  ;;
end
