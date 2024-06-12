(* #use "topfind";; *)
(* #require "smtml";; *)
(* #install_printer Smtml.Expr.pp;; *)
[@@@ocaml.warning "-32"]
open Smtml

type expr = Expr.t
type time = int

type r = {
    a : int;
    b : int;
    address : expr;
    value : expr;
    condition : expr;
    time : time;
  }

type concrete = expr * time

type m = {
    concrete : concrete array;
    records : r list;
    time : time;
  }

module Utils = struct
  let true_ = Smtml.Expr.make (Val True)

  let ty_i32 = Smtml.Ty.Ty_bitv 32

  let not_ a =
    Smtml.Expr.unop Ty_bool Not a

  let and_ a b =
    (* let ty = Smtml.Ty.Ty_bool in *)
    (* Smtml.Expr.binop ty And a b *)
    Expr.Bool.and_ a b

  let ite a b c =
    if Expr.equal b c then b
    else
      match Expr.view b, Expr.view c with
      | Val True, Val False -> a
      | Val False, Val True -> not_ a
      | _ ->
         Smtml.Expr.triop Ty_bool Ite a b c

  let rec eq a b =
    match Expr.view a, Expr.view b with
    | Triop (Ty_bool, Ite, cond, l, r), Val _ ->
       ite cond (eq l b) (eq r b)
    | Val _, Triop (Ty_bool, Ite, cond, l, r) ->
       ite cond (eq l a) (eq r a)
    | _, _ ->
       Smtml.Expr.relop Ty_bool Eq a b

  let gt a b =
    Smtml.Expr.relop ty_i32 Gt a b
  let ge a b =
    Smtml.Expr.relop ty_i32 Ge a b

  let add a b =
    Smtml.Expr.binop ty_i32 Add a b

  let n x = Smtml.Expr.make (Val (Num (I32 (Int32.of_int x))))

  let zero = Smtml.Expr.make (Val (Num (I32 0l)))
end
open Utils

let empty = {
    concrete = Array.make 10 (zero, 0);
    records = [];
    time = 0;
  }


let to_int i =
  match Int32.unsigned_to_int i with
  | None -> assert false
  | Some i -> i

module Opt = struct
  module O = Optimizer.Z3
  let optimizer = O.create ()

  let max_ e =
    match Expr.view e with
    | Val (Num (I32 i)) -> to_int i
    | Val _ -> assert false
    | _ ->
       O.push optimizer;
       let r = match O.maximize optimizer e with
         | None -> assert false
         | Some (Num (I32 i)) -> to_int i
         | Some _ -> assert false
       in
       O.pop optimizer;
       r

  let min_ e =
    match Expr.view e with
    | Val (Num (I32 i)) -> to_int i
    | Val _ -> assert false
    | _ ->
       O.push optimizer;
       let r = match O.minimize optimizer e with
         | None -> assert false
         | Some (Num (I32 i)) -> to_int i
         | Some _ -> assert false
       in
       O.pop optimizer;
       r

end

let optimizer = Opt.optimizer

module B = Solver.Z3_batch
let batch_solver = B.create ()

let equiv e1 e2 =
  match Expr.view e1, Expr.view e2 with
  | Val _, Val _ -> Expr.equal e1 e2
  | _ ->
     Expr.equal e1 e2 ||
       match B.check batch_solver [not_ (eq e1 e2)] with
       | `Unknown | `Sat -> false
       | `Unsat -> true

let in_range a b x =
  let not_in_range =
    x.b > b || x.a < a
  in
  not not_in_range
(* x.b <= b && x.a >= a *)

let set a i v =
  let a = Array.copy a in
  a.(i) <- v;
  a

let store_concrete m ~address ~value =
  let time = m.time + 1 in
  let concrete = set m.concrete address (value, time) in
  { m with time; concrete }

let store_expr m ~address ~value =
  let a = Opt.min_ address in
  let b = Opt.max_ address in
  let time = m.time + 1 in
  let records =
    List.filter (fun x ->
        not (in_range a b x) ||
          (not (equiv x.address address))
      )
      m.records
  in
  let r = {
      a; b; address; value; condition = true_; time;
    }
  in
  { records = r :: records; time; concrete = m.concrete }

let store m ~address ~value =
  match Expr.view address with
  | Val (Num (I32 i)) ->
     let i = to_int i in
     store_concrete m ~address:i ~value
  | _ ->
     store_expr m ~address ~value

let rec insert ~address value time (records : r list) =
  let[@inline] mk () =
    { a = address; b = address; address = n address; value; condition = true_; time; }
  in
  match records with
  | [] -> [mk ()]
  | h :: t ->
     if h.time < time then
       mk () :: records
     else
       h :: insert ~address value time t

let compare_records (r1:r) (r2:r) = compare r2.time r1.time

let make_ite a b address m =
  let concrete_records =
    let a = max a 0 in
    let b = min b (Array.length m.concrete - 1) in
    let len = max 0 (b - a + 1) in
    List.init len (fun i ->
        let address = a + i in
        let value, time = m.concrete.(address) in
        { a = address; b = address; address = n address; value; condition = true_; time; }
      )
  in
  let compare_records (r1:r) (r2:r) = compare r2.time r1.time in
  let concrete_records =
    List.sort compare_records concrete_records
  in
  let records = List.merge compare_records concrete_records m.records in
  let add_ite (r : r) (expr : expr) =
    let cond =
      and_
        (eq address r.address)
        (r.condition)
    in
    if in_range a b r then
      ite cond r.value expr
    else expr
  in
  List.fold_right add_ite records zero

let load_concrete m ~address =
  make_ite address address (n address) m

let load_expr m ~address =
  let a = Opt.min_ address in
  let b = Opt.max_ address in
  make_ite a b address m

let load m ~address =
  match Expr.view address with
  | Val (Num (I32 i)) ->
     let i = to_int i in
     load_concrete m ~address:i
  | _ ->
     load_expr m ~address

let array_map3 f a1 a2 a3 =
  assert(Array.length a1 = Array.length a2);
  assert(Array.length a1 = Array.length a3);
  Array.mapi (fun i v1 -> f v1 a2.(i) a3.(i)) a1

let array_mapi2 f a1 a2 =
  assert(Array.length a1 = Array.length a2);
  Array.mapi (fun i v1 -> f i v1 a2.(i)) a1

let merge_concrete concrete delta other delta_other =
  let added = ref [] in
  let concrete' =
    let f address (left, left_time) (right, right_time) =
      let value, time =
        if left_time = right_time then
          (* Not completely sure, it depends on what exactly should be the meaning of merge.
             If the state of merge is:
             1) either the value from left or right, no other value possible, then that's ok
             2) if delta_left then value_left
                else if delta_right then value_right
                else value_old
                In that case that single ite is not OK.
             Also in the 1st case having the result forced to value_right doesn't
             carry the property that delta_right holds
           *)
          ite delta left right, left_time
        else begin
            (* Same remark as above for the semantics *)
            if left_time < right_time then
              let r =
                { a = address; b = address; address = n address; value = right; condition = delta_other; time = right_time; }
              in
              added := r :: !added;
              left, left_time
            else
              let r =
                { a = address; b = address; address = n address; value = left; condition = delta; time = left_time; }
              in
              added := r :: !added;
              right, right_time
          end
      in
      value, time
    in
    array_mapi2 f concrete other
  in
  concrete', !added

let merge_records records delta other delta_other time =
  let before, after = List.partition (fun (r:r) -> r.time <= time) records in
  let before_other, after_other = List.partition (fun (r:r) -> r.time <= time) other in
  assert(before = before_other);
  let after = List.map (fun r -> { r with condition = and_ delta r.condition }) after in
  let after_other = List.map (fun r -> { r with condition = and_ delta_other r.condition }) after_other in
  List.concat [after; after_other; before]

let merge (m : m) delta other delta_other time =
  let concrete, added_records = merge_concrete m.concrete delta other.concrete delta_other in
  let records = merge_records m.records delta other.records delta_other time in
  let records = List.merge compare_records added_records records in
  { records; concrete;
    time = max m.time other.time }


(** Boom *)
let s s =
  let open Smtml in
  Expr.mk_symbol (Symbol.make ty_i32 s)

let va = s "a"
let vi = s "i"
let vj = s "j"
let () = B.add batch_solver [gt va (n 100)]
let () = B.add batch_solver [ge vi (n 0)]
let () = B.add batch_solver [ge vj (n 0)]
let () = Opt.O.add optimizer [gt va (n 100)]
let () = Opt.O.add optimizer [ge vi (n 0)]
let () = Opt.O.add optimizer [ge vj (n 0)]


let a_addr = n 1
let i_addr = n 2
let j_addr = n 3
let boom_addr = n 4

let m =
  empty
  |> store ~address:a_addr ~value:va
  |> store ~address:i_addr ~value:vi
  |> store ~address:j_addr ~value:vj

let m1 =
  store ~address:(add vi va) ~value:(n 23) m

let v = load m1 ~address:(add vi va)

let cond =
  eq (load m1 ~address:(add vj va)) (n 23)

(*
    (bool.eq
       (bool.ite (bool.eq (i32.add j a) (i32.add i a))
          (i32 23)
          (bool.ite (bool.eq (i32.add j a) (i32 3))
             j
             (bool.ite (bool.eq (i32.add j a) (i32 2))
                i
                (bool.ite (bool.eq (i32.add j a) (i32 1)) a (i32 0)))))
       (i32 23))
 *)

let m_eq =
  store ~address:(boom_addr) ~value:(n 0) m1

let m_neq =
  store ~address:(boom_addr) ~value:(n 1) m1

let m_merge = merge m_eq cond m_neq (not_ cond) m1.time

let r = load m_merge ~address:boom_addr
