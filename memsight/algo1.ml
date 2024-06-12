(* #use "topfind";; *)
(* #require "smtml";; *)
(* #install_printer Smtml.Expr.pp;; *)
[@@@ocaml.warning "-32"]
open Smtml

type expr = Smtml.Expr.t
type time = int

type r = {
    address : expr;
    value : expr;
    condition : expr;
    time : time;
  }

type m = {
    records : r list;
    time : time;
  }

let empty = { records = []; time = 0 }

let true_ = Smtml.Expr.make (Val True)

let store m ~address ~value =
  let time = m.time + 1 in
  let r = {
      address; value; condition = true_; time;
    }
  in
  { records = r :: m.records; time }

let ty_i32 = Smtml.Ty.Ty_bitv 32

let ite a b c =
  Smtml.Expr.triop Ty_bool Ite a b c

let eq a b =
  Smtml.Expr.relop Ty_bool Eq a b

let gt a b =
  Smtml.Expr.relop ty_i32 Gt a b

let and_ a b =
  (* let ty = Smtml.Ty.Ty_bool in *)
  (* Smtml.Expr.binop ty And a b *)
  Expr.Bool.and_ a b

let add a b =
  Smtml.Expr.binop ty_i32 Add a b

let not_ a =
  Smtml.Expr.unop Ty_bool Not a

let n x = Smtml.Expr.make (Val (Num (I32 (Int32.of_int x))))

let zero = Smtml.Expr.make (Val (Num (I32 0l)))

let load m ~address =
  let add_ite (r : r) (expr : expr) =
    let cond =
      and_
        (eq address r.address)
        (r.condition)
    in
    ite cond r.value expr
  in
  List.fold_right add_ite m.records zero

let merge (m : m) delta other delta_other time =
  let before, after = List.partition (fun (r:r) -> r.time <= time) m.records in
  let before_other, after_other = List.partition (fun (r:r) -> r.time <= time) other.records in
  assert(before = before_other);
  let after = List.map (fun r -> { r with condition = and_ delta r.condition }) after in
  let after_other = List.map (fun r -> { r with condition = and_ delta_other r.condition }) after_other in
  { records = List.concat [after; after_other; before];
    time = max m.time other.time }

let m =
  empty
  |> store ~address:(n 1) ~value:(n 10)
  |> store ~address:(n 2) ~value:(n 20)
  |> store ~address:(n 3) ~value:(n 30)

let v =
  load m ~address:(n 2)

let m1 =
  m
  |> store ~address:(n 4) ~value:(n 40)
  |> store ~address:(n 5) ~value:(n 50)
  |> store ~address:(n 6) ~value:(n 60)

let m2 =
  m
  |> store ~address:(n 4) ~value:(n 41)
  |> store ~address:(n 5) ~value:(n 51)
  |> store ~address:(n 6) ~value:(n 61)

let s s =
  let open Smtml in
  Expr.mk_symbol (Symbol.make ty_i32 s)

let v = s "v"

let c1 = gt v (n 10)
let c2 = not_ c1

let m3 = merge m1 c1 m2 c2 m.time

let v =
  load m3 ~address:(n 2)

let v =
  load m3 ~address:(n 4)

(** Boom *)

let va = s "a"
let vi = s "i"
let vj = s "j"

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

module S = Solver.Z3_incremental

let solver = Solver.Z3_incremental.create ()

let () = S.push solver
let () = S.add solver [(eq r (n 0))]
let c = S.check solver []
let v = S.get_value solver vi
let v' = S.get_value solver vj
let () = S.pop solver 1

