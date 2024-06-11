#use "topfind";;
#require "smtml";;
#install_printer Smtml.Expr.pp;;
open Smtml

type expr = Smtml.Expr.t
type time = int

type r = {
    a : int;
    b : int;
    address : expr;
    value : expr;
    condition : expr;
    time : time;
  }

type m = {
    records : r list;
    time : time;
  }

(* type concrete = expr * time *)

(* type m' = { *)
(*     concrete : concrete array; *)
(*     records : r list; *)
(*     time : time; *)
(*   } *)


let empty = { records = []; time = 0 }

let true_ = Smtml.Expr.make (Val True)

let ty_i32 = Smtml.Ty.Ty_bitv 32

let ite a b c =
  Smtml.Expr.triop Ty_bool Ite a b c

let eq a b =
  Smtml.Expr.relop Ty_bool Eq a b

let gt a b =
  Smtml.Expr.relop ty_i32 Gt a b
let ge a b =
  Smtml.Expr.relop ty_i32 Ge a b

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

module O = Smtml.Optimizer.Z3
module B = Solver.Z3_batch

let batch_solver = B.create ()

let optimizer = O.create ()

let to_int i =
  match Int32.unsigned_to_int i with
  | None -> assert false
  | Some i -> i

let max_ e =
  O.push optimizer;
  let r = match O.maximize optimizer e with
  | None -> assert false
  | Some (Num (I32 i)) -> to_int i
  in
  O.pop optimizer;
  r

let min_ e =
  O.push optimizer;
  let r = match O.minimize optimizer e with
  | None -> assert false
  | Some (Num (I32 i)) -> to_int i
  in
  O.pop optimizer;
  r

let equiv e1 e2 =
  match B.check batch_solver [not_ (eq e1 e2)] with
  | `Unknown
  | `Sat -> false
  | `Unsat -> true

let in_range a b x =
  let not_in_range =
    x.b > b || x.a < a
  in
  not not_in_range
(* x.b <= b && x.a >= a *)

let store m ~address ~value =
  let a = min_ address in
  let b = max_ address in
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
  { records = r :: records; time }

let load m ~address =
  let a = min_ address in
  let b = max_ address in
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
  |> store ~address:(n 3) ~value:(n 40)

let s s =
  let open Smtml in
  Expr.mk_symbol (Symbol.make ty_i32 s)

let va = s "a"
let vi = s "i"
let vj = s "j"

let a_addr = n 1
let i_addr = n 2
let j_addr = n 3

let m =
  empty
  |> store ~address:a_addr ~value:va
  |> store ~address:i_addr ~value:vi
  |> store ~address:j_addr ~value:vj

let m1 =
  store ~address:(add vi va) ~value:(n 23) m

let m2 =
  store ~address:(add vi va) ~value:(n 44) m1

let v = load m2 ~address:(add vi va)




(** Boom *)

let va = s "a"
let vi = s "i"
let vj = s "j"
let () = B.add batch_solver [gt va (n 100)]
let () = B.add batch_solver [ge vi (n 0)]
let () = B.add batch_solver [ge vj (n 0)]
let () = O.add optimizer [gt va (n 100)]
let () = O.add optimizer [ge vi (n 0)]
let () = O.add optimizer [ge vj (n 0)]


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

