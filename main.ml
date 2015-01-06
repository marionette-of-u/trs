exception INVALID_ARGUMENT

let rec nth =
  function (x :: _, 0)  -> x
         | (x :: xs, n) -> nth(xs, n - 1)
         | ([], _)      -> raise INVALID_ARGUMENT

let rec zip =
  function ([], [])           -> []
         | (x :: xs, y :: ys) -> (x, y) :: zip (xs, ys)
         | (_, _)             -> raise INVALID_ARGUMENT

let rec exists f =
  function []        -> false
         | (y :: ys) -> if f y then true else exists f ys

let rec map f =
  function []        -> []
         | (x :: xs) -> (f x) :: map f xs

let rec concat =
  function []        -> []
         | (x :: xs) -> x @ (concat xs)

type vname = string * int

type term =
  | V of vname
  | T of string * term list

type subst = (vname, term) Hashtbl.t

(* get_vname: vname * term -> vname *)
let get_vname vt =
  match vt with
    | (v, t) -> v

(* get_vname: vname * term -> term *)
let get_term vt =
  match vt with
    | (v, t) -> t

let empty_subst = Hashtbl.create 1

(* add_subst: subst -> vname -> term -> subst *)
let add_subst s x t = Hashtbl.add s x t; s

(* indom: vname -> subst -> bool *)
let indom x s = Hashtbl.mem s x

(* app: subst -> vname -> term *)
let app s v = Hashtbl.find s v

(* lift: subst -> term -> term *)
let rec lift s t =
  match t with
    | V x       -> if indom x s then app s x else V x
    | T (f, ts) -> T(f, map (lift s) ts)

(* occurs: vname -> term -> bool *)
let rec occurs x t =
  match t with
    | V y       -> x = y
    | T (_, ts) -> exists (occurs x) ts

exception UNIFY

(* solve: (term * term) list * internal_subst -> internal_subst *)
let rec solve ttlist_and_subst =
  match ttlist_and_subst with
    | ([], s)
      -> s
    | ((V x, t) :: rest, s)
      -> if V x = t then solve (rest, s) else elim x t rest s
    | ((t, V x) :: rest, s)
      -> elim x t rest s
    | ((T(f, ts), T(g, us)) :: rest, s)
      -> if f = g then solve (zip(ts, us) @ rest, s) else raise UNIFY

(* elim: vname -> term -> (term * term) list -> internal_subst -> internal_subst *)
and elim x t rest s =
  let xt = lift (add_subst empty_subst x t) in
    if occurs x t then raise UNIFY
    else solve(map (fun (t1, t2) -> (xt t1, xt t2)) rest,
                 (x, t) :: (map (fun (y, u) -> (y, xt u)) s))

let internal_subst_to_hashtbl_subst s =
  let tbl = empty_subst in
    for i = 1 to List.length s do
      Hashtbl.add tbl (get_vname (nth (s, i))) (get_term (nth (s, i)))
    done;
    tbl

let unify (t1, t2) =
  internal_subst_to_hashtbl_subst (solve ([(t1, t2)], []))

let main () =
  0;;

main ()

