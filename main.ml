exception INVALID_ARGUMENT

let rec nth =
  function (x :: _, 0)  -> x
         | (x :: xs, n) -> nth(xs, n - 1)
         | ([], _)      -> raise INVALID_ARGUMENT

let null s =
  match s with
    | []       -> true
    | (_ :: _) -> false

let rec zip =
  function ([], [])           -> []
         | (x :: xs, y :: ys) -> (x, y) :: zip (xs, ys)
         | (_, _)             -> raise INVALID_ARGUMENT

let rec forall p =
  function []        -> true
         | (x :: xs) -> p x && forall p xs

let rec exists f =
  function []        -> false
         | (y :: ys) -> if f y then true else exists f ys

let rec map f =
  function []        -> []
         | (x :: xs) -> (f x) :: map f xs

let rec concat =
  function []        -> []
         | (x :: xs) -> x @ (concat xs)

let rec allapp f g =
  function []        -> ()
         | (x :: xs) -> f x; g xs; allapp f g xs

type vname = string * int

type term =
  | V of vname
  | T of string * term list

let rec print_term t =
  match t with
    | (V (str, _))
      -> print_string str; ()
    | (T (str, s))
      -> print_string str;
         if null s then () else print_string "(";
         allapp print_term (fun s -> if null s then () else print_string ", ") s;
         if null s then () else print_string ")"

type subst = (vname * term) list

(* get_vname: vname * term -> vname *)
let get_vname vt =
  match vt with
    | (v, t) -> v

(* get_vname: vname * term -> term *)
let get_term vt =
  match vt with
    | (v, t) -> t

let empty_subst = []

(* add_subst: subst -> vname -> term -> subst *)
let add_subst s x t = (x, t) :: s

(* indom: vname -> subst -> bool *)
let indom x s = exists (fun (y, _) -> x = y) s

(* app: subst -> vname -> term *)
let rec app s x =
  match s with
    | (y, t) :: rest -> if x = y then t else app rest x
    | _              -> raise INVALID_ARGUMENT

(* lift: subst -> term -> term *)
let rec lift s t =
  match t with
    | V x       -> if indom x s then app s x else V x
    | T (f, ts) -> T (f, map (lift s) ts)

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
    | ((T (f, ts), T (g, us)) :: rest, s)
      -> if f = g then solve (zip(ts, us) @ rest, s) else raise UNIFY

(* elim: vname -> term -> (term * term) list -> internal_subst -> internal_subst *)
and elim x t rest s =
  let xt = lift (add_subst empty_subst x t) in
    if occurs x t then raise UNIFY
    else solve(map (fun (t1, t2) -> (xt t1, xt t2)) rest,
                 (x, t) :: (map (fun (y, u) -> (y, xt u)) s))

(* unify: term * term -> subst *)
let unify (t1, t2) = solve ([(t1, t2)], [])

(* matchs: (term * term) list -> subst -> subst *)
let rec matchs ttlist s =
  match ttlist with
    | []
      -> s
    | (V x, t) :: rest
      -> if indom x s then if app s x = t then matchs rest s else raise UNIFY
         else matchs rest (add_subst s x t)
    | (t, V x) :: rest
      -> raise UNIFY
    | (T (f, ts), T (g, us)) :: rest
      -> if f = g then matchs (zip (ts, us) @ rest) s else raise UNIFY

(* pattern_match: term * term -> subst *)
let pattern_match pat obj = matchs [(pat, obj)] empty_subst

exception NORM

(* rewrite: (term * term) * list -> term -> term *)
let rec rewrite ttlist t =
  try try_rewrite ttlist t with
    | UNIFY -> retry_rewrite ttlist t

(* try_rewrite: (term * term) * list -> term -> term *)
and try_rewrite ttlist t =
  match ttlist with
    | []               -> raise NORM
    | ((l, r) :: rest) -> lift (pattern_match l t) r

(* retry_rewrite: (term * term) * list -> term -> term *)
and retry_rewrite ttlist t =
  match ttlist with
    | []               -> raise NORM
    | ((l, r) :: rest) -> rewrite rest t

(* norm: (term * term) list -> term *)
let rec norm r t =
  match t with
    | V x       -> V x
    | T (f, ts) -> inner_norm r f ts

(* inner_norm: (term * term) list -> vname -> term list *)
and inner_norm r f ts =
  let u = T (f, map (norm r) ts) in
    try norm r (rewrite r u) with
      | NORM -> u

type order =
  | GR
  | EQ
  | NGE

let int_to_order a = if a > 0 then GR else if a = 0 then EQ else NGE

(* lex: order -> alpha list * beta list -> order *)
let rec lex ord alpha_list_and_beta_list =
  match alpha_list_and_beta_list with
    | ([], [])           -> EQ
    | (x :: xs, y :: ys) -> inner_lex (ord (x, y)) ord xs ys
    | (_, _)             -> raise INVALID_ARGUMENT

(* inner_lex: order -> alpha list -> beta list -> order *)
and inner_lex o ord xs ys =
  match o with
    | GR  -> GR
    | EQ  -> lex ord (xs, ys)
    | NGE -> NGE

(* lpo: (string * string -> order) -> (term * term) -> order *)
let rec lpo ord st =
  match st with
    | (s, V x)
      -> if s = V x then EQ
         else if occurs x s then GR else NGE
    | (V _, T _)
      -> NGE
    | (T (f, ss), T (g, ts))
      -> if forall (fun si -> lpo ord (si, T (g, ts)) = NGE) ss
         then inner_lpo (ord (f, g)) ord (T (f, ss)) ss ts
         else GR

(* lpo: order -> (string * string -> order) -> term -> (term * term) -> order *)
and inner_lpo o ord s ss ts =
  match o with
    | GR
      -> if forall (fun ti -> lpo ord (s, ti) = GR) ts
         then GR else NGE
    | EQ
      -> if forall (fun ti -> lpo ord (s, ti) = GR) ts
      then lex (lpo ord) (ss, ts)
      else NGE
    | NGE
      -> NGE

(* let lpo_functor (t, u) = (lpo (fun (a, b) -> int_to_order (String.compare a b))) (t, u) *)

let lpo_functor (t, u) = print_string "compare "; print_term t; print_string " vs "; print_term u; print_string "\n"; (lpo (fun (a, b) -> print_string a; print_string ", "; print_string b; print_string " = "; print_int (String.compare a b); print_string "\n"; int_to_order (String.compare a b))) (t, u)

(* rename: int -> term -> term *)
let rec rename n =
  function (V (x, i))  -> V (x, i + n)
         | (T (f, ts)) -> T (f, map (rename n) ts)

(* maxs: int list -> int *)
let rec maxs =
  function (i :: is) -> max i (maxs is)
         | []        -> 0

(* maxindex: term -> int *)
let rec maxindex =
  function (V (x, i))  -> i
         | (T (_, ts)) -> maxs (map maxindex ts)

(* ccp: (term -> term) -> term * term -> term * term -> (term * term) list *)
let ccp c tr l2r2 =
  match tr with
    | (t, r) -> match l2r2 with
      | (l2, r2) ->
          try
            [(lift (unify (t, l2)) r, lift (unify (t, l2)) (c r2))]
          with
            | UNIFY -> []

let rec ccps ttlist (l, r) =
  let rec cps c =
    function (V _, _)       -> []
           | (T (f, ts), r) -> concat (map (ccp c (T (f, ts), r)) ttlist) @ (inner_cps c (f, [], ts, r))

    and inner_cps c =
      function (_, _, [], _)         -> []
             | (f, ts0, t :: ts1, r)
               -> let cf s = c (T (f, ts0 @ [s] @ ts1)) in
                    (cps cf (t, r)) @ (inner_cps c (f, ts0 @ [t], ts1, r))

    and m t = rename (maxs (map (fun (ts, us) -> max (maxindex ts) (maxindex us)) ttlist) + 1) t

  in cps (fun t -> t) (m l, m r)

let critical_pairs2 r1 r2 = concat (map (ccps r1) r2)

let critical_pairs r = critical_pairs2 r r

let rec replace context t =
  match context with
    | []                  -> t
    | ((f, ts, us) :: cs) -> replace cs (T (f, ts @ [t] @ us))

type ids = (term * term) list

let rec print_ids ttlist =
  match ttlist with
    | (t, u) :: s -> print_term t; print_string " = "; print_term u; print_string "\n"; print_ids s
    | [] -> ()

exception FAIL

let add_rule (l, r, ids_e, ids_s, ids_r) =
  let rec simpl triple_ids =
    match triple_ids with
      | ([], e', r')
        -> (e', r')
      | ((g, d) :: u, e', u')
        -> let g' = norm [(l, r)] g
             in if g' = g
             then let d' = norm ((l, r) :: ids_r @ ids_s) d
             in simpl (u, e', (g, d') :: u')
             else simpl (u, (g', d) :: ids_e, u')
  in let (e', s') = simpl (ids_s, ids_e, [])
  in let (e'', r') = simpl (ids_r, e', [])
    in (e'', (l, r) :: s', r')

let orient ord =
  let rec ori triple_ids =
    match triple_ids with
      | ([], ids_s, ids_r)
        -> (ids_s, ids_r)
      | ((s, t) :: ids_e, ids_s, ids_r)
        -> let s' = norm (ids_r @ ids_s) s
           and t' = norm (ids_r @ ids_s) t
           in if s' = t' then ori (ids_e, ids_s, ids_r)
                         else if ord (s', t') = GR then ori (add_rule (s', t', ids_e, ids_s, ids_r))
                         else if ord (t', s') = GR then ori (add_rule (t', s', ids_e, ids_s, ids_r))
                         else raise FAIL
  in ori

let rec size t =
  match t with
    | (V _)       -> 1
    | (T (_, ts)) -> sizes ts + 1
  and sizes ts =
    match ts with
      | []        -> 0
      | (t :: ts) -> size t + sizes ts

let rec min_rule tt_i_ids_ids =
  match tt_i_ids_ids with
    | (rl, n, [], r')
      -> (rl, r')
    | (rl, n, (l, r) :: rest, r')
      -> let m = size l + size r
           in if m < n then min_rule ((l, r), m, rest, rl :: r')
                       else min_rule (rl, n, rest, (l, r) :: r')

let choose ttlist =
  match ttlist with
    | ((l, r) :: rest) -> min_rule ((l, r), size l + size r, rest, [])
    | _             -> raise INVALID_ARGUMENT

let complete ord ids_e =
  let rec compl esr =
    match orient ord esr with
      | ([], r')
        -> r'
      | (s', r')
        -> let (rl, s'') = choose s'
           in let cps = critical_pairs2 [rl] r' @
                        critical_pairs2 r' [rl] @
                        critical_pairs2 [rl] [rl]
            in compl (cps, s'', rl :: r')
  in compl (ids_e, [], [])

let ct  name   = T (name, [])
let fn  name s = T (name, s)
let var name   = V (name, 0)

let h x y = fn  "H" [x; y]
let g x y = fn  "G" [x; y]
let f x y = fn  "F" [x; y]
let i x   = fn  "i" [x]
let vx    = var "x"
let vy    = var "y"
let vz    = var "z"
let zero  = ct  "0"
let one   = ct  "1"
let u     = ct  "u"

(* H(H(x, y), z) -> H(x, H(y, z)) *)
let rule1 =
  (h (h vx vy) vz, h vx (h vy vz))

(* H(i(x), x) -> 0 *)
let rule2 =
  (h (i vx) vx, zero)

(* H(0, x) -> x *)
let rule3 =
  (h zero vx, vx)

(* G(G(x, y), z) -> G(x, G(y, z)) *)
let rule4 =
  (g (g vx vy) vz, g vx (g vy vz))

(* G(F(i(x), 1), x) -> 1 *)
let rule5 =
  (g (f (i vx) one) vx, one)

(* G(1, x) -> x *)
let rule6 =
  (g one vx, vx)

(* G(0, x) -> 0 *)
let rule7 =
  (g zero vx, zero)

(* F(x, 0) -> 1 *)
let rule8 =
  (f vx zero, one)

(* F(x, 1) -> x *)
let rule9 =
  (f vx one, vx)

(* G(F(x, y), F(x, z)) -> F(x, H(y, z)) *)
let rule10 =
  (g (f vx vy) (f vx vz), f vx (h vy vz ))

(* H(x, x) -> G(H(1, 1), x) *)
let rule11 =
  (h vx vx, g (h one one) vx)

(* G(x, x) -> F(x, H(1, 1)) *)
let rule12 =
  (g vx vx, f vx (h one one))

let test_complete () = print_ids (complete lpo_functor [
  rule1; rule2; rule3;
  rule4; rule5; rule6;
  rule7; rule8; rule9;
  rule10; rule11; rule12])

let main () = test_complete ();;

main ()

