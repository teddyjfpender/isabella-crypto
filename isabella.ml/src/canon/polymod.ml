(** Polynomial ring arithmetic over Z_q[X]/(f(X))
    Generated from Canon/Rings/PolyMod.thy *)

type poly = int list

let zero_poly = []

let const_poly c = if c = 0 then [] else [c]

let poly_degree p = if p = [] then 0 else List.length p - 1

let poly_coeff p i = if i < List.length p then List.nth p i else 0

let poly_add p q =
  let n = max (List.length p) (List.length q) in
  List.init n (fun i -> poly_coeff p i + poly_coeff q i)

let poly_neg p = List.map (fun x -> -x) p

let poly_sub p q = poly_add p (poly_neg q)

let poly_scale c p = List.map (( * ) c) p

let poly_mult_coeff p q k =
  let rec sum acc j =
    if j > k then acc
    else sum (acc + poly_coeff p j * poly_coeff q (k - j)) (j + 1)
  in sum 0 0

let poly_mult p q =
  if p = [] || q = [] then []
  else List.init (List.length p + List.length q - 1) (poly_mult_coeff p q)

(** Reduce polynomial mod X^n + 1 *)
let rec poly_mod p n =
  if List.length p <= n then
    p @ List.init (n - List.length p) (fun _ -> 0)
  else
    let lo, hi = (List.filteri (fun i _ -> i < n) p,
                  List.filteri (fun i _ -> i >= n) p) in
    let neg_hi = List.map (fun x -> -x) hi in
    let padded = neg_hi @ List.init (n - List.length neg_hi) (fun _ -> 0) in
    poly_mod (poly_add lo padded) n

let ring_mod_coeff p q = List.map (fun x -> x mod q) p

let ring_mod p n q = ring_mod_coeff (poly_mod p n) q

let ring_mult p q n modq = ring_mod (poly_mult p q) n modq

let ring_add p q n modq = ring_mod (poly_add p q) n modq

let ring_sub p q n modq = ring_mod (poly_sub p q) n modq

type ring_params = { ring_n : int; ring_q : int }

let make_ring_params n q = { ring_n = n; ring_q = q }

let valid_ring_params p = p.ring_n > 0 && p.ring_q > 1

let valid_ring_elem params p =
  List.length p = params.ring_n &&
  List.for_all (fun c -> c >= 0 && c < params.ring_q) p
