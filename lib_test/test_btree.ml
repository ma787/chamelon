open OUnit2
open Chamelon.Btree

let rec is_valid_tree tree acc = match tree with
| Il (v::next, pl::pls, c::cn, r, t, id) ->
  let lk, lp = List.length (v::next) + acc, List.length (pl::pls) + acc in 
  let lc = if acc=0 then List.length (c::cn) else lk+1 in
  if lk != lp then false
  else if (not r && (lk < (t-1) || lk > (2*t -1))) then false
  else if (not r && (lc < t || lc > 2*t)) || (r && lc<2) then false
  else (is_valid_tree c 0) && (is_valid_tree (Il (next, pls, cn, r, t, id)) (acc+1))
| Il ([], [], c::[], _, _, _) -> is_valid_tree c 0
| Lf (ks, pls, r, t, _) ->
  let lk, lp = List.length ks, List.length pls in
  if lk != lp then false
  else if r then true
  else if lk < (t-1) || lk > (2*t -1) then false
  else true
| _ -> false

let rec payload_match tree items storage = 
  let rec get_pair tree k = match tree with
  | Il (v::next, pl::pls, _::cn, r, t, id) -> if v=k then (v, pl) else get_pair (Il (next, pls, cn, r, t, id)) k
  | Lf (v::next, pl::pls, r, t, id) -> if v=k then (v, pl) else get_pair (Lf (next, pls, r, t, id)) k
  | _ -> raise (NotFound "key not found in node") in match items with
  | (k, pl)::its -> let c = search tree k in 
  let tk, _ = get_pair c k in
  let tp = String.sub (Cstruct.to_string (List.assoc tk (List.rev storage))) 0 (String.length pl) in (* get latest write to storage for this pointer *)
  tk=k && tp=pl && payload_match tree its storage
  | [] -> true

let rec same_tree tr1 tr2 =
  let l1, l2 = Attrs.is_leaf tr1, Attrs.is_leaf tr2 in
  if l1 && l2 then (Attrs.get_keys tr1) = (Attrs.get_keys tr2)
  else if not (l1 || l2) then try
    ((Attrs.get_keys tr1) = (Attrs.get_keys tr2)) && List.fold_left2 (fun acc a b -> acc && (same_tree a b)) true (Attrs.get_cn tr1) (Attrs.get_cn tr2)
  with Invalid_argument _ -> false
  else false

let all_chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
let block_size = 256;;

let of_cs t = Serial.of_cstruct t

let rec random_string n =
  if n=0 then ""
  else let i = Random.int 62 in
  String.make 1 all_chars.[i] ^ random_string (n-1)

let remove_items items toremove = let eq a b = a=b in let m a = not (List.exists (eq a) toremove) in List.filter m items

let rec keys_from_pair items = match items with
| (k, _)::its -> k::(keys_from_pair its)
| [] -> [] 

let rec create_key_list n l = if n=0 then l else let i = Random.int32 (Int32.of_int 800) in if List.mem i l then create_key_list n l else create_key_list (n-1) (i::l)
let rec create_payload_list l = match l with
| _::ks -> (random_string block_size)::(create_payload_list ks)
| [] -> []

let get_test_tree n =
  let t = Random.int 30 in
  let keys = create_key_list n [] in
  let payloads = create_payload_list keys in
  let tree = insert_list (create_btree block_size t) block_size keys payloads in t, tree, (List.combine keys payloads)

let slice l li ui =
let rec drop l n = if n=0 then l else match l with
| _::cs -> drop cs (n-1)
| [] -> raise (Failure "out of range") in
let rec take oldl newl n = if n=0 then newl else match oldl with
| c::cs -> take cs (c::newl) (n-1)
| [] -> raise (Failure "out of range") in
take (drop l li) [] (ui-li)

(* let string_of_pair_list l =
let rec string_of_pairs l = match l with
| (k, pl)::cs -> "(" ^ (string_of_int k) ^ ", " ^ (string_of_int pl) ^ ")" ^ (if cs=[] then "" else ", " ^ (string_of_pairs cs))
| [] -> "" in
"[" ^ (string_of_pairs l) ^ "]" *)

let new_tree t ks pls = insert_list (create_btree block_size t) block_size ks pls;;

let ks = List.map Int32.of_int [63; 16; 51; 77; 61; 43; 57; 12; 44; 72; 45; 34; 20; 7; 93; 29; 58; 59; 60; 62];;
let pls = create_payload_list ks;;
let pairs = List.combine ks pls;;

let tr1 = List.map Int32.of_int [7; 63; 72; 45; 44];;
let pl1 = List.map (fun i -> List.assoc i pairs) tr1;;
let tr2 = tr1 @ (List.map Int32.of_int [34; 60; 12; 29; 16]);;
let pl2 = List.map (fun i -> List.assoc i pairs) tr2;;

let its1 = remove_items pairs (List.combine tr1 pl1);;
let its2 = remove_items pairs (List.combine tr2 pl2);;
let a = new_tree 2 ks pls;;
let a_cs = of_cs 2 (Int32.of_int 999);;
let s = !Storage.storage;;
let a1 = delete_list block_size (new_tree 2 ks pls) tr1;;
let a1_cs = of_cs 2 (Int32.of_int 999);;
let s1 = !Storage.storage;;
let a2 = delete_list block_size (new_tree 2 ks pls) tr2;;
let a2_cs = of_cs 2 (Int32.of_int 999);;
let s2 = !Storage.storage;;
let a3 = insert_list a2 block_size tr2 pl2;;
let a3_cs = of_cs 2 (Int32.of_int 999);;
let s3 = !Storage.storage;;
let a4 = delete_list block_size (new_tree 2 ks pls) ks;; (*starts here *)
let a4_cs = of_cs 2 (Int32.of_int 999);;
let s4 = !Storage.storage;;
let b = new_tree 3 ks pls;;
let b_cs = of_cs 3 (Int32.of_int 999);;
let sb = !Storage.storage;;
let b1 = delete_list block_size (new_tree 3 ks pls) tr1;;
let b1_cs = of_cs 3 (Int32.of_int 999);;
let sb1 = !Storage.storage;;
let b2 = delete_list block_size (new_tree 3 ks pls) tr2;;
let b2_cs = of_cs 3 (Int32.of_int 999);;
let sb2 = !Storage.storage;;
let b3 = insert_list b2 block_size tr2 pl2;;
let b3_cs = of_cs 3 (Int32.of_int 999);;
let sb3 = !Storage.storage;;
let b4 = delete_list block_size (new_tree 3 ks pls) ks;;
let b4_cs = of_cs 3 (Int32.of_int 999);;
let sb4 = !Storage.storage;;
let bf, c, pairs2 = get_test_tree 200;;
let c_cs = of_cs bf (Int32.of_int 999);;
let sc = !Storage.storage;;
let keys2 = keys_from_pair pairs2;;
let pairs2_slice = let n = Random.int 75 in slice pairs2 n (200-n);;
let tr3 = keys_from_pair pairs2_slice;;
let pl3 = List.map (fun i -> List.assoc i pairs2) tr3;;

let pairs3 = remove_items pairs2 pairs2_slice;;
let c1 = delete_list block_size c tr3;;
let c1_cs = of_cs bf (Int32.of_int 999);;
let sc1 = !Storage.storage;;
let c2 = insert_list c1 block_size tr3 pl3;;
let c2_cs = of_cs bf (Int32.of_int 999);;
let sc2 = !Storage.storage;;
let c3 = delete_list block_size c2 keys2;;
let c3_cs = of_cs bf (Int32.of_int 999);;

let tests = "test suite for btree" >::: [
  "inserting a series of elements (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a 0));
  "payloads and keys match (t=2)" >:: (fun _ -> assert_bool "" (payload_match a pairs s));
  "tree structure maintained in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a a_cs));
  "deleting 5 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a1 0));
  "deleting 5 elements maintains tree structure in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a1 a1_cs));
  "deleting 5 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a1 its1 s1));
  "deleting 10 elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a2 0));
  "deleting 10 elements maintains tree structure in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a2 a2_cs));
  "deleting 10 elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a2 its2 s2));
  "reinserting the deleted elements maintains tree structure (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a3 0));
  "reinserting the deleted elements maintains tree structure in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a3 a3_cs));
  "reinserting the deleted elements maintains key/payload pairs (t=2)" >:: (fun _ -> assert_bool "" (payload_match a3 pairs s3));
  "deleting all elements results in valid tree (t=2)" >:: (fun _ -> assert_bool "" (is_valid_tree a4 0));
  "deleting all elements results in empty tree (t=2)" >:: (fun _ -> assert_equal a4 (Lf ([], [], true, 2, 0)));
  "deleting all elements results in empty tree in storage (t=2)" >:: (fun _ -> assert_bool "" (same_tree a4 a4_cs));
  "inserting a series of elements (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b 0));
  "tree structure maintained in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b b_cs));
  "payloads and keys match (t=3)" >:: (fun _ -> assert_bool "" (payload_match b pairs sb));
  "deleting 5 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b1 0));
  "deleting 5 elements maintains tree structure in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b1 b1_cs));
  "deleting 5 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b1 its1 sb1));
  "deleting 10 elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b2 0));
  "deleting 10 elements maintains tree structure in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b2 b2_cs));
  "deleting 10 elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b2 its2 sb2));
  "reinserting the deleted elements maintains tree structure (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b3 0));
  "reinserting the deleted elements maintains tree structure in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b3 b3_cs));
  "reinserting the deleted elements maintains key/payload pairs (t=3)" >:: (fun _ -> assert_bool "" (payload_match b3 pairs sb3));
  "deleting all elements results in valid tree (t=3)" >:: (fun _ -> assert_bool "" (is_valid_tree b4 0));
  "deleting all elements results in empty tree (t=3)" >:: (fun _ -> assert_equal b4 (Lf ([], [], true, 3, 0)));
  "deleting all elements results in empty tree in storage (t=3)" >:: (fun _ -> assert_bool "" (same_tree b4 b4_cs));
  "inserting a series of elements (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c 0));
  "tree structure maintained in storage (random t)" >:: (fun _ -> assert_bool "" (same_tree c c_cs));
  "payloads and keys match (random t)" >:: (fun _ -> assert_bool "" (payload_match c pairs2 sc));
  "deleting random number of elements maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c1 0));
  "deleting random number of elements maintains tree structure in storage (random t)" >:: (fun _ -> assert_bool "" (same_tree c1 c1_cs));
  "deleting random number of elements maintains key/payload pairs (random t)" >:: (fun _ -> assert_bool "" (payload_match c1 pairs3 sc1));
  "reinserting the deleted elements maintains tree structure (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c2 0));
  "reinserting the deleted elements maintains tree structure in storage (random t)" >:: (fun _ -> assert_bool "" (same_tree c2 c2_cs));
  "reinserting the deleted elements maintains key/payload pairs (random t)" >:: (fun _ -> assert_bool "" (payload_match c2 pairs2 sc2));
  "deleting all elements results in valid tree (random t)" >:: (fun _ -> assert_bool "" (is_valid_tree c3 0));
  "deleting all elements results in empty tree (random t)" >:: (fun _ -> assert_equal c3 (Lf ([], [], true, bf, 0)));
  "deleting all elements results in empty tree in storage (random t)" >:: (fun _ -> assert_bool "" (same_tree c3 c3_cs)); 
]

let _ = run_test_tt_main tests
