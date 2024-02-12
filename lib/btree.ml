type keys = int32 list
type pl = string
type node = Lf of keys * pl list * bool * int * int | Il of keys * pl list * node list * bool * int * int

exception MalformedTree of string
exception NotFound of string
exception NullTree of string
exception TreeCapacityNotMet of string
exception NoSpace of string

let sizeof_pointer = 4

let pointers = ref (List.map Int32.of_int (List.init 100 (fun i -> i)));;
let storage = ref [];;
let ids = ref [];;

let take_pointer pointers =
  let p = List.hd !pointers in
  let newp = List.tl !pointers in
  pointers := newp;
  p

let take_spec_pointer p pointers =
  if not (List.mem p !pointers) then raise Not_found
  else let newp = List.filter (fun i -> not (Int32.equal i p)) !pointers in
  pointers := newp

let store (pointer, cs) =
  let current = !storage in
  if List.mem_assoc pointer current then
  let news = List.filter ((fun (p, _) -> pointer != p)) current in
  storage := (pointer, cs)::news
  else storage := (pointer, cs)::current

let store_id (id, pointer) =
  let current = !ids in
  ids := (id, pointer)::current

let rec to_string tree = let ks, ps, cs, root, tval, pointer = match tree with
| Il (k, p, c, r, t, pi) -> k, p, c, r, t, pi
| Lf (k, p, r, t, pi) -> k, p, [], r, t, pi in
let string_of_int32_list l = "[" ^ (List.fold_left (fun acc x ->  acc ^ "0x" ^ Int32.to_string x ^ ",") "" l) ^ "]" in
let string_of_str_list l = "[" ^ (List.fold_left (fun acc x -> acc ^ x ^ ",") "" l) ^ "]" in
let string_of_tree_list l = "[" ^ (List.fold_left (fun acc x -> acc ^ (to_string x) ^ ",") "" l) ^ "]" in
"(Id: " ^ (string_of_int pointer) ^ ", " ^ (string_of_int32_list ks) ^ ", " ^ (string_of_str_list ps) ^ ", " ^ 
(if List.length cs > 0 then ((string_of_tree_list cs) ^ ", ") else "") ^ (string_of_bool root) ^ ", " ^ (string_of_int tval) ^ ")"

let n_keys tree = match tree with
| Il (ks, _, _, _, _, _) -> List.length ks
| Lf (ks, _, _, _, _) -> List.length ks

let is_leaf tree = match tree with
| Il _ -> false
| Lf _ -> true

let is_root tree = match tree with
| Il (_, _, _, r, _, _) -> r
| Lf (_, _, r, _, _) -> r

let get_hd tree = match tree with
| Il (ks, _, _, _, _, _) -> List.hd ks
| Lf (ks, _, _, _, _) -> List.hd ks

let get_keys tree = match tree with
| Il (ks, _, _, _, _, _) -> ks
| Lf (ks, _, _, _, _) -> ks

let get_pls tree = match tree with
| Il (_, pls, _, _, _, _) -> pls
| Lf (_, pls, _, _, _) -> pls

let get_cn tree = match tree with
| Il (_, _, cn, _, _, _) -> cn
| _ -> []

let get_id tree = match tree with
| Il (_, _, _, _, _, pi) -> pi
| Lf (_, _, _, _, pi) -> pi

let get_child_ids tree = match tree with
| Il (_, _, cn, _, _, _) -> List.map get_id cn
| Lf _ -> []

let get_all_ids tree = 
let rec get_id_list tree = match tree with
| Il (_, _, cn, true, _, pi) -> pi::(get_child_ids tree) @ (List.flatten (List.map get_id_list cn))
| Il (_, _, cn, _, _, _) -> (get_child_ids tree) @ (List.flatten (List.map get_id_list cn))
| Lf (_, _, true, _, pi) -> [pi]
| Lf _ -> [] in
List.sort_uniq Int.compare (get_id_list tree)

let get_all_keys tree = 
  let rec get_key_list tree = match tree with
  | Il (ks, _, cn, _, _, _) -> ks @ (List.flatten (List.map get_key_list cn))
  | Lf (ks, _, _, _, _) -> ks in
  List.sort_uniq Int32.compare (get_key_list tree)

let restore tree k p c = match tree with
| Lf ([], [], r, t, pi) -> Lf (k::[], p::[], r, t, pi)
| Lf (v::next, pl::pls, r, t, pi) -> Lf (k::v::next, p::pl::pls, r, t, pi)
| Il ([], [], cn, r, t, pi) -> Il (k::[], p::[], c::cn, r, t, pi)
| Il (v::next, pl::pls, cn, r, t, pi) -> Il (k::v::next, p::pl::pls, c::cn, r, t, pi)
| _ -> raise (MalformedTree "keys/payloads/children mismatch")

(* searches for a node with key k and returns node *)
let rec search tree k = let eq a b = a=b in
let search_next tnode ks nv npl nc  = let tnext = search tnode k in (match tnext with
| Il ([], [], _::[], _, _, _) -> restore tnext nv npl nc
| Il (v::_, _::_, _::_, _, _, _) -> 
  if List.exists (eq v) ks then restore tnext nv npl nc else tnext
| _ -> tnext) in
match tree with
| Il (v::next, pl::pls, c::cn, r, t, pi) -> 
  if k=v then tree
  else if k<v then search c k
  else search_next (Il (next, pls, cn, r, t, pi)) (v::next) v pl c
| Il ([], [], c::[], _, _, _) -> search c k
| Lf (v::next, pl::pls, r, t, pi) ->
  if k=v then tree
  else if k>v then
    if next=[] then raise (NotFound ("key not found"))
    else restore (search (Lf (next, pls, r, t, pi)) k) v pl (Lf ([], [], false, 0, -1))
  else raise (NotFound "key not found")
| _ -> raise (NotFound "key not found")

let rec search_by_id tree p = match tree with
| Il (_::next, _::pls, c::cn, r, t, pi) -> 
  if p=pi then (tree, true) 
  else let (tr1, f1) = search_by_id c p in
    if f1 then (tr1, f1) else search_by_id (Il (next, pls, cn, r, t, pi)) p
| Il (_, _, c::[], _, _, _) -> search_by_id c p
| Lf (_, _, _, _, pi) -> if p=pi then (tree, true) else (tree, false)
| _ -> raise (MalformedTree "")

let rec get_left l i m = match l with
| c::cs -> if i=m then [] else c::(get_left cs (i+1) m)
| [] -> []

let rec get_right l i m = match l with
| c::cs -> 
  if m=(-1) then c::(get_right cs i m)
  else if i=m then get_right cs i (-1)
  else get_right cs (i+1) m
| [] -> []

let rec get_left_cn l i m = match l with
| c::cs -> if i=m then [c] else c::(get_left_cn cs (i+1) m)
| [] -> []

(* adds a key, payload and child to a node *)
(* key must not already be in the node *)
let rec update_node tree k p c1 c2 = match tree with
| Il (v::next, pl::pls, c::cn, r, t, pi) -> (match c1, c with
  | Lf (k1::_, p1::_, _, _, _), Lf (k3::_, p3::_, _, _, _) ->
    if (k1=k3 && p1=p3) then Il (k::v::next, p::pl::pls, c1::c2::cn, r, t, pi)
    else restore (update_node (Il (next, pls, cn, r, t, pi)) k p c1 c2) v pl c
  | Il (k1::_, p1::_, _::_, _, _, _), Il (k3::_, p3::_, _::_, _, _, _) ->
    if (k1=k3 && p1=p3) then Il (k::v::next, p::pl::pls, c1::c2::cn, r, t, pi)
    else restore (update_node (Il (next, pls, cn, r, t, pi)) k p c1 c2) v pl c
  | _ -> raise (MalformedTree "child type mismatch"))
| Il ([], [], c::cn, r, t, pi) -> (match c1, c with (* right-most node *)
  | Lf (k1::_, p1::_, _, _, _), Lf (k3::_, p3::_, _, _, _) ->
    if (k1=k3 && p1=p3) then Il (k::[], p::[], c1::c2::cn, r, t, pi)
    else raise (MalformedTree "child node to split not found")
  | Il (k1::_, p1::_, _::_, _, _, _), Il (k3::_, p3::_, _::_, _, _, _) ->
    if (k1=k3 && p1=p3) then Il (k::[], p::[], c1::c2::cn, r, t, pi)
    else raise (MalformedTree "child node to split not found")
  | _ -> raise (MalformedTree "child type mismatch"))
| _ -> raise (MalformedTree "must be internal node with >1 child")

(* splits a root node into three *)
(* resulting in a new root and increasing the tree depth by 1 *)
let split_root tree ids = match tree, ids with
| Il (ks, pls, c::cn, true, t, pi), pi1::pi2::_ -> 
  let mk, mp = List.nth ks (t-1), List.nth pls (t-1) in
  let tl = Il (get_left ks 0 (t-1), get_left pls 0 (t-1), c::(get_left cn 0 (t-1)), false, t, pi1) in
  let tr = Il (get_right ks 0 (t-1), get_right pls 0 (t-1), get_right (c::cn) 0 (t-1), false, t, pi2) in
  Il (mk::[], mp::[], tl::tr::[], true, t, pi)
| Lf (ks, pls, _, t, pi), pi1::pi2::_ -> let mk, mp = List.nth ks (t-1), List.nth pls (t-1) in
let tl = Lf (get_left ks 0 (t-1), get_left pls 0 (t-1), false, t, pi1) in
let tr = Lf (get_right ks 0 (t-1), get_right pls 0 (t-1), false, t, pi2) in
Il (mk::[], mp::[], tl::tr::[], true, t, pi)
| _, _ -> raise (NullTree "")

(* splits a node in two on a given key index *)
(* migrates key to parent node and returns parent, which may now be full *)
let split tree parent m id =
if is_leaf parent then raise (MalformedTree "leaf node cannot be parent")
else match tree with
| Il (ks, pls, c::cn, _, t, pi) ->
  let mk, mp, mc = List.nth ks m, List.nth pls m, List.nth cn m in
  let tl = Il (get_left ks 0 m, get_left pls 0 m, get_left_cn (c::cn) 0 m, false, t, pi) in
  let tr = Il (get_right ks 0 m, get_right pls 0 m, mc::(get_right cn 0 m), false, t, id) in
  update_node parent mk mp tl tr
| Lf (ks, pls, _, t, pi) ->
  let mk, mp = List.nth ks m, List.nth pls m in
  let tl = Lf (get_left ks 0 m, get_left pls 0 m, false, t, pi) in
  let tr = Lf (get_right ks 0 m, get_right pls 0 m, false, t, id) in
  update_node parent mk mp tl tr
| _ -> raise (NullTree "")

(* inserts a given key and payload into the tree *)
let rec insert tree k p i maxid = match tree with
| Lf (v::next, pl::pls, r, t, pi) ->
  let l = (List.length (v::next) == 2*t-1) in
  if (l && r && not i) then insert (split_root tree (maxid::(maxid+1)::[])) k p false (maxid+2)
  else if (l && not r) then raise (MalformedTree "full node not split ahead of time")
  else if k<v then Lf (k::v::next, p::pl::pls, r, t, pi)
  else if k=v then Lf (v::next, p::pls, r, t, pi) (* update payload *)
  else if next=[] then Lf (v::k::next, pl::p::pls, r, t, pi)
  else restore (insert (Lf (next, pls, r, t, pi)) k p false maxid) v pl (Lf ([], [], false, 0, 0))
| Lf ([], [], true, t, pi) -> Lf (k::[], p::[], true, t, pi)
| Il (v::next, pl::pls, c1::c2::cn, r, t, pi) -> (* every non-leaf node must have at least 2 children *)
  let l = (List.length(v::next) == 2*t-1) in
  if (l && r && not i) then insert (split_root tree (maxid::(maxid+1)::[])) k p false (maxid+2)(* root is full *)
  else if (l && not r) then raise (MalformedTree "parent node cannot be full")
  else if k<v then match c1 with
    | Il (k1s, _, _, _, _, _) -> 
      if List.length k1s == 2*t-1 then insert (split c1 tree (t-1) maxid) k p true (maxid+1)
      else let c  = insert c1 k p false maxid in Il (v::next, pl::pls, c::c2::cn, r, t, pi)
    | Lf (k1s, _, _, _, _) -> 
      if List.length k1s == 2*t-1 then insert (split c1 tree (t-1) maxid) k p true (maxid+1)
      else let c  = insert c1 k p false maxid in Il (v::next, pl::pls, c::c2::cn, r, t, pi)
  else if k=v then Il (v::next, p::pls, c1::c2::cn, r, t, pi) (* update payload *)
  else if next=[] then match c2 with (* rightmost child *)
    | Il (k2s, _, _, _, _, _) ->
      if List.length k2s == 2*t-1 then insert (split c2 tree (t-1) maxid) k p true (maxid+1)
      else let c  = insert c2 k p false maxid in Il (v::next, pl::pls, c1::c::cn, r, t, pi)
    | Lf (k2s, _, _, _, _) ->
      if List.length k2s == 2*t-1 then insert (split c2 tree (t-1) maxid) k p true (maxid+1)
      else let c  = insert c2 k p false maxid in Il (v::next, pl::pls, c1::c::cn, r, t, pi)
  else restore (insert (Il (next, pls, c2::cn, r, t, pi)) k p false maxid) v pl c1
| _ -> raise (MalformedTree "internal node cannot be empty or without children")

(* takes two child nodes and their separating key and merges them into one node *)
let rec merge parent s1 s2 ignore iroot l = match parent with
| Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| Il (v::next, pl::pls, c1::c2::cn, r, t, pi) -> 
  if (c1=s1 && c2=s2) then match s1, s2 with
    | Lf _, Il _ -> raise (MalformedTree "nodes must be at same level")
    | Il _, Lf _ -> raise (MalformedTree "nodes must be at same level")
    | Lf (k1s, p1s, false, _, pi1), Lf (k2s, p2s, false, _, _pi2) ->
    if r && (l + (List.length (v::next)) = 1) && not iroot then 
      Lf (k1s @ (v::k2s), p1s @ (pl::p2s), true, t, pi) (* node ids pi1 and pi2 now unused *)
    else
      let km, pm = k1s @ (v::k2s), p1s @ (pl::p2s) in (* TODO: concatenate lists without @ *)
      let l = List.length km in 
      if ((l < t-1 || l > 2*t-1) && not ignore) then raise (TreeCapacityNotMet "")
      else let s = Lf (km, pm, false, t, pi1) in
      Il (next, pls, s::cn, r, t, pi) (* node id pi2 is now unused *)
    | Il (k1s, p1s, cn1, false, _, pi1), Il (k2s, p2s, cn2, false, _, _pi2) ->
      if r && (l + (List.length (v::next)) = 1) && not iroot then
        Il (k1s @ (v::k2s), p1s @ (pl::p2s), cn1 @ cn2, r, t, pi)
      else
        let km, pm, cm = k1s @ (v::k2s), p1s @ (pl::p2s), cn1 @ cn2 in
        let l = List.length k1s in
        if (l < t-1 || l > 2*t-1) then raise (TreeCapacityNotMet "")
        else let s = Il (km, pm, cm, false, t, pi1) in
        Il (next, pls, s::cn, r, t, pi)
    | _, _ -> raise (MalformedTree "child nodes cannot be empty")
  else restore (merge (Il (next, pls, (c2::cn), r, t, pi)) s1 s2 ignore iroot (l+1)) v pl c1
| _ -> raise (NotFound "could not find sibling nodes") (* occurs if s1 and s2 are not child nodes of given parent *)

let rec find_predecessor tree (k, p) i = match tree with
| Lf (v::next, pl::pls, r, t, pi) ->
  if i then
    if next=[] then (v, pl)
    else find_predecessor (Lf (next, pls, r, t, pi)) (k, p) i (* find largest key in leaf node *)
  else
    if k=v then raise (NotFound "") (* the predecessor is higher in the tree **)
    else if next=[] then raise (NotFound "key not found")
    else if List.hd next = k then (v, pl)
    else find_predecessor (Lf (next, pls, r, t, pi)) (k, p) i
| Il (v::next, pl::pls, c1::c2::cn, r, t, pi) ->
  if not i then
    if k=v then find_predecessor c1 (k, p) true
    else if k<v then find_predecessor c1 (k,p) i
    else if (next=[] || k < List.hd next) then 
      (try find_predecessor c2 (k, p) i 
      with (NotFound "") -> (v, pl))
    else find_predecessor (Il (next, pls, (c2::cn), r, t, pi)) (k, p) i
  else
    if cn=[] then find_predecessor c2 (k, p) true
    else find_predecessor (Il (next, pls, (c2::cn), r, t, pi)) (k, p) i
| _ -> raise (NotFound "key or predecessor not found")

let rec find_successor tree (k, p) i = match tree with
| Lf (v::next, pl::pls, r, t, pi) ->
  if i then (v, pl)
  else if r then
    if next=[] then raise (NotFound "key or successor not found")
    else if k=v then find_successor (Lf (next, pls, r, t, pi)) (k, p) true
    else find_successor (Lf (next, pls, r, t, pi)) (k, p) i
  else
    if next=[] then 
      if k=v then raise (NotFound "") (* the successor is higher in the tree *)
      else raise (NotFound "key not found")
    else if k=v then find_successor (Lf (next, pls, r, t, pi)) (k, p) true
    else find_successor (Lf (next, pls, r, t, pi)) (k, p) i
| Il (v::next, pl::pls, c1::c2::cn, r, t, pi) -> 
  if not i then
    if k=v then find_successor c2 (k, p) true
    else if k<v then 
      (try find_successor c1 (k, p) i 
      with (NotFound "") -> (v, pl))
    else if next=[] then find_successor c2 (k, p) i
    else find_successor (Il (next, pls, (c2::cn), r, t, pi)) (k, p) i
  else
    find_successor c1 (k, p) i
| _ -> raise (NotFound "key or predecessor not found")

(* swaps the positions of keys 'ok' and 'nk' in a tree along with their payloads *)
(* nk must be either the predecessor or successor of ok and must be at a lower depth *)
let rec swap_i tree ok op nk np i = match tree with
| Lf (v::next, pl::pls, r, t, pi) ->
  if i then
    if v=nk then Lf (ok::next, op::pls, r, t, pi)
    else if next=[] then raise (NotFound "at least one key to swap not found")
    else restore (swap_i (Lf (next, pls, r, t, pi)) ok op nk np i) v pl (Lf ([], [], false, 0, 0))
  else 
    if v=ok then restore (swap_i (Lf (next, pls, r, t, pi)) ok op nk np true) nk np (Lf ([], [], false, 0, 0))
    else if next=[] then raise (NotFound "at least one key to swap not found")
    else restore (swap_i (Lf (next, pls, r, t, pi)) ok op nk np i) v pl (Lf ([], [], false, 0, 0))
| Il (v::next, pl::pls, c1::c2::cn, r, t, pi) ->
  if i then
    if nk<ok then
      if next=[] then Il (v::next, pl::pls, c1::(swap_i c2 ok op nk np i)::cn, r, t, pi)
      else restore (swap_i (Il (next, pls, (c2::cn), r, t, pi)) ok op nk np i) v pl c1
    else Il (v::next, pl::pls, (swap_i c1 ok op nk np i)::c2::cn, r, t, pi)
  else if ok=v then
    if nk>ok then Il (nk::next, np::pls, c1::(swap_i c2 ok op nk np true)::cn, r, t, pi)
    else Il (nk::next, np::pls, (swap_i c1 ok op nk np true)::c2::cn, r, t, pi)
  else if ok>v then 
    if next=[] then Il (v::next, pl::pls, c1::(swap_i c2 ok op nk np i)::cn, r, t, pi)
    else restore (swap_i (Il (next, pls, (c2::cn), r, t, pi)) ok op nk np i) v pl c1
  else Il (v::next, pl::pls, (swap_i c1 ok op nk np i)::c2::cn, r, t, pi)
| _ -> raise (NotFound "at least one key to swap not found")

let steal tree morec = match tree with
| Il (_, _, ca::cb::_, r, t, _) -> 
  let cbid = get_id cb in
  let mt = merge tree ca cb true r 0 in
  let mc = (match mt with
  | Il (_, _, c::_, _, _, _) -> c
  | _ -> raise (MalformedTree "merge failed")) in
  if ca=morec then split mc mt (n_keys ca - 1) cbid
  else if cb=morec then split mc mt t cbid
  else raise (MalformedTree "child node not found")
| _ -> raise (MalformedTree "must be an internal node with the two specified child nodes")

let rec delete tree k i = match tree with
| Il (v::next, pl::pls, ca::cb::cn, r, t, pi) -> 
  let l1, l2 = n_keys ca, n_keys cb in
  if k=v then
    if not (is_leaf ca && l1 < t) then let nk, np = find_predecessor tree (v, pl) false in (* check left subtree *)
    let newt = swap_i tree v pl nk np false in (match newt with
    | Il (k1s, p1s, c1::cn1, r1, t1, pi) -> Il (k1s, p1s, (delete c1 k 0)::cn1, r1, t1, pi)
    | _ -> raise (MalformedTree "swap failed"))
    else if not (is_leaf cb && l2 < t) then let nk, np = find_successor tree (v, pl) false in (* check right subtree *)
    let newt = swap_i tree v pl nk np false in (match newt with
    | Il (k1s, p1s, c1::c2::cn1, r1, t1, pi) -> Il (k1s, p1s, c1::(delete c2 k 0)::cn1, r1, t1, pi)
    | _ -> raise (MalformedTree "swap failed"))
    else let mt = merge tree ca cb false false 0 in (match mt with (* merge around key to delete and recursively delete it *)
    | Il (k1::k1s, p1::p1s, c1::cn1, r1, t1, pi) -> Il (k1::k1s, p1::p1s, (delete c1 k 0)::cn1, r1, t1, pi)
    | Il ([], [], c1::[], r1, t1, pi) -> Il ([], [], (delete c1 k 0)::[], r1, t1, pi)
    | Lf (_::_, _::_, true, _, _) -> delete mt k 0
    | _ -> raise (MalformedTree "merge failed"))
  else let leftc, rightc = k<v, next=[] in
    if leftc then
      if l1 < t then
        if (l2 >= t) then delete (steal tree cb) k i (* steal from right sibling *)
        else let mt = merge tree ca cb false false i in (match mt with
        | Il (_::_, _::_, _::_, _, _, _) -> delete mt k i
        | Il ([], [], c1::[], r1, t1, pi) -> Il ([], [], (delete c1 k 0)::[], r1, t1, pi)
        | Lf (_::_, _::_, true, _, _) -> delete mt k 0
        | _ -> raise (MalformedTree "merge failed")) (* merge children and recursively delete *)
        else Il (v::next, pl::pls, (delete ca k 0)::cb::cn, r, t, pi) (* check left subtree *)
    else if rightc then
      if l2 < t then
        if (l1 >= t) then delete (steal tree ca) k i (* steal from left sibling *)
        else let mt = merge tree ca cb false false i in (match mt with
        | Il (_::_, _::_, _::_, _, _, _) -> delete mt k i
        | Il ([], [], c1::[], r1, t1, pi) -> Il ([], [], (delete c1 k 0)::[], r1, t1, pi)
        | Lf (_::_, _::_, true, _, _) -> delete mt k 0
        | _ -> raise (MalformedTree "merge failed")) (* merge children and recursively delete *)
        else Il (v::next, pl::pls, ca::(delete cb k 0)::cn, r, t, pi) (* check right subtree *)
    else restore (delete (Il (next, pls, (cb::cn), r, t, pi)) k (i+1)) v pl ca (* check next key in node *)
| Lf (v::next, pl::pls, r, t, pi) ->
  if k=v then Lf (next, pls, r, t, pi)
  else if (k>v && next!=[]) then restore (delete (Lf (next, pls, r, t, pi)) k (i+1)) v pl (Lf ([], [], false, 0, 0))
  else raise (NotFound "key to delete not found")
| _ -> raise (MalformedTree ("not an internal node with >1 child"))

let rec insert_list tree keys maxid = match keys with
| k::ks -> insert_list (insert tree k "abcdefgh" false maxid) ks (maxid+1) 
| [] -> tree

let rec delete_list tree keys = match keys with
| k::ks -> delete_list (delete tree k 0) ks
| [] -> tree

let create_btree t = Lf ([], [], true, t, 0)

(* finds an existing pointer for a head block or gives it one (that doesn't collide with a key) and stores an (id, pointer) entry *)
let get_or_take_pointer pointers ks ids i =
  try
    List.assoc i !ids
  with Not_found ->
    let free = List.filter (fun i -> not (List.mem i ks)) !pointers in
    let p = List.hd free in
    take_spec_pointer p pointers;
    store_id (i, p);
    p

let head_block_into_cstruct block_size tree cpointer =
  let nk = n_keys tree in
  let cs = Cstruct.create block_size in
  Cstruct.LE.set_uint32 cs 0 (Int32.of_int (get_id tree)); (* id of this node *)
  Cstruct.LE.set_uint32 cs sizeof_pointer cpointer; (* pointer to block containing child node pointers *)
  Cstruct.LE.set_uint32 cs (2*sizeof_pointer) (Int32.of_int nk); (* number of keys in this node*)
  let keys = get_keys tree in
  for n=0 to nk-1 do
    Cstruct.LE.set_uint32 cs ((n+3)*sizeof_pointer) (List.nth keys n);
  done;
  cs

let data_block_into_cstruct block_size pl =
  let cs = Cstruct.create block_size in
  Cstruct.blit_from_string pl 0 cs 0 (String.length pl);
  cs

let child_block_into_cstruct block_size cpointers =
  let cs = Cstruct.create block_size in
  for n=0 to (List.length cpointers - 1) do
    Cstruct.LE.set_uint32 cs (n*sizeof_pointer) (List.nth cpointers n);
  done;
  cs

let rec to_cstruct block_size pointers ks ids tree =
  let rec store_pls ks pls =
    if pls=[] then ()
    else let cs = data_block_into_cstruct block_size (List.hd pls) in
    let k = List.hd ks in
    take_spec_pointer k pointers;
    store (k, cs);
    store_pls (List.tl ks) (List.tl pls) in
  let get_cpointers cn =
    let cn_ids = List.map get_id cn in
    List.map (fun i -> get_or_take_pointer pointers ks ids i) cn_ids in (* gets the pointers to the head blocks of the child nodes *)
  let id = get_id tree in
  let pointer = get_or_take_pointer pointers ks ids id in
  let cn = get_cn tree in
  let cblockpointer = if cn!=[] then take_pointer pointers else Int32.max_int in (* if this is a leaf node then child block pointer set to null *)
  let hdblock = head_block_into_cstruct block_size tree cblockpointer in
  store (pointer, hdblock); (* stores the head block of this b-tree node *)
  store_pls (get_keys tree) (get_pls tree); (* stores the data blocks of the b-tree *)
  if cn != [] then 
    let cblock = child_block_into_cstruct block_size (get_cpointers cn) in 
    store (cblockpointer, cblock);
    List.iter (to_cstruct block_size pointers ks ids) cn
  else () (* stores the child block of this b-tree node *)

let rec read_pointers cs acc n lim off =
  if n<lim then acc
  else let p = Cstruct.LE.get_uint32 cs (n*sizeof_pointer + off) in
  read_pointers cs (p::acc) (n-1) lim off

let of_data_block_cstruct pointer = 
  let cs = List.assoc pointer !storage in
  Cstruct.to_string cs

let of_child_block_cstruct pointer n =
  let cs = List.assoc pointer !storage in
  read_pointers cs [] n 0 0

let rec of_cstruct t pointer =
  let hdblock = List.assoc pointer !storage in
  let id = Int32.to_int (Cstruct.LE.get_uint32 hdblock 0) in
  let cpointer = Cstruct.LE.get_uint32 hdblock sizeof_pointer in
  let nk = Int32.to_int (Cstruct.LE.get_uint32 hdblock (2*sizeof_pointer)) in
  let keys = read_pointers hdblock [] (nk-1) 0 (3*sizeof_pointer) in
  let pls = List.init nk (fun _ -> "") in (* do not read block data from disk *)
  let r = id = 0 in (* root node has id 0 *)
  if cpointer = Int32.max_int then Lf (keys, pls, r, t, id)
  else let cpointers = of_child_block_cstruct cpointer nk in
  let cn = List.map (of_cstruct t) cpointers in
  Il (keys, pls, cn, r, t, id)
