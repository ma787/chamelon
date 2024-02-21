type keys = int32 list
type pl = string
type node = Lf of keys * pl list * bool * int * int | Il of keys * pl list * node list * bool * int * int

exception MalformedTree of string
exception NotFound of string
exception NullTree of string
exception TreeCapacityNotMet of string
exception NoSpace

module IdSet = Set.Make(Int)

let sizeof_pointer = 4

module Attrs = struct
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
  | Il (_, _, _, _, _, id) -> id
  | Lf (_, _, _, _, id) -> id

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
  end


module Storage = struct
  let pointers = ref (List.map Int32.of_int (List.init 1000 (fun i -> i)));;
  let storage = ref [];;
  let ids = ref [];;

  let take_pointer pointers =
    if !pointers=[] then raise NoSpace
    else let p = List.hd !pointers in
    let newp = List.tl !pointers in
    pointers := newp;
    p

  let take_rev_pointer pointers =
    if !pointers=[] then raise NoSpace
    else let rev_pointers = List.rev !pointers in
    let p = List.hd rev_pointers in
    let newp = List.rev (List.tl rev_pointers) in
    pointers := newp;
    p
  
  let take_spec_pointer p pointers =
    if not (List.mem p !pointers) then raise NoSpace
    else let newp = List.filter (fun i -> not (Int32.equal i p)) !pointers in
    pointers := newp
  
  let read pointer =
    List.assoc pointer !storage
  
  let write (pointer, cs) =
    let current = !storage in
    let news = List.filter (fun (p, _) -> not (Int32.equal pointer p)) current in
    storage := (pointer, cs)::news
  
  let store_id (id, pointer) =
    let current = !ids in
    let newi = List.filter ((fun (i, _) -> id != i)) current in
    ids := (id, pointer)::newi
  
  let remove_id id =
    let current = !ids in
    let newi = List.filter (fun (i, _) -> id != i) current in
    ids := newi
  
  let find_first_free_id ids =
    let ilist, _ = List.split !ids in
    let s = IdSet.of_list ilist in
    let max_id = IdSet.max_elt s in
    let free_ids set max = IdSet.(diff (of_list (List.init max (fun i -> i))) set) in
    let free = free_ids s max_id in
    if IdSet.is_empty free then (max_id+1)
    else IdSet.find_first (fun i -> i=i) free

  let get_or_take_id_pointer pointers ks ids i =
    try
      List.assoc i !ids
    with Not_found ->
      let free = List.rev (List.filter (fun i -> not (List.mem i ks)) !pointers) in
      let p = List.hd free in
      take_spec_pointer p pointers;
      store_id (i, p);
      p
  
  let get_cpointers ks cn =
    let cn_ids = List.map Attrs.get_id cn in
    List.map (fun i -> get_or_take_id_pointer pointers ks ids i) cn_ids (* gets the pointers to the head blocks of the child nodes *)
  
  let deallocate pointer =
    let newp = pointer::(!pointers) in
    pointers := List.sort_uniq Int32.compare newp
  end
    


module Serial = struct
  let head_block_into_cstruct block_size tree cpointer =
    let nk = Attrs.n_keys tree in
    let cs = Cstruct.create block_size in
    Cstruct.LE.set_uint32 cs 0 (Int32.of_int (Attrs.get_id tree)); (* id of this node *)
    Cstruct.LE.set_uint32 cs sizeof_pointer cpointer; (* pointer to block containing child node pointers *)
    Cstruct.LE.set_uint32 cs (2*sizeof_pointer) (Int32.of_int nk); (* number of keys in this node*)
    let keys = Attrs.get_keys tree in
    for n=0 to nk-1 do
      Cstruct.LE.set_uint32 cs ((n+3)*sizeof_pointer) (List.nth keys n);
    done;
    cs
  
  let data_block_into_cstruct block_size pl =
    let cs = Cstruct.create block_size in
    Cstruct.blit_from_string pl 0 cs 0 (String.length pl);
    cs
  
  let store_pl block_size k p =
    let cs = data_block_into_cstruct block_size p in
    Storage.write (k, cs)
  
  (* finds an existing pointer for a head block or gives it one (that doesn't collide with a key) and stores an (id, pointer) entry *)
  let child_block_into_cstruct block_size cpointers =
    let cs = Cstruct.create block_size in
    for n=0 to (List.length cpointers - 1) do
      Cstruct.LE.set_uint32 cs (n*sizeof_pointer) (List.nth cpointers n);
    done;
    cs
  
  let rec to_cstruct block_size pointers ks ids tree =
    let id = Attrs.get_id tree in
    let pointer = Storage.get_or_take_id_pointer pointers ks ids id in
    let cn = Attrs.get_cn tree in
    let cblockpointer = if cn!=[] then Storage.take_rev_pointer pointers else Int32.max_int in (* if this is a leaf node then child block pointer set to null *)
    let hdblock = head_block_into_cstruct block_size tree cblockpointer in
    Storage.write (pointer, hdblock); (* stores the head block of this b-tree node *)
    if cn != [] then 
      let cblock = child_block_into_cstruct block_size (Storage.get_cpointers ks cn) in 
      Storage.write (cblockpointer, cblock);
      List.iter (to_cstruct block_size pointers ks ids) cn
    else () (* stores the child block of this b-tree node *)
  
  let cpointer_from_head_block_cs tree =
    let id = Attrs.get_id tree in
    let pointer = List.assoc id !Storage.ids in
    let hblock = Storage.read pointer in
    Cstruct.LE.get_uint32 hblock sizeof_pointer
  
  let rec read_pointers cs acc n lim off =
    if n<lim then acc
    else let p = Cstruct.LE.get_uint32 cs (n*sizeof_pointer + off) in
    read_pointers cs (p::acc) (n-1) lim off
  
  let of_data_block_cstruct pointer = 
    let cs = List.assoc pointer !Storage.storage in
    Cstruct.to_string cs
  
  let of_child_block_cstruct pointer n =
    let cs = List.assoc pointer !Storage.storage in
    read_pointers cs [] n 0 0
  
  let rec of_cstruct t pointer =
    let hdblock = List.assoc pointer !Storage.storage in
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
  end

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

let write_new_node block_size allks tree =
  let id = Attrs.get_id tree in
  let id_pointer = Storage.get_or_take_id_pointer Storage.pointers allks Storage.ids id in
  let leaf = Attrs.is_leaf tree in
  if not leaf then
    let cn = Attrs.get_cn tree in
    let cpointers = Storage.get_cpointers allks cn in
    let cblockpointer = (try Serial.cpointer_from_head_block_cs tree with Not_found -> Storage.take_rev_pointer Storage.pointers) in (* does this work? *)
    Storage.write (cblockpointer, Serial.child_block_into_cstruct block_size cpointers);
    Storage.write (id_pointer, Serial.head_block_into_cstruct block_size tree cblockpointer);
    Storage.store_id (id, id_pointer)
  else
    Storage.write (id_pointer, Serial.head_block_into_cstruct block_size tree Int32.max_int);
    Storage.store_id (id, id_pointer)

(* adds a key and child to a node *)
(* key must not already be in the node *)
let rec update_node block_size allks tree k c1 c2 = match tree with
| Il (v::next, pl::pls, c::cn, r, t, id) -> 
  if Attrs.is_leaf c1 != Attrs.is_leaf c then
    raise (MalformedTree "child type mismatch")
  else if Attrs.get_hd c1 = Attrs.get_hd c then
    Il (k::v::next, ""::pl::pls, c1::c2::cn, r, t, id)
  else restore (update_node block_size allks (Il (next, pls, cn, r, t, id)) k c1 c2) v pl c
| Il ([], [], c::cn, r, t, id) -> (* right-most node *)
  if Attrs.is_leaf c1 != Attrs.is_leaf c then 
    raise (MalformedTree "child type mismatch")
  else if Attrs.get_hd c1 = Attrs.get_hd c then 
    Il (k::[], ""::[], c1::c2::cn, r, t, id)
  else raise (MalformedTree "child node to split not found")
| _ -> raise (MalformedTree "must be internal node with >1 child")

(* splits a root node into three *)
(* resulting in a new root and increasing the tree depth by 1 *)
let split_root block_size allks tree =
let write_new_root tr =
  let id = Attrs.get_id tr in
  let pointer = List.assoc id !Storage.ids in
  let c = Serial.cpointer_from_head_block_cs tr in
  let cpointer = if c = Int32.max_int then Storage.take_rev_pointer Storage.pointers else c in
  let hblock = Serial.head_block_into_cstruct block_size tr cpointer in
  let cblock = Serial.child_block_into_cstruct block_size (Storage.get_cpointers allks (Attrs.get_cn tr)) in
  Storage.write (pointer, hblock); (* overwrite old head block *)
  Storage.write (cpointer, cblock); tr in (* overwrite old child block and return root *)
let id1 = Storage.find_first_free_id Storage.ids in
match tree with
| Il (ks, pls, c::cn, true, t, id) -> 
  let mk, mp = List.nth ks (t-1), List.nth pls (t-1) in
  let tl = Il (get_left ks 0 (t-1), get_left pls 0 (t-1), c::(get_left cn 0 (t-1)), false, t, id1) in
  write_new_node block_size allks tl;
  let id2 = Storage.find_first_free_id Storage.ids in
  let tr = Il (get_right ks 0 (t-1), get_right pls 0 (t-1), get_right (c::cn) 0 (t-1), false, t, id2) in
  write_new_node block_size allks tr;
  write_new_root (Il (mk::[], mp::[], tl::tr::[], true, t, id))
| Lf (ks, pls, _, t, id) -> 
  let mk, mp = List.nth ks (t-1), List.nth pls (t-1) in
  let tl = Lf (get_left ks 0 (t-1), get_left pls 0 (t-1), false, t, id1) in
  write_new_node block_size allks tl;
  let id2 = Storage.find_first_free_id Storage.ids in
  let tr = Lf (get_right ks 0 (t-1), get_right pls 0 (t-1), false, t, id2) in
  write_new_node block_size allks tr;
  write_new_root (Il (mk::[], mp::[], tl::tr::[], true, t, id))
| _ -> raise (NullTree "")

(* splits a node in two on a given key index *)
(* migrates key to parent node and returns parent, which may now be full *)
let split block_size tree parent allks m =
if Attrs.is_leaf parent then raise (MalformedTree "leaf node cannot be parent")
else let id1 = Storage.find_first_free_id Storage.ids in match tree with
| Il (ks, pls, c::cn, _, t, id) ->
  let mk, mc = List.nth ks m, List.nth cn m in
  let tl = Il (get_left ks 0 m, get_left pls 0 m, get_left_cn (c::cn) 0 m, false, t, id) in
  write_new_node block_size allks tl;
  let tr = Il (get_right ks 0 m, get_right pls 0 m, mc::(get_right cn 0 m), false, t, id1) in
  write_new_node block_size allks tr;
  update_node block_size allks parent mk tl tr
| Lf (ks, pls, _, t, id) ->
  let mk = List.nth ks m in
  let tl = Lf (get_left ks 0 m, get_left pls 0 m, false, t, id) in
  let tr = Lf (get_right ks 0 m, get_right pls 0 m, false, t, id1) in
  let newt = update_node block_size allks parent mk tl tr in
  write_new_node block_size allks newt; newt
| _ -> raise (NullTree "")

(* inserts a given key and payload into the tree *)
let rec insert tree block_size allks k p i = match tree with
| Lf (v::next, pl::pls, r, t, id) ->
  let l = (List.length (v::next) == 2*t-1) in
  if (l && r && not i) then insert (split_root block_size allks tree) block_size allks k p false
  else if (l && not r) then raise (MalformedTree "full node not split ahead of time")
  else if k<v then (Serial.store_pl block_size k p; Lf (k::v::next, ""::pl::pls, r, t, id))
  else if k=v then (Serial.store_pl block_size k p; tree) (* update payload *)
  else if next=[] then (Serial.store_pl block_size k p; Lf (v::k::next, pl::""::pls, r, t, id))
  else restore (insert (Lf (next, pls, r, t, id)) block_size allks k p false) v pl (Lf ([], [], false, 0, 0))
| Lf ([], [], true, t, id) -> Serial.store_pl block_size k p; Lf (k::[], ""::[], true, t, id)
| Il (v::next, pl::pls, c1::c2::cn, r, t, id) -> (* every non-leaf node must have at least 2 children *)
  let l = (List.length(v::next) == 2*t-1) in
  if (l && r && not i) then insert (split_root block_size allks tree) block_size allks k p false (* root is full *)
  else if (l && not r) then raise (MalformedTree "parent node cannot be full")
  else if k<v then match c1 with
    | Il (k1s, _, _, _, _, _) -> 
      if List.length k1s == 2*t-1 then insert (split block_size c1 tree allks (t-1)) block_size allks k p true
      else let c  = insert c1 block_size allks k p false in Il (v::next, pl::pls, c::c2::cn, r, t, id)
    | Lf (k1s, _, _, _, _) -> 
      if List.length k1s == 2*t-1 then insert (split block_size c1 tree allks (t-1)) block_size allks k p true
      else let c  = insert c1 block_size allks k p false in Il (v::next, pl::pls, c::c2::cn, r, t, id)
  else if k=v then (Serial.store_pl block_size k p; Il (v::next, ""::pls, c1::c2::cn, r, t, id)) (* update payload *)
  else if next=[] then match c2 with (* rightmost child *)
    | Il (k2s, _, _, _, _, _) ->
      if List.length k2s == 2*t-1 then insert (split block_size c2 tree allks (t-1)) block_size allks k p true
      else let c  = insert c2 block_size allks k p false in Il (v::next, pl::pls, c1::c::cn, r, t, id)
    | Lf (k2s, _, _, _, _) ->
      if List.length k2s == 2*t-1 then insert (split block_size c2 tree allks (t-1)) block_size allks k p true
      else let c  = insert c2 block_size allks k p false in Il (v::next, pl::pls, c1::c::cn, r, t, id)
  else restore (insert (Il (next, pls, c2::cn, r, t, id)) block_size allks k p false) v pl c1
| _ -> raise (MalformedTree "internal node cannot be empty or without children")

(* takes two child nodes and merges them into one node *)
let rec merge block_size allks parent s1 s2 ignore iroot l = match parent with
| Lf _ -> raise (MalformedTree "leaf node cannot be parent")
| Il (v::next, pl::pls, c1::c2::cn, r, t, id) -> 
  if (c1=s1 && c2=s2) then match s1, s2 with
    | Lf _, Il _ -> raise (MalformedTree "nodes must be at same level")
    | Il _, Lf _ -> raise (MalformedTree "nodes must be at same level")
    | Lf (k1s, p1s, false, _, id1), Lf (k2s, p2s, false, _, id2) ->
    if r && (l + (List.length (v::next)) = 1) && not iroot then
      let id1_pointer = Storage.get_or_take_id_pointer Storage.pointers allks Storage.ids id1 in
      Storage.deallocate id1_pointer;
      Storage.remove_id id1;
      let id2_pointer = Storage.get_or_take_id_pointer Storage.pointers allks Storage.ids id2 in
      Storage.deallocate id2_pointer;
      Storage.remove_id id2; (* node ids id1 and id2 now unused *)
      let tr = Lf (k1s @ (v::k2s), p1s @ (pl::p2s), true, t, id) in
      write_new_node block_size allks tr; tr (* new root can be written to disk *)
    else
      let km, pm = k1s @ (v::k2s), p1s @ (pl::p2s) in (* TODO: concatenate lists without @ *)
      let l = List.length km in 
      if ((l < t-1 || l > 2*t-1) && not ignore) then raise (TreeCapacityNotMet "")
      else let s = Lf (km, pm, false, t, id1) in
      if not ignore then write_new_node block_size allks s; (* can only write new child nodes if this is a real merge and not a steal *)
      let id2_pointer = Storage.get_or_take_id_pointer Storage.pointers allks Storage.ids id2 in
      Storage.deallocate id2_pointer;
      Storage.remove_id id2; (* node id id2 is now unused *)
      Il (next, pls, s::cn, r, t, id) (* cannot write incomplete node to disk *)
    | Il (k1s, p1s, cn1, false, _, id1), Il (k2s, p2s, cn2, false, _, id2) ->
      if r && (l + (List.length (v::next)) = 1) && not iroot then
        let id1_pointer = Storage.get_or_take_id_pointer Storage.pointers allks Storage.ids id1 in
        Storage.deallocate id1_pointer;
        Storage.remove_id id1;
        let id2_pointer = Storage.get_or_take_id_pointer Storage.pointers allks Storage.ids id2 in
        Storage.deallocate id2_pointer;
        Storage.remove_id id2;
        let tr = Il (k1s @ (v::k2s), p1s @ (pl::p2s), cn1 @ cn2, r, t, id) in
        write_new_node block_size allks tr; tr
      else
        let km, pm, cm = k1s @ (v::k2s), p1s @ (pl::p2s), cn1 @ cn2 in
        let l = List.length k1s in
        if (l < t-1 || l > 2*t-1) then raise (TreeCapacityNotMet "")
        else let s = Il (km, pm, cm, false, t, id1) in
        if not ignore then write_new_node block_size allks s;
        let id2_pointer = Storage.get_or_take_id_pointer Storage.pointers allks Storage.ids id2 in
        Storage.deallocate id2_pointer;
        Storage.remove_id id2; (* node id id2 is now unused *)
        Il (next, pls, s::cn, r, t, id)
    | _, _ -> raise (MalformedTree "child nodes cannot be empty")
  else restore (merge block_size allks (Il (next, pls, (c2::cn), r, t, id)) s1 s2 ignore iroot (l+1)) v pl c1
| _ -> raise (NotFound "could not find sibling nodes") (* occurs if s1 and s2 are not child nodes of given parent *)

let rec find_predecessor tree k i = match tree with
| Lf (v::next, _::pls, r, t, pi) ->
  if i then
    if next=[] then v
    else find_predecessor (Lf (next, pls, r, t, pi)) k i (* find largest key in leaf node *)
  else
    if k=v then raise (NotFound "") (* the predecessor is higher in the tree **)
    else if next=[] then raise (NotFound "key not found")
    else if List.hd next = k then v
    else find_predecessor (Lf (next, pls, r, t, pi)) k i
| Il (v::next, _::pls, c1::c2::cn, r, t, pi) ->
  if not i then
    if k=v then find_predecessor c1 k true
    else if k<v then find_predecessor c1 k i
    else if (next=[] || k < List.hd next) then 
      (try find_predecessor c2 k i 
      with (NotFound "") -> v)
    else find_predecessor (Il (next, pls, (c2::cn), r, t, pi)) k i
  else
    if cn=[] then find_predecessor c2 k true
    else find_predecessor (Il (next, pls, (c2::cn), r, t, pi)) k i
| _ -> raise (NotFound "key or predecessor not found")

let rec find_successor tree k i = match tree with
| Lf (v::next, _::pls, r, t, pi) ->
  if i then v
  else if r then
    if next=[] then raise (NotFound "key or successor not found")
    else if k=v then find_successor (Lf (next, pls, r, t, pi)) k true
    else find_successor (Lf (next, pls, r, t, pi)) k i
  else
    if next=[] then 
      if k=v then raise (NotFound "") (* the successor is higher in the tree *)
      else raise (NotFound "key not found")
    else if k=v then find_successor (Lf (next, pls, r, t, pi)) k true
    else find_successor (Lf (next, pls, r, t, pi)) k i
| Il (v::next, _::pls, c1::c2::cn, r, t, pi) -> 
  if not i then
    if k=v then find_successor c2 k true
    else if k<v then 
      (try find_successor c1 k i 
      with (NotFound "") -> v)
    else if next=[] then find_successor c2 k i
    else find_successor (Il (next, pls, (c2::cn), r, t, pi)) k i
  else
    find_successor c1 k i
| _ -> raise (NotFound "key or predecessor not found")

(* swaps the positions of keys 'ok' and 'nk' in a tree *)
(* nk must be either the predecessor or successor of ok and must be at a lower depth *)
let rec swap_i tree ok nk i = match tree with
| Lf (v::next, pl::pls, r, t, pi) ->
  if i then
    if v=nk then Lf (ok::next, pl::pls, r, t, pi)
    else if next=[] then raise (NotFound "at least one key to swap not found")
    else restore (swap_i (Lf (next, pls, r, t, pi)) ok nk i) v pl (Lf ([], [], false, 0, 0))
  else 
    if v=ok then restore (swap_i (Lf (next, pls, r, t, pi)) ok nk true) nk "" (Lf ([], [], false, 0, 0))
    else if next=[] then raise (NotFound "at least one key to swap not found")
    else restore (swap_i (Lf (next, pls, r, t, pi)) ok nk i) v pl (Lf ([], [], false, 0, 0))
| Il (v::next, pl::pls, c1::c2::cn, r, t, pi) ->
  if i then
    if nk<ok then
      if next=[] then Il (v::next, pl::pls, c1::(swap_i c2 ok nk i)::cn, r, t, pi)
      else restore (swap_i (Il (next, pls, (c2::cn), r, t, pi)) ok nk i) v pl c1
    else Il (v::next, pl::pls, (swap_i c1 ok nk i)::c2::cn, r, t, pi)
  else if ok=v then
    if nk>ok then Il (nk::next, pl::pls, c1::(swap_i c2 ok nk true)::cn, r, t, pi)
    else Il (nk::next, pl::pls, (swap_i c1 ok nk true)::c2::cn, r, t, pi)
  else if ok>v then 
    if next=[] then Il (v::next, pl::pls, c1::(swap_i c2 ok nk i)::cn, r, t, pi)
    else restore (swap_i (Il (next, pls, (c2::cn), r, t, pi)) ok nk i) v pl c1
  else Il (v::next, pl::pls, (swap_i c1 ok nk i)::c2::cn, r, t, pi)
| _ -> raise (NotFound "at least one key to swap not found")

let steal block_size allks tree morec = match tree with
| Il (_, _, ca::cb::_, r, t, _) -> 
  let mt = merge block_size allks tree ca cb true r 0 in
  let mc = (match mt with
  | Il (_, _, c::_, _, _, _) -> c
  | _ -> raise (MalformedTree "merge failed")) in
  if ca=morec then split block_size mc mt allks (Attrs.n_keys ca - 1)
  else if cb=morec then split block_size mc mt allks t
  else raise (MalformedTree "child node not found")
| _ -> raise (MalformedTree "must be an internal node with the two specified child nodes")

let rec delete block_size allks tree k i = 
let confirm_write tr = if i=0 then write_new_node block_size allks tr; tr in match tree with
| Il (v::next, pl::pls, ca::cb::cn, r, t, id) -> 
  let l1, l2 = Attrs.(n_keys ca, n_keys cb) in
  if k=v then
    if not (Attrs.is_leaf ca && l1 < t) then let nk = find_predecessor tree v false in (* check left subtree *)
    let newt = swap_i tree v nk false in (match newt with
    | Il (k1s, p1s, c1::cn1, r1, t1, id) -> confirm_write (Il (k1s, p1s, (delete block_size allks c1 k 0)::cn1, r1, t1, id))
    | _ -> raise (MalformedTree "swap failed"))
    else if not (Attrs.is_leaf cb && l2 < t) then let nk = find_successor tree v false in (* check right subtree *)
    let newt = swap_i tree v nk false in (match newt with
    | Il (k1s, p1s, c1::c2::cn1, r1, t1, id) -> confirm_write (Il (k1s, p1s, c1::(delete block_size allks c2 k 0)::cn1, r1, t1, id))
    | _ -> raise (MalformedTree "swap failed"))
    else let mt = merge block_size allks tree ca cb false false 0 in (match mt with (* merge around key to delete and recursively delete it *)
    | Il (k1::k1s, p1::p1s, c1::cn1, r1, t1, id) -> confirm_write (Il (k1::k1s, p1::p1s, (delete block_size allks c1 k 0)::cn1, r1, t1, id))
    | Il ([], [], c1::[], r1, t1, id) -> 
      let tr = Il ([], [], (delete block_size allks c1 k 0)::[], r1, t1, id) in
      if i=0 then write_new_node block_size allks tr; tr
    | Lf (_::_, _::_, true, _, _) -> delete block_size allks mt k 0
    | _ -> raise (MalformedTree "merge failed"))
  else let leftc, rightc = k<v, next=[] in
    if leftc then
      if l1 < t then
        if (l2 >= t) then confirm_write (delete block_size allks (steal block_size allks tree cb) k i) (* steal from right sibling *)
        else let mt = merge block_size allks tree ca cb false false i in (match mt with
        | Il (_::_, _::_, _::_, _, _, _) -> confirm_write (delete block_size allks mt k i)
        | Il ([], [], c1::[], r1, t1, id) -> confirm_write (Il ([], [], (delete block_size allks c1 k 0)::[], r1, t1, id))
        | Lf (_::_, _::_, true, _, _) -> confirm_write (delete block_size allks mt k 0)
        | _ -> raise (MalformedTree "merge failed")) (* merge children and recursively delete *)
        else confirm_write (Il (v::next, pl::pls, (delete block_size allks ca k 0)::cb::cn, r, t, id)) (* check left subtree *)
    else if rightc then
      if l2 < t then
        if (l1 >= t) then confirm_write (delete block_size allks (steal block_size allks tree ca) k i) (* steal from left sibling *)
        else let mt = merge block_size allks tree ca cb false false i in (match mt with
        | Il (_::_, _::_, _::_, _, _, _) -> confirm_write (delete block_size allks mt k i)
        | Il ([], [], c1::[], r1, t1, id) -> confirm_write (Il ([], [], (delete block_size allks c1 k 0)::[], r1, t1, id))
        | Lf (_::_, _::_, true, _, _) -> delete block_size allks mt k 0
        | _ -> raise (MalformedTree "merge failed")) (* merge children and recursively delete *)
        else confirm_write (Il (v::next, pl::pls, ca::(delete block_size allks cb k 0)::cn, r, t, id)) (* check right subtree *)
    else let tr = restore (delete block_size allks (Il (next, pls, (cb::cn), r, t, id)) k (i+1)) v pl ca in (* check next key in node *)
    write_new_node block_size allks tr; tr
| Lf (v::next, pl::pls, r, t, id) ->
  if k=v then confirm_write (Lf (next, pls, r, t, id))
  else if (k>v && next!=[]) then 
    let tr = restore (delete block_size allks (Lf (next, pls, r, t, id)) k (i+1)) v pl (Lf ([], [], false, 0, 0)) in
    write_new_node block_size allks tr; tr
  else raise (NotFound "key to delete not found")
| _ -> raise (MalformedTree ("not an internal node with >1 child"))

let rec insert_list tree block_size keys payloads = match keys, payloads with
| k::ks, pl::pls -> 
  let tr = insert tree block_size (Attrs.get_all_keys tree) k pl false in
  insert_list tr block_size ks pls
| _ -> tree

let rec delete_list block_size tree keys = match keys with
| k::ks -> delete_list block_size (delete block_size (Attrs.get_all_keys tree) tree k 0) ks
| [] -> tree

let create_btree block_size t = let tr = Lf ([], [], true, t, 0) in write_new_node block_size [] tr; tr
