type keys = int32 list
type pl = string
type node = Lf of keys * pl list * bool * int * int | Il of keys * pl list * node list * bool * int * int

exception MalformedTree of string
exception NotFound of string
exception NullTree of string
exception TreeCapacityNotMet of string
exception NoSpace

open Lwt.Infix

module Make(Sectors: Mirage_block.S) = struct
  module This_Block = Block_ops.Make(Sectors)
  let sizeof_pointer = 4

  type error = [
    | `Not_found
    | `No_space
  ]

  module IdSet = Set.Make(Int)

  module Attrs = struct
    let rec to_string tree = let ks, ps, cs, root, bfval, pointer = match tree with
    | Il (k, p, c, r, bf, pi) -> k, p, c, r, bf, pi
    | Lf (k, p, r, bf, pi) -> k, p, [], r, bf, pi in
    let string_of_int32_list l = "[" ^ (List.fold_left (fun acc x ->  acc ^ "0x" ^ Int32.to_string x ^ ",") "" l) ^ "]" in
    let string_of_str_list l = "[" ^ (List.fold_left (fun acc x -> acc ^ x ^ ",") "" l) ^ "]" in
    let string_of_tree_list l = "[" ^ (List.fold_left (fun acc x -> acc ^ (to_string x) ^ ",") "" l) ^ "]" in
    "(Id: " ^ (string_of_int pointer) ^ ", " ^ (string_of_int32_list ks) ^ ", " ^ (string_of_str_list ps) ^ ", " ^ 
    (if List.length cs > 0 then ((string_of_tree_list cs) ^ ", ") else "") ^ (string_of_bool root) ^ ", " ^ (string_of_int bfval) ^ ")"

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
    end

  module Ids = struct
    let ids = ref []
    let store_id (id, (hpointer, cblockpointer)) =
      let current = !ids in
      let newi = List.filter ((fun (i, _) -> id != i)) current in
      ids := (id, (hpointer, cblockpointer))::newi
    
    let find_first_free_id ids =
      let ilist, _ = List.split !ids in
      let s = IdSet.of_list ilist in
      let max_id = IdSet.max_elt s in
      let free_ids set max = IdSet.(diff (of_list (List.init max (fun i -> i))) set) in
      let free = free_ids s max_id in
      if IdSet.is_empty free then (max_id+1)
      else IdSet.find_first (fun i -> i=i) free

    let get_node_pointers_from_id id = List.assoc id !ids

    let get_all_pointers l =
      let rec list_from_pair_list plist acc = match plist with
      | (h, c)::prs -> list_from_pair_list prs (h::c::acc)
      | [] -> acc in
      let _ids, pointer_pairs = List.split !ids in
      list_from_pair_list pointer_pairs l
      
    let remove_id id =
      let current = !ids in
      let newi = List.filter (fun (i, _) -> id != i) current in
      ids := newi (* deallocate elsewhere *)
    end

  module Serial = struct
    let write_block t pointer cs =
      This_Block.write t pointer [cs] >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> Lwt.return (Ok ())
    
    let rec read_pointers cs acc n lim =
      if n<lim then acc
      else let p = Cstruct.LE.get_uint32 cs (n*sizeof_pointer) in
      read_pointers cs (p::acc) (n-1) lim
    
    let write_data_block_from_pl t block_size pointer next pl =
      let cs = Cstruct.create block_size in
      Cstruct.LE.set_uint32 cs 0 next;
      Cstruct.blit_from_string pl 0 cs sizeof_pointer (String.length pl);
      write_block t pointer cs
    
    let read_data_block t block_size pointer =
      let cs = Cstruct.create block_size in
      This_Block.read t pointer [cs] >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> let p, s = Cstruct.LE.get_uint32 cs 0, Cstruct.to_string ~off:sizeof_pointer cs in
      Lwt.return @@ Ok (p, s)
    
    (* finds an existing pointer for a head block or gives it one (that doesn't collide with a key) and stores an (id, pointer) entry *)
    let write_child_block t block_size cblockpointer cpointers =
      let cs = Cstruct.create block_size in
      for n=0 to (List.length cpointers - 1) do
        Cstruct.LE.set_uint32 cs (n*sizeof_pointer) (List.nth cpointers n);
      done;
      write_block t cblockpointer cs
    
    let read_child_block t block_size cblockpointer n =
      let cs = Cstruct.create block_size in
      This_Block.read t cblockpointer [cs] >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> let cpointers = read_pointers cs [] n 0 in
      Lwt.return @@ Ok cpointers
      
    let write_head_block t block_size tree hpointer cpointer =
      let nk = Attrs.n_keys tree in
      let cs = Cstruct.create block_size in
      Cstruct.LE.set_uint32 cs 0 (Int32.of_int (Attrs.get_id tree)); (* id of this node *)
      Cstruct.LE.set_uint32 cs sizeof_pointer cpointer; (* pointer to block containing child node pointers *)
      Cstruct.LE.set_uint32 cs (2*sizeof_pointer) (Int32.of_int nk); (* number of keys in this node*)
      let keys = Attrs.get_keys tree in
      for n=0 to nk-1 do
        Cstruct.LE.set_uint32 cs ((n+3)*sizeof_pointer) (List.nth keys n);
      done;
      write_block t hpointer cs

    let rec of_cstruct t block_size bf pointer =
      let rec get_cn cpointers acc = match cpointers with
      | c::cl -> of_cstruct t block_size bf (Int64.of_int32 c) >>= (function
        | Error _ as e -> Lwt.return e
        | Ok (tr) -> get_cn cl (tr::acc))
      | [] -> Lwt.return @@ Ok (acc) in
      let hblock = Cstruct.create block_size in
      This_Block.read t pointer [hblock] >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> 
        let id = Int32.to_int (Cstruct.LE.get_uint32 hblock 0) in
        if (pointer=2L && id != 1) then Lwt.return @@ Ok (Lf ([], [], true, bf, 1))
        else let cblockpointer = Cstruct.LE.get_uint32 hblock sizeof_pointer in
        let nk = Int32.to_int (Cstruct.LE.get_uint32 hblock (2*sizeof_pointer)) in
        let keys = List.sort Int32.compare (read_pointers hblock [] ((nk-1) + 3) 3) in
        let pls = List.init nk (fun _ -> "") in (* do not read block data from disk *)
        let r = id = 1 in (* root node has id 1 *)
        if Int32.equal cblockpointer Int32.max_int then Lwt.return @@ Ok (Lf (keys, pls, r, bf, id))
        else read_child_block t block_size (Int64.of_int32 cblockpointer) nk >>= (function
        | Error _ as e -> Lwt.return e
        | Ok (cpointers) -> get_cn cpointers [] >>= (function
        | Error _ as e -> Lwt.return e
        | Ok (cn_list) -> 
          let cn = List.sort (fun tr1 tr2 -> Int32.compare (Attrs.get_hd tr1) (Attrs.get_hd tr2)) cn_list in
          Lwt.return @@ Ok (Il (keys, pls, cn, r, bf, id))))
    end

  module Block_ops = struct
    let add_key_to_head_block t block_size hpointer k =
      let hblock = Cstruct.create block_size in
      This_Block.read t hpointer [hblock] >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> 
        let nk = Int32.to_int (Cstruct.LE.get_uint32 hblock (2*sizeof_pointer)) in
        Cstruct.LE.set_uint32 hblock (2*sizeof_pointer) (Int32.of_int (nk+1));
        Cstruct.LE.set_uint32 hblock ((nk+3)*sizeof_pointer) k;
        Lwt.return @@ Ok hblock
    
    let remove_key_from_head_block t block_size hpointer k =
      let hblock = Cstruct.create block_size in
      This_Block.read t hpointer [hblock] >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> 
        let nk = Int32.to_int (Cstruct.LE.get_uint32 hblock (2*sizeof_pointer)) in
        let keys = List.sort Int32.compare (Serial.read_pointers hblock [] (nk+2) 3) in
        let newk = List.filter (fun i -> not (Int32.equal k i)) keys in
        Cstruct.LE.set_uint32 hblock ((nk+2)*sizeof_pointer) Int32.zero;
        for n=0 to (nk-2) do
          Cstruct.LE.set_uint32 hblock ((n+3)*sizeof_pointer) (List.nth newk n);
        done;
        Cstruct.LE.set_uint32 hblock (2*sizeof_pointer) (Int32.of_int (nk-1));
        Lwt.return @@ Ok hblock
    
    let replace_key_in_head_block t block_size hpointer ok newk =
      let hblock = Cstruct.create block_size in
      This_Block.read t hpointer [hblock] >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> 
        let nk = Int32.to_int (Cstruct.LE.get_uint32 hblock (2*sizeof_pointer)) in
        let keys = List.sort Int32.compare (Serial.read_pointers hblock [] (nk+2) 3) in
        let newks = List.filter (fun i -> not (Int32.equal ok i)) keys in
        Cstruct.LE.set_uint32 hblock ((nk+2)*sizeof_pointer) newk;
        for n=0 to (nk-2) do
          Cstruct.LE.set_uint32 hblock ((n+3)*sizeof_pointer) (List.nth newks n);
        done;
        Cstruct.LE.set_uint32 hblock (2*sizeof_pointer) (Int32.of_int (nk-1));
        Lwt.return @@ Ok hblock
    
    let add_cpointer_to_child_block t block_size cblockpointer cpointer nk =
      let cblock = Cstruct.create block_size in
      This_Block.read t cblockpointer [cblock] >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> Cstruct.LE.set_uint32 cblock ((nk+1)*sizeof_pointer) cpointer; Lwt.return @@ Ok (cblock)
    
    let remove_cpointer_from_child_block t block_size cblockpointer cpointer nk =
      let cblock = Cstruct.create block_size in
      This_Block.read t cblockpointer [cblock] >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> 
        let cpointers = Serial.read_pointers cblock [] nk 0 in
        let newc = List.filter (fun i -> not (Int32.equal cpointer i)) cpointers in
        Cstruct.LE.set_uint32 cblock (((List.length (cpointers))-1)*sizeof_pointer) Int32.zero;
        for n=0 to (List.length newc)-1 do
          Cstruct.LE.set_uint32 cblock (n*sizeof_pointer) (List.nth newc n);
        done;
        Lwt.return @@ Ok cblock
    end

  module Node_writes = struct
    (* gets the pointers to the head blocks of every node in cn *)
    let get_cpointers cn =
      let cn_ids = List.map Attrs.get_id cn in
      let cn_pointer_pairs = List.map (fun i -> List.assoc i !Ids.ids) cn_ids in
      let _hpointers, cpointers = List.split cn_pointer_pairs in cpointers

    let write_internal_node t block_size hpointer cblockpointer tree =
      let id = Attrs.get_id tree in
      let cn = Attrs.get_cn tree in
      let cpointers = get_cpointers cn in
      Serial.write_head_block t block_size tree (Int64.of_int32 hpointer) cblockpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> Serial.write_child_block t block_size (Int64.of_int32 cblockpointer) cpointers >>= function
        | Error _ as e -> Lwt.return e
        | Ok () -> Ids.store_id (id, (hpointer, cblockpointer)); Lwt.return (Ok ())
    
    let write_leaf_node t block_size hpointer tree =
      let id = Attrs.get_id tree in
      Serial.write_head_block t block_size tree (Int64.of_int32 hpointer) Int32.max_int >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> Ids.store_id (id, (hpointer, Int32.max_int)); Lwt.return (Ok ())
    
    let get_node_split_update t block_size hpointer cblockpointer nk k cpointer =
      Block_ops.add_cpointer_to_child_block t block_size cblockpointer cpointer nk >>= function
      | Error _ as e -> Lwt.return e
      | Ok cblock -> Block_ops.add_key_to_head_block t block_size hpointer k >>= function
        | Error _ as e -> Lwt.return e
        | Ok hblock -> Lwt.return @@ Ok (hblock, cblock)
    
    let write_node_split_update t hpointer cblockpointer hblock cblock =
      Serial.write_block t hpointer hblock >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> Serial.write_block t cblockpointer cblock >>= function
        | Error _ as e -> Lwt.return e
        | Ok () -> Lwt.return @@ (Ok ())

    let node_split_update t block_size hpointer cblockpointer nk k cpointer =
      get_node_split_update t block_size (Int64.of_int32 hpointer) (Int64.of_int32 cblockpointer) nk k cpointer >>= function
      | Error _ -> Lwt.return @@ Error `No_space
      | Ok (hblock, cblock) -> write_node_split_update t (Int64.of_int32 hpointer) (Int64.of_int32 cblockpointer) hblock cblock >>= (function
        | Ok () -> Lwt.return (Ok ())
        | Error _ -> Lwt.return @@ Error `No_space)
  end

  let restore tree k p c = match tree with
  | Lf ([], [], r, bf, id) -> Lf (k::[], p::[], r, bf, id)
  | Lf (v::next, pl::pls, r, bf, id) -> Lf (k::v::next, p::pl::pls, r, bf, id)
  | Il ([], [], cn, r, bf, id) -> Il (k::[], p::[], c::cn, r, bf, id)
  | Il (v::next, pl::pls, cn, r, bf, id) -> Il (k::v::next, p::pl::pls, c::cn, r, bf, id)
  | _ -> raise (MalformedTree "keys/payloads/children mismatch")

  (* searches for a node with key k and returns node *)
  let rec search tree k = let eq a b = a=b in
  let search_next tnode ks nv npl nc  = let tnext = search tnode k in (match tnext with
  | Il ([], [], _::[], _, _, _) -> restore tnext nv npl nc
  | Il (v::_, _::_, _::_, _, _, _) -> 
    if List.exists (eq v) ks then restore tnext nv npl nc else tnext
  | _ -> tnext) in
  match tree with
  | Il (v::next, pl::pls, c::cn, r, bf, id) -> 
    if k=v then tree
    else if k<v then search c k
    else search_next (Il (next, pls, cn, r, bf, id)) (v::next) v pl c
  | Il ([], [], c::[], _, _, _) -> search c k
  | Lf (v::next, pl::pls, r, bf, id) ->
    if k=v then tree
    else if k>v then
      if next=[] then raise (NotFound ("key not found"))
      else restore (search (Lf (next, pls, r, bf, id)) k) v pl (Lf ([], [], false, 0, -1))
    else raise (NotFound "key not found")
  | _ -> raise (NotFound "key not found")

  let rec search_by_id tree i = match tree with
  | Il (_::next, _::pls, c::cn, r, bf, id) -> 
    if id=i then (tree, true) 
    else let (tr1, f1) = search_by_id c i in
      if f1 then (tr1, f1) else search_by_id (Il (next, pls, cn, r, bf, id)) i
  | Il (_, _, c::[], _, _, _) -> search_by_id c i
  | Lf (_, _, _, _, id) -> if id=i then (tree, true) else (tree, false)
  | _ -> raise (MalformedTree "")

  (* adds a key and child to a node *)
  (* key must not already be in the node *)
  let rec update_node block_size tree k c1 c2 = match tree with
  | Il (v::next, pl::pls, c::cn, r, bf, id) -> 
    if Attrs.is_leaf c1 != Attrs.is_leaf c then
      raise (MalformedTree "child type mismatch")
    else if Attrs.get_hd c1 = Attrs.get_hd c then
      Il (k::v::next, ""::pl::pls, c1::c2::cn, r, bf, id)
    else restore (update_node block_size (Il (next, pls, cn, r, bf, id)) k c1 c2) v pl c
  | Il ([], [], c::cn, r, bf, id) -> (* right-most node *)
    if Attrs.is_leaf c1 != Attrs.is_leaf c then 
      raise (MalformedTree "child type mismatch")
    else if Attrs.get_hd c1 = Attrs.get_hd c then 
      Il (k::[], ""::[], c1::c2::cn, r, bf, id)
    else raise (MalformedTree "child node to split not found")
  | _ -> raise (MalformedTree "must be internal node with >1 child")

  (* splits a root node into three, resulting in a new root and increasing the tree depth by 1 *)
  (* hpointers : [left_pointer, right_pointer] *)
  (* cblockpointers: [left_child_pointer, right_child_pointer] *)
  let split_root t block_size hpointers cblockpointers tree =
  let id1 = Ids.find_first_free_id Ids.ids in match tree with
  | Il (ks, pls, c::cn, true, bf, id) -> 
    (let mk, mp = List.nth ks (bf-1), List.nth pls (bf-1) in
    let tl = Il (Attrs.get_left ks 0 (bf-1), Attrs.get_left pls 0 (bf-1), c::(Attrs.get_left cn 0 (bf-1)), false, bf, id1) in
    Node_writes.write_internal_node t block_size (List.hd hpointers) (List.hd cblockpointers) tl >>= function
    | Error _ as e -> Lwt.return e
    | Ok () -> 
      let id2 = Ids.find_first_free_id Ids.ids in
      let tr = Il (Attrs.get_right ks 0 (bf-1), Attrs.get_right pls 0 (bf-1), Attrs.get_right (c::cn) 0 (bf-1), false, bf, id2) in
      Node_writes.write_internal_node t block_size (List.hd (List.tl hpointers)) (List.hd (List.tl cblockpointers)) tr >>= (function
      | Error _ as e -> Lwt.return e
      | Ok () ->
        let newr = (Il (mk::[], mp::[], tl::tr::[], true, bf, id)) in
        let hpointer, cblockpointer = Ids.get_node_pointers_from_id id in
        Node_writes.write_internal_node t block_size hpointer cblockpointer newr >>= (function
        | Error _ as e -> Lwt.return e
        | Ok () -> 
          Ids.store_id (id1, (List.hd hpointers, List.hd cblockpointers));
          Ids.store_id (id2, (List.hd (List.tl hpointers), List.hd (List.tl cblockpointers)));
          Lwt.return @@ Ok (newr))))
  | Lf (ks, pls, _, bf, id) -> 
    (let mk, mp = List.nth ks (bf-1), List.nth pls (bf-1) in
    let tl = Lf (Attrs.get_left ks 0 (bf-1), Attrs.get_left pls 0 (bf-1), false, bf, id1) in
    Node_writes.write_leaf_node t block_size (List.hd hpointers) tl >>= function
    | Error _ as e -> Lwt.return e
    | Ok () ->
      let id2 = Ids.find_first_free_id Ids.ids in
      let tr = Lf (Attrs.get_right ks 0 (bf-1), Attrs.get_right pls 0 (bf-1), false, bf, id2) in
      Node_writes.write_leaf_node t block_size (List.hd (List.tl hpointers)) tr >>= (function
      | Error _ as e -> Lwt.return e
      | Ok () ->
        let newr = (Il (mk::[], mp::[], tl::tr::[], true, bf, id)) in
        let hpointer, cblockpointer = Ids.get_node_pointers_from_id id in
        Node_writes.write_internal_node t block_size hpointer cblockpointer newr >>= (function
        | Error _ as e -> Lwt.return e
        | Ok () -> 
          Ids.store_id (id1, (List.hd hpointers, List.hd cblockpointers));
          Ids.store_id (id2, (List.hd (List.tl hpointers), List.hd (List.tl cblockpointers)));
          Lwt.return @@ Ok (newr))))
  | _ -> raise (NullTree "")

  (* splits a node in two on a given key index *)
  (* migrates key to parent node and returns parent, which may now be full *)
  (* hpointers : [left_pointer, right_pointer, parent_pointer] *)
  (* cblockpointers: [left_child_pointer, right_child_pointer, parent_child_pointer] *)
  let split t block_size nhpointer ncblockpointer tree parent m =
  if Attrs.is_leaf parent then raise (MalformedTree "leaf node cannot be parent")
  else let id1 = Ids.find_first_free_id Ids.ids in 
  let hpointer, cblockpointer = Ids.get_node_pointers_from_id (Attrs.get_id tree) in
  let phpointer, pcblockpointer = Ids.get_node_pointers_from_id (Attrs.get_id parent) in match tree with
  | Il (ks, pls, c::cn, _, bf, id) ->
    (let mk, mc = List.nth ks m, List.nth cn m in
    let tl = Il (Attrs.get_left ks 0 m, Attrs.get_left pls 0 m, Attrs.get_left_cn (c::cn) 0 m, false, bf, id) in
    Node_writes.write_internal_node t block_size hpointer cblockpointer tl >>= function
    | Error _ -> Lwt.return @@ Error `No_space
    | Ok () -> 
      let tr = Il (Attrs.get_right ks 0 m, Attrs.get_right pls 0 m, mc::(Attrs.get_right cn 0 m), false, bf, id1) in
      Node_writes.write_internal_node t block_size nhpointer ncblockpointer tr >>= (function
      | Error _ -> Lwt.return @@ Error `No_space
      | Ok () ->
        let nk = Attrs.n_keys parent in
        Node_writes.node_split_update t block_size phpointer pcblockpointer nk mk nhpointer >>= (function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok () ->
          let updated = update_node block_size parent mk tl tr in
          Ids.store_id (id1, (nhpointer, ncblockpointer));
          Lwt.return @@ Ok (updated))))
  | Lf (ks, pls, _, bf, id) ->
    (let mk = List.nth ks m in
    let tl = Lf (Attrs.get_left ks 0 m, Attrs.get_left pls 0 m, false, bf, id) in
    Node_writes.write_leaf_node t block_size hpointer tl >>= function
    | Error _ -> Lwt.return @@ Error `No_space
    | Ok () ->
      let tr = Lf (Attrs.get_right ks 0 m, Attrs.get_right pls 0 m, false, bf, id1) in
      Node_writes.write_leaf_node t block_size nhpointer tr >>= (function
      | Error _ -> Lwt.return @@ Error `No_space
      | Ok () -> 
        let nk = Attrs.n_keys parent in
        Node_writes.node_split_update t block_size phpointer pcblockpointer nk mk nhpointer >>= (function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok () ->
          let updated = update_node block_size parent mk tl tr in
          Ids.store_id (id1, (nhpointer, ncblockpointer));
          Lwt.return @@ Ok (updated))))
  | _ -> raise (NullTree "")

  (* inserts a given key and payload into the tree *)
  let rec insert t block_size tree k i pointers =
    match tree with
  | Lf (v::next, pl::pls, r, bf, id) ->
    let l = (List.length (v::next) == 2*bf-1) in
    if (l && r && not i) then (match pointers with
      | p1::p2::ps -> split_root t block_size [p1; p2] [Int32.max_int; Int32.max_int] tree >>= (function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (tr) -> insert t block_size tr k false ps)
      | _ -> Lwt.return @@ Error `No_space)
    else if (l && not r) then raise (MalformedTree "full node not split ahead of time")
    else if k<v then Lwt.return @@ Ok (Lf (k::v::next, ""::pl::pls, r, bf, id), id, false, pointers)
    else if k=v then Lwt.return @@ Ok (tree, id, true, pointers) (* update payload *)
    else if next=[] then Lwt.return @@ Ok (Lf (v::k::next, pl::""::pls, r, bf, id), id, false, pointers)
    else insert t block_size (Lf (next, pls, r, bf, id)) k false pointers >>= (function
      | Error _ -> Lwt.return @@ Error `No_space
      | Ok (tr, tr_id, update, ps) -> 
        let r_tr = restore tr v pl (Lf ([], [], false, 0, 0)) in
        Lwt.return @@ Ok (r_tr, tr_id, update, ps))
  | Lf ([], [], true, bf, id) -> Lwt.return @@ Ok (Lf (k::[], ""::[], true, bf, id), id, false, pointers)
  | Il (v::next, pl::pls, c1::c2::cn, r, bf, id) -> (* every non-leaf node must have at least 2 children *)
    let l = (List.length(v::next) == 2*bf-1) in
    if (l && r && not i) then (
      if Attrs.is_leaf c1 then (match pointers with
        | p1::p2::ps -> split_root t block_size [p1; p2] [Int32.max_int; Int32.max_int] tree >>= (function
          | Error _ -> Lwt.return @@ Error `No_space
          | Ok (tr) -> insert t block_size tr k false ps)
        | _ -> Lwt.return @@ Error `No_space)
      else match pointers with
      | p1::p2::p3::p4::ps -> split_root t block_size [p1; p2] [p3; p4] tree >>= (function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (tr) -> insert t block_size tr k false ps)
      | _ -> Lwt.return @@ Error `No_space) (* root is full *)
    else if (l && not r) then raise (MalformedTree "parent node cannot be full")
    else if k<v then match c1 with
      | Il (k1s, _, _, _, _, _) -> 
        if List.length k1s == 2*bf-1 then (match pointers with
          | p1::p2::ps -> split t block_size p1 p2 c1 tree (bf-1) >>= (function
            | Error _ -> Lwt.return @@ Error `No_space
            | Ok (tr) -> insert t block_size tr k true ps)
          | _ -> Lwt.return @@ Error `No_space)
        else insert t block_size c1 k false pointers >>= (function 
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (c, c_id, update, ps) -> Lwt.return @@ Ok (Il (v::next, pl::pls, c::c2::cn, r, bf, id), c_id, update, ps))
      | Lf (k1s, _, _, _, _) -> 
        if List.length k1s == 2*bf-1 then (match pointers with
          | p1::ps -> split t block_size p1 Int32.max_int c1 tree (bf-1) >>= (function
            | Error _ -> Lwt.return @@ Error `No_space
            | Ok (tr) -> insert t block_size tr k true ps)
          | _ -> Lwt.return @@ Error `No_space)
        else insert t block_size c1 k false pointers >>= (function 
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (c, c_id, update, ps) -> Lwt.return @@ Ok (Il (v::next, pl::pls, c::c2::cn, r, bf, id), c_id, update, ps))
    else if k=v then Lwt.return @@ Ok (tree, id, true, pointers) (* update payload *)
    else if next=[] then match c2 with (* rightmost child *)
      | Il (k2s, _, _, _, _, _) ->
        if List.length k2s == 2*bf-1 then (match pointers with
          | p1::p2::ps -> split t block_size p1 p2 c2 tree (bf-1) >>= (function
            | Error _ -> Lwt.return @@ Error `No_space
            | Ok (tr) -> insert t block_size tr k true ps)
          | _ -> Lwt.return @@ Error `No_space)
        else insert t block_size c2 k false pointers >>= (function 
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (c, c_id, update, ps) -> Lwt.return @@ Ok (Il (v::next, pl::pls, c1::c::cn, r, bf, id), c_id, update, ps))
      | Lf (k2s, _, _, _, _) ->
        if List.length k2s == 2*bf-1 then (match pointers with
          | p1::ps -> split t block_size p1 Int32.max_int c2 tree (bf-1) >>= (function
            | Error _ -> Lwt.return @@ Error `No_space
            | Ok (tr) -> insert t block_size tr k true ps)
          | _ -> Lwt.return @@ Error `No_space)
        else insert t block_size c2 k false pointers >>= (function 
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (c, c_id, update, ps) -> Lwt.return @@ Ok (Il (v::next, pl::pls, c1::c::cn, r, bf, id), c_id, update, ps))
    else (insert t block_size (Il (next, pls, c2::cn, r, bf, id)) k false pointers >>= function
    | Error _ -> Lwt.return @@ Error `No_space
    | Ok (tr, tr_id, update, ps) -> Lwt.return @@ Ok (restore tr v pl c1, tr_id, update, ps))
  | _ -> raise (MalformedTree "internal node cannot be empty or without children")

  let insert_and_write t block_size tree k pl pointers last =
    let write_block t block_size k next pl tr ps =
      Serial.write_data_block_from_pl t block_size (Int64.of_int32 k) next pl >>= function
      | Error _ -> Lwt.return @@ Error `No_space
      | Ok () -> Lwt.return @@ Ok (tr, ps) in
    insert t block_size tree k false pointers >>= function
    | Error _ -> Lwt.return @@ Error `No_space
    | Ok (tr, tr_id, update, ps) ->
      let next = if (ps=[] || last) then Int32.max_int else List.hd ps in
      if not update then
        let hpointer, _cpointer = Ids.get_node_pointers_from_id tr_id in
        Block_ops.add_key_to_head_block t block_size (Int64.of_int32 hpointer) k >>= (function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok (hblock) -> Serial.write_block t (Int64.of_int32 hpointer) hblock >>= (function
          | Error _ -> Lwt.return @@ Error `No_space
          | Ok () -> write_block t block_size k next pl tr ps))
      else write_block t block_size k next pl tr ps

  (* takes two child nodes and merges them into one node *)
  let rec merge t block_size parent s1 s2 ignore iroot l = 
    let confirm_merge hpointer cblockpointer k nk cid tr =
      let fhpointer, fcblockpointer = Ids.get_node_pointers_from_id cid in
      Ids.remove_id cid; (* node id id2 is now unused *)
      let _hpointer, cpointer = Ids.get_node_pointers_from_id cid in
      Block_ops.remove_cpointer_from_child_block t block_size (Int64.of_int32 cblockpointer) cpointer nk >>= function
      | Error _ -> Lwt.return @@ Error `No_space
      | Ok (cblock) -> Block_ops.remove_key_from_head_block t block_size (Int64.of_int32 hpointer) k >>= (function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (hblock) -> Serial.write_block t (Int64.of_int32 cblockpointer) cblock >>= (function
          | Error _ -> Lwt.return @@ Error `No_space
          | Ok () -> Serial.write_block t (Int64.of_int32 hpointer) hblock >>= (function
            | Error _ -> Lwt.return @@ Error `No_space
            | Ok () -> Lwt.return @@ Ok (tr, false, fhpointer, fcblockpointer))))
    in match parent with
  | Lf _ -> raise (MalformedTree "leaf node cannot be parent")
  | Il (v::next, pl::pls, c1::c2::cn, r, bf, id) -> 
    if (c1=s1 && c2=s2) then match s1, s2 with
      | Lf _, Il _ -> raise (MalformedTree "nodes must be at same level")
      | Il _, Lf _ -> raise (MalformedTree "nodes must be at same level")
      | Lf (k1s, p1s, false, _, id1), Lf (k2s, p2s, false, _, id2) ->
      if r && (l + (List.length (v::next)) = 1) && not iroot then
        (Ids.remove_id id1; Ids.remove_id id2; (* node ids id1 and id2 now unused *)
        let tr = Lf (k1s @ (v::k2s), p1s @ (pl::p2s), true, bf, id) in
        let hpointer, _cblockpointer = Ids.get_node_pointers_from_id id in
        Node_writes.write_leaf_node t block_size hpointer tr >>= function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok () -> Lwt.return @@ Ok (tr, true, Int32.max_int, Int32.max_int)) (* new root can be written to disk *)
      else
        (let km, pm = k1s @ (v::k2s), p1s @ (pl::p2s) in (* TODO: concatenate lists without @ *)
        let l = List.length km in 
        if ((l < bf-1 || l > 2*bf-1) && not ignore) then raise (TreeCapacityNotMet "")
        else let s = Lf (km, pm, false, bf, id1) in
        let tr = Il (next, pls, s::cn, r, bf, id) in
        let hpointer, _cblockpointer = Ids.get_node_pointers_from_id id1 in
        let ppointer, pcblockpointer = Ids.get_node_pointers_from_id id in
        if not ignore then (Node_writes.write_leaf_node t block_size hpointer s >>= function (* can only write new child nodes if this is a real merge and not a steal *)
          | Error _ -> Lwt.return @@ Error `No_space
          | Ok () -> confirm_merge ppointer pcblockpointer v (Attrs.n_keys parent) id2 tr)
        else confirm_merge ppointer pcblockpointer v (Attrs.n_keys parent) id2 tr)
      | Il (k1s, p1s, cn1, false, _, id1), Il (k2s, p2s, cn2, false, _, id2) ->
        if r && (l + (List.length (v::next)) = 1) && not iroot then
          (Ids.remove_id id1; Ids.remove_id id2;
          let tr = Il (k1s @ (v::k2s), p1s @ (pl::p2s), cn1 @ cn2, r, bf, id) in
          let hpointer, cblockpointer = Ids.get_node_pointers_from_id id in
          Node_writes.write_internal_node t block_size hpointer cblockpointer tr >>= function
          | Error _ -> Lwt.return @@ Error `No_space
          | Ok () -> Lwt.return @@ Ok (tr, true, Int32.max_int, Int32.max_int))
        else
          (let km, pm, cm = k1s @ (v::k2s), p1s @ (pl::p2s), cn1 @ cn2 in
          let l = List.length k1s in
          if (l < bf-1 || l > 2*bf-1) then raise (TreeCapacityNotMet "")
          else let s = Il (km, pm, cm, false, bf, id1) in
          let tr = Il (next, pls, s::cn, r, bf, id) in
          let hpointer, cblockpointer = Ids.get_node_pointers_from_id id1 in
          let ppointer, pcblockpointer = Ids.get_node_pointers_from_id id in
          if not ignore then (Node_writes.write_internal_node t block_size hpointer cblockpointer s >>= function
          | Error _ -> Lwt.return @@ Error `No_space
          | Ok () -> confirm_merge ppointer pcblockpointer v (Attrs.n_keys parent) id2 tr)
          else confirm_merge ppointer pcblockpointer v (Attrs.n_keys parent) id2 tr)
      | _, _ -> raise (MalformedTree "child nodes cannot be empty")
    else (merge t block_size (Il (next, pls, (c2::cn), r, bf, id)) s1 s2 ignore iroot (l+1) >>= function
    | Error _ -> Lwt.return @@ Error `No_space
    | Ok (tr, change, fhp, fcbp) -> Lwt.return @@ Ok (restore tr v pl c1, change, fhp, fcbp))
  | _ -> raise (NotFound "could not find sibling nodes") (* occurs if s1 and s2 are not child nodes of given parent *)

  let rec find_predecessor tree k i = match tree with
  | Lf (v::next, _::pls, r, bf, id) ->
    if i then
      if next=[] then v
      else find_predecessor (Lf (next, pls, r, bf, id)) k i (* find largest key in leaf node *)
    else
      if k=v then raise (NotFound "") (* the predecessor is higher in the tree **)
      else if next=[] then raise (NotFound "key not found")
      else if List.hd next = k then v
      else find_predecessor (Lf (next, pls, r, bf, id)) k i
  | Il (v::next, _::pls, c1::c2::cn, r, bf, id) ->
    if not i then
      if k=v then find_predecessor c1 k true
      else if k<v then find_predecessor c1 k i
      else if (next=[] || k < List.hd next) then 
        (try find_predecessor c2 k i 
        with (NotFound "") -> v)
      else find_predecessor (Il (next, pls, (c2::cn), r, bf, id)) k i
    else
      if cn=[] then find_predecessor c2 k true
      else find_predecessor (Il (next, pls, (c2::cn), r, bf, id)) k i
  | _ -> raise (NotFound "key or predecessor not found")

  let rec find_successor tree k i = match tree with
  | Lf (v::next, _::pls, r, bf, id) ->
    if i then v
    else if r then
      if next=[] then raise (NotFound "key or successor not found")
      else if k=v then find_successor (Lf (next, pls, r, bf, id)) k true
      else find_successor (Lf (next, pls, r, bf, id)) k i
    else
      if next=[] then 
        if k=v then raise (NotFound "") (* the successor is higher in the tree *)
        else raise (NotFound "key not found")
      else if k=v then find_successor (Lf (next, pls, r, bf, id)) k true
      else find_successor (Lf (next, pls, r, bf, id)) k i
  | Il (v::next, _::pls, c1::c2::cn, r, bf, id) -> 
    if not i then
      if k=v then find_successor c2 k true
      else if k<v then 
        (try find_successor c1 k i 
        with (NotFound "") -> v)
      else if next=[] then find_successor c2 k i
      else find_successor (Il (next, pls, (c2::cn), r, bf, id)) k i
    else
      find_successor c1 k i
  | _ -> raise (NotFound "key or predecessor not found")

  (* swaps the positions of keys 'ok' and 'nk' in a tree *)
  (* nk must be either the predecessor or successor of ok and must be at a lower depth *)
  let rec swap_i t block_size tree ok nk i = 
    let replace id ok nk tr opt =
      let hpointer, _cpointer = Ids.get_node_pointers_from_id id in
      Block_ops.replace_key_in_head_block t block_size (Int64.of_int32 hpointer) ok nk >>= function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok (hblock) -> Serial.write_block t (Int64.of_int32 hpointer) hblock >>= (function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok () -> 
          if opt=0 then Lwt.return @@ Ok (tr)
          else if opt=1 then swap_i t block_size tr ok nk true >>= (function
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok (tr) -> Lwt.return @@ Ok (restore tr nk "" (Lf ([], [], false, 0, 0))))
          else (match tr with
            | Il (_::next, pl::pls, c1::c2::cn, r, bf, id) ->
              let ex1 = if nk>ok then swap_i t block_size c1 ok nk else swap_i t block_size c2 ok nk in ex1 true >>= (function
              | Error _ -> Lwt.return @@ Error `Not_found
              | Ok (tr) -> (if nk>ok then Lwt.return @@ Ok (Il (nk::next, pl::pls, c1::tr::cn, r, bf, id))
              else Lwt.return @@ Ok (Il (nk::next, pl::pls, tr::c2::cn, r, bf, id))))
            | _ -> raise (MalformedTree "")))
    in match tree with
  | Lf (v::next, pl::pls, r, bf, id) ->
    if i then
      if v=nk then (replace (Attrs.get_id tree) nk ok (Lf (ok::next, pl::pls, r, bf, id)) 0)
      else if next=[] then raise (NotFound "at least one key to swap not found")
      else swap_i t block_size (Lf (next, pls, r, bf, id)) ok nk i >>= function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok (tr) -> Lwt.return @@ Ok (restore tr v pl (Lf ([], [], false, 0, 0))) 
    else 
      if v=ok then (replace (Attrs.get_id tree) ok nk (Lf (next, pls, r, bf, id)) 1) 
        (* TODO : get rid of unnecessary write by changing i to two-bit int and distinguishing this case *)
      else if next=[] then raise (NotFound "at least one key to swap not found")
      else swap_i t block_size (Lf (next, pls, r, bf, id)) ok nk i >>= (function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok (tr) -> Lwt.return @@ Ok (restore tr v pl (Lf ([], [], false, 0, 0))))
  | Il (v::next, pl::pls, c1::c2::cn, r, bf, id) ->
    if i then
      if nk<ok then
        if next=[] then swap_i t block_size c2 ok nk i >>= function
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (tr) -> Lwt.return @@ Ok (Il (v::next, pl::pls, c1::tr::cn, r, bf, id))
        else swap_i t block_size (Il (next, pls, (c2::cn), r, bf, id)) ok nk i >>= function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok (tr) -> Lwt.return @@ Ok (restore tr v pl c1)
      else swap_i t block_size c1 ok nk i >>= function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok (tr) -> Lwt.return @@ Ok (Il (v::next, pl::pls, tr::c2::cn, r, bf, id))
    else if ok=v then replace (Attrs.get_id tree) ok nk tree 2
    else if ok>v then 
      if next=[] then swap_i t block_size c2 ok nk i >>= function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok (tr) -> Lwt.return @@ Ok (Il (v::next, pl::pls, c1::tr::cn, r, bf, id))
      else swap_i t block_size (Il (next, pls, (c2::cn), r, bf, id)) ok nk i >>= function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok (tr) -> Lwt.return @@ Ok (restore tr v pl c1)
    else swap_i t block_size c1 ok nk i >>= (function
    | Error _ -> Lwt.return @@ Error `Not_found
    | Ok (tr) -> Lwt.return @@ Ok (Il (v::next, pl::pls, tr::c2::cn, r, bf, id)))
  | _ -> raise (NotFound "at least one key to swap not found")

  let steal t block_size tree morec = match tree with
  | Il (_, _, ca::cb::_, r, bf, _) -> 
    merge t block_size tree ca cb true r 0 >>= (function
    | Error _ -> Lwt.return @@ Error `Not_found
    | Ok (mt, _, hpointer, cblockpointer) -> 
      let mc = (match mt with
      Il (_, _, c::_, _, _, _) -> c
      | _ -> raise (MalformedTree "merge failed")) in
      let lim = (if ca=morec then (Attrs.n_keys ca - 1) else if cb=morec then bf else -1) in
      if lim = -1 then raise (MalformedTree "child node not found")
      else split t block_size hpointer cblockpointer mc mt lim)
  | _ -> raise (MalformedTree "must be an internal node with the two specified child nodes")

  let rec delete t block_size tree k i = match tree with
  | Il (v::next, pl::pls, ca::cb::cn, r, bf, id) -> 
    let l1, l2 = Attrs.(n_keys ca, n_keys cb) in
    if k=v then
      if not (l1 < bf) then let nk = find_predecessor tree v false in (* check left subtree *)
      swap_i t block_size tree v nk false >>= (function
      | Error _ -> Lwt.return @@ Error `Not_found
        | Ok (newt) -> (match newt with
          | Il (k1s, p1s, c1::cn1, r1, bf1, id) -> delete t block_size c1 k 0 >>= (function
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok (tr) -> Lwt.return @@ Ok (Il (k1s, p1s, tr::cn1, r1, bf1, id)))
          | _ -> raise (MalformedTree "swap failed")))
      else if not (l2 < bf) then let nk = find_successor tree v false in (* check right subtree *)
      swap_i t block_size tree v nk false >>= (function 
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok (newt) -> (match newt with
          | Il (k1s, p1s, c1::c2::cn1, r1, bf1, id) -> delete t block_size c2 k 0 >>= (function
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok (tr) -> Lwt.return @@ Ok (Il (k1s, p1s, c1::tr::cn1, r1, bf1, id)))
          | _ -> raise (MalformedTree "swap failed")))
      else merge t block_size tree ca cb false false i >>= (function 
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok (mt, change, _, _) -> (match mt with (* merge around key to delete and recursively delete it *)
          | Il (_::_, _::_, _::_, true, _, _) -> delete t block_size mt k (if change then 0 else i)
          | Il (k1::k1s, p1::p1s, c1::cn1, r1, bf1, id) -> delete t block_size c1 k 0 >>= (function 
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok (tr) -> Lwt.return @@ Ok (Il (k1::k1s, p1::p1s, tr::cn1, r1, bf1, id)))
          | Il ([], [], c1::[], r1, bf1, id) -> delete t block_size c1 k 0 >>= (function 
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok (tr) -> Lwt.return @@ Ok (Il ([], [], tr::[], r1, bf1, id)))
          | Lf (_::_, _::_, true, _, _) -> delete t block_size mt k 0
          | _ -> raise (MalformedTree "merge failed")))
    else let leftc, rightc = k<v, next=[] in
      if leftc then
        if l1 < bf then
          if (l2 >= bf) then steal t block_size tree cb >>= (function (* steal from right sibling *)
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok (tr) -> delete t block_size tr k i)
        else merge t block_size tree ca cb false false i >>= (function 
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (mt, change, _, _) -> (match mt with (* merge around key to delete and recursively delete it *)
            | Il (_::_, _::_, _::_, _, _, _) -> delete t block_size mt k (if change then 0 else i)
            | Il ([], [], c1::[], r1, bf1, id) -> delete t block_size c1 k 0 >>= (function 
              | Error _ -> Lwt.return @@ Error `Not_found
              | Ok (tr) -> Lwt.return @@ Ok (Il ([], [], tr::[], r1, bf1, id)))
            | Lf (_::_, _::_, true, _, _) -> delete t block_size mt k 0
            | _ -> raise (MalformedTree "merge failed"))) 
          else delete t block_size ca k 0 >>= (function (* check left subtree *)
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (tr) -> Lwt.return @@ Ok (Il (v::next, pl::pls, tr::cb::cn, r, bf, id)))
      else if rightc then
        if l2 < bf then
          if (l1 >= bf) then steal t block_size tree ca >>= function
            | Error _ -> Lwt.return @@ Error `No_space
            | Ok (tr) -> delete t block_size tr k i (* steal from left sibling *)
          else merge t block_size tree ca cb false false i >>= (function 
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok (mt, change, _, _) -> (match mt with (* merge around key to delete and recursively delete it *)
              | Il (_::_, _::_, _::_, _, _, _) -> delete t block_size mt k (if change then 0 else i)
              | Il ([], [], c1::[], r1, bf1, id) -> delete t block_size c1 k 0 >>= (function 
                | Error _ -> Lwt.return @@ Error `Not_found
                | Ok (tr) -> Lwt.return @@ Ok (Il ([], [], tr::[], r1, bf1, id)))
              | Lf (_::_, _::_, true, _, _) -> delete t block_size mt k 0
              | _ -> raise (MalformedTree "merge failed")))
        else delete t block_size cb k 0 >>= (function (* check left subtree *)
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (tr) -> Lwt.return @@ Ok (Il (v::next, pl::pls, ca::tr::cn, r, bf, id))) (* check right subtree *)
        else delete t block_size (Il (next, pls, (cb::cn), r, bf, id)) k (i+1) >>= (function (* check next key in node *)
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (tr) -> Lwt.return @@ Ok (restore tr v pl ca))
  | Lf (v::next, pl::pls, r, bf, id) ->
    if k=v then (
      let hpointer, _cblockpointer = Ids.get_node_pointers_from_id id in
      Block_ops.remove_key_from_head_block t block_size (Int64.of_int32 hpointer) k >>= (function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok (hblock) -> Serial.write_block t (Int64.of_int32 hpointer) hblock >>= (function
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok () -> Lwt.return @@ Ok ((Lf (next, pls, r, bf, id))))))
    else if (k>v && next!=[]) then delete t block_size (Lf (next, pls, r, bf, id)) k (i+1) >>= (function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok (tr) -> Lwt.return @@ Ok (restore tr v pl (Lf ([], [], false, 0, 0))))
    else raise (NotFound "key to delete not found")
  | _ -> raise (MalformedTree ("not an internal node with >1 child"))

  let rec delete_list t block_size tree keys = match keys with
  | k::ks -> 
    delete t block_size tree k 0 >>= (function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok (tr) -> delete_list t block_size tr ks >>= (function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok (tr1) -> Lwt.return @@ Ok (tr1)))
  | [] -> Lwt.return @@ Ok (tree)
end
