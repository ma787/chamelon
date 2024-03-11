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
    | Il (k::_, _, _, _, _, _) -> k
    | Lf (k::_, _, _, _, _) -> k
    | _ -> Int32.max_int

    let get_keys tree = match tree with
    | Il (ks, _, _, _, _, _) -> ks
    | Lf (ks, _, _, _, _) -> ks

    let get_pls tree = match tree with
    | Il (_, pls, _, _, _, _) -> pls
    | Lf (_, pls, _, _, _) -> pls

    let get_cn tree = match tree with
    | Il (_, _, cn, _, _, _) -> cn
    | _ -> []

    let get_degree tree = match tree with
    | Il (_, _, _, _, bf, _) -> bf
    | Lf (_, _, _, bf, _) -> bf

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

  module Tree_ops = struct
    let restore tree k p c = match tree with
    | Lf ([], [], r, bf, id) -> Lf (k::[], p::[], r, bf, id)
    | Lf (v::next, pl::pls, r, bf, id) -> Lf (k::v::next, p::pl::pls, r, bf, id)
    | Il ([], [], cn, r, bf, id) -> Il (k::[], p::[], c::cn, r, bf, id)
    | Il (v::next, pl::pls, cn, r, bf, id) -> Il (k::v::next, p::pl::pls, c::cn, r, bf, id)
    | _ -> raise (MalformedTree "keys/payloads/children mismatch")

    let rec get_next tree k = match tree with
    | Il (v::next, _::pls, _::cn, r, t, id) ->
      if v=k then try [List.hd next] with Failure _ -> []
      else get_next (Il (next, pls, cn, r, t, id)) k
    | Il ([], _, _, _, _, _) -> []
    | Lf (v::next, _::pls, r, t, id) ->
      if v=k then try [List.hd next] with Failure _ -> []
      else get_next (Lf (next, pls, r, t, id)) k
    | Lf ([], _, _, _, _) -> []
    | _ -> raise (MalformedTree "invalid tree structure")

    let rec get_child tree kl = 
      if Attrs.is_leaf tree then (Lf ([], [], false, 0, -1))
      else match kl with
    | [] -> (match tree with
      | Il (_::next, _::pls, _::cn, r, t, id) -> get_child (Il (next, pls, cn, r, t, id)) kl
      | Il ([], [], c::[], _, _, _) -> c
      | _ -> raise (MalformedTree ""))
    | k::_ -> (match tree with
      | Il (v::next, _::pls, c::cn, r, t, id) ->
        if v=k then c else get_child (Il (next, pls, cn, r, t, id)) kl
      | Il ([], [], _::[], _, _, _) -> raise (NotFound "child node not found")
      | _ -> raise (MalformedTree ""))
    
    let rec replace_child tree kl newc =
      if Attrs.is_leaf tree then (Lf ([], [], false, 0, -1))
      else match kl with
    | [] -> (match tree with
      | Il (v::next, pl::pls, c::cn, r, t, id) -> restore (replace_child (Il (next, pls, cn, r, t, id)) kl newc) v pl c
      | Il ([], [], _::[], r, t, id) -> Il ([], [], newc::[], r, t, id)
      | _ -> raise (MalformedTree ""))
    | k::_ -> (match tree with
      | Il (v::next, pl::pls, c::cn, r, t, id) ->
        if v=k then (Il (v::next, pl::pls, newc::cn, r, t, id)) else restore (replace_child (Il (next, pls, cn, r, t, id)) kl newc) v pl c
      | Il ([], [], _::[], _, _, _) -> raise (NotFound "child node not found")
      | _ -> raise (MalformedTree ""))
    
    let rec remove_key tree k = match tree with
    | Lf (ks, pls, r, t, id) -> Lf ((List.filter (fun i -> not (Int32.equal k i)) ks), List.tl pls, r, t, id)
    | _ -> raise (MalformedTree "cannot remove key from internal node")
  
    let rec replace_and_remove tree kl newc =
      match kl with
    | [] -> raise (NotFound "merge key not given")
    | k::_ -> (match tree with
      | Il (v::next, pl::pls, c1::c2::cn, r, t, id) ->
        if v=k then (Il (next, pls, newc::cn, r, t, id)) else restore (replace_and_remove (Il (next, pls, (c2::cn), r, t, id)) kl newc) v pl c1
      | _ -> raise (NotFound "merge key to remove not found"))
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
        if (pointer=2L && id != 1) then (Ids.ids := [(1, (2l, Int32.max_int))]; Lwt.return @@ Ok (Lf ([], [], true, bf, 1)))
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

  (* searches for a node with key k and returns node *)
  let rec search tree k = let eq a b = a=b in
  let search_next tnode ks nv npl nc  = let tnext = search tnode k in (match tnext with
  | Il ([], [], _::[], _, _, _) -> Tree_ops.restore tnext nv npl nc
  | Il (v::_, _::_, _::_, _, _, _) -> 
    if List.exists (eq v) ks then Tree_ops.restore tnext nv npl nc else tnext
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
      else Tree_ops.restore (search (Lf (next, pls, r, bf, id)) k) v pl (Lf ([], [], false, 0, -1))
    else raise (NotFound "key not found")
  | _ -> raise (NotFound "key not found")

  (* adds a key and child to a node *)
  (* key must not already be in the node *)
  let rec update_node tree k c1 c2 = match tree with
  | Il (v::next, pl::pls, c::cn, r, bf, id) -> 
    if Attrs.is_leaf c1 != Attrs.is_leaf c then
      raise (MalformedTree "child type mismatch")
    else if Attrs.get_hd c1 = Attrs.get_hd c then
      Il (k::v::next, ""::pl::pls, c1::c2::cn, r, bf, id)
    else Tree_ops.restore (update_node (Il (next, pls, cn, r, bf, id)) k c1 c2) v pl c
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
    let func lf hp cbp =
      if lf then Node_writes.write_leaf_node t block_size hp
      else Node_writes.write_internal_node t block_size hp cbp in
    let ctr d lf ks pls cn bf id =
      let dtn = if d then Attrs.get_left else Attrs.get_right in
      if lf then Lf (dtn ks 0 (bf-1), dtn pls 0 (bf-1), false, bf, id)
      else Il (dtn ks 0 (bf-1), dtn pls 0 (bf-1), dtn cn 0 (bf-1), false, bf, id) in
  let ks, pls, cn, bf, id, leaf = Attrs.get_keys tree, List.init (Attrs.n_keys tree) (fun _ -> ""), Attrs.get_cn tree, 
  Attrs.get_degree tree, Attrs.get_id tree, Attrs.is_leaf tree in
  let id1 = Ids.find_first_free_id Ids.ids in
  let mk, mp = List.nth ks (bf-1), List.nth pls (bf-1) in
  let tl = ctr true leaf ks pls cn bf id1 in
  func leaf (List.hd hpointers) (List.hd cblockpointers) tl >>= function
  | Error _ as e -> Lwt.return e
  | Ok () -> 
    let id2 = Ids.find_first_free_id Ids.ids in
    let tr = ctr false leaf ks pls cn bf id2 in
    func leaf (List.hd (List.tl hpointers)) (List.hd (List.tl cblockpointers)) tr >>= (function
    | Error _ as e -> Lwt.return e
    | Ok () ->
      let newr = (Il (mk::[], mp::[], tl::tr::[], true, bf, id)) in
      let hpointer, cblockpointer = Ids.get_node_pointers_from_id id in
      Node_writes.write_internal_node t block_size hpointer cblockpointer newr >>= (function
      | Error _ as e -> Lwt.return e
      | Ok () -> 
        Ids.store_id (id1, (List.hd hpointers, List.hd cblockpointers));
        Ids.store_id (id2, (List.hd (List.tl hpointers), List.hd (List.tl cblockpointers)));
        Lwt.return @@ Ok (newr)))

  (* splits a node in two on a given key index *)
  (* migrates key to parent node and returns parent, which may now be full *)
  (* hpointers : [left_pointer, right_pointer, parent_pointer] *)
  (* cblockpointers: [left_child_pointer, right_child_pointer, parent_child_pointer] *)
  let split t block_size nhpointer ncblockpointer tree parent m =
  let func lf hp cbp =
    if lf then Node_writes.write_leaf_node t block_size hp
    else Node_writes.write_internal_node t block_size hp cbp in
  let ctr d lf ks pls cn bf id mc =
    let op1, op2 = if d then Attrs.get_left, Attrs.get_left_cn else Attrs.get_right, Attrs.get_right in
    if lf then Lf (op1 ks 0 m, op1 pls 0 m, false, bf, id)
    else Il (op1 ks 0 m, op1 pls 0 m, (if d then (op2 cn 0 m) else mc::(op2 cn 0 m)), false, bf, id) in
  if Attrs.is_leaf parent then raise (MalformedTree "leaf node cannot be parent")
  else let hpointer, cblockpointer = Ids.get_node_pointers_from_id (Attrs.get_id tree) in
  let phpointer, pcblockpointer = Ids.get_node_pointers_from_id (Attrs.get_id parent) in 
  let ks, pls, cn, bf, id, cleaf = Attrs.get_keys tree, List.init (Attrs.n_keys tree) (fun _ -> ""), Attrs.get_cn tree, 
  Attrs.get_degree tree, Attrs.get_id tree, Attrs.is_leaf tree in
  let id1 = Ids.find_first_free_id Ids.ids in
  let mk, mc = List.nth ks m, (if cleaf then (Lf ([], [], false, 0, -1)) else List.nth cn m) in
  let tl = ctr true cleaf ks pls cn bf id mc in func cleaf hpointer cblockpointer tl >>= function
  | Error _ -> Lwt.return @@ Error `No_space
  | Ok () ->
    let tr = ctr false cleaf ks pls cn bf id1 mc in func cleaf nhpointer ncblockpointer tr >>= function
    | Error _ -> Lwt.return @@ Error `No_space
    | Ok () -> 
      let nk = Attrs.n_keys parent in
      Node_writes.node_split_update t block_size phpointer pcblockpointer nk mk nhpointer >>= function
      | Error _ -> Lwt.return @@ Error `No_space
      | Ok () ->
        let updated = update_node parent mk tl tr in
        Ids.store_id (id1, (nhpointer, ncblockpointer));
        Lwt.return @@ Ok (updated)

  (* inserts a given key into the tree *)
  let rec insert t block_size tree k v i pointers =
    let insert_key tree k = match tree with
      | Lf (ks, pls, r, bf, id) -> Lf (k::ks, ""::pls, r, bf, id)
      | _ -> raise (MalformedTree "") in
    let id, bf, root, leaf = Attrs.get_id tree, Attrs.get_degree tree, Attrs.is_root tree, Attrs.is_leaf tree in
    let lim = 2*bf-1 in
    let empty, full = (Int32.equal v Int32.max_int), Attrs.n_keys tree = lim in
    if (full && root && not i) then (match pointers with
      | p1::p2::ps when leaf -> split_root t block_size [p1; p2] [Int32.max_int; Int32.max_int] tree >>= (function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (tr) -> insert t block_size tr k (Attrs.get_hd tr) false ps)
      | p1::p2::p3::p4::ps when (not leaf) -> split_root t block_size [p1; p2] [p3; p4] tree >>= (function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (tr) -> insert t block_size tr k (Attrs.get_hd tr) false ps)
      | _ -> Lwt.return @@ Error `No_space)
    else if (full && not root) then raise (MalformedTree "full node not split ahead of time")
    else if (empty && root) then Lwt.return @@ Ok (insert_key tree k, id, false, pointers)
    else if k=v then Lwt.return @@ Ok (tree, id, true, pointers)
    else let next = Tree_ops.get_next tree v in
      if (k>v && next != []) then insert t block_size tree k (List.hd (Tree_ops.get_next tree v)) false pointers >>= (function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (tr, tr_id, update, ps) -> Lwt.return @@ Ok (tr, tr_id, update, ps))
      else let pkey = if k<v then [v] else [] in 
      if leaf then Lwt.return @@ Ok (insert_key tree k, id, false, pointers)
      else let c = Tree_ops.get_child tree pkey in
      let cleaf = Attrs.is_leaf c in
      if (Attrs.n_keys c = lim) then (match pointers with
        | p1::ps when cleaf -> split t block_size p1 Int32.max_int c tree (bf-1) >>= (function
          | Error _ -> Lwt.return @@ Error `No_space
          | Ok (tr) -> insert t block_size tr k (Attrs.get_hd tr) true ps)
        | p1::p2::ps when (not cleaf) -> split t block_size p1 p2 c tree (bf-1) >>= (function
          | Error _ -> Lwt.return @@ Error `No_space
          | Ok (tr) -> insert t block_size tr k (Attrs.get_hd tr) true ps)
        | _ -> Lwt.return @@ Error `No_space)
      else insert t block_size c k (Attrs.get_hd c) false pointers >>= (function 
      | Error _ -> Lwt.return @@ Error `No_space
      | Ok (newc, c_id, update, ps) -> Lwt.return @@ Ok (Tree_ops.replace_child tree pkey newc, c_id, update, ps))

  let insert_and_write t block_size tree k pl pointers last =
    let write_block t block_size k next pl tr ps =
      Serial.write_data_block_from_pl t block_size (Int64.of_int32 k) next pl >>= function
      | Error _ -> Lwt.return @@ Error `No_space
      | Ok () -> Lwt.return @@ Ok (tr, ps) in
    insert t block_size tree k (Attrs.get_hd tree) false pointers >>= function
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
  let rec merge t block_size parent v s1 s2 ignore iroot = 
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
            | Ok () -> Lwt.return @@ Ok (tr, false, fhpointer, fcblockpointer)))) in
    let id, bf, root, leaf = Attrs.get_id parent, Attrs.get_degree parent, Attrs.is_root parent, Attrs.is_leaf parent in
    let onek, next = Attrs.n_keys parent = 1, Tree_ops.get_next parent v in
    let s1l, s2l = Attrs.is_leaf s1, Attrs.is_leaf s2 in
    if ((s1l && (not s2l)) || ((not s1l) && s2l)) then raise (MalformedTree "nodes must be at same level")
    else if leaf then raise (MalformedTree "leaf node cannot be parent")
    else 
      let m1, m2 = Tree_ops.get_child parent [v] = s1, (next != [] && Tree_ops.get_child parent next = s2) in
      if m1 && m2 then
        (let hpointer, cblockpointer = Ids.get_node_pointers_from_id id in
        let k1s, k2s = Attrs.get_keys s1, Attrs.get_keys s2 in
        let klen = List.length k1s + List.length k2s + 1 in
        let pm, cm = List.init klen (fun _ -> ""), (if not leaf then Attrs.get_cn s1 @ Attrs.get_cn s2 else []) in
        let id1, id2 = Attrs.get_id s1, Attrs.get_id s2 in
        if (root && onek && not iroot) then 
          (let mk = Attrs.get_hd parent in
          (Ids.remove_id id1; Ids.remove_id id2;
          let func = Node_writes.(if leaf then write_leaf_node t block_size hpointer else write_internal_node t block_size hpointer cblockpointer) in
          let tr = (if leaf then (Lf (k1s @ (mk::k2s), pm, true, bf, id)) else (Il (k1s @ (mk::k2s), pm, cm, true, bf, id))) in
          func tr >>= function
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok () -> Lwt.return @@ Ok (tr, true, Int32.max_int, Int32.max_int)))
        else 
          let km = k1s @ (v::k2s) in
          let s = (if leaf then (Lf (km, pm, false, bf, id1)) else (Il (km, pm, cm, false, bf, id1))) in
          let tr = Tree_ops.replace_and_remove parent [v] s in
          let chpointer, ccblockpointer = Ids.get_node_pointers_from_id id1 in
          let func = Node_writes.(if leaf then write_leaf_node t block_size chpointer else write_internal_node t block_size chpointer ccblockpointer) in
          if not ignore then (func tr >>= function
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok () -> confirm_merge hpointer cblockpointer v (Attrs.n_keys parent) id2 tr)
          else confirm_merge hpointer ccblockpointer v (Attrs.n_keys parent) id2 tr)
        else if next=[] then raise (NotFound "could not find sibling nodes")
        else merge t block_size parent (List.hd next) s1 s2 ignore iroot >>= (function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (tr, change, fhp, fcbp) -> Lwt.return @@ Ok (tr, change, fhp, fcbp))

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
  let rec swap_i t block_size tree ok nk v found index = 
    let swap_child kl f = let c = Tree_ops.get_child tree kl in swap_i t block_size c (Attrs.get_hd c) ok nk f 0 in
    let swap_next n i = swap_i t block_size tree ok nk (List.hd n) i (index+1) in
    let id, bf, r, leaf = Attrs.get_id tree, Attrs.get_degree tree, Attrs.is_root tree, Attrs.is_leaf tree in
    let ks, pls, next = Attrs.get_keys tree, List.init (Attrs.n_keys tree) (fun _ -> ""), Tree_ops.get_next tree v in
    let replace cond =
      let hpointer, cblockpointer = Ids.get_node_pointers_from_id id in
      let func =
        if cond then fun _ -> Lwt.return @@ Ok ()
        else if leaf then Node_writes.write_leaf_node t block_size hpointer 
        else Node_writes.write_internal_node t block_size hpointer cblockpointer in
      func tree >>= (function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok () -> Lwt.return @@ Ok ()) in
    if v=nk then
      if (found=0 || not leaf) then raise (MalformedTree "order violation")
      else let newks = List.mapi (fun i k -> if i=index then ok else k) ks in 
      let tr = Lf (newks, pls, r, bf, id) in replace (found=1) >>= function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok () -> Lwt.return @@ Ok (tr)
    else if (v=ok || found>0) then
      if (next=[] && leaf) then raise (NotFound "one key not found")
      else replace (found != 0) >>= function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok () -> 
          if leaf then swap_next next (if found=0 then 1 else found)
          else if nk>ok then 
            if next=[] then swap_child next 2
            else swap_next next (if found=0 then 1 else found)
          else swap_child [v] 2
    else if v>ok then
      if next=[] then swap_child next 0
      else swap_next next 0
    else swap_child [v] 0

  let steal t block_size tree morec = match tree with
  | Il (_, _, ca::cb::_, r, bf, _) -> 
    merge t block_size tree (Attrs.get_hd tree) ca cb true r >>= (function
    | Error _ -> Lwt.return @@ Error `Not_found
    | Ok (mt, _, hpointer, cblockpointer) -> 
      let mc = (match mt with
      Il (_, _, c::_, _, _, _) -> c
      | _ -> raise (MalformedTree "merge failed")) in
      let lim = (if ca=morec then (Attrs.n_keys ca - 1) else if cb=morec then bf else -1) in
      if lim = -1 then raise (MalformedTree "child node not found")
      else split t block_size hpointer cblockpointer mc mt lim)
  | _ -> raise (MalformedTree "must be an internal node with the two specified child nodes")

  let rec delete t block_size v tree k =
    let merge_and_delete v ca cb =
      merge t block_size tree v ca cb false false >>= function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok (mt, _, _, _) -> (match mt with
        | Il (_::_, _::_, _::_, true, _, _) -> delete t block_size (Attrs.get_hd mt) mt k (* a merge involving the root node could reduce tree height so we need to restart *)
        | Il (v::next, pl::pls, c::cn, r, bf, id) -> delete t block_size (Attrs.get_hd c) c k >>= (function
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (tr) -> Lwt.return @@ Ok (Il (v::next, pl::pls, tr::cn, r, bf, id)))
        | Il ([], [], c::[], r, bf, id) -> delete t block_size (Attrs.get_hd c) c k >>= (function
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (tr) -> Lwt.return @@ Ok (Il ([], [], tr::[], r, bf, id)))
        | Lf (_::_, _::_, true, _, _) -> delete t block_size (Attrs.get_hd mt) mt k
        | _ -> raise (MalformedTree "merge failed")) in
    if Int32.(equal v max_int) then Lwt.return @@ Ok (tree) (* cannot delete anything from an empty node *)
    else let ks, pls, r, bf, id, leaf = Attrs.(get_keys tree, List.init (n_keys tree) (fun _ -> ""), is_root tree, get_degree tree, get_id tree, is_leaf tree) in
      let next = Tree_ops.get_next tree v in
      let ca, cb = if not leaf then Tree_ops.(get_child tree [v], get_child tree next) else (Lf ([], [], false, 0, -1)), (Lf ([], [], false, 0, -1)) in
      let l1, l2 = Attrs.(n_keys ca, n_keys cb) in
      let leftc, rightc, lempty, rempty = k<v, next=[], l1<bf, l2<bf in
      if k=v then
        if leaf then let hpointer, _cblockpointer = Ids.get_node_pointers_from_id id in
          Block_ops.remove_key_from_head_block t block_size (Int64.of_int32 hpointer) k >>= (function
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok (hblock) -> Serial.write_block t (Int64.of_int32 hpointer) hblock >>= (function
              | Error _ -> Lwt.return @@ Error `Not_found
              | Ok () -> Lwt.return @@ Ok (Tree_ops.remove_key tree k)))
        else if not (lempty && rempty) then
          let func = (if lempty then find_successor tree v else find_predecessor tree v) in
          let rk = func false in
          swap_i t block_size tree v rk v 0 0 >>= function
            | Error _ -> Lwt.return @@ Error `Not_found
            | Ok (newt) -> (match newt with
              | Il (k1s, pls, c1::c2::cn, r, bf, id) -> 
                let vc, c = Attrs.(if lempty then get_hd c2, c2 else get_hd c1, c1) in delete t block_size vc c k >>= (function
                  | Error _ -> Lwt.return @@ Error `Not_found
                  | Ok (tr) -> Lwt.return @@ Ok (Il (k1s, pls, (if lempty then c1::tr::cn else tr::c2::cn), r, bf, id)))
              | _ -> raise (MalformedTree "swap failed"))
        else merge_and_delete v ca cb
      else let ci = if lempty then cb else ca in 
        if (not leaf && (leftc && lempty && not rempty || rightc && rempty && not lempty)) then steal t block_size tree ci >>= function (* one child has enough keys to steal one from it *)
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (tr) -> delete t block_size (Attrs.get_hd tr) tr k
        else if (not leaf && (leftc && lempty || rightc && rempty)) then merge_and_delete v ca cb (* both child nodes have the minimum number of keys *)
        else if (not leaf && (leftc || rightc)) then delete t block_size (Attrs.get_hd ci) ci k >>= function (* check child node *)
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (tr) -> Lwt.return @@ Ok (Il (ks, pls, Attrs.get_cn (Tree_ops.replace_child tree (if leftc then [v] else next) tr), r, bf, id))
        else if (leaf && not leftc && rightc) then raise (NotFound "key to delete not found")
        else delete t block_size (List.hd next) tree k

  let rec delete_list t block_size tree keys = match keys with
  | k::ks -> 
    delete t block_size (Attrs.get_hd tree) tree k >>= (function
      | Error _ -> Lwt.return @@ Error `Not_found
      | Ok (tr) -> delete_list t block_size tr ks >>= (function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok (tr1) -> Lwt.return @@ Ok (tr1)))
  | [] -> Lwt.return @@ Ok (tree)
end
