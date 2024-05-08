type keys = int64 list
type node = 
| Lf of keys * bool * int * int
| Il of keys * node list * bool * int * int

exception MalformedTree of string
exception NotFound of string
exception InvalidOperation of string

let null_tree = Lf ([], false, 0, -1)
let null_pointer = Int64.max_int

open Lwt.Infix

module Make(Sectors: Mirage_block.S) = struct
  module Block_types = Block_type.Make (Sectors)

  open Block_types
  let sizeof_pointer = 8

  type error = [
    | `Read_error
    | `Write_error
    | `No_space
  ]

  module IdSet = Set.Make(Int)

  module Attrs = struct
    let n_keys tree = match tree with
    | Il (ks, _, _, _, _) -> List.length ks
    | Lf (ks, _, _, _) -> List.length ks
  
    let get_hd tree = match tree with
    | Il (ks, _, _, _, _) -> List.hd ks
    | Lf (ks, _, _, _) -> List.hd ks
  
    let is_leaf tree = match tree with
    | Il _ -> false
    | Lf _ -> true
  
    let get_id tree = match tree with
    | Il (_, _, _, _, id) -> id
    | Lf (_, _, _, id) -> id
  
    let get_all tree = match tree with
    | Il (ks, cn, r, b, id) -> ks, cn, r, b, id
    | Lf (ks, r, b, id) -> ks, [], r, b, id
  
    let get_child_ids tree = match tree with
    | Il (_, cn, _, _, _) -> 
      List.map (fun tr -> let _, _, _, _, id = get_all tr in id) cn
    | Lf _ -> []
  
    let get_all_ids tree = 
    let rec get_id_list tree = match tree with
    | Il (_, cn, true, _, id) -> id::(get_child_ids tree) @ (List.flatten (List.map get_id_list cn))
    | Il (_, cn, _, _, _) -> (get_child_ids tree) @ (List.flatten (List.map get_id_list cn))
    | Lf (_, true, _, id) -> [id]
    | Lf _ -> [] in
    List.sort_uniq Int.compare (get_id_list tree)

    let get_all_keys tree = 
      let rec get_key_list tree = match tree with
      | Il (ks, cn, _, _, _) -> ks @ (List.flatten (List.map get_key_list cn))
      | Lf (ks, _, _, _) -> ks in
      List.sort_uniq Int64.compare (get_key_list tree)
  
    let split_ks n ks = 
      let rec splitv ks newks i = match ks with
      | c::cs -> 
        if i=n then [c], List.rev newks, cs else splitv cs (c::newks) (i+1)
      | [] -> [], List.rev newks, ks
    in splitv ks [] 0
  
    let split_cn n cn = 
      let rec splitv cn newcn i = match cn with
      | c::cs -> if i=n then List.rev newcn, cn else splitv cs (c::newcn) (i+1)
      | [] -> List.rev newcn, cn
    in splitv cn [] 0
  
    let rec get_index l v i = match l with
    | [] -> raise (Failure "not in list")
    | c::cs -> if c=v then i else get_index cs v (i+1)
  
    let rec to_string tree = 
    let ks, cn, r, b, id = get_all tree in
    let string_of_int64_list l = 
      "{" ^ (List.fold_left (fun acc x -> 
        acc ^ Int64.to_string x ^ ",") "" l) ^ "}" in
    let string_of_tree_list l = 
      let s = (List.fold_left (fun acc x -> acc ^ (to_string x) ^ ",") "" l) in 
      if s = "" then s else "[" ^ s ^ "], " in 
    "(" ^ (string_of_int64_list ks) ^ ", " ^ (string_of_tree_list cn) ^ 
    (string_of_bool r) ^ ", " ^ (string_of_int b) ^ ", " ^ (string_of_int id) ^ ")"
    end

  open Attrs
  
  module Tree_ops = struct
    (* adds key k, payload p and child c to each associated list *)
    let restore tree k c = match tree with
    | Lf ([], r, b, id) -> Lf (k::[], r, b, id)
    | Lf (v::next, r, b, id) -> Lf (k::v::next, r, b, id)
    | Il ([], cn, r, b, id) -> Il (k::[], c::cn, r, b, id)
    | Il (v::next, cn, r, b, id) -> Il (k::v::next, c::cn, r, b, id)
  
    (* returns [next key] or [] if k is the rightmost key in the node *)
    let rec get_next tree k = match tree with
    | Il (v::next, _::cn, r, b, id) ->
      if v=k then try [List.hd next] with Failure _ -> []
      else get_next (Il (next, cn, r, b, id)) k
    | Il ([], _, _, _, _) -> []
    | Lf (v::next, r, b, id) ->
      if v=k then try [List.hd next] with Failure _ -> []
      else get_next (Lf (next, r, b, id)) k
    | _ -> raise (MalformedTree "invalid tree structure")
  
    (* returns either the left child of key in kl/rightmost child if kl=[] *)
    let rec get_child tree kl =
      if Attrs.is_leaf tree then null_tree
      else match kl with
      | [] -> (match tree with
        | Il (_::next, _::cn, r, b, id) -> 
          get_child (Il (next, cn, r, b, id)) kl
        | Il ([], c::[], _, _, _) -> c
        | _ -> raise (MalformedTree "invalid tree structure"))
      | k::_ -> (match tree with
        | Il (v::next, c::cn, r, b, id) ->
          if v=k then c else get_child (Il (next, cn, r, b, id)) kl
        | Il ([], _::[], _, _, _) -> raise (NotFound "child node not found")
        | _ -> raise (MalformedTree "invalid tree structure"))
  
    (* replaces the child node associated with kl with newc *)
    let rec replace_child tree kl newc =
      if Attrs.is_leaf tree then null_tree
      else match kl with
      | [] -> (match tree with
        | Il (v::next, c::cn, r, b, id) -> 
        restore (replace_child (Il (next, cn, r, b, id)) kl newc) v c
        | Il ([], _::[], r, b, id) -> Il ([], newc::[], r, b, id)
        | _ -> raise (MalformedTree "invalid tree structure"))
      | k::_ -> (match tree with
        | Il (v::next, c::cn, r, b, id) ->
          if v=k then (Il (v::next, newc::cn, r, b, id))
          else restore (replace_child (Il (next, cn, r, b, id)) kl newc) v c
        | Il ([], _::[], _, _, _) -> raise (NotFound "child node not found")
      | _ -> raise (MalformedTree "invalid tree structure"))
  
    let rec insert_key tree k = match tree with
    | Lf (v::next, r, b, id) ->
      if k<v then Lf (k::v::next, r, b, id)
      else if k=v then Lf (k::next, r, b, id)
      else restore (insert_key (Lf (next, r, b, id)) k) v null_tree
    | Lf ([], r, b, id) -> Lf (k::[], r, b, id)
    | _ -> raise (InvalidOperation "cannot insert key in internal node")
  
    let rec remove_key tree k = match tree with
    | Lf (v::next, r, b, id) ->
      if v=k then Lf (next, r, b, id)
      else restore (remove_key (Lf (next, r, b, id)) k) v null_tree
    | _ -> raise (InvalidOperation "cannot remove key from internal node")
  
    (* replaces the child nodes of the key in kl with newc *)
    let rec replace_and_remove tree kl newc =
      match kl with
      | [] -> raise (NotFound "merge key not given")
      | k::_ -> (match tree with
        | Il (v::next, c1::c2::cn, r, b, id) ->
          if v=k then (Il (next, newc::cn, r, b, id)) 
          else 
            let tr = replace_and_remove (Il (next, (c2::cn), r, b, id)) kl newc
            in restore tr v c1
        | _ -> raise (NotFound "merge key to remove not found"))
  
    (* adds a key, payload and child to a node
      * key must not already be in the node *)
    let rec update_node tree k c1 c2 = match tree with
    | Il (v::next, c::cn, r, b, id) -> 
      if is_leaf c1 != is_leaf c then
        raise (MalformedTree "child node type mismatch")
      else if get_hd c1 = get_hd c then
        Il (k::v::next, c1::c2::cn, r, b, id)
      else restore (update_node (Il (next, cn, r, b, id)) k c1 c2) v c
    | Il ([], c::cn, r, b, id) -> (* right-most node *)
      if is_leaf c1 != is_leaf c then 
        raise (MalformedTree "child node type mismatch")
      else if get_hd c1 = get_hd c then 
        Il (k::[], c1::c2::cn, r, b, id)
      else raise (NotFound "child node to replace not found")
    | _ -> raise (MalformedTree "invalid tree structure")
    end

  open Tree_ops

  module Ids = struct
    let ids = ref []

    let store_id id hpointer cblockpointer =
      let current = !ids in
      let newi = List.filter ((fun (i, _) -> id != i)) current in
      ids := (id, (hpointer, cblockpointer))::newi

    let find_first_free_id _ =
      let ilist, _ = List.split !ids in
      let s = IdSet.of_list ilist in
      let max_id = IdSet.max_elt s in
      let free_ids set max = IdSet.(diff (of_list (List.init max (fun i -> (i+1)))) set) in
      let free = free_ids s max_id in
      if IdSet.is_empty free then (max_id+1)
      else IdSet.find_first (fun i -> i=i) free

    let get_node_pointers_from_id id = List.assoc id !ids

    let remove_id id =
      let current = !ids in
      let newi = List.filter (fun (i, _) -> id != i) current in
      ids := newi
    
    let get_all_node_pointers _ =
      let rec gather l acc = match l with
      | (_, (hp, cbp))::pairs -> 
        if Int64.(equal cbp max_int) then gather pairs (hp::acc)
        else gather pairs (hp::cbp::acc) 
      | [] -> acc in
      gather !ids []
    end

  module Serial = struct
    let write_block t pointer cs = 
      This_Block.write t.block pointer [cs] >>= function
      | Error _ -> Lwt.return @@ Error `Write_error
      | Ok () -> Lwt.return @@ Ok ()

    let read_pointers cs n lim =
      let rec aux cs acc n lim =
        if n<lim then acc
        else let p = Cstruct.LE.get_uint64 cs (n*sizeof_pointer) in
        aux cs (p::acc) (n-1) lim in
      aux cs [] n lim
    
    let write_data_block t pointer next pl =
      let cs = Cstruct.create t.block_size in
      Cstruct.LE.set_uint64 cs 0 next;
      Cstruct.blit_from_string pl 0 cs sizeof_pointer (String.length pl);
      write_block t pointer cs

    let read_data_block t pointer =
      let cs = Cstruct.create t.block_size in
      This_Block.read t.block pointer [cs] >>= function
      | Error _ -> Lwt.return @@ Error `Read_error
      | Ok () -> Lwt.return @@ Ok cs
    
    let write_cpointer_block t pointer cpointers =
      let cs = Cstruct.create t.block_size in
      for n=0 to (List.length cpointers - 1) do
        Cstruct.LE.set_uint64 cs (n*sizeof_pointer) (List.nth cpointers n);
      done;
      write_block t pointer cs
    
    let read_cpointer_block t pointer =
      let cs = Cstruct.create t.block_size in
      This_Block.read t.block pointer [cs] >>= function
      | Error _ -> Lwt.return @@ Error `Read_error
      | Ok () -> Lwt.return @@ Ok cs

    let parse_cpointer_block cs n = read_pointers cs n 0
    
    let write_head_block t tree hpointer cblockpointer =
      let nk = Attrs.n_keys tree in
      let cs = Cstruct.create t.block_size in
      let ks, _, _, _, id = Attrs.get_all tree in
      (* id of this node *)
      Cstruct.LE.set_uint64 cs 0 (Int64.of_int id);
      (* pointer to block containing child node pointers *)
      Cstruct.LE.set_uint64 cs sizeof_pointer cblockpointer;
      (* number of keys in this node *)
      Cstruct.LE.set_uint64 cs (2*sizeof_pointer) (Int64.of_int nk);
      for n=0 to nk-1 do
        Cstruct.LE.set_uint64 cs ((n+3)*sizeof_pointer) (List.nth ks n);
      done;
      write_block t hpointer cs

    let read_head_block t pointer =
      let cs = Cstruct.create t.block_size in
      This_Block.read t.block pointer [cs] >>= function
      | Error _ -> Lwt.return @@ Error `Read_error
      | Ok () -> Lwt.return @@ Ok cs

    let parse_keys cs =
      let nk = Int64.to_int (Cstruct.LE.get_uint64 cs (2*sizeof_pointer)) in
      let ks = List.sort Int64.compare (read_pointers cs (nk+2) 3) in
      nk, ks
    
    let rec of_cstruct t b pointer =
      let rec get_cn cpointers acc = match cpointers with
      | cptr::more_pointers -> of_cstruct t b cptr >>= (function
        | Error _ as e -> Lwt.return e
        | Ok (tr) -> get_cn more_pointers (tr::acc) )
      | [] -> Lwt.return @@ Ok (acc) in
      read_head_block t pointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let id = Int64.to_int (Cstruct.LE.get_uint64 hblock 0) in
        if (Int64.equal pointer 2L) && id!=1 then begin
          Ids.ids := [(1, (2L, Int64.max_int))];
          Lwt.return @@ Ok (Lf ([], true, b, 1))
        end else let cblockpointer = Cstruct.LE.get_uint64 hblock sizeof_pointer in
        Ids.store_id id pointer cblockpointer;
        let nk, ks = parse_keys hblock in
        let r = id = 1 in (* root node has id 1 *)
        if Int64.equal cblockpointer null_pointer then 
          Lwt.return @@ Ok (Lf (ks, r, b, id))
        else read_cpointer_block t cblockpointer >>= function
        | Error _ as e -> Lwt.return e
        | Ok cblock ->
          let cpointers = parse_cpointer_block cblock nk in
          get_cn cpointers [] >>= (function
          | Error _ as e -> Lwt.return @@ e
          | Ok cn_unsorted ->
            let cn = List.sort (fun tr1 tr2 -> 
              Int64.compare (get_hd tr1) (get_hd tr2)) cn_unsorted in
            Lwt.return @@ Ok (Il (ks, cn, r, b, id)))

    let get_block_pointers t n = 
      let get_block t = match !(t.lookahead).blocks with
      | p::ptrs -> 
        t.lookahead := {!(t.lookahead) with blocks = ptrs}; Lwt.return @@ Ok p
      | [] -> Lwt.return @@ Error `No_space in
      let rec aux t acc n =
        if n=0 then Lwt.return @@ Ok acc
        else get_block t >>= function
        | Error _ as e -> Lwt.return e
        | Ok p -> aux t (p::acc) (n-1) in
      aux t [] n
    end
  
  open Serial

  module Block_ops = struct
    let add_key_to_head_block t hpointer k =
      read_head_block t hpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let nk = Int64.to_int (Cstruct.LE.get_uint64 hblock (2*sizeof_pointer)) in
        Cstruct.LE.set_uint64 hblock (2*sizeof_pointer) (Int64.of_int (nk+1));
        Cstruct.LE.set_uint64 hblock ((nk+3)*sizeof_pointer) k;
        write_block t hpointer hblock

    let replace_key_in_head_block t hpointer k newk =
      read_head_block t hpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let nk, ks = parse_keys hblock in
        let newks = List.filter (fun i -> not (Int64.equal k i)) ks in
        Cstruct.LE.set_uint64 hblock ((nk+2)*sizeof_pointer) newk;
        for n=0 to (nk-2) do
          Cstruct.LE.set_uint64 hblock ((n+3)*sizeof_pointer) (List.nth newks n);
        done;
        (if Int64.(equal newk zero) then
          Cstruct.LE.set_uint64 hblock (2*sizeof_pointer) (Int64.of_int (nk-1)));
        write_block t hpointer hblock
    
    let add_cpointer_to_child_block t cblockpointer cpointer nk =
      read_cpointer_block t cblockpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok cblock -> 
        Cstruct.LE.set_uint64 cblock ((nk+1)*sizeof_pointer) cpointer;
        write_block t cblockpointer cblock

    let remove_cpointer_from_child_block t cblockpointer cpointer nk =
      read_cpointer_block t cblockpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok cblock ->
        let cpointers = parse_cpointer_block cblock nk in
        let new_cpointers = 
          List.filter (fun i -> not (Int64.equal cpointer i)) cpointers in
        for n=0 to nk-1 do
          Cstruct.LE.set_uint64 cblock (n*sizeof_pointer) (List.nth new_cpointers n);
        done;
        Cstruct.LE.set_uint64 cblock (nk*sizeof_pointer) (Int64.of_int 399);
        write_block t cblockpointer cblock
    end
  
  open Block_ops

  module Node_writes = struct
    let get_cpointers cn =
      let cn_ids = List.map Attrs.get_id cn in
      let cn_pointer_pairs = List.map Ids.get_node_pointers_from_id cn_ids in
      let hpointers, _cpointers = List.split cn_pointer_pairs in hpointers

    let write_node t tree hpointer cblockpointer =
      let commit_id id ptr = 
        Ids.store_id id hpointer ptr; 
        Lwt.return @@ Ok () in
      let _, cn, _, _, id = get_all tree in
      write_head_block t tree hpointer cblockpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok () ->
        if is_leaf tree then commit_id id null_pointer 
        else let cpointers = get_cpointers cn in
        write_cpointer_block t cblockpointer cpointers >>= function
        | Error _ as e -> Lwt.return e
        | Ok () -> commit_id id cblockpointer
    
    let write_node_split_update t id nk k cpointer =
      let hpointer, cblockpointer = Ids.get_node_pointers_from_id id in
      add_cpointer_to_child_block t cblockpointer cpointer nk >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> add_key_to_head_block t hpointer k
    end

  open Node_writes

  (* splits a node in two on a given key index
  * migrates key to parent node and returns parent, which may now be full
  * if the node is a root, this can increase the depth of the tree by 1 *)
  let split t tree parent m ignore =
    let split_node tree lid rid =
      let ks, cn, _, t, _ = get_all tree in
      let mk, lks, rks = split_ks m ks in
      let lcn, rcn = split_cn (m+1) cn in
      let tl, tr = 
        if (is_leaf tree) then Lf (lks, false, t, lid), Lf (rks, false, t, rid)
        else Il (lks, lcn, false, t, lid), Il (rks, rcn, false, t, rid) in 
      List.hd mk, tl, tr in
    let (_, _, root, b, cid), pid = get_all tree, get_id parent in
    let root_split = 
      if fst ignore then false else (root && (get_hd parent) = (get_hd tree)) in
    let pleaf, cleaf = is_leaf parent, is_leaf tree in
    if pleaf && not root_split then 
      raise (InvalidOperation "cannot split with leaf node as parent")
    else 
      let lid, rid = if fst ignore then snd ignore
      else if root_split then let i = Ids.find_first_free_id () in i, i+1
      else cid, Ids.find_first_free_id () in
      let mk, t_left, t_right = split_node tree lid rid in
      let newt = if root_split then Il (mk::[], t_left::t_right::[], true, b, pid)
      else update_node parent mk t_left t_right in
      let n_pointers = 
        if fst ignore then 0 
        (* if the root is being split and is a leaf it needs a cblockpointer *)
        else if root_split then if pleaf then 3 else 4
        else if cleaf then 1 else 2 in
      if fst ignore then Lwt.return @@ Ok newt else
        Serial.get_block_pointers t n_pointers >>= function
        | Error _ as e -> Lwt.return e
        | Ok pointers -> let hl, cl, hr, cr, crt = match pointers with
          | hl::hr::crt::[] when root_split && pleaf -> hl, null_pointer, hr, null_pointer, crt
          | hl::cl::hr::cr::[] when root_split && not pleaf -> hl, cl, hr, cr, null_pointer
          | hr::more when not root_split ->
            let hl, cl = Ids.get_node_pointers_from_id lid in 
            hl, cl, hr, (if cleaf then null_pointer else List.hd more), null_pointer
          | _ -> null_pointer, null_pointer, null_pointer, null_pointer, null_pointer in
          if Int64.equal hl null_pointer then Lwt.return @@ Error `No_space
          else write_node t t_left hl cl >>= function
          | Error _ as e -> Lwt.return e
          | Ok () -> write_node t t_right hr cr >>= function
            | Error _ as e -> Lwt.return e
            | Ok () ->  
              if root_split then begin
                let hpointer, cblockpointer = Ids.get_node_pointers_from_id pid in
                write_node t newt hpointer (min crt cblockpointer) >>= function
                | Error _ as e -> Lwt.return e
                | Ok () -> Lwt.return @@ Ok newt
              end else begin 
              write_node_split_update t pid (n_keys parent) mk hr >>= function
              | Error _ as e -> Lwt.return e
              | Ok () -> Lwt.return @@ Ok newt
              end

  let rec insertv t tree k p ckey ignore =
    let no_split = false, (-1, -1) in
    let _, _, root, b, id = get_all tree in
    let lim = 2*b-1 in
    let empty, full = (ckey < Int64.zero), n_keys tree = lim in
    if (full && root && not ignore) then
      split t tree tree (b-1) no_split >>= function
      | Error _ as e -> Lwt.return e
      | Ok tr -> insertv t tr k p (get_hd tr) false
    else if (full && not root && not ignore) then 
      raise (MalformedTree "full node not split ahead of time")
    else if (empty && root) then 
      Lwt.return @@ Ok (Tree_ops.insert_key tree k, id, false)
    else if empty then raise (MalformedTree "empty non-root node")
    else if k=ckey then Lwt.return @@ Ok (tree, id, true)
    else let next = get_next tree ckey in
      if (k>ckey && next != []) then insertv t tree k p (List.hd next) ignore
      else let pkey = if k<ckey then [ckey] else [] in
      if (is_leaf tree) then Lwt.return @@ Ok (insert_key tree k, id, false)
      else let c = get_child tree pkey in
        if (n_keys c) = lim then 
          split t c tree (b-1) no_split >>= function
          | Error _ as e -> Lwt.return e
          | Ok tr -> insertv t tr k p (Attrs.get_hd tr) true
        else insertv t c k p (Attrs.get_hd c) false >>= function
          | Error _ as e -> Lwt.return e
          | Ok (newc, cid, update) -> 
            Lwt.return @@ Ok (replace_child tree pkey newc, cid, update)
  
  let insert t tree k p next =
    let write_and_return tree = 
      write_data_block t k next p >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> Lwt.return @@ Ok tree in
    if Int64.(equal k max_int) then begin
      Lwt.return @@ Error `Write_error 
    end else let _, _, root, _, _ = get_all tree in
    if not root then 
      raise (InvalidOperation "insert can only be called on a root node")
    else 
      let ckey = try get_hd tree with Failure _ -> Int64.minus_one in
      insertv t tree k p ckey false >>= function
      | Error _ as e -> Lwt.return e
      | Ok (newt, id, update) ->
        if not update then
          let hpointer, _cpointer = Ids.get_node_pointers_from_id id in
          add_key_to_head_block t hpointer k >>= function
          | Error _ as e -> Lwt.return e
          | Ok () -> write_and_return newt
        else write_and_return newt
      
  (* takes two child nodes and merges them into one node 
  * the parent node loses a key in the process
  * if the node is a root, this can decrease the depth by 1 *)
  let rec merge t parent ckey s1 s2 ignore =
    let check_length l b = 
      if ((l < b-1 || l > 2*b-1) && not ignore) then 
        raise (InvalidOperation "merge will result in an invalid node") 
      else () in
    let _, _, root, b, pid = get_all parent in
    let one_key, next = n_keys parent = 1, get_next parent ckey in
    let s1_leaf, s2_leaf = is_leaf s1, is_leaf s2 in
    if ((s1_leaf && not s2_leaf) || (s2_leaf && not s1_leaf)) then
      raise (MalformedTree "internal node and leaf node at same level")
    else if (is_leaf parent) then 
      raise (InvalidOperation "cannot merge with leaf node as parent")
    else
      let m1, m2 = get_child parent [ckey] = s1, get_child parent next = s2 in
      if m1 && m2 then
        let k1s, cn1, _, _, lid = get_all s1 in
        let k2s, cn2, _, _, rid = get_all s2 in
        let _ = check_length (List.length k1s + List.length k2s + 1) b in
        let merged_ks, merged_cn = k1s @ (ckey::k2s), cn1 @ cn2 in
        let reduce = root && one_key && not ignore in
        let mid = if reduce then pid else lid in
        let s = if s1_leaf then Lf (merged_ks, reduce, b, mid)
        else Il (merged_ks, merged_cn, reduce, b, mid) in
        if reduce then begin
          let hl, cl = Ids.get_node_pointers_from_id lid in
          let hr, cr = Ids.get_node_pointers_from_id rid in
          let hpointer, cblockpointer = Ids.get_node_pointers_from_id pid in
          let crt = if is_leaf s then Int64.max_int else cblockpointer in
          write_node t s hpointer crt >>= function
          | Error _ as e -> Lwt.return e
          | Ok () -> 
            Ids.remove_id lid; Ids.remove_id rid;
            if is_leaf s then Lwt.return @@ Ok (s, [hl; hr; cblockpointer])
            else Lwt.return @@ Ok (s, [hl; cl; hr; cr])
        end else begin
          let tr = replace_and_remove parent [ckey] s in
          if ignore then Lwt.return @@ Ok (tr, []) else begin
            let hl, cl = Ids.get_node_pointers_from_id lid in
            write_node t s hl cl >>= function
            | Error _ as e -> Lwt.return e
            | Ok () ->
              let hpointer, cblockpointer = Ids.get_node_pointers_from_id pid in
              let cpointer, _ = Ids.get_node_pointers_from_id rid in
              remove_cpointer_from_child_block t cblockpointer cpointer (n_keys parent) >>= function
              | Error _ as e -> Lwt.return e
              | Ok () -> replace_key_in_head_block t hpointer ckey (Int64.of_int 593) >>= function
                | Error _ as e -> Lwt.return e
                | Ok () -> 
                  let hr, cr = Ids.get_node_pointers_from_id rid in
                  Ids.remove_id rid; Lwt.return @@ Ok (tr, [hr; cr])
            end
        end
      else if next=[] then raise (NotFound "could not find sibling nodes")
      else merge t parent (List.hd next) s1 s2 ignore

  let rec find_predecessor tree k = 
    let rec get_largest tree =
      let rec last l = match l with
      | c::cs -> if cs=[] then c else last cs 
      | [] -> raise (Failure "empty list") in
      if is_leaf tree then
        let ks, _, _, _, _ = get_all tree in last ks
      else let c2 = get_child tree [] in get_largest c2 
    in match tree with
    | Lf (v::next, r, t, id) ->
      if next=[] then raise (NotFound "key not found")
      else if List.hd next=k then v
      else find_predecessor (Lf (next, r, t, id)) k
    | Il (v::next, c1::c2::cn, r, t, id) ->
      if k=v then get_largest c1
      else if k<v then find_predecessor c1 k
      else if next=[] then find_predecessor c2 k 
      else find_predecessor (Il (next, c2::cn, r, t, id)) k
    | _ -> raise (MalformedTree "tree structure invalid")

  let rec find_successor tree k = 
    let rec get_smallest tree =
      if is_leaf tree then get_hd tree
      else let c1 = get_child tree [get_hd tree] in get_smallest c1
    in match tree with
    | Lf (v::next, r, t, id) ->
      if next=[] then raise (NotFound "key not found")
      else if v=k then List.hd next
      else find_successor (Lf (next, r, t, id)) k
    | Il (v::next, c1::c2::cn, r, t, id) ->
      if k=v then get_smallest c2
      else if k<v then find_successor c1 k
      else if next=[] then find_successor c2 k 
      else find_successor (Il (next, c2::cn, r, t, id)) k
    | _ -> raise (MalformedTree "tree structure invalid")

  (* swaps the positions of (oldkey, oldpl) and (newkey, newpl) in a tree
  * newkey must be either the predecessor or successor of oldkey 
  * it must also be at a lower depth than oldkey
  * found = 0 - not found
  * found = 1 - found in this node 
  * found = 2 - found higher in the tree *)
  let rec swap t tree ok nk ckey found index =
    let replace id k1 k2 =
      let hpointer, _ = Ids.get_node_pointers_from_id id in
      replace_key_in_head_block t hpointer k1 k2 in
    let swap_child tree kl f = 
      let c = get_child tree kl in 
      swap t c ok nk (get_hd c) f 0 >>= function
      | Error _ as e -> Lwt.return e
      | Ok newc -> Lwt.return @@ Ok (replace_child tree kl newc) in
    let swap_next tree kl f = 
      swap t tree ok nk (List.hd kl) f (index+1) in
    let replace_in_list l n = 
      List.mapi (fun i a -> if i=index then n else a) l in
    let ks, cn, r, b, id = get_all tree in
    let leaf, next = is_leaf tree, get_next tree ckey in
    let successor = nk>ok in
    if ckey=nk then
      if (found=0 || not leaf) then raise (MalformedTree "order violation")
      else begin 
        let tr = Lf (replace_in_list ks ok, r, b, id) in
        if found=1 then Lwt.return @@ Ok tr
        else replace id nk ok >>= function
        | Error _ as e -> Lwt.return e
        | Ok () -> Lwt.return @@ Ok tr
      end 
    else if (ckey=ok || found>0) then
      let nt = if ckey!=ok then Lwt.return @@ Ok tree else
        replace id ok nk >>= function
        | Error _ as e -> Lwt.return @@ e
        | Ok () ->
          if leaf then Lwt.return @@ Ok (Lf (replace_in_list ks nk, r, b, id))
          else Lwt.return @@ Ok (Il (replace_in_list ks nk, cn, r, b, id))
      in nt >>= function
      | Error _ as e -> Lwt.return e
      | Ok newt ->
      if (next=[] && leaf) then 
        raise (NotFound "at least one key in 
      swap not found")
      (* either key and successor are both in this leaf 
        or predecessor is the rightmost key *)
      else if leaf then swap_next newt next (max 1 found)
      else if found=0 then let kl = if successor then next else [nk] in 
        swap_child newt kl 2 (* pick edge to go down *)
      else (* find smallest key in subtree if successor *)
        if successor then swap_child newt [ckey] 2
        else if next=[] then swap_child newt next 2
        else swap_next newt next (max 1 found) (* and largest key if predecessor *)
    else if ckey>ok then
      if next=[] then swap_child tree next 0
      else swap_next tree next 0
    else swap_child tree [ckey] 0

  (* redistributes a key from morec to its immediate sibling node *)
  let steal t tree ckey morec =
    let rec store_ops l r = match l with
    | f::fs -> f >>= (function
      | Error _ as e -> Lwt.return e
      | Ok () -> store_ops fs r)
    | [] -> Lwt.return @@ Ok r in
    let _, _, _, b, pid = get_all tree in
    let next = get_next tree ckey in
    let ca, cb = get_child tree [ckey], get_child tree next in
    let ca_id, cb_id = get_id ca, get_id cb in
    merge t tree ckey ca cb true >>= fun r -> 
      let mt = match r with | Ok (tr, _) -> tr | _ -> null_tree in
    let merged_child = get_child mt next in
    let lim = (if ca=morec then (n_keys ca)-1 else if cb=morec then b else -1) in
    if lim = -1 then raise (NotFound "child node not found")
    else split t merged_child mt lim (true, (ca_id, cb_id)) >>= fun r -> 
      let tr = match r with | Ok tr -> tr | _ -> null_tree in
      let new_sp = let ks, _, _, _, _ = get_all merged_child in List.nth ks lim in
      let lessc = if ca=morec then cb else ca in
      let lid, mid = get_id lessc, get_id morec in
      let hpointer, _ = Ids.get_node_pointers_from_id pid in 
      let lpointer, lcpointer = Ids.get_node_pointers_from_id lid in
      let mpointer, mcpointer = Ids.get_node_pointers_from_id mid in
      let ops =
      [replace_key_in_head_block t hpointer ckey new_sp;
      replace_key_in_head_block t mpointer new_sp (Int64.of_int 723);
      add_key_to_head_block t lpointer ckey] in
      if is_leaf morec then store_ops ops tr else begin
        let movedc_key = if morec=cb then [get_hd morec] else [] in
        let movedc_cpointer, _ = 
          Ids.get_node_pointers_from_id (get_id (get_child morec movedc_key)) in
        let more_ops = 
        [remove_cpointer_from_child_block t mcpointer movedc_cpointer (n_keys morec);
        add_cpointer_to_child_block t lcpointer movedc_cpointer (n_keys lessc)] in
        store_ops (ops @ more_ops) tr
      end

  let rec deletev t tree k ckey pointers swapped =
    if ckey<Int64.zero then Lwt.return @@ Ok (tree, pointers)
    else 
      let ks, _, _, b, id = get_all tree in
      let leaf, next = is_leaf tree, get_next tree ckey in
      let ca, cb = 
      if not leaf then get_child tree [ckey], get_child tree next 
      else null_tree, null_tree in
      let l1, l2 = n_keys ca, n_keys cb in
      let left, right, lempty, rempty = k<ckey, k>ckey && next=[], l1<b, l2<b in
      (* swapping causes an inversion *)
      let leftc, rightc = if swapped then not left, left else left, right in
      if k=ckey then
        if leaf then begin
          let hpointer, _ = Ids.get_node_pointers_from_id id in
          replace_key_in_head_block t hpointer k (Int64.of_int 750) >>= function
          | Error _ as e -> Lwt.return e
          | Ok () -> Lwt.return @@ Ok (remove_key tree k, pointers)
        end else if not (lempty && rempty) then
          let key_to_swap = (* swap with inorder predecessor/successor *)
            (if lempty then find_successor else find_predecessor) tree ckey in
          swap t tree ckey key_to_swap ckey 0 (get_index ks ckey 0) >>= function
          | Error _ as e -> Lwt.return e
          | Ok tr -> deletev t tr k key_to_swap pointers true
          (* merge around key to delete if neither child node has enough keys *)
        else merge t tree ckey ca cb false >>= function
        | Error _ as e -> Lwt.return e
        | Ok (tr, freed) -> deletev t tr k (get_hd tr) (pointers @ freed) false
      else if not (leftc || rightc) then deletev t tree k (List.hd next) pointers false
      else if not leaf then
        let c = if lempty || (rightc && not rempty) then cb else ca in
        let ok = (leftc && not lempty) || (rightc && not rempty) in
        if ok then (* k is in subtree which can lose a key *)
          deletev t c k (get_hd c) pointers false >>= function
          | Error _ as e -> Lwt.return e
          | Ok (c_del, freed) ->
            Lwt.return @@ Ok (replace_child tree (if leftc then [ckey] else next) c_del, freed)
        else if lempty && rempty then (* merge needed *)
          merge t tree ckey ca cb false >>= function
          | Error _ as e -> Lwt.return e
          | Ok (tr, freed) -> deletev t tr k (get_hd tr) (pointers @ freed) false
          (* steal a key a sibling of the subtree containing k *)
        else steal t tree ckey c >>= function
        | Error _ as e -> Lwt.return e
        | Ok tr -> deletev t tr k (get_hd tr) pointers false
      else if left || right then raise (NotFound "key to delete not found")
      else deletev t tree k (List.hd next) pointers false (* continue searching this leaf *)

  let delete t tree k = 
    let _, _, root, _, _ = get_all tree in
    if not root then 
      raise (InvalidOperation "delete can only be called on a root node")
    else deletev t tree k (try get_hd tree with Failure _ -> Int64.minus_one) [] false

  let rec delete_list t tree keys pointers = match keys with
  | k::ks -> delete t tree k >>= (function
   | Error _ as e -> Lwt.return e
   | Ok (tr, pointers) -> delete_list t tr ks pointers)
  | [] -> Lwt.return @@ Ok (tree, (List.filter (fun f -> not Int64.(equal f max_int)) pointers)) 
  end
