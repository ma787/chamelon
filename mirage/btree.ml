type keys = int32 list
type pls = int64 list
type node = 
| Lf of keys * pls * bool * int * int64
| Il of keys * pls * int64 list * bool * int * (int64 * int64)

exception MalformedTree of string
exception InvalidOperation of string

let null_pointer = Int64.max_int
let null_tree = Lf ([], [], false, 0, null_pointer)
let root_pointer = 2L

open Lwt.Infix

module Make(Sectors: Mirage_block.S) = struct
  module Block_types = Block_type.Make (Sectors)

  open Block_types
  let sizeof_pointer = 8
  let sizeof_key = 4

  type error = [
    | `Read_error
    | `Write_error
    | `No_space
  ]

  module Offsets = struct
    let valid = 0
    let nk = 2
    let first_key = 4
    let last_key n_keys = 4*n_keys
    let first_pl b = 8*b
    let last_pl b n_keys = 8*(b + n_keys - 1)
    let cb_pointer b = 24*b - 8
  end

  module Attrs = struct
    let n_keys tree = match tree with
    | Il (ks, _, _, _, _, _) -> List.length ks
    | Lf (ks, _, _, _, _) -> List.length ks
  
    let get_hd tree = match tree with
    | Il (ks, _, _, _, _, _) -> List.hd ks
    | Lf (ks, _, _, _, _) -> List.hd ks
  
    let is_leaf tree = match tree with
    | Il _ -> false
    | Lf _ -> true

    let is_empty tree = match tree with
    | Il (ks, _, _, _, _, _) -> ks=[]
    | Lf (ks, _, _, _, _) -> ks=[]
  
    let get_all tree = match tree with
    | Il (ks, pls, cn, r, b, _) -> ks, pls, cn, r, b
    | Lf (ks, pls, r, b, _) -> ks, pls, [], r, b

    let get_pointers tree = match tree with
    | Il (_, _, _, _, _, (hptr, cbptr)) -> hptr, cbptr
    | Lf (_, _, _, _, ptr) -> ptr, null_pointer
  
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
  
    let to_string tree = 
      let ks, pls, cn, r, b = get_all tree in
      let string_of_list l f = 
        "{" ^ (List.fold_left (fun acc x -> 
          acc ^ f x ^ ",") "" l) ^ "}" in
      let f, g = Int32.to_string, Int64.to_string in
      "(" ^ (string_of_list ks f) ^ ", " ^ (string_of_list pls g) ^ 
      ", " ^ (string_of_list cn g) ^ (string_of_bool r) ^ ", " ^ 
      (string_of_int b) ^ ")"
    end

  open Attrs

  module Serial = struct
    let write_block t pointer cs = 
      This_Block.write t.block pointer [cs] >>= function
      | Error _ -> Lwt.return @@ Error `Write_error
      | Ok () -> Lwt.return @@ Ok ()

    let read_block t pointer =
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

    let parse_cpointer_block cs n = 
      let rec aux cs acc n lim =
        if n<lim then acc
        else let p = Cstruct.LE.get_uint64 cs (n*sizeof_pointer) in
        aux cs (p::acc) (n-1) lim in
      aux cs [] n 0
    
    let write_head_block t tree =
      let nk = Attrs.n_keys tree in
      let hpointer, cblockpointer = get_pointers tree in
      let cs = Cstruct.create t.block_size in
      let ks, pls, _, _, b = Attrs.get_all tree in
      (* value identifying the root node *)
      let v = if Int64.equal hpointer root_pointer then 1 else 0 in
      Cstruct.LE.set_uint16 cs Offsets.valid v; 
      (* number of keys in this node *)
      Cstruct.LE.set_uint16 cs Offsets.nk nk;
      for n=0 to nk-1 do
        Cstruct.LE.set_uint32 cs (Offsets.first_key + n*sizeof_key) (List.nth ks n);
        Cstruct.LE.set_uint64 cs ((Offsets.first_pl b) + n*sizeof_pointer) (List.nth pls n);
      done;
      (* pointer to block containing child node pointers *)
      Cstruct.LE.set_uint64 cs (Offsets.cb_pointer b) cblockpointer;
      write_block t hpointer cs

    let write_empty_root t tree =
      let _, _, _, _, b = get_all tree in
      let hpointer, cblockpointer = get_pointers tree in
      let cs = Cstruct.create t.block_size in
      Cstruct.LE.set_uint16 cs Offsets.valid 1;
      Cstruct.LE.set_uint16 cs Offsets.nk 0;
      Cstruct.LE.set_uint64 cs (Offsets.cb_pointer b) cblockpointer;
      write_block t hpointer cs

    let parse_keys cs =
      let rec aux cs acc n =
        if n < Offsets.first_key then acc
        else let k = Cstruct.LE.get_uint32 cs n in
        aux cs (k::acc) (n-sizeof_key) in
      let nk = Cstruct.LE.get_uint16 cs Offsets.nk in
      nk, aux cs [] (Offsets.last_key nk)

    let parse_pls cs b =
      let rec aux cs acc n =
        if n < Offsets.first_pl b then acc
        else let pl = Cstruct.LE.get_uint64 cs n in
        aux cs (pl::acc) (n-sizeof_pointer) in
      let nk = Cstruct.LE.get_uint16 cs Offsets.nk in
      aux cs [] (Offsets.last_pl b nk)

    let read_node t b pointer =
      read_block t pointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let r = (Int64.equal pointer root_pointer) in
        let valid = Cstruct.LE.get_uint16 hblock Offsets.valid in
        if valid!=1 then 
          if r then Lwt.return @@ Ok (Lf ([], [], true, b, pointer), false)
          else Lwt.return @@ Error `Read_error
        else let cblockpointer = Cstruct.LE.get_uint64 hblock (Offsets.cb_pointer b) in
        let nk, ks = parse_keys hblock in
        let pls = parse_pls hblock b in
        if Int64.equal cblockpointer null_pointer then 
          Lwt.return @@ Ok (Lf (ks, pls, r, b, pointer), true)
        else read_block t cblockpointer >>= function
        | Error _ as e -> Lwt.return e
        | Ok cblock ->
          let cpointers = parse_cpointer_block cblock nk in
          Lwt.return @@ Ok (Il (ks, pls, cpointers, r, b, (pointer, cblockpointer)), true)

    (* get_all_pointers marks every pointer in the b-tree as used in the bitmap [arr] *)
    let rec get_all_pointers t b hpointer arr =
      let rec mark_pointers lookahead pointers = match pointers with
      | p::ps -> Cstruct.set_uint8 lookahead (Int64.to_int p) 1; mark_pointers lookahead ps
      | [] -> lookahead in
      read_block t hpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let pls = parse_pls hblock b in
        let new_arr = mark_pointers arr pls in
        Cstruct.set_uint8 new_arr (Int64.to_int hpointer) 1;
        let cblockpointer = Cstruct.LE.get_uint64 hblock (Offsets.cb_pointer b) in
        if Int64.(equal cblockpointer max_int) then Lwt.return @@ Ok new_arr
        else read_block t cblockpointer >>= function
        | Error _ as e -> Lwt.return e
        | Ok cblock -> 
          let nk = Cstruct.LE.get_uint16 hblock Offsets.nk in
          let cpointers = parse_cpointer_block cblock (nk+1) in
          Lwt_list.fold_left_s (fun arr_res cpointer -> match arr_res with
          | Error _ as e -> Lwt.return e
          | Ok old_arr ->
            get_all_pointers t b cpointer old_arr >>= function
            | Error _ as e -> Lwt.return e
            | Ok n_arr -> Lwt.return @@ Ok n_arr) (Ok new_arr) cpointers
    end
  
  open Serial

  module Tree_ops = struct
    (* adds key k, payload p and child c to each associated list *)
    let restore tree k p c = match tree with
    | Lf ([], [], r, b, ptr) -> Lf (k::[], p::[], r, b, ptr)
    | Lf (v::next, pl::pls, r, b, ptr) -> Lf (k::v::next, p::pl::pls, r, b, ptr)
    | Il ([], [], cn, r, b, ptrs) -> Il (k::[], p::[], c::cn, r, b, ptrs)
    | Il (v::next, pl::pls, cn, r, b, ptrs) -> Il (k::v::next, p::pl::pls, c::cn, r, b, ptrs)
    | _ -> raise (MalformedTree "invalid tree structure")
  
    (* returns [next key] or [] if k is the rightmost key in the node *)
    let rec get_next tree k = match tree with
    | Il (v::next, _::pls, _::cn, r, b, ptrs) ->
      if v=k then try [List.hd next] with Failure _ -> []
      else get_next (Il (next, pls, cn, r, b, ptrs)) k
    | Il ([], [], _, _, _, _) -> []
    | Lf (v::next, _::pls, r, b, ptr) ->
      if v=k then try [List.hd next] with Failure _ -> []
      else get_next (Lf (next, pls, r, b, ptr)) k
    | _ -> raise (MalformedTree "invalid tree structure")

    let rec get_pl_from_key tree k = match tree with
    | Il (v::next, pl::pls, _::cn, r, b, ptrs) -> 
      if v=k then pl else get_pl_from_key (Il (next, pls, cn, r, b, ptrs)) k
    | Lf (v::next, pl::pls, r, b, ptr) ->
      if v=k then pl else get_pl_from_key (Lf (next, pls, r, b, ptr)) k
    | _ -> raise Not_found

    let rec get_cpointer tree kl =
      if Attrs.is_leaf tree then null_pointer
      else match kl with
      | [] -> (match tree with
        | Il (_::next, _::pls, _::cn, r, b, ptrs) -> 
          get_cpointer (Il (next, pls, cn, r, b, ptrs)) kl
        | Il ([], [], c::[], _, _, _) -> c
        | _ -> raise (MalformedTree "invalid tree structure"))
      | k::_ -> (match tree with
        | Il (v::next, _::pls, c::cn, r, b, ptrs) ->
          if v=k then c else get_cpointer (Il (next, pls, cn, r, b, ptrs)) kl
        | Il ([], [], _::[], _, _, _) -> raise Not_found
        | _ -> raise (MalformedTree "invalid tree structure"))
  
    (* reads in either the left child of key in kl/rightmost child if kl=[] *)
    let get_child t tree kl =
      let _, _, _, _, b = get_all tree in
      let cpointer = get_cpointer tree kl in
      read_node t b cpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok (tr, _) -> Lwt.return @@ Ok tr
  
    let rec insert_key_and_pl tree k p = match tree with
    | Lf (v::next, pl::pls, r, b, ptr) ->
      if k<v then Lf (k::v::next, p::pl::pls, r, b, ptr)
      else if k=v then Lf (k::next, p::pls, r, b, ptr)
      else restore (insert_key_and_pl (Lf (next, pls, r, b, ptr)) k p) v pl null_pointer
    | Lf ([], [], r, b, ptr) -> Lf (k::[], p::[], r, b, ptr)
    | _ -> raise (InvalidOperation "cannot insert key in internal node")
    
    let rec update_node tree k p cptr = match tree with
    | Il (v::next, pl::pls, c::cn, r, b, ptrs) -> 
      if k<v then
        Il (k::v::next, p::pl::pls, cptr::c::cn, r, b, ptrs)
      else restore (update_node (Il (next, pls, cn, r, b, ptrs)) k p cptr) v pl c
    | Il ([], [], c::cn, r, b, ptrs) -> Il (k::[], p::[], cptr::c::cn, r, b, ptrs)
    | _ -> raise (MalformedTree "invalid tree structure")
    
    let rec remove_key tree k = match tree with
    | Lf (v::next, pl::pls, r, b, ptr) ->
      if v=k then Lf (next, pls, r, b, ptr)
      else restore (remove_key (Lf (next, pls, r, b, ptr)) k) v pl null_pointer
    | _ -> raise (InvalidOperation "cannot remove key from internal node")
    end

  open Tree_ops

  module Block_ops = struct
    let rec get_key_index x l i = match l with
      | c::cs -> if Int32.equal x c then i else get_key_index x cs (i+1)
      | [] -> -1
    
    let add_key_and_pl_to_hblock t b hpointer k p =
      read_block t hpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let nk = Cstruct.LE.get_uint16 hblock Offsets.nk in
        Cstruct.LE.set_uint16 hblock Offsets.nk (nk+1);
        Cstruct.LE.set_uint32 hblock (Offsets.last_key (nk+1)) k;
        Cstruct.LE.set_uint64 hblock (Offsets.last_pl b (nk+1)) p;
        write_block t hpointer hblock

    let replace_key_and_pl_in_hblock t b hpointer k newk newp =
      read_block t hpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let _, ks = parse_keys hblock in
        let key_index = get_key_index k ks 0 in
        Cstruct.LE.set_uint32 hblock (Offsets.last_key (key_index+1)) newk;
        Cstruct.LE.set_uint64 hblock (Offsets.last_pl b (key_index+1)) newp;
        write_block t hpointer hblock
    
    let remove_key_and_pl_in_hblock t b hpointer k pl =
      read_block t hpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let nk, ks = parse_keys hblock in
        let pls = parse_pls hblock b in
        let newks = List.(sort Int32.compare (filter (fun i -> Int32.equal i k) ks)) in
        let newpls = List.filter (fun i -> Int64.equal i pl) pls in
        Cstruct.LE.set_uint16 hblock Offsets.nk (nk-1);
        for n=0 to nk-2 do
          Cstruct.LE.set_uint32 hblock (Offsets.first_key + n*sizeof_key) (List.nth newks n);
          Cstruct.LE.set_uint64 hblock ((Offsets.first_pl b) + n*sizeof_pointer) (List.nth newpls n);
        done;
        write_block t hpointer hblock
    
    let add_cpointer_to_child_block t cblockpointer cpointer nk =
      read_block t cblockpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok cblock ->
        Cstruct.LE.set_uint64 cblock ((nk+1)*sizeof_pointer) cpointer;
        write_block t cblockpointer cblock

    let remove_cpointer_from_child_block t cblockpointer cpointer nk =
      read_block t cblockpointer >>= function
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
    let write_node t tree =
      let _, _, cpointers, _, _ = get_all tree in
      let _, cblockpointer = get_pointers tree in
      write_head_block t tree >>= function
      | Error _ as e -> Lwt.return e
      | Ok () ->
        if is_leaf tree then Lwt.return @@ Ok ()
        else write_cpointer_block t cblockpointer cpointers >>= function
        | Error _ as e -> Lwt.return e
        | Ok () -> Lwt.return @@ Ok ()
    
    let write_node_split_update t b nk k pl hpointer cblockpointer cpointer =
      add_cpointer_to_child_block t cblockpointer cpointer nk >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> add_key_and_pl_to_hblock t b hpointer k pl
    end

  open Node_writes

  let rec search t tree k ckey =
    if is_leaf tree then
      if Int32.equal ckey k then Lwt.return @@ Ok tree
      else let next = get_next tree ckey in
      if next=[] then Lwt.return @@ Error `Not_found
      else search t tree k (List.hd next)
    else if Int32.equal ckey k then Lwt.return @@ Ok tree
    else if k<ckey then get_child t tree [ckey] >>= function
    | Error _ as e -> Lwt.return e
    | Ok c -> search t c k (get_hd c)
    else let next = get_next tree ckey in
      if next=[] then get_child t tree next >>= function
      | Error _ as e -> Lwt.return e
      | Ok c -> search t c k (get_hd c)
      else search t tree k (List.hd next) 

  let rec get_largest t tree ckey =
    if ckey<Int32.zero then Lwt.return @@ Ok Int32.zero
    else if is_leaf tree then
      let next = get_next tree ckey in
      if next=[] then Lwt.return @@ Ok ckey
      else get_largest t tree (List.hd next)
    else get_child t tree [] >>= function
    | Error _ as e -> Lwt.return e
    | Ok c -> get_largest t c (get_hd c)

  (* splits a node in two on a given key index
  * migrates key to parent node and returns parent, which may now be full
  * if the node is a root, this can increase the depth of the tree by 1 *)
  let split t tree parent m rptr =
    let ignore = not (Int64.equal rptr null_pointer) in
    let split_lists tree =
      let ks, pls, cn, _, _ = get_all tree in
      let mk, lks, rks = split_ks m ks in
      let mp, lpls, rpls = split_ks m pls in
      let lcn, rcn = split_cn (m+1) cn in
      List.hd mk, List.hd mp, lks, lpls, lcn, rks, rpls, rcn in
    let _, _, _, root, b = get_all tree in
    let root_split = 
      if ignore then false else (root && (get_hd parent) = (get_hd tree)) in
    let pleaf, cleaf = is_leaf parent, is_leaf tree in
    if pleaf && not root_split then 
      raise (InvalidOperation "cannot split with leaf node as parent")
    else
      let mk, mp, lks, lpls, lcn, rks, rpls, rcn = split_lists tree in
      let n_pointers = 
        if ignore then 0 
        (* if the root is being split and is a leaf it needs a cblockpointer *)
        else if root_split then if pleaf then 3 else 4
        else if cleaf then 1 else 2 in
      if ignore then
        Lwt.return @@ Ok (update_node parent mk mp rptr) else
        Allocate.get_blocks t n_pointers >>= function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok blocks ->
          let hl, cl, hr, cr, crt =
            if root_split then
              if pleaf then 
                Cstruct.LE.(get_uint64 blocks 0, null_pointer, get_uint64 blocks 1,
            null_pointer, get_uint64 blocks 2)
              else Cstruct.LE.(get_uint64 blocks 0, get_uint64 blocks 1, get_uint64 blocks 2,
              get_uint64 blocks 3, null_pointer)
            else let hl, cl = get_pointers tree in
            Cstruct.LE.(hl, cl, get_uint64 blocks 0, 
            (if cleaf then null_pointer else get_uint64 blocks 1), null_pointer) in
          let hp, cbp = get_pointers parent in
          let t_left, t_right = 
            if cleaf then Lf (lks, lpls, false, b, hl), Lf (rks, rpls, false, b, hr)
            else Il (lks, lpls, lcn, false, b, (hl, cl)), Il (rks, rpls, rcn, false, b, (hr, cr)) in
          if Int64.equal hl null_pointer then Lwt.return @@ Error `No_space
          else write_node t t_left >>= function
          | Error _ as e -> Lwt.return e
          | Ok () -> write_node t t_right >>= function
            | Error _ as e -> Lwt.return e
            | Ok () ->  
              if root_split then begin
                let new_cbp = min crt cbp in
                let newt = Il (mk::[], mp::[], hl::hr::[], true, b, (hp, new_cbp)) in
                write_node t newt >>= function
                | Error _ as e -> Lwt.return e
                | Ok () -> Lwt.return @@ Ok newt
              end else begin 
              write_node_split_update t b (n_keys parent) mk mp hr hp cbp >>= function
              | Error _ as e -> Lwt.return e
              | Ok () -> Lwt.return @@ Ok (update_node parent mk mp hr)
              end

  let rec insertv t tree k p ckey ignore =
    let _, _, _, root, b = get_all tree in
    let lim = 2*b-1 in
    let empty, full = (ckey < Int32.zero), n_keys tree = lim in
    if (full && root && not ignore) then
      split t tree tree (b-1) null_pointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok tr -> insertv t tr k p (get_hd tr) false
    else if (full && not root && not ignore) then 
      raise (MalformedTree "full node not split ahead of time")
    else if (empty && root) then
      let tr = insert_key_and_pl tree k p in Lwt.return @@ Ok (tr, tr, false)
    else if empty then raise (MalformedTree "empty non-root node")
    else if k=ckey then Lwt.return @@ Ok (tree, tree, true)
    else let next = get_next tree ckey in
      if (k>ckey && next != []) then insertv t tree k p (List.hd next) ignore
      else let pkey = if k<ckey then [ckey] else [] in
      if (is_leaf tree) then 
        let tr = insert_key_and_pl tree k p in Lwt.return @@ Ok (tr, tr, false)
      else get_child t tree pkey >>= function
      | Error _ as e -> Lwt.return e
      | Ok c ->
        if (n_keys c) = lim then 
          split t c tree (b-1) null_pointer >>= function
          | Error _ as e -> Lwt.return e
          | Ok tr -> insertv t tr k p (Attrs.get_hd tr) true
        else insertv t c k p (Attrs.get_hd c) false >>= function
          | Error _ as e -> Lwt.return e
          | Ok (_, lf, update) -> 
            Lwt.return @@ Ok (tree, lf, update)
  
  let insert t tree k p =
    let _, _, _, root, b = get_all tree in
    if not root then 
      raise (InvalidOperation "insert can only be called on a root node")
    else 
      let ckey = try get_hd tree with Failure _ -> Int32.minus_one in
      insertv t tree k p ckey false >>= function
      | Error _ as e -> Lwt.return e
      | Ok (newt, new_lf, update) ->
        let hpointer, _cpointer = get_pointers new_lf in
        if update then 
          replace_key_and_pl_in_hblock t b hpointer k k p >>= function
          | Error _ as e -> Lwt.return e
          | Ok () -> Lwt.return @@ Ok newt
        else add_key_and_pl_to_hblock t b hpointer k p >>= function
        | Error _ as e -> Lwt.return e
        | Ok () -> Lwt.return @@ Ok newt
      
 (* takes two child nodes and merges them into one node 
  * the parent node loses a key in the process
  * if the node is a root, this can decrease the depth by 1
  * returns the parent node, the merged child and any unused pointers *)
  let rec merge t parent ckey s1 s2 ignore =
    let check_length l b = 
      if ((l < b-1 || l > 2*b-1) && not ignore) then 
        raise (InvalidOperation "merge will result in an invalid node") 
      else () in
    let _, _, _, root, b = get_all parent in
    let one_key, next = n_keys parent = 1, get_next parent ckey in
    let s1_leaf, s2_leaf = is_leaf s1, is_leaf s2 in
    if ((s1_leaf && not s2_leaf) || (s2_leaf && not s1_leaf)) then
      raise (MalformedTree "internal node and leaf node at same level")
    else if (is_leaf parent) then 
      raise (InvalidOperation "cannot merge with leaf node as parent")
    else
      let hl, cl = get_pointers s1 in
      let hr, cr = get_pointers s2 in
      let m1, m2 = Int64.(equal (get_cpointer parent [ckey]) hl, 
      equal (get_cpointer parent next) hr) in
      if m1 && m2 then
        let mp = get_pl_from_key parent ckey in
        let k1s, p1s, cn1, _, _ = get_all s1 in
        let k2s, p2s, cn2, _, _ = get_all s2 in
        let _ = check_length (List.length k1s + List.length k2s + 1) b in
        let mks, mpls, mcn = k1s @ (ckey::k2s), p1s @ (mp::p2s), cn1 @ cn2 in
        let hpointer, cblockpointer = get_pointers parent in
        let reduce = root && one_key && not ignore in
        let crt = if s1_leaf then Int64.max_int else cblockpointer in
        let hs, csp = if reduce then hpointer, crt else hl, cl in
        let s = if s1_leaf then Lf (mks, mpls, reduce, b, hs)
        else Il (mks, mpls, mcn, reduce, b, (hs, csp)) in
        if reduce then begin
          write_node t s >>= function
          | Error _ as e -> Lwt.return e
          | Ok () -> 
            if is_leaf s then Lwt.return @@ Ok (s, s, [hl; hr; cblockpointer])
            else Lwt.return @@ Ok (s, s, [hl; cl; hr; cr])
        end else begin
          let tr = remove_key parent ckey in
          if ignore then Lwt.return @@ Ok (tr, s, []) else begin
            write_node t s >>= function
            | Error _ as e -> Lwt.return e
            | Ok () ->
              remove_cpointer_from_child_block t cblockpointer hr (n_keys parent) >>= function
              | Error _ as e -> Lwt.return e
              | Ok () -> remove_key_and_pl_in_hblock t b hpointer ckey mp >>= function
                | Error _ as e -> Lwt.return e
                | Ok () -> Lwt.return @@ Ok (tr, s, [hr; cr])
            end
        end
      else if next=[] then raise Not_found
      else merge t parent (List.hd next) s1 s2 ignore

  let replace t tree k (newk, newpl) =
    let _, _, _, _, b = get_all tree in
    let hpointer, _ = get_pointers tree in
    replace_key_and_pl_in_hblock t b hpointer k newk newpl >>= function
    | Error _ as e -> Lwt.return e
    | Ok () -> Lwt.return @@ Ok (tree, (newk, newpl))

  let rec swap_predecessor t tree k p ckey found =
    let swap_child kl f = 
      get_child t tree kl >>= function
      | Error _ as e -> Lwt.return e 
      | Ok c -> swap_predecessor t c k p (get_hd c) f >>= function
        | Error _ as e -> Lwt.return e
        | Ok (_, pred) -> Lwt.return @@ Ok (tree, pred) in
    let leaf, next = is_leaf tree, get_next tree ckey in
    if found then
      if next=[] then
        if leaf then replace t tree ckey (k, p)
        else swap_child next found
      else swap_predecessor t tree k p (List.hd next) found
    else if leaf then raise Not_found
    else if ckey=k then swap_child [ckey] true >>= function
      | Error _ as e -> Lwt.return e
      | Ok (_, pred) -> replace t tree k pred >>= function
        | Error _ as e -> Lwt.return e
        | Ok (tr, _) -> Lwt.return @@ Ok (tr, pred)
    else if k<ckey then swap_child [ckey] false
    else if next=[] then swap_child next false
    else swap_predecessor t tree k p (List.hd next) false

  let rec swap_successor t tree k p ckey found =
    let swap_child kl f = 
      get_child t tree kl >>= function
      | Error _ as e -> Lwt.return e 
      | Ok c -> swap_successor t c k p (get_hd c) f >>= function
        | Error _ as e -> Lwt.return e
        | Ok (_, scr) -> Lwt.return @@ Ok (tree, scr) in
    let leaf, next = is_leaf tree, get_next tree ckey in
    if found then
      if leaf then replace t tree (get_hd tree) (k, p)
      else swap_child [ckey] found
    else if leaf then raise Not_found
    else if ckey=k then swap_child next true >>= function
      | Error _ as e -> Lwt.return e
      | Ok (_, scr) -> replace t tree k scr >>= function
        | Error _ as e -> Lwt.return e
        | Ok (tr, _) -> Lwt.return @@ Ok (tr, scr)
    else if k<ckey then swap_child [ckey] false
    else if next=[] then swap_child next false
    else swap_successor t tree k p (List.hd next) false

  (* redistributes a key from morec to its immediate sibling node *)
  let steal t tree ckey morec =
    let rec store_ops l r = match l with
    | f::fs -> f >>= (function
      | Error _ as e -> Lwt.return e
      | Ok () -> store_ops fs r)
    | [] -> Lwt.return @@ Ok r in
    let _, _, _, _, b = get_all tree in
    let next = get_next tree ckey in
    let cb_p = get_cpointer tree next in 
    get_child t tree [ckey] >>= function
    | Error _ as e -> Lwt.return e
    | Ok ca -> get_child t tree next >>= function
      | Error _ as e -> Lwt.return e
      | Ok cb ->
        merge t tree ckey ca cb true >>= function
        | Error _ as e -> Lwt.return e
        | Ok (mt, merged_child, _) ->
          let lim = (if ca=morec then (n_keys ca)-1 else if cb=morec then b else -1) in
          if lim = -1 then raise Not_found
          else split t merged_child mt lim cb_p >>= fun r -> 
            let tr = match r with | Ok tr -> tr | _ -> null_tree in
            let ks, pls, _, _, _ = get_all merged_child in 
            let mk, mp = List.nth ks lim, List.nth pls lim in
            let lessc = if ca=morec then cb else ca in
            let hpointer, _ = get_pointers tree in 
            let lpointer, lcpointer = get_pointers lessc in
            let mpointer, mcpointer = get_pointers morec in
            let ops =
            [replace_key_and_pl_in_hblock t b hpointer ckey mk mp;
            remove_key_and_pl_in_hblock t b mpointer mk mp;
            add_key_and_pl_to_hblock t b lpointer ckey (get_pl_from_key tree ckey)] in
            if is_leaf morec then store_ops ops tr else begin
              let movedc_key = if morec=cb then [get_hd morec] else [] in
              let movedc_cpointer = get_cpointer morec movedc_key in
              let more_ops = 
              [remove_cpointer_from_child_block t mcpointer movedc_cpointer (n_keys morec);
              add_cpointer_to_child_block t lcpointer movedc_cpointer (n_keys lessc)] in
              store_ops (ops @ more_ops) tr
            end

  let rec deletev t tree k ckey pointers swapped =
    let get_child_nodes ckey next = get_child t tree [ckey] >>= function
    | Error _ as e -> Lwt.return e
    | Ok ca -> get_child t tree next >>= function
      | Error _ as e -> Lwt.return e
      | Ok cb -> Lwt.return @@ Ok (ca, cb) in
    if ckey<Int32.zero then Lwt.return @@ Ok (tree, pointers)
    else 
      let _, _, _, _, b = get_all tree in
      let leaf, next = is_leaf tree, get_next tree ckey in
      let left, right, found = k<ckey, k>ckey && next=[], k=ckey in
      (* swapping causes an inversion *)
      let leftc, rightc = if swapped then not left, left else left, right in
      if not (found || leftc || rightc) then deletev t tree k (List.hd next) pointers false
      else get_child_nodes ckey next >>= function
      | Error _ as e -> Lwt.return e
      | Ok (ca, cb) ->
        let l1, l2 = n_keys ca, n_keys cb in
        let lempty, rempty = l1<b, l2<b in
        if found then
          let p = get_pl_from_key tree k in
          if leaf then begin
            let hpointer, _ = get_pointers tree in
            remove_key_and_pl_in_hblock t b hpointer k p >>= function
            | Error _ as e -> Lwt.return e
            | Ok () -> Lwt.return @@ Ok (remove_key tree k, pointers)
          end else if not (lempty && rempty) then
            let func = if lempty then swap_successor else swap_predecessor in
            func t tree k p ckey false >>= function
            | Error _ as e -> Lwt.return e
            | Ok (tr, (new_ckey, _)) -> deletev t tr k new_ckey pointers true
            (* merge around key to delete if neither child node has enough keys *)
          else merge t tree ckey ca cb false >>= function
          | Error _ as e -> Lwt.return e
          | Ok (tr, _, freed) -> deletev t tr k (get_hd tr) (pointers @ freed) false
        else if not leaf then
          let c = if lempty || (rightc && not rempty) then cb else ca in
          let ok = (leftc && not lempty) || (rightc && not rempty) in
          if ok then (* k is in subtree which can lose a key *)
            deletev t c k (get_hd c) pointers false >>= function
            | Error _ as e -> Lwt.return e
            | Ok (_, freed) -> Lwt.return @@ Ok (tree, freed)
          else if lempty && rempty then (* merge needed *)
            merge t tree ckey ca cb false >>= function
            | Error _ as e -> Lwt.return e
            | Ok (tr, _, freed) -> deletev t tr k (get_hd tr) (pointers @ freed) false
            (* steal a key a sibling of the subtree containing k *)
          else steal t tree ckey c >>= function
          | Error _ as e -> Lwt.return e
          | Ok tr -> deletev t tr k (get_hd tr) pointers false
        else if left || right then raise Not_found
        else deletev t tree k (List.hd next) pointers false (* continue searching this leaf *)

  let delete t tree k = 
    let _, _, _, root, _ = get_all tree in
    if not root then 
      raise (InvalidOperation "delete can only be called on a root node")
    else deletev t tree k (try get_hd tree with Failure _ -> Int32.minus_one) [] false

  let rec delete_list t tree keys pointers = match keys with
  | k::ks -> delete t tree k >>= (function
   | Error _ as e -> Lwt.return e
   | Ok (tr, pointers) -> delete_list t tr ks pointers)
  | [] -> Lwt.return @@ Ok (tree, (List.filter (fun f -> not Int64.(equal f max_int)) pointers)) 
  end
