type keys = int64 list
type node = 
| Lf of keys * bool * int * int64
| Il of keys * int64 list * bool * int * (int64 * int64)

exception MalformedTree of string
exception NotFound of string
exception InvalidOperation of string

let null_pointer = Int64.max_int
let null_tree = Lf ([], false, 0, null_pointer)
let root_pointer = 2L

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
  
    let get_all tree = match tree with
    | Il (ks, cn, r, b, _) -> ks, cn, r, b
    | Lf (ks, r, b, _) -> ks, [], r, b

    let get_pointers tree = match tree with
    | Il (_, _, _, _, (hptr, cbptr)) -> hptr, cbptr
    | Lf (_, _, _, ptr) -> ptr, null_pointer
  
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
      let ks, cn, r, b = get_all tree in
      let string_of_int64_list l = 
        "{" ^ (List.fold_left (fun acc x -> 
          acc ^ Int64.to_string x ^ ",") "" l) ^ "}" in
      "(" ^ (string_of_int64_list ks) ^ ", " ^ (string_of_int64_list cn) ^ 
      (string_of_bool r) ^ ", " ^ (string_of_int b) ^ ")"
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
    
    let write_cpointer_block t pointer cpointers =
      let cs = Cstruct.create t.block_size in
      for n=0 to (List.length cpointers - 1) do
        Cstruct.LE.set_uint64 cs (n*sizeof_pointer) (List.nth cpointers n);
      done;
      write_block t pointer cs

    let parse_cpointer_block cs n = read_pointers cs n 0
    
    let write_head_block t tree =
      let nk = Attrs.n_keys tree in
      let hpointer, cblockpointer = get_pointers tree in
      let cs = Cstruct.create t.block_size in
      let ks, _, _, _ = Attrs.get_all tree in
      (* value identifying the root node *)
      let v = Int64.(if equal hpointer root_pointer then one else zero) in
      Cstruct.LE.set_uint64 cs 0 v; 
      (* pointer to block containing child node pointers *)
      Cstruct.LE.set_uint64 cs sizeof_pointer cblockpointer;
      (* number of keys in this node *)
      Cstruct.LE.set_uint64 cs (2*sizeof_pointer) (Int64.of_int nk);
      for n=0 to nk-1 do
        Cstruct.LE.set_uint64 cs ((n+3)*sizeof_pointer) (List.nth ks n);
      done;
      write_block t hpointer cs

    let write_empty_root t tree =
      let hpointer, cblockpointer = get_pointers tree in
      let cs = Cstruct.create t.block_size in
      Cstruct.LE.set_uint64 cs 0 Int64.one;
      Cstruct.LE.set_uint64 cs sizeof_pointer cblockpointer;
      Cstruct.LE.set_uint64 cs (2*sizeof_pointer) Int64.zero;
      write_block t hpointer cs

    let parse_keys cs =
      let nk = Int64.to_int (Cstruct.LE.get_uint64 cs (2*sizeof_pointer)) in
      let ks = List.sort Int64.compare (read_pointers cs (nk+2) 3) in
      nk, ks

    let read_node t b pointer =
      read_block t pointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let r = (Int64.equal pointer root_pointer) in
        let valid = Cstruct.LE.get_uint64 hblock 0 in
        if r && not Int64.(equal valid one) then Lwt.return @@ Ok (Lf ([], true, b, pointer)) 
        else let cblockpointer = Cstruct.LE.get_uint64 hblock sizeof_pointer in
        let nk, ks = parse_keys hblock in
        if Int64.equal cblockpointer null_pointer then 
          Lwt.return @@ Ok (Lf (ks, r, b, pointer))
        else read_block t cblockpointer >>= function
        | Error _ as e -> Lwt.return e
        | Ok cblock ->
          let cpointers = parse_cpointer_block cblock nk in
          Lwt.return @@ Ok (Il (ks, cpointers, r, b, (pointer, cblockpointer)))

    let rec used_blocks t pointer =
      read_block t pointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let nk = Int64.to_int (Cstruct.LE.get_uint64 hblock (2*sizeof_pointer)) in
        let cblockpointer = Cstruct.LE.get_uint64 hblock sizeof_pointer in
        if Int64.(equal cblockpointer max_int) then Lwt.return @@ Ok []
        else read_block t cblockpointer >>= function
        | Error _ as e -> Lwt.return e
        | Ok cblock ->
          let cpointers = parse_cpointer_block cblock nk in
          Lwt_list.fold_left_s (fun l p -> match l with
          | Error _ as e -> Lwt.return e
          | Ok blocks -> used_blocks t p >>= function
            | Error _ as e -> Lwt.return e
            | Ok new_blocks -> Lwt.return @@ Ok (new_blocks @ blocks)) (Ok cpointers) cpointers >>= function
          | Error _ as e -> Lwt.return e
          | Ok blocks -> Lwt.return @@ Ok blocks


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

  module Tree_ops = struct
    (* adds key k, payload p and child c to each associated list *)
    let restore tree k c = match tree with
    | Lf ([], r, b, ptr) -> Lf (k::[], r, b, ptr)
    | Lf (v::next, r, b, ptr) -> Lf (k::v::next, r, b, ptr)
    | Il ([], cn, r, b, ptrs) -> Il (k::[], c::cn, r, b, ptrs)
    | Il (v::next, cn, r, b, ptrs) -> Il (k::v::next, c::cn, r, b, ptrs)
  
    (* returns [next key] or [] if k is the rightmost key in the node *)
    let rec get_next tree k = match tree with
    | Il (v::next, _::cn, r, b, ptrs) ->
      if v=k then try [List.hd next] with Failure _ -> []
      else get_next (Il (next, cn, r, b, ptrs)) k
    | Il ([], _, _, _, _) -> []
    | Lf (v::next, r, b, ptr) ->
      if v=k then try [List.hd next] with Failure _ -> []
      else get_next (Lf (next, r, b, ptr)) k
    | _ -> raise (MalformedTree "invalid tree structure")

    let rec get_cpointer tree kl =
      if Attrs.is_leaf tree then null_pointer
      else match kl with
      | [] -> (match tree with
        | Il (_::next, _::cn, r, b, ptrs) -> 
          get_cpointer (Il (next, cn, r, b, ptrs)) kl
        | Il ([], c::[], _, _, _) -> c
        | _ -> raise (MalformedTree "invalid tree structure"))
      | k::_ -> (match tree with
        | Il (v::next, c::cn, r, b, ptrs) ->
          if v=k then c else get_cpointer (Il (next, cn, r, b, ptrs)) kl
        | Il ([], _::[], _, _, _) -> raise (NotFound "child node not found")
        | _ -> raise (MalformedTree "invalid tree structure"))
  
    (* reads in either the left child of key in kl/rightmost child if kl=[] *)
    let get_child t tree kl =
      let _, _, _, b = get_all tree in
      let cpointer = get_cpointer tree kl in
      read_node t b cpointer
  
    let rec insert_key tree k = match tree with
    | Lf (v::next, r, b, ptr) ->
      if k<v then Lf (k::v::next, r, b, ptr)
      else if k=v then Lf (k::next, r, b, ptr)
      else restore (insert_key (Lf (next, r, b, ptr)) k) v null_pointer
    | Lf ([], r, b, ptr) -> Lf (k::[], r, b, ptr)
    | _ -> raise (InvalidOperation "cannot insert key in internal node")
    
    let rec update_node tree k cptr = match tree with
    | Il (v::next, c::cn, r, b, ptrs) -> 
      if k<v then
        Il (k::v::next, cptr::c::cn, r, b, ptrs)
      else restore (update_node (Il (next, cn, r, b, ptrs)) k cptr) v c
    | Il ([], c::cn, r, b, ptrs) -> Il (k::[], cptr::c::cn, r, b, ptrs)
    | _ -> raise (MalformedTree "invalid tree structure")
    
    let rec remove_key tree k = match tree with
    | Lf (v::next, r, b, ptr) ->
      if v=k then Lf (next, r, b, ptr)
      else restore (remove_key (Lf (next, r, b, ptr)) k) v null_pointer
    | _ -> raise (InvalidOperation "cannot remove key from internal node")
    end

  open Tree_ops

  module Block_ops = struct
    let add_key_to_head_block t hpointer k =
      read_block t hpointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok hblock ->
        let nk = Int64.to_int (Cstruct.LE.get_uint64 hblock (2*sizeof_pointer)) in
        Cstruct.LE.set_uint64 hblock (2*sizeof_pointer) (Int64.of_int (nk+1));
        try
        Cstruct.LE.set_uint64 hblock ((nk+3)*sizeof_pointer) k;
        write_block t hpointer hblock
        with Invalid_argument _ -> 
          Format.eprintf "tried to add key %Ld to head block at pointer %Ld, offset %d" k hpointer ((nk+3)*sizeof_pointer);
          Lwt.return @@ Error `Write_error

    let replace_key_in_head_block t hpointer k newk =
      read_block t hpointer >>= function
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
      let _, cpointers, _, _ = get_all tree in
      let _, cblockpointer = get_pointers tree in
      write_head_block t tree >>= function
      | Error _ as e -> Lwt.return e
      | Ok () ->
        if is_leaf tree then Lwt.return @@ Ok ()
        else write_cpointer_block t cblockpointer cpointers >>= function
        | Error _ as e -> Lwt.return e
        | Ok () -> Lwt.return @@ Ok ()
    
    let write_node_split_update t nk k hpointer cblockpointer cpointer =
      add_cpointer_to_child_block t cblockpointer cpointer nk >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> add_key_to_head_block t hpointer k
    end

  open Node_writes

  (* splits a node in two on a given key index
  * migrates key to parent node and returns parent, which may now be full
  * if the node is a root, this can increase the depth of the tree by 1 *)
  let split t tree parent m rptr =
    let ignore = not (Int64.equal rptr null_pointer) in
    let split_lists tree =
      let ks, cn, _, _ = get_all tree in
      let mk, lks, rks = split_ks m ks in
      let lcn, rcn = split_cn (m+1) cn in
      List.hd mk, lks, lcn, rks, rcn in
    let _, _, root, b = get_all tree in
    let root_split = 
      if ignore then false else (root && (get_hd parent) = (get_hd tree)) in
    let pleaf, cleaf = is_leaf parent, is_leaf tree in
    if pleaf && not root_split then 
      raise (InvalidOperation "cannot split with leaf node as parent")
    else
      let mk, lks, lcn, rks, rcn = split_lists tree in
      let n_pointers = 
        if ignore then 0 
        (* if the root is being split and is a leaf it needs a cblockpointer *)
        else if root_split then if pleaf then 3 else 4
        else if cleaf then 1 else 2 in
      if ignore then
        Lwt.return @@ Ok (update_node parent mk rptr) else
        Serial.get_block_pointers t n_pointers >>= function
        | Error _ as e -> Lwt.return e
        | Ok pointers -> let hl, cl, hr, cr, crt = match pointers with
          | hl::hr::crt::[] when root_split && pleaf -> hl, null_pointer, hr, null_pointer, crt
          | hl::cl::hr::cr::[] when root_split && not pleaf -> hl, cl, hr, cr, null_pointer
          | hr::more when not root_split ->
            let hl, cl = get_pointers tree in 
            hl, cl, hr, (if cleaf then null_pointer else List.hd more), null_pointer
          | _ -> null_pointer, null_pointer, null_pointer, null_pointer, null_pointer in
          let hp, cbp = get_pointers parent in
          let t_left, t_right = 
            if cleaf then Lf (lks, false, b, hl), Lf (rks, false, b, hr)
            else Il (lks, lcn, false, b, (hl, cl)), Il (rks, rcn, false, b, (hr, cr)) in
          if Int64.equal hl null_pointer then Lwt.return @@ Error `No_space
          else write_node t t_left >>= function
          | Error _ as e -> Lwt.return e
          | Ok () -> write_node t t_right >>= function
            | Error _ as e -> Lwt.return e
            | Ok () ->  
              if root_split then begin
                let new_cbp = min crt cbp in
                let newt = Il (mk::[], hl::hr::[], true, b, (hp, new_cbp)) in
                write_node t newt >>= function
                | Error _ as e -> Lwt.return e
                | Ok () -> Lwt.return @@ Ok newt
              end else begin 
              write_node_split_update t (n_keys parent) mk hr hp cbp >>= function
              | Error _ as e -> Lwt.return e
              | Ok () -> Lwt.return @@ Ok (update_node parent mk hr)
              end

  let rec insertv t tree k p ckey ignore =
    let _, _, root, b = get_all tree in
    let lim = 2*b-1 in
    let empty, full = (ckey < Int64.zero), n_keys tree = lim in
    if (full && root && not ignore) then
      split t tree tree (b-1) null_pointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok tr -> insertv t tr k p (get_hd tr) false
    else if (full && not root && not ignore) then 
      raise (MalformedTree "full node not split ahead of time")
    else if (empty && root) then
      let tr = insert_key tree k in Lwt.return @@ Ok (tr, tr, false)
    else if empty then raise (MalformedTree "empty non-root node")
    else if k=ckey then Lwt.return @@ Ok (tree, tree, true)
    else let next = get_next tree ckey in
      if (k>ckey && next != []) then insertv t tree k p (List.hd next) ignore
      else let pkey = if k<ckey then [ckey] else [] in
      if (is_leaf tree) then 
        let tr = insert_key tree k in Lwt.return @@ Ok (tr, tr, false)
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
  
  let insert t tree k p next =
    let write_and_return tree = 
      write_data_block t k next p >>= function
      | Error _ as e -> Lwt.return e
      | Ok () -> Lwt.return @@ Ok tree in
    if Int64.(equal k max_int) then begin
      Lwt.return @@ Error `Write_error 
    end else let _, _, root, _ = get_all tree in
    if not root then 
      raise (InvalidOperation "insert can only be called on a root node")
    else 
      let ckey = try get_hd tree with Failure _ -> Int64.minus_one in
      insertv t tree k p ckey false >>= function
      | Error _ as e -> Lwt.return e
      | Ok (newt, new_lf, update) ->
        if not update then
          let hpointer, _cpointer = get_pointers new_lf in
          add_key_to_head_block t hpointer k >>= function
          | Error _ as e -> Lwt.return e
          | Ok () -> write_and_return newt
        else write_and_return newt
      
 (* takes two child nodes and merges them into one node 
  * the parent node loses a key in the process
  * if the node is a root, this can decrease the depth by 1
  * returns the parent node, the merged child and any unused pointers *)
  let rec merge t parent ckey s1 s2 ignore =
    let check_length l b = 
      if ((l < b-1 || l > 2*b-1) && not ignore) then 
        raise (InvalidOperation "merge will result in an invalid node") 
      else () in
    let _, _, root, b = get_all parent in
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
        let k1s, cn1, _, _ = get_all s1 in
        let k2s, cn2, _, _ = get_all s2 in
        let _ = check_length (List.length k1s + List.length k2s + 1) b in
        let merged_ks, merged_cn = k1s @ (ckey::k2s), cn1 @ cn2 in
        let hpointer, cblockpointer = get_pointers parent in
        let reduce = root && one_key && not ignore in
        let crt = if s1_leaf then Int64.max_int else cblockpointer in
        let hs, csp = if reduce then hpointer, crt else hl, cl in
        let s = if s1_leaf then Lf (merged_ks, reduce, b, hs)
        else Il (merged_ks, merged_cn, reduce, b, (hs, csp)) in
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
              | Ok () -> replace_key_in_head_block t hpointer ckey (Int64.of_int 593) >>= function
                | Error _ as e -> Lwt.return e
                | Ok () -> Lwt.return @@ Ok (tr, s, [hr; cr])
            end
        end
      else if next=[] then raise (NotFound "could not find sibling nodes")
      else merge t parent (List.hd next) s1 s2 ignore

  let replace t tree k1 k2 =
    let hpointer, _ = get_pointers tree in
    replace_key_in_head_block t hpointer k1 k2 >>= function
    | Error _ as e -> Lwt.return e
    | Ok () -> Lwt.return @@ Ok (tree, k1)

  let rec swap_predecessor t tree k ckey found =
    let swap_child kl f = 
      get_child t tree kl >>= function
      | Error _ as e -> Lwt.return e 
      | Ok c -> swap_predecessor t c k (get_hd c) f >>= function
        | Error _ as e -> Lwt.return e
        | Ok (_, pred) -> Lwt.return @@ Ok (tree, pred) in
    let leaf, next = is_leaf tree, get_next tree ckey in
    if found then
      if next=[] then
        if leaf then replace t tree ckey k
        else swap_child next found
      else swap_predecessor t tree k (List.hd next) found
    else if leaf then raise (NotFound "key not found")
    else if ckey=k then swap_child [ckey] true >>= function
      | Error _ as e -> Lwt.return e
      | Ok (_, pred) -> replace t tree k pred >>= function
        | Error _ as e -> Lwt.return e
        | Ok (tr, _) -> Lwt.return @@ Ok (tr, pred)
    else if k<ckey then swap_child [ckey] false
    else if next=[] then swap_child next false
    else swap_predecessor t tree k (List.hd next) false

  let rec swap_successor t tree k ckey found =
    let swap_child kl f = 
      get_child t tree kl >>= function
      | Error _ as e -> Lwt.return e 
      | Ok c -> swap_successor t c k (get_hd c) f >>= function
        | Error _ as e -> Lwt.return e
        | Ok (_, scr) -> Lwt.return @@ Ok (tree, scr) in
    let leaf, next = is_leaf tree, get_next tree ckey in
    if found then
      if leaf then replace t tree (get_hd tree) k
      else swap_child [ckey] found
    else if leaf then raise (NotFound "key not found")
    else if ckey=k then swap_child next true >>= function
      | Error _ as e -> Lwt.return e
      | Ok (_, scr) -> replace t tree k scr >>= function
        | Error _ as e -> Lwt.return e
        | Ok (tr, _) -> Lwt.return @@ Ok (tr, scr)
    else if k<ckey then swap_child [ckey] false
    else if next=[] then swap_child next false
    else swap_successor t tree k (List.hd next) false

  (* redistributes a key from morec to its immediate sibling node *)
  let steal t tree ckey morec =
    let rec store_ops l r = match l with
    | f::fs -> f >>= (function
      | Error _ as e -> Lwt.return e
      | Ok () -> store_ops fs r)
    | [] -> Lwt.return @@ Ok r in
    let _, _, _, b = get_all tree in
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
          if lim = -1 then raise (NotFound "child node not found")
          else split t merged_child mt lim cb_p >>= fun r -> 
            let tr = match r with | Ok tr -> tr | _ -> null_tree in
            let new_sp = let ks, _, _, _ = get_all merged_child in List.nth ks lim in
            let lessc = if ca=morec then cb else ca in
            let hpointer, _ = get_pointers tree in 
            let lpointer, lcpointer = get_pointers lessc in
            let mpointer, mcpointer = get_pointers morec in
            let ops =
            [replace_key_in_head_block t hpointer ckey new_sp;
            replace_key_in_head_block t mpointer new_sp (Int64.of_int 723);
            add_key_to_head_block t lpointer ckey] in
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
    if ckey<Int64.zero then Lwt.return @@ Ok (tree, pointers)
    else 
      let _, _, _, b = get_all tree in
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
          if leaf then begin
            let hpointer, _ = get_pointers tree in
            replace_key_in_head_block t hpointer k (Int64.of_int 750) >>= function
            | Error _ as e -> Lwt.return e
            | Ok () -> Lwt.return @@ Ok (remove_key tree k, pointers)
          end else if not (lempty && rempty) then
            let func = if lempty then swap_successor else swap_predecessor in
            func t tree k ckey false >>= function
            | Error _ as e -> Lwt.return e
            | Ok (tr, key_to_swap) -> deletev t tr k key_to_swap pointers true
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
        else if left || right then raise (NotFound "key to delete not found")
        else deletev t tree k (List.hd next) pointers false (* continue searching this leaf *)

  let delete t tree k = 
    let _, _, root, _ = get_all tree in
    if not root then 
      raise (InvalidOperation "delete can only be called on a root node")
    else deletev t tree k (try get_hd tree with Failure _ -> Int64.minus_one) [] false

  let rec delete_list t tree keys pointers = match keys with
  | k::ks -> delete t tree k >>= (function
   | Error _ as e -> Lwt.return e
   | Ok (tr, pointers) -> delete_list t tr ks pointers)
  | [] -> Lwt.return @@ Ok (tree, (List.filter (fun f -> not Int64.(equal f max_int)) pointers)) 
  end
