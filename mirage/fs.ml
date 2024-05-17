type blockpair = int64 * int64
type directory_head = blockpair

let root_pair = (0L, 1L)
let btree_root = 2L


let pp_blockpair = Fmt.(pair ~sep:comma int64 int64)

open Lwt.Infix

module Make(Sectors: Mirage_block.S)(Clock : Mirage_clock.PCLOCK) = struct
  module Fs_Btree = Btree.Make(Sectors)
  module Block_types = Block_type.Make(Sectors)

  open Block_types

  type write_result = [ `No_space | `Split | `Split_emergency ]

  type key = Mirage_kv.Key.t

  let log_src = Logs.Src.create "chamelon-fs" ~doc:"chamelon FS layer"
  module Log = (val Logs.src_log log_src : Logs.LOG)

  (* error type definitions straight outta mirage-kv *)
  type error = [
    | `Not_found           of key (** key not found *)
    | `Dictionary_expected of key (** key does not refer to a dictionary. *)
    | `Value_expected      of key (** key does not refer to a value. *)
  ]
  type write_error = [
    | error
    | `No_space                (** No space left on the device. *)
    | `Too_many_retries of int (** {!batch} has been trying to commit [n] times
                                   without success. *)
  ]
  
  let root_node = ref Btree.null_tree
  
  module Read = struct

    (* get the wodge of data at this block number, and attempt to parse it *)
    let block_of_block_number {block_size; block; program_block_size; _} block_location =
      let cs = Cstruct.create block_size in
      This_Block.read block block_location [cs] >>= function
      | Error b -> Lwt.return @@ Error (`Block b)
      | Ok () ->
        match Chamelon.Block.of_cstruct ~program_block_size cs with
        | Error (`Msg s) ->
          Log.err (fun f -> f "error reading block %Ld : %s"
                      block_location s);
          Lwt.return @@ Error (`Chamelon `Corrupt)
        | Ok extant_block -> Lwt.return @@ Ok extant_block

    (* get the blocks at pair (first, second), parse them, and return whichever is more recent *)
    let block_of_block_pair t (l1, l2) =
      let open Lwt_result.Infix in
      Lwt_result.both (block_of_block_number t l1) (block_of_block_number t l2) >>= fun (b1, b2) ->
      if Chamelon.Block.(compare (revision_count b1) (revision_count b2)) < 0
      then Lwt.return @@ Ok b2
      else Lwt.return @@ Ok b1
          
  end

  module Traverse = struct
    open Lookahead

    let build_btree t b =
      let set tree = root_node := tree; Lwt.return @@ Ok () in
      Fs_Btree.Serial.read_node t b btree_root >>= function
      | Error _ as e -> Lwt.return e
      | Ok (tree, valid) -> 
        if valid then set tree
        else Fs_Btree.Serial.write_empty_root t tree >>= function
        | Error _ as e -> Lwt.return e
        | Ok () -> set tree

    let rec get_indirect_block_pointers t a_res pointer =
      match a_res with
      | Error _ as e -> Lwt.return e
      | Ok arr ->
        let open Lwt_result.Infix in
        Log.err (fun f -> f "indirect block pointer found: %Ld" pointer);
        let data = Cstruct.create t.block_size in
        This_Block.read t.block pointer [data] >>= fun () ->
        let next = Cstruct.LE.get_uint64 data (t.block_size - 8) in
        if not Int64.(equal next zero) then Log.err (fun f -> f "next=%Ld" next);
        if Int64.(equal next max_int) then Lwt.return @@ Ok arr
        else begin
          set_index arr next 1;
          get_indirect_block_pointers t (Ok arr) next
        end

    let rec follow_links t arr = function
      | Chamelon.Entry.Data (pointer, _length) -> begin
          Log.debug (fun f -> f "reading indirect block pointers for file starting at %Ld" pointer);
          set_index arr pointer 1;
          get_indirect_block_pointers t (Ok arr) pointer
        end
      | Chamelon.Entry.Metadata (a, b) ->
        match (in_use arr a || in_use arr b) with
        | true -> Log.err (fun f -> f "cycle detected: blockpair %a encountered again after initial visit." pp_blockpair (a, b));
          Lwt.return @@ Error `Disconnected
        | false ->
          Read.block_of_block_pair t (a, b) >>= function
          | Error (`Block e) ->
            Log.err (fun m -> m "error reading block pair %Ld, %Ld (0x%Lx, 0x%Lx): %a"
                        a b a b This_Block.pp_error e);
            Lwt.return @@ Error e
          | Error (`Chamelon `Corrupt) ->
            Log.err (fun f -> f "filesystem seems corrupted; we couldn't make sense of a block pair");
            Lwt.return @@ Error `Disconnected
          | Ok block ->
            Log.debug (fun f -> f "finding blocks linked from %a" pp_blockpair (a, b));
            let links = Chamelon.Block.linked_blocks block in
            let string_of_link_list l = List.fold_left (fun acc lk -> match lk with
            | Chamelon.Entry.Metadata (a, b) -> acc ^ "metadata: (" ^ (Int64.to_string a) ^ ", " ^ (Int64.to_string b) ^ "), "
            | Chamelon.Entry.Data (a, b) -> acc ^ "data: (" ^ (Int64.to_string a) ^ ", " ^ (Int64.to_string b) ^ "), ") "" l in
            Log.debug (fun f -> f "found %d linked blocks: %s" (List.length links) (string_of_link_list links));
            Lwt_list.fold_left_s (fun so_far link ->
                match so_far with
                | Error _ as e -> Lwt.return e
                | Ok arr ->
                  follow_links t arr link >>= function
                  | Error e ->
                    Log.err (fun f -> f "filesystem seems corrupted; we couldn't get a list of unused blocks: %a" This_Block.pp_error e);
                    Lwt.return @@ Error `Disconnected
                  | Ok new_arr -> Lwt.return @@ Ok new_arr
              ) (Ok arr) links
            >>= function
            | Ok new_arr -> set_index new_arr a 1; set_index new_arr b 1;
              Lwt.return @@ Ok new_arr
            | e -> Lwt.return e
        
    let follow_links_tree t b =
      Log.err (fun f -> f "scanning filesystem");
      let arr = Cstruct.create (This_Block.block_count t.block) in
      follow_links t arr (Chamelon.Entry.Metadata root_pair) >>= function
      | Error _ as e -> Lwt.return e
      | Ok new_arr -> 
        Log.err (fun f -> f "calling get_all_pointers");
        Fs_Btree.Serial.get_all_pointers t b btree_root new_arr >>= function
        | Error _ -> Lwt.return @@ Error `Disconnected
        | Ok final_arr -> Lwt.return @@ Ok final_arr

    (* [last_block t pair] returns the last blockpair in the hardtail
     * linked list starting at [pair], which may well be [pair] itself *)
    let rec last_block t pair =
      let open Lwt_result.Infix in
      Read.block_of_block_pair t pair >>= fun block ->
      match List.find_opt (fun e ->
          Chamelon.Tag.is_hardtail (fst e)
        ) (Chamelon.Block.entries block) with
      | None -> Lwt.return @@ Ok pair
      | Some entry -> match Chamelon.Dir.hard_tail_links entry with
        | None -> Lwt.return @@ Ok pair
        | Some next_pair -> last_block t next_pair
  end

  module Write = struct
    (* from the littlefs spec, we should be checking whether
     * the on-disk data matches what we have in memory after
     * doing this write. Then if it doesn't, we should rewrite
     * to a different block, and note the block as bad so we don't
     * try to write to it in the future.
     *
     * I don't think that's necessary in our execution context.
     * we're not writing directly to a flash controller,
     * we're probably writing to a file on another filesystem
     * managed by an OS with its own bad block detection.
     * That's my excuse for punting on it for now, anyway. *)
    let block_to_block_number t data block_location : (unit, write_result) result Lwt.t =
      let block_device = t.block in
      This_Block.write block_device block_location [data] >>= function
      | Ok () -> Lwt.return @@ Ok ()
      | Error e ->
        Log.err (fun m -> m "block write error: %a" This_Block.pp_write_error e);
        Lwt.return @@ Error `No_space

    let rec block_to_block_pair t data (b1, b2) : (unit, write_result) result Lwt.t =
      let split data  =
        Allocate.get_block_pair t >>= function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok (new_block_1, new_block_2) when Int64.equal new_block_1 new_block_2 ->
          (* if there is only 1 block remaining, we'll get the same one twice.
           * That's not enough for the split. *)
          Lwt.return @@ Error `No_space
        | Ok (new_block_1, new_block_2) -> begin
            Log.debug (fun m -> m "splitting block pair %Ld, %Ld to %Ld, %Ld"
                           b1 b2 new_block_1 new_block_2);
            let old_block, new_block = Chamelon.Block.split data (new_block_1, new_block_2) in
            Log.debug (fun m -> m "keeping %d entries in the old block, and putting %d in the new one"
                           (List.length @@ Chamelon.Block.entries old_block)
                           (List.length @@ Chamelon.Block.entries new_block));
            (* be very explicit about writing the new block first, and only overwriting
             * the old block pair if the new block pair write succeeded *)
            block_to_block_pair t new_block (new_block_1, new_block_2) >>= function
            | Error `Split | Error `Split_emergency | Error `No_space ->
              Lwt.return @@ Error `No_space
            | Ok () -> begin
                Log.debug (fun f -> f "wrote new pair; overwriting old pair");
                (* ignore any warnings about needing to split, etc *)
                let cs1 = Cstruct.create t.block_size in
                let serialize = Chamelon.Block.into_cstruct ~program_block_size:t.program_block_size in
                let _ = serialize cs1 old_block in
                Lwt_result.both
                  (block_to_block_number t cs1 b1)
                  (block_to_block_number t cs1 b2) >>= function
                | Ok _ -> Lwt.return @@ Ok ()
                | Error _ as e -> Lwt.return e
              end
          end
      in
      let cs1 = Cstruct.create t.block_size in
      let serialize = Chamelon.Block.into_cstruct ~program_block_size:t.program_block_size in
      match serialize cs1 data with
      | `Ok -> begin
        Lwt_result.both
          (block_to_block_number t cs1 b1)
          (block_to_block_number t cs1 b2)
        >>= function
        | Ok _ -> Lwt.return @@ Ok ()
        | Error _ as e -> Lwt.return e
      end
      | `Split | `Split_emergency | `Unwriteable ->
        (* try a compaction first *)
        Cstruct.memset cs1 0x00;
        let compacted = Chamelon.Block.compact data in
        Log.debug (fun m -> m "split requested for a block with %d entries. compacted, we had %d"
                       (List.length @@ Chamelon.Block.entries data)
                       (List.length @@ Chamelon.Block.entries compacted)
                   );
        match serialize cs1 compacted, Chamelon.Block.hardtail compacted with
        | `Ok, _ -> begin
            Log.debug (fun f -> f "compaction was sufficient. Will not split %a" pp_blockpair (b1, b2));
            Lwt_result.both
              (block_to_block_number t cs1 b1)
              (block_to_block_number t cs1 b2)
            >>= function
            | Ok _ -> Lwt.return @@ Ok ()
            | Error _ as e -> Lwt.return e
          end
        | `Split, None | `Split_emergency, None -> begin
            Log.debug (fun f -> f "compaction was insufficient and the block has no hardtail. Splitting %a" pp_blockpair (b1, b2));
            split compacted
          end
        | `Split, _ -> begin
            Log.debug (fun f -> f "split needed, but the block's already split. Writing the compacted block");
            Lwt_result.both
              (block_to_block_number t cs1 b1)
              (block_to_block_number t cs1 b2)
            >>= function
            | Ok _ -> Lwt.return @@ Ok ()
            | Error _ as e -> Lwt.return e
          end
        | `Split_emergency, _  | `Unwriteable, _ ->
          Log.err (fun f -> f "Couldn't write to block %a" pp_blockpair (b1, b2));
          Lwt.return @@ Error `No_space
  end

  module Find : sig
    type blockwise_entry_list = blockpair * (Chamelon.Entry.t list)

    (** [all_entries_in_dir t head] gives an *uncompacted* list of all
     * entries in the directory starting at [head].
     * the returned entries in the directory are split up by block,
     * so the caller can distinguish between re-uses of the same ID number
     * when the directory spans multiple block numbers *)
    val all_entries_in_dir : t -> directory_head ->
      (blockwise_entry_list list, error) result Lwt.t

    (** [entries_of_name t head name] scans [head] (and any subsequent blockpairs in the directory's
     * hardtail list) for `id` entries matching [name]. If an `id` is found for [name],
     * all entries matching `id` from the directory are returned (compacted). *)
    val entries_of_name : t -> directory_head -> string -> (blockwise_entry_list list,
                                                           [`No_id of key
                                                           | `Not_found of key]
                                                          ) result Lwt.t

    (** [find_first_blockpair_of_directory t head l] finds and enters
     *  the segments in [l] recursively until none remain.
     *  It returns `No_id if an entry is not present and `No_structs if an entry
     *  is present, but does not represent a valid directory. *)
    val find_first_blockpair_of_directory : t -> directory_head -> string list ->
      [`Basename_on of directory_head | `No_id of string | `No_structs] Lwt.t

  end = struct
    type blockwise_entry_list = blockpair * (Chamelon.Entry.t list)

    (* nb: all does mean *all* here; the list is returned uncompacted,
     * so the caller may have to compact to avoid reporting on expired state *)
    let rec all_entries_in_dir t block_pair =
      Read.block_of_block_pair t block_pair >>= function
      | Error _ -> Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v "hard_tail"))
      | Ok block ->
        let this_blocks_entries = Chamelon.Block.entries block in
        match Chamelon.Block.hardtail block with
        | None -> Lwt.return @@ Ok [(block_pair, this_blocks_entries)]
        | Some nextpair ->
          all_entries_in_dir t nextpair >>= function
          | Ok entries -> Lwt.return @@ Ok ((block_pair, this_blocks_entries) :: entries)
          | Error _ -> Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v "hard_tail"))

    let entries_of_name t block_pair name =
      let entries_of_id entries id =
        let matches (tag, _) = 0 = compare tag.Chamelon.Tag.id id in
        List.find_all matches entries
      in
      let id_of_key entries key =
        let data_matches c = 0 = String.(compare key @@ Cstruct.to_string c) in
        let tag_matches t = Chamelon.Tag.(fst t.type3 = LFS_TYPE_NAME)
        in
        match List.find_opt (fun (tag, data) ->
            tag_matches tag && data_matches data
          ) entries with
        | Some (tag, _) -> Some tag.Chamelon.Tag.id
        | None -> None
      in
      let open Lwt_result in
      all_entries_in_dir t block_pair >>= fun entries_by_block ->
      let entries_matching_name (block, entries) =
        match id_of_key (Chamelon.Entry.compact entries) name with
        | None ->
          Log.debug (fun m -> m "id for %S not found in %d entries from %a"
                         name (List.length entries) pp_blockpair block);
          Error (`No_id (Mirage_kv.Key.v name))
        | Some id ->
          Log.debug (fun m -> m "name %S is associated with id %d on blockpair %a"
                         name id pp_blockpair block);
          let entries = entries_of_id entries id in
          Log.debug (fun m -> m "found %d entries for id %d in %a"
                         (List.length entries) id pp_blockpair block);
          let compacted = Chamelon.Entry.compact entries in
          Log.debug (fun m -> m "after compaction, there were %d entries for id %d in %a"
                         (List.length compacted) id pp_blockpair block);
          Ok (block, compacted)
      in
      let blockwise_matches = List.filter_map (fun es ->
          match entries_matching_name es with
          | Ok (_, []) | Error _ -> None
          | Ok (block, l) -> Some (block, l)
        ) entries_by_block in
      Lwt.return (Ok blockwise_matches)

    let rec find_first_blockpair_of_directory t block_pair key =
      match key with
      | [] -> Lwt.return @@ `Basename_on block_pair
      | key::remaining ->
        entries_of_name t block_pair key >>= function
        | Error _ -> Lwt.return @@ `No_id key
        | Ok [] -> Lwt.return @@ `No_id key
        | Ok l ->
          (* just look at the last entry with this name, and get the entries *)
          let l = snd @@ List.(hd @@ rev l) in
          match List.filter_map Chamelon.Dir.of_entry l with
          | [] -> Lwt.return `No_structs
          | next_blocks::_ ->
            find_first_blockpair_of_directory t next_blocks remaining

  end

  let last_modified_value t key =
    (* find (parent key) on the filesystem *)
    Find.find_first_blockpair_of_directory t root_pair Mirage_kv.Key.(segments @@ parent key) >>= function
    | `No_structs -> Lwt.return @@ Error (`Not_found key)
    | `No_id k -> Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v k))
    | `Basename_on block_pair ->
      (* get all the entries in (parent key) *)
      Find.entries_of_name t block_pair @@ Mirage_kv.Key.basename key >>= function
      | Error (`No_id k) | Error (`Not_found k) -> Lwt.return @@ Error (`Not_found k)
      | Ok l ->
	(* [l] contains all entries associated with (basename key),
	 * some of which are hopefully last-updated metadata entries. *)
	(* We don't care which block any of the entries were on *)
	let l = List.(map snd l |> flatten) in
	(* find the mtime-looking entries *)
	match List.find_opt (fun (tag, _data) ->
	    Chamelon.Tag.(fst @@ tag.type3) = LFS_TYPE_USERATTR &&
	    Chamelon.Tag.(snd @@ tag.type3) = 0x74
	  ) l with
	| None ->
	  Log.warn (fun m -> m "Key %a found but it had no time attributes associated" Mirage_kv.Key.pp key);
	  Lwt.return @@ Error (`Not_found key)
	| Some (_tag, data) ->
	  match Chamelon.Entry.ctime_of_cstruct data with
	  | None ->
	    Log.err (fun m -> m "Time attributes (%a) found for %a but they were not parseable" Cstruct.hexdump_pp data Mirage_kv.Key.pp key);

	    Lwt.return @@ Error (`Not_found key)
	  | Some k -> Lwt.return @@ Ok k


  let rec mkdir t parent_blockpair key =
    (* mkdir has its own function for traversing the directory structure
     * because we want to make anything that's missing along the way,
     * rather than having to get an error, mkdir, get another error, mkdir... *)
    let follow_directory_pointers t block_pair = function
      | [] -> begin
        Traverse.last_block t block_pair >>= function
        | Ok pair -> Lwt.return @@ `New_writes_to pair
        | Error _ ->
          Log.err (fun f -> f "error finding last block from blockpair %Ld, %Ld"
                      (fst block_pair) (snd block_pair));
          Lwt.return @@ `New_writes_to block_pair
      end
      | key::remaining ->
        Find.entries_of_name t block_pair key >>= function
        | Error _ -> Lwt.return @@ `Not_found key
        | Ok [] -> Lwt.return `No_structs
        | Ok l ->
          (* we only care about the last block with entries, and don't care
           * which block it is *)
          let l = snd @@ List.(hd @@ rev l) in
          match List.filter_map Chamelon.Dir.of_entry l with
          | [] -> Lwt.return `No_structs
          | next_blocks::_ -> Lwt.return (`Continue (remaining, next_blocks))
    in 
    (* [find_or_mkdir t parent_blockpair dirname] will:
     * attempt to find [dirname] in the directory starting at [parent_blockpair] or any other blockpairs in its hardtail linked list
     * if no valid entries corresponding to [dirname] are found:
        * allocate new blocks for [dirname]
        * find the last blockpair (q, r) in [parent_blockpair]'s hardtail linked list
        * create a directory entry for [dirname] in (q, r)
     *)
    let find_or_mkdir t parent_blockpair (dirname : string) =
      follow_directory_pointers t parent_blockpair [dirname] >>= function
      | `Continue (_path, next_blocks) -> Lwt.return @@ Ok next_blocks
      | `New_writes_to next_blocks -> Lwt.return @@ Ok next_blocks
      | `No_structs | `Not_found _ ->
        Lwt_mutex.with_lock t.new_block_mutex @@ fun () ->
        (* for any error case, try making the directory *)
        (* TODO: it's probably wise to put a delete entry first here if we got No_structs
         * or another "something weird happened" case *)
        (* first off, get a block pair for our new directory *)
        Allocate.get_block_pair t >>= function
        | Error _ -> Lwt.return @@ Error (`No_space)
        | Ok (dir_block_0, dir_block_1) ->
          (* first, write empty commits to the new blockpair; if that fails,
           * we want to bail before making any more structure *)
          Write.block_to_block_pair t (Chamelon.Block.of_entries ~revision_count:1 []) (dir_block_0, dir_block_1) >>= function
          | Error _ ->
            Log.err (fun f -> f "error initializing a directory at a fresh block pair (%Ld, %Ld)"
                         dir_block_0 dir_block_1);
            Lwt.return @@ Error `No_space
          | Ok () ->
            (* we want to write the entry for our new subdirectory to
             * the *last* blockpair in the parent directory, so follow
             * all the hardtails *)
            Traverse.last_block t parent_blockpair >>= function
            | Error _ -> Lwt.return @@ Error (`Not_found dirname)
            | Ok last_pair_in_dir ->
              Log.debug (fun f -> f "found last pair %a in directory starting at %a"
                             pp_blockpair last_pair_in_dir
                             pp_blockpair parent_blockpair);
              Read.block_of_block_pair t last_pair_in_dir >>= function
              | Error _ -> Lwt.return @@ Error (`Not_found dirname)
              | Ok block_to_write ->
                let extant_ids = Chamelon.Block.ids block_to_write in
                let dir_id = match Chamelon.Block.IdSet.max_elt_opt extant_ids with
                  | None -> 1
                  | Some s -> s + 1
                in
                let name = Chamelon.Dir.name dirname dir_id in
                let dirstruct = Chamelon.Dir.mkdir ~to_pair:(dir_block_0, dir_block_1) dir_id in
                let new_block = Chamelon.Block.add_commit block_to_write [name; dirstruct] in
                Write.block_to_block_pair t new_block last_pair_in_dir >>= function
                | Error _ -> Lwt.return @@ Error `No_space
                | Ok () -> Lwt.return @@ Ok (dir_block_0, dir_block_1)
    in
    match key with
    | [] -> Lwt.return @@ Ok parent_blockpair
    | dirname::more ->
      let open Lwt_result in
      (* finally, the recursive bit: when we've successfully found or made a directory
       * but we have more components in the path,
       * find or make the next component relative to the juts-returned blockpair *)
      find_or_mkdir t parent_blockpair dirname >>= fun newpair ->
      mkdir t newpair more

  module File_read : sig
    val get : t -> Mirage_kv.Key.t -> (string, error) result Lwt.t
    val get_value : t -> (int64 * int64) -> string -> ([> `Btree of int64 * int | `Inline of string],[> `Not_found of string | `Value_expected of string]) result Lwt.t
    val get_partial : t -> Mirage_kv.Key.t -> offset:int -> length:int ->
       (string, error) result Lwt.t
    val get_file_keys_partial : t -> int64 -> int -> int -> (Cstruct.t, [> `Not_found of key]) result Lwt.t

  end = struct
    let key_size = 4
    let key_index t size = 
      let f = Float.(to_int (ceil (of_int size /. of_int t.block_size))) in
      if f<1 then 1 else f

    (* returns a cstruct containing the pointers to the file in reverse *)
    let get_file_keys t key pointer =
      (* number of keys with pointers to blocks containing file data *)
      let rec read_keys pointer acc =
        Log.err (fun f -> f "reading indirect block pointer %Ld" pointer);
        let data = Cstruct.create t.block_size in
        This_Block.read t.block pointer [data]  >>= function
          | Error _ as e -> Lwt.return e
          | Ok () ->
            let next, key_region = Chamelon.File.of_block data in
            Log.err (fun f -> f "next: %Ld, key region offset: %d, length: %d" next key_region.off key_region.len);
            Log.err (fun f -> f "first key in key region: %ld" (Cstruct.LE.get_uint32 key_region 0));
            if Int64.(equal next max_int) then Lwt.return (Ok (key_region::acc))
            else read_keys next (key_region::acc) in
      read_keys pointer [] >>= function
        | Error _ -> Lwt.return @@ Error (`Not_found key)
        | Ok (key_list) -> Lwt.return @@ Ok (Cstruct.concat key_list)
      
    let rec read_file t cached_node key_cs off file_size n acc =
      if n < 0 then 
        let final_cs = Cstruct.concat acc in
        if Cstruct.length final_cs < file_size then
          Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
        else Lwt.return @@ Ok (Cstruct.to_string final_cs ~off:(off mod t.block_size) ~len:file_size)
      else let key = Cstruct.LE.get_uint32 key_cs n in
      Log.err (fun f -> f "got key %ld at offset %d" key n);
      let search_result = 
        try
          Lwt.return @@ Ok (Fs_Btree.Tree_ops.get_pl_from_key cached_node key, cached_node) 
        with Not_found ->
          let ks, _, _, _, _ = Fs_Btree.Attrs.get_all cached_node in
          Log.err (fun f -> f "keys in cached node: %a" Fmt.(list ~sep:sp uint32) ks);
          Log.err (fun f -> f "key not found in cached node, searching tree");
          let tree_root = !root_node in
          Fs_Btree.search t tree_root key (Fs_Btree.Attrs.get_hd tree_root) >>= function
          | Error _ -> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
          | Ok tree -> Lwt.return @@ Ok (Fs_Btree.Tree_ops.get_pl_from_key tree key, tree)
      in search_result >>= function
      | Error _ as e -> 
        Log.err (fun f -> f "search failed"); Lwt.return e
      | Ok (file_pointer, new_node) ->
        Log.err (fun f -> f "found file pointer %Ld associated with key %ld" file_pointer key);
        let data = Cstruct.create t.block_size in
        This_Block.read t.block file_pointer [data] >>= function
        | Error _-> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
        | Ok () ->
          Log.err (fun f -> f "first 10 bytes of this block: %s" (Cstruct.to_string data ~len:10)); 
          Log.err (fun f -> f "last 10 bytes of this block: %s" (Cstruct.to_string data ~off:(Cstruct.length data - 10) ~len:10));
          read_file t new_node key_cs off file_size (n-key_size) (data::acc)
      
    let read_btree_file t key (pointer, file_size) =
      get_file_keys t key pointer >>= function
      | Error _ as e -> Lwt.return e
      | Ok key_cs ->
        let n_keys = key_index t file_size in
        Log.err (fun f -> f "calculated %d keys for file_size %d at pointer %Ld" n_keys file_size pointer);
        let keys = Cstruct.sub key_cs 0 (n_keys*key_size) in
        Log.err (fun f -> f "truncated key region has offset: %d, length: %d" keys.off keys.len);
        read_file t !root_node keys 0 file_size ((n_keys-1)*key_size) []

    let get_file_keys_partial t pointer off len =
      let capacity = (t.block_size / key_size) - 2 in
      let first_key, last_key = key_index t off, key_index t (off+len) in
      Log.err (fun f -> f "first key: %d, last key: %d" first_key last_key);
      let first_key_offset = ((first_key mod capacity)-1)*key_size in
      Log.err (fun f -> f "first key offset: %d" first_key_offset);
      Log.err (fun f -> f "last key offset: %d" (last_key*key_size));
      let rec read_key_selection pointer read acc first_found =
        Log.err (fun f -> f "reading indirect block at pointer %Ld" pointer);
        let data = Cstruct.create t.block_size in
        This_Block.read t.block pointer [data] >>= function
        | Error _ as e -> Lwt.return e
        | Ok () ->
          let next, key_region = Chamelon.File.of_block data in
          let now_read = read+capacity in
          let found = now_read>first_key in
          if now_read > last_key then
            let indirect_offset = if found && not first_found then first_key_offset else 0 in
            let final_k = Cstruct.sub key_region indirect_offset ((last_key*key_size)-indirect_offset) in
            Lwt.return @@ Ok (final_k::acc)
          else if not first_found then
            let kl = if found then 
              (Cstruct.sub key_region first_key_offset ((capacity*key_size)-first_key_offset))::acc 
            else acc in
            read_key_selection next (read+capacity) kl found
          else
            read_key_selection next now_read (key_region::acc) first_found in
      read_key_selection pointer 0 [] false >>= function
      | Error _ -> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
      | Ok (key_list) -> Lwt.return @@ Ok (Cstruct.concat key_list)

    let rec read_btree_partial t key (pointer, file_size) off len acc =
      if off>=file_size then Lwt.return @@ Ok ""
      else let new_len = min (file_size-off) len in
      let to_read = min (t.block_size-(off mod t.block_size)) new_len in
      get_file_keys_partial t pointer off to_read >>= function
      | Error _ -> Lwt.return @@ Error (`Not_found key)
      | Ok key_cs -> 
        read_file t !root_node key_cs off to_read (Cstruct.length key_cs - key_size) [] >>= function
        | Error _ -> Lwt.return @@ Error (`Not_found key)
        | Ok s -> 
          if new_len-to_read=0 then Lwt.return @@ Ok (String.concat "" (List.rev (s::acc)))
          else read_btree_partial t key (pointer, file_size) (off+to_read) (new_len-to_read) (s::acc)

    let get_value t parent_dir_head filename =
      Find.entries_of_name t parent_dir_head filename >|= function
      | Error _ | Ok [] -> Error (`Not_found filename)
      | Ok compacted ->
        (* if there are >1 block with entries, we only care about the last one *)
        let compacted = snd @@ List.(hd @@ rev compacted) in
        let inline_files = List.find_opt (fun (tag, _data) ->
            Chamelon.Tag.((fst tag.type3) = LFS_TYPE_STRUCT) &&
            Chamelon.Tag.((snd tag.type3) = 0x01)
          )
        in
        let btree_files = List.find_opt (fun (tag, _block) ->
            Chamelon.Tag.((fst tag.type3 = LFS_TYPE_STRUCT) &&
                          Chamelon.Tag.((snd tag.type3 = 0x02)
                                       ))) in
        Log.debug (fun m -> m "found %d entries with name %s" (List.length compacted) filename);
        match inline_files compacted, btree_files compacted with
        | Some (_tag, data), None -> Ok (`Inline (Cstruct.to_string data))
        | None, None -> begin
          (* is it actually a directory? *)
            match List.find_opt (fun (tag, _data) ->
                Chamelon.Tag.((fst tag.type3) = LFS_TYPE_STRUCT) &&
                Chamelon.Tag.((snd tag.type3) = 0x00)
              ) compacted with
            | Some _ -> Error (`Value_expected filename)
            | None ->
              Log.debug (fun f -> f "an ID was found for the filename, but no entries are structs or files");
              Error (`Not_found filename)
        end
        | _, Some (_, btr) ->
          match Chamelon.File.btree_of_cstruct btr with
          | Some (pointer, length) -> Ok (`Btree (pointer, Int64.to_int length))
          | None -> Error (`Value_expected filename)

    let get t key : (string, error) result Lwt.t =
      let map_result = function
        | Ok (`Inline d) -> Lwt.return (Ok d)
        | Ok (`Btree btr) -> read_btree_file t key btr
        | Error (`Not_found k) -> Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v k))
        | Error (`Value_expected k) -> Lwt.return @@ Error (`Value_expected (Mirage_kv.Key.v k))
      in
      match Mirage_kv.Key.segments key with
      | [] -> Lwt.return @@ Error (`Value_expected key)
      | basename::[] -> get_value t root_pair basename >>= map_result
      | _ ->
        let dirname = Mirage_kv.Key.(parent key |> segments) in
        Find.find_first_blockpair_of_directory t root_pair dirname >>= function
        | `Basename_on pair -> begin
            get_value t pair (Mirage_kv.Key.basename key) >>= map_result
          end
        | _ -> Lwt.return @@ Error (`Not_found key)

    let get_partial t key ~offset ~length : (string, error) result Lwt.t =
      if offset < 0 then begin
        Log.err (fun f -> f "read requested with negative offset");
        Lwt.return @@ Error (`Not_found key)
      end else if length <= 0 then begin
        Log.err (fun f -> f "read requested with length <= 0");
        Lwt.return @@ Ok ""
      end else begin
        let map_result = function
          | Error (`Not_found k) -> Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v k))
          | Error (`Value_expected k) -> Lwt.return @@ Error (`Value_expected (Mirage_kv.Key.v k))
          | Ok (`Inline d) -> begin
            try Lwt.return @@ Ok (String.sub d offset @@ min length @@ (String.length d) - offset)
            with Invalid_argument _ -> Lwt.return @@ Error (`Not_found key)
          end
          | Ok (`Btree btr) -> read_btree_partial t key btr offset length []
        in
        match Mirage_kv.Key.segments key with
        | [] -> Lwt.return @@ Error (`Value_expected key)
        | basename::[] -> get_value t root_pair basename >>= map_result
        | _ ->
          let dirname = Mirage_kv.Key.(parent key |> segments) in
          Find.find_first_blockpair_of_directory t root_pair dirname >>= function
          | `Basename_on pair -> begin
              get_value t pair (Mirage_kv.Key.basename key) >>= map_result
            end
          | _ -> Lwt.return @@ Error (`Not_found key)
      end
  end

  module Size = struct
    let get_file_size t parent_dir_head filename =
      Find.entries_of_name t parent_dir_head filename >|= function
      | Error _ | Ok [] -> Error (`Not_found (Mirage_kv.Key.v filename))
      | Ok compacted ->
        let entries = snd @@ List.(hd @@ rev compacted) in
        let inline_files = List.find_opt (fun (tag, _data) ->
            Chamelon.Tag.((fst tag.type3) = LFS_TYPE_STRUCT) &&
            Chamelon.Tag.((snd tag.type3) = 0x01)
          )
        in
        let btree_files = List.find_opt (fun (tag, _block) ->
            Chamelon.Tag.((fst tag.type3 = LFS_TYPE_STRUCT) &&
                          Chamelon.Tag.((snd tag.type3 = 0x02)
                                       ))) in
        Log.debug (fun m -> m "found %d entries with name %s" (List.length compacted) filename);
        match inline_files entries, btree_files entries with
        | None, None -> Error (`Not_found (Mirage_kv.Key.v filename))
        | Some (tag, _data), None ->
          Ok tag.Chamelon.Tag.length
        | _, Some (_tag, data) ->
          match Chamelon.File.btree_of_cstruct data with
          | Some (_pointer, length) -> Ok (Int64.to_int length)
          | None -> Error (`Value_expected (Mirage_kv.Key.v filename))

    let rec size_all t blockpair =
      Find.all_entries_in_dir t blockpair >>= function
      | Error _ -> Lwt.return 0
      | Ok l ->
        let entries = List.(map snd l |> flatten) in
        Lwt_list.fold_left_s (fun acc e ->
            match Chamelon.Content.size e with
            | `File n -> Lwt.return @@ acc + n
            | `Skip -> Lwt.return @@ acc
            | `Dir p ->
              Log.debug (fun f -> f "descending into dirpair %a" pp_blockpair p);
              size_all t p >>= fun s -> Lwt.return @@ s + acc
          ) 0 entries

    let size t key : (int, error) result Lwt.t =
      Log.debug (fun f -> f "getting size on key %a" Mirage_kv.Key.pp key);
      match Mirage_kv.Key.segments key with
      | [] -> size_all t root_pair >>= fun i -> Lwt.return @@ Ok i
      | basename::[] -> get_file_size t root_pair basename
      | segments ->
        Log.debug (fun f -> f "descending into segments %a" Fmt.(list ~sep:comma string) segments);
        Find.find_first_blockpair_of_directory t root_pair segments >>= function
        | `Basename_on p -> size_all t p >|= fun i -> Ok i
        | `No_id _ | `No_structs -> begin
            (* no directory by that name, so try for a file *)
            Find.find_first_blockpair_of_directory t root_pair segments >>= function
            | `Basename_on pair -> begin
                get_file_size t pair (Mirage_kv.Key.basename key)
              end
            | _ -> Lwt.return @@ Error (`Not_found key)
        end

  end

  module File_write : sig
    (** [set_in_directory directory_head t filename data] creates entries in
     * [directory] for [filename] pointing to [data] *)
    val set_in_directory : directory_head -> t -> string -> offset:int -> length:int -> string ->
      (unit, write_error) result Lwt.t

  end = struct
    let key_size = 4
    let key_index t size = Float.(to_int (ceil (of_int size /. of_int t.block_size)))

    let write_indirect_blocks t file_size block_pointers keys =
      Log.err (fun f -> f "write indirect blocks call");
      let n_keys = key_index t file_size in
      let capacity = (t.block_size / key_size) - 2 in
      let rec write_block t pointer read n_block =
        let block_cs = Cstruct.create t.block_size in
        let now_read = read+capacity in
        let last_block = now_read >= n_keys in
        let to_write = if last_block then n_keys-read else now_read in
        Cstruct.blit keys (read*key_size) block_cs 0 (to_write*key_size);
        let next = if not last_block then 
          Cstruct.LE.get_uint64 block_pointers (n_block*sizeof_pointer)
        else Int64.max_int in 
        Log.err (fun f -> f "pointer: %Ld, read: %d, n_block: %d, n_keys: %d, capacity: %d, now_read: %d, last_block: %b, to_write: %d, next: %Ld"
        pointer read n_block n_keys capacity now_read last_block to_write next);
        Cstruct.LE.set_uint64 block_cs (t.block_size-sizeof_pointer) next;
        Log.err (fun f -> f "block to be written at pointer %Ld has key %ld at offset 0" pointer (Cstruct.LE.get_uint32 block_cs 0));
        This_Block.write t.block pointer [block_cs] >>= function
        | Error _ as e -> Lwt.return e
        | Ok () -> if last_block then Lwt.return @@ Ok ()
          else write_block t next now_read (n_block+1) in
      write_block t (Cstruct.LE.get_uint64 block_pointers 0) 0 1

    let rec append_indirect_block t pointer keys starting_offset ptr_to_add nk =
      let rec append_key cs off n =
        Log.err (fun f -> f "appending key %d to offset %d, number of keys: %d" n off nk);
        Cstruct.blit keys (n*key_size) cs off key_size;
        if n=(nk-1) then () else append_key cs (off+key_size) (n+1) in
      let block_cs = Cstruct.create t.block_size in
      This_Block.read t.block pointer [block_cs] >>= function
      | Error _ -> Lwt.return @@ Error `Disconnected
      | Ok () ->
        let next = Cstruct.LE.get_uint64 block_cs (t.block_size-sizeof_pointer) in
        if Int64.(equal next max_int) then begin
          append_key block_cs starting_offset 0;
          Log.err (fun f -> f "setting pointer %Ld in indirect block" ptr_to_add);
          Cstruct.LE.set_uint64 block_cs (t.block_size-sizeof_pointer) ptr_to_add;
          Log.err (fun f -> f "rewriting indirect block to %Ld" pointer);
          This_Block.write t.block pointer [block_cs]
        end else append_indirect_block t next keys starting_offset ptr_to_add nk

    let rec write_btree_keys t tree key_cs data file_pointers k n written =
      let off = n*sizeof_pointer in
      let pl = Cstruct.LE.get_uint64 file_pointers off in
      Fs_Btree.insert t tree k pl >>= function
      | Error _ -> Lwt.return @@ Error `Disconnected
      | Ok tr -> 
        let block_cs = Cstruct.create t.block_size in
        let len = min t.block_size (String.length data - written) in
        let data_s = String.sub data (n*t.block_size) len in
        Log.err (fun f -> f "first 10 bytes of string to write: %s" (String.sub data_s 0 10));
        Log.err (fun f -> f "last 10 bytes of string to write: %s" (String.sub data_s (len-10) 10));
        Cstruct.blit_from_string data (n*t.block_size) block_cs 0 len;
        Log.err (fun f -> f "writing data to pointer %Ld, key = %ld" pl k);
        This_Block.write t.block pl [block_cs] >>= function
        | Error _ as e -> Lwt.return e
        | Ok () ->
          Cstruct.LE.set_uint32 key_cs (n*key_size) k;
          if len < t.block_size then Lwt.return @@ Ok (tr)
          else write_btree_keys t tr key_cs data file_pointers Int32.(add k one) (n+1) (written+len)

    let write_file t data (prev_pointer, prev_file_size) append =
      let n_keys_in_block = (t.block_size / 4) - 2 in
      let size_in_last_block = if not append then 0 else prev_file_size mod t.block_size in
      let data_length = String.length data in
      let to_add = 
        if append then 
          if size_in_last_block=0 then 0
          else min data_length (t.block_size-size_in_last_block) 
        else 0 in
      let continue_write data =
        let file_size = String.length data in
        if file_size = 0 then Lwt.return @@ Ok (Int64.max_int, file_size)
        else let prev_keys = key_index t prev_file_size in
        let n_keys_for_file_size = key_index t file_size in
        let key_offset_in_indirect = prev_keys mod n_keys_in_block in
        let space_in_indirect = n_keys_in_block - key_offset_in_indirect in
        let overflow = space_in_indirect < n_keys_for_file_size in
        let rem = if overflow then space_in_indirect else n_keys_for_file_size in
        let n_keys = 
          if append then n_keys_for_file_size-rem
          else key_index t file_size in
        let n_indirect_blocks = 
          let n = Float.(to_int (ceil (of_int n_keys) /. (of_int n_keys_in_block))) in
          if n < 1 then 1 else n in
        let n_file_blocks = key_index t file_size in
        Log.err (fun f -> f "n_keys_in_block: %d, file_size: %d, prev_keys: %d, rem: %d, n_keys: %d, n_indirect_blocks: %d, n_file_blocks: %d"
        n_keys_in_block file_size prev_keys rem n_keys n_indirect_blocks n_file_blocks);
        Allocate.get_blocks t (n_indirect_blocks + n_file_blocks) >>= function
        | Error _ -> Lwt.return @@ Error `No_space
        | Ok block_pointers ->
          let cutoff = n_indirect_blocks*sizeof_pointer in
          let indirect_cs = Cstruct.sub block_pointers 0 cutoff in
          let file_pointer_cs = Cstruct.sub block_pointers cutoff 
          (Cstruct.length block_pointers - cutoff) in
          let key_cs = Cstruct.create (n_file_blocks * key_size) in
          let tree_root = !root_node in
          let ckey = Fs_Btree.Attrs.(if is_empty tree_root then Int32.minus_one else get_hd tree_root) in
          Fs_Btree.get_largest t tree_root ckey >>= function
          | Error _ -> Lwt.return @@ Error `No_space
          | Ok largest_key ->
            let first_key = Int32.(add largest_key one) in
            write_btree_keys t tree_root key_cs data file_pointer_cs first_key 0 0 >>= function
            | Error _ -> Lwt.return @@ Error `No_space
            | Ok tree ->
              root_node := tree;
              let pointer = Cstruct.LE.get_uint64 block_pointers 0 in
              let append_pointer = if overflow then pointer else Int64.max_int in
              if (prev_file_size=0) then
                write_indirect_blocks t file_size indirect_cs key_cs >>= function
                | Error _ -> Lwt.return @@ Error `No_space
                | Ok () -> Lwt.return @@ Ok (pointer, file_size)
              else append_indirect_block t prev_pointer key_cs (key_offset_in_indirect*key_size) append_pointer rem >>= function
              | Error _ -> Lwt.return @@ Error `No_space
              | Ok () -> 
                (* if the appended data's keys fit into the indirect block, we are done *)
                if n_keys=0 then Lwt.return @@ Ok (Int64.max_int, prev_file_size+file_size)
                else let trunc_keys = Cstruct.sub key_cs (rem*key_size) (Cstruct.length key_cs - (rem*key_size)) in
                write_indirect_blocks t file_size indirect_cs trunc_keys >>= function
                | Error _ -> Lwt.return @@ Error `No_space
                | Ok () -> Lwt.return @@ Ok (Int64.max_int, prev_file_size+file_size) in
      if to_add > 0 then 
        File_read.get_file_keys_partial t prev_pointer (prev_file_size-to_add) to_add >>= function
        | Error _ as e -> Lwt.return e
        | Ok key_cs ->
          let key = Cstruct.LE.get_uint32 key_cs 0 in
          let tree_root = !root_node in
          Fs_Btree.(search t tree_root key (Attrs.get_hd tree_root)) >>= function
          | Error _ -> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
          | Ok tree -> let pointer = Fs_Btree.Tree_ops.get_pl_from_key tree key in
            let block_cs = Cstruct.create t.block_size in
            This_Block.read t.block pointer [block_cs] >>= function
            | Error _ -> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
            | Ok () ->
              Log.err (fun f -> f "got last block of file at pointer %Ld from key %ld" pointer key);
              Log.err (fun f -> f "first 10 bytes in this block: %s" (Cstruct.to_string block_cs ~off:0 ~len:10));
              Log.err (fun f -> f "last 10 bytes of file: %s" (Cstruct.to_string block_cs ~off:(size_in_last_block-10) ~len:10));
              Log.err (fun f -> f "last 10 bytes in this block: %s" (Cstruct.to_string block_cs ~off:(t.block_size-10) ~len:10));
              Cstruct.blit_from_string data 0 block_cs size_in_last_block to_add;
              This_Block.write t.block pointer [block_cs] >>= function
              | Error _ -> Lwt.return @@ Error `No_space
              | Ok () -> 
                Log.err (fun f -> f "appended %d bytes to block at pointer %Ld" to_add pointer);
                Log.err (fun f -> f "%d bytes remaining to write to new blocks" (data_length-to_add));
                continue_write (String.sub data to_add (data_length-to_add)) >>= function
                | Error _ as e -> Lwt.return e
                | Ok _ -> Lwt.return @@ Ok (Int64.max_int, prev_file_size+data_length)
      else continue_write data
    
    let update_in_place t data prev_pointer offset =
      let rec write_data cached_node keys n data written first_off =
        let key = Cstruct.LE.get_uint32 keys (n*key_size) in
        let search_result = 
          try
            Lwt.return @@ Ok (Fs_Btree.Tree_ops.get_pl_from_key cached_node key, cached_node) 
          with Not_found ->
            let ks, _, _, _, _ = Fs_Btree.Attrs.get_all cached_node in
            Log.err (fun f -> f "keys in cached node: %a" Fmt.(list ~sep:sp uint32) ks);
            Log.err (fun f -> f "key not found in cached node, searching tree");
            let tree_root = !root_node in
            Fs_Btree.search t tree_root key (Fs_Btree.Attrs.get_hd tree_root) >>= function
            | Error _ -> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
            | Ok tree -> Lwt.return @@ Ok (Fs_Btree.Tree_ops.get_pl_from_key tree key, tree)
        in search_result >>= function
        | Error _ as e -> 
          Log.err (fun f -> f "search failed"); Lwt.return e
        | Ok (file_pointer, new_node) ->
          let block_cs = Cstruct.create t.block_size in
          if n=0 || ((String.length data)-written<t.block_size) then
            This_Block.read t.block file_pointer [block_cs] >>= function
            | Error _ -> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
            | Ok () ->
              let off = if n=0 then first_off else 0 in
              let len = min t.block_size (String.length data - written) in
              Cstruct.blit_from_string data written block_cs off len;
              Log.err (fun f -> f "copying %d bytes into block at pointer %Ld" len file_pointer);
              Log.err (fun f -> f "first 10 bytes: %s" (String.sub data written 10));
              Log.err (fun f -> f "last 10 bytes: %s" (String.sub data (written+len-10) 10));
              This_Block.write t.block file_pointer [block_cs] >>= function
              | Error _ -> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
              | Ok () ->
                if len<t.block_size then Lwt.return @@ Ok ()
                else write_data new_node keys (n+1) data (written+len) first_off
          else begin 
            Cstruct.blit_from_string data written block_cs 0 t.block_size;
            This_Block.write t.block file_pointer [block_cs] >>= function
            | Error _ -> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
            | Ok () -> write_data new_node keys (n+1) data (written+t.block_size) first_off 
          end in
      File_read.get_file_keys_partial t prev_pointer offset (String.length data) >>= function
      | Error _ -> Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
      | Ok key_cs -> write_data !root_node key_cs 0 data 0 (offset mod t.block_size)

    let write_file_entry t filename root dir_block_pair entries pointer file_size =
      let next = match Chamelon.Block.(IdSet.max_elt_opt @@ ids root) with
        | None -> 1
        | Some n -> n + 1
      in
      let name = Chamelon.File.name filename next in
      let ctime = Chamelon.Entry.ctime next (Clock.now_d_ps ()) in
      let btree = Chamelon.File.create_btree_file next 
          ~pointer:pointer ~file_size:(Int64.of_int file_size)
      in
      let new_entries = entries @ [name; ctime; btree] in
              Log.err (fun m -> m "writing %d entries for file %s of size %d" (List.length new_entries) filename file_size);
              let new_block = Chamelon.Block.add_commit root new_entries in
              Write.block_to_block_pair t new_block dir_block_pair >>= function
              | Error `No_space -> Lwt.return @@ Error `No_space
              | Error _ -> Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v filename))
              | Ok () -> Lwt.return @@ Ok ()

    let rec find_and_write_file dir_block_pair t filename data entries (pointer, file_size) append in_place =
      Read.block_of_block_pair t dir_block_pair >>= function
      | Error _ -> Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v filename))
      | Ok root ->
        match Chamelon.Block.hardtail root with
        | Some next_blockpair -> find_and_write_file next_blockpair t filename data entries (pointer, file_size) append in_place
        | None ->
          if in_place>(-1) then update_in_place t data pointer in_place
          else write_file t data (pointer, file_size) append >>= function
          | Error _ as e -> Lwt.return e
          | Ok (p, f_size) ->
            Log.err (fun f -> f "written file to pointer %Ld with filesize %d" p f_size);
            let newp = if Int64.(equal p max_int) then pointer else p in
            write_file_entry t filename root dir_block_pair entries newp f_size

    let rec write_inline block_pair t filename data entries =
      Read.block_of_block_pair t block_pair >>= function
      | Error _ ->
        Log.err (fun m -> m "error reading block pair %Ld, %Ld"
                     (fst block_pair) (snd block_pair));
        Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v filename))
      | Ok extant_block ->
        match Chamelon.Block.hardtail extant_block with
        | Some next_blockpair -> write_inline next_blockpair t filename data entries
        | None ->
          let used_ids = Chamelon.Block.ids extant_block in
          let next = match Chamelon.Block.IdSet.max_elt_opt used_ids with
            | None -> 1
            | Some n -> n + 1
          in
          let ctime = Chamelon.Entry.ctime next (Clock.now_d_ps ()) in
          let file = Chamelon.File.write_inline filename next (Cstruct.of_string data) in
          let commit = entries @ (ctime :: file) in
          Log.debug (fun m -> m "writing %d entries for inline file %s" (List.length file) filename);
          let new_block = Chamelon.Block.add_commit extant_block commit in
          Write.block_to_block_pair t new_block block_pair >>= function
          | Error `No_space -> Lwt.return @@ Error `No_space
          | Error `Split | Error `Split_emergency ->
            Log.err (fun m -> m "couldn't write a block, because it got too big");
            Lwt.return @@ Error `No_space
          | Ok () -> Lwt.return @@ Ok ()

    let set_in_directory block_pair t (filename : string) ~offset ~length data =
      Log.err (fun f -> f "set_in_directory: %s, off=%d, len=%d" filename offset length);
      if String.length filename < 1 then Lwt.return @@ Error (`Value_expected Mirage_kv.Key.empty)
      else begin
        Lwt_mutex.with_lock t.new_block_mutex @@ fun () ->
        Find.entries_of_name t block_pair filename >>= function
        | Error (`Not_found _ ) as e -> Lwt.return e
        | Ok [] | Ok ((_, [])::_) | Error (`No_id _) -> begin
            Log.debug (fun m -> m "writing new file %s, size %d" filename (String.length data));
            if (String.length data) > (t.block_size / 4) then
              find_and_write_file block_pair t filename data [] (Int64.max_int, 0) false (-1)
            else
              write_inline block_pair t filename data []
          end
        | Ok ((block, hd::tl)::entries) ->
          let id = Chamelon.Tag.((fst hd).id) in
          Log.debug (fun m -> m "deleting existing entry %s at id %d" filename id);
          let delete = (Chamelon.Tag.(delete id), Cstruct.create 0) in
          let all_entries = 
            let _, es = List.split entries in List.flatten ((hd::tl)::es) in
          let btree_files = List.find_opt (fun (tag, _block) ->
            Chamelon.Tag.((fst tag.type3 = LFS_TYPE_STRUCT) &&
                          Chamelon.Tag.((snd tag.type3 = 0x02)
                                       ))) in
          let btr_entry = match btree_files all_entries with
          | None -> (Int64.max_int, 0)
          | Some btree -> (match Chamelon.File.btree_of_cstruct (snd btree) with
            | None -> (Int64.max_int, 0)
            | Some (p, f_size) -> (p, Int64.to_int f_size)) in
          let to_write = String.length data in
          let prev_file_size = snd btr_entry in
          if offset>prev_file_size then Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
          else let append, in_place = offset=prev_file_size, prev_file_size!=0 in
          let in_place_off = if in_place then offset else -1 in
          if not append && (offset+length)>prev_file_size then 
            (Log.err (fun f -> f "write requested at offset %d of length %d which exceeds file size %d"
          offset length prev_file_size);
          Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty))
          else if to_write > (t.block_size / 4) || append || in_place then
            find_and_write_file block t filename data [delete] btr_entry append in_place_off
          else
            write_inline block t filename data [delete]
      end

  end

  module Delete = struct
    let key_size = 4
    let delete_file_data t dir filename = 
      let rec get_keys keys acc n =
        if n<0 then acc
        else let k = Cstruct.LE.get_uint32 keys (n*t.block_size) in
        get_keys keys (k::acc) (n-1) in
      let rec plist_to_cstruct pointers cs n =
        if pointers=[] then cs
        else let pointer = List.hd pointers in
        Cstruct.LE.set_uint64 cs (n*sizeof_pointer) pointer;
        plist_to_cstruct (List.tl pointers) cs (n+1) in     
      File_read.get_value t dir filename >>= function
      | Ok (`Inline _) -> Lwt.return @@ Ok ()
      | Ok (`Btree btr) -> 
        File_read.get_file_keys_partial t (fst btr) 0 (snd btr) >>= (function
        | Error _ -> Lwt.return @@ Error `Not_found
        | Ok keys -> 
          let ks = get_keys keys [] ((Cstruct.length keys)-key_size) in
          Fs_Btree.delete_list t !root_node ks [] >>= function
          | Error _ -> Lwt.return @@ Error `Not_found
          | Ok (tree, pointers) -> 
            root_node := tree;
            let cs = Cstruct.create ((List.length pointers)*sizeof_pointer) in
            let pointer_cs = plist_to_cstruct pointers cs 0 in
            let lookahead = !(t.lookahead) in
            Lookahead.add_to_lookahead lookahead pointer_cs;
            t.lookahead := lookahead;
            Lwt.return @@ Ok ())
      | Error (`Not_found _) -> Lwt.return @@ Ok ()
      | Error (`Value_expected _) -> Lwt.return @@ Ok ()

    let delete_in_directory directory_head t name =
      Find.entries_of_name t directory_head name >>= function
        (* several "it's not here" cases *)
      | Error (`No_id _) | Error (`Not_found _) ->
        Log.debug (fun m -> m "no id or nothing found for %s" name);
        Lwt.return @@ Ok ()
      | Ok [] | Ok ((_,[])::_) ->
        Log.debug (fun m -> m "no entries on %a for %s"
                       pp_blockpair directory_head name);
        Lwt.return @@ Ok ()
      | Ok ((blockpair_with_id, hd::_tl)::_) ->
        delete_file_data t blockpair_with_id name >>= (function
        | Error _ -> 
          Log.debug (fun m -> m "file not found in dir for %s" name);
          Lwt.return @@ Ok ()
        | Ok () ->
          let id = Chamelon.Tag.((fst hd).id) in
          Log.debug (fun m -> m "id %d found for name %s on block %a" id name
                   pp_blockpair blockpair_with_id);
          Read.block_of_block_pair t blockpair_with_id >>= function
          | Error _ -> Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v name))
          | Ok block ->
            Log.debug (fun m -> m "adding deletion for id %d on block pair %a"
                         id pp_blockpair blockpair_with_id);
            let deletion = Chamelon.Tag.delete id in
            let new_block = Chamelon.Block.add_commit block [(deletion, Cstruct.empty)] in
            Write.block_to_block_pair t new_block blockpair_with_id >>= function
            | Error _ -> Lwt.return @@ Error `No_space
            | Ok () -> Lwt.return @@ Ok ())

  end

(* [block_size_device] is the block size used by the underlying block device which
 * we're trying to mount a filesystem from,
 * as opposed to the block size recorded in the filesystem's superblock *)
  let check_superblock ~program_block_size ~block_size_device cs =
    match Chamelon.Block.of_cstruct ~program_block_size cs with
    | Error (`Msg s) ->
      Log.err (fun f -> f "error parsing block when checking superblock: %s" s);
      Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
    | Ok parsed_block ->
      (* does this block have the expected superblock entries? *)
      (* the order of entries is strictly specified: name, then the inline struct, then
       * any other entries in the superblock *)
      match Chamelon.Block.entries parsed_block with
      | maybe_name :: maybe_struct :: _ when
          Chamelon.Superblock.is_valid_name maybe_name &&
          Chamelon.Superblock.is_valid_superblock maybe_struct -> begin
        match Chamelon.Superblock.parse (snd maybe_struct) with
        | Error (`Msg s) ->
          Log.err (fun f -> f "error parsing block when checking superblock: %s" s);
          Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
        | Ok sb ->
          if sb.version_major != fst Chamelon.Superblock.version then begin
            Log.err (fun f -> f "filesystem is an incompatible version");
            Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
          end else if not @@ Int32.equal sb.block_size block_size_device then begin
            Log.err (fun f -> f "filesystem expects a block device with size %ld but the device block size is %ld" sb.block_size block_size_device);
            Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
          end else Lwt.return @@ Ok (Chamelon.Block.revision_count parsed_block, sb)
      end
      | _ -> Log.err (fun f -> f "expected entries not found on parsed superblock");
        Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)

  (* `device` should be an already-connected block device *)
  let connect ~program_block_size ~block_size device : (t, error) result Lwt.t =
    This_Block.connect ~block_size device >>= fun block ->
    Log.err (fun f -> f "initiating filesystem with block size %d (0x%x)" block_size block_size);
    let block0, block1= Cstruct.create block_size, Cstruct.create block_size in
    Lwt_result.both 
      (This_Block.read block 0L [block0])
      (This_Block.read block 1L [block1])
    >>= function
    | Error e ->
      Log.err (fun f -> f "first blockpair read failed: %a" This_Block.pp_error e);
      Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
    | Ok ((), ()) ->
      (* make sure the block is parseable and block size matches *)
      Lwt_result.both
        (check_superblock ~program_block_size ~block_size_device:(Int32.of_int block_size) block0)
        (check_superblock ~program_block_size ~block_size_device:(Int32.of_int block_size) block1)
      >>= function
      | Error _ as e -> Lwt.return e
      | Ok ((rc0, sb0), (rc1, sb1)) ->
        let lookahead = ref (Cstruct.create (This_Block.block_count block)) in
        let file_size_max, name_length_max =
          if rc1 > rc0 then sb1.file_size_max, sb1.name_length_max else sb0.file_size_max, sb0.name_length_max
        in
        let t = {block;
                 block_size;
                 program_block_size;
                 lookahead;
                 file_size_max;
                 name_length_max;
                 new_block_mutex = Lwt_mutex.create ()}
        in
        Log.debug (fun f -> f "mounting fs with file size max %ld, name length max %ld" file_size_max name_length_max);
        Lwt_mutex.lock t.new_block_mutex >>= fun () ->
        let b = t.block_size / 24 in
        Traverse.build_btree t b >>= function
        | Error _e ->
          Lwt_mutex.unlock t.new_block_mutex;
          Log.err (fun f -> f "couldn't build b-tree");
          Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
        | Ok () ->
          (Traverse.follow_links_tree t b >>= function
          | Error _e ->
            Lwt_mutex.unlock t.new_block_mutex;
            Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
          | Ok lookahead_arr ->
            let lookahead = ref lookahead_arr in
            Lwt_mutex.unlock t.new_block_mutex;
            Lwt.return @@ Ok {t with lookahead; block; block_size; program_block_size})

  let format ~program_block_size ~block_size (sectors : Sectors.t) :
    (unit, write_error) result Lwt.t =
    This_Block.connect ~block_size sectors >>= fun block ->
    let write_whole_block n b = This_Block.write block n
        [fst @@ Chamelon.Block.to_cstruct ~program_block_size ~block_size b]
    in
    let name = Chamelon.Superblock.name in
    let block_count = This_Block.block_count block in
    let superblock_inline_struct = Chamelon.Superblock.inline_struct (Int32.of_int block_size) (Int32.of_int block_count) in
    let block_0 = Chamelon.Block.of_entries ~revision_count:1 [name; superblock_inline_struct] in
    let block_1 = Chamelon.Block.of_entries ~revision_count:2 [name; superblock_inline_struct] in
    Lwt_result.both
    (write_whole_block (fst root_pair) block_0)
    (write_whole_block (snd root_pair) block_1) >>= function
    | Ok ((), ()) -> Lwt.return @@ Ok ()
    | _ -> Lwt.return @@ Error `No_space

end
