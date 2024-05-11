open Lwt.Infix
open Logs_syslog_lwt

(* in LittleFS, the superblock and the root of the filesystem
 * is always at a constant pair - addresses (0, 1) *)
let root_pair = (0L, 1L)

module Make(Sectors : Mirage_block.S)(Clock : Mirage_clock.PCLOCK) = struct
  module Fs = Fs.Make(Sectors)(Clock)
  module Block_types = Block_type.Make(Sectors)

  type key = Mirage_kv.Key.t

  type statvfs = {
    f_bsize : int64;
    f_frsize : int64;
    f_blocks : int64;
    f_bfree : int64;
    f_bavail : int64;
    f_files : int64;
    f_ffree : int64;
    f_favail : int64;
    f_fsid : int64;
    f_flag : int64;
    f_namemax : int64;
  }

  let install_logger () =
    unix_reporter () >|= function
      | Ok r -> Logs.set_reporter r
      | Error e -> print_endline e

  let _ = Lwt_main.run (install_logger ())

  let log_src = Logs.Src.create "chamelon-kv" ~doc:"chamelon KV layer"
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

  let pp_error fmt = function
    | `Not_found key -> Format.fprintf fmt "key %a not found" Mirage_kv.Key.pp key
    | `Dictionary_expected key -> Format.fprintf fmt "%a was not a dictionary" Mirage_kv.Key.pp key
    | `Value_expected key -> Format.fprintf fmt "%a was not a value" Mirage_kv.Key.pp key

  let pp_write_error fmt = function
    | `No_space -> Format.fprintf fmt "no space left on device"
    | `Too_many_retries n -> Format.fprintf fmt "tried to write %d times and didn't succeed" n
    | #error as e -> pp_error fmt e

  type t = Block_types.t

  let get = Fs.File_read.get

  let get_partial = Fs.File_read.get_partial

  (* [set] does a little work on top of the filesystem's set functions, because
   * we need to make directories if the key has >1 segment in it. *)
  (* Once we've either found or created the parent directory, we can ask the FS layer
   * to set the data appropriately there. *)
  let set t key data : (unit, write_error) result Lwt.t =
    let name_length = String.length @@ Mirage_kv.Key.basename key in
    if name_length > (Int32.to_int t.Block_types.name_length_max) then begin
      Log.err (fun f -> f "key length %d exceeds max length %ld - refusing to write" name_length t.Block_types.name_length_max);
      Lwt.return @@ Error (`Not_found Mirage_kv.Key.empty)
    end else begin
      let dir = Mirage_kv.Key.parent key in
      Fs.Find.find_first_blockpair_of_directory t root_pair
        (Mirage_kv.Key.segments dir) >>= function
      | `Basename_on block_pair ->
        Log.debug (fun m -> m "found basename of path %a on block pair %Ld, %Ld"
                      Mirage_kv.Key.pp key
                      (fst block_pair) (snd block_pair));
        (* the directory already exists, so just write the file *)
        Fs.File_write.set_in_directory block_pair t (Mirage_kv.Key.basename key) data
      | `No_id path -> begin
          Log.debug (fun m -> m "path component %s had no id; making it and its children" path);
          (* something along the path is missing, so make it. *)
          (* note we need to call mkdir with the whole path (except for the basename),
           * so that we get all levels of directory we may need,
           * not just the first thing that was found missing. *)
          Fs.mkdir t root_pair (Mirage_kv.Key.segments dir) >>= function
          | Error (`Not_found _) -> Lwt.return @@ (Error (`Not_found (Mirage_kv.Key.v path)))
          | Error `No_space as e -> Lwt.return e
          | Ok block_pair ->
            Log.debug (fun m -> m "made filesystem structure for %a, writing to blockpair %Ld, %Ld"
                          Mirage_kv.Key.pp dir (fst block_pair) (snd block_pair)
                      );
            Fs.File_write.set_in_directory block_pair t (Mirage_kv.Key.basename key) data
        end
      (* No_structs represents an inconsistent on-disk structure.
       * We can't do the right thing, so we return an error. *)
      | `No_structs ->
        Log.err (fun m -> m "id was present but no matching directory structure");
        Lwt.return @@ Error (`Not_found key)
    end

  (** [list t key], where [key] is a reachable directory,
   * gives the files and directories (values and dictionaries) in [key].
   * It is not a recursive listing. *)
  let list t key : ((string * [`Dictionary | `Value]) list, error) result Lwt.t =
    let cmp (name1, _) (name2, _) = String.compare name1 name2 in
    (* once we've found the (first) directory pair of the *parent* directory,
     * get the list of all entries naming files or directories
     * and sort them *)
    let ls_in_dir dir_pair =
      Fs.Find.all_entries_in_dir t dir_pair >>= function
      | Error _ -> Lwt.return @@ Error (`Not_found key)
      | Ok entries_by_block ->
        let translate entries = List.filter_map Chamelon.Entry.info_of_entry entries |> List.sort cmp in
        (* we have to compact first, because IDs are unique per *block*, not directory.
         * If we compact after flattening the list, we might wrongly conflate multiple
         * entries in the same directory, but on different blocks. *)
        let compacted = List.map (fun (_block, entries) -> Chamelon.Entry.compact entries) entries_by_block in
        Lwt.return @@ Ok (translate @@ List.flatten compacted)
    in
    (* find the parent directory of the [key] *)
    match (Mirage_kv.Key.segments key) with
    | [] -> ls_in_dir root_pair
    | segments ->
      (* descend into each segment until we run out, at which point we'll be in the
       * directory we want to list *)
      Fs.Find.find_first_blockpair_of_directory t root_pair segments >>= function
      | `No_id k ->
        (* be sure to return `k` as the error value, so the user might find out
         * which part of a complex path is missing and be more easily able to fix the problem *)
        Lwt.return @@ Error (`Not_found (Mirage_kv.Key.v k))
      (* No_structs is returned if part of the path is present, but not a directory (usually meaning
       * it's a file instead) *)
      | `No_structs -> Lwt.return @@ Error (`Not_found key)
      | `Basename_on pair -> ls_in_dir pair

  (** [exists t key] returns true *only* for a file/value called (basename key) set in (dirname key).
   * A directory/dictionary doesn't cut it. *)
  let exists t key =
    list t (Mirage_kv.Key.parent key) >>= function
    | Error _ as e -> Lwt.return e
    | Ok l ->
      let lookup (name, dict_or_val) =
        if (String.compare name (Mirage_kv.Key.basename key)) = 0 then
          Some dict_or_val
        else None
      in
      Lwt.return @@ Ok (List.find_map lookup l)

  let size t key = Fs.Size.size t key

  let remove t key =
    if Mirage_kv.Key.(equal empty key) then begin
      (* it's impossible to remove the root directory in littlefs, as it's
       * implicitly at the root pair *)
      Log.warn (fun m -> m "refusing to delete the root directory");
      Lwt.return @@ Error (`Not_found key)
    end else
      (* first, find the parent directory from which to delete (basename key) *)
      Fs.Find.find_first_blockpair_of_directory t root_pair Mirage_kv.Key.(segments @@ parent key) >>= function
      | `Basename_on pair ->
        Log.debug (fun f -> f "found %a in a directory starting at %a, will delete"
                      Mirage_kv.Key.pp key Fmt.(pair ~sep:comma int64 int64) 
                      pair);
        Fs.Delete.delete_in_directory pair t (Mirage_kv.Key.basename key)
      (* if we couldn't find (parent key), it's already pretty deleted *)
      | `No_id _ | `No_structs -> Lwt.return @@ Ok ()

  (* [last_modified t key] gives the timestamp metadata for a file/value,
   * or (for a directory) the most recently modified file/value within the directory.
   * We don't have to recurse, thankfully, so we only have to examine files. *)
  let last_modified t key =
    (* figure out whether [key] represents a directory. *)
    Fs.Find.find_first_blockpair_of_directory t root_pair (Mirage_kv.Key.segments key) >>= function
    | `No_id _ | `No_structs ->
      (* [key] either doesn't exist or is a value; Fs.last_modified_value handles both *)
      Fs.last_modified_value t key
    | `Basename_on _block_pair ->
      (* we were asked to get the last_modified time of a directory :/ *)
      let open Lwt_result.Infix in
      list t key >>= fun l ->
      (* luckily, the spec says we should only check last_modified dates to a depth of 1 *)
      (* unfortunately, the spec *doesn't* say what the last_modified time of an empty directory is :/ *)
      (* it's convenient for us to say it's the earliest possible time,
       * such that our fold can just use the latest time it's seen in the list as the accumulator *)
      Lwt_list.fold_left_s (fun span entry ->
          match span with
          | Error _ as e -> Lwt.return e
          | Ok prev ->
            match entry with
            | _, `Dictionary -> Lwt.return (Ok prev)
            | (name, `Value) ->
              Fs.last_modified_value t Mirage_kv.Key.(key / name) >>= fun new_span ->
              match Ptime.Span.of_d_ps prev, Ptime.Span.of_d_ps new_span with
              | None, _ | _, None -> Lwt.return @@ Error (`Not_found key)
              | Some p, Some n ->
                match Ptime.of_span p, Ptime.of_span n with
                | None, _ | _, None -> Lwt.return @@ Error (`Not_found key)
                | Some p_ts, Some a_ts ->
                  if Ptime.is_later a_ts ~than:p_ts
                  then Lwt.return @@ Ok new_span
                  else Lwt.return @@ Ok prev
        )
        (Ok Ptime.Span.(zero |> to_d_ps)) l

  (* this is probably a surprising implementation for `batch`. Concurrent writes are not
   * supported by this implementation (there's a global write mutex) so we don't have
   * to do any work to make sure that writes don't get in each other's way. *)
  let batch t ?(retries=13) f =
    let _ = retries in f t

  (** [digest t key] is the SHA256 sum of `key` if `key` is a value.
   * If [key] is a dictionary, it's a recursive digest of `key`'s contents. *)
  let digest t key =
    let rec aux ctx t key =
      get t key >>= function
      | Ok v ->
        let digest = Digestif.SHA256.feed_string ctx v in
        Lwt.return @@ Ok digest
      | Error (`Value_expected _) -> begin
          (* let's see whether we can get a digest for the directory contents *)
          (* unfortunately we can't just run a digest of the block list,
           * because CTZs can change file contents without changing
           * metadata if the length remains the same, and also because
           * there are many differences possible in the entry list that map to the same
           * filesystem structure *)
          list t key >>= function
          | Error e ->
            Log.err (fun m -> m "error listing %a: %a\n%!" Mirage_kv.Key.pp key pp_error e);
            Lwt.return @@ Error (`Not_found key)
          | Ok l -> begin
              (* There's no explicit statement in the mli about whether
               * we should descend beyond 1 dictionary for `digest`,
               * but I'm not sure how we can meaningfully have a digest if we don't *)
              Lwt_list.fold_left_s (fun ctx_result (basename, _) ->
                  match ctx_result with
                  | Error _ as e -> Lwt.return e
                  | Ok ctx ->
                    let path = Mirage_kv.Key.add key basename in
                    aux ctx t path
                ) (Ok ctx) l
            end
        end
      | Error _ as e -> Lwt.return e
    in
    let ctx = Digestif.SHA256.init () in
    Log.debug (fun f -> f "context for digest initiated");
    aux ctx t key >|= function
    | Error e -> Error e
    | Ok ctx -> Ok Digestif.SHA256.(to_raw_string @@ get ctx)

  let disconnect _ = Lwt.return_unit

  let connect ~program_block_size block =
    Sectors.get_info block >>= fun info ->
    let block_size = info.Mirage_block.sector_size in
    Fs.connect ~program_block_size ~block_size block

  let format ~program_block_size block =
    Sectors.get_info block >>= fun info ->
    let block_size = info.Mirage_block.sector_size in
    Fs.format ~program_block_size ~block_size block

  let exists_bool t key =
    if Mirage_kv.Key.to_string key = "/" then Lwt.return @@ Ok true
    else list t (Mirage_kv.Key.parent key) >>= function
    | Error _ as e -> Lwt.return e
    | Ok l ->
      let lookup (name, _dict_or_val) =
        if (String.compare name (Mirage_kv.Key.basename key)) = 0 then true
        else false in 
        Lwt.return @@ Ok (List.fold_left (fun found f -> found || lookup f) false l)

  let mkdir t path : (unit, write_error) result Lwt.t =
    let dir = Mirage_kv.Key.v path in
    Fs.mkdir t root_pair (Mirage_kv.Key.segments dir) >>= function
    | Error (`Not_found _) -> Lwt.return @@ (Error (`Not_found dir))
    | Error `No_space as e -> Lwt.return e
    | Ok _directory_head -> Lwt.return @@ Ok ()

  let statfs t (_path : string) =
    let open Block_types in
    let block_count = Int64.of_int (Block_types.This_Block.block_count t.block) in
    let block_size = Int64.of_int t.block_size in
    let unused = Int64.of_int (List.length !(t.lookahead).blocks) in
    let free = Int64.sub block_count unused in
    let namemax = Int64.of_int32 t.file_size_max in
    let stat =  {f_bsize = block_size;
                f_frsize = block_count;
                f_blocks = block_count;
                f_bfree = free;
                f_bavail = free;
                f_files = Int64.zero;
                f_ffree = Int64.zero;
                f_favail = Int64.zero;
                f_fsid = Int64.zero;
                f_flag = Int64.zero;
                f_namemax = namemax}
    in Lwt.return @@ stat

  let stat t path =
    let err i = Lwt.return @@ Cstruct.create i in
    let return cs = disconnect t.Block_types.block >>= fun _ -> Lwt.return @@ cs in
    let key = Mirage_kv.Key.v path in
    exists_bool t key >>= function
    | Error _ -> Log.err (fun f -> f "error during existence check for %s" path); err 1
    | Ok false -> Log.err (fun f -> f "error: %s does not exist in fs" path); remove t (Mirage_kv.Key.v path) >>= fun _ -> err 2
    | Ok true ->
      let info = Cstruct.create (1 + 8 + Int32.to_int (t.Block_types.name_length_max) + 1) in (* type : 8 bits, size : 64 bits, name : NAME_LENGTH_MAX+1 *)
      if (path = "/") then (* special case for root *)
        (Cstruct.set_uint8 info 0 0x002;
        Cstruct.blit_from_string "/" 0 info 9 1;
        return info)
      else
        Fs.Find.find_first_blockpair_of_directory t root_pair Mirage_kv.Key.(segments @@ parent key) >>= function
        | `No_structs -> Log.err (fun f -> f "parent directory not found"); err 1
        | `No_id _ -> Log.err (fun f -> f "parent directory not found"); err 1
        | `Basename_on block_pair ->
          Fs.Find.entries_of_name t block_pair @@ Mirage_kv.Key.basename key >>= function
          | Error _ -> Log.err (fun f -> f "error during entries_of_name call for %s" path); err 1
          | Ok [] -> Log.err (fun f -> f "no entries matching name found for %s" path); err 1
          | Ok compacted ->
            let entries = snd @@ List.(hd @@ rev compacted) in
            let name = List.find_opt (fun (tag, _data) ->
              Chamelon.Tag.((fst tag.type3 = LFS_TYPE_NAME))) in
            match name entries with
            | None -> Log.err (fun f -> f "name match failed for %s" path); err 1
            | Some (tag, data) ->
              let file_type = snd tag.type3 in
              Cstruct.set_uint8 info 0 file_type;
              Cstruct.blit data 0 info 9 (Cstruct.length data);
              if Int.equal file_type 0x002 then return info
              else
                (let inline_files = List.find_opt (fun (tag, _data) ->
                  Chamelon.Tag.((fst tag.type3) = LFS_TYPE_STRUCT) &&
                  Chamelon.Tag.((snd tag.type3) = 0x01)) in
                let ctz_files = List.find_opt (fun (tag, _block) ->
                    Chamelon.Tag.((fst tag.type3 = LFS_TYPE_STRUCT) &&
                                  Chamelon.Tag.((snd tag.type3 = 0x02)
                                              ))) in
                match inline_files entries, ctz_files entries with
                | None, None -> Log.err (fun f -> f "both inline and ctz matches failed for %s" path); err 1
                | Some (tag, _data), None -> Cstruct.LE.set_uint64 info 1 (Int64.of_int tag.Chamelon.Tag.length); return info
                | _, Some (_tag, data) ->
                  match Chamelon.File.ctz_of_cstruct data with
                  | Some (_pointer, length) -> Cstruct.LE.set_uint64 info 1 length; return info
                  | None -> Log.err (fun f -> f "ctz_of_cstruct failed for %s" path); err 1)

  let mknod t path = set t (Mirage_kv.Key.v path) "" >>= fun _ -> Lwt.return_unit
end
