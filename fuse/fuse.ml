open Logs_syslog_lwt
open Fuse
open Lwt.Infix
open Unix

module Littlefs = Kv.Make(Block)(Pclock)

let program_block_size = 16

let install_logger () =
  unix_reporter () >|= function
    | Ok r -> Logs.set_reporter r
    | Error e -> print_endline e

let _ = Lwt_main.run (install_logger ())
let log_src = Lwt_main.run (Lwt.return (Logs.Src.create "chamelon-fuse" ~doc:"chamelon FUSE driver"))
module Log = (val Logs.src_log log_src : Logs.LOG)

let u_stat = Lwt_main.run @@ (Lwt.return @@ LargeFile.stat ".")
let u_statfs = Lwt_main.run @@ (Lwt.return @@ Unix_util.statvfs ".")

let mount block_size image =
  let open Lwt.Infix in
  Block.connect ~prefered_sector_size:(Some block_size) image >>= fun block ->
  Littlefs.connect block ~program_block_size >>= function
  | Error _ -> Format.eprintf "Error doing the initial filesystem read\n%!"; exit 1
  | Ok t -> Lwt.return t

let chamelon_statfs bs img path =
  let open Unix_util in
  Lwt_main.run @@ (
      Log.app (fun f -> f "statfs call, path = %s" path);
      mount bs img >>= fun t ->
      Littlefs.statfs t path >>= fun stat ->
      let fs_stat = {f_bsize = stat.f_bsize;
      f_frsize = stat.f_frsize;
      f_blocks = stat.f_blocks;
      f_bfree = stat.f_bfree;
      f_bavail = stat.f_bavail;
      f_files = u_statfs.f_files;
      f_ffree = u_statfs.f_ffree;
      f_favail = u_statfs.f_favail;
      f_fsid = u_statfs.f_fsid;
      f_flag = u_statfs.f_flag;
      f_namemax = stat.f_namemax}
      in Lwt.return @@ fs_stat)

let chamelon_stat bs img path =
  let open Unix.LargeFile in
  Lwt_main.run @@ (
    Log.app (fun f -> f "stat call, path = %s" path);
    mount bs img >>= fun t ->
    Littlefs.stat t path >>= fun info ->
      try
        let file_type = Cstruct.get_uint8 info 0 in
        Lwt.return @@ {st_dev = 0;
        st_ino = u_stat.st_ino;
        st_kind = (if Int.equal file_type 0x002 then S_DIR else S_REG);
        st_perm = if Int.equal file_type 0x001 then 0o444 else u_stat.st_perm;
        st_nlink = 1;
        st_uid = u_stat.st_uid;
        st_gid = u_stat.st_gid;
        st_rdev = u_stat.st_rdev;
        st_size = (if Int.equal file_type 0x001 then Int64.of_int32 (Cstruct.LE.get_uint32 info 1) else u_stat.st_size);
        st_atime = u_stat.st_atime;
        st_mtime = u_stat.st_mtime;
        st_ctime = u_stat.st_ctime}
      with Invalid_argument _ -> raise (Unix_error (ENOENT, "stat", path))
  )

let chamelon_readdir bs img path (_fd : int) =
  Lwt_main.run @@ (
    Log.app (fun f -> f "readdir call, path = %s" path);
    mount bs img >>= fun t ->
    Littlefs.list t (Mirage_kv.Key.v path) >>= function
    | Error _ -> Log.app (fun f -> f "error reading entries from path %s" path); Lwt.return @@ []
    | Ok entries -> Log.app (fun f -> f "successfully read entries from path %s" path); Lwt.return @@ (List.map fst entries)
  )

let do_fopen path _flags = Log.app (fun f -> f "fopen call, path = %s" path); None

let chamelon_read bs img path buf offset (_fd : int) =
  Lwt_main.run @@ (
    mount bs img >>= fun t ->
    let off = Int64.to_int offset in
    let buf_cs = Cstruct.of_bigarray buf in
    Log.app (fun f -> f "attempting to read %d bytes from %s from file offset %d" (Cstruct.length buf_cs) path off);
    Littlefs.get_partial t (Mirage_kv.Key.v path) ~offset:off ~length:(Cstruct.length buf_cs) >>= function
    | Error _ -> Log.app (fun f -> f "error reading %s" path); Lwt.return @@ -1
    | Ok v -> 
      let len = String.length v in
      Cstruct.blit_from_string v 0 buf_cs 0 len; (* write to buffer *)
      Log.app (fun f -> f "successfully read %d bytes from %s beginning at offset %d into buffer" len path off);
      Log.app (fun f -> f "data read (first 10 bytes): %s" (String.sub v 0 (min 10 (String.length v))));
      Lwt.return @@ len)

let chamelon_write bs img path buf offset (_fd : int) =
  Lwt_main.run @@ (
    mount bs img >>= fun t ->
    let buf_cs = Cstruct.of_bigarray buf ~off:0 in
    let data = Cstruct.to_string buf_cs in
    let to_write, err =
      if String.equal data "-" then begin
        match Bos.OS.File.(read dash) with
        | Error _ -> "", -1
        | Ok data -> data, 0
      end else data, 0 in
    if Int.equal err (-1) then (Log.app (fun m -> m "couldn't understand what I should write\n%!"); Lwt.return @@ -1)
    else 
      (Littlefs.set t (Mirage_kv.Key.v path) to_write >>= (function
      | Ok () -> 
        Log.app (fun f -> f "successfully wrote %d bytes from file offset %Ld to buffer of size %d" (String.length to_write) offset (Cstruct.length buf_cs)); 
        Log.app (fun f -> f "data written (first 10 bytes): %s" (String.sub to_write 0 (min 10 (String.length to_write))));
        Lwt.return @@ (String.length to_write)
      | Error _ -> Log.app (fun f -> f "error when writing to %s" path); Lwt.return @@ -1))
 )

let chamelon_mkdir bs img path (_mode : int) =
  Lwt_main.run @@ (
    Log.app (fun f -> f "mkdir call, path = %s" path);
    mount bs img >>= fun t -> Littlefs.mkdir t path >>= fun _ -> Lwt.return_unit
  )

let chamelon_remove bs img path =
  Lwt_main.run @@ (
    Log.app (fun f -> f "remove call, path = %s" path);
    mount bs img >>= fun t -> Littlefs.remove t (Mirage_kv.Key.v path) >>= fun _ -> Lwt.return_unit
  )

let chamelon_mknod bs img path (_mode : int) =
  Lwt_main.run @@ (
    Log.app (fun f -> f "mknod call, path = %s" path);
    mount bs img >>= fun t -> Littlefs.mknod t path
  )

let _ =
  let bs, img = int_of_string (Array.get Sys.argv 2), (Array.get Sys.argv 3) in
  main (Array.sub Sys.argv 0 2)
    {
      default_operations with
      init = (fun () -> Log.app (fun f -> f "filesystem started"));
      getattr = chamelon_stat bs img;
      statfs = chamelon_statfs bs img;
      readdir = chamelon_readdir bs img ;
      fopen = do_fopen;
      flush = (fun _path _fd -> ());
      read = chamelon_read bs img;
      write = chamelon_write bs img;
      mkdir = chamelon_mkdir bs img;
      rmdir = chamelon_remove bs img;
      unlink = chamelon_remove bs img;
      mknod = chamelon_mknod bs img;
      utime = (fun _path _atime _mtime -> ());
    }
