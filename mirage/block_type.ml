module Make(Sectors : Mirage_block.S) = struct
  let sizeof_pointer = 8

  module This_Block = Block_ops.Make(Sectors)

  let log_src = Logs.Src.create "chamelon-block_type" ~doc:"chamelon block interface"
  module Log = (val Logs.src_log log_src : Logs.LOG)

  type key = Mirage_kv.Key.t
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

  type t = {
    block : This_Block.t;
    block_size : int;
    program_block_size : int;
    lookahead : Cstruct.t ref;
    file_size_max : Cstruct.uint32;
    name_length_max : Cstruct.uint32;
    new_block_mutex : Lwt_mutex.t;
  }

  module Lookahead = struct
    let set_lookahead t lookahead = 
      t.lookahead := lookahead

    let set_index lookahead p value =
      try
        Cstruct.set_uint8 lookahead (Int64.to_int p) value;
      with Invalid_argument _ -> ()

    let rec set_indices lookahead cs n lim value =
      if n>=lim then ()
      else let block_index = Cstruct.LE.get_uint64 cs n in
      set_index lookahead block_index value;
      set_indices lookahead cs (n+sizeof_pointer) lim value

    let update_lookahead lookahead used_blocks =
      set_indices lookahead used_blocks 0 (Cstruct.length used_blocks) 1

    let add_to_lookahead lookahead unused_blocks =
      set_indices lookahead unused_blocks 0 (Cstruct.length unused_blocks) 0

    let rec find_first_free_block lookahead off =
      let lim = Cstruct.length lookahead in
      if Int.compare off lim >= 0 then Int64.max_int
      else let value = Cstruct.get_uint8 lookahead off in
      if value=0 then Int64.of_int off 
      else find_first_free_block lookahead (off+1)

    let in_use lookahead pointer =
      let off = Int64.to_int pointer in
      let lim = Cstruct.length lookahead in
      if Int.compare off lim >= 0 then false
      else (Cstruct.get_uint8 lookahead off)=1

    let used_blocks lookahead = 
      let rec scan lookahead off n lim =
        if off=lim then n
        else let value = Cstruct.get_uint8 lookahead off in
        scan lookahead (off+1) (n+value) lim in
      scan lookahead 0 0 (Cstruct.length lookahead)
    end

  module Allocate = struct
    open Lwt.Infix
    open Lookahead

    let get_blocks t n: (Cstruct.t, write_error) result Lwt.t =
      let get_block lookahead off =
        let p = find_first_free_block lookahead off in
        if Int64.(equal p max_int) then 
          Lwt.return @@ Error `No_space
        else Lwt.return @@ Ok p in
      let rec aux lookahead blocks off n =
        if n<0 then Lwt.return @@ Ok blocks
        else get_block lookahead off >>= function
        | Error _ as e -> Lwt.return e
        | Ok pointer ->
          Cstruct.LE.set_uint64 blocks (n*sizeof_pointer) pointer;
          aux lookahead blocks (Int64.to_int pointer + 1) (n-1)
      in let current = !(t.lookahead) in
      aux current (Cstruct.create (n*sizeof_pointer)) 0 (n-1) >>= function
      | Error _ as e -> Lwt.return e
      | Ok blocks ->
        update_lookahead current blocks; 
        set_lookahead t current; 
        Lwt.return @@ Ok blocks 

    (* [get_block_pair fs] wraps [get_blocks fs 2] to return a pair for the caller's convenience *)
    let get_block_pair t =
      get_blocks t 2 >>= function
      | Error _ as e -> Lwt.return e
      | Ok blocks ->
        let b1, b2 = Cstruct.LE.(get_uint64 blocks 0, get_uint64 blocks 8) in
        Lwt.return @@ Ok (b1, b2)
    end
  end
