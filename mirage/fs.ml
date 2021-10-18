type error = [
  | `Block of Mirage_block.error
  | `KV of Mirage_kv.error
]

type littlefs_write_error = [
    `Too_long (* path exceeds the allowable file name size *)
]

module Make(This_Block: Mirage_block.S) = struct

  type write_error = [
    | `Block_write of This_Block.write_error
    | `KV_write of Mirage_kv.write_error
    | `Littlefs_write of littlefs_write_error
  ]

  module Allocator = struct
    (* TODO: uh, eventually we'll need a real allocator :sweat_smile: *)
    let next _ = (2l, 3l)
  end

  let block_write_wrap = function
    | Error e -> Error (`Block_write e)
    | Ok _ as o -> o

  let format device ~block_size : (unit, write_error) result Lwt.t =
    let open Lwt.Infix in
    This_Block.get_info device >>= fun {sector_size; size_sectors; _} ->
    (* TODO: there are some error cases here, like a block size that is larger
     * than the available disk, nonsensical block sizes, etc; we should return error variants for those *)
    let block_count =
      let size_in_bytes = Int64.(mul size_sectors @@ of_int sector_size) in
      Int64.(div size_in_bytes @@ of_int32 block_size) |> Int64.to_int32
    in

    let name = Littlefs.Superblock.name in
    let superblock_inline_struct = Littlefs.Superblock.inline_struct block_size block_count in
    let rootdir_metadata_blocks = Allocator.next device in

    match Littlefs.Dir.create_dir "/" rootdir_metadata_blocks with
    | Error e -> Lwt.return @@ Error (`Littlefs_write e)
    | Ok (create, dir, structure) ->
      let write_me = Littlefs.Block.commit block_size Littlefs.Block.empty
          [name;
           superblock_inline_struct;
           create;
           dir;
           structure]
      in
      let next_rev_count = Int32.(add write_me.revision_count one) in
      This_Block.write device 0L [(Littlefs.Block.to_cstruct ~block_size write_me)] >|= block_write_wrap >>= function
      | Ok () -> 
        This_Block.write device 1L [(Littlefs.Block.to_cstruct ~block_size @@ {write_me with revision_count = next_rev_count})] >|= block_write_wrap
      | e -> Lwt.return e
end