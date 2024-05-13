let sizeof_pointer = 8

let inline_struct_chunk = 0x01
let file_chunk = 0x01
let btree_chunk = 0x02

let name n id = Tag.({
    valid = true;
    type3 = (Tag.LFS_TYPE_NAME, file_chunk);
    id;
    length = String.length n;
  }, Cstruct.of_string n)

let create_inline id contents = Tag.({
    valid = true;
    type3 = (Tag.LFS_TYPE_STRUCT, inline_struct_chunk);
    id;
    length = (Cstruct.length contents);
  })

let create_btree_file id ~pointer ~file_size =
  let cs = Cstruct.create 16 in
  Cstruct.LE.set_uint64 cs 0 pointer;
  Cstruct.LE.set_uint64 cs 8 file_size;
  Tag.({
    valid = true;
    type3 = (Tag.LFS_TYPE_STRUCT, btree_chunk);
    id;
    length = (Cstruct.length cs);
  }, cs)

let btree_of_cstruct cs =
  if Cstruct.length cs < 16 then None
  else Some Cstruct.LE.(get_uint64 cs 0, get_uint64 cs 8)

let write_inline n id contents =
  [name n id; (create_inline id contents), contents; ]

let of_block cs =
  let key_region_len = Cstruct.length cs - sizeof_pointer in
  let pointer = Cstruct.LE.get_uint64 cs key_region_len in
  (pointer, Cstruct.sub cs 0 key_region_len)

let rec first_byte_on_index ~block_size index last_index =
  let b_size = block_size - sizeof_pointer in
  if index = last_index then 0
  else b_size + (first_byte_on_index ~block_size (index + 1) last_index)
