module Make(Sectors : Mirage_block.S) = struct
  module This_Block = Block_ops.Make(Sectors)

type lookahead = {
  offset : int;
  blocks : int64 list ;
}

type t = {
  block : This_Block.t;
  block_size : int;
  program_block_size : int;
  lookahead : lookahead ref;
  file_size_max : Cstruct.uint32;
  name_length_max : Cstruct.uint32;
  new_block_mutex : Lwt_mutex.t;
}
end