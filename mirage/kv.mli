(** Kv.Make provides the module fulfilling Mirage_kv.RW, plus a few bonus calls.
 * Many functions contain calls to the Fs module, which provides lower-level operations
 * dealing directly with on-disk structures. *)

module Make(Sectors: Mirage_block.S)(Clock : Mirage_clock.PCLOCK) : sig

  include Mirage_kv.RW

  val format : program_block_size:int -> Sectors.t -> (unit, write_error) result Lwt.t
  val connect : program_block_size:int -> Sectors.t -> (t, error) result Lwt.t
  val size : t -> key -> (int, error) result Lwt.t

  (** [get_partial t k ~offset ~length] gives errors for length <= 0 and offset < 0.
   * [get_partial t k ~offset ~length], if successful, gives a result of (Ok v) where String.length v <= [length]. If [offset + length] is greater than the file length, (Ok v) is returned where [v]'s first byte is [offset] and its last byte is the last byte in the file. *)
  val get_partial : t -> key -> offset:int -> length:int -> (string, error) result Lwt.t

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
  
  val mkdir : t -> string -> (unit, write_error) result Lwt.t
  val statfs : t -> string -> statvfs Lwt.t
  val stat : t -> string -> Cstruct.t Lwt.t
  val mknod : t -> string -> unit Lwt.t

end
