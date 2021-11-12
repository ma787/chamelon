#include <stdint.h>

#define CAML_NAME_SPAC
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>

CAMLprim value ctz(value a) {
	uint32_t res = __builtin_ctz(Int32_val(a));
	return (copy_int32(res));
}

