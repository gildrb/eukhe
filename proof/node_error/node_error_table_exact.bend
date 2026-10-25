# eukhe: the proof of LAW node_error_table_exact

import Base
import ../../bend/node_error.bend as Ne
import ../../bend/ffi_node_error.bend as FNe
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/node_error.bend as NodeError
import ./base.bend as LANodeError

# PROOF of LAW node_error_table_exact: every code computes to its row.

def NodeError.node_error_table_exact(c):
  match c:
    case Ne.E2big{}:
      {==}
    case Ne.Eacces{}:
      {==}
    case Ne.Eagain{}:
      {==}
    case Ne.Ebadf{}:
      {==}
    case Ne.Ebusy{}:
      {==}
    case Ne.Ecanceled{}:
      {==}
    case Ne.Eexist{}:
      {==}
    case Ne.Efault{}:
      {==}
    case Ne.Efbig{}:
      {==}
    case Ne.Eintr{}:
      {==}
    case Ne.Einval{}:
      {==}
    case Ne.Eio{}:
      {==}
    case Ne.Eisdir{}:
      {==}
    case Ne.Eloop{}:
      {==}
    case Ne.Emfile{}:
      {==}
    case Ne.Emlink{}:
      {==}
    case Ne.Enametoolong{}:
      {==}
    case Ne.Enfile{}:
      {==}
    case Ne.Enodev{}:
      {==}
    case Ne.Enoent{}:
      {==}
    case Ne.Enoexec{}:
      {==}
    case Ne.Enomem{}:
      {==}
    case Ne.Enospc{}:
      {==}
    case Ne.Enosys{}:
      {==}
    case Ne.Enotdir{}:
      {==}
    case Ne.Enotempty{}:
      {==}
    case Ne.Enotsup{}:
      {==}
    case Ne.Enxio{}:
      {==}
    case Ne.Eoverflow{}:
      {==}
    case Ne.Eperm{}:
      {==}
    case Ne.Epipe{}:
      {==}
    case Ne.Erofs{}:
      {==}
    case Ne.Espipe{}:
      {==}
    case Ne.Esrch{}:
      {==}
    case Ne.Etimedout{}:
      {==}
    case Ne.Etxtbsy{}:
      {==}
    case Ne.Exdev{}:
      {==}
    case Ne.Unknown{}:
      {==}
