# `slice-cell`

`slice_cell::SliceCell<T>` is much like `Cell<[T]>`, but with some additional features.

In particular, `&SliceCell<u8>` implements `std::io::Read` and `Write` (under the `"std"` cargo feature), `tokio::io::AsyncRead` and `AsyncWrite` (under the `"tokio"` cargo feature), and `slice_cell::io::Cursor<&SliceCell<u8>>` implements those as well as `std::io::Seek` and `tokio::io::AsyncSeek`.
