use crate::SliceCell;
use std::{
    io::{self, Read, Seek, SeekFrom, Write},
    vec::Vec,
};
#[cfg(feature = "tokio")]
use std::{
    pin::Pin,
    task::{Context, Poll},
};
#[cfg(feature = "tokio")]
use tokio::io::{AsyncRead, AsyncSeek, AsyncWrite, ReadBuf};

// mostly copied from stdlib: e.g. library/std/src/io/cursor.rs:281
// note that these *cannot* implement BufRead, since fill_buf returns a `&[u8]` which could be
// shared with another thread.

impl Write for &SliceCell<u8> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let write_len = std::cmp::min(self.len(), buf.len());
        if write_len > 0 {
            let dst;
            (dst, *self) = self.split_at(write_len);
            dst.copy_from_slice(buf);
        }
        Ok(write_len)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl Read for &SliceCell<u8> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let read_len = std::cmp::min(self.len(), buf.len());
        if read_len > 0 {
            let src;
            (src, *self) = self.split_at(read_len);
            src.copy_into_slice(&mut buf[..read_len]);
        }
        Ok(read_len)
    }
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        let read_len = self.len();
        if read_len == 0 {
            return Ok(0);
        }

        buf.reserve(read_len);
        let write_into = buf.spare_capacity_mut();
        debug_assert!(write_into.len() >= read_len);

        let src;
        (src, *self) = self.split_at(read_len);
        // SAFETY: cannot use `Vec::extend_from_slice`, since it could reallocate, which could be arbitrary user code,
        // e.g. a custom global allocator could access *src through a `thread_local`.
        unsafe {
            // SAFETY: *src does not overlap with write_into,
            // and no other code can access *src concurrently,
            // since copy_nonoverlapping is just a memcpy.
            std::ptr::copy_nonoverlapping(
                src.as_ptr().cast::<u8>(),
                write_into.as_mut_ptr().cast(),
                read_len,
            );
            // SAFETY: We just wrote `read_len` bytes into the spare capacity.
            buf.set_len(buf.len() + read_len);
        }
        Ok(read_len)
    }
}

pub struct Cursor<T> {
    inner: T,
    pos: u64,
}

// SAFETY: We do not allow access to the inner `T` by (pinned) reference.
impl<T> Unpin for Cursor<T> {}

impl<T> Cursor<T> {
    pub const fn new(inner: T) -> Self {
        Self { inner, pos: 0 }
    }

    pub fn into_inner(self) -> T {
        self.inner
    }

    pub fn position(&self) -> u64 {
        self.pos
    }

    pub fn set_position(&mut self, pos: u64) {
        self.pos = pos;
    }
}

impl<T: AsRef<SliceCell<u8>>> Cursor<T> {
    pub fn remaining_slice(&self) -> &SliceCell<u8> {
        let len = self.pos.min(self.inner.as_ref().len() as u64);
        &self.inner.as_ref()[(len as usize)..]
    }
}

impl<T: AsRef<SliceCell<u8>>> Write for Cursor<T> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let slice: &SliceCell<u8> = self.inner.as_ref();
        let pos = std::cmp::min(self.pos, slice.len() as u64);
        let amt = (&slice[(pos as usize)..]).write(buf)?;
        self.pos += amt as u64;
        Ok(amt)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl<T: AsRef<SliceCell<u8>>> Read for Cursor<T> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = Read::read(&mut self.remaining_slice(), buf)?;
        self.pos += n as u64;
        Ok(n)
    }
    fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<()> {
        let n = buf.len();
        Read::read_exact(&mut self.remaining_slice(), buf)?;
        self.pos += n as u64;
        Ok(())
    }
}

impl<T: AsRef<SliceCell<u8>>> Seek for Cursor<T> {
    fn seek(&mut self, style: SeekFrom) -> io::Result<u64> {
        let (base_pos, offset) = match style {
            SeekFrom::Start(n) => {
                self.pos = n;
                return Ok(n);
            }
            SeekFrom::End(n) => (self.inner.as_ref().len() as u64, n),
            SeekFrom::Current(n) => (self.pos, n),
        };
        match base_pos.checked_add_signed(offset) {
            Some(n) => {
                self.pos = n;
                Ok(self.pos)
            }
            None => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid seek to a negative or overflowing position",
            )),
        }
    }
}

#[cfg(feature = "tokio")]
impl AsyncRead for &SliceCell<u8> {
    fn poll_read(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let read_len = std::cmp::min(buf.remaining(), self.len());
        if read_len > 0 {
            let src;
            (src, *self) = self.split_at(read_len);
            if cfg!(feature = "tokio_assumptions") {
                // SAFETY: Assumes that `ReadBuf::put_slice` does not perform a
                // context switch, and that it only accesses itself and the slice
                // passed to it. (i.e. it does not access *self except through
                // the reference we pass to it)
                buf.put_slice(unsafe { &*src.as_ptr() });
            } else {
                // SAFETY: we do not de-initialize any bytes of this buffer
                let unfilled = unsafe { buf.unfilled_mut() };
                debug_assert!(
                    read_len <= unfilled.len(),
                    "unfilled.len() should be == buf.remaining()"
                );
                // SAFETY: we are copying read_len bytes from `src` into `unfilled`.
                // We know they do not overlap, since `unfilled` is `&mut [u8]` and
                // `src` is a cell type.
                // We know we do not go off the end of either, since `read_len` is
                // the minimum of their lengths.
                unsafe {
                    std::ptr::copy_nonoverlapping(
                        src.as_ptr() as *const u8,
                        unfilled.as_mut_ptr().cast(),
                        read_len,
                    );
                }
                // SAFETY: we just wrote read_len bytes
                unsafe {
                    buf.assume_init(read_len);
                }
                buf.advance(read_len);
            }
        }
        Poll::Ready(Ok(()))
    }
}

#[cfg(feature = "tokio")]
impl AsyncWrite for &SliceCell<u8> {
    fn poll_write(
        mut self: Pin<&mut Self>,
        _: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<Result<usize, io::Error>> {
        Poll::Ready(self.write(buf))
    }

    fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
        Poll::Ready(Ok(()))
    }

    fn poll_shutdown(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
        Poll::Ready(Ok(()))
    }
}

#[cfg(feature = "tokio")]
impl<T: AsRef<SliceCell<u8>>> AsyncRead for Cursor<T> {
    fn poll_read(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let old_len = buf.filled().len();
        std::task::ready!(AsyncRead::poll_read(
            Pin::new(&mut self.remaining_slice()),
            cx,
            buf
        ))?;
        let new_len = buf.filled().len();
        self.pos += (new_len - old_len) as u64;
        Poll::Ready(Ok(()))
    }
}

#[cfg(feature = "tokio")]
impl<T: AsRef<SliceCell<u8>>> AsyncWrite for Cursor<T> {
    fn poll_write(
        mut self: Pin<&mut Self>,
        _: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<Result<usize, io::Error>> {
        Poll::Ready(self.write(buf))
    }

    fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
        Poll::Ready(Ok(()))
    }

    fn poll_shutdown(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
        Poll::Ready(Ok(()))
    }
}

#[cfg(feature = "tokio")]
impl<T: AsRef<SliceCell<u8>>> AsyncSeek for Cursor<T> {
    fn start_seek(mut self: Pin<&mut Self>, style: SeekFrom) -> io::Result<()> {
        self.seek(style)?;
        Ok(())
    }

    fn poll_complete(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<u64>> {
        Poll::Ready(Ok(self.pos))
    }
}

#[cfg(test)]
mod tests {
    use crate::{io::Cursor, SliceCell};
    use alloc::boxed::Box;
    use std::io::{Read, Seek, Write};

    #[test]
    fn concurrent() {
        let data: Box<SliceCell<u8>> =
            SliceCell::new_boxed(std::vec![0u8; 2048].into_boxed_slice());
        let mut writer: Cursor<&SliceCell<u8>> = Cursor::new(&*data);
        let mut reader: Cursor<&SliceCell<u8>> = Cursor::new(&*data);
        let mut buf = [0u8; 14];

        writer.write(b"Hello, world!!").unwrap();

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Hello, world!!");

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, [0u8; 14]);

        writer.write(b"Wonderful day!").unwrap();
        writer.write(b"wow, much cell").unwrap();

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"wow, much cell");

        reader.seek(std::io::SeekFrom::Start(0)).unwrap();

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Hello, world!!");
        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Wonderful day!");
        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"wow, much cell");
    }

    #[test]
    fn rc() {
        let data = SliceCell::try_new_rc(std::vec![0u8; 2048].into()).unwrap();
        let mut writer = Cursor::new(data.clone());
        let mut reader = Cursor::new(data.clone());
        drop(data);
        let mut buf = [0u8; 14];

        writer.write(b"Hello, world!!").unwrap();

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Hello, world!!");

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, [0u8; 14]);

        writer.write(b"Wonderful day!").unwrap();
        writer.write(b"wow, much cell").unwrap();

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"wow, much cell");

        reader.seek(std::io::SeekFrom::Start(0)).unwrap();

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Hello, world!!");
        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Wonderful day!");
        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"wow, much cell");
    }
}
