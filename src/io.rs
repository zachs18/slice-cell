use std::io::{self, Read, Seek, SeekFrom, Write};
// mostly copied from stdlib: e.g. library/std/src/io/cursor.rs:281
// note that these *cannot* implement BufRead, since fill_buf returns a `&[u8]` which could be
// shared with another thread.

use alloc::vec::Vec;

use crate::SliceCell;

impl Write for &SliceCell<u8> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let write_len = core::cmp::min(self.len(), buf.len());
        if write_len > 0 {
            unsafe {
                core::ptr::copy_nonoverlapping(buf.as_ptr(), self.as_ptr(), write_len);
            }
            *self = self.split_at(write_len).1;
        }
        Ok(write_len)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl Read for &SliceCell<u8> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let read_len = core::cmp::min(self.len(), buf.len());
        if read_len > 0 {
            unsafe {
                core::ptr::copy_nonoverlapping(self.as_ptr(), buf.as_mut_ptr(), read_len);
            }
            *self = self.split_at(read_len).1;
        }
        Ok(read_len)
    }
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        let read_len = self.len();
        if read_len == 0 {
            return Ok(0);
        }
        buf.reserve(read_len);
        unsafe {
            let write_into = buf.spare_capacity_mut();
            debug_assert!(write_into.len() >= read_len);
            core::ptr::copy_nonoverlapping(self.as_ptr(), write_into.as_mut_ptr().cast(), read_len);
            buf.set_len(buf.len() + read_len);
        }
        *self = self.split_at(read_len).1;
        Ok(read_len)
    }
}

pub struct Cursor<T> {
    inner: T,
    pos: u64,
}

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

#[cfg(test)]
mod tests {
    use crate::{io::Cursor, SliceCell};
    use std::io::{Read, Seek, Write};

    #[test]
    fn concurrent() {
        let data = SliceCell::new_boxed(std::vec![0u8; 2048].into_boxed_slice());
        let mut writer = Cursor::new(&*data);
        let mut reader = Cursor::new(&*data);
        let mut buf = [0u8; 13];

        writer.write(b"Hello, world!").unwrap();

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Hello, world!");

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, [0u8; 13]);

        writer.write(b"Hello, world!").unwrap();
        writer.write(b"Hello, world!").unwrap();

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Hello, world!");

        reader.seek(std::io::SeekFrom::Start(0)).unwrap();

        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Hello, world!");
        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Hello, world!");
        reader.read(&mut buf).unwrap();
        assert_eq!(buf, *b"Hello, world!");
    }
}
