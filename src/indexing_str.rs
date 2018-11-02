//! String slice support for the `indexing` crate.
// FIXME(eddyb) ensure `indexing::Range` can't break
// `str`'s UTF-8 requirement, without overhead

use indexing::container_traits::{Contiguous, Trustworthy};
use indexing::{Container, Range};
use std::ops::Deref;

pub struct Str(str);

impl<'a> From<&'a str> for &'a Str {
    fn from(s: &'a str) -> Self {
        unsafe { &*(s as *const str as *const Str) }
    }
}

impl Deref for Str {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

unsafe impl Trustworthy for Str {
    type Item = u8;
    fn base_len(&self) -> usize {
        self.0.len()
    }
}

unsafe impl Contiguous for Str {
    fn begin(&self) -> *const Self::Item {
        self.0.as_ptr()
    }
    fn end(&self) -> *const Self::Item {
        unsafe { self.begin().offset(self.0.len() as isize) }
    }
    fn as_slice(&self) -> &[Self::Item] {
        self.0.as_bytes()
    }
}

impl Str {
    pub fn slice<'a, 'b, 'i>(input: &'b Container<'i, &'a Self>, range: Range<'i>) -> &'b Self {
        // NOTE(eddyb) following code is copied from `str::is_char_boundary`:
        let valid_utf8_start = |bytes: &[u8]| {
            match bytes.first() {
                None => true,
                // This is bit magic equivalent to: b < 128 || b >= 192
                Some(&b) => (b as i8) >= -0x40,
            }
        };

        let (_, after) = input.split_around(range);
        let (bytes, bytes_after) = (&input[range], &input[after]);

        // HACK(eddyb) ensure the range is still a valid `str`
        assert!(valid_utf8_start(bytes));
        assert!(valid_utf8_start(bytes_after));

        unsafe { &*(bytes as *const [u8] as *const Str) }
    }
}
