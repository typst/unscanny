//! A crate for string scanning.

use std::fmt::{self, Debug, Formatter, Write};
use std::ops::Range;

/// A string scanner.
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Scanner<'a> {
    /// The string to scan.
    string: &'a str,
    /// The index at which we currently are. To guarantee safety, it must always
    /// hold that:
    /// - 0 <= cursor <= string.len()
    /// - cursor is on a character boundary
    cursor: usize,
}

impl<'a> Scanner<'a> {
    /// Create a new string scanner, starting with a cursor position of `0`.
    #[inline]
    pub fn new(string: &'a str) -> Self {
        Self { string, cursor: 0 }
    }

    /// The full source string.
    #[inline]
    pub fn string(&self) -> &'a str {
        self.string
    }

    /// The current cursor position.
    #[inline]
    pub fn cursor(&self) -> usize {
        self.cursor
    }

    /// Whether the cursor is at the end of the string.
    #[inline]
    pub fn done(&self) -> bool {
        self.cursor == self.string.len()
    }

    /// The subslice before the cursor.
    #[inline]
    pub fn before(&self) -> &'a str {
        debug_assert!(self.string.is_char_boundary(self.cursor));
        unsafe { self.string.get_unchecked(.. self.cursor) }
    }

    /// The subslice after the cursor.
    #[inline]
    pub fn after(&self) -> &'a str {
        debug_assert!(self.string.is_char_boundary(self.cursor));
        unsafe { self.string.get_unchecked(self.cursor ..) }
    }

    /// The subslices before and after the cursor.
    #[inline]
    pub fn parts(&self) -> (&'a str, &'a str) {
        (self.before(), self.after())
    }

    /// The subslice from `start` to the cursor.
    ///
    /// Snaps `start` into the bounds of the string and to the next character
    /// boundary.
    #[inline]
    pub fn from(&self, start: usize) -> &'a str {
        let start = self.snap(start).min(self.cursor);
        debug_assert!(self.string.is_char_boundary(start));
        debug_assert!(self.string.is_char_boundary(self.cursor));
        unsafe { self.string.get_unchecked(start .. self.cursor) }
    }

    /// The subslice from the cursor to `end`.
    ///
    /// Snaps `end` into the bounds of the string and to the next character
    /// boundary.
    #[inline]
    pub fn to(&self, end: usize) -> &'a str {
        let end = self.snap(end).max(self.cursor);
        debug_assert!(self.string.is_char_boundary(self.cursor));
        debug_assert!(self.string.is_char_boundary(end));
        unsafe { self.string.get_unchecked(self.cursor .. end) }
    }

    /// The subslice from the `start` to `end`.
    ///
    /// Snaps `start` and `end` into the bounds of the string and to the next character
    /// boundary.
    #[inline]
    pub fn get(&self, range: Range<usize>) -> &'a str {
        let start = self.snap(range.start);
        let end = self.snap(range.end).max(start);
        debug_assert!(self.string.is_char_boundary(start));
        debug_assert!(self.string.is_char_boundary(end));
        unsafe { self.string.get_unchecked(start .. end) }
    }

    /// The character right behind the cursor.
    #[inline]
    pub fn peek(&self) -> Option<char> {
        self.after().chars().next()
    }

    /// Whether the part right behind the cursor starts with the given pattern.
    #[inline]
    pub fn at<T>(&self, mut pat: impl Pattern<T>) -> bool {
        pat.matches(self.after()).is_some()
    }

    /// Look at the n-th character relative to the cursor without changing the
    /// cursor.
    ///
    /// - `scout(-1)` is the character before the cursor.
    /// - `scout(0)` is the same as `peek()`.
    ///
    /// Runs in `O(|n|)`.
    #[inline]
    pub fn scout(&self, n: isize) -> Option<char> {
        if n >= 0 {
            self.after().chars().nth(n as usize)
        } else {
            self.before().chars().nth_back((-n - 1) as usize)
        }
    }

    /// The byte index of the n-th character relative to the cursor.
    ///
    /// - `locate(-1)` is the byte position of the character before the cursor.
    /// - `locate(0)` is the same as `cursor()`.
    ///
    /// Runs in `O(|n|)`.
    #[inline]
    pub fn locate(&self, n: isize) -> usize {
        if n >= 0 {
            let mut chars = self.after().chars();
            for _ in 0 .. n {
                if chars.next().is_none() {
                    break;
                }
            }
            self.string.len() - chars.as_str().len()
        } else {
            let mut chars = self.before().chars();
            for _ in 0 .. -n {
                if chars.next_back().is_none() {
                    break;
                }
            }
            chars.as_str().len()
        }
    }

    /// Consume and return the character right behind the cursor.
    #[inline]
    pub fn eat(&mut self) -> Option<char> {
        let peeked = self.peek();
        if let Some(c) = peeked {
            self.cursor += c.len_utf8();
        }
        peeked
    }

    /// Consume and return the character right before the cursor, moving it
    /// back.
    #[inline]
    pub fn uneat(&mut self) -> Option<char> {
        let unpeeked = self.before().chars().next_back();
        if let Some(c) = unpeeked {
            self.cursor -= c.len_utf8();
        }
        unpeeked
    }

    /// Consume the given pattern if that's what's right behind the cursor.
    ///
    /// Returns `true` if the pattern was consumed.
    #[inline]
    pub fn eat_if<T>(&mut self, mut pat: impl Pattern<T>) -> bool {
        if let Some(len) = pat.matches(self.after()) {
            self.cursor += len;
            true
        } else {
            false
        }
    }

    /// Consume while the given pattern is what's right behind the cursor.
    ///
    /// Returns the consumed substring.
    #[inline]
    pub fn eat_while<T>(&mut self, mut pat: impl Pattern<T>) -> &'a str {
        let start = self.cursor;
        while let Some(len @ 1 ..) = pat.matches(self.after()) {
            self.cursor += len;
        }
        self.from(start)
    }

    /// Consume until the given pattern is what's right behind the cursor.
    ///
    /// Returns the consumed substring.
    #[inline]
    pub fn eat_until<T>(&mut self, mut pat: impl Pattern<T>) -> &'a str {
        let start = self.cursor;
        while !self.done() && pat.matches(self.after()).is_none() {
            self.eat();
        }
        self.from(start)
    }

    /// Consume all whitespace until the next non-whitespace character.
    ///
    /// Returns the consumed whitespace.
    #[inline]
    pub fn eat_whitespace(&mut self) -> &'a str {
        self.eat_while(char::is_whitespace)
    }

    /// Consume the given pattern if that's what's right behind the cursor or
    /// panic otherwise.
    #[inline]
    #[track_caller]
    pub fn expect<T>(&mut self, mut pat: impl Pattern<T>) {
        if let Some(len) = pat.matches(self.after()) {
            self.cursor += len;
        } else {
            pat.expected();
        }
    }

    /// Jump to a byte position in the source string.
    ///
    /// Snaps into the bounds of the string and to the next character boundary.
    #[inline]
    pub fn jump(&mut self, target: usize) {
        self.cursor = self.snap(target);
    }
}

impl<'a> Scanner<'a> {
    /// Snaps an index in-bounds and to the next codepoint boundary.
    #[inline]
    fn snap(&self, mut index: usize) -> usize {
        index = index.min(self.string.len());
        while !self.string.is_char_boundary(index) {
            index -= 1;
        }
        index
    }
}

impl Debug for Scanner<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("Scanner(")?;
        let (before, after) = self.parts();
        if !before.is_empty() {
            before.fmt(f)?;
            f.write_char(' ')?;
        }
        f.write_char('|')?;
        if !after.is_empty() {
            f.write_char(' ')?;
            after.fmt(f)?;
        }
        f.write_char(')')
    }
}

/// Something a string can start with.
///
/// This is implemented for:
///
/// | Type                   | Example                           |
/// |------------------------|-----------------------------------|
/// | `char`                 | `scanner.at('a')`                 |
/// | `&str`                 | `scanner.at("hello")`             |
/// | `[char: N]`, `&[char]` | `scanner.at(['a', 'b', 'c'])`     |
/// | `FnMut(char) -> bool`  | `scanner.at(char::is_alphabetic)` |
/// | `FnMut(&char) -> bool` | `scanner.at(char::is_ascii)`      |
///
/// As you might have noticed, this closely mirrors the
/// [`Pattern`](std::str::pattern::Pattern) trait from the standard library.
/// This trait is unfortunately unstable though, so we can't use it in the
/// scanner's method signatures. Furthermore, it doesn't support passing `&char`
/// functions which is quite useful because some char methods take `self` by
/// reference.
pub trait Pattern<T>: Sealed<T> {}

use sealed::Sealed;
mod sealed {
    pub unsafe trait Sealed<T> {
        /// If the string starts with the pattern, return `Some(len)` with the
        /// byte length of the match. For safety, it must hold that `len` is in
        /// bounds of `string` and that `len` bytes into the string, there is a
        /// UTF-8 char boundary.
        fn matches(&mut self, string: &str) -> Option<usize>;

        /// Panic with a message stating that the pattern was expected.
        fn expected(&self);
    }
}

impl Pattern<()> for char {}
unsafe impl Sealed<()> for char {
    #[inline]
    fn matches(&mut self, string: &str) -> Option<usize> {
        let mut buf = [0; 4];
        let needle = &*self.encode_utf8(&mut buf);
        string.starts_with(needle).then(|| needle.len())
    }

    #[cold]
    fn expected(&self) {
        panic!("expected {self:?}");
    }
}

impl Pattern<()> for &str {}
unsafe impl Sealed<()> for &str {
    #[inline]
    fn matches(&mut self, string: &str) -> Option<usize> {
        string.starts_with(&*self).then(|| self.len())
    }

    #[cold]
    fn expected(&self) {
        panic!("expected {self:?}");
    }
}

impl Pattern<()> for &[char] {}
unsafe impl Sealed<()> for &[char] {
    #[inline]
    fn matches(&mut self, string: &str) -> Option<usize> {
        let next = string.chars().next()?;
        self.iter().any(|&c| c == next).then(|| next.len_utf8())
    }

    #[cold]
    fn expected(&self) {
        struct Or<'a>(&'a [char]);

        impl Debug for Or<'_> {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                let mut iter = self.0.iter();
                if let Some(c) = iter.next() {
                    c.fmt(f)?;
                    for c in iter {
                        f.write_str(" or ")?;
                        c.fmt(f)?;
                    }
                }
                Ok(())
            }
        }

        if self.is_empty() {
            panic!("empty slice cannot match");
        } else {
            panic!("expected {:?}", Or(self));
        }
    }
}

impl<const N: usize> Pattern<()> for [char; N] {}
unsafe impl<const N: usize> Sealed<()> for [char; N] {
    #[inline]
    fn matches(&mut self, string: &str) -> Option<usize> {
        self.as_slice().matches(string)
    }

    #[cold]
    fn expected(&self) {
        self.as_slice().expected();
    }
}

impl<const N: usize> Pattern<()> for &[char; N] {}
unsafe impl<const N: usize> Sealed<()> for &[char; N] {
    #[inline]
    fn matches(&mut self, string: &str) -> Option<usize> {
        self.as_slice().matches(string)
    }

    #[cold]
    fn expected(&self) {
        self.as_slice().expected();
    }
}

impl<F> Pattern<char> for F where F: FnMut(char) -> bool {}
unsafe impl<F> Sealed<char> for F
where
    F: FnMut(char) -> bool,
{
    #[inline]
    fn matches(&mut self, string: &str) -> Option<usize> {
        string.chars().next().filter(|&c| self(c)).map(char::len_utf8)
    }

    #[cold]
    fn expected(&self) {
        panic!("expected closure to return `true`");
    }
}

impl<F> Pattern<&char> for F where F: FnMut(&char) -> bool {}
unsafe impl<F> Sealed<&char> for F
where
    F: FnMut(&char) -> bool,
{
    #[inline]
    fn matches(&mut self, string: &str) -> Option<usize> {
        string.chars().next().filter(self).map(char::len_utf8)
    }

    #[cold]
    fn expected(&self) {
        panic!("expected closure to return `true`");
    }
}
