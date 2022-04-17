/*!
Painless string scanning.

Basically, you'll want to use this crate if it's too much pain to solve your
problem with a bare `chars()` iterator. Speaking more broadly, `unscanny` is
useful in these situations:
- You need to parse simple flat grammars (dates, times, custom stuff, ...) and
  want an interface that's a bit more convenient to use than a simple char
  iterator.
- You're hand-writing a tokenizer.

The `Scanner` keeps an internal cursor, allows you to peek around it, advance it
beyond chars or other patterns  and easily slice substrings before and after the
cursor.

Note that the scanner doesn't have built-in support for parsing things like
numbers. It's a level of abstraction below that and wouldn't want to mandate a
specific number format. However, you can very easily build your required
abstractions on top.

# Example
Recognizing and parsing a simple comma separated list of floats.
```
# use unscanny::Scanner;
let mut s = Scanner::new(" +12 , -15.3, 14.3  ");
let mut nums = vec![];
while !s.done() {
    s.eat_whitespace();
    let start = s.cursor();
    s.eat_if(['+', '-']);
    s.eat_while(char::is_ascii_digit);
    s.eat_if('.');
    s.eat_while(char::is_ascii_digit);
    nums.push(s.from(start).parse::<f64>().unwrap());
    s.eat_whitespace();
    s.eat_if(',');
}
assert_eq!(nums, [12.0, -15.3, 14.3]);
```
*/

#![deny(missing_docs)]

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

    /// Whether the scanner has fully consumed the string.
    #[inline]
    pub fn done(&self) -> bool {
        self.cursor == self.string.len()
    }

    /// The subslice before the cursor.
    #[inline]
    pub fn before(&self) -> &'a str {
        // Safety: The cursor is always in-bounds and on a codepoint boundary.
        debug_assert!(self.string.is_char_boundary(self.cursor));
        unsafe { self.string.get_unchecked(.. self.cursor) }
    }

    /// The subslice after the cursor.
    #[inline]
    pub fn after(&self) -> &'a str {
        // Safety: The cursor is always in-bounds and on a codepoint boundary.
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
        // Safety:
        // - Snapping returns an in-bounds index that is on a codepoint boundary
        // - The cursor is always in-bounds and on a codepoint boundary.
        // - The start index is <= the end index due to the `min()`
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
        // Safety:
        // - Snapping returns an in-bounds index that is on a codepoint boundary
        // - The cursor is always in-bounds and on a codepoint boundary.
        // - The end index is >= the start index due to the `max()`
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
        // Safety:
        // - Snapping returns an in-bounds index that is on a codepoint boundary
        // - The end index is >= the start index due to the `max()`
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
            // Safety: When `c` is right behind the cursor, there must be an
            // in-bounds codepoint boundary at `self.cursor + c.len_utf8()`.
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
            // Safety: When `c` is right before the cursor, there must be an
            // in-bounds codepoint boundary at `self.cursor - c.len_utf8()`.
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
            // Safety: The contract of `matches` guarantees that there is an
            // in-bounds codepoint boundary at `len` bytes into `self.after()`.
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
            // Safety: The contract of `matches` guarantees that there is an
            // in-bounds codepoint boundary at `len` bytes into `self.after()`.
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
            // Safety: The contract of `matches` guarantees that there is an
            // in-bounds codepoint boundary at `len` bytes into `self.after()`.
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
        // Safety: Snapping returns an in-bounds index that is on a codepoint
        // boundary.
        self.cursor = self.snap(target);
    }
}

impl<'a> Scanner<'a> {
    /// Snaps an index in-bounds and to the next codepoint boundary.
    #[inline]
    fn snap(&self, mut index: usize) -> usize {
        // Safety:
        // - The call to `min()` brings the index in bounds
        // - After the while loop, the index must be on a codepoint boundary
        // - `index` cannot underflow because 0 is always a codepoint boundary
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
/// | `[char; N]`, `&[char]` | `scanner.at(['a', 'b', 'c'])`     |
/// | `FnMut(char) -> bool`  | `scanner.at(char::is_alphabetic)` |
/// | `FnMut(&char) -> bool` | `scanner.at(char::is_ascii)`      |
///
/// As you might have noticed, this closely mirrors the
/// [`Pattern`](std::str::pattern::Pattern) trait from the standard library.
/// Unfortunately, this trait is unstable, so we can't use it in the scanner's
/// method signatures. Furthermore, it doesn't support passing `&char` functions
/// which is quite useful because some char methods take `self` by reference.
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
        // Safety: When the string starts with the needle, there must be an
        // in-bounds codepoint boundary at `needle.len()` bytes into the
        // string.
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
        // Safety: When the string starts with the `self`, there must be an
        // in-bounds codepoint boundary at `self.len()` bytes into the string.
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
        // Safety: When the `string` starts with `next`, there must be an
        // in-bounds codepoint boundary at `next.len_utf8()` bytes into the
        // string.
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
        // Safety: When the `string` starts with `next`, there must be an
        // in-bounds codepoint boundary at `next.len_utf8()` bytes into the
        // string.
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
        // Safety: When the `string` starts with `next`, there must be an
        // in-bounds codepoint boundary at `next.len_utf8()` bytes into the
        // string.
        string.chars().next().filter(self).map(char::len_utf8)
    }

    #[cold]
    fn expected(&self) {
        panic!("expected closure to return `true`");
    }
}

#[cfg(test)]
mod tests {
    use super::Scanner;

    #[test]
    fn test_fmt() {
        let mut s = Scanner::new("hello world");
        assert_eq!(format!("{s:?}"), r#"Scanner(| "hello world")"#);
        s.eat_while(char::is_alphabetic);
        assert_eq!(format!("{s:?}"), r#"Scanner("hello" | " world")"#);
        s.eat_while(|_| true);
        assert_eq!(format!("{s:?}"), r#"Scanner("hello world" |)"#);
    }

    #[test]
    fn test_empty() {
        let mut s = Scanner::new("");
        s.jump(10);
        assert_eq!(s.cursor(), 0);
        assert_eq!(s.done(), true);
        assert_eq!(s.before(), "");
        assert_eq!(s.after(), "");
        assert_eq!(s.from(0), "");
        assert_eq!(s.from(10), "");
        assert_eq!(s.to(10), "");
        assert_eq!(s.to(10), "");
        assert_eq!(s.get(10 .. 20), "");
        assert_eq!(s.at(""), true);
        assert_eq!(s.at('a'), false);
        assert_eq!(s.at(|_| true), false);
        assert_eq!(s.scout(-1), None);
        assert_eq!(s.scout(-1), None);
        assert_eq!(s.scout(1), None);
        assert_eq!(s.locate(-1), 0);
        assert_eq!(s.locate(0), 0);
        assert_eq!(s.locate(1), 0);
        assert_eq!(s.eat(), None);
        assert_eq!(s.uneat(), None);
        assert_eq!(s.eat_if(""), true);
        assert_eq!(s.eat_if('a'), false);
        assert_eq!(s.eat_while(""), "");
        assert_eq!(s.eat_while('a'), "");
        assert_eq!(s.eat_until(""), "");
        assert_eq!(s.eat_whitespace(), "");
    }

    #[test]
    fn test_slice() {
        let mut s = Scanner::new("zoo 🦍🌴🎍 party");
        assert_eq!(s.parts(), ("", "zoo 🦍🌴🎍 party"));
        assert_eq!(s.get(2 .. 9), "o 🦍");
        assert_eq!(s.get(2 .. 22), "o 🦍🌴🎍 party");
        s.eat_while(char::is_ascii);
        assert_eq!(s.parts(), ("zoo ", "🦍🌴🎍 party"));
        assert_eq!(s.from(1), "oo ");
        assert_eq!(s.to(15), "🦍🌴");
        assert_eq!(s.to(16), "🦍🌴🎍");
        assert_eq!(s.to(17), "🦍🌴🎍 ");
        assert_eq!(s.to(usize::MAX), "🦍🌴🎍 party");
        s.eat_until(char::is_whitespace);
        assert_eq!(s.parts(), ("zoo 🦍🌴🎍", " party"));
        assert_eq!(s.from(3), " 🦍🌴🎍");
    }

    #[test]
    fn test_done_and_peek() {
        let mut s = Scanner::new("äbc");
        assert_eq!(s.done(), false);
        assert_eq!(s.peek(), Some('ä'));
        s.eat();
        assert_eq!(s.done(), false);
        assert_eq!(s.peek(), Some('b'));
        s.eat();
        assert_eq!(s.done(), false);
        assert_eq!(s.peek(), Some('c'));
        s.eat();
        assert_eq!(s.done(), true);
        assert_eq!(s.peek(), None);
    }

    #[test]
    fn test_at() {
        let mut s = Scanner::new("Ђ12");
        assert!(s.at('Ђ'));
        assert!(s.at(['b', 'Ђ', 'Њ']));
        assert!(s.at("Ђ"));
        assert!(s.at("Ђ1"));
        assert!(s.at(char::is_alphabetic));
        assert!(!s.at(&['b', 'c']));
        assert!(!s.at("a13"));
        assert!(!s.at(char::is_numeric));
        s.eat();
        assert!(s.at(char::is_numeric));
        assert!(s.at(char::is_ascii_digit));
    }

    #[test]
    fn test_scout_and_locate() {
        let mut s = Scanner::new("a🐆c1Ф");
        s.eat_until(char::is_numeric);
        assert_eq!(s.scout(-4), None);
        assert_eq!(s.scout(-3), Some('a'));
        assert_eq!(s.scout(-2), Some('🐆'));
        assert_eq!(s.scout(-1), Some('c'));
        assert_eq!(s.scout(0), Some('1'));
        assert_eq!(s.scout(1), Some('Ф'));
        assert_eq!(s.scout(2), None);
        assert_eq!(s.locate(-4), 0);
        assert_eq!(s.locate(-3), 0);
        assert_eq!(s.locate(-2), 1);
        assert_eq!(s.locate(-1), 5);
        assert_eq!(s.locate(0), 6);
        assert_eq!(s.locate(1), 7);
        assert_eq!(s.locate(2), 9);
        assert_eq!(s.locate(3), 9);
    }

    #[test]
    fn test_eat_and_uneat() {
        let mut s = Scanner::new("🐶🐱🐭");
        assert_eq!(s.eat(), Some('🐶'));
        s.jump(usize::MAX);
        assert_eq!(s.uneat(), Some('🐭'));
        assert_eq!(s.uneat(), Some('🐱'));
        assert_eq!(s.uneat(), Some('🐶'));
        assert_eq!(s.uneat(), None);
        assert_eq!(s.eat(), Some('🐶'));
    }

    #[test]
    fn test_conditional_and_looping() {
        let mut s = Scanner::new("abc123def33");
        assert_eq!(s.eat_if('b'), false);
        assert_eq!(s.eat_if('a'), true);
        assert_eq!(s.eat_while(['a', 'b', 'c']), "bc");
        assert_eq!(s.eat_while(char::is_numeric), "123");
        assert_eq!(s.eat_until(char::is_numeric), "def");
        assert_eq!(s.eat_while('3'), "33");
    }

    #[test]
    fn test_eat_whitespace() {
        let mut s = Scanner::new("ሙም  \n  b\tቂ");
        assert_eq!(s.eat_whitespace(), "");
        assert_eq!(s.eat_while(char::is_alphabetic), "ሙም");
        assert_eq!(s.eat_whitespace(), "  \n  ");
        assert_eq!(s.eat_if('b'), true);
        assert_eq!(s.eat_whitespace(), "\t");
        assert_eq!(s.eat_while(char::is_alphabetic), "ቂ");
    }

    #[test]
    fn test_expect_okay() {
        let mut s = Scanner::new("🦚12");
        s.expect('🦚');
        s.jump(1);
        s.expect("🦚");
        assert_eq!(s.after(), "12");
    }

    #[test]
    #[should_panic(expected = "expected '🐢'")]
    fn test_expect_char_fail() {
        let mut s = Scanner::new("no turtle in sight");
        s.expect('🐢');
    }

    #[test]
    #[should_panic(expected = "expected \"🐢\"")]
    fn test_expect_str_fail() {
        let mut s = Scanner::new("no turtle in sight");
        s.expect("🐢");
    }

    #[test]
    #[should_panic(expected = "empty slice cannot match")]
    fn test_expect_empty_array_fail() {
        let mut s = Scanner::new("");
        s.expect([]);
    }

    #[test]
    #[should_panic(expected = "expected '🐢' or '🐬'")]
    fn test_expect_array_fail() {
        let mut s = Scanner::new("no turtle or dolphin in sight");
        s.expect(['🐢', '🐬']);
    }

    #[test]
    #[should_panic(expected = "expected closure to return `true`")]
    fn test_expect_closure_fail() {
        let mut s = Scanner::new("no numbers in sight");
        s.expect(char::is_numeric);
    }
}
