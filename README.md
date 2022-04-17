# unscanny
[![Crates.io](https://img.shields.io/crates/v/unscanny.svg)](https://crates.io/crates/unscanny)
[![Documentation](https://docs.rs/unscanny/badge.svg)](https://docs.rs/unscanny)

Painless string scanning.

```toml
[dependencies]
unscanny = "0.1"
```

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

# Example
Recognizing and parsing a simple comma separated list of floats.
```rust
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

## Safety
This crate internally uses unsafe code for better performance. However, all
unsafe code is documented with justification why its safe, all accesses are
checked in debug mode and everything is tested.

## License
This crate is dual-licensed under the MIT and Apache 2.0 licenses.
