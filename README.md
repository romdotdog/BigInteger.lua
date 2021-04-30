# BigInteger.lua

A transpilation of https://github.com/Yaffle/BigInteger to Luau.

## Issues?

Please test it on the parent repository. If it occurs, then file
the issue to the parent repository. If it doesn't occur, then
make an issue here, I will try to correct the mistake.

## Documentation

```lua
bigint.new(x: number | string)
-- Creates a new bigint. You can do usual arithmetic between two bigint objects.
-- If you encounter an internal error, make sure the bigint is not being multiplied
-- by a regular number.
-- Strings can start with 0x, 0o, or 0b for hexadecimal, octal, and binary respectively.

tostring(bigint.new("100"))
-- Converts the bigint to a base 10 string of digits.

bigint.new("100"):toString(base: number | nil)
-- or
bigint.toString(bigint.new("100"), base: number | nil)
-- Converts the bigint passed to a string of digits with an optional base.
```

---

_If you liked this repository, then give it a ⭐!_
