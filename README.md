# cpf-rs

Brazilian CPF parsing, validating and formatting library.

```rust
use cpf::Cpf;

// If all you need is validating a CPF number, use the `valid` function:
assert!(cpf::valid("38521139039"));

// For formatting and additional metadata from the number, parse into a `Cpf` struct:
let cpf: Cpf = "38521139039".parse().unwrap();

assert_eq!(cpf.formatted().as_str(), "385.211.390-39");
assert_eq!(cpf.digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);
```

## no_std support

The library can be used on no_std environments by disabling the `std` flag:

```toml
[dependencies]
cpf = { version = "0.1", default-features = false }
```

## Random CPF generation support

The `rand` feature flag enables random CPF generation:

```toml
[dependencies]
cpf = { version = "0.1", features = ["rand"] }
rand = "0.8"
```

```rust
use cpf::Cpf;
use rand;
use rand::Rng;

let cpf: Cpf = rand::thread_rng().gen();
```
