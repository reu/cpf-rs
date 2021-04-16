# cpf-rs

Brazilian CPF parsing, validating and formatting library.

```rust
use cpf::Cpf;

// Use the `valid` function if all you need is validating a CPF number
assert!(cpf::valid("38521139039"));
assert!(!cpf::valid("38521139030"));

// Parse into a Cpf struct if you need formatting and other metadata
let cpf: Cpf = "38521139039".parse()?;

assert_eq!(cpf.formatted().as_str(), "385.211.390-39");
assert_eq!(cpf.digits(), &[3, 8, 5, 2, 1, 1, 3, 9, 0, 3, 9]);

// Note that the Cpf struct is guaranteed to always be valid
assert!("38521139030".parse::<Cpf>().is_err());
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
