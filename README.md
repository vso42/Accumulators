# CL-RSA-B Accumulator

This project implements the CL-RSA-B cryptographic accumulator, as described in the paper "Accumulators with Applications to Anonymity-Preserving Revocation."

## Features

- **CL-RSA-B Accumulator**: Efficient set membership proofs and dynamic updates.
- **Witness Update**: Uses modular exponentiation for witness updates, avoiding issues with modular arithmetic by not using Bezout's coefficients directly.

## Usage

1. **Build the project:**
   ```bash
   cargo build --release
   ```

2. **Run the project:**
   ```bash
   cargo run
   ```

## Notes

- Bezout's coefficients are calculated but not used for witness updates due to modular arithmetic issues. Instead, the new witness is computed as w^(y^(-1)) mod n.
- For more details, see the referenced paper.
