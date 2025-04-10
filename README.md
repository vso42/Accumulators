CL-RSA-B accumulator implementation from the paper Accumulators with Applications to
Anonymity-Preserving Revocation.Bezouts coefficients are calculated but not used for the witness update due to unwanted modular arithmetic failure, maybe using montgomery form. Instead, the new witness is computed as w^(y^(-1)) mod n.
