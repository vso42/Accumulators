use crypto_bigint::{
    modular::{MontyForm, MontyParams},
    U256, U512, Odd, NonZero, CheckedMul, RandomMod, Invert, CheckedAdd, CheckedDiv, CheckedSub,
};
use crypto_primes::{generate_safe_prime, is_safe_prime};
use rand::rngs::OsRng;
use std::collections::HashMap;

struct BraavosAccumulator {
    sk: U256,        // p'q' = (p-1)/2 * (q-1)/2
    n: Odd<U512>,    // RSA modulus as an Odd type
    a: MontyForm<8>, // Current accumulator value in Montgomery form
    prf_key: U256,   // PRF key for element generation
    element_cache: HashMap<Vec<u8>, U256>, // Cache for x -> prime mapping
    monty_params: MontyParams<8>, // Montgomery parameters for modular arithmetic
}

impl BraavosAccumulator {
    fn new(prime_bits: u32) -> Result<Self, &'static str> {
        // Generate safe primes using crypto-primes
        let p = generate_safe_prime::<U256>(prime_bits);
        let q = generate_safe_prime::<U256>(prime_bits);

        // Ensure the primes are safe
        assert!(is_safe_prime(&p));
        assert!(is_safe_prime(&q));

        // Convert U256 primes to U512 with proper padding
        let p_512 = pad_u256_to_u512(p);
        let q_512 = pad_u256_to_u512(q);

        let n = p_512.checked_mul(&q_512).unwrap();
        let n_odd = Odd::new(n).expect("RSA modulus must be odd");

        // Calculate p' and q' where p = 2p' + 1 and q = 2q' + 1
        let divisor = NonZero::new(U256::from(2u32)).unwrap();
        let p_prime = (p - U256::ONE).wrapping_div(&divisor);
        let q_prime = (q - U256::ONE).wrapping_div(&divisor);
        let sk = p_prime.checked_mul(&q_prime).unwrap();

        // Initialize Montgomery parameters
        let monty_params = MontyParams::new(n_odd);

        // Select random a' from Z*n and set a = (a')^2 mod n
        let a_prime = U512::random_mod(&mut OsRng, &NonZero::new(n).unwrap());
        let a_prime_monty = MontyForm::new(&a_prime, monty_params);
        let a = a_prime_monty.mul(&a_prime_monty);

        // Generate random PRF key
        let prf_key = U256::random_mod(&mut OsRng, &NonZero::new(U256::MAX).unwrap());

        Ok(Self {
            sk,
            n: n_odd,
            a,
            prf_key,
            element_cache: HashMap::new(),
            monty_params,
        })
    }

    fn get_or_generate_element(&mut self, x: &[u8]) -> U256 {
        if let Some(&prime) = self.element_cache.get(x) {
            return prime;
        }
        let mut seed = Vec::with_capacity(x.len() + 32);
        seed.extend_from_slice(x);
        seed.extend_from_slice(&self.prf_key.to_be_bytes());
        let prime = generate_safe_prime::<U256>(256);
        self.element_cache.insert(x.to_vec(), prime);
        prime
    }

    fn add(&mut self, x: &[u8]) -> Result<U512, &'static str> {
        let elem = self.get_or_generate_element(x);
        let elem_inv = if elem.inv_mod(&self.sk).is_some().into() {
            elem.inv_mod(&self.sk).unwrap()
        } else {
            return Err("Element not invertible modulo sk");
        };
        let elem_inv_512 = pad_u256_to_u512(elem_inv);
        let w_monty = self.mont_mod_exp(self.a, &elem_inv_512);
        let w = w_monty.retrieve();
        Ok(w % *self.n.as_ref())
    }

    fn delete(&mut self, x: &[u8]) -> Result<(), &'static str> {
        let elem = self.get_or_generate_element(x);
        let elem_inv = if elem.inv_mod(&self.sk).is_some().into() {
            elem.inv_mod(&self.sk).unwrap()
        } else {
            return Err("Element not invertible modulo sk");
        };
        let elem_inv_512 = pad_u256_to_u512(elem_inv);
        let new_a = self.mont_mod_exp(self.a, &elem_inv_512);
        self.a = MontyForm::new(&(new_a.retrieve() % *self.n.as_ref()), self.monty_params);
        Ok(())
    }

    fn verify(&mut self, x: &[u8], w: U512) -> bool {
        let elem = self.get_or_generate_element(x);
        let elem_512 = pad_u256_to_u512(elem);
        let w_reduced = w % *self.n.as_ref();
        let w_monty = MontyForm::new(&w_reduced, self.monty_params);
        let computed_a = self.mont_mod_exp(w_monty, &elem_512);
        let computed_a_reduced = computed_a.retrieve() % *self.n.as_ref();
        let current_a_reduced = self.a.retrieve() % *self.n.as_ref();
        println!("Verification debug:");
        println!("w^x = {:?}", computed_a_reduced);
        println!("a = {:?}", current_a_reduced);
        computed_a_reduced == current_a_reduced
    }

    fn mont_mod_exp(&self, base: MontyForm<8>, exponent: &U512) -> MontyForm<8> {
        let mut result = MontyForm::new(&U512::ONE, self.monty_params);
        for i in (0..512).rev() {
            result = result.mul(&result);
            if (exponent.as_words()[i / 64] >> (i % 64)) & 1 == 1 {
                result = result.mul(&base);
            }
        }
        result
    }

    // Compute Bezout coefficients (b1, c1) such that:
    //   a * b1 + b * c1 ≡ 1 (mod sk)
    fn bezout_coeffs(&self, a: U256, b: U256) -> Result<(U256, U256), &'static str> {
        // Initialize coefficients
        let mut old_s = U256::ONE;
        let mut s = U256::ZERO;
        let mut old_t = U256::ZERO;
        let mut t = U256::ONE;
        let mut r = a % self.sk;
        let mut old_r = b % self.sk;
        
        while r != U256::ZERO {
            let quotient = old_r / r;
            let temp = r;
            r = old_r - quotient * r;
            old_r = temp;
            
            let temp_s = s;
            s = old_s.wrapping_sub(&quotient.wrapping_mul(&s));
            old_s = temp_s;
            
            let temp_t = t;
            t = old_t.wrapping_sub(&quotient.wrapping_mul(&t));
            old_t = temp_t;
        }
        
        // Make coefficients positive modulo sk
        while old_s < U256::ZERO {
            old_s = old_s.wrapping_add(&self.sk);
        }
        while old_t < U256::ZERO {
            old_t = old_t.wrapping_add(&self.sk);
        }
        
        // Reduce coefficients modulo sk
        old_s = old_s % self.sk;
        old_t = old_t % self.sk;
        
        // Verify Bezout identity modulo sk
        let check = (a.wrapping_mul(&old_s).wrapping_add(&b.wrapping_mul(&old_t))) % self.sk;
        
        if check != U256::ONE {
            return Err("Bezout coefficients verification failed");
        }
        
        Ok((old_s, old_t))
    }
    
    fn update_witness_on_deletion(&mut self, x: &[u8], w: U512, y: &[u8]) -> Result<U512, &'static str> {
        let elem_x = self.get_or_generate_element(x);
        let elem_y = self.get_or_generate_element(y);
        
        // Convert to Montgomery form
        let w_monty = MontyForm::new(&w, self.monty_params);
        
        // Compute y^(-1) mod sk
        let y_inv = if elem_y.inv_mod(&self.sk).is_some().into() {
            elem_y.inv_mod(&self.sk).unwrap()
        } else {
            return Err("Element y is not invertible modulo sk");
        };
        
        // Convert y_inv to U512
        let y_inv_512 = pad_u256_to_u512(y_inv);
        
        // Compute w^(y^(-1)) mod n
        let updated_witness = self.mont_mod_exp(w_monty, &y_inv_512);
        
        // Convert back to normal form
        let result = updated_witness.retrieve() % *self.n.as_ref();
        
        // Debug output
        println!("Witness update verification:");
        println!("Original witness = {:?}", w);
        println!("Current accumulator = {:?}", self.a.retrieve());
        println!("Element x = {:?}", elem_x);
        println!("Element y = {:?}", elem_y);
        println!("y_inv = {:?}", y_inv);
        println!("Final result = {:?}", result);
        
        Ok(result)
    }
}

fn pad_u256_to_u512(value: U256) -> U512 {
    let mut bytes = [0u8; 64];
    let value_bytes = value.to_be_bytes();
    bytes[32..].copy_from_slice(&value_bytes);
    U512::from_be_slice(&bytes)
}

fn main() {
    println!("Initializing BraavosAccumulator...");
    let mut acc = BraavosAccumulator::new(64).expect("Failed to create accumulator");
    println!("Accumulator initialized successfully!");

    let x = b"element_x";
    let y = b"element_y";

    println!("Initial accumulator value: {:?}", acc.a.retrieve());

    println!("Adding element x...");
    let w_x = acc.add(x).expect("Failed to add element x");
    println!("Witness for x: {:?}", w_x);
    println!("Accumulator after adding x: {:?}", acc.a.retrieve());

    println!("Verifying element x...");
    assert!(acc.verify(x, w_x), "Verification for x failed");
    println!("Element x verified successfully!");

    println!("Adding element y...");
    let w_y = acc.add(y).expect("Failed to add element y");
    println!("Witness for y: {:?}", w_y);
    println!("Accumulator after adding y: {:?}", acc.a.retrieve());

    println!("Deleting element y...");
    acc.delete(y).expect("Failed to delete element y");
    println!("Accumulator after deleting y: {:?}", acc.a.retrieve());
    println!("Element y deleted successfully!");

    println!("Updating witness for x...");
    let mut updated_witness = acc.update_witness_on_deletion(x, w_x, y)
        .expect("Failed to update witness");
    println!("Updated witness: {:?}", updated_witness);

    println!("Verifying element x with updated witness...");
    assert!(acc.verify(x, updated_witness), "Verification for x failed");
    println!("Element x verified successfully!");

    let z = b"element_z";

    println!("Adding element z...");
    let w_z = acc.add(z).expect("Failed to add element z");
    println!("Witness for z: {:?}", w_z);
    println!("Accumulator after adding z: {:?}", acc.a.retrieve());

    let d = b"element_d";

    println!("Adding element d...");
    acc.add(d).expect("Failed to add element d");
    println!("Accumulator after adding d: {:?}", acc.a.retrieve());
    println!("Element d added successfully!");

    println!("Deleting element d...");
    acc.delete(d).expect("Failed to delete element d");
    println!("Accumulator after deleting d: {:?}", acc.a.retrieve());
    println!("Element d deleted successfully!");

    println!("Updating witness for x...");
    updated_witness = acc.update_witness_on_deletion(x, updated_witness, d)
        .expect("Failed to update witness");
    println!("Updated witness: {:?}", updated_witness); 

    println!("Verifying element x with updated witness...");
    assert!(acc.verify(x, updated_witness), "Verification for x failed");
    println!("Element x verified successfully!");

    println!("Deleting element z...");
    acc.delete(z).expect("Failed to delete element z");
    println!("Accumulator after deleting z: {:?}", acc.a.retrieve());
    println!("Element z deleted successfully!");

    println!("Updating witness for x...");
    updated_witness = acc.update_witness_on_deletion(x, updated_witness, z)
        .expect("Failed to update witness");
    println!("Updated witness: {:?}", updated_witness);

    println!("Verifying element x with updated witness...");
    assert!(acc.verify(x, updated_witness), "Verification for x failed");
    println!("Element x verified successfully!");



    println!("All operations completed successfully!");
}