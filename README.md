# tstp2ladr

Convert TSTP proofs to LADR format or Prover9 hints.

Reads TSTP proofs produced by Vampire, E prover, or Prover9 and converts them to human-readable LADR format or Prover9 hint input files.

## Requirements

- LADR-2026 (Prover9/Mace4) built with `libladr.a`
- GCC or compatible C compiler

## Build

Edit `LADR` path in `Makefile` to point to your LADR-2026 directory, then:

```
make
```

## Usage

### Convert a TSTP proof to LADR format

```
eprover --cpu-limit=60 --tstp-format -s --proof-object problem.p > proof.tstp
cat proof.tstp | ./tstp2ladr > proof.ladr
```

### Generate Prover9 hints from a TSTP proof

```
cat proof.tstp | ./tstp2ladr -hints -p problem.p > hints.in
```

### Full verification pipeline: E prover → hints → Prover9 → Ivy checker

```
# Step 1: Prove with E prover
eprover --cpu-limit=60 --tstp-format -s --proof-object problem.p > proof.tstp

# Step 2: Convert to Prover9 hints
cat proof.tstp | ./tstp2ladr -hints -p problem.p > hints.in

# Step 3: Re-prove with Prover9 using hints (produces Ivy-verifiable proof)
prover9 -ladr_out -t 60 -f problem.p hints.in > p9_proof.out

# Step 4: Convert to Ivy format and verify with ACL2
prooftrans ivy < p9_proof.out > proof.ivy
checker proof.ivy
```

This pipeline takes an E prover proof (which cannot be checked by Ivy) and converts it into a Prover9 proof that can be formally verified by the Ivy/ACL2 proof checker.

## Options

| Flag | Description |
|------|-------------|
| `-ladr` | Output LADR format (default) |
| `-hints` | Output Prover9 hints format |
| `-p FILE` | Problem file (needed for `-hints` to include axioms) |

## License

GPL v2 (links against LADR libladr.a which is GPL).

## Author

Copyright (c) 2026 Jeffrey P. Machado.
