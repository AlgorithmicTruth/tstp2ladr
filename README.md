# tstp2ladr

Convert TSTP proofs to LADR format or Prover9 hints.

Reads TSTP proofs produced by Vampire, E prover, or Prover9 and converts
them to either a readable LADR-style rendering of the proof, or a Prover9
hints input file for re-proving and formal verification.

The two output modes serve different purposes:

- **`-hints` (the verification path).** Emits a Prover9 input file whose
  hints come from the TSTP proof's clauses.  Prover9 then finds its *own*
  proof, guided by those hints, and that proof can be formally checked by
  the Ivy/ACL2 checker.  This is the robust route and the one to use when
  you need a verifiable result.

- **`-ladr` (a readable approximation).** Renders the TSTP proof directly
  in Prover9's LADR proof format for human reading.  Note this conversion
  is inherently lossy: TSTP does not record the term/literal position
  vectors that LADR justifications use (e.g. the `(a,1,1)` coordinates in
  `para(3(a,1),4(a,1,1))`).  tstp2ladr reconstructs these on a best-effort
  basis, but when a position cannot be recovered the step is emitted with
  a placeholder and a warning is printed to stderr.  The result is good
  for reading and inspection, but is **not** guaranteed to be a faithful,
  independently checkable LADR proof.  For verification, use `-hints`.

## Requirements

- LADR-2026 (Prover9/Mace4) built with `libladr.a`
- GCC or compatible C compiler

## Build

Edit `LADR` path in `Makefile` to point to your LADR-2026 directory, then:

```
make
```

## Usage

### Render a TSTP proof in LADR format (readable approximation)

```
eprover --cpu-limit=60 --tstp-format -s --proof-object problem.p > proof.tstp
cat proof.tstp | ./tstp2ladr > proof.ladr
```

This is for human reading.  If tstp2ladr reports that some steps have
placeholder positions, those steps could not be fully reconstructed from
the TSTP input; the rendering is approximate.  Use `-hints` for a
verifiable proof.

### Generate Prover9 hints from a TSTP proof (verification path)

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

This pipeline takes an E prover proof (which cannot be checked by Ivy)
and uses it to guide Prover9 to a proof that can be formally verified by
the Ivy/ACL2 proof checker.  Because Prover9 re-derives the proof itself,
the lossy position-reconstruction issue of the `-ladr` rendering does not
arise here -- hints only need to match clauses, not carry positions.

## Options

| Flag | Description |
|------|-------------|
| `-ladr` | Output LADR format (default).  Readable approximation; position reconstruction is best-effort and may be incomplete. |
| `-hints` | Output Prover9 hints format.  Use this for verifiable proofs. |
| `-p FILE` | Problem file (needed for `-hints` to include axioms). |

## License

GPL v2 (links against LADR libladr.a which is GPL).

## Author

Copyright (c) 2026 Jeffrey P. Machado.
