# Split Accumulators

This is a proof-of-concept of a split accumulator system for scaling anonymous
revocation to large numbers of credential holders (100M+) while maintaining
privacy. Witness updates are non-interactive.

The bilinear accumulator of [Nguyen05] is the basis, employing a pairing-friendly
elliptic curve (BLS12-381 is currently assumed). A single accumulator is split
into partitions such that each membership handle belongs to a single partition.
The holder of a membership witness only needs to update it against revocations in
their own partition, which may be orders of magnitude smaller than the combined
registry. Reversal of revocations is not supported, except by rolling back the
update log. Proofs of revocation (non-membership proofs) are also not supported.
A formal write-up of the security analysis will be forthcoming.

A few components are employed here:

- An efficient bilinear accumulator in line with [KB21], which is only updated upon
  revocations.
- A new batch update protocol, which is a bit smaller and more efficient than [VB20]
  (for deletions only).
- Signatures over individual accumulator states, tied to specific epoch identifiers.
  This is based on the signature construction from [BW07], under the Hidden Strong
  Diffie-Hellman assumption.
- A efficient zero-knowledge proof of membership that does not reveal the member value or
  the partitioned accumulator value.
- Update logs, used by holders to update their non-revocation proofs (not demonstrated in this
  PoC yet). Multiple partitions are contained in each log, and for large or long-running
  registries, multiple log files may be employed. The number of member handles assigned to an
  individual log should be high enough to avoid correlation of holders.
- Revocation managers would be required to publish the latest epoch value, or a policy for
  validating the epoch value of non-revocation proofs (f.ex. a timestamp within the past 24
  hours).
- Each membership proof must additionally be attested by a proof of knowledge of a signature
  over the member handle. Generally, it is expected that the member handle would be encoded as
  one message in a multi-message elliptic curve signature supporting partial disclosure, such
  as a [BBS] or Pointcheval-Sanders signature. This repository does not currently implement
  signatures for member handles.

## General performance characteristics

Performance numbers are currently evaluated on a 2021 Macbook Pro. Performance would be lower
on mobile devices, but is still expected to be reasonable.

- Each revocation can be encoded in 52 bytes (+ framing)
- Each epoch update is 144 bytes per partition (+ framing)
- Batch removal of 100 members from a partition is currently about 14ms, and applying the
  batch removal as a holder is about 12ms. Updates to the registry can be multi-threaded
  as individual partitions are evaluated independently.
- 100 partitions can be signed in about 50ms. Once a partition is fully revoked, it does not
  need to be signed again.
- For the split accumulator, a membership proof can be generated in about 8ms and verified in
  about 9ms. For the traditional accumulator, the times are each about 2ms, and only the
  verifier needs to perform pairing operations.
- The proof size is 532 bytes for the split accumulator and 160 bytes for the traditional
  accumulator.

For a concrete example (sizes are adjustable according to desired performance):

- Create a registry of size 80,000,000 split into 500 partitions of 160,000 members each.
- Revoking 600 members per batch, and 300 batches/year over a 5-year lifespan.
- About 640Kb per day is added to the log.
- Each holder normally processes 250 updates per day in around 25ms.
- After 60 days without updating, a holder would download 37.5Mb before processing 15,000
  updates in around 2s.

A smaller registry of 10,000 members split into 4 partitions would grow by approximately
5.6Kb/day at a rate of 1% revocation, maxing out at about 560Kb when fully revoked.
To revoke an entire registry, the manager may also update the current epoch value and not
sign any registry partitions, which does not increase the size of the update log.

To run the benchmarks, execute in the root directory:

```sh
cargo bench
```

These benchmarks cover the essential accumulator operations: creating and applying batch
updates, signing states, and proving and verifying membership proofs.

[Nguyen05]: https://eprint.iacr.org/2005/123
[BW07]: https://link.springer.com/chapter/10.1007/978-3-540-71677-8_1
[VB20]: https://eprint.iacr.org/2020/777
[KB21]: https://eprint.iacr.org/2021/638
[BBS]: https://datatracker.ietf.org/doc/draft-irtf-cfrg-bbs-signatures/

## License

Licensed under Apache License, Version 2.0, ([LICENSE](LICENSE) or https://www.apache.org/licenses/LICENSE-2.0)
