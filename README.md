# Split Accumulators

This is a proof-of-concept of a split accumulator system for scaling anonymous
revocation to large numbers of credential holders (100M+) while maintaining
privacy. Witness updates are non-interactive.

The bilinear accumulator of [Ngu05] is the basis, employing a pairing-friendly
elliptic curve (BLS12-381 is currently assumed). A single accumulator is split
into partitions such that each membership handle belongs to a single partition.
The holder of a membership witness only needs to update it against revocations in
their own partition, which may be orders of magnitude smaller than the combined
registry. Reversal of revocations is not supported, except by rolling back the
update log.

A few components are employed here:

- An efficient bilinear accumulator in line with [KB21], which is only updated upon
  revocations.
- A new batch update protocol, which is a bit smaller and more efficient than [VB20].
- Signatures over individual accumulator states, tied to specific epoch identifiers
  (based on the signature construction from [BW07], under the Hidden Strong Diffie-Helman
  assumption).
- A efficient zero-knowledge proof of membership that does not reveal the member value or
  the partitioned accumulator value.
- Update logs, used by holders to update their non-revocation proofs (not yet implemented).
  Multiple partitions are contained in each log, and for large or long-running registries,
  multiple log files may be employed. The number of member handles assigned to an individual
  log should be high enough to avoid correlation of holders.
- Revocation managers would be required to publish the latest epoch value, or a policy for
  validating the epoch value of non-revocation proofs (f.ex. a timestamp within the past 24
  hours).
- Each member handle must additionally be attested by a proof of knowledge of a signature.
  Generally, it is expected that the member handle would be encoded as a signed message in
  a multi-message elliptic curve signature supporting partial disclosure, such as BBS or PS.
  This repository does not implement signatures for member handles.

General statistics (performance evaluated on a 2021 Macbook Pro):

- Each revocation can be encoded in 52 bytes (+ framing)
- Each epoch update is 148 bytes per partition (+ framing)
- Batch removal of 100 members from a partition is currently about 14ms, and applying the
  batch removal as a holder is about 12ms. Updates to the registry can be multi-threaded
  as individual partitions are evaluated independently.
- 100 partitions can be signed in about 50ms.
- A membership proof can be generated in about 7ms and verified in about 8ms. Only the
  verifier needs to perform pairing operations.

For a concrete example (sizes are adjustable according to desired performance):

- 10,000,000 members split into 400 partitions of 25,000, with 50 partitions (1,250,000
  members) assigned to each of 8 update logs.
- Revoking 1% of members per day (a much higher rate than generally expected).
- About 640Kb per day is added to each log.
- Each holder processes 250 updates per day in around 25ms.
- After 60 days a holder would download 37.5Mb and process 15,000 updates in around 2s.
- Performance would be lower on mobile devices, but is still expected to be reasonable.

A formal write-up of the security analysis will be forthcoming.

[Ngu05]: https://eprint.iacr.org/2005/123
[BW07]: https://link.springer.com/chapter/10.1007/978-3-540-71677-8_1
[VB20]: https://eprint.iacr.org/2020/777
[KB21]: https://eprint.iacr.org/2021/638

## License

Licensed under Apache License, Version 2.0, ([LICENSE](LICENSE) or https://www.apache.org/licenses/LICENSE-2.0)
