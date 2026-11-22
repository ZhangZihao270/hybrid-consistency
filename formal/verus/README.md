# Verus proof of the HOT counterexample

This directory contains the machine-checked three-replica register model and the
original two-execution HOT counterexample. The entry point is `hot.rs`;
`async_weak.rs` contains the end-to-end theorem
`original_hot_from_async_replication`.

The theorem constructs two executions with independent clients. Two concurrent
weak read-modify-writes both return 1 and write 2 and 5, respectively. The first
strong read returns 5 in one execution and 2 in the other; its client sends no
further messages. After the third replica fails, an independent second strong
read completes on the two remaining replicas. Under the stated assumptions, at
least one execution violates hybrid consistency H.

The result is conditional on the theorem's explicit model assumptions. In
particular, it uses the hybrid strong-read assumption A and the functional
interpretation of T, and requires a weak-replication interface in which either
concurrent write can be released to the third replica and applied there first,
while the competing write and branch-dependent feedback are delayed. Ordinary
background exchanges and acknowledgments are allowed. Eventual asynchronous
storage by itself is not proved to imply that selective read visibility.

The proof quantifies over deterministic handlers in the formalized
three-replica register interface. A representation of every SMR protocol in
that interface, and a machine-checked extension to arbitrary replica counts,
are not established here. See the requirements of the theorem in
`async_weak.rs` for the precise service, scheduling and weak-interface
conditions.

## Verify

Use Verus `0.2026.08.02.b677dd5` with Rust toolchain
`1.97.1-x86_64-unknown-linux-gnu`, and make `verus` available on `PATH`:

```sh
./verify.sh
```

To check the main proof and its dependencies with `--no-cheating`:

```sh
verus --crate-type lib --no-cheating \
  --verify-module async_weak --verify-module background_replication \
  --verify-module weak_round --verify-module weak_visibility --verify-module weak_construction \
  --verify-module prepared_service --verify-module prepared_hot --verify-module async_messages \
  --verify-module async_fork --verify-module hybrid_majority --verify-module order_extension \
  --verify-module operation_history --verify-module register_history hot.rs
```
