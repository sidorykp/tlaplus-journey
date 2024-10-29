# tlaplus-journey
TLA+ algorithms with TLAPS proofs

# Money Transfer
A simple (but not trivial) algorithm modeling money transfer between accounts.

What makes the algorithm non-trivial:
1. It is **fault-tolerant**.
2. It models any number of accounts and money transfers.
3. It is **fully proved** using TLAPS.
4. The main invariant that is proved is a **global invariant**: the global amount of money present in the model.